-- -----------------------------------------------------------------------------
-- | This is the top-level module in the LLVM code generator.
--

module LlvmCodeGen ( llvmCodeGen, llvmFixupAsm ) where

#include "HsVersions.h"

import Llvm
import Llvm.CodeOutput
import Llvm.TypeConversions
import LlvmCodeGen.Base
import LlvmCodeGen.CodeGen
import LlvmCodeGen.Data
--import LlvmCodeGen.Ppr
import LlvmCodeGen.Output
import LlvmCodeGen.Regs
import LlvmMangler

import CgUtils ( fixStgRegisters )
import Cmm
import Hoopl
import PprCmm

import BufWrite
import DynFlags
import ErrUtils
import FastString
import Outputable
import UniqSupply
import Platform
import SysTools ( figureLlvmVersion )
import qualified Stream

import Control.Monad ( when )
import Data.IORef ( writeIORef )
import Data.Maybe ( fromMaybe, catMaybes )
import System.IO

import LLVM.General.AST

-- -----------------------------------------------------------------------------
-- | Top-level of the LLVM Code generator
--
llvmCodeGen :: DynFlags -> Handle -> UniqSupply
               -> Stream.Stream IO RawCmmGroup ()
               -> IO ()
llvmCodeGen dflags h us cmm_stream
  = do bufh <- newBufHandle h

       -- Pass header
       showPass dflags "LLVM CodeGen"

       -- get llvm version, cache for later use
       ver <- (fromMaybe defaultLlvmVersion) `fmap` figureLlvmVersion dflags
       writeIORef (llvmVersion dflags) ver

       -- warn if unsupported
       debugTraceMsg dflags 2
            (text "Using LLVM version:" <+> text (show ver))
       let doWarn = wopt Opt_WarnUnsupportedLlvmVersion dflags
       when (ver < minSupportLlvmVersion && doWarn) $
           errorMsg dflags (text "You are using an old version of LLVM that"
                            <> text " isn't supported anymore!"
                            $+$ text "We will try though...")
       when (ver > maxSupportLlvmVersion && doWarn) $
           putMsg dflags (text "You are using a new version of LLVM that"
                          <> text " hasn't been tested yet!"
                          $+$ text "We will try though...")

       -- run code generation
       runLlvm dflags ver bufh us $
         llvmCodeGen' (targetPlatform dflags) (liftStream cmm_stream)

       -- write bitcode to file
       --writeBitcodeToFile filenm m

       bFlush bufh

llvmCodeGen' :: Platform -> Stream.Stream LlvmM RawCmmGroup () -> LlvmM ()
llvmCodeGen' platform cmm_stream = do
  -- Preamble
  -- Set the data layout and target
  let dl = Just $ platformToDataLayout platform
  let tt = Just $ platformToTargetTriple platform
  modifyModule (\mod -> mod {moduleDataLayout = dl,
                             moduleTargetTriple = tt})
  ghcInternalFunctions
  cmmMetaLlvmPrelude

  -- Procedures
  let llvmStream = Stream.mapM llvmGroupLlvmGens cmm_stream
  _ <- Stream.collect llvmStream

  -- Declare aliases for forward references
  aliases <- generateAliases
  let defs = outputLlvmData aliases
  outputLlvm defs

  -- Postamble
  cmmUsedLlvmGens

{-      m   <- newModule
        dl  <- newCString (platformToDataLayoutString platform)
        tgt <- newCString (platformToTargetString platform)
        LFC.setDataLayout m dl
        LFC.setTarget m tgt
-}
{-      -- Preamble
        renderLlvm pprLlvmHeader -- i.e. data layout plus target triple
        ghcInternalFunctions
        cmmMetaLlvmPrelude

        -- Procedures
        let llvmStream = Stream.mapM llvmGroupLlvmGens cmm_stream -- :: Stream LlvmM () () 
        _ <- Stream.collect llvmStream  -- Stream.collect turns a stream into a regular list
                                        -- :: LlvmM [()]
        -- Declare aliases for forward references
        renderLlvm . pprLlvmData =<< generateAliases

        -- Postamble
        cmmUsedLlvmGens
-}

llvmGroupLlvmGens :: RawCmmGroup -> LlvmM ()
llvmGroupLlvmGens cmm = do

        -- Insert functions into map, collect data
        let split (CmmData s d' )     = return $ Just (s, d')
            split (CmmProc h l live g) = do
              -- Set function type
              let l' = case mapLookup (g_entry g) h of
                         Nothing                   -> l
                         Just (Statics info_lbl _) -> info_lbl
              lml <- strCLabel_llvm l'
              funInsert lml =<< llvmFunTy live
              return Nothing
        cdata <- fmap catMaybes $ mapM split cmm

        {-# SCC "llvm_datas_gen" #-}
          cmmDataLlvmGens cdata
        {-# SCC "llvm_procs_gen" #-}
          mapM_ cmmLlvmGen cmm

-- -----------------------------------------------------------------------------
-- | Do LLVM code generation on all these Cmms data sections.
--
cmmDataLlvmGens :: [(Section,CmmStatics)] -> LlvmM ()

cmmDataLlvmGens statics
  = do lmdatas <- mapM genLlvmData statics

       let (gss, tss) = unzip lmdatas

       let regGlobal (LMGlobal (LMGlobalVar l ty _ _ _ _) _)
                        = funInsert l ty
           regGlobal _  = return ()
       mapM_ regGlobal (concat gss)

       outputLlvm $ outputLlvmData (concat gss, concat tss)

-- | Complete LLVM code generation phase for a single top-level chunk of Cmm.
cmmLlvmGen ::RawCmmDecl -> LlvmM ()
cmmLlvmGen cmm@CmmProc{} = do

    -- rewrite assignments to global regs
    dflags <- getDynFlag id
    let fixed_cmm = {-# SCC "llvm_fix_regs" #-}
                    fixStgRegisters dflags cmm

    dumpIfSetLlvm Opt_D_dump_opt_cmm "Optimised Cmm" (pprCmmGroup [fixed_cmm])

    -- generate llvm code from cmm
    llvmBC <- withClearVars $ genLlvmProc fixed_cmm

    -- allocate IDs for info table and code, so the mangler can later
    -- make sure they end up next to each other.
    itableSection <- freshSectionId
    _codeSection <- freshSectionId

    -- pretty print
    (defs, ivars) <- fmap unzip $ mapM (outputLlvmCmmDecl itableSection) llvmBC

    -- Output, note down used variables
    outputLlvm (concat defs)
    mapM_ markUsedVar $ concat ivars

cmmLlvmGen _ = return ()

-- -----------------------------------------------------------------------------
-- | Generate meta data nodes
--

cmmMetaLlvmPrelude :: LlvmM ()
cmmMetaLlvmPrelude = do
  metas <- flip mapM stgTBAA $ \(uniq, name, parent) -> do
    -- Generate / lookup meta data IDs
    tbaaId <- getMetaUniqueId
    setUniqMeta uniq tbaaId
    parentId <- maybe (return Nothing) getUniqMeta parent
    -- Build definition
    return $ MetaUnamed tbaaId $ MetaStruct
        [ MetaStr name
        , case parentId of
          Just p  -> MetaNode p
          Nothing -> MetaVar $ LMLitVar $ LMNullLit i8Ptr
        ]
  outputLlvm $ outputLlvmMetas metas

-- -----------------------------------------------------------------------------
-- | Marks variables as used where necessary
--

cmmUsedLlvmGens :: LlvmM ()
cmmUsedLlvmGens = do

  -- LLVM would discard variables that are internal and not obviously
  -- used if we didn't provide these hints. This will generate a
  -- definition of the form
  --
  --   @llvm.used = appending global [42 x i8*] [i8* bitcast <var> to i8*, ...]
  --
  -- Which is the LLVM way of protecting them against getting removed.
  ivars <- getUsedVars
  let cast x = LMBitc (LMStaticPointer (pVarLift x)) i8Ptr
      ty     = (LMArray (length ivars) i8Ptr)
      usedArray = LMStaticArray (map cast ivars) ty
      sectName  = Just $ fsLit "llvm.metadata"
      lmUsedVar = LMGlobalVar (fsLit "llvm.used") ty Appending sectName Nothing Constant
      lmUsed    = LMGlobal lmUsedVar (Just usedArray)
  if null ivars
     then return ()
     else outputLlvm $ outputLlvmData ([lmUsed], [])

-- Converts a platform to strings representing the data layout and target OS+Arch
platformToDataLayoutString :: Platform -> String
platformToDataLayoutString platform =
    case platform of
      Platform { platformArch = ArchX86, platformOS = OSDarwin } ->
          "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:128:128-n8:16:32"
      Platform { platformArch = ArchX86, platformOS = OSMinGW32 } ->
          "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-f80:128:128-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32"
      Platform { platformArch = ArchX86, platformOS = OSLinux } ->
                  "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32"
      Platform { platformArch = ArchX86_64, platformOS = OSDarwin } ->
                  "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64"
      Platform { platformArch = ArchX86_64, platformOS = OSLinux } ->
                  "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64"
      Platform { platformArch = ArchARM {}, platformOS = OSLinux } ->
                  "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:64:128-a0:0:64-n32"
      Platform { platformArch = ArchARM {}, platformOS = OSAndroid } ->
                  "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:64:128-a0:0:64-n32"
      Platform { platformArch = ArchARM {}, platformOS = OSQNXNTO } ->
                  "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:64:128-a0:0:64-n32"
      Platform { platformArch = ArchARM {}, platformOS = OSiOS } ->
                  "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:64:128-a0:0:64-n32"
      _ ->
          ""

platformToTargetString :: Platform -> String
platformToTargetString platform =
    case platform of
      Platform { platformArch = ArchX86, platformOS = OSDarwin } ->
          "i386-apple-darwin9.8"
      Platform { platformArch = ArchX86, platformOS = OSMinGW32 } ->
          "i686-pc-win32"
      Platform { platformArch = ArchX86, platformOS = OSLinux } ->
          "i386-pc-linux-gnu"
      Platform { platformArch = ArchX86_64, platformOS = OSDarwin } ->
          "x86_64-apple-darwin10.0.0"
      Platform { platformArch = ArchX86_64, platformOS = OSLinux } ->
          "x86_64-linux-gnu"
      Platform { platformArch = ArchARM {}, platformOS = OSLinux } ->
          "arm-unknown-linux-gnueabi"
      Platform { platformArch = ArchARM {}, platformOS = OSAndroid } ->
          "arm-unknown-linux-androideabi"
      Platform { platformArch = ArchARM {}, platformOS = OSQNXNTO } ->
          "arm-unknown-nto-qnx8.0.0eabi"
      Platform { platformArch = ArchARM {}, platformOS = OSiOS } ->
          "arm-apple-darwin10"
      _ ->
          ""