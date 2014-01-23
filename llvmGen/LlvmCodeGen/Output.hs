-- ----------------------------------------------------------------------------
-- | Pretty print helpers for the LLVM Code generator.
--

module LlvmCodeGen.Output (
        outputLlvmData, outputLlvmCmmDecl, outputInfoTable, infoSection, iTableSuf
    ) where

#include "HsVersions.h"

import Llvm
import Llvm.CodeOutput
import LlvmCodeGen.Base
import LlvmCodeGen.Data

import CLabel
import Cmm

import FastString
import Unique

import LLVM.General.AST

-- ----------------------------------------------------------------------------
-- * Top level
--

outputLlvmData :: LlvmData -> [Definition]
outputLlvmData (globals, types) =
    let outputLlvmTys (LMAlias    a) = outputLlvmAlias a
        outputLlvmTys (LMFunction f) = undefined -- this should be defined
        outputLlvmTys _other         = undefined

        types'   = map outputLlvmTys types
        globals' = outputLlvmGlobals globals
    in types' ++ globals'

-- | Pretty print LLVM code
outputLlvmCmmDecl :: Int -> LlvmCmmDecl -> LlvmM ([Definition], [LlvmVar])
outputLlvmCmmDecl _ (CmmData _ lmdata)
  = return (concat $ map outputLlvmData lmdata, [])

outputLlvmCmmDecl count (CmmProc mb_info entry_lbl live (ListGraph blks))
  = do (idoc, ivar) <- case mb_info of
                        Nothing -> return ([], [])
                        Just (Statics info_lbl dat)
                         -> outputInfoTable count info_lbl (Statics entry_lbl dat)

       let sec = mkLayoutSection (count + 1)
           (lbl',sec') = case mb_info of
                           Nothing                   -> (entry_lbl, Nothing)
                           Just (Statics info_lbl _) -> (info_lbl,  sec)
           link = if externallyVisibleCLabel lbl'
                      then ExternallyVisible
                      else Internal
           lmblocks = map (\(Cmm.BasicBlock id stmts) ->
                                LlvmBlock (getUnique id) stmts) blks

       fun <- mkLlvmFunc live lbl' link  sec' lmblocks

       return ((outputLlvmFunction fun):idoc, ivar)

-- | Output CmmStatic
outputInfoTable :: Int -> CLabel -> CmmStatics -> LlvmM ([Definition], [LlvmVar])
outputInfoTable count info_lbl stat
  = do (ldata, ltypes) <- genLlvmData (Text, stat)

       dflags <- getDynFlags
       let setSection (LMGlobal (LMGlobalVar _ ty l _ _ c) d) = do
             lbl <- strCLabel_llvm info_lbl
             let sec = mkLayoutSection count
                 ilabel = lbl `appendFS` fsLit iTableSuf
                 gv = LMGlobalVar ilabel ty l sec (llvmInfAlign dflags) c
                 v = if l == Internal then [gv] else []
             funInsert ilabel ty
             return (LMGlobal gv d, v)
           setSection v = return (v,[])

       (ldata', llvmUsed) <- setSection (last ldata)
       if length ldata /= 1
          then error "outputInfoTable: invalid info table!"
          else return (outputLlvmData ([ldata'], ltypes), llvmUsed)


-- | We generate labels for info tables by converting them to the same label
-- as for the entry code but adding this string as a suffix.
iTableSuf :: String
iTableSuf = "_itable"


-- | Create a specially crafted section declaration that encodes the order this
-- section should be in the final object code.
-- 
-- The LlvmMangler.llvmFixupAsm pass over the assembly produced by LLVM uses
-- this section declaration to do its processing.
mkLayoutSection :: Int -> LMSection
mkLayoutSection n
  = Just (fsLit $ infoSection ++ show n)


-- | The section we are putting info tables and their entry code into, should
-- be unique since we process the assembly pattern matching this.
infoSection :: String
infoSection = "X98A__STRIP,__me"

