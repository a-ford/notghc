{-# LANGUAGE NamedFieldPuns #-}
module Main where

import GHC
import GHC.Paths  -- we need this to get the lib dir of GHC
import DynFlags
import Hooks
import Outputable
import ErrUtils
import CodeOutput
import Unique
import UniqSupply
import GhcMonad
import PipelineMonad
import DriverPipeline
import DriverPhases
import HscMain
import HscTypes
import qualified Stream
import Hooks
import CodeOutput
import TyCon
import CorePrep
import ProfInit

import Cmm
import CmmLint
import CmmInfo
import CmmBuildInfoTables
import CmmPipeline
import CmmParse

import LlvmCodeGen

import System.Environment
import Data.List
import Control.Exception.Base
import System.IO


main :: IO ()
main = do
  args0 <- getArgs
  let infiles = filterHsFiles args0
  (args1, _warns) <- parseStaticFlags (map noLoc args0)
  defaultErrorHandler defaultFatalMessager defaultFlushOut $ do
    runGhc (Just libdir) $ do
      dflags0 <- getSessionDynFlags
      (dflags1, _leftover, _warns) <- parseDynamicFlags dflags0 args1
      -- Hook in the new LLVM back end
      let dflags2 = dflags1 { hooks = (hooks dflags1) {runPhaseHook = Just newRunPhaseHook} }
      setSessionDynFlags dflags2
      setTargets =<< mapM (\fname -> guessTarget fname Nothing) infiles
      load LoadAllTargets
      return ()

filterHsFiles :: [String] -> [String]
filterHsFiles = filter (\f -> isSuffixOf ".hs" f || isSuffixOf ".lhs" f)

-- | Compile to hard-code.
hscGenHardCode' :: HscEnv -> CgGuts -> ModSummary -> FilePath
               -> IO (FilePath, Maybe FilePath) -- ^ @Just f@ <=> _stub.c is f
hscGenHardCode' hsc_env cgguts mod_summary output_filename = do
        let CgGuts{ -- This is the last use of the ModGuts in a compilation.
                    -- From now on, we just use the bits we need.
                    cg_module   = this_mod,
                    cg_binds    = core_binds,
                    cg_tycons   = tycons,
                    cg_foreign  = foreign_stubs0,
                    cg_dep_pkgs = dependencies,
                    cg_hpc_info = hpc_info } = cgguts
            dflags = hsc_dflags hsc_env
            location = ms_location mod_summary
            data_tycons = filter isDataTyCon tycons
            -- cg_tycons includes newtypes, for the benefit of External Core,
            -- but we don't generate any code for newtypes

        -------------------
        -- PREPARE FOR CODE GENERATION
        -- Do saturation and convert to A-normal form
        prepd_binds <- {-# SCC "CorePrep" #-}
                       corePrepPgm dflags hsc_env core_binds data_tycons ;
        -----------------  Convert to STG ------------------
        (stg_binds, cost_centre_info)
            <- {-# SCC "CoreToStg" #-}
               myCoreToStg dflags this_mod prepd_binds

        let prof_init = profilingInitCode this_mod cost_centre_info
            foreign_stubs = foreign_stubs0 `appendStubC` prof_init

        ------------------  Code generation ------------------

        cmms <- {-# SCC "NewCodeGen" #-}
                         tryNewCodeGen hsc_env this_mod data_tycons
                             cost_centre_info
                             stg_binds hpc_info

        ------------------  Code output -----------------------
        rawcmms0 <- {-# SCC "cmmToRawCmm" #-}
                   cmmToRawCmm dflags cmms

        let dump a = do dumpIfSet_dyn dflags Opt_D_dump_cmm_raw "Raw Cmm"
                           (ppr a)
                        return a
            rawcmms1 = Stream.mapM dump rawcmms0
        (output_filename, (_stub_h_exists, stub_c_exists))
            <- {-# SCC "codeOutput" #-}
               codeOutput' dflags this_mod output_filename location
               foreign_stubs dependencies rawcmms1
        return (output_filename, stub_c_exists)

hscPostBackendPhase' :: DynFlags -> HscSource -> HscTarget -> Phase
hscPostBackendPhase' _ HsBootFile _    =  StopLn
hscPostBackendPhase' dflags _ hsc_lang =
  case hsc_lang of
        HscC -> HCc
        HscAsm | gopt Opt_SplitObjs dflags -> Splitter
               | otherwise                 -> As
        HscLlvm        -> LlvmMangle -- We compile in the HscOut phase
        HscNothing     -> StopLn
        HscInterpreted -> StopLn

-- For the HscOut compilation phase, run the custom LLVM backend.
newRunPhaseHook :: PhasePlus -> FilePath -> DynFlags -> CompPipeline (PhasePlus, FilePath)
newRunPhaseHook (HscOut src_flavour mod_name result) _ dflags = do
        location <- getLocation src_flavour mod_name
        setModLocation location

        let o_file = ml_obj_file location -- The real object file
            hsc_lang = hscTarget dflags
            next_phase = hscPostBackendPhase' dflags src_flavour hsc_lang

        case result of
            HscNotGeneratingCode ->
                return (RealPhase next_phase,
                        panic "No output filename from Hsc when no-code")
            HscUpToDate ->
                do liftIO $ touchObjectFile dflags o_file
                   -- The .o file must have a later modification date
                   -- than the source file (else we wouldn't get Nothing)
                   -- but we touch it anyway, to keep 'make' happy (we think).
                   return (RealPhase StopLn, o_file)
            HscUpdateBoot ->
                do -- In the case of hs-boot files, generate a dummy .o-boot
                   -- stamp file for the benefit of Make
                   liftIO $ touchObjectFile dflags o_file
                   return (RealPhase next_phase, o_file)
            HscRecomp cgguts mod_summary
              -> do output_fn <- phaseOutputFilename next_phase

                    liftIO $ debugTraceMsg dflags 1 (text output_fn)

                    PipeState{hsc_env=hsc_env'} <- getPipeState

                    (outputFilename, mStub) <- liftIO $ hscGenHardCode' hsc_env' cgguts mod_summary output_fn
                    case mStub of
                        Nothing -> return ()
                        Just stub_c ->
                            do stub_o <- liftIO $ compileStub hsc_env' stub_c
                               setStubO stub_o

                    return (RealPhase next_phase, outputFilename)

{-
-- We should bypass every stage after generating object code
newRunPhaseHook (RealPhase LlvmOpt) input dflags = P (\env state -> return (state, (RealPhase LlvmLlc, "")))
newRunPhaseHook (RealPhase LlvmLlc) input dflags = P (\env state -> return (state, (RealPhase LlvmMangle, "")))
-- may need this
newRunPhaseHook (RealPhase LlvmMangle) input dflags = P (\env state -> return (state, (RealPhase As, "")))
newRunPhaseHook (RealPhase As) input dflags = P (\env state -> return (state, (RealPhase StopLn, "")))
-}
--newRunPhaseHook (RealPhase Cmm) input dflags =
--    do liftIO $ debugTraceMsg dflags 0 (ppr (RealPhase Cmm))
--       case hscTarget dflags of
--         HscLlvm -> compileCmmToBc input dflags
--         _       -> runPhase (RealPhase Cmm) input dflags
{-
newRunPhaseHook (RealPhase As) input dflags =
    do liftIO $ debugTraceMsg dflags 0 (ppr (RealPhase As))
       _ <- liftIO $ getLine -- Breakpoint so I can manually hack at the asm
       runPhase (RealPhase As) input dflags
-}

-- For every other stage, just let GHC handle it.
newRunPhaseHook p input dflags =
    do liftIO $ debugTraceMsg dflags 1 (ppr p)
       runPhase p input dflags

compileCmmToBc :: FilePath -> DynFlags -> CompPipeline (PhasePlus, FilePath)
compileCmmToBc input_fn dflags
  = do
      let hsc_lang = hscTarget dflags
      let next_phase = hscPostBackendPhase' dflags HsSrcFile hsc_lang
      output_fn <- phaseOutputFilename next_phase
      PipeState{hsc_env} <- getPipeState
      liftIO $ compileCmmFile hsc_env input_fn output_fn
      return (RealPhase next_phase, output_fn)

compileCmmFile :: HscEnv -> FilePath -> FilePath -> IO ()
compileCmmFile hsc_env input_fn output_fn = runHsc hsc_env $ do
    let dflags = hsc_dflags hsc_env
    cmm <- ioMsgMaybe $ parseCmmFile dflags input_fn
    liftIO $ do
        us <- mkSplitUniqSupply 'S'
        let initTopSRT = initUs_ us emptySRT
        dumpIfSet_dyn dflags Opt_D_dump_cmm "Parsed Cmm" (ppr cmm)
        (_, cmmgroup) <- cmmPipeline hsc_env initTopSRT cmm
        rawCmms <- cmmToRawCmm dflags (Stream.yield cmmgroup)
        _ <- llvmCodeOutput dflags no_mod output_fn no_loc NoStubs [] rawCmms
        return ()
  where
    no_mod = panic "hscCmmFile: no_mod"
    no_loc = ModLocation{ ml_hs_file  = Just input_fn,
                          ml_hi_file  = panic "hscCmmFile: no hi file",
                          ml_obj_file = panic "hscCmmFile: no obj file" }

codeOutput' :: DynFlags
           -> Module
           -> FilePath
           -> ModLocation
           -> ForeignStubs
           -> [PackageId]
           -> Stream.Stream IO RawCmmGroup ()                       -- Compiled C--
           -> IO (FilePath, -- output filename
                  (Bool{-stub_h_exists-}, Maybe FilePath{-stub_c_exists-}))
codeOutput' dflags this_mod filenm location foreign_stubs pkg_deps cmm_stream
  =
    case hscTarget dflags of
      HscLlvm -> llvmCodeOutput dflags this_mod filenm location foreign_stubs pkg_deps cmm_stream
      _       -> codeOutput dflags this_mod filenm location foreign_stubs pkg_deps cmm_stream

-- body mostly copied from codeOutput
llvmCodeOutput :: DynFlags
               -> Module
               -> FilePath
               -> ModLocation
               -> ForeignStubs
               -> [PackageId]
               -> Stream.Stream IO RawCmmGroup ()                       -- Compiled C--
               -> IO (FilePath,
                      (Bool{-stub_h_exists-}, Maybe FilePath{-stub_c_exists-}))
llvmCodeOutput dflags this_mod filenm location foreign_stubs pkg_deps cmm_stream
  = do  {
        -- Lint each CmmGroup as it goes past
        ; let linted_cmm_stream =
                 if gopt Opt_DoCmmLinting dflags
                    then Stream.mapM do_lint cmm_stream
                    else cmm_stream

              do_lint cmm = do
                { showPass dflags "CmmLint"
                ; case cmmLint dflags cmm of
                        Just err -> do { log_action dflags dflags SevDump noSrcSpan defaultDumpStyle err
                                       ; ghcExit dflags 1
                                       }
                        Nothing  -> return ()
                ; return cmm
                }

        ; showPass dflags "CodeOutput"
        ; stubs_exist <- outputForeignStubs dflags this_mod location foreign_stubs
        -- at this point, we have already checked that we are using the LLVM back end
        ; outputLlvm' dflags filenm linted_cmm_stream
        ; return (filenm, stubs_exist)
        }

-- Copied from CodeOutput
doOutput :: String -> (Handle -> IO a) -> IO a
doOutput filenm io_action = bracket (openFile filenm WriteMode) hClose io_action

outputLlvm' :: DynFlags -> FilePath -> Stream.Stream IO RawCmmGroup () -> IO ()
outputLlvm' dflags filenm cmm_stream
  = do ncg_uniqs <- mkSplitUniqSupply 'n'
       llvmCodeGen dflags filenm ncg_uniqs cmm_stream
{-
       {-# SCC "llvm_output" #-} doOutput filenm $
           \f -> {-# SCC "llvm_CodeGen" #-}
                 llvmCodeGen dflags f ncg_uniqs cmm_stream
-}