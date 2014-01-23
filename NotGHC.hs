module NotGHC where

import GHC
import GHC.Paths  -- we need this to get the lib dir of GHC
import DynFlags
import Hooks

import LlvmCodeGen

import System.Environment
import Data.List

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
      let dflags2 = dflags1 { hooks = insertHook RunPhaseHook runPhaseHook (hooks dflags1) }
      setSessionDynFlags dflags2
      setTargets =<< mapM (\fname -> guessTarget fname Nothing) infiles
      

filterHsFiles :: [String] -> [String]
filterHsFiles = filter (\f -> isSuffixOf ".hs" f || isSuffixOf ".lhs" f)

-- For the Cmm compilation phase, run the custom LLVM backend.
runPhaseHook :: PhasePlus -> FilePath -> DynFlags -> CompPipeline (PhasePlus, FilePath)
runPhaseHook (RealPhase Cmm) input dflags =
    case hscTarget dflags of {
      HscLlvm -> compileCmmToBc input dflags
      _       -> runPhase (RealPhase Cmm) input dflags
    }
-- For every other stage, just let GHC handle it.
runPhaseHook p input dflags = runPhase p input dflags

compileCmmToBc :: FilePath -> DynFlags -> CompPipeline (PhasePlus, FilePath)
compileCmmToBc input_fn dflags
  = do
      let hsc_lang = hscTarget dflags
      let next_phase = hscPostBackendPhase dflags HsSrcFile hsc_lang
      output_fn <- phaseOutputFileName next_phase
      PipeState{hsc_env} <- getPipeState
      liftIO $ compileCmmFile hsc_env input_fn output_fn
      return (RealPhase next_phase, output_fn)

compileCmmFile :: HscEnv -> FilePath -> FilePath -> IO ()
compileCmmFile hsc_env input_fn output_fn = runHsc hsc_env $ do
    let dflags = hsc_dflags hsc_env
    cmm <- ioMsgMaybe $ parseCmmFile dflags filename
    liftIO $ do
        us <- mkSplitUniqSupply 'S'
        let initTopSRT = initUs_ us emptySRT
        dumpIfSet_dyn dflags Opt_D_dump_cmm "Parsed Cmm" (ppr cmm)
        (_, cmmgroup) <- cmmPipeline hsc_env initTopSRT cmm
        rawCmms <- cmmToRawCmm dflags (Stream.yield cmmgroup)
        _ <- llvmCodeOutput dflags no_mod output_filename no_loc NoStubs [] rawCmms
        return ()
  where
    no_mod = panic "hscCmmFile: no_mod"
    no_loc = ModLocation{ ml_hs_file  = Just filename,
                          ml_hi_file  = panic "hscCmmFile: no hi file",
                          ml_obj_file = panic "hscCmmFile: no obj file" }

-- body mostly copied from codeOutput
llvmCodeOutput :: DynFlags
           -> Module
           -> FilePath
           -> ModLocation
           -> ForeignStubs
           -> [PackageId]
           -> Stream IO RawCmmGroup ()                       -- Compiled C--
           -> IO (FilePath,
                  (Bool{-stub_h_exists-}, Maybe FilePath{-stub_c_exists-}))
llvmCodeOutput dflags this_mod filenm location foreign_stubs pkg_deps cmm_stream
  = 
    do  {
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

outputLlvm' :: DynFlags -> FilePath -> Stream IO RawCmmGroup () -> IO ()
outputLlvm' dflags filenm cmm_stream
  = do ncg_uniqs <- mkSplitUniqSupply 'n'

       {-# SCC "llvm_output" #-} doOutput filenm $
           \f -> {-# SCC "llvm_CodeGen" #-}
                 llvmCodeGen dflags f ncg_uniqs cmm_stream
