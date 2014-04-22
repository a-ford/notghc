-- | This is a copy of many parts of the Main API for compiling plain Haskell source code.
--
-- We need to copy these across since many functions we call are not
-- exported by HscMain. This is rather ugly, but necessary to build
-- against vanilla GHC.
{-# LANGUAGE ForeignFunctionInterface, NamedFieldPuns, PatternGuards #-}

module HscMainMod (newRunPhaseHook) where
-- The official GHC API, and various things we need from GHC
import GHC
import GHC.Paths
import CmdLineParser
import CodeOutput
import Unique
import UniqSupply
import GhcMonad hiding (logWarnings)
import PipelineMonad
import DriverPipeline
import DriverPhases
import HscMain
import HscTypes
import qualified Stream
import Stream (Stream)
import Hooks
import CodeOutput
import TyCon
import CorePrep
import ProfInit
import Bag
import SysTools
import CoreSyn
import CostCentre
import StgSyn
import StgCmm
import CoreToStg
import SimplStg
import Platform

import Cmm
import CmmLint
import CmmInfo
import CmmBuildInfoTables
import CmmPipeline
import CmmParse

import LlvmCodeGen

import System.Environment
import System.Directory
import Data.List
import Control.Exception.Base
import System.IO

import Text.Printf
import Control.Exception
import System.CPUTime


-- Implementations of the various modes (--show-iface, mkdependHS. etc.)
import LoadIface        ( showIface )
import HscMain          ( newHscEnv )
import DriverPipeline   ( oneShot, compileFile )
import DriverMkDepend   ( doMkDependHS )
#ifdef GHCI
import InteractiveUI    ( interactiveUI, ghciWelcomeMsg, defaultGhciSettings )
#endif


-- Various other random stuff that we need
import Config
import Constants
import HscTypes
import Packages         ( dumpPackages )
import DriverPhases
import BasicTypes       ( failed )
import StaticFlags
import DynFlags
import ErrUtils
import FastString
import Outputable
import SrcLoc
import Util
import Panic
import MonadUtils       ( liftIO )

-- Imports for --abi-hash
import LoadIface           ( loadUserInterface )
import Module              ( mkModuleName )
import Finder              ( findImportedModule, cannotFindInterface )
import TcRnMonad           ( initIfaceCheck )
import Binary              ( openBinMem, put_, fingerprintBinMem )

-- Standard Haskell libraries
import System.IO
import System.Environment
import System.Exit
import System.FilePath
import Control.Monad
import Data.Char
import Data.List
import Data.Maybe

#include "HsVersions.h"

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
--        start <- liftIO $ getCPUTime
--        let start' = (fromIntegral start) / (10^9)
--        liftIO $ debugTraceMsg dflags 0 (text (show start'))
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

newRunPhaseHook (RealPhase As) input dflags =
    do end <- liftIO $ getCPUTime
       let end' = (fromIntegral end) / (10^9)
       liftIO $ debugTraceMsg dflags 0 (text (show end'))
       liftIO $ debugTraceMsg dflags 1 (ppr (RealPhase As))
--       _ <- liftIO $ getLine -- Breakpoint so I can manually hack at the asm
       runPhase (RealPhase As) input dflags


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

-- | Deal with errors and warnings returned by a compilation step
--
-- In order to reduce dependencies to other parts of the compiler, functions
-- outside the "main" parts of GHC return warnings and errors as a parameter
-- and signal success via by wrapping the result in a 'Maybe' type. This
-- function logs the returned warnings and propagates errors as exceptions
-- (of type 'SourceError').
--
-- This function assumes the following invariants:
--
--  1. If the second result indicates success (is of the form 'Just x'),
--     there must be no error messages in the first result.
--
--  2. If there are no error messages, but the second result indicates failure
--     there should be warnings in the first result. That is, if the action
--     failed, it must have been due to the warnings (i.e., @-Werror@).
ioMsgMaybe :: IO (Messages, Maybe a) -> Hsc a
ioMsgMaybe ioA = do
    ((warns,errs), mb_r) <- liftIO ioA
    logWarnings warns
    case mb_r of
        Nothing -> throwErrors errs
        Just r  -> ASSERT( isEmptyBag errs ) return r

tryNewCodeGen   :: HscEnv -> Module -> [TyCon]
                -> CollectedCCs
                -> [StgBinding]
                -> HpcInfo
                -> IO (Stream IO CmmGroup ())
         -- Note we produce a 'Stream' of CmmGroups, so that the
         -- backend can be run incrementally.  Otherwise it generates all
         -- the C-- up front, which has a significant space cost.
tryNewCodeGen hsc_env this_mod data_tycons
              cost_centre_info stg_binds hpc_info = do
    let dflags = hsc_dflags hsc_env

    let cmm_stream :: Stream IO CmmGroup ()
        cmm_stream = {-# SCC "StgCmm" #-}
            StgCmm.codeGen dflags this_mod data_tycons
                           cost_centre_info stg_binds hpc_info

        -- codegen consumes a stream of CmmGroup, and produces a new
        -- stream of CmmGroup (not necessarily synchronised: one
        -- CmmGroup on input may produce many CmmGroups on output due
        -- to proc-point splitting).

    let dump1 a = do dumpIfSet_dyn dflags Opt_D_dump_cmm
                       "Cmm produced by new codegen" (ppr a)
                     return a

        ppr_stream1 = Stream.mapM dump1 cmm_stream

    -- We are building a single SRT for the entire module, so
    -- we must thread it through all the procedures as we cps-convert them.
    us <- mkSplitUniqSupply 'S'

    -- When splitting, we generate one SRT per split chunk, otherwise
    -- we generate one SRT for the whole module.
    let
     pipeline_stream
      | gopt Opt_SplitObjs dflags
        = {-# SCC "cmmPipeline" #-}
          let run_pipeline us cmmgroup = do
                let (topSRT', us') = initUs us emptySRT
                (topSRT, cmmgroup) <- cmmPipeline hsc_env topSRT' cmmgroup
                let srt | isEmptySRT topSRT = []
                        | otherwise         = srtToData topSRT
                return (us', srt ++ cmmgroup)

          in do _ <- Stream.mapAccumL run_pipeline us ppr_stream1
                return ()

      | otherwise
        = {-# SCC "cmmPipeline" #-}
          let initTopSRT = initUs_ us emptySRT
              run_pipeline = cmmPipeline hsc_env
          in do topSRT <- Stream.mapAccumL run_pipeline initTopSRT ppr_stream1
                Stream.yield (srtToData topSRT)

    let
        dump2 a = do dumpIfSet_dyn dflags Opt_D_dump_cmm "Output Cmm" $ ppr a
                     return a

        ppr_stream2 = Stream.mapM dump2 pipeline_stream

    return ppr_stream2



myCoreToStg :: DynFlags -> Module -> CoreProgram
            -> IO ( [StgBinding] -- output program
                  , CollectedCCs) -- cost centre info (declared and used)
myCoreToStg dflags this_mod prepd_binds = do
    stg_binds
        <- {-# SCC "Core2Stg" #-}
           coreToStg dflags this_mod prepd_binds

    (stg_binds2, cost_centre_info)
        <- {-# SCC "Stg2Stg" #-}
           stg2stg dflags this_mod stg_binds

    return (stg_binds2, cost_centre_info)

compileStub :: HscEnv -> FilePath -> IO FilePath
compileStub hsc_env stub_c = do
        (_, stub_o) <- runPipeline StopLn hsc_env (stub_c,Nothing)  Nothing
                                   Temporary Nothing{-no ModLocation-} Nothing

        return stub_o

touchObjectFile :: DynFlags -> FilePath -> IO ()
touchObjectFile dflags path = do
  createDirectoryIfMissing True $ takeDirectory path
  SysTools.touch dflags "Touching object file" path


-- | Throw some errors.
throwErrors :: ErrorMessages -> Hsc a
throwErrors = liftIO . throwIO . mkSrcErr

-- | Run a compilation pipeline, consisting of multiple phases.
--
-- This is the interface to the compilation pipeline, which runs
-- a series of compilation steps on a single source file, specifying
-- at which stage to stop.
--
-- The DynFlags can be modified by phases in the pipeline (eg. by
-- OPTIONS_GHC pragmas), and the changes affect later phases in the
-- pipeline.
runPipeline
  :: Phase                      -- ^ When to stop
  -> HscEnv                     -- ^ Compilation environment
  -> (FilePath,Maybe PhasePlus) -- ^ Input filename (and maybe -x suffix)
  -> Maybe FilePath             -- ^ original basename (if different from ^^^)
  -> PipelineOutput             -- ^ Output filename
  -> Maybe ModLocation          -- ^ A ModLocation, if this is a Haskell module
  -> Maybe FilePath             -- ^ stub object, if we have one
  -> IO (DynFlags, FilePath)    -- ^ (final flags, output filename)
runPipeline stop_phase hsc_env0 (input_fn, mb_phase)
             mb_basename output maybe_loc maybe_stub_o

    = do let
             dflags0 = hsc_dflags hsc_env0

             -- Decide where dump files should go based on the pipeline output
             dflags = dflags0 { dumpPrefix = Just (basename ++ ".") }
             hsc_env = hsc_env0 {hsc_dflags = dflags}

             (input_basename, suffix) = splitExtension input_fn
             suffix' = drop 1 suffix -- strip off the .
             basename | Just b <- mb_basename = b
                      | otherwise             = input_basename

             -- If we were given a -x flag, then use that phase to start from
             start_phase = fromMaybe (RealPhase (startPhase suffix')) mb_phase

             isHaskell (RealPhase (Unlit _)) = True
             isHaskell (RealPhase (Cpp   _)) = True
             isHaskell (RealPhase (HsPp  _)) = True
             isHaskell (RealPhase (DriverPhases.Hsc   _)) = True
             isHaskell (HscOut {})           = True
             isHaskell _                     = False

             isHaskellishFile = isHaskell start_phase

             env = PipeEnv{ pe_isHaskellishFile = isHaskellishFile,
                            stop_phase,
                            src_filename = input_fn,
                            src_basename = basename,
                            src_suffix = suffix',
                            output_spec = output }

         -- We want to catch cases of "you can't get there from here" before
         -- we start the pipeline, because otherwise it will just run off the
         -- end.
         --
         -- There is a partial ordering on phases, where A < B iff A occurs
         -- before B in a normal compilation pipeline.

         let happensBefore' = happensBefore dflags
         case start_phase of
             RealPhase start_phase' ->
                 when (not (start_phase' `happensBefore'` stop_phase)) $
                       throwGhcExceptionIO (UsageError
                                   ("cannot compile this file to desired target: "
                                      ++ input_fn))
             HscOut {} -> return ()

         debugTraceMsg dflags 4 (text "Running the pipeline")
         r <- runPipeline' start_phase hsc_env env input_fn
                           maybe_loc maybe_stub_o

         -- If we are compiling a Haskell module, and doing
         -- -dynamic-too, but couldn't do the -dynamic-too fast
         -- path, then rerun the pipeline for the dyn way
         let dflags = extractDynFlags hsc_env
         -- NB: Currently disabled on Windows (ref #7134, #8228, and #5987)
         when (not $ platformOS (targetPlatform dflags) == OSMinGW32) $ do
           when isHaskellishFile $ whenCannotGenerateDynamicToo dflags $ do
               debugTraceMsg dflags 4
                   (text "Running the pipeline again for -dynamic-too")
               let dflags' = dynamicTooMkDynamicDynFlags dflags
               hsc_env' <- newHscEnv dflags'
               _ <- runPipeline' start_phase hsc_env' env input_fn
                                 maybe_loc maybe_stub_o
               return ()
         return r

runPipeline'
  :: PhasePlus                  -- ^ When to start
  -> HscEnv                     -- ^ Compilation environment
  -> PipeEnv
  -> FilePath                   -- ^ Input filename
  -> Maybe ModLocation          -- ^ A ModLocation, if this is a Haskell module
  -> Maybe FilePath             -- ^ stub object, if we have one
  -> IO (DynFlags, FilePath)    -- ^ (final flags, output filename)
runPipeline' start_phase hsc_env env input_fn
             maybe_loc maybe_stub_o
  = do
  -- Execute the pipeline...
  let state = PipeState{ hsc_env, maybe_loc, maybe_stub_o = maybe_stub_o }

  evalP (pipeLoop start_phase input_fn) env state

-- ---------------------------------------------------------------------------
-- outer pipeline loop

-- | pipeLoop runs phases until we reach the stop phase
pipeLoop :: PhasePlus -> FilePath -> CompPipeline (DynFlags, FilePath)
pipeLoop phase input_fn = do
  env <- getPipeEnv
  dflags <- getDynFlags
  let happensBefore' = happensBefore dflags
      stopPhase = stop_phase env
  case phase of
   RealPhase realPhase | realPhase `eqPhase` stopPhase            -- All done
     -> -- Sometimes, a compilation phase doesn't actually generate any output
        -- (eg. the CPP phase when -fcpp is not turned on).  If we end on this
        -- stage, but we wanted to keep the output, then we have to explicitly
        -- copy the file, remembering to prepend a {-# LINE #-} pragma so that
        -- further compilation stages can tell what the original filename was.
        case output_spec env of
        Temporary ->
            return (dflags, input_fn)
        output ->
            do pst <- getPipeState
               final_fn <- liftIO $ getOutputFilename
                                        stopPhase output (src_basename env)
                                        dflags stopPhase (maybe_loc pst)
               when (final_fn /= input_fn) $ do
                  let msg = ("Copying `" ++ input_fn ++"' to `" ++ final_fn ++ "'")
                      line_prag = Just ("{-# LINE 1 \"" ++ src_filename env ++ "\" #-}\n")
                  liftIO $ copyWithHeader dflags msg line_prag input_fn final_fn
               return (dflags, final_fn)


     | not (realPhase `happensBefore'` stopPhase)
        -- Something has gone wrong.  We'll try to cover all the cases when
        -- this could happen, so if we reach here it is a panic.
        -- eg. it might happen if the -C flag is used on a source file that
        -- has {-# OPTIONS -fasm #-}.
     -> panic ("pipeLoop: at phase " ++ show realPhase ++
           " but I wanted to stop at phase " ++ show stopPhase)

   _
     -> do liftIO $ debugTraceMsg dflags 4
                                  (ptext (sLit "Running phase") <+> ppr phase)
           (next_phase, output_fn) <- runHookedPhase phase input_fn dflags
           r <- pipeLoop next_phase output_fn
           case phase of
               HscOut {} ->
                   whenGeneratingDynamicToo dflags $ do
                       setDynFlags $ dynamicTooMkDynamicDynFlags dflags
                       -- TODO shouldn't ignore result:
                       _ <- pipeLoop phase input_fn
                       return ()
               _ ->
                   return ()
           return r

runHookedPhase :: PhasePlus -> FilePath -> DynFlags
               -> CompPipeline (PhasePlus, FilePath)
runHookedPhase pp input dflags =
  lookupHook runPhaseHook runPhase dflags pp input dflags

getOutputFilename
  :: Phase -> PipelineOutput -> String
  -> DynFlags -> Phase{-next phase-} -> Maybe ModLocation -> IO FilePath
getOutputFilename stop_phase output basename dflags next_phase maybe_location
 | is_last_phase, Persistent   <- output = persistent_fn
 | is_last_phase, SpecificFile <- output = case outputFile dflags of
                                           Just f -> return f
                                           Nothing ->
                                               panic "SpecificFile: No filename"
 | keep_this_output                      = persistent_fn
 | otherwise                             = newTempName dflags suffix
    where
          hcsuf      = hcSuf dflags
          odir       = objectDir dflags
          osuf       = objectSuf dflags
          keep_hc    = gopt Opt_KeepHcFiles dflags
          keep_s     = gopt Opt_KeepSFiles dflags
          keep_bc    = gopt Opt_KeepLlvmFiles dflags

          myPhaseInputExt HCc       = hcsuf
          myPhaseInputExt MergeStub = osuf
          myPhaseInputExt StopLn    = osuf
          myPhaseInputExt other     = phaseInputExt other

          is_last_phase = next_phase `eqPhase` stop_phase

          -- sometimes, we keep output from intermediate stages
          keep_this_output =
               case next_phase of
                       As      | keep_s     -> True
                       LlvmOpt | keep_bc    -> True
                       HCc     | keep_hc    -> True
                       _other               -> False

          suffix = myPhaseInputExt next_phase

          -- persistent object files get put in odir
          persistent_fn
             | StopLn <- next_phase = return odir_persistent
             | otherwise            = return persistent

          persistent = basename <.> suffix

          odir_persistent
             | Just loc <- maybe_location = ml_obj_file loc
             | Just d <- odir = d </> persistent
             | otherwise      = persistent

logWarnings :: WarningMessages -> Hsc ()
logWarnings w = HscTypes.Hsc $ \_ w0 -> return ((), w0 `unionBags` w)
