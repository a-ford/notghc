--------------------------------------------------------------------------------
-- | Call into the Haskell LLVM API to generate LLVM bitcode.
--

module Llvm.CodeOutput where


-- import ErrUtils
-- import Outputable

import Llvm.AbsSyn as AbsSyn
import Llvm.MetaData
import Llvm.Types
import Llvm.TypeConversions

import DynFlags
import Unique
import FastString

import LLVM.General.AST as AST
import qualified LLVM.General.AST.Global as G
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST.InlineAssembly as IA

import Data.Maybe

--------------------------------------------------------------------------------
-- * Top Level Output functions
--------------------------------------------------------------------------------

-- unused
-- | Output out a whole LLVM module.
outputLlvmModule :: LlvmModule -> DynFlags -> Module
outputLlvmModule (LlvmModule comments aliases meta globals decls funcs) dflags
    = Module {
        moduleName = "<module-name-here>",
        moduleDataLayout = Just (platformToDataLayout (targetPlatform dflags)),
        moduleTargetTriple =
            Just (platformToTargetTriple (targetPlatform dflags)),
        moduleDefinitions = concat [alis, metas, glos, decs, funs]
      }
    where alis  = outputLlvmAliases aliases
          metas = outputLlvmMetas meta
          glos  = outputLlvmGlobals globals
          decs  = outputLlvmFunctionDecls decls
          funs  = outputLlvmFunctions funcs

-- | Output out a list of global mutable variable definitions
outputLlvmGlobals :: [LMGlobal] -> [Definition]
outputLlvmGlobals ls = map outputLlvmGlobal ls

-- | Output out a global mutable variable definition
outputLlvmGlobal :: LMGlobal -> Definition
outputLlvmGlobal (LMGlobal var@(LMGlobalVar name ty link sec ali con) dat) =
    let section = (Just . unpackFS) =<< sec
        alignment = maybe 0 fromIntegral ali
        init = case dat of
                 Just stat -> Just (llvmStaticToConstant stat)
                 Nothing   -> Just (C.Null (llvmTypeToType (pLower ty)))
        ty' = case dat of
                 Just stat -> llvmTypeToType (getStatType stat)
                 Nothing   -> llvmTypeToType (pLower ty)
        name' = llvmVarToName var
        link' = llvmLinkageTypeToLinkage link
    in
      if con == Alias then
          GlobalDefinition
          (globalAliasDefaults {
               G.name = name',
               G.linkage = link',
               G.type' = ty',
               G.aliasee = fromJust init
           })
      else
          GlobalDefinition
          (globalVariableDefaults {
             G.name = name',
             G.linkage = link',
             G.isConstant = (con == Constant),
             G.type' = ty',
             G.initializer = init,
             G.section = section,
             G.alignment = alignment
           })
outputLlvmGlobal (LMGlobal var val) =
    error "outputLlvmGlobal: Non Global variable output as global."

-- | Output out a list of LLVM type aliases.
outputLlvmAliases :: [LlvmAlias] -> [Definition]
outputLlvmAliases alis = map outputLlvmAlias alis

-- | Output out an LLVM type alias.
outputLlvmAlias :: LlvmAlias -> Definition
outputLlvmAlias (name, ty) =
    TypeDefinition (mkName name) (Just (llvmTypeToType ty))

-- | Output out a list of LLVM metadata.
outputLlvmMetas :: [MetaDecl] -> [Definition]
outputLlvmMetas metas = map (outputLlvmMeta ) metas

-- | Output out an LLVM metadata definition
outputLlvmMeta :: MetaDecl -> Definition
outputLlvmMeta  (MetaUnamed n m) =
    MetadataNodeDefinition (MetadataNodeID (fromIntegral n))
                               [(Just (outputLlvmMetaExpr  m))]
outputLlvmMeta  (MetaNamed n m) =
    NamedMetadataDefinition (unpackFS n)
                                (map (MetadataNodeID . fromIntegral) m)

-- | Output an LLVM metadata value.
outputLlvmMetaExpr :: MetaExpr -> Operand
outputLlvmMetaExpr = metaExprToOperand

-- | Output out a list of function definitions.
outputLlvmFunctions :: LlvmFunctions -> [Definition]
outputLlvmFunctions  funcs = map outputLlvmFunction funcs

-- | Output out a function definition.
-- body = [LlvmBlock] = [LlvmBlock {LlvmBlockId [LlvmStatement]}]
outputLlvmFunction :: LlvmFunction -> Definition
outputLlvmFunction
  (LlvmFunction dec@(LlvmFunctionDecl name link cc retTy vArgs params ali)
                args attrs sec body)
    =
      let baseDecl = outputLlvmFunctionDeclBase dec
          argNames = map (Left . unpackFS) args
          parameters = if (length argNames) == (length params)
                       then zipWith llvmParameterToNamedParameter
                                      params argNames
                       else
                           error $ "outputLlvmFunction: Number of arg names" ++
                                   " supplied does not match type signature."
      in GlobalDefinition $
           baseDecl {
               G.parameters = (parameters, vArgs == VarArgs),
               G.functionAttributes = map llvmFuncAttrToFunctionAttribute attrs,
               G.section = (Just . unpackFS) =<< sec,
               G.basicBlocks = outputLlvmBlocks body
             }

-- | Output out a list of function declaration.
outputLlvmFunctionDecls :: LlvmFunctionDecls -> [Definition]
outputLlvmFunctionDecls  decs = map outputLlvmFunctionDecl decs

-- | Output out a function declaration.
-- Declarations define the function type but don't define the actual body of
-- the function.
outputLlvmFunctionDecl :: LlvmFunctionDecl -> Definition
outputLlvmFunctionDecl dec = GlobalDefinition (outputLlvmFunctionDeclBase dec)

-- | Output a function declaration, but don't wrap it as a Definition
outputLlvmFunctionDeclBase :: LlvmFunctionDecl -> Global
outputLlvmFunctionDeclBase
  (LlvmFunctionDecl name link cc retTy vArgs params ali)
    =
      let ali' = maybe 0 fromIntegral ali
          -- Function declarations have no argument names,
          -- we only care about the types here.
          parameters = zipWith llvmParameterToNamedParameter
                                 params (repeat (Left ""))
      in functionDefaults {
               G.linkage = llvmLinkageTypeToLinkage link,
               G.callingConvention = llvmCallConventionToCallingConvention cc,
               G.returnType = llvmTypeToType retTy,
               G.name = mkName name,
               G.parameters = (parameters, vArgs == VarArgs),
               G.alignment = ali'
             }

-- | Output out a list of LLVM blocks.
outputLlvmBlocks :: LlvmBlocks -> [BasicBlock]
outputLlvmBlocks  blocks = map outputLlvmBlock blocks

partitionEithers :: [Either a b] -> ([a], [b])
partitionEithers [] = ([], [])
partitionEithers ((Left x):zs) =
    let (xs, ys) = partitionEithers zs in (x:xs, ys)
partitionEithers ((Right y):zs) =
    let (xs, ys) = partitionEithers zs in (xs, y:ys)

head' :: [a] -> a
head' [x] = x
head' _ = error "Fatal error in head'"

-- | Output out an LLVM block.
-- It must be part of a function definition.
outputLlvmBlock :: LlvmBlock -> BasicBlock
outputLlvmBlock  (LlvmBlock blockId stmts) =
    BasicBlock name instrs (head' terminator)
        where
          name = Name (show blockId)
          -- terminator had better be a singleton list here,
          -- else the block is invalid
          (instrs, terminator) =
              partitionEithers (map outputLlvmStatement stmts)

{-  let isLabel (MkLabel _) = True
      isLabel _           = False
      (block, rest)       = break isLabel stmts
      outputRest = case rest of
                     (MkLabel id):xs -> outputLlvmBlock (LlvmBlock id xs)
                     _               -> ()
  in do mapM_ outputLlvmStatement block
        outputRest
-}

-- | Output out an LLVM block label.
--outputLlvmBlockLabel :: LlvmBlockId -> Name
--outputLlvmBlockLabel blockId = Name (show blockId)

-- | Output an LLVM statement.
outputLlvmStatement ::  LlvmStatement ->
                        Either (Named Instruction) (Named Terminator)
outputLlvmStatement  stmt =
  case stmt of
    MetaStmt    meta s        -> outputMetaStatement  meta s
    _                         -> outputMetaStatement  [] stmt

-- Output an LLVM statement with metadata annotations.
-- By making instructions and terminators named, we are able to do assignments.
outputMetaStatement ::  [MetaAnnot] -> LlvmStatement ->
                        Either (Named Instruction) (Named Terminator)
outputMetaStatement  meta stmt =
    case stmt of
      Assignment  dst expr      -> Left $ outputAssignment dst expr meta
      AbsSyn.Fence st ord       -> Left $ outputFence st ord meta
      Branch      target        -> Right $ outputBranch target meta
      BranchIf    cond ifT ifF  -> Right $ outputBranchIf cond ifT ifF meta
      -- We don't need comments
      Comment     comments      ->
          error "outputMetaStatement: Can't generate comments."
      -- We don't need labels either
      MkLabel     label         ->
          error "outputMetaStatement: Can't generate comments."
      AbsSyn.Store value ptr    -> Left $ outputStore value ptr meta
      AbsSyn.Switch scrut def tgs -> Right $ outputSwitch scrut def tgs meta
      Return      result        -> Right $ outputReturn result meta
      Expr        expr          -> Left $ outputMetaExpr meta expr
      AbsSyn.Unreachable        ->
          Right $ Do (AST.Unreachable (outputMetaAnnots  meta)) -- T
      Nop                       -> error "NOP generated as a statement"
      MetaStmt    meta s        -> outputMetaStatement meta s

-- | Output an LLVM expression.
outputLlvmExpression :: LlvmExpression -> Named Instruction
outputLlvmExpression  expr
  = case expr of
      MExpr      meta e           -> outputMetaExpr meta e
      _                           -> outputMetaExpr [] expr

outputMetaExpr :: [MetaAnnot] -> LlvmExpression -> Named Instruction
outputMetaExpr  meta expr =
    case expr of
      AbsSyn.Alloca tp amount        -> outputAlloca tp amount meta
      LlvmOp        op left right    -> outputLlvmMachOp op left right meta
      AbsSyn.Call   tp fp args attrs ->
          outputCall tp fp (map MetaVar args) attrs meta
      CallM         tp fp args attrs -> outputCall tp fp args attrs meta
      Cast          op from to       -> outputCast op from to meta
      Compare       op left right    -> outputCmpOp op left right meta
      Extract       vec idx          -> outputExtract vec idx meta
      Insert        vec elt idx      -> outputInsert vec elt idx meta
      GetElemPtr    inb ptr indexes  -> outputGetElementPtr inb ptr indexes meta
      AbsSyn.Load   ptr              -> outputLoad ptr meta
      Malloc        tp amount        -> outputMalloc tp amount meta
      AbsSyn.Phi    tp precessors    -> outputPhi tp precessors meta
      Asm           asm c ty v se sk ->
          error "outputMetaExpr: Assembly not used"
      MExpr         meta e           -> outputMetaExpr meta e

--------------------------------------------------------------------------------
-- * Individual print functions
--------------------------------------------------------------------------------

-- | Should always be a function pointer. So a global var of function type
-- (since globals are always pointers) or a local var of pointer function type.
outputCall :: LlvmCallType -> LlvmVar -> [MetaExpr] -> [LlvmFuncAttr] ->
              [MetaAnnot] -> Named Instruction
outputCall  ct fptr args attrs metas =
  case fptr of
    -- if local var function pointer, unwrap
    LMLocalVar _ (LMPointer (LMFunction d)) -> ppCall' d

    -- should be function type otherwise
    LMGlobalVar _ (LMFunction d) _ _ _ _    -> ppCall' d

    -- not pointer or function, so error
    _other -> error $ "outputCall called with non LMFunction type!\nMust be "
                ++ " called with either global var of function type or "
                ++ "local var of pointer function type."

    where
        ppCall' decl@(LlvmFunctionDecl name _ cc ret varargs params _) =
            {- IGNORED:
                - map fst params (arg types)
                - varargs
                - Function type, including lifting to ptr type -}
            let tc = ct == TailCall
                cc' = llvmCallConventionToCallingConvention cc
                args' = map outputLlvmMetaExpr args
                pattrs =
                    map (map llvmParamAttrToParameterAttribute . snd) params
                attrs' = map llvmFuncAttrToFunctionAttribute attrs
                metas' = outputMetaAnnots metas
            in  Do $ AST.Call { isTailCall = tc,
                                callingConvention = cc',
                                returnAttributes = [],
                                function = Right (llvmVarToOperand fptr),
                                arguments = zip args' pattrs,
                                functionAttributes = attrs',
                                metadata = metas'
                              }



outputLlvmMachOp ::  LlvmMachOp -> LlvmVar -> LlvmVar ->
                     [MetaAnnot] -> Named Instruction
outputLlvmMachOp  op left right metas =
    Do $
       (case op of
          LM_MO_Add  -> Add False False left' right' metas'
          LM_MO_Sub  -> Sub False False left' right' metas'
          LM_MO_Mul  -> Mul False False left' right' metas'
          LM_MO_UDiv -> UDiv False left' right' metas'
          LM_MO_SDiv -> SDiv False left' right' metas'
          LM_MO_URem -> URem left' right' metas'
          LM_MO_SRem -> SRem left' right' metas'
          LM_MO_FAdd -> FAdd left' right' metas'
          LM_MO_FSub -> FSub left' right' metas'
          LM_MO_FMul -> FMul left' right' metas'
          LM_MO_FDiv -> FDiv left' right' metas'
          LM_MO_FRem -> FRem left' right' metas'
          LM_MO_Shl  -> Shl False False left' right' metas'
          LM_MO_LShr -> LShr False left' right' metas'
          LM_MO_AShr -> AShr False left' right' metas'
          LM_MO_And  -> And left' right' metas'
          LM_MO_Or   -> Or left' right' metas'
          LM_MO_Xor  -> Xor left' right' metas')
                where left' = llvmVarToOperand  left
                      right' = llvmVarToOperand  right
                      metas' = outputMetaAnnots  metas


outputCmpOp ::  LlvmCmpOp -> LlvmVar -> LlvmVar ->
                [MetaAnnot] -> Named Instruction
outputCmpOp  op left right metas =
    let
        left' = llvmVarToOperand  left
        right' = llvmVarToOperand  right
        lty = getVarType left
        rty = getVarType right
        metas' = outputMetaAnnots  metas
    in if isInt lty && isInt rty
       then Do $ ICmp ((fromJust . llvmCmpOpToIntegerPredicate) op)
                        left' right' metas'
       else if isFloat lty && isFloat rty
            then Do $ FCmp ((fromJust . llvmCmpOpToFloatingPointPredicate) op)
                             left' right' metas'
            else error $
                     "outputCmpOp: Cannot compare incomparable types " ++
                     show lty ++ ", " ++ show rty

outputAssignment ::  LlvmVar -> LlvmExpression -> [MetaAnnot] ->
                     Named Instruction
outputAssignment  var expr metas =
    case outputLlvmExpression  (MExpr metas expr) of
      Do expr' -> (llvmVarToName var) := expr'
      _        -> error "Named expression must be a 'Do'"

outputSyncOrdering :: LlvmSyncOrdering -> MemoryOrdering
outputSyncOrdering SyncUnord     = Unordered
outputSyncOrdering SyncMonotonic = Monotonic
outputSyncOrdering SyncAcquire   = Acquire
outputSyncOrdering SyncRelease   = Release
outputSyncOrdering SyncAcqRel    = AcquireRelease
outputSyncOrdering SyncSeqCst    = SequentiallyConsistent

-- The st (single-thread) boolean might need to be negated.
outputFence :: Bool -> LlvmSyncOrdering -> [MetaAnnot] -> Named Instruction
outputFence  st ord metas = Do $ AST.Fence atom metas'
    where atom = Atomicity st (outputSyncOrdering ord)
          metas' = outputMetaAnnots  metas

-- XXX: On x86, vector types need to be 16-byte aligned for aligned access, but
-- we have no way of guaranteeing that this is true with GHC (we would need to
-- modify the layout of the stack and closures, change the storage manager,
-- etc.). So, we blindly tell LLVM that *any* vector store or load could be
-- unaligned. In the future we may be able to guarantee that certain vector
-- access patterns are aligned, in which case we will need a more granular way
-- of specifying alignment.

outputLoad :: LlvmVar -> [MetaAnnot] -> Named Instruction
outputLoad  var metas
    -- We say the load is non-volatile and non-atomic.
    | isVecPtrVar var = Do $ AST.Load False op Nothing 1 metas'
    | otherwise       = Do $ AST.Load False op Nothing 0 metas'
  where
    isVecPtrVar = isVector . pLower . getVarType
    op = llvmVarToOperand  var
    metas' = outputMetaAnnots  metas

outputStore :: LlvmVar -> LlvmVar -> [MetaAnnot] -> Named Instruction
outputStore  val dst metas
    -- We say the store is non-volatile and non-atomic.
    | isVecPtrVar dst = Do $ AST.Store False dstOp valOp Nothing 1 metas'
    | otherwise       = Do $ AST.Store False dstOp valOp Nothing 0 metas'
  where
    isVecPtrVar :: LlvmVar -> Bool
    isVecPtrVar = isVector . pLower . getVarType
    dstOp = llvmVarToOperand  dst
    valOp = llvmVarToOperand  val
    metas' = outputMetaAnnots  metas

outputCast ::  LlvmCastOp -> LlvmVar -> LlvmType ->
               [MetaAnnot] -> Named Instruction
outputCast  op var ty metas =
    Do $ (case op of
            LM_Trunc    -> Trunc operand ty' metas'
            LM_Zext     -> ZExt operand ty' metas'
            LM_Sext     -> SExt operand ty' metas'
            LM_Fptrunc  -> FPTrunc operand ty' metas'
            LM_Fpext    -> FPToUI operand ty' metas'
            LM_Fptoui   -> FPToUI operand ty' metas'
            LM_Fptosi   -> FPToSI operand ty' metas'
            LM_Uitofp   -> UIToFP operand ty' metas'
            LM_Sitofp   -> SIToFP operand ty' metas'
            LM_Ptrtoint -> PtrToInt operand ty' metas'
            LM_Inttoptr -> IntToPtr operand ty' metas'
            LM_Bitcast  -> BitCast operand ty' metas')
           where
             operand = llvmVarToOperand var
             ty' = llvmTypeToType ty
             metas' = outputMetaAnnots  metas

-- As of LLVM 3.0, malloc is no longer an instruction of the LLVM IR.
outputMalloc :: LlvmType -> Int -> [MetaAnnot] -> Named Instruction --'done'
outputMalloc tp amount metas = error "malloc not implemented"

outputAlloca :: LlvmType -> Int -> [MetaAnnot] -> Named Instruction
outputAlloca  ty amount metas = Do $ AST.Alloca ty' (Just numElems) 0 metas'
    where ty' = llvmTypeToType ty
          -- The number of elements of type ty' to allocate space for
          numElems = ConstantOperand (C.Int 32 (toInteger amount))
          metas' = outputMetaAnnots  metas

outputGetElementPtr ::  Bool -> LlvmVar -> [LlvmVar] ->
                        [MetaAnnot] -> Named Instruction
outputGetElementPtr  inb ptr idx metas = Do $ GetElementPtr inb ptr' idx' metas'
    where ptr' = llvmVarToOperand  ptr
          idx' = map (llvmVarToOperand ) idx
          metas' = outputMetaAnnots  metas

outputReturn :: Maybe LlvmVar -> [MetaAnnot] -> Named Terminator
outputReturn  var metas = Do $ Ret var' metas'
    where var' = (Just . llvmVarToOperand) =<< var
          metas' = outputMetaAnnots  metas

-- Unconditional branch to target
outputBranch :: LlvmVar -> [MetaAnnot] -> Named Terminator
outputBranch  var metas = Do $ Br name metas'
    where name = llvmVarToName var
          metas' = outputMetaAnnots  metas

outputBranchIf ::  LlvmVar -> LlvmVar -> LlvmVar ->
                   [MetaAnnot] -> Named Terminator
outputBranchIf  cond trueT falseT metas =
    Do $ CondBr cond' trueT' falseT' metas'
    where cond' = llvmVarToOperand  cond
          trueT' = llvmVarToName trueT
          falseT' = llvmVarToName falseT
          metas' = outputMetaAnnots  metas

outputPhi :: LlvmType -> [(LlvmVar,LlvmVar)] -> [MetaAnnot] -> Named Instruction
outputPhi  ty preds metas = Do $ AST.Phi ty' preds' metas'
    where ty' = llvmTypeToType ty
          preds' = map (\(op,name) -> (llvmVarToOperand  op, llvmVarToName name)) preds
          errStr = concat $ map (\(op,name) -> show op) preds
          metas' = outputMetaAnnots  metas

outputSwitch ::  LlvmVar -> LlvmVar -> [(LlvmVar,LlvmVar)] ->
                 [MetaAnnot] -> Named Terminator
outputSwitch  op dflt targets metas = Do $ AST.Switch op' dflt' targets' metas'
    where op' = llvmVarToOperand op
          dflt' = llvmVarToName dflt
          targets' =
              map (\(con, name) -> (llvmVarToConstant con, llvmVarToName name))
                  targets
          metas' = outputMetaAnnots  metas

outputAsm ::  LMString -> LMString -> LlvmType -> [LlvmVar] ->
              Bool -> Bool -> IA.InlineAssembly
outputAsm asm constraints rty vars sideeffect alignstack =
    IA.InlineAssembly {
      IA.type' = llvmTypeToType rty,
      IA.assembly = unpackFS asm,
      IA.constraints = unpackFS constraints,
      IA.hasSideEffects = sideeffect,
      IA.alignStack= alignstack,
      IA.dialect = IA.ATTDialect
   }

-- Get a value from a vector
outputExtract :: LlvmVar -> LlvmVar -> [MetaAnnot] -> Named Instruction
outputExtract  vec idx metas = Do $ ExtractElement vec' idx' metas'
    where vec' = llvmVarToOperand vec
          idx' = llvmVarToOperand idx
          metas' = outputMetaAnnots  metas

-- Insert a value into a vector
outputInsert ::  LlvmVar -> LlvmVar -> LlvmVar ->
                 [MetaAnnot] -> Named Instruction
outputInsert  vec elt idx metas = Do $ InsertElement vec' elt' idx' metas'
    where vec' = llvmVarToOperand vec
          elt' = llvmVarToOperand elt
          idx' = llvmVarToOperand idx
          metas' = outputMetaAnnots  metas

outputMetaAnnots :: [MetaAnnot] -> InstructionMetadata
outputMetaAnnots  metas = (concat . map (outputMetaAnnot )) metas

outputMetaAnnot :: MetaAnnot -> InstructionMetadata
outputMetaAnnot  (MetaAnnot str expr) =
    [(unpackFS str, metaExprToMetadataNode expr)]