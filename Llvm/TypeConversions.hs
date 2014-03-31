--------------------------------------------------------------------------------
-- | Conversions from backend types to llvm-general AST types
--

module Llvm.TypeConversions where

import Llvm.AbsSyn as AbsSyn
import Llvm.MetaData
import Llvm.Types as Types

import LLVM.General.AST as AST
import qualified LLVM.General.Target as T
import qualified LLVM.General.AST.Linkage as L
import qualified LLVM.General.AST.Global as G
import qualified LLVM.General.AST.Visibility as V
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST.Attribute as A
import qualified LLVM.General.AST.Float as F
import qualified LLVM.General.AST.AddrSpace as AS
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST.IntegerPredicate as IP
import qualified LLVM.General.AST.FloatingPointPredicate as FPP
import qualified LLVM.General.AST.Operand as O
import qualified LLVM.General.AST.DataLayout as DL

import FastString
import Platform

import Unique
import UniqSupply
import Data.Word
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad.Error as Err

import GHC.Float

-- Many of these functions look kind of like a non-polymorphic id

llvmLinkageTypeToLinkage :: LlvmLinkageType -> L.Linkage
llvmLinkageTypeToLinkage link =
    case link of
      Types.Internal -> L.Internal
      Types.LinkOnce -> L.LinkOnce
      Types.Weak -> L.Weak
      Types.Appending -> L.Appending
      Types.ExternWeak -> L.ExternWeak
      -- external is the default which ExternallyDefault should translate to,
      -- but there is no explicit default value in llvm-general
      Types.ExternallyVisible -> L.External
      Types.External -> L.External
      Types.Private -> L.Private

llvmVarToGlobal :: LlvmVar -> Bool -> G.Global
llvmVarToGlobal var@(LMGlobalVar str ty link sec ali con) alias =
    let name = mkName str
        linkage = llvmLinkageTypeToLinkage link
        visibility = V.Default
        type' = llvmTypeToType ty -- Different for alias vs "real"?
    in if alias then
           G.GlobalAlias {
                  G.name = name,
                  G.linkage = linkage,
                  G.visibility = visibility,
                  G.type' = type',
                  G.aliasee = C.GlobalReference name -- surely wrong
                }
       else
           G.GlobalVariable {
                  G.name = name,
                  G.linkage = linkage,
                  G.visibility = visibility,
                  G.isThreadLocal = False,
                  G.addrSpace = AS.AddrSpace 0, -- Default address space
                  G.hasUnnamedAddr = False,
                  G.isConstant = (con == Constant),
                  G.type' = type',
                  G.initializer = Nothing,
                  G.section = (Just . unpackFS) =<< sec,
                  G.alignment = if ali==Nothing then 0 else (fromIntegral . fromJust) ali
                }
llvmVarToGlobal (LMLocalVar uniq ty) alias = error "undefined error"
llvmVarToGlobal (LMNLocalVar str ty) alias = error "undefined error"
llvmVarToGlobal (LMLitVar lit) alias = error "undefined error"


floatToSomeFloat :: Double -> LlvmType -> F.SomeFloat
floatToSomeFloat d ty =
    case ty of
      Types.LMFloat    -> F.Single (narrowFp d)
      Types.LMDouble   -> F.Double d
      -- These are unimplemented, but aren't generated in the first place.
      -- X86_FP80 {- need to split into a 16 and 64 bit word -}
      Types.LMFloat80  -> error "TypeConversions: X86 specific 80 bit floats not implemented."
      -- Quadruple {- need to split into two 64 bit words -}
      Types.LMFloat128 -> error "TypeConversions: 128 bit floats not implemented."
      t          -> error $ "Not an floating type: " ++ show t

llvmTypeToType :: LlvmType -> AST.Type
llvmTypeToType ty =
    case ty of
      Types.LMInt width -> IntegerType (fromIntegral width)
      Types.LMFloat -> FloatingPointType 32 IEEE
      Types.LMDouble -> FloatingPointType 64 IEEE
      Types.LMFloat80 -> FloatingPointType 80 DoubleExtended
      Types.LMFloat128 -> FloatingPointType 128 IEEE
      Types.LMPointer ty -> PointerType (llvmTypeToType ty) (AS.AddrSpace 0) -- default address space
      Types.LMArray len ty -> ArrayType (fromIntegral len) (llvmTypeToType ty)
      Types.LMVector len typ -> VectorType (fromIntegral len) (llvmTypeToType ty)
      Types.LMLabel -> error "undefined error"
      Types.LMVoid -> VoidType
      Types.LMStruct tys -> StructureType True (map llvmTypeToType tys) -- packed
      Types.LMAlias ali -> NamedTypeReference (Name ((unpackFS . fst) ali))
      Types.LMMetadata -> MetadataType
      Types.LMFunction decl@(LlvmFunctionDecl name link cc ty vArgs params ali) -> FunctionType (llvmTypeToType ty) (map (llvmTypeToType . fst) params) (vArgs == VarArgs)

llvmStaticToConstant :: LlvmStatic -> C.Constant
llvmStaticToConstant stat =
    case stat of
      Types.LMComment str -> error "llvmStaticToConstant: comments unimplemented"
      Types.LMStaticLit lit -> llvmLitToConstant lit
      Types.LMUninitType ty -> C.Undef (llvmTypeToType ty)
      Types.LMStaticStr str ty -> error "llvmStaticToConstant: No conversion defined for LMStaticStr"
      -- The type here is of the array, not of its elements.
      -- Therefore we must get the type of the elements.
      Types.LMStaticArray stats ty -> C.Array (llvmTypeToType (getElemType ty)) (map llvmStaticToConstant stats)
      Types.LMStaticStruc stats ty -> C.Struct Nothing True (map llvmStaticToConstant stats) -- packed
      -- Sticking in a pVarLower here made absolutely no difference (???)
      Types.LMStaticPointer var -> llvmVarToConstant var -- very questionable

      -- static expressions
      Types.LMBitc stat ty -> C.BitCast (llvmStaticToConstant stat) (llvmTypeToType ty)
      Types.LMPtoI stat ty -> C.PtrToInt (llvmStaticToConstant stat) (llvmTypeToType ty)
      Types.LMAdd statL statR -> C.Add False False (llvmStaticToConstant statL) (llvmStaticToConstant statR) -- bools are for no (un)signed wrap
      Types.LMSub statL statR -> C.Sub False False (llvmStaticToConstant statL) (llvmStaticToConstant statR) -- bools are for no (un)signed wrap

llvmCallConventionToCallingConvention :: LlvmCallConvention -> CC.CallingConvention
llvmCallConventionToCallingConvention conv =
    case conv of
      CC_Ccc -> CC.C
      CC_Fastcc -> CC.Fast
      CC_Coldcc -> CC.Cold
      CC_Ncc 10 -> CC.GHC
      CC_X86_Stdcc -> CC.Numbered 64
      CC_Ncc code -> CC.Numbered (fromIntegral code)

llvmFuncAttrToFunctionAttribute :: LlvmFuncAttr -> A.FunctionAttribute
llvmFuncAttrToFunctionAttribute attr =
    case attr of
      AlwaysInline -> A.AlwaysInline
      InlineHint -> A.InlineHint
      NoInline -> A.NoInline
      OptSize -> A.OptimizeForSize
      NoReturn -> A.NoReturn
      NoUnwind -> A.NoUnwind
      ReadNone -> A.ReadNone
      ReadOnly -> A.ReadOnly
      Ssp -> A.StackProtect
      SspReq -> A.StackProtectReq
      NoRedZone -> A.NoRedZone
      NoImplicitFloat -> A.NoImplicitFloat
      Naked -> A.Naked

llvmParamAttrToParameterAttribute :: LlvmParamAttr -> A.ParameterAttribute
llvmParamAttrToParameterAttribute attr =
    case attr of
      ZeroExt -> A.ZeroExt
      SignExt -> A.SignExt
      InReg -> A.InReg
      ByVal -> A.ByVal
      SRet -> A.SRet
      NoAlias -> A.NoAlias
      NoCapture -> A.NoCapture
      Nest -> A.Nest

llvmCmpOpToPredicate :: LlvmCmpOp -> Either IP.IntegerPredicate FPP.FloatingPointPredicate
llvmCmpOpToPredicate op =
    let intOp = llvmCmpOpToIntegerPredicate op
        fpOp  = llvmCmpOpToFloatingPointPredicate op
    in if intOp /= Nothing then Left (fromJust intOp) else Right (fromJust fpOp)

-- Convert comparator operators to integer predicates
llvmCmpOpToIntegerPredicate :: LlvmCmpOp -> Maybe IP.IntegerPredicate
llvmCmpOpToIntegerPredicate op =
    case op of
      LM_CMP_Eq  -> Just IP.EQ
      LM_CMP_Ne  -> Just IP.NE
      LM_CMP_Ugt -> Just IP.UGT
      LM_CMP_Uge -> Just IP.UGE
      LM_CMP_Ult -> Just IP.ULT
      LM_CMP_Ule -> Just IP.ULE
      LM_CMP_Sgt -> Just IP.SGT
      LM_CMP_Sge -> Just IP.SGE
      LM_CMP_Slt -> Just IP.SLT
      LM_CMP_Sle -> Just IP.SLE
      _          -> Nothing

-- The difference between O and U prefixed predicates relates to qNaN (quiet NaN) values
llvmCmpOpToFloatingPointPredicate :: LlvmCmpOp -> Maybe FPP.FloatingPointPredicate
llvmCmpOpToFloatingPointPredicate op =
    case op of
      LM_CMP_Feq -> Just FPP.OEQ
      LM_CMP_Fne -> Just FPP.ONE
      LM_CMP_Fgt -> Just FPP.OGT
      LM_CMP_Fge -> Just FPP.OGE
      LM_CMP_Flt -> Just FPP.OLT
      LM_CMP_Fle -> Just FPP.OLE
      _          -> Nothing


llvmVarToOperand :: LlvmVar -> O.Operand
llvmVarToOperand v@(LMGlobalVar str ty link sec ali con) = ConstantOperand (C.GlobalReference (llvmVarToName v))
-- (mkName str))
-- Hashing a Unique technically doesn't guarantee a unique Int, but we won't get
-- any collisions until 2^32 or 2^64 calls.
llvmVarToOperand v@(LMLocalVar uniq ty) = LocalReference (llvmVarToName v)
--((UnName . fromIntegral . getKey) uniq)
--error $ "llvmVarToOperand " ++ (show uniq)
llvmVarToOperand v@(LMNLocalVar str ty) = LocalReference (llvmVarToName v)
-- error $ "llvmVarToOperand " ++ (unpackFS str)
llvmVarToOperand v@(LMLitVar lit) = ConstantOperand (llvmStaticToConstant (LMStaticLit lit))

llvmParameterToNamedParameter :: LlvmParameter -> Either String Word -> AST.Parameter
llvmParameterToNamedParameter (ty, attrs) name =
    Parameter ty' name' attrs'
        where attrs' = map llvmParamAttrToParameterAttribute attrs
              ty' = llvmTypeToType ty
              name' = either Name UnName name

-- Can we get rid of the IO here? (not without more context to assign unique names)
-- Doesn't matter, we can use the context we have when converting parameters
-- to just call llvmParameterToNamedParameter directly.
llvmParameterToParameter :: LlvmParameter -> IO AST.Parameter
llvmParameterToParameter param =
    do us <- mkSplitUniqSupply 'k'
       let name = uniqFromSupply us
       return (llvmParameterToNamedParameter param (Right (fromIntegral (getKey name))))

platformToDataLayout :: Platform -> DL.DataLayout
platformToDataLayout platform =
    case platform of
      Platform { platformArch = ArchX86, platformOS = OSDarwin } ->
          DL.DataLayout { DL.endianness = Just DL.LittleEndian,
                          DL.stackAlignment = Nothing, -- default stack alignment
                          DL.pointerLayouts = Map.fromList [(AS.AddrSpace 0,
                                                             (32, DL.AlignmentInfo 32 (Just 32)))],
                          DL.typeLayouts = Map.fromList [((DL.IntegerAlign, 1),
                                                          DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 8),
                                                    DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 16),
                                                    DL.AlignmentInfo 16 (Just 16)),
                                                   ((DL.IntegerAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.IntegerAlign, 64),
                                                    DL.AlignmentInfo 32 (Just 64)),
                                                   ((DL.FloatAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.FloatAlign, 64),
                                                    DL.AlignmentInfo 32 (Just 64)),
                                                   ((DL.VectorAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 128),
                                                    DL.AlignmentInfo 128 (Just 128)),
                                                   ((DL.AggregateAlign, 0),
                                                    DL.AlignmentInfo 0 (Just 64)),
                                                   ((DL.FloatAlign, 80),
                                                    DL.AlignmentInfo 128 (Just 128))],
                       DL.nativeSizes = Just (Set.fromList [8, 16, 32])
                     }
      Platform { platformArch = ArchX86, platformOS = OSMinGW32 } ->
          DL.DataLayout { DL.endianness = Just DL.LittleEndian,
                       DL.stackAlignment = Nothing, -- default stack alignment
                       DL.pointerLayouts = Map.fromList [(AS.AddrSpace 0,
                                                          (32, DL.AlignmentInfo 32 (Just 32)))],
                       DL.typeLayouts = Map.fromList [((DL.IntegerAlign, 1),
                                                       DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 8),
                                                    DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 16),
                                                    DL.AlignmentInfo 16 (Just 16)),
                                                   ((DL.IntegerAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.IntegerAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.FloatAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.FloatAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 128),
                                                    DL.AlignmentInfo 128 (Just 128)),
                                                   ((DL.AggregateAlign, 0),
                                                    DL.AlignmentInfo 0 (Just 64)),
                                                   ((DL.FloatAlign, 80),
                                                    DL.AlignmentInfo 32 (Just 32))],
                       DL.nativeSizes = Just (Set.fromList [8, 16, 32])
                     }
      Platform { platformArch = ArchX86, platformOS = OSLinux } ->
          DL.DataLayout { DL.endianness = Just DL.LittleEndian,
                       DL.stackAlignment = Nothing, -- default stack alignment
                       DL.pointerLayouts = Map.fromList [(AS.AddrSpace 0,
                                                          (32, DL.AlignmentInfo 32 (Just 32)))],
                       DL.typeLayouts = Map.fromList [((DL.IntegerAlign, 1),
                                                       DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 8),
                                                    DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 16),
                                                    DL.AlignmentInfo 16 (Just 16)),
                                                   ((DL.IntegerAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.IntegerAlign, 64),
                                                    DL.AlignmentInfo 32 (Just 64)),
                                                   ((DL.FloatAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.FloatAlign, 64),
                                                    DL.AlignmentInfo 32 (Just 64)),
                                                   ((DL.VectorAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 128),
                                                    DL.AlignmentInfo 128 (Just 128)),
                                                   ((DL.AggregateAlign, 0),
                                                    DL.AlignmentInfo 0 (Just 64)),
                                                   ((DL.FloatAlign, 80),
                                                    DL.AlignmentInfo 32 (Just 32))],
                       DL.nativeSizes = Just (Set.fromList [8, 16, 32])
                     }
      Platform { platformArch = ArchX86_64, platformOS = OSDarwin } ->
          DL.DataLayout { DL.endianness = Just DL.LittleEndian,
                       DL.stackAlignment = Nothing, -- default stack alignment
                       DL.pointerLayouts = Map.fromList [(AS.AddrSpace 0,
                                                          (64, DL.AlignmentInfo 64 (Just 64)))],
                       DL.typeLayouts = Map.fromList [((DL.IntegerAlign, 1),
                                                       DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 8),
                                                    DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 16),
                                                    DL.AlignmentInfo 16 (Just 16)),
                                                   ((DL.IntegerAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.IntegerAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.FloatAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.FloatAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 128),
                                                    DL.AlignmentInfo 128 (Just 128)),
                                                   ((DL.AggregateAlign, 0),
                                                    DL.AlignmentInfo 0 (Just 64)),
                                                   ((DL.StackAlign, 0),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.FloatAlign, 80),
                                                    DL.AlignmentInfo 128 (Just 128))],
                       DL.nativeSizes = Just (Set.fromList [8, 16, 32, 64])
                     }
      Platform { platformArch = ArchX86_64, platformOS = OSLinux } ->
          DL.DataLayout { DL.endianness = Just DL.LittleEndian,
                       DL.stackAlignment = Nothing, -- default stack alignment
                       DL.pointerLayouts = Map.fromList [(AS.AddrSpace 0,
                                                          (64, DL.AlignmentInfo 64 (Just 64)))],
                       DL.typeLayouts = Map.fromList [((DL.IntegerAlign, 1),
                                                       DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 8),
                                                    DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 16),
                                                    DL.AlignmentInfo 16 (Just 16)),
                                                   ((DL.IntegerAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.IntegerAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.FloatAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.FloatAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 128),
                                                    DL.AlignmentInfo 128 (Just 128)),
                                                   ((DL.AggregateAlign, 0),
                                                    DL.AlignmentInfo 0 (Just 64)),
                                                   ((DL.StackAlign, 0),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.FloatAlign, 80),
                                                    DL.AlignmentInfo 128 (Just 128))],
                       DL.nativeSizes = Just (Set.fromList [8, 16, 32, 64])
                     }
      Platform { platformArch = ArchARM {}, platformOS = OSLinux } ->
          DL.DataLayout { DL.endianness = Just DL.LittleEndian,
                       DL.stackAlignment = Nothing, -- default stack alignment
                       DL.pointerLayouts = Map.fromList [(AS.AddrSpace 0,
                                                          (32, DL.AlignmentInfo 32 (Just 32)))],
                       DL.typeLayouts = Map.fromList [((DL.IntegerAlign, 1),
                                                       DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 8),
                                                    DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 16),
                                                    DL.AlignmentInfo 16 (Just 16)),
                                                   ((DL.IntegerAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.IntegerAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.FloatAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.FloatAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 128),
                                                    DL.AlignmentInfo 64 (Just 128)),
                                                   ((DL.AggregateAlign, 0),
                                                    DL.AlignmentInfo 0 (Just 64))],
                       DL.nativeSizes = Just (Set.fromList [32])
                     }
      Platform { platformArch = ArchARM {}, platformOS = OSAndroid } ->
          DL.DataLayout { DL.endianness = Just DL.LittleEndian,
                       DL.stackAlignment = Nothing, -- default stack alignment
                       DL.pointerLayouts = Map.fromList [(AS.AddrSpace 0,
                                                          (32, DL.AlignmentInfo 32 (Just 32)))],
                       DL.typeLayouts = Map.fromList [((DL.IntegerAlign, 1),
                                                       DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 8),
                                                    DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 16),
                                                    DL.AlignmentInfo 16 (Just 16)),
                                                   ((DL.IntegerAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.IntegerAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.FloatAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.FloatAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 128),
                                                    DL.AlignmentInfo 64 (Just 128)),
                                                   ((DL.AggregateAlign, 0),
                                                    DL.AlignmentInfo 0 (Just 64))],
                       DL.nativeSizes = Just (Set.fromList [32])
                     }
      Platform { platformArch = ArchARM {}, platformOS = OSQNXNTO } ->
          DL.DataLayout { DL.endianness = Just DL.LittleEndian,
                       DL.stackAlignment = Nothing, -- default stack alignment
                       DL.pointerLayouts = Map.fromList [(AS.AddrSpace 0,
                                                          (32, DL.AlignmentInfo 32 (Just 32)))],
                       DL.typeLayouts = Map.fromList [((DL.IntegerAlign, 1),
                                                       DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 8),
                                                    DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 16),
                                                    DL.AlignmentInfo 16 (Just 16)),
                                                   ((DL.IntegerAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.IntegerAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.FloatAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.FloatAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 128),
                                                    DL.AlignmentInfo 64 (Just 128)),
                                                   ((DL.AggregateAlign, 0),
                                                    DL.AlignmentInfo 0 (Just 64))],
                       DL.nativeSizes = Just (Set.fromList [32])
                     }
      Platform { platformArch = ArchARM {}, platformOS = OSiOS } ->
          DL.DataLayout { DL.endianness = Just DL.LittleEndian,
                       DL.stackAlignment = Nothing, -- default stack alignment
                       DL.pointerLayouts = Map.fromList [(AS.AddrSpace 0,
                                                          (32, DL.AlignmentInfo 32 (Just 32)))],
                       DL.typeLayouts = Map.fromList [((DL.IntegerAlign, 1),
                                                       DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 8),
                                                    DL.AlignmentInfo 8 (Just 8)),
                                                   ((DL.IntegerAlign, 16),
                                                    DL.AlignmentInfo 16 (Just 16)),
                                                   ((DL.IntegerAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.IntegerAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.FloatAlign, 32),
                                                    DL.AlignmentInfo 32 (Just 32)),
                                                   ((DL.FloatAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 64),
                                                    DL.AlignmentInfo 64 (Just 64)),
                                                   ((DL.VectorAlign, 128),
                                                    DL.AlignmentInfo 64 (Just 128)),
                                                   ((DL.AggregateAlign, 0),
                                                    DL.AlignmentInfo 0 (Just 64))],
                       DL.nativeSizes = Just (Set.fromList [32])
                     }
      _ ->
          DL.defaultDataLayout

{-
split :: (Char -> Bool) -> String -> [String]
split f xs = split' f "" [] xs
    where split' f w ws [] = w:ws
          split' f w ws (x:xs) | f x = split' f "" (w:ws) xs
                               | otherwise = split' f (w++"x") ws xs

-- Note, this function does not work for data layout strings in general,
-- only the ones of the exact form defined above.
-- It's a horrible function as it is, making it work generally would make it
-- even uglier.
dlStringToDataLayout :: String -> DL.DataLayout
dlStringToDataLayout dl =
    let ws = split (== '-') dl
        endianness = case (ws!!0) of
                       "e" -> Just DL.LittleEndian
                       "E" -> Just DL.BigEndian
                       -- throw an error here, even though the dl may be correct in some format
                       _   -> error "dlStringToDataLayout: Could not parse."
        stackAlignment = Nothing -- default stack alignment
        pointerLayouts =
            let ints = (map read (split (== ':') (drop 2 (ws!!1)))) in
            Map.fromList [(AS.AddrSpace 0, (ints!!0, DL.AlignmentInfo (ints!!1) (Just (ints!!2))))]
        -- get strings that describe a type layout
        tlStrings = filter (\(t:ss) -> t == 'i' || t == 'f' || t == 'v' || t == 'a') ws
        tlStrToTlPair (t:ss) =
            let ints = (map read (split (== ':') ss)) in
            case t of
              'i' -> ((DL.IntegerAlign, (ints!!0)), DL.AlignmentInfo (ints!!1) (Just (ints!!2)))
              'f' -> ((DL.FloatAlign, (ints!!0)), DL.AlignmentInfo (ints!!1) (Just (ints!!2)))
              'v' -> ((DL.VectorAlign, (ints!!0)), DL.AlignmentInfo (ints!!1) (Just (ints!!2)))
              'a' -> ((DL.AggregateAlign, (ints!!0)), DL.AlignmentInfo (ints!!1) (Just (ints!!2)))
              _   -> error "dlStringToDataLayout: Could not parse."
        typeLayouts = Map.fromList (map tlStrToTlPair tlStrings)
        nsString = head (filter (\(t:ss) -> t == 'n') ws)
        nativeSizes = Just (Set.fromList (map read (drop 2 (split (== ':') nsString))))
    in
      DL.DataLayout { DL.endianness = endianness,
                      DL.stackAlignment = stackAlignment,
                      DL.pointerLayouts = pointerLayouts,
                      DL.typeLayouts = typeLayouts,
                      DL.nativeSizes = nativeSizes }


-- | LLVM data layout description for the host target
dataLayout :: Platform -> String
dataLayout platform =
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
    Platform { platformArch = ArchX86, platformOS = OSiOS } ->
        "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:128:128-n8:16:32"
    _ ->
        ""

platformToDataLayout :: Platform -> DL.DataLayout
platformToDataLayout = dlStringToDataLayout . dataLayout
-}

platformToTargetTriple :: Platform -> String
platformToTargetTriple platform =
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

--FIXME

platformToTargetMachine :: Platform -> IO T.Target
platformToTargetMachine platform =
    do T.initializeAllTargets --must call this before lookupTarget
       t <- Err.runErrorT $ T.lookupTarget Nothing (platformToTargetTriple platform)
       case t of
         Left err -> error err
         Right (target, warn) -> return target

llvmVarToName ::  LlvmVar -> AST.Name
llvmVarToName (LMGlobalVar name ty link sec ali con) = Name (unpackFS name)
llvmVarToName (LMLocalVar uniq LMLabel) = Name (show uniq)
llvmVarToName (LMLocalVar uniq ty) = Name ('l' : show uniq)
llvmVarToName (LMNLocalVar name ty) = Name (unpackFS name)
llvmVarToName _ = error "llvmVarToName: not a valid name"



llvmVarToConstant :: LlvmVar -> C.Constant
llvmVarToConstant v@(LMGlobalVar name ty link sec ali con) = C.GlobalReference (llvmVarToName v)
--error (unpackFS name)
llvmVarToConstant v@(LMLocalVar uniq ty) = error "llvmVarToConstant: Undefined for LMLocalVar"
llvmVarToConstant v@(LMNLocalVar str ty) = error "llvmVarToConstant: Undefined for LMNLocalVar"
llvmVarToConstant v@(LMLitVar lit) = llvmLitToConstant lit
-- error "llvmVarToConstant: Undefined for LMLitVar"

mkName :: LMString -> AST.Name
mkName = Name . unpackFS

metaExprToMetadataNode :: MetaExpr -> AST.MetadataNode
metaExprToMetadataNode (MetaStr    s ) =
    MetadataNode [Just (MetadataStringOperand (unpackFS s))]
metaExprToMetadataNode (MetaNode   n ) =
    MetadataNodeReference (MetadataNodeID (fromIntegral n))
metaExprToMetadataNode (MetaVar    v ) =
    case v of
      LMGlobalVar name LMMetadata link sec ali con ->
          MetadataNode [Just (ConstantOperand (llvmVarToConstant v))]
      LMLocalVar uniq LMMetadata -> error $ "metaExprToMetadataNode" ++ (show uniq)
--          MetadataNode [Just (LocalReference (llvmVarToName v))]
      LMNLocalVar str LMMetadata -> error $ "metaExprToMetadataNode" ++ (unpackFS str)
--          MetadataNode [Just (LocalReference (llvmVarToName v))]
      _ -> error "metaExprToMetadataNode: variable is not of type LMMetadata"
metaExprToMetadataNode (MetaStruct es) =
    MetadataNode $ map (Just . metaExprToOperand) es

llvmLitToConstant :: LlvmLit -> C.Constant
llvmLitToConstant lit =
    case lit of
      LMIntLit i ty -> C.Int (fromIntegral (llvmIntWidth ty)) i
      LMFloatLit d ty -> C.Float (floatToSomeFloat d ty)
      LMNullLit ty -> C.Null (llvmTypeToType ty)
      LMVectorLit lits -> C.Vector (map llvmLitToConstant lits)
      LMUndefLit ty -> C.Undef (llvmTypeToType ty)

llvmCastToConstant :: LlvmCastOp -> LlvmVar -> LlvmType -> C.Constant
llvmCastToConstant castop v ty =
    case castop of
      LM_Trunc    -> C.Trunc op ty'
      LM_Zext     -> C.ZExt op ty'
      LM_Sext     -> C.SExt op ty'
      LM_Fptrunc  -> C.FPTrunc op ty'
      LM_Fpext    -> C.FPExt op ty'
      LM_Fptoui   -> C.FPToUI op ty'
      LM_Fptosi   -> C.FPToSI op ty'
      LM_Uitofp   -> C.UIToFP op ty'
      LM_Sitofp   -> C.SIToFP op ty'
      LM_Ptrtoint -> C.PtrToInt op ty'
      LM_Inttoptr -> C.IntToPtr op ty'
      LM_Bitcast  -> C.BitCast op ty'
    where op = llvmVarToConstant v
          ty' = llvmTypeToType ty

llvmExpressionToConstant :: LlvmExpression -> C.Constant
llvmExpressionToConstant expr =
    case expr of
      AbsSyn.Alloca tp amount       -> error "undefined error"
      LlvmOp     op left right      -> llvmOpToConstant op left right
      AbsSyn.Call tp fp args attrs  -> error "undefined error"
      CallM      tp fp args attrs   -> error "undefined error"
      Cast       castop from to     -> llvmCastToConstant castop from to
      Compare    op left right      -> llvmCompareToConstant op left right
      Extract    vec idx            -> llvmExtractToConstant vec idx
      Insert     vec elt idx        -> llvmInsertToConstant vec elt idx
      GetElemPtr inb ptr indexes    -> llvmGetElemPtrToConstant inb ptr indexes
      AbsSyn.Load ptr               -> error "undefined error"
      Malloc     tp amount          -> error "undefined error"
      AbsSyn.Phi tp precessors      -> error "undefined error"
      Asm        asm c ty v se sk   -> error "undefined error"
      MExpr      meta e             -> error "undefined error"

llvmCompareToConstant :: LlvmCmpOp -> LlvmVar -> LlvmVar -> C.Constant
llvmCompareToConstant op left right =
    case op' of
      Left iOp -> C.ICmp iOp l r
      Right fpOp -> C.FCmp fpOp l r
    where op' = llvmCmpOpToPredicate op
          l = llvmVarToConstant left
          r = llvmVarToConstant right

llvmExtractToConstant :: LlvmVar -> LlvmVar -> C.Constant
llvmExtractToConstant vec idx =
    C.ExtractElement (llvmVarToConstant vec) (llvmVarToConstant idx)

llvmInsertToConstant :: LlvmVar -> LlvmVar -> LlvmVar -> C.Constant
llvmInsertToConstant vec elt idx =
    C.InsertElement (llvmVarToConstant vec) (llvmVarToConstant elt) (llvmVarToConstant idx)

llvmGetElemPtrToConstant :: Bool -> LlvmVar -> [LlvmVar] -> C.Constant
llvmGetElemPtrToConstant inb ptr indexes =
    C.GetElementPtr inb (llvmVarToConstant ptr) (map llvmVarToConstant indexes)

llvmOpToConstant :: LlvmMachOp -> LlvmVar -> LlvmVar -> C.Constant
llvmOpToConstant op left right =
    let left' = llvmVarToConstant left
        right' = llvmVarToConstant right in
    case op of
       LM_MO_Add  -> C.Add False False left' right'
       LM_MO_Sub  -> C.Sub False False left' right'
       LM_MO_Mul  -> C.Mul False False left' right'
       LM_MO_UDiv -> C.UDiv False left' right'
       LM_MO_SDiv -> C.SDiv False left' right'
       LM_MO_URem -> C.URem left' right'
       LM_MO_SRem -> C.SRem left' right'
       LM_MO_FAdd -> C.FAdd left' right'
       LM_MO_FSub -> C.FSub left' right'
       LM_MO_FMul -> C.FMul left' right'
       LM_MO_FDiv -> C.FDiv left' right'
       LM_MO_FRem -> C.FRem left' right'
       LM_MO_Shl  -> C.Shl False False left' right'
       LM_MO_LShr -> C.LShr False left' right'
       LM_MO_AShr -> C.AShr False left' right'
       LM_MO_And  -> C.And left' right'
       LM_MO_Or   -> C.Or left' right'
       LM_MO_Xor  -> C.Xor left' right'

-- | Output an LLVM metadata value.
metaExprToOperand :: MetaExpr -> Operand
metaExprToOperand (MetaStr    s ) =
    MetadataStringOperand (unpackFS s)
metaExprToOperand (MetaNode   n ) =
    MetadataNodeOperand (MetadataNodeReference (MetadataNodeID (fromIntegral n)))
-- This seems to match up better with what is produced by GHC
metaExprToOperand (MetaVar    v ) = llvmVarToOperand v
--    MetadataNodeOperand (MetadataNode [Just (llvmVarToOperand v)])
metaExprToOperand (MetaStruct es) =
    MetadataNodeOperand (MetadataNode $ map (Just . metaExprToOperand) es)



--     case v of
--       LMGlobalVar name LMMetadata link sec ali con ->
--           ConstantOperand (llvmVarToConstant v)
--       LMLocalVar uniq LMMetadata -> error $ "metaExprToOperand " ++ (show uniq)
-- -- LocalReference (llvmVarToName v)
--       LMNLocalVar str LMMetadata -> error $ "metaExprToOperand " ++ (unpackFS str)
-- --          LocalReference (llvmVarToName v)
--       LMLitVar lit ->
--           ConstantOperand (llvmLitToConstant lit)
--       _ -> MetadataNodeOperand (MetadataNode [Just (llvmVarToOperand v)])
-- --error $ "metaExprToOperand: variable " ++ show v ++ " is not of type LMMetadata"

-- Returns the width in bits of an integer type.
llvmIntWidth :: LlvmType -> Int
llvmIntWidth (LMInt n) = n
llvmIntWidth _         = error "Must give an integer type."