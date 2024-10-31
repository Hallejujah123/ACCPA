// Generated from stellaParser.g4 by ANTLR 4.12.0

import {ParseTreeListener} from "antlr4";


import { Start_ProgramContext } from "./stellaParser";
import { Start_ExprContext } from "./stellaParser";
import { Start_TypeContext } from "./stellaParser";
import { ProgramContext } from "./stellaParser";
import { LanguageCoreContext } from "./stellaParser";
import { AnExtensionContext } from "./stellaParser";
import { DeclFunContext } from "./stellaParser";
import { DeclFunGenericContext } from "./stellaParser";
import { DeclTypeAliasContext } from "./stellaParser";
import { DeclExceptionTypeContext } from "./stellaParser";
import { DeclExceptionVariantContext } from "./stellaParser";
import { InlineAnnotationContext } from "./stellaParser";
import { ParamDeclContext } from "./stellaParser";
import { FoldContext } from "./stellaParser";
import { AddContext } from "./stellaParser";
import { IsZeroContext } from "./stellaParser";
import { VarContext } from "./stellaParser";
import { TypeAbstractionContext } from "./stellaParser";
import { DivideContext } from "./stellaParser";
import { LessThanContext } from "./stellaParser";
import { DotRecordContext } from "./stellaParser";
import { GreaterThanContext } from "./stellaParser";
import { EqualContext } from "./stellaParser";
import { ThrowContext } from "./stellaParser";
import { MultiplyContext } from "./stellaParser";
import { ConstMemoryContext } from "./stellaParser";
import { ListContext } from "./stellaParser";
import { TryCatchContext } from "./stellaParser";
import { TryCastAsContext } from "./stellaParser";
import { HeadContext } from "./stellaParser";
import { TerminatingSemicolonContext } from "./stellaParser";
import { NotEqualContext } from "./stellaParser";
import { ConstUnitContext } from "./stellaParser";
import { SequenceContext } from "./stellaParser";
import { ConstFalseContext } from "./stellaParser";
import { AbstractionContext } from "./stellaParser";
import { ConstIntContext } from "./stellaParser";
import { VariantContext } from "./stellaParser";
import { ConstTrueContext } from "./stellaParser";
import { SubtractContext } from "./stellaParser";
import { TypeCastContext } from "./stellaParser";
import { IfContext } from "./stellaParser";
import { ApplicationContext } from "./stellaParser";
import { DerefContext } from "./stellaParser";
import { IsEmptyContext } from "./stellaParser";
import { PanicContext } from "./stellaParser";
import { LessThanOrEqualContext } from "./stellaParser";
import { SuccContext } from "./stellaParser";
import { InlContext } from "./stellaParser";
import { GreaterThanOrEqualContext } from "./stellaParser";
import { InrContext } from "./stellaParser";
import { MatchContext } from "./stellaParser";
import { LogicNotContext } from "./stellaParser";
import { ParenthesisedExprContext } from "./stellaParser";
import { TailContext } from "./stellaParser";
import { RecordContext } from "./stellaParser";
import { LogicAndContext } from "./stellaParser";
import { TypeApplicationContext } from "./stellaParser";
import { LetRecContext } from "./stellaParser";
import { LogicOrContext } from "./stellaParser";
import { TryWithContext } from "./stellaParser";
import { PredContext } from "./stellaParser";
import { TypeAscContext } from "./stellaParser";
import { NatRecContext } from "./stellaParser";
import { UnfoldContext } from "./stellaParser";
import { RefContext } from "./stellaParser";
import { DotTupleContext } from "./stellaParser";
import { FixContext } from "./stellaParser";
import { LetContext } from "./stellaParser";
import { AssignContext } from "./stellaParser";
import { TupleContext } from "./stellaParser";
import { ConsListContext } from "./stellaParser";
import { PatternBindingContext } from "./stellaParser";
import { BindingContext } from "./stellaParser";
import { MatchCaseContext } from "./stellaParser";
import { PatternConsContext } from "./stellaParser";
import { PatternTupleContext } from "./stellaParser";
import { PatternListContext } from "./stellaParser";
import { PatternRecordContext } from "./stellaParser";
import { PatternVariantContext } from "./stellaParser";
import { PatternAscContext } from "./stellaParser";
import { PatternIntContext } from "./stellaParser";
import { PatternInrContext } from "./stellaParser";
import { PatternTrueContext } from "./stellaParser";
import { PatternInlContext } from "./stellaParser";
import { PatternVarContext } from "./stellaParser";
import { ParenthesisedPatternContext } from "./stellaParser";
import { PatternSuccContext } from "./stellaParser";
import { PatternFalseContext } from "./stellaParser";
import { PatternUnitContext } from "./stellaParser";
import { PatternCastAsContext } from "./stellaParser";
import { LabelledPatternContext } from "./stellaParser";
import { TypeTupleContext } from "./stellaParser";
import { TypeTopContext } from "./stellaParser";
import { TypeBoolContext } from "./stellaParser";
import { TypeRefContext } from "./stellaParser";
import { TypeRecContext } from "./stellaParser";
import { TypeAutoContext } from "./stellaParser";
import { TypeSumContext } from "./stellaParser";
import { TypeVarContext } from "./stellaParser";
import { TypeVariantContext } from "./stellaParser";
import { TypeUnitContext } from "./stellaParser";
import { TypeNatContext } from "./stellaParser";
import { TypeBottomContext } from "./stellaParser";
import { TypeParensContext } from "./stellaParser";
import { TypeFunContext } from "./stellaParser";
import { TypeForAllContext } from "./stellaParser";
import { TypeRecordContext } from "./stellaParser";
import { TypeListContext } from "./stellaParser";
import { RecordFieldTypeContext } from "./stellaParser";
import { VariantFieldTypeContext } from "./stellaParser";


/**
 * This interface defines a complete listener for a parse tree produced by
 * `stellaParser`.
 */
export default class stellaParserListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by `stellaParser.start_Program`.
	 * @param ctx the parse tree
	 */
	enterStart_Program?: (ctx: Start_ProgramContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.start_Program`.
	 * @param ctx the parse tree
	 */
	exitStart_Program?: (ctx: Start_ProgramContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.start_Expr`.
	 * @param ctx the parse tree
	 */
	enterStart_Expr?: (ctx: Start_ExprContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.start_Expr`.
	 * @param ctx the parse tree
	 */
	exitStart_Expr?: (ctx: Start_ExprContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.start_Type`.
	 * @param ctx the parse tree
	 */
	enterStart_Type?: (ctx: Start_TypeContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.start_Type`.
	 * @param ctx the parse tree
	 */
	exitStart_Type?: (ctx: Start_TypeContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.program`.
	 * @param ctx the parse tree
	 */
	enterProgram?: (ctx: ProgramContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.program`.
	 * @param ctx the parse tree
	 */
	exitProgram?: (ctx: ProgramContext) => void;
	/**
	 * Enter a parse tree produced by the `LanguageCore`
	 * labeled alternative in `stellaParser.languageDecl`.
	 * @param ctx the parse tree
	 */
	enterLanguageCore?: (ctx: LanguageCoreContext) => void;
	/**
	 * Exit a parse tree produced by the `LanguageCore`
	 * labeled alternative in `stellaParser.languageDecl`.
	 * @param ctx the parse tree
	 */
	exitLanguageCore?: (ctx: LanguageCoreContext) => void;
	/**
	 * Enter a parse tree produced by the `AnExtension`
	 * labeled alternative in `stellaParser.extension`.
	 * @param ctx the parse tree
	 */
	enterAnExtension?: (ctx: AnExtensionContext) => void;
	/**
	 * Exit a parse tree produced by the `AnExtension`
	 * labeled alternative in `stellaParser.extension`.
	 * @param ctx the parse tree
	 */
	exitAnExtension?: (ctx: AnExtensionContext) => void;
	/**
	 * Enter a parse tree produced by the `DeclFun`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	enterDeclFun?: (ctx: DeclFunContext) => void;
	/**
	 * Exit a parse tree produced by the `DeclFun`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	exitDeclFun?: (ctx: DeclFunContext) => void;
	/**
	 * Enter a parse tree produced by the `DeclFunGeneric`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	enterDeclFunGeneric?: (ctx: DeclFunGenericContext) => void;
	/**
	 * Exit a parse tree produced by the `DeclFunGeneric`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	exitDeclFunGeneric?: (ctx: DeclFunGenericContext) => void;
	/**
	 * Enter a parse tree produced by the `DeclTypeAlias`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	enterDeclTypeAlias?: (ctx: DeclTypeAliasContext) => void;
	/**
	 * Exit a parse tree produced by the `DeclTypeAlias`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	exitDeclTypeAlias?: (ctx: DeclTypeAliasContext) => void;
	/**
	 * Enter a parse tree produced by the `DeclExceptionType`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	enterDeclExceptionType?: (ctx: DeclExceptionTypeContext) => void;
	/**
	 * Exit a parse tree produced by the `DeclExceptionType`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	exitDeclExceptionType?: (ctx: DeclExceptionTypeContext) => void;
	/**
	 * Enter a parse tree produced by the `DeclExceptionVariant`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	enterDeclExceptionVariant?: (ctx: DeclExceptionVariantContext) => void;
	/**
	 * Exit a parse tree produced by the `DeclExceptionVariant`
	 * labeled alternative in `stellaParser.decl`.
	 * @param ctx the parse tree
	 */
	exitDeclExceptionVariant?: (ctx: DeclExceptionVariantContext) => void;
	/**
	 * Enter a parse tree produced by the `InlineAnnotation`
	 * labeled alternative in `stellaParser.annotation`.
	 * @param ctx the parse tree
	 */
	enterInlineAnnotation?: (ctx: InlineAnnotationContext) => void;
	/**
	 * Exit a parse tree produced by the `InlineAnnotation`
	 * labeled alternative in `stellaParser.annotation`.
	 * @param ctx the parse tree
	 */
	exitInlineAnnotation?: (ctx: InlineAnnotationContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.paramDecl`.
	 * @param ctx the parse tree
	 */
	enterParamDecl?: (ctx: ParamDeclContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.paramDecl`.
	 * @param ctx the parse tree
	 */
	exitParamDecl?: (ctx: ParamDeclContext) => void;
	/**
	 * Enter a parse tree produced by the `Fold`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterFold?: (ctx: FoldContext) => void;
	/**
	 * Exit a parse tree produced by the `Fold`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitFold?: (ctx: FoldContext) => void;
	/**
	 * Enter a parse tree produced by the `Add`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterAdd?: (ctx: AddContext) => void;
	/**
	 * Exit a parse tree produced by the `Add`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitAdd?: (ctx: AddContext) => void;
	/**
	 * Enter a parse tree produced by the `IsZero`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterIsZero?: (ctx: IsZeroContext) => void;
	/**
	 * Exit a parse tree produced by the `IsZero`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitIsZero?: (ctx: IsZeroContext) => void;
	/**
	 * Enter a parse tree produced by the `Var`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterVar?: (ctx: VarContext) => void;
	/**
	 * Exit a parse tree produced by the `Var`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitVar?: (ctx: VarContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeAbstraction`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTypeAbstraction?: (ctx: TypeAbstractionContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeAbstraction`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTypeAbstraction?: (ctx: TypeAbstractionContext) => void;
	/**
	 * Enter a parse tree produced by the `Divide`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterDivide?: (ctx: DivideContext) => void;
	/**
	 * Exit a parse tree produced by the `Divide`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitDivide?: (ctx: DivideContext) => void;
	/**
	 * Enter a parse tree produced by the `LessThan`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterLessThan?: (ctx: LessThanContext) => void;
	/**
	 * Exit a parse tree produced by the `LessThan`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitLessThan?: (ctx: LessThanContext) => void;
	/**
	 * Enter a parse tree produced by the `DotRecord`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterDotRecord?: (ctx: DotRecordContext) => void;
	/**
	 * Exit a parse tree produced by the `DotRecord`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitDotRecord?: (ctx: DotRecordContext) => void;
	/**
	 * Enter a parse tree produced by the `GreaterThan`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterGreaterThan?: (ctx: GreaterThanContext) => void;
	/**
	 * Exit a parse tree produced by the `GreaterThan`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitGreaterThan?: (ctx: GreaterThanContext) => void;
	/**
	 * Enter a parse tree produced by the `Equal`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterEqual?: (ctx: EqualContext) => void;
	/**
	 * Exit a parse tree produced by the `Equal`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitEqual?: (ctx: EqualContext) => void;
	/**
	 * Enter a parse tree produced by the `Throw`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterThrow?: (ctx: ThrowContext) => void;
	/**
	 * Exit a parse tree produced by the `Throw`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitThrow?: (ctx: ThrowContext) => void;
	/**
	 * Enter a parse tree produced by the `Multiply`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterMultiply?: (ctx: MultiplyContext) => void;
	/**
	 * Exit a parse tree produced by the `Multiply`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitMultiply?: (ctx: MultiplyContext) => void;
	/**
	 * Enter a parse tree produced by the `ConstMemory`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterConstMemory?: (ctx: ConstMemoryContext) => void;
	/**
	 * Exit a parse tree produced by the `ConstMemory`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitConstMemory?: (ctx: ConstMemoryContext) => void;
	/**
	 * Enter a parse tree produced by the `List`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterList?: (ctx: ListContext) => void;
	/**
	 * Exit a parse tree produced by the `List`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitList?: (ctx: ListContext) => void;
	/**
	 * Enter a parse tree produced by the `TryCatch`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTryCatch?: (ctx: TryCatchContext) => void;
	/**
	 * Exit a parse tree produced by the `TryCatch`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTryCatch?: (ctx: TryCatchContext) => void;
	/**
	 * Enter a parse tree produced by the `TryCastAs`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTryCastAs?: (ctx: TryCastAsContext) => void;
	/**
	 * Exit a parse tree produced by the `TryCastAs`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTryCastAs?: (ctx: TryCastAsContext) => void;
	/**
	 * Enter a parse tree produced by the `Head`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterHead?: (ctx: HeadContext) => void;
	/**
	 * Exit a parse tree produced by the `Head`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitHead?: (ctx: HeadContext) => void;
	/**
	 * Enter a parse tree produced by the `TerminatingSemicolon`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTerminatingSemicolon?: (ctx: TerminatingSemicolonContext) => void;
	/**
	 * Exit a parse tree produced by the `TerminatingSemicolon`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTerminatingSemicolon?: (ctx: TerminatingSemicolonContext) => void;
	/**
	 * Enter a parse tree produced by the `NotEqual`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterNotEqual?: (ctx: NotEqualContext) => void;
	/**
	 * Exit a parse tree produced by the `NotEqual`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitNotEqual?: (ctx: NotEqualContext) => void;
	/**
	 * Enter a parse tree produced by the `ConstUnit`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterConstUnit?: (ctx: ConstUnitContext) => void;
	/**
	 * Exit a parse tree produced by the `ConstUnit`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitConstUnit?: (ctx: ConstUnitContext) => void;
	/**
	 * Enter a parse tree produced by the `Sequence`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterSequence?: (ctx: SequenceContext) => void;
	/**
	 * Exit a parse tree produced by the `Sequence`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitSequence?: (ctx: SequenceContext) => void;
	/**
	 * Enter a parse tree produced by the `ConstFalse`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterConstFalse?: (ctx: ConstFalseContext) => void;
	/**
	 * Exit a parse tree produced by the `ConstFalse`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitConstFalse?: (ctx: ConstFalseContext) => void;
	/**
	 * Enter a parse tree produced by the `Abstraction`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterAbstraction?: (ctx: AbstractionContext) => void;
	/**
	 * Exit a parse tree produced by the `Abstraction`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitAbstraction?: (ctx: AbstractionContext) => void;
	/**
	 * Enter a parse tree produced by the `ConstInt`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterConstInt?: (ctx: ConstIntContext) => void;
	/**
	 * Exit a parse tree produced by the `ConstInt`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitConstInt?: (ctx: ConstIntContext) => void;
	/**
	 * Enter a parse tree produced by the `Variant`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterVariant?: (ctx: VariantContext) => void;
	/**
	 * Exit a parse tree produced by the `Variant`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitVariant?: (ctx: VariantContext) => void;
	/**
	 * Enter a parse tree produced by the `ConstTrue`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterConstTrue?: (ctx: ConstTrueContext) => void;
	/**
	 * Exit a parse tree produced by the `ConstTrue`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitConstTrue?: (ctx: ConstTrueContext) => void;
	/**
	 * Enter a parse tree produced by the `Subtract`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterSubtract?: (ctx: SubtractContext) => void;
	/**
	 * Exit a parse tree produced by the `Subtract`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitSubtract?: (ctx: SubtractContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeCast`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTypeCast?: (ctx: TypeCastContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeCast`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTypeCast?: (ctx: TypeCastContext) => void;
	/**
	 * Enter a parse tree produced by the `If`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterIf?: (ctx: IfContext) => void;
	/**
	 * Exit a parse tree produced by the `If`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitIf?: (ctx: IfContext) => void;
	/**
	 * Enter a parse tree produced by the `Application`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterApplication?: (ctx: ApplicationContext) => void;
	/**
	 * Exit a parse tree produced by the `Application`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitApplication?: (ctx: ApplicationContext) => void;
	/**
	 * Enter a parse tree produced by the `Deref`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterDeref?: (ctx: DerefContext) => void;
	/**
	 * Exit a parse tree produced by the `Deref`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitDeref?: (ctx: DerefContext) => void;
	/**
	 * Enter a parse tree produced by the `IsEmpty`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterIsEmpty?: (ctx: IsEmptyContext) => void;
	/**
	 * Exit a parse tree produced by the `IsEmpty`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitIsEmpty?: (ctx: IsEmptyContext) => void;
	/**
	 * Enter a parse tree produced by the `Panic`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterPanic?: (ctx: PanicContext) => void;
	/**
	 * Exit a parse tree produced by the `Panic`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitPanic?: (ctx: PanicContext) => void;
	/**
	 * Enter a parse tree produced by the `LessThanOrEqual`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterLessThanOrEqual?: (ctx: LessThanOrEqualContext) => void;
	/**
	 * Exit a parse tree produced by the `LessThanOrEqual`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitLessThanOrEqual?: (ctx: LessThanOrEqualContext) => void;
	/**
	 * Enter a parse tree produced by the `Succ`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterSucc?: (ctx: SuccContext) => void;
	/**
	 * Exit a parse tree produced by the `Succ`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitSucc?: (ctx: SuccContext) => void;
	/**
	 * Enter a parse tree produced by the `Inl`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterInl?: (ctx: InlContext) => void;
	/**
	 * Exit a parse tree produced by the `Inl`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitInl?: (ctx: InlContext) => void;
	/**
	 * Enter a parse tree produced by the `GreaterThanOrEqual`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterGreaterThanOrEqual?: (ctx: GreaterThanOrEqualContext) => void;
	/**
	 * Exit a parse tree produced by the `GreaterThanOrEqual`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitGreaterThanOrEqual?: (ctx: GreaterThanOrEqualContext) => void;
	/**
	 * Enter a parse tree produced by the `Inr`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterInr?: (ctx: InrContext) => void;
	/**
	 * Exit a parse tree produced by the `Inr`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitInr?: (ctx: InrContext) => void;
	/**
	 * Enter a parse tree produced by the `Match`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterMatch?: (ctx: MatchContext) => void;
	/**
	 * Exit a parse tree produced by the `Match`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitMatch?: (ctx: MatchContext) => void;
	/**
	 * Enter a parse tree produced by the `LogicNot`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterLogicNot?: (ctx: LogicNotContext) => void;
	/**
	 * Exit a parse tree produced by the `LogicNot`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitLogicNot?: (ctx: LogicNotContext) => void;
	/**
	 * Enter a parse tree produced by the `ParenthesisedExpr`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterParenthesisedExpr?: (ctx: ParenthesisedExprContext) => void;
	/**
	 * Exit a parse tree produced by the `ParenthesisedExpr`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitParenthesisedExpr?: (ctx: ParenthesisedExprContext) => void;
	/**
	 * Enter a parse tree produced by the `Tail`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTail?: (ctx: TailContext) => void;
	/**
	 * Exit a parse tree produced by the `Tail`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTail?: (ctx: TailContext) => void;
	/**
	 * Enter a parse tree produced by the `Record`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterRecord?: (ctx: RecordContext) => void;
	/**
	 * Exit a parse tree produced by the `Record`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitRecord?: (ctx: RecordContext) => void;
	/**
	 * Enter a parse tree produced by the `LogicAnd`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterLogicAnd?: (ctx: LogicAndContext) => void;
	/**
	 * Exit a parse tree produced by the `LogicAnd`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitLogicAnd?: (ctx: LogicAndContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeApplication`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTypeApplication?: (ctx: TypeApplicationContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeApplication`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTypeApplication?: (ctx: TypeApplicationContext) => void;
	/**
	 * Enter a parse tree produced by the `LetRec`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterLetRec?: (ctx: LetRecContext) => void;
	/**
	 * Exit a parse tree produced by the `LetRec`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitLetRec?: (ctx: LetRecContext) => void;
	/**
	 * Enter a parse tree produced by the `LogicOr`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterLogicOr?: (ctx: LogicOrContext) => void;
	/**
	 * Exit a parse tree produced by the `LogicOr`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitLogicOr?: (ctx: LogicOrContext) => void;
	/**
	 * Enter a parse tree produced by the `TryWith`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTryWith?: (ctx: TryWithContext) => void;
	/**
	 * Exit a parse tree produced by the `TryWith`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTryWith?: (ctx: TryWithContext) => void;
	/**
	 * Enter a parse tree produced by the `Pred`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterPred?: (ctx: PredContext) => void;
	/**
	 * Exit a parse tree produced by the `Pred`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitPred?: (ctx: PredContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeAsc`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTypeAsc?: (ctx: TypeAscContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeAsc`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTypeAsc?: (ctx: TypeAscContext) => void;
	/**
	 * Enter a parse tree produced by the `NatRec`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterNatRec?: (ctx: NatRecContext) => void;
	/**
	 * Exit a parse tree produced by the `NatRec`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitNatRec?: (ctx: NatRecContext) => void;
	/**
	 * Enter a parse tree produced by the `Unfold`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterUnfold?: (ctx: UnfoldContext) => void;
	/**
	 * Exit a parse tree produced by the `Unfold`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitUnfold?: (ctx: UnfoldContext) => void;
	/**
	 * Enter a parse tree produced by the `Ref`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterRef?: (ctx: RefContext) => void;
	/**
	 * Exit a parse tree produced by the `Ref`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitRef?: (ctx: RefContext) => void;
	/**
	 * Enter a parse tree produced by the `DotTuple`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterDotTuple?: (ctx: DotTupleContext) => void;
	/**
	 * Exit a parse tree produced by the `DotTuple`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitDotTuple?: (ctx: DotTupleContext) => void;
	/**
	 * Enter a parse tree produced by the `Fix`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterFix?: (ctx: FixContext) => void;
	/**
	 * Exit a parse tree produced by the `Fix`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitFix?: (ctx: FixContext) => void;
	/**
	 * Enter a parse tree produced by the `Let`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterLet?: (ctx: LetContext) => void;
	/**
	 * Exit a parse tree produced by the `Let`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitLet?: (ctx: LetContext) => void;
	/**
	 * Enter a parse tree produced by the `Assign`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterAssign?: (ctx: AssignContext) => void;
	/**
	 * Exit a parse tree produced by the `Assign`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitAssign?: (ctx: AssignContext) => void;
	/**
	 * Enter a parse tree produced by the `Tuple`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterTuple?: (ctx: TupleContext) => void;
	/**
	 * Exit a parse tree produced by the `Tuple`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitTuple?: (ctx: TupleContext) => void;
	/**
	 * Enter a parse tree produced by the `ConsList`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	enterConsList?: (ctx: ConsListContext) => void;
	/**
	 * Exit a parse tree produced by the `ConsList`
	 * labeled alternative in `stellaParser.expr`.
	 * @param ctx the parse tree
	 */
	exitConsList?: (ctx: ConsListContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.patternBinding`.
	 * @param ctx the parse tree
	 */
	enterPatternBinding?: (ctx: PatternBindingContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.patternBinding`.
	 * @param ctx the parse tree
	 */
	exitPatternBinding?: (ctx: PatternBindingContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.binding`.
	 * @param ctx the parse tree
	 */
	enterBinding?: (ctx: BindingContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.binding`.
	 * @param ctx the parse tree
	 */
	exitBinding?: (ctx: BindingContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.matchCase`.
	 * @param ctx the parse tree
	 */
	enterMatchCase?: (ctx: MatchCaseContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.matchCase`.
	 * @param ctx the parse tree
	 */
	exitMatchCase?: (ctx: MatchCaseContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternCons`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternCons?: (ctx: PatternConsContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternCons`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternCons?: (ctx: PatternConsContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternTuple`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternTuple?: (ctx: PatternTupleContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternTuple`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternTuple?: (ctx: PatternTupleContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternList`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternList?: (ctx: PatternListContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternList`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternList?: (ctx: PatternListContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternRecord`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternRecord?: (ctx: PatternRecordContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternRecord`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternRecord?: (ctx: PatternRecordContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternVariant`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternVariant?: (ctx: PatternVariantContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternVariant`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternVariant?: (ctx: PatternVariantContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternAsc`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternAsc?: (ctx: PatternAscContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternAsc`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternAsc?: (ctx: PatternAscContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternInt`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternInt?: (ctx: PatternIntContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternInt`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternInt?: (ctx: PatternIntContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternInr`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternInr?: (ctx: PatternInrContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternInr`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternInr?: (ctx: PatternInrContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternTrue`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternTrue?: (ctx: PatternTrueContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternTrue`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternTrue?: (ctx: PatternTrueContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternInl`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternInl?: (ctx: PatternInlContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternInl`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternInl?: (ctx: PatternInlContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternVar`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternVar?: (ctx: PatternVarContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternVar`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternVar?: (ctx: PatternVarContext) => void;
	/**
	 * Enter a parse tree produced by the `ParenthesisedPattern`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterParenthesisedPattern?: (ctx: ParenthesisedPatternContext) => void;
	/**
	 * Exit a parse tree produced by the `ParenthesisedPattern`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitParenthesisedPattern?: (ctx: ParenthesisedPatternContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternSucc`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternSucc?: (ctx: PatternSuccContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternSucc`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternSucc?: (ctx: PatternSuccContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternFalse`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternFalse?: (ctx: PatternFalseContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternFalse`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternFalse?: (ctx: PatternFalseContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternUnit`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternUnit?: (ctx: PatternUnitContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternUnit`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternUnit?: (ctx: PatternUnitContext) => void;
	/**
	 * Enter a parse tree produced by the `PatternCastAs`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	enterPatternCastAs?: (ctx: PatternCastAsContext) => void;
	/**
	 * Exit a parse tree produced by the `PatternCastAs`
	 * labeled alternative in `stellaParser.pattern`.
	 * @param ctx the parse tree
	 */
	exitPatternCastAs?: (ctx: PatternCastAsContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.labelledPattern`.
	 * @param ctx the parse tree
	 */
	enterLabelledPattern?: (ctx: LabelledPatternContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.labelledPattern`.
	 * @param ctx the parse tree
	 */
	exitLabelledPattern?: (ctx: LabelledPatternContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeTuple`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeTuple?: (ctx: TypeTupleContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeTuple`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeTuple?: (ctx: TypeTupleContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeTop`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeTop?: (ctx: TypeTopContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeTop`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeTop?: (ctx: TypeTopContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeBool`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeBool?: (ctx: TypeBoolContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeBool`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeBool?: (ctx: TypeBoolContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeRef`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeRef?: (ctx: TypeRefContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeRef`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeRef?: (ctx: TypeRefContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeRec`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeRec?: (ctx: TypeRecContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeRec`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeRec?: (ctx: TypeRecContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeAuto`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeAuto?: (ctx: TypeAutoContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeAuto`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeAuto?: (ctx: TypeAutoContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeSum`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeSum?: (ctx: TypeSumContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeSum`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeSum?: (ctx: TypeSumContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeVar`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeVar?: (ctx: TypeVarContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeVar`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeVar?: (ctx: TypeVarContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeVariant`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeVariant?: (ctx: TypeVariantContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeVariant`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeVariant?: (ctx: TypeVariantContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeUnit`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeUnit?: (ctx: TypeUnitContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeUnit`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeUnit?: (ctx: TypeUnitContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeNat`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeNat?: (ctx: TypeNatContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeNat`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeNat?: (ctx: TypeNatContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeBottom`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeBottom?: (ctx: TypeBottomContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeBottom`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeBottom?: (ctx: TypeBottomContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeParens`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeParens?: (ctx: TypeParensContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeParens`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeParens?: (ctx: TypeParensContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeFun`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeFun?: (ctx: TypeFunContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeFun`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeFun?: (ctx: TypeFunContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeForAll`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeForAll?: (ctx: TypeForAllContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeForAll`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeForAll?: (ctx: TypeForAllContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeRecord`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeRecord?: (ctx: TypeRecordContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeRecord`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeRecord?: (ctx: TypeRecordContext) => void;
	/**
	 * Enter a parse tree produced by the `TypeList`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	enterTypeList?: (ctx: TypeListContext) => void;
	/**
	 * Exit a parse tree produced by the `TypeList`
	 * labeled alternative in `stellaParser.stellatype`.
	 * @param ctx the parse tree
	 */
	exitTypeList?: (ctx: TypeListContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.recordFieldType`.
	 * @param ctx the parse tree
	 */
	enterRecordFieldType?: (ctx: RecordFieldTypeContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.recordFieldType`.
	 * @param ctx the parse tree
	 */
	exitRecordFieldType?: (ctx: RecordFieldTypeContext) => void;
	/**
	 * Enter a parse tree produced by `stellaParser.variantFieldType`.
	 * @param ctx the parse tree
	 */
	enterVariantFieldType?: (ctx: VariantFieldTypeContext) => void;
	/**
	 * Exit a parse tree produced by `stellaParser.variantFieldType`.
	 * @param ctx the parse tree
	 */
	exitVariantFieldType?: (ctx: VariantFieldTypeContext) => void;
}

