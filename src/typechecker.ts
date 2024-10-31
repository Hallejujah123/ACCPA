import type {
  DeclFun,
  Expr,
  Pattern,
  PatternVar,
  PatternVariant,
  Program,
  Type,
  TypeBool,
  TypeBottom,
  TypeFun,
  TypeList,
  TypeNat,
  TypeRecord,
  TypeRef,
  TypeSum,
  TypeTuple,
  TypeUnit,
  TypeVariant,
} from "./ast";

enum Errors {
  UNEXPECTED_TYPE_FOR_PARAMETER = "ERROR_UNEXPECTED_TYPE_FOR_PARAMETER",
  UNEXPECTED_TYPE_FOR_EXPRESSION = "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION",
  UNEXPECTED_LAMBDA = "ERROR_UNEXPECTED_LAMBDA",
  NOT_A_FUNCTION = "ERROR_NOT_A_FUNCTION",
  UNDEFINED_VARIABLE = "ERROR_UNDEFINED_VARIABLE",
  MISSING_MAIN = "ERROR_MISSING_MAIN",

  MISSING_RECORD_FIELDS = "ERROR_MISSING_RECORD_FIELDS",
  UNEXPECTED_RECORD_FIELDS = "ERROR_UNEXPECTED_RECORD_FIELDS",
  UNEXPECTED_RECORD = "ERROR_UNEXPECTED_RECORD",
  NOT_A_RECORD = "ERROR_NOT_A_RECORD",
  UNEXPECTED_FIELD_ACCESS = "ERROR_UNEXPECTED_FIELD_ACCESS",
  UNEXPECTED_TUPLE = "ERROR_UNEXPECTED_TUPLE",
  NOT_A_TUPLE = "ERROR_NOT_A_TUPLE",

  AMBIGUOUS_SUM_TYPE = "ERROR_AMBIGUOUS_SUM_TYPE",
  AMBIGUOUS_LIST_TYPE = "ERROR_AMBIGUOUS_LIST_TYPE",
  ILLEGAL_EMPTY_MATCHING = "ERROR_ILLEGAL_EMPTY_MATCHING",
  NONEXHAUSTIVE_MATCH_PATTERNS = "ERROR_NONEXHAUSTIVE_MATCH_PATTERNS",
  NOT_A_LIST = "ERROR_NOT_A_LIST",
  UNEXPECTED_LIST = "ERROR_UNEXPECTED_LIST",
  UNEXPECTED_INJECTION = "ERROR_UNEXPECTED_INJECTION",
  UNEXPECTED_PATTERN_FOR_TYPE = "ERROR_UNEXPECTED_PATTERN_FOR_TYPE",

  AMBIGUOUS_VARIANT_TYPE = "ERROR_AMBIGUOUS_VARIANT_TYPE",
  UNEXPECTED_VARIANT = "ERROR_UNEXPECTED_VARIANT",
  UNEXPECTED_VARIANT_LABEL = "ERROR_UNEXPECTED_VARIANT_LABEL",

  EXCEPTION_TYPE_NOT_DECLARED = "ERROR_EXCEPTION_TYPE_NOT_DECLARED",
  AMBIGUOUS_THROW_TYPE = "ERROR_AMBIGUOUS_THROW_TYPE",
  AMBIGUOUS_REFERENCE_TYPE = "ERROR_AMBIGUOUS_REFERENCE_TYPE",
  AMBIGUOUS_PANIC_TYPE = "ERROR_AMBIGUOUS_PANIC_TYPE",
  NOT_A_REFERENCE = "ERROR_NOT_A_REFERENCE",
  UNEXPECTED_MEMORY_ADDRESS = "ERROR_UNEXPECTED_MEMORY_ADDRESS",

  UNEXPECTED_SUBTYPE = "ERROR_UNEXPECTED_SUBTYPE",
}

interface Context {
  symbolTable: Map<string, Type>;
  exceptionType: Type | null;
  hasMain: boolean;
}

function generateEmptyContext(): Context {
  return {
    symbolTable: new Map(),
    exceptionType: null,
    hasMain: false,
  };
}

function copyContextWithSymbol(
  ctx: Context,
  name: string,
  type: Type
): Context {
  const newSymbols = new Map(ctx.symbolTable);
  newSymbols.set(name, type);
  return {
    ...ctx,
    symbolTable: newSymbols,
  };
}

const TYPE_NAT: TypeNat = { type: "TypeNat" };
const TYPE_BOOL: TypeBool = { type: "TypeBool" };
const TYPE_UNIT: TypeUnit = { type: "TypeUnit" };
const TYPE_BOT: TypeBottom = { type: "TypeBottom" };
const TYPE_LIST = (t: Type): TypeList => ({ type: "TypeList", elementType: t });
const TYPE_FUN = (param: Type, ret: Type): TypeFun => ({
  type: "TypeFun",
  parametersTypes: [param],
  returnType: ret,
});
const TYPE_REF = (type: Type): TypeRef => ({
  type: "TypeRef",
  referredType: type,
});
const TYPE_SUM = (left: Type, right: Type): TypeSum => ({
  type: "TypeSum",
  left,
  right,
});

export function typecheckProgram(ast: Program) {
  const ctx = generateEmptyContext();
  for (const decl of ast.declarations) {
    switch (decl.type) {
      case "DeclFun":
        ctx.symbolTable.set(decl.name, {
          type: "TypeFun",
          parametersTypes: [decl.parameters[0].paramType],
          returnType: decl.returnType!,
        });
        typecheckFunctionDecl(decl, ctx);
        break;
      case "DeclExceptionType": {
        ctx.exceptionType = decl.exceptionType;
      }
      default:
        throw new Error("Unknown declaration type");
    }
  }

  if (!ctx.hasMain) {
    throw new Error(Errors.MISSING_MAIN);
  }
  console.log("Everything typechecks!");
}

function typecheckFunctionDecl(decl: DeclFun, ctx: Context) {
  const { name, parameters, returnValue, returnType } = decl;
  if (name === "main") {
    ctx.hasMain = true;
  }
  const param = parameters[0];
  const newContext = copyContextWithSymbol(ctx, param.name, param.paramType);
  const bodyType = typecheckExpr(returnValue, returnType!, newContext);
  verifyTypesMatch(returnType!, bodyType);
}

function typecheckExpr(
  expr: Expr,
  expectedType: Type | null,
  ctx: Context
): Type {
  switch (expr.type) {
    case "Var": {
      const { symbolTable } = ctx;
      if (!symbolTable.has(expr.name)) {
        throw new Error(Errors.UNDEFINED_VARIABLE);
      }
      return symbolTable.get(expr.name)!;
    }
    case "ConstBool": {
      return TYPE_BOOL;
    }
    case "If": {
      const condType = typecheckExpr(expr.condition, TYPE_BOOL, ctx);
      verifyTypesMatch(condType, TYPE_BOOL);
      const thenType = typecheckExpr(expr.thenExpr, expectedType, ctx);
      const elseType = typecheckExpr(expr.elseExpr, expectedType, ctx);
      verifyTypesMatch(thenType, elseType);
      return thenType;
    }
    case "ConstInt": {
      return TYPE_NAT;
    }
    case "Succ": {
      const exprType = typecheckExpr(expr.expr, TYPE_NAT, ctx);
      verifyTypesMatch(TYPE_NAT, exprType);
      return TYPE_NAT;
    }
    case "NatIsZero": {
      const exprType = typecheckExpr(expr.expr, TYPE_NAT, ctx);
      verifyTypesMatch(exprType, TYPE_NAT);
      return TYPE_BOOL;
    }
    case "NatRec": {
      const { n, initial, step } = expr;
      const nType = typecheckExpr(n, TYPE_NAT, ctx);
      verifyTypesMatch(nType, TYPE_NAT);
      const initialType = typecheckExpr(initial, expectedType, ctx);
      if (initialType == null) {
        throw new Error("Couldn't infer a type for Nat::rec initial value");
      }
      const stepExpectedType: TypeFun = {
        type: "TypeFun",
        parametersTypes: [TYPE_NAT],
        returnType: {
          type: "TypeFun",
          parametersTypes: [initialType],
          returnType: initialType,
        },
      };
      const stepActualType = typecheckExpr(step, stepExpectedType, ctx);
      verifyTypesMatch(stepExpectedType, stepActualType);
      return initialType;
    }
    case "Abstraction": {
      if (expectedType && expectedType.type !== "TypeFun") {
        throw new Error(Errors.UNEXPECTED_LAMBDA);
      }
      const { parameters, returnValue } = expr;
      const param = parameters[0];
      const paramExpected = expectedType?.parametersTypes[0];
      if (paramExpected) {
        try {
          verifyTypesMatch(paramExpected, param.paramType);
        } catch {
          throw new Error(Errors.UNEXPECTED_TYPE_FOR_PARAMETER);
        }
      }
      const newContext = copyContextWithSymbol(
        ctx,
        param.name,
        param.paramType
      );
      const bodyType = typecheckExpr(
        returnValue,
        expectedType?.returnType ?? null,
        newContext
      );
      return {
        type: "TypeFun",
        parametersTypes: [param.paramType],
        returnType: bodyType,
      };
    }
    case "Application": {
      const { function: func, arguments: args } = expr;
      const funcType = typecheckExpr(func, null, ctx);
      if (funcType.type !== "TypeFun") {
        throw new Error(Errors.NOT_A_FUNCTION);
      }
      const argType = typecheckExpr(args[0], funcType.parametersTypes[0], ctx);
      verifyTypesMatch(funcType.parametersTypes[0], argType);
      if (expectedType) {
        verifyTypesMatch(funcType.returnType, expectedType);
      }
      return (funcType as TypeFun).returnType;
    }
    case "Sequence": {
      const { expr1, expr2 } = expr;
      const expr1Type = typecheckExpr(expr1, TYPE_UNIT, ctx);
      verifyTypesMatch(TYPE_UNIT, expr1Type);
      return typecheckExpr(expr2, expectedType, ctx);
    }

    case "Unit": {
      return TYPE_UNIT;
    }
    case "Tuple": {
      if (expectedType && expectedType.type !== "TypeTuple") {
        throw new Error(Errors.UNEXPECTED_TUPLE);
      }
      const [expr1, expr2] = expr.exprs;
      const type1 = typecheckExpr(expr1, expectedType?.types[0] ?? null, ctx);
      const type2 = typecheckExpr(expr2, expectedType?.types[1] ?? null, ctx);
      return {
        type: "TypeTuple",
        types: [type1, type2],
      };
    }
    case "DotTuple": {
      const { expr: tuple, index } = expr;
      const tupleType = typecheckExpr(tuple, null, ctx);
      if (tupleType.type !== "TypeTuple") {
        throw new Error(Errors.NOT_A_TUPLE);
      }
      return tupleType.types[index - 1];
    }
    case "Record": {
      if (expectedType && expectedType.type !== "TypeRecord") {
        throw new Error(Errors.UNEXPECTED_RECORD);
      }
      const { bindings } = expr;

      return {
        type: "TypeRecord",
        fieldTypes: bindings.map((b, i) => ({
          type: "RecordFieldType" as const,
          label: b.name,
          fieldType: typecheckExpr(
            b.expr,
            (expectedType as TypeRecord | null)?.fieldTypes[i] ?? null,
            ctx
          ),
        })),
      };
    }
    case "DotRecord": {
      const { expr: record, label } = expr;
      const recordType = typecheckExpr(record, null, ctx);
      if (recordType.type !== "TypeRecord") {
        throw new Error(Errors.NOT_A_RECORD);
      }
      const fieldType = recordType.fieldTypes.find(
        (field) => field.label === label
      );
      if (fieldType == null) {
        throw new Error(Errors.UNEXPECTED_FIELD_ACCESS);
      }
      return fieldType.fieldType;
    }
    case "Let": {
      const { body, patternBindings } = expr;
      for (const { pattern, rhs } of patternBindings) {
        const { name } = pattern as PatternVar;
        const type = typecheckExpr(rhs, null, ctx);
        ctx = copyContextWithSymbol(ctx, name, type);
      }
      return typecheckExpr(body, expectedType, ctx);
    }

    case "TypeAscription": {
      const { expr: expression, ascribedType } = expr;
      const inferredType = typecheckExpr(expression, ascribedType, ctx);
      verifyTypesMatch(ascribedType, inferredType);
      return ascribedType;
    }
    case "Inl": {
      if (expectedType && expectedType.type !== "TypeSum") {
        throw new Error(Errors.UNEXPECTED_INJECTION);
      }
      const { expr: expression } = expr;
      const actualType = typecheckExpr(
        expression,
        expectedType?.left ?? null,
        ctx
      );
      if (expectedType) {
        verifyTypesMatch(expectedType.left, actualType);
        return expectedType;
      } else {
        return TYPE_SUM(actualType, TYPE_BOT);
      }
    }
    case "Inr": {
      if (expectedType && expectedType.type !== "TypeSum") {
        throw new Error(Errors.UNEXPECTED_INJECTION);
      }
      const { expr: expression } = expr;
      const actualType = typecheckExpr(
        expression,
        expectedType?.right ?? null,
        ctx
      );
      if (expectedType) {
        verifyTypesMatch(expectedType.right, actualType);
        return expectedType;
      } else {
        return TYPE_SUM(TYPE_BOT, actualType);
      }
    }
    case "Match": {
      const { cases, expr: expression } = expr;
      const exprType = typecheckExpr(expression, null, ctx);
      if (cases.length === 0) {
        throw new Error(Errors.ILLEGAL_EMPTY_MATCHING);
      }
      let caseBodyExpectedType: Type | null = expectedType;
      for (const matchCase of cases) {
        const extendedCtx = checkPattern(matchCase.pattern, exprType, ctx);
        const inferredType = typecheckExpr(
          matchCase.expr,
          expectedType,
          extendedCtx
        );
        if (caseBodyExpectedType != null) {
          verifyTypesMatch(caseBodyExpectedType, inferredType);
        } else {
          caseBodyExpectedType = inferredType;
        }
      }
      if (
        !isExhaustive(
          exprType,
          cases.map((case_) => case_.pattern)
        )
      ) {
        throw new Error(Errors.NONEXHAUSTIVE_MATCH_PATTERNS);
      }
      return caseBodyExpectedType!;
    }
    case "List": {
      if (expectedType && expectedType.type !== "TypeList") {
        throw new Error(Errors.UNEXPECTED_LIST);
      }
      const { exprs } = expr;
      let elementExpectedType: Type | null = expectedType;
      for (const element of exprs) {
        const inferredType = typecheckExpr(
          element,
          expectedType?.elementType ?? null,
          ctx
        );
        if (elementExpectedType) {
          verifyTypesMatch(elementExpectedType, inferredType);
        } else {
          elementExpectedType = inferredType;
        }
      }
      return TYPE_LIST(elementExpectedType ?? TYPE_BOT);
    }
    case "Cons": {
      const { head, tail } = expr;
      if (expectedType && expectedType.type !== "TypeList") {
        throw new Error(Errors.UNEXPECTED_LIST);
      }
      const headType = typecheckExpr(
        head,
        expectedType?.elementType ?? null,
        ctx
      );
      const tailType = typecheckExpr(tail, expectedType, ctx);
      if (tailType.type !== "TypeList") {
        throw new Error(Errors.NOT_A_LIST);
      }
      verifyTypesMatch(headType, tailType.elementType);
      return tailType;
    }
    case "ListHead": {
      const { expr: expression } = expr;
      const exprType = typecheckExpr(
        expression,
        expectedType && TYPE_LIST(expectedType),
        ctx
      );
      if (exprType.type !== "TypeList") {
        throw new Error(Errors.NOT_A_LIST);
      }
      return exprType.elementType;
    }
    case "ListTail": {
      const { expr: expression } = expr;
      const exprType = typecheckExpr(
        expression,
        expectedType && TYPE_LIST(expectedType),
        ctx
      );
      if (exprType.type !== "TypeList") {
        throw new Error(Errors.NOT_A_LIST);
      }
      return exprType;
    }
    case "ListIsEmpty": {
      const { expr: expression } = expr;
      const exprType = typecheckExpr(
        expression,
        expectedType && TYPE_LIST(expectedType),
        ctx
      );
      if (exprType.type !== "TypeList") {
        throw new Error(Errors.NOT_A_LIST);
      }
      return TYPE_BOOL;
    }
    case "Variant": {
      const { label, expr: value } = expr;
      let fieldExpectedType: Type | null = null;
      if (expectedType) {
        if (expectedType.type !== "TypeVariant") {
          throw new Error(Errors.UNEXPECTED_VARIANT);
        }
        const field = expectedType.fieldTypes.find(
          (field) => field.label === label
        );
        if (field == undefined) {
          throw new Error(Errors.UNEXPECTED_VARIANT_LABEL);
        }
        fieldExpectedType = field.fieldType!;
      }
      const fieldType = typecheckExpr(value!, fieldExpectedType, ctx);
      if (fieldExpectedType) {
        verifyTypesMatch(fieldExpectedType, fieldType);
      }
      return (
        expectedType ?? {
          type: "TypeVariant",
          fieldTypes: [{ type: "VariantFieldType", label, fieldType }],
        }
      );
    }
    case "Fix": {
      const { expr: func } = expr;
      const expected = expectedType && TYPE_FUN(expectedType, expectedType);
      const actualType = typecheckExpr(func, expected, ctx);
      if (actualType.type !== "TypeFun") {
        throw new Error(Errors.NOT_A_FUNCTION);
      }
      verifyTypesMatch(actualType.parametersTypes[0], actualType.returnType);
      return actualType.returnType;
    }

    case "ConstMemory": {
      if (!expectedType) {
        throw new Error(Errors.AMBIGUOUS_REFERENCE_TYPE);
      }
      if (expectedType.type !== "TypeRef") {
        throw new Error(Errors.UNEXPECTED_MEMORY_ADDRESS);
      }
      return expectedType;
    }
    case "Reference": {
      const { expr: initialValue } = expr;
      if (expectedType && expectedType.type === "TypeRef") {
        expectedType = expectedType.referredType;
      }
      const exprType = typecheckExpr(initialValue, expectedType, ctx);
      return TYPE_REF(exprType);
    }
    case "Dereference": {
      const { expr: reference } = expr;
      const refType = typecheckExpr(
        reference,
        expectedType && TYPE_REF(expectedType),
        ctx
      );
      if (refType.type !== "TypeRef") {
        throw new Error(Errors.NOT_A_REFERENCE);
      }
      return refType.referredType;
    }
    case "Assignment": {
      const { lhs, rhs } = expr;
      const lhsType = typecheckExpr(lhs, null, ctx);
      if (lhsType.type !== "TypeRef") {
        throw new Error(Errors.NOT_A_REFERENCE);
      }
      const rhsType = typecheckExpr(rhs, lhsType.referredType, ctx);
      verifyTypesMatch(rhsType, lhsType.referredType);
      return TYPE_UNIT;
    }
    case "Panic": {
      if (!expectedType) {
        return TYPE_BOT;
      }
      return expectedType;
    }
    case "Throw": {
      if (ctx.exceptionType == null) {
        throw new Error(Errors.EXCEPTION_TYPE_NOT_DECLARED);
      }
      if (!expectedType) {
        return TYPE_BOT;
      }
      const { expr: thrownValue } = expr;
      const valueType = typecheckExpr(thrownValue, ctx.exceptionType, ctx);
      verifyTypesMatch(ctx.exceptionType, valueType);
      return expectedType;
    }
    case "TryWith": {
      const { tryExpr, fallbackExpr } = expr;
      const tryType = typecheckExpr(tryExpr, expectedType, ctx);
      const fallbackType = typecheckExpr(fallbackExpr, expectedType, ctx);
      verifyTypesMatch(tryType, fallbackType);
      return tryType;
    }
    case "TryCatch": {
      const { tryExpr, pattern, fallbackExpr } = expr;
      const tryType = typecheckExpr(tryExpr, expectedType, ctx);
      if (ctx.exceptionType == null) {
        throw new Error(Errors.EXCEPTION_TYPE_NOT_DECLARED);
      }
      const fallbackExprCtx = checkPattern(pattern, ctx.exceptionType, ctx);
      const fallbackType = typecheckExpr(
        fallbackExpr,
        expectedType,
        fallbackExprCtx
      );
      verifyTypesMatch(tryType, fallbackType);
      return tryType;
    }

    case "TypeCast": {
      const { expr: expression, castType } = expr;
      const _ = typecheckExpr(expression, null, ctx);
      return castType;
    }
    default:
      throw new Error("Unknown expression type");
  }
}

function checkPattern(pattern: Pattern, type: Type, ctx: Context): Context {
  switch (pattern.type) {
    case "PatternVar": {
      return copyContextWithSymbol(ctx, pattern.name, type);
    }
    case "PatternInl": {
      if (type.type !== "TypeSum") {
        throw new Error(Errors.UNEXPECTED_PATTERN_FOR_TYPE);
      }
      return checkPattern(pattern.pattern, type.left, ctx);
    }
    case "PatternInr": {
      if (type.type !== "TypeSum") {
        throw new Error(Errors.UNEXPECTED_PATTERN_FOR_TYPE);
      }
      return checkPattern(pattern.pattern, type.right, ctx);
    }
    case "PatternVariant": {
      if (type.type !== "TypeVariant") {
        throw new Error(Errors.UNEXPECTED_PATTERN_FOR_TYPE);
      }
      const { label, pattern: innerPattern } = pattern;
      const { fieldTypes } = type;
      const field = fieldTypes.find((field) => field.label === label);
      if (field == undefined) {
        throw new Error(Errors.UNEXPECTED_PATTERN_FOR_TYPE);
      }
      return checkPattern(innerPattern!, field.fieldType!, ctx);
    }
    default:
      throw new Error("Unimplemented");
  }
}

function isExhaustive(type: Type, patterns: Pattern[]): boolean {
  const types = patterns.map((pattern) => pattern.type);
  if (types.some((type) => type === "PatternVar")) return true;
  switch (type.type) {
    case "TypeSum": {
      return types.includes("PatternInl") && types.includes("PatternInr");
    }
    case "TypeVariant": {
      const { fieldTypes } = type;
      const usedPatternLabels = (patterns as PatternVariant[]).map(
        (pattern) => pattern.label
      );
      for (const { label } of fieldTypes) {
        if (!usedPatternLabels.includes(label)) {
          return false;
        }
      }
      return true;
    }
    default:
      return false;
  }
}

function verifyTypesMatch(expected: Type, actual: Type) {
  // expected = super, actual = sub
  if (expected.type === "TypeTop") {
    return true;
  }
  if (actual.type === "TypeBottom") {
    return true;
  }
  if (expected.type === actual.type) {
    switch (expected.type) {
      case "TypeFun": {
        verifyTypesMatch(
          (actual as TypeFun).parametersTypes[0], // super
          expected.parametersTypes[0] // sub
        );
        verifyTypesMatch(expected.returnType, (actual as TypeFun).returnType);
        return true;
      }
      case "TypeTuple": {
        const [expected1, expected2] = expected.types;
        const [actual1, actual2] = (actual as TypeTuple).types;
        verifyTypesMatch(expected1, actual1);
        verifyTypesMatch(expected2, actual2);
        return true;
      }
      case "TypeRecord": {
        const actualFields = (actual as TypeRecord).fieldTypes;
        for (const { label, fieldType } of expected.fieldTypes) {
          const actualField = actualFields.find((f) => f.label === label);
          if (actualField == null) {
            throw new Error(Errors.MISSING_RECORD_FIELDS);
          }
          verifyTypesMatch(fieldType, actualField.fieldType);
        }
        return true;
      }
      case "TypeList": {
        verifyTypesMatch(
          expected.elementType,
          (actual as TypeList).elementType
        );
        return true;
      }
      case "TypeVariant": {
        const actualFields = (actual as TypeVariant).fieldTypes;
        for (const { label, fieldType } of actualFields) {
          const expectedField = expected.fieldTypes.find(
            (f) => f.label === label
          );
          if (expectedField == null) {
            throw new Error(Errors.UNEXPECTED_VARIANT_LABEL);
          }
          verifyTypesMatch(expectedField.fieldType!, fieldType!);
        }
        return true;
      }
      case "TypeRef": {
        verifyTypesMatch(
          expected.referredType,
          (actual as TypeRef).referredType
        );
        verifyTypesMatch(
          (actual as TypeRef).referredType,
          expected.referredType
        );
        return true;
      }
      case "TypeSum": {
        verifyTypesMatch(expected.left, (actual as TypeSum).left);
        verifyTypesMatch(expected.right, (actual as TypeSum).right);
      }
      default:
        return true;
    }
  }
  throw new Error(Errors.UNEXPECTED_SUBTYPE);
}
