//
// builtins.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include <vector>
#include <string_view>

class AST;
class Decl;
class Type;
class FnSig;

//---------------------- Builtins -------------------------------------------
//---------------------------------------------------------------------------

namespace Builtin
{
  enum Kind : int
  {
    Type_Void,
    Type_Bool,
    Type_Char,
    Type_I8,
    Type_I16,
    Type_I32,
    Type_I64,
    Type_ISize,
    Type_U8,
    Type_U16,
    Type_U32,
    Type_U64,
    Type_USize,
    Type_F32,
    Type_F64,

    Type_Ptr,
    Type_Ref,
    Type_Enum,
    Type_Lit,

    Type_IntLiteral,
    Type_FloatLiteral,
    Type_StringLiteral,
    Type_PtrLiteral,

    Default_Constructor,
    Default_Copytructor,
    Default_Assignment,
    Default_Equality,
    Default_Compare,
    Default_Destructor,

    Array_Constructor,
    Array_Copytructor,
    Array_Assignment,
    Array_Destructor,

    Tuple_Constructor,
    Tuple_Inittructor,
    Tuple_Copytructor,
    Tuple_Assignment,
    Tuple_AssignmentEx,
    Tuple_Destructor,

    Builtin_Destructor,

    Plus,
    Minus,
    Not,
    LNot,
    PreInc,
    PreDec,
    DeRef,
    Range,

    Add,
    Sub,
    Div,
    Mul,
    Rem,
    Shl,
    Shr,
    And,
    Or,
    Xor,
    LAnd,
    LOr,
    LT,
    GT,
    LE,
    GE,
    EQ,
    NE,
    Cmp,
    Assign,
    MulAssign,
    DivAssign,
    RemAssign,
    AddAssign,
    SubAssign,
    ShlAssign,
    ShrAssign,
    AndAssign,
    XorAssign,
    OrAssign,
    AddCarry,
    SubCarry,
    MulCarry,

    OffsetAdd,
    OffsetSub,
    Difference,
    OffsetAddAssign,
    OffsetSubAssign,

    ArrayLen,
    ArrayData,
    ArrayIndex,
    ArrayBegin,
    ArrayEnd,
    ArrayEq,
    ArrayCmp,

    TupleLen,
    TupleEq,
    TupleEqEx,
    TupleCmp,
    TupleCmpEx,

    StringLen,
    StringData,
    StringSlice,
    StringAppend,
    StringCreate,

    Bool,

    CallOp,

    is_same,
    is_const,
    is_rvalue,
    is_match,
    tuple_len,
    array_len,

    is_nan,
    is_finite,
    is_normal,
    nan,
    inf,

    is_integral,
    is_floating_point,
    is_arithmetic,

    clz,
    ctz,
    popcnt,
    signbit,

    abs,
    min,
    max,
    floor,
    ceil,
    round,
    trunc,
    copysign,
    frexp,
    ldexp,
    sqrt,

    is_allocator_aware,

    memset,
    memcpy,
    memmove,
    memfind,

    __site__,

    Module,
  };

  auto type(Kind kind) -> Type *;

  auto fn(Decl *module, Builtin::Kind kind, Type *T1 = nullptr, Type *T2 = nullptr) -> FnSig;

  auto where(FnSig const &fx) -> bool;
};

Decl *make_builtin_module(AST *ast);
