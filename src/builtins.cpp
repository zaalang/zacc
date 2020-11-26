//
// builtins.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "builtins.h"
#include "ast.h"
#include "mir.h"
#include "query.h"
#include <iostream>
#include <cassert>

using namespace std;

namespace Builtin
{ 
  //|--------------------- Builtins -------------------------------------------
  //|--------------------------------------------------------------------------

  struct BuiltinModule : public ModuleDecl
  {
    BuiltinModule() noexcept;

    inline static BuiltinType voidtype = BuiltinType(BuiltinType::Void);
    inline static BuiltinType booltype = BuiltinType(BuiltinType::Bool);
    inline static BuiltinType chartype = BuiltinType(BuiltinType::Char);
    inline static BuiltinType i8type = BuiltinType(BuiltinType::I8);
    inline static BuiltinType i16type = BuiltinType(BuiltinType::I16);
    inline static BuiltinType i32type = BuiltinType(BuiltinType::I32);
    inline static BuiltinType i64type = BuiltinType(BuiltinType::I64);
    inline static BuiltinType isizetype = BuiltinType(BuiltinType::ISize);
    inline static BuiltinType u8type = BuiltinType(BuiltinType::U8);
    inline static BuiltinType u16type = BuiltinType(BuiltinType::U16);
    inline static BuiltinType u32type = BuiltinType(BuiltinType::U32);
    inline static BuiltinType u64type = BuiltinType(BuiltinType::U64);
    inline static BuiltinType usizetype = BuiltinType(BuiltinType::USize);
    inline static BuiltinType f32type = BuiltinType(BuiltinType::F32);
    inline static BuiltinType f64type = BuiltinType(BuiltinType::F64);

    inline static BuiltinType intliteraltype = BuiltinType(BuiltinType::IntLiteral);
    inline static BuiltinType floatliteraltype = BuiltinType(BuiltinType::FloatLiteral);
    inline static BuiltinType stringliteraltype = BuiltinType(BuiltinType::StringLiteral);
    inline static BuiltinType ptrliteraltype = BuiltinType(BuiltinType::PtrLiteral);

    Decl *make_typealias(string_view name, Type *type, long flags, int line)
    {
      auto ty = new TypeAliasDecl(SourceLocation{ line, 21 });

      ty->name = name;
      ty->type = type;
      ty->flags = TypeAliasDecl::Public | flags;
      ty->owner = this;

      decls.push_back(ty);

      return ty;
    }

    Decl *make_typealias(string_view name, Type *type, int line)
    {
      return make_typealias(name, type, 0, line);
    }

    Decl *make_concept(string_view text, int line)
    {
      auto koncept = new ConceptDecl(SourceLocation{ line, 21 });

      koncept->name = "var";
      koncept->flags = ConceptDecl::Public;
      koncept->owner = this;

      decls.push_back(koncept);

      return koncept;
    }

    Decl *make_function(Builtin::Kind kind, string_view text, long flags, int line)
    {
      map<string_view, Type*> typeargs;

      auto find_type = [&](string_view name) -> Type * {
        if (name == "void") return &voidtype;
        if (name == "bool") return &booltype;
        if (name == "char") return &chartype;
        if (name == "i8") return &i8type;
        if (name == "i16") return &i16type;
        if (name == "i32") return &i32type;
        if (name == "i64") return &i64type;
        if (name == "isize") return &isizetype;
        if (name == "u8") return &u8type;
        if (name == "u16") return &u16type;
        if (name == "u32") return &u32type;
        if (name == "u64") return &u64type;
        if (name == "usize") return &usizetype;
        if (name == "f32") return &f32type;
        if (name == "f64") return &f64type;
        if (name == "int") return &i32type;
        if (name == "float") return &f64type;
        if (name == "intptr") return &isizetype;
        if (name == "uintptr") return &usizetype;
        if (name == "#int") return &intliteraltype;
        if (name == "#float") return &floatliteraltype;
        if (name == "#string") return &stringliteraltype;
        if (name == "null") return &ptrliteraltype;
        if (auto j = typeargs.find(name); j != typeargs.end()) return j->second;
        throw logic_error("invalid type");
      };

      SourceText src(text.begin(), text.end());

      auto consume = [&](LexCursor &cursor) {

        Token tok;
        cursor = lex(src, cursor, tok);

        if (tok == Token::tilde && text[cursor.position] == '#')
        {
          auto beg = tok.text.begin();
          cursor = lex(src, cursor, tok);
          tok.text = string_view(&*beg, tok.text.end() - beg);
        }

        if (tok == Token::hash)
        {
          auto beg = tok.text.begin();
          cursor = lex(src, cursor, tok);
          tok.text = string_view(&*beg, tok.text.end() - beg);
        }

        return tok;
      };

      auto try_consume = [&](LexCursor &cursor, string_view txt) {

        auto beg = cursor;

        if (consume(cursor).text == txt)
          return true;

        cursor = beg;

        return false;
      };

      auto parse_sub_type = [&](LexCursor &cursor) -> Type * {

        auto tok = consume(cursor);
        auto type = find_type(tok.text);

        if (try_consume(cursor, "("))
        {
          vector<Type*> fields;

          while (true)
          {
            tok = consume(cursor);

            fields.push_back(find_type(tok.text));

            if (try_consume(cursor, "..."))
              fields.back() = new UnpackType(fields.back());

            if (!try_consume(cursor, ","))
              break;
          }

          consume(cursor);

          type = new FunctionType(type, new TupleType(fields));
        }

        if (try_consume(cursor, "["))
        {
          tok = consume(cursor);

          type = new ArrayType(type, find_type(tok.text));

          consume(cursor);
        }

        if (try_consume(cursor, "mut"))
        {
          if (try_consume(cursor, "*"))
            type = new PointerType(type);

          if (try_consume(cursor, "&"))
            type = new ReferenceType(type);
        }

        if (try_consume(cursor, "*"))
          type = new PointerType(new ConstType(type));

        if (try_consume(cursor, "&"))
          type = new ReferenceType(new ConstType(type));

        if (try_consume(cursor, "&&"))
          type = new ReferenceType(new QualArgType(type));

        return type;
      };

      auto parse_type = [&](LexCursor &cursor) -> Type * {

        if (try_consume(cursor, "("))
        {
          vector<Type*> fields;

          while (true)
          {
            fields.push_back(parse_sub_type(cursor));

            if (!try_consume(cursor, ","))
              break;
          }

          consume(cursor);

          return new TupleType(fields);
        }

        return parse_sub_type(cursor);
      };

      LexCursor cursor;
      cursor.lineno = line - 1;
      cursor.linestart = -31;

      if (try_consume(cursor, "pub"))
        flags |= FunctionDecl::Public;

      if (try_consume(cursor, "const"))
        flags |= FunctionDecl::Const;

      try_consume(cursor, "fn");

      auto name = consume(cursor);

      if (name.text == "[" || name.text == "(")
      {
        name.text = string_view(name.text.data(), name.text.length() + 1);

        consume(cursor);
      }

      auto fn = new FunctionDecl(name.loc);

      fn->flags = flags;
      fn->builtin = kind;
      fn->name = name.text;

      try_consume(cursor, "::");

      if (try_consume(cursor, "<"))
      {
        while (!try_consume(cursor, ">"))
        {
          auto arg = new TypeArgDecl(name.loc);

          arg->name = consume(cursor).text;

          fn->args.push_back(arg);

          typeargs[arg->name] = new TypeArgType(arg);

          if (try_consume(cursor, "="))
          {
            arg->defult = parse_type(cursor);
          }

          try_consume(cursor, ",");
        }
      }

      if (try_consume(cursor, "("))
      {
        while (!try_consume(cursor, ")"))
        {
          auto parm = new ParmVarDecl(name.loc);

          parm->type = parse_type(cursor);

          if (try_consume(cursor, "..."))
            parm->type = new PackType(parm->type);

          if (try_consume(cursor, "="))
          {
            auto value = consume(cursor);

            if (value.text == "0")
              parm->defult = new IntLiteralExpr(Numeric::int_literal(0), value.loc);

            if (value.text == "0.0")
              parm->defult = new FloatLiteralExpr(Numeric::float_literal(0.0), value.loc);

            if (value.text == "\"\"")
              parm->defult = new StringLiteralExpr("", value.loc);

            if (value.text == "'\\0'")
              parm->defult = new CharLiteralExpr(Numeric::int_literal(0), value.loc);

            if (value.text == "false")
              parm->defult = new BoolLiteralExpr(false, value.loc);

            if (value.text == "null")
              parm->defult = new PointerLiteralExpr(value.loc);

            if (value.text == "void")
              parm->defult = new VoidLiteralExpr(value.loc);

            if (value.text == "cast")
            {
              parm->defult = new CastExpr(typeargs["T"], new IntLiteralExpr(Numeric::int_literal(0), value.loc), value.loc);

              cursor.position += 6;
            }
          }

          fn->parms.push_back(parm);

          try_consume(cursor, ",");
        }
      }

      if (try_consume(cursor, "->"))
      {
        fn->returntype = parse_type(cursor);
      }

      fn->owner = this;

      decls.push_back(fn);

      return fn;
    }

    Decl *make_function(Builtin::Kind kind, string_view text, int line)
    {
      return make_function(kind, text, FunctionDecl::Builtin, line);
    }
  };

  BuiltinModule::BuiltinModule() noexcept
    : ModuleDecl("#builtin", __FILE__)
  {
    make_typealias("void", &voidtype, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("bool", &booltype, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("char", &chartype, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("i8", &i8type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("i16", &i16type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("i32", &i32type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("i64", &i64type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("isize", &isizetype, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("u8", &u8type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("u16", &u16type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("u32", &u32type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("u64", &u64type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("usize", &usizetype, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("f32", &f32type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("f64", &f64type, TypeAliasDecl::Implicit, __LINE__);
    make_typealias("byte", &u8type, __LINE__);
    make_typealias("int", &i32type, __LINE__);
    make_typealias("float", &f64type, __LINE__);
    make_typealias("intptr", &isizetype, __LINE__);
    make_typealias("uintptr", &usizetype, __LINE__);
    make_typealias("null", &ptrliteraltype, TypeAliasDecl::Implicit, __LINE__);

    make_concept("concept var<T> = true", __LINE__);

    make_function(Type_Void, "pub const fn void(void = void) -> void", __LINE__);
    make_function(Type_Bool, "pub const fn bool(bool = false) -> bool", __LINE__);
    make_function(Type_Char, "pub const fn char(char = '\\0') -> char", __LINE__);
    make_function(Type_I8, "pub const fn i8(i8 = 0) -> i8", __LINE__);
    make_function(Type_I16, "pub const fn i16(i16 = 0) -> i16", __LINE__);
    make_function(Type_I32, "pub const fn i32(i32 = 0) -> i32", __LINE__);
    make_function(Type_I64, "pub const fn i64(i64 = 0) -> i64", __LINE__);
    make_function(Type_ISize, "pub const fn isize(isize = 0) -> isize", __LINE__);
    make_function(Type_U8, "pub const fn u8(u8 = 0) -> u8", __LINE__);
    make_function(Type_U16, "pub const fn u16(u16 = 0) -> u16", __LINE__);
    make_function(Type_U32, "pub const fn u32(u32 = 0) -> u32", __LINE__);
    make_function(Type_U64, "pub const fn u64(u64 = 0) -> u64", __LINE__);
    make_function(Type_USize, "pub const fn usize(usize = 0) -> usize", __LINE__);
    make_function(Type_F32, "pub const fn f32(f32 = 0.0) -> f32", __LINE__);
    make_function(Type_F64, "pub const fn f64(f64 = 0.0) -> f64", __LINE__);
    make_function(Type_IntLiteral, "pub const fn #int(#int = 0) -> #int", __LINE__);
    make_function(Type_FloatLiteral, "pub const fn #float(#float = 0.0) -> #float", __LINE__);
    make_function(Type_StringLiteral, "pub const fn #string(#string = \"\") -> #string", __LINE__);
    make_function(Type_PtrLiteral, "pub const fn null<T = null>(null = null) -> T", __LINE__);

    make_function(Type_Ptr, "pub fn #ptr<T>(T = null) -> T", __LINE__);
    make_function(Type_Ref, "pub fn #ref<T>(T) -> T", __LINE__);
    make_function(Type_Enum, "pub fn #enum<T>(T = cast<T>(0)) -> T", __LINE__);
    make_function(Type_Lit, "pub fn #lit<T, V>() -> T", __LINE__);

    make_function(Array_Constructor, "pub fn #array<T>() -> T", FunctionDecl::Defaulted, __LINE__);
    make_function(Array_Copytructor, "pub fn #array<T>(T&&) -> T", FunctionDecl::Defaulted, __LINE__);
    make_function(Array_Assignment, "pub fn =<T>(T mut &, T&&) -> T mut &", FunctionDecl::Defaulted, __LINE__);
    make_function(Array_Destructor, "pub fn ~#array<T>(T mut &) -> void", FunctionDecl::Defaulted, __LINE__);

    make_function(Tuple_Constructor, "pub fn #tuple<T>() -> T", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_Inittructor, "pub fn #tuple<T>(T&&...) -> T", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_Copytructor, "pub fn #tuple<T>(T&&) -> T", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_Assignment, "pub fn =<T>(T mut &, T&&) -> T mut &", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_AssignmentEx, "pub fn =<T, U>(T mut &, U&&) -> T mut &", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_Destructor, "pub fn ~#tuple<T>(T mut &) -> void", FunctionDecl::Defaulted, __LINE__);

    make_function(Builtin_Destructor, "pub fn ~#builtin<T>(T mut &) -> void", __LINE__);

    make_function(Plus, "pub const fn +<T>(T) -> T", __LINE__);
    make_function(Minus, "pub const fn -<T>(T) -> T", __LINE__);
    make_function(Not, "pub const fn ~<T>(T) -> T", __LINE__);
    make_function(PreInc, "pub fn ++<T>(T mut &) -> T mut &", __LINE__);
    make_function(PreDec, "pub fn --<T>(T mut &) -> T mut &", __LINE__);
    make_function(DeRef, "pub fn *<T>(T*) -> T&", __LINE__);
    make_function(DeRef, "pub fn *<T>(T mut *) -> T mut &", __LINE__);
    make_function(Range, "pub const fn ..<T, U>(T, U) -> (T, U)", __LINE__);
    make_function(Range, "pub const fn ..=<T, U>(T, U) -> (T, U, void)", __LINE__);

    make_function(Add, "pub const fn +<T>(T, T) -> T", __LINE__);
    make_function(Sub, "pub const fn -<T>(T, T) -> T", __LINE__);
    make_function(Div, "pub const fn /<T>(T, T) -> T", __LINE__);
    make_function(Mul, "pub const fn *<T>(T, T) -> T", __LINE__);
    make_function(Rem, "pub const fn %<T>(T, T) -> T", __LINE__);
    make_function(Shl, "pub const fn <<<T>(T, int) -> T", __LINE__);
    make_function(Shr, "pub const fn >><T>(T, int) -> T", __LINE__);
    make_function(And, "pub const fn &<T>(T, T) -> T", __LINE__);
    make_function(Or, "pub const fn |<T>(T, T) -> T", __LINE__);
    make_function(Xor, "pub const fn ^<T>(T, T) -> T", __LINE__);

    make_function(LNot, "pub const fn !(bool) -> bool", __LINE__);
    make_function(LAnd, "pub const fn &&(bool, bool) -> bool", __LINE__);
    make_function(LOr, "pub const fn ||(bool, bool) -> bool", __LINE__);

    make_function(LT, "pub const fn <::<T>(T, T) -> bool", __LINE__);
    make_function(GT, "pub const fn >::<T>(T, T) -> bool", __LINE__);
    make_function(LE, "pub const fn <=::<T>(T, T) -> bool", __LINE__);
    make_function(GE, "pub const fn >=::<T>(T, T) -> bool", __LINE__);
    make_function(EQ, "pub const fn ==::<T>(T, T) -> bool", __LINE__);
    make_function(NE, "pub const fn !=::<T>(T, T) -> bool", __LINE__);
    make_function(Cmp, "pub const fn <=>::<T>(T, T) -> int", __LINE__);

    make_function(LT, "pub const fn <::<T>(T*, T*) -> bool", __LINE__);
    make_function(GT, "pub const fn >::<T>(T*, T*) -> bool", __LINE__);
    make_function(LE, "pub const fn <=::<T>(T*, T*) -> bool", __LINE__);
    make_function(GE, "pub const fn >=::<T>(T*, T*) -> bool", __LINE__);
    make_function(EQ, "pub const fn ==::<T>(T*, T*) -> bool", __LINE__);
    make_function(NE, "pub const fn !=::<T>(T*, T*) -> bool", __LINE__);
    make_function(Cmp, "pub const fn <=>::<T>(T*, T*) -> int", __LINE__);

    make_function(OffsetAdd, "pub fn +<T>(T, usize) -> T", __LINE__);
    make_function(OffsetSub, "pub fn -<T>(T, usize) -> T", __LINE__);
    make_function(Difference, "pub fn -<T>(T*, T*) -> usize", __LINE__);

    make_function(Assign, "pub fn =<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(AddAssign, "pub fn +=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(SubAssign, "pub fn -=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(DivAssign, "pub fn /=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(MulAssign, "pub fn *=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(RemAssign, "pub fn %=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(ShlAssign, "pub fn <<=<T>(T mut &, int) -> T mut &", __LINE__);
    make_function(ShrAssign, "pub fn >>=<T>(T mut &, int) -> T mut &", __LINE__);
    make_function(AndAssign, "pub fn &=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(OrAssign, "pub fn |=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(XorAssign, "pub fn ^=<T>(T mut &, T) -> T mut &", __LINE__);

    make_function(OffsetAddAssign, "pub fn +=<T>(T mut &, usize) -> T mut &", __LINE__);
    make_function(OffsetSubAssign, "pub fn -=<T>(T mut &, usize) -> T mut &", __LINE__);

    make_function(AddCarry, "pub fn __add_with_carry<T>(T, T) -> (T, T)", __LINE__);
    make_function(SubCarry, "pub fn __sub_with_carry<T>(T, T) -> (T, T)", __LINE__);
    make_function(MulCarry, "pub fn __mul_with_carry<T>(T, T) -> (T, T)", __LINE__);

    make_function(ArrayLen, "pub const fn len<T>(T&) -> usize", __LINE__);
    make_function(ArrayData, "pub fn data<T, N>(T[N]&) -> T*", __LINE__);
    make_function(ArrayData, "pub fn data<T, N>(T[N] mut &) -> T mut *", __LINE__);
    make_function(ArrayIndex, "pub fn []<T, N>(T[N]&, usize) -> T&", __LINE__);
    make_function(ArrayIndex, "pub fn []<T, N>(T[N] mut &, usize) -> T mut &", __LINE__);
    make_function(ArrayBegin, "pub fn begin<T, N>(T[N]&) -> T*", __LINE__);
    make_function(ArrayBegin, "pub fn begin<T, N>(T[N] mut &) -> T mut *", __LINE__);
    make_function(ArrayEnd, "pub fn end<T, N>(T[N]&) -> T*", __LINE__);
    make_function(ArrayEnd, "pub fn end<T, N>(T[N] mut &) -> T mut *", __LINE__);
    make_function(ArrayEq, "pub fn ==<T, N>(T[N]&, T[N]&) -> bool", FunctionDecl::Defaulted, __LINE__);
    make_function(ArrayCmp, "pub fn <=><T, N>(T[N]&, T[N]&) -> int", FunctionDecl::Defaulted, __LINE__);

    make_function(TupleLen, "pub const fn len<T>(T&) -> usize", __LINE__);
    make_function(TupleEq, "pub fn ==<T>(T&, T&) -> bool", FunctionDecl::Defaulted, __LINE__);
    make_function(TupleEqEx, "pub fn ==<T, U>(T&, U&) -> bool", FunctionDecl::Defaulted, __LINE__);
    make_function(TupleCmp, "pub fn <=><T>(T&, T&) -> int", FunctionDecl::Defaulted, __LINE__);
    make_function(TupleCmpEx, "pub fn <=><T, U>(T&, U&) -> int", FunctionDecl::Defaulted, __LINE__);

    make_function(StringLen, "pub const fn len(#string) -> usize", __LINE__);
    make_function(StringData, "pub fn data(#string) -> u8*", __LINE__);
    make_function(StringSlice, "pub const fn [](#string, (usize, usize)) -> #string", __LINE__);
    make_function(StringAppend, "pub const fn +(#string, #string) -> #string", __LINE__);
    make_function(StringCreate, "pub const fn #string(u8*, usize) -> #string", __LINE__);

    make_function(Bool, "pub const fn bool<T>(T) -> bool", __LINE__);

    make_function(CallOp, "pub fn ()<R, V>(R(V...)&, V&&...) -> R", __LINE__);

    make_function(is_same, "pub const fn __is_same<T, U>() -> bool", __LINE__);
    make_function(is_const, "pub const fn __is_const<T>() -> bool", __LINE__);
    make_function(is_rvalue, "pub const fn __is_rvalue<T>() -> bool", __LINE__);
    make_function(is_match, "pub const fn __is_match<T, U>() -> bool", __LINE__);
    make_function(is_array, "pub const fn __is_array<T>() -> bool", __LINE__);
    make_function(is_tuple, "pub const fn __is_tuple<T>() -> bool", __LINE__);
    make_function(is_allocator_aware, "pub const fn __is_allocator_aware<T>() -> bool", __LINE__);
    make_function(tuple_len, "pub const fn __tuple_len<T>() -> usize", __LINE__);
    make_function(array_len, "pub const fn __array_len<T>() -> usize", __LINE__);

    make_function(is_nan, "pub const fn __is_nan<T>(T) -> bool", __LINE__);
    make_function(is_finite, "pub const fn __is_finite<T>(T) -> bool", __LINE__);
    make_function(is_normal, "pub const fn __is_normal<T>(T) -> bool", __LINE__);
    make_function(nan, "pub const fn __nan() -> #float", __LINE__);
    make_function(inf, "pub const fn __inf() -> #float", __LINE__);

    make_function(is_integral, "pub const fn __is_integral<T>() -> bool", __LINE__);
    make_function(is_floating_point, "pub const fn __is_floating_point<T>() -> bool", __LINE__);
    make_function(is_arithmetic, "pub const fn __is_arithmetic<T>() -> bool", __LINE__);

    make_function(clz, "pub const fn __clz<T>(T) -> int", __LINE__);
    make_function(ctz, "pub const fn __ctz<T>(T) -> int", __LINE__);
    make_function(popcnt, "pub const fn __popcnt<T>(T) -> int", __LINE__);
    make_function(signbit, "pub const fn __signbit<T>(T) -> int", __LINE__);
    make_function(abs, "pub const fn __abs<T>(T) -> T", __LINE__);
    make_function(min, "pub const fn __min<T>(T, T) -> T", __LINE__);
    make_function(max, "pub const fn __max<T>(T, T) -> T", __LINE__);
    make_function(floor, "pub const fn __floor<T>(T) -> T", __LINE__);
    make_function(ceil, "pub const fn __ceil<T>(T) -> T", __LINE__);
    make_function(round, "pub const fn __round<T>(T) -> T", __LINE__);
    make_function(trunc, "pub const fn __trunc<T>(T) -> T", __LINE__);
    make_function(copysign, "pub const fn __copysign<T>(T, T) -> T", __LINE__);
    make_function(frexp, "pub const fn __frexp<T>(T) -> (T, int)", __LINE__);
    make_function(ldexp, "pub const fn __ldexp<T>(T, int) -> T", __LINE__);
    make_function(sqrt, "pub const fn __sqrt<T>(T) -> T", __LINE__);

    make_function(memset, "pub fn __memset(void mut *, u8, usize) -> void mut *", __LINE__);
    make_function(memcpy, "pub fn __memcpy(void mut *, void*, usize) -> void mut *", __LINE__);
    make_function(memmove, "pub fn __memmove(void mut *, void*, usize) -> void mut *", __LINE__);
    make_function(memfind, "pub fn __memfind(void*, u8, usize) -> usize", __LINE__);

    make_function(__site__, "pub const fn __site__() -> (#string, int, int, #string)", __LINE__);
  }

  //|///////////////////// type /////////////////////////////////////////////
  auto type(Kind kind) -> Type *
  {
    switch (kind)
    {
      case Builtin::Type_Void:
        return &BuiltinModule::voidtype;

      case Builtin::Type_Bool:
        return &BuiltinModule::booltype;

      case Builtin::Type_Char:
        return &BuiltinModule::chartype;

      case Builtin::Type_I8:
        return &BuiltinModule::i8type;

      case Builtin::Type_I16:
        return &BuiltinModule::i16type;

      case Builtin::Type_I32:
        return &BuiltinModule::i32type;

      case Builtin::Type_I64:
        return &BuiltinModule::i64type;

      case Builtin::Type_ISize:
        return &BuiltinModule::isizetype;

      case Builtin::Type_U8:
        return &BuiltinModule::u8type;

      case Builtin::Type_U16:
        return &BuiltinModule::u16type;

      case Builtin::Type_U32:
        return &BuiltinModule::u32type;

      case Builtin::Type_U64:
        return &BuiltinModule::u64type;

      case Builtin::Type_USize:
        return &BuiltinModule::usizetype;

      case Builtin::Type_F32:
        return &BuiltinModule::f32type;

      case Builtin::Type_F64:
        return &BuiltinModule::f64type;

      case Builtin::Type_IntLiteral:
        return &BuiltinModule::intliteraltype;

      case Builtin::Type_FloatLiteral:
        return &BuiltinModule::floatliteraltype;

      case Builtin::Type_StringLiteral:
        return &BuiltinModule::stringliteraltype;

      case Builtin::Type_PtrLiteral:
        return &BuiltinModule::ptrliteraltype;

      default:
        assert(false);
    }

    throw logic_error("invalid builtin type");
  }

  //|///////////////////// fn ///////////////////////////////////////////////
  auto fn(Decl *module, Builtin::Kind kind, Type *T1, Type *T2) -> FnSig
  {
    assert(module->kind() == Decl::Module && decl_cast<ModuleDecl>(module)->name == "#builtin");

    for(auto &decl : decl_cast<ModuleDecl>(module)->decls)
    {
      if (decl->kind() != Decl::Function)
        continue;

      if (auto fn = decl_cast<FunctionDecl>(decl); fn->builtin == kind)
      {
        FnSig fx(fn);

        if (T1)
          fx.set_type(fn->args[0], T1);

        if (T2)
          fx.set_type(fn->args[1], T2);

        return fx;
      }
    }

    throw logic_error("invalid builtin function");
  }

  //|///////////////////// where ////////////////////////////////////////////
  auto where(FnSig const &fx) -> bool
  {
    auto is_builtin = [](Type *type) { return type->klass() == Type::Builtin; };
    auto is_int_literal = [](Type *type) { return type == &BuiltinModule::intliteraltype; };
    auto is_float_literal = [](Type *type) { return type == &BuiltinModule::floatliteraltype; };
    auto is_ptr_literal = [](Type *type) { return type == &BuiltinModule::ptrliteraltype; };

    auto is_int = [&](Type *type) { return is_int_type(type) || is_int_literal(type); };
    auto is_float = [&](Type *type) { return is_float_type(type) || is_float_literal(type); };
    auto is_numeric = [&](Type *type) { return is_int(type) || is_float(type); };
    auto is_enum = [&](Type *type) { return is_enum_type(type); };
    auto is_bool = [&](Type *type) { return is_bool_type(type); };
    auto is_char = [&](Type *type) { return is_char_type(type); };
    auto is_pointer = [&](Type *type) { return is_pointer_type(type); };
    auto is_reference = [&](Type *type) { return is_reference_type(type); };

    switch (fx.fn->builtin)
    {
      case Builtin::Type_Ptr:
      case Builtin::Type_PtrLiteral:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_pointer_type(T->second) || is_ptr_literal(T->second);
        break;

      case Builtin::Type_Ref:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_reference_type(T->second);
        break;

      case Builtin::Array_Constructor:
      case Builtin::Array_Copytructor:
      case Builtin::Array_Assignment:
      case Builtin::Array_Destructor:
      case Builtin::ArrayLen:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_array_type(T->second);
        break;

      case Builtin::Tuple_Constructor:
      case Builtin::Tuple_Copytructor:
      case Builtin::Tuple_Assignment:
      case Builtin::Tuple_Destructor:
      case Builtin::TupleLen:
      case Builtin::TupleEq:
      case Builtin::TupleCmp:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_tuple_type(T->second);
        break;

      case Builtin::Tuple_AssignmentEx:
      case Builtin::TupleEqEx:
      case Builtin::TupleCmpEx:
        if (auto T = fx.find_type(fx.fn->args[0]), U = fx.find_type(fx.fn->args[1]); T != fx.typeargs.end() && U != fx.typeargs.end())
          return is_tuple_type(T->second) && is_tuple_type(U->second) && T->second != U->second && type_cast<TupleType>(T->second)->fields.size() == type_cast<TupleType>(U->second)->fields.size();
        break;

      case Builtin::Bool:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_bool(T->second) || is_pointer(T->second) || is_reference(T->second) || is_ptr_literal(T->second) || is_int_literal(T->second);
        break;

      case Builtin::Plus:
      case Builtin::Minus:
      case Builtin::Add:
      case Builtin::Sub:
      case Builtin::Div:
      case Builtin::Mul:
      case Builtin::Rem:
      case Builtin::AddAssign:
      case Builtin::SubAssign:
      case Builtin::DivAssign:
      case Builtin::MulAssign:
      case Builtin::RemAssign:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_numeric(T->second) || is_char(T->second);
        break;

      case Builtin::LT:
      case Builtin::GT:
      case Builtin::LE:
      case Builtin::GE:
      case Builtin::EQ:
      case Builtin::NE:
      case Builtin::Cmp:
        if (is_pointer(decl_cast<ParmVarDecl>(fx.fn->parms[0])->type))
          return true;
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_builtin(T->second) || is_enum(T->second);
        break;

      case Builtin::OffsetAdd:
      case Builtin::OffsetSub:
      case Builtin::OffsetAddAssign:
      case Builtin::OffsetSubAssign:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_pointer(T->second);
        break;

      case Builtin::Not:
      case Builtin::And:
      case Builtin::Or:
      case Builtin::Xor:
      case Builtin::AndAssign:
      case Builtin::OrAssign:
      case Builtin::XorAssign:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_int(T->second) || is_bool(T->second) || is_char(T->second);
        break;

      case Builtin::Shl:
      case Builtin::Shr:
      case Builtin::ShlAssign:
      case Builtin::ShrAssign:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_int(T->second) || is_char(T->second);;
        break;

      case Builtin::clz:
      case Builtin::ctz:
      case Builtin::popcnt:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_int(T->second) || is_bool(T->second) || is_char(T->second);
        break;

      case Builtin::signbit:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_int(T->second) || is_float(T->second);
        break;

      case Builtin::PreInc:
      case Builtin::PreDec:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_numeric(T->second) || is_pointer(T->second) || is_char(T->second);
        break;

      case Builtin::Assign:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_builtin(T->second) || is_enum(T->second) || is_pointer(T->second) || is_reference(T->second);
        break;

      case Builtin::is_const:
      case Builtin::is_rvalue:
      case Builtin::is_array:
      case Builtin::is_tuple:
      case Builtin::is_allocator_aware:
      case Builtin::is_integral:
      case Builtin::is_floating_point:
      case Builtin::is_arithmetic:
        return fx.typeargs.size() == 1;

      case Builtin::is_same:
      case Builtin::is_match:
        return fx.typeargs.size() == 2;

      case Builtin::array_len:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_array_type(T->second);
        break;

      case Builtin::tuple_len:
        if (auto T = fx.find_type(fx.fn->args[0]); T != fx.typeargs.end())
          return is_tuple_type(T->second);
        break;

      default:
        return true;
    }

    return false;
  }
}

//|///////////////////// make_builtin_module ////////////////////////////////
Decl *make_builtin_module(AST *ast)
{
  return ast->make_decl<Builtin::BuiltinModule>();
}
