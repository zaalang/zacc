//
// builtins.cpp
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
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

    static inline BuiltinType voidtype = BuiltinType(BuiltinType::Void);
    static inline BuiltinType booltype = BuiltinType(BuiltinType::Bool);
    static inline BuiltinType chartype = BuiltinType(BuiltinType::Char);
    static inline BuiltinType i8type = BuiltinType(BuiltinType::I8);
    static inline BuiltinType i16type = BuiltinType(BuiltinType::I16);
    static inline BuiltinType i32type = BuiltinType(BuiltinType::I32);
    static inline BuiltinType i64type = BuiltinType(BuiltinType::I64);
    static inline BuiltinType isizetype = BuiltinType(BuiltinType::ISize);
    static inline BuiltinType u8type = BuiltinType(BuiltinType::U8);
    static inline BuiltinType u16type = BuiltinType(BuiltinType::U16);
    static inline BuiltinType u32type = BuiltinType(BuiltinType::U32);
    static inline BuiltinType u64type = BuiltinType(BuiltinType::U64);
    static inline BuiltinType usizetype = BuiltinType(BuiltinType::USize);
    static inline BuiltinType f32type = BuiltinType(BuiltinType::F32);
    static inline BuiltinType f64type = BuiltinType(BuiltinType::F64);

    static inline BuiltinType intliteraltype = BuiltinType(BuiltinType::IntLiteral);
    static inline BuiltinType floatliteraltype = BuiltinType(BuiltinType::FloatLiteral);
    static inline BuiltinType stringliteraltype = BuiltinType(BuiltinType::StringLiteral);
    static inline BuiltinType declidliteraltype = BuiltinType(BuiltinType::DeclidLiteral);
    static inline BuiltinType typeidliteraltype = BuiltinType(BuiltinType::TypeidLiteral);
    static inline BuiltinType ptrliteraltype = BuiltinType(BuiltinType::PtrLiteral);

    Decl *make_typealias(string_view name, Type *type, long flags, int line)
    {
      auto ty = new TypeAliasDecl(SourceLocation{ line, 21 });

      ty->name = Ident::from(name);
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

      koncept->name = Ident::kw_var;
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
        if (name == "#declid") return &declidliteraltype;
        if (name == "#typeid") return &typeidliteraltype;
        if (name == "null") return &ptrliteraltype;
        if (name == "var") return new TypeArgType(new TypeArgDecl(Ident::kw_var, {}));
        if (auto j = typeargs.find(name); j != typeargs.end()) return j->second;
        throw logic_error("invalid type");
      };

      SourceText src(text.begin(), text.end());

      auto consume = [&](LexCursor &cursor) {

        Token tok;
        cursor = lex(src, cursor, tok);

        if (tok == Token::tilde && text[cursor.position] == '#')
        {
          auto beg = tok.text.data();
          cursor = lex(src, cursor, tok);
          cursor = lex(src, cursor, tok);
          tok.text = string_view(beg, tok.text.length() + 2);
        }

        if (tok == Token::hash && text[cursor.position] != '#')
        {
          auto beg = tok.text.data();
          cursor = lex(src, cursor, tok);
          tok.text = string_view(beg, tok.text.length() + 1);
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

          if (tok == Token::r_square)
            type = new SliceType(type);
          else
            type = new ArrayType(type, find_type(tok.text));

          if (tok != Token::r_square)
            consume(cursor);
        }

        while (true)
        {
          if (try_consume(cursor, "mut"))
          {
            if (try_consume(cursor, "*"))
              type = new PointerType(type);

            if (try_consume(cursor, "&"))
              type = new ReferenceType(type);
          }

          else if (try_consume(cursor, "*"))
            type = new PointerType(new ConstType(type));

          else if (try_consume(cursor, "&"))
            type = new ReferenceType(new ConstType(type));

          else if (try_consume(cursor, "&&"))
            type = new ReferenceType(new QualArgType(type));

          else
            break;
        }

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
      fn->name = Ident::from(name.text);

      try_consume(cursor, "::");

      if (try_consume(cursor, "<"))
      {
        while (!try_consume(cursor, ">"))
        {
          auto name = consume(cursor);

          auto arg = new TypeArgDecl(name.loc);

          arg->name = Ident::from(name.text);
          arg->owner = fn;

          fn->args.push_back(arg);

          typeargs[name.text] = new TypeArgType(arg);

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

          if (try_consume(cursor, "#"))
            parm->flags |= ParmVarDecl::Literal;

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
              parm->defult = new CastExpr(parm->type, new IntLiteralExpr(Numeric::int_literal(0), value.loc), value.loc);

              cursor.position += 3;
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
    : ModuleDecl(Ident::from("#builtin"), __FILE__)
  {
    make_typealias("void", &voidtype, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("bool", &booltype, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("char", &chartype, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("i8", &i8type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("i16", &i16type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("i32", &i32type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("i64", &i64type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("isize", &isizetype, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("u8", &u8type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("u16", &u16type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("u32", &u32type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("u64", &u64type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("usize", &usizetype, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("f32", &f32type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("f64", &f64type, TypeAliasDecl::Builtin, __LINE__);
    make_typealias("byte", &u8type, __LINE__);
    make_typealias("int", &i32type, __LINE__);
    make_typealias("float", &f64type, __LINE__);
    make_typealias("intptr", &isizetype, __LINE__);
    make_typealias("uintptr", &usizetype, __LINE__);
    make_typealias("null", &ptrliteraltype, TypeAliasDecl::Builtin, __LINE__);

    make_concept("concept var<T> = true", __LINE__);

    make_function(Type_Void, "pub const fn void(void = void) -> void", FunctionDecl::Builtin, __LINE__);
    make_function(Type_Bool, "pub const fn bool(bool = false) -> bool", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_Char, "pub const fn char(char = '\\0') -> char", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_I8, "pub const fn i8(i8 = 0) -> i8", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_I16, "pub const fn i16(i16 = 0) -> i16", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_I32, "pub const fn i32(i32 = 0) -> i32", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_I64, "pub const fn i64(i64 = 0) -> i64", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_ISize, "pub const fn isize(isize = 0) -> isize", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_U8, "pub const fn u8(u8 = 0) -> u8", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_U16, "pub const fn u16(u16 = 0) -> u16", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_U32, "pub const fn u32(u32 = 0) -> u32", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_U64, "pub const fn u64(u64 = 0) -> u64", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_USize, "pub const fn usize(usize = 0) -> usize", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_F32, "pub const fn f32(f32 = 0.0) -> f32", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_F64, "pub const fn f64(f64 = 0.0) -> f64", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_IntLiteral, "pub const fn #int(#int = 0) -> #int", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_FloatLiteral, "pub const fn #float(#float = 0.0) -> #float", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_StringLiteral, "pub const fn #string(#string = \"\") -> #string", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_DeclidLiteral, "pub const fn #declid(#declid = cast(0)) -> #declid", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_TypeidLiteral, "pub const fn #typeid(#typeid = cast(0)) -> #typeid", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_PtrLiteral, "pub const fn null<T = null>(null = null) -> T", FunctionDecl::Builtin, __LINE__);

    make_function(Type_Ptr, "pub fn #ptr<T>(T = null) -> T", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_Ref, "pub fn #ref<T>(T) -> T", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_Enum, "pub fn #enum<T>(T = cast(0)) -> T", FunctionDecl::Builtin | FunctionDecl::Constructor, __LINE__);
    make_function(Type_Lit, "pub fn #lit<T, V>() -> T", FunctionDecl::Builtin, __LINE__);

    make_function(Array_Constructor, "pub fn #array<T>() -> T", FunctionDecl::Defaulted | FunctionDecl::Constructor, __LINE__);
    make_function(Array_Copytructor, "pub fn #array<T>(T&&) -> T", FunctionDecl::Defaulted, __LINE__);
    make_function(Array_Assignment, "pub fn =<T>(T mut &, T&&) -> T mut &", FunctionDecl::Defaulted, __LINE__);
    make_function(Array_Destructor, "pub fn ~#array<T>(T mut &) -> void", FunctionDecl::Defaulted | FunctionDecl::Destructor, __LINE__);

    make_function(Tuple_Constructor, "pub fn #tuple<T>() -> T", FunctionDecl::Defaulted | FunctionDecl::Constructor, __LINE__);
    make_function(Tuple_Inittructor, "pub fn #tuple<T>(T&&...) -> T", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_Copytructor, "pub fn #tuple<T>(T&&) -> T", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_CopytructorEx, "pub fn #tuple<T, U>(U&&) -> T", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_Assignment, "pub fn =<T>(T mut &, T&&) -> T mut &", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_AssignmentEx, "pub fn =<T, U>(T mut &, U&&) -> T mut &", FunctionDecl::Defaulted, __LINE__);
    make_function(Tuple_Destructor, "pub fn ~#tuple<T>(T mut &) -> void", FunctionDecl::Defaulted | FunctionDecl::Destructor, __LINE__);

    make_function(Builtin_Destructor, "pub fn ~#builtin<T>(T mut &) -> void", FunctionDecl::Builtin | FunctionDecl::Destructor, __LINE__);

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
    make_function(Shl, "pub const fn <<<T, U>(T, U) -> T", __LINE__);
    make_function(Shr, "pub const fn >><T, U>(T, U) -> T", __LINE__);
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

    make_function(OffsetAdd, "pub fn +<T>(T, usize) -> T", __LINE__);
    make_function(OffsetSub, "pub fn -<T>(T, usize) -> T", __LINE__);
    make_function(Difference, "pub fn -<T>(T*, T*) -> usize", __LINE__);

    make_function(Assign, "pub fn =<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(AddAssign, "pub fn +=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(SubAssign, "pub fn -=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(DivAssign, "pub fn /=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(MulAssign, "pub fn *=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(RemAssign, "pub fn %=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(ShlAssign, "pub fn <<=<T, U>(T mut &, U) -> T mut &", __LINE__);
    make_function(ShrAssign, "pub fn >>=<T, U>(T mut &, U) -> T mut &", __LINE__);
    make_function(AndAssign, "pub fn &=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(OrAssign, "pub fn |=<T>(T mut &, T) -> T mut &", __LINE__);
    make_function(XorAssign, "pub fn ^=<T>(T mut &, T) -> T mut &", __LINE__);

    make_function(OffsetAddAssign, "pub fn +=<T>(T mut &, usize) -> T mut &", __LINE__);
    make_function(OffsetSubAssign, "pub fn -=<T>(T mut &, usize) -> T mut &", __LINE__);

    make_function(AddCarry, "pub fn __add_with_carry<T>(T, T) -> (T, T)", __LINE__);
    make_function(SubBorrow, "pub fn __sub_with_borrow<T>(T, T) -> (T, T)", __LINE__);
    make_function(MulCarry, "pub fn __mul_with_carry<T>(T, T) -> (T, T)", __LINE__);

    make_function(ArrayLen, "pub const fn len<T>(T&) -> usize", __LINE__);
    make_function(ArrayData, "pub fn data<T, N>(T[N]&) -> T*", __LINE__);
    make_function(ArrayData, "pub fn data<T, N>(T[N] mut &) -> T mut *", __LINE__);
    make_function(ArrayIndex, "pub fn []<T, N>(T[N]&, usize) -> T&", __LINE__);
    make_function(ArrayIndex, "pub fn []<T, N>(T[N] mut &, usize) -> T mut &", __LINE__);
    make_function(ArrayIndex, "pub fn []<T, N>(T[N]&, T*) -> T&", __LINE__);
    make_function(ArrayIndex, "pub fn []<T, N>(T[N] mut &, T*) -> T mut &", __LINE__);
    make_function(ArrayBegin, "pub fn begin<T, N>(T[N]&) -> T*", __LINE__);
    make_function(ArrayBegin, "pub fn begin<T, N>(T[N] mut &) -> T mut *", __LINE__);
    make_function(ArrayEnd, "pub fn end<T, N>(T[N]&) -> T*", __LINE__);
    make_function(ArrayEnd, "pub fn end<T, N>(T[N] mut &) -> T mut *", __LINE__);
    make_function(ArrayEq, "pub const fn ==<T>(T&, T&) -> bool", FunctionDecl::Defaulted, __LINE__);
    make_function(ArrayCmp, "pub const fn <=><T>(T&, T&) -> int", FunctionDecl::Defaulted, __LINE__);
    make_function(ArrayCreate, "pub const fn __array_literal<T>(T*, usize) -> T[]", __LINE__);

    make_function(TupleLen, "pub const fn len<T>(T&) -> usize", __LINE__);
    make_function(TupleEq, "pub const fn ==<T>(T&, T&) -> bool", FunctionDecl::Defaulted, __LINE__);
    make_function(TupleEqEx, "pub const fn ==<T, U>(T&, U&) -> bool", FunctionDecl::Defaulted, __LINE__);
    make_function(TupleCmp, "pub const fn <=><T>(T&, T&) -> int", FunctionDecl::Defaulted, __LINE__);
    make_function(TupleCmpEx, "pub const fn <=><T, U>(T&, U&) -> int", FunctionDecl::Defaulted, __LINE__);

    make_function(StringLen, "pub const fn len(#string) -> usize", __LINE__);
    make_function(StringData, "pub fn data(#string) -> u8*", __LINE__);
    make_function(StringIndex, "pub fn [](#string, u8*) -> u8&", __LINE__);
    make_function(StringBegin, "pub fn begin(#string) -> u8*", __LINE__);
    make_function(StringEnd, "pub fn end(#string) -> u8*", __LINE__);
    make_function(StringSlice, "pub const fn [](#string, (usize, usize)) -> #string", __LINE__);
    make_function(StringAppend, "pub const fn +(#string, #string) -> #string", __LINE__);
    make_function(StringCreate, "pub const fn #string(u8*, usize) -> #string", __LINE__);
    make_function(StringCreate, "pub const fn __string_literal(u8*, usize) -> #string", __LINE__);

    make_function(SliceLen, "pub const fn len<T>(T) -> usize", __LINE__);
    make_function(SliceData, "pub fn data<T>(T[]) -> T*", __LINE__);
    make_function(SliceIndex, "pub fn []<T>(T[], T*) -> T&", __LINE__);
    make_function(SliceBegin, "pub fn begin<T>(T[]) -> T*", __LINE__);
    make_function(SliceEnd, "pub fn end<T>(T[]) -> T*", __LINE__);

    make_function(Bool, "pub const fn bool<T>(T) -> bool", __LINE__);

    make_function(CallOp, "pub fn ()<R, V>(R(V...)&, V&&...) -> R", __LINE__);

    make_function(is_same, "pub const fn __is_same<T, U>() -> bool", __LINE__);
    make_function(is_const, "pub const fn __is_const<T>() -> bool", __LINE__);
    make_function(is_rvalue, "pub const fn __is_rvalue<T>() -> bool", __LINE__);
    make_function(is_match, "pub const fn __is_match<U, T>() -> bool", __LINE__);
    make_function(is_enum, "pub const fn __is_enum<T>() -> bool", __LINE__);
    make_function(is_array, "pub const fn __is_array<T>() -> bool", __LINE__);
    make_function(is_tuple, "pub const fn __is_tuple<T>() -> bool", __LINE__);
    make_function(is_union, "pub const fn __is_union<T>() -> bool", __LINE__);
    make_function(is_struct, "pub const fn __is_struct<T>() -> bool", __LINE__);
    make_function(is_vtable, "pub const fn __is_vtable<T>() -> bool", __LINE__);
    make_function(is_lambda, "pub const fn __is_lambda<T>() -> bool", __LINE__);
    make_function(is_slice, "pub const fn __is_slice<T>() -> bool", __LINE__);
    make_function(is_builtin, "pub const fn __is_builtin<T>() -> bool", __LINE__);
    make_function(is_pointer, "pub const fn __is_pointer<T>() -> bool", __LINE__);
    make_function(is_reference, "pub const fn __is_reference<T>() -> bool", __LINE__);
    make_function(is_instance, "pub const fn __is_instance<U, T>() -> bool", __LINE__);
    make_function(is_trivial_copy, "pub const fn __is_trivial_copy<T>() -> bool", __LINE__);
    make_function(is_trivial_assign, "pub const fn __is_trivial_assign<T>() -> bool", __LINE__);
    make_function(is_trivial_destroy, "pub const fn __is_trivial_destroy<T>() -> bool", __LINE__);
    make_function(is_const_eval, "pub fn __is_const_eval() -> bool", __LINE__);
    make_function(tuple_len, "pub const fn __tuple_len<T>() -> usize", __LINE__);
    make_function(array_len, "pub const fn __array_len<T>() -> usize", __LINE__);

    make_function(is_nan, "pub const fn __is_nan<T>(T) -> bool", __LINE__);
    make_function(is_finite, "pub const fn __is_finite<T>(T) -> bool", __LINE__);
    make_function(is_normal, "pub const fn __is_normal<T>(T) -> bool", __LINE__);
    make_function(nan, "pub const fn __nan() -> #float", __LINE__);
    make_function(inf, "pub const fn __inf() -> #float", __LINE__);

    make_function(is_integral, "pub const fn __is_integral<T>() -> bool", __LINE__);
    make_function(is_unsigned, "pub const fn __is_unsigned<T>() -> bool", __LINE__);
    make_function(is_floating_point, "pub const fn __is_floating_point<T>() -> bool", __LINE__);
    make_function(is_arithmetic, "pub const fn __is_arithmetic<T>() -> bool", __LINE__);

    make_function(clz, "pub const fn __clz<T>(T) -> int", __LINE__);
    make_function(ctz, "pub const fn __ctz<T>(T) -> int", __LINE__);
    make_function(popcnt, "pub const fn __popcnt<T>(T) -> int", __LINE__);
    make_function(signbit, "pub const fn __signbit<T>(T) -> int", __LINE__);
    make_function(byteswap, "pub const fn __byteswap<T>(T) -> T", __LINE__);
    make_function(bitreverse, "pub const fn __bitreverse<T>(T) -> T", __LINE__);

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

    make_function(alloca, "pub fn __alloca(usize, ##int = 0) -> void mut *", __LINE__);

    make_function(symbol, "pub fn extern(##string) -> uintptr", __LINE__);

    make_function(atomic_load, "pub fn __atomic_load<T>(T*, ##int) -> T", __LINE__);
    make_function(atomic_store, "pub fn __atomic_store<T>(T mut *, T, ##int) -> void", __LINE__);
    make_function(atomic_xchg, "pub fn __atomic_xchg<T>(T mut *, T, ##int) -> T", __LINE__);
    make_function(atomic_cmpxchg, "pub fn __atomic_cmpxchg<T>(T mut *, T, T, ##int, ##int, ##int) -> bool", __LINE__);

    make_function(atomic_fetch_add, "pub fn __atomic_fetch_add<T>(T*, T, ##int) -> T", __LINE__);
    make_function(atomic_fetch_sub, "pub fn __atomic_fetch_sub<T>(T*, T, ##int) -> T", __LINE__);
    make_function(atomic_fetch_and, "pub fn __atomic_fetch_and<T>(T*, T, ##int) -> T", __LINE__);
    make_function(atomic_fetch_xor, "pub fn __atomic_fetch_xor<T>(T*, T, ##int) -> T", __LINE__);
    make_function(atomic_fetch_or, "pub fn __atomic_fetch_or<T>(T*, T, ##int) -> T", __LINE__);
    make_function(atomic_fetch_nand, "pub fn __atomic_fetch_nand<T>(T*, T, ##int) -> T", __LINE__);

    make_function(atomic_thread_fence, "pub fn __atomic_thread_fence(##int) -> void", __LINE__);

    make_function(rdtsc, "pub fn __rdtsc() -> u64", __LINE__);
    make_function(rdtscp, "pub fn __rdtscp() -> (u64, u32)", __LINE__);
    make_function(relax, "pub fn __relax() -> void", __LINE__);
    make_function(inline_asm, "pub fn __asm<V>(##string, ##string, V...) -> uintptr", __LINE__);

    make_function(decl_kind, "pub const fn __decl_kind(#declid) -> #int", __LINE__);
    make_function(decl_name, "pub const fn __decl_name(#declid) -> #string", __LINE__);
    make_function(decl_flags, "pub const fn __decl_flags(#declid) -> #int", __LINE__);
    make_function(decl_parent, "pub const fn __decl_parent(#declid) -> #declid", __LINE__);
    make_function(decl_children, "pub const fn __decl_children(#declid, #int = 0) -> #declid[]", __LINE__);
    make_function(type_decl, "pub const fn #declid(#typeid) -> #declid", __LINE__);
    make_function(type_name, "pub const fn __type_name(#typeid) -> #string", __LINE__);
    make_function(type_children, "pub const fn __type_children(#typeid, #int = 0) -> #declid[]", __LINE__);
    make_function(type_query, "pub const fn __type_query(#int, var ...) -> #typeid", __LINE__);

    make_function(__argc__, "pub fn __argc__() -> int", __LINE__);
    make_function(__argv__, "pub fn __argv__() -> u8**", __LINE__);
    make_function(__envp__, "pub fn __envp__() -> u8**", __LINE__);

    make_function(__site__, "pub const fn __site__() -> (#string, int, int, #string)", __LINE__);
    make_function(__decl__, "pub const fn __decl__() -> #declid", __LINE__);
    make_function(__function__, "pub const fn __function__() -> #declid", __LINE__);
    make_function(__module__, "pub const fn __module__() -> #declid", __LINE__);

    make_function(__cfg, "pub const fn __cfg(##string) -> bool", __LINE__);
    make_function(__cfg__, "pub const fn __cfg__() -> #string", __LINE__);
    make_function(__srcdir__, "pub const fn __srcdir__() -> #string", __LINE__);
    make_function(__bindir__, "pub const fn __bindir__() -> #string", __LINE__);
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

      case Builtin::Type_DeclidLiteral:
        return &BuiltinModule::declidliteraltype;

      case Builtin::Type_TypeidLiteral:
        return &BuiltinModule::typeidliteraltype;

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
    assert(module->kind() == Decl::Module && decl_cast<ModuleDecl>(module)->name == "#builtin"sv);

    for (auto &decl : decl_cast<ModuleDecl>(module)->decls)
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
  auto where(Decl *decl, vector<pair<Decl*, Type*>> const &typeargs) -> bool
  {
    auto is_builtin = [](Type *type) { return type->klass() == Type::Builtin; };
    auto is_int_literal = [](Type *type) { return type == &BuiltinModule::intliteraltype; };
    auto is_float_literal = [](Type *type) { return type == &BuiltinModule::floatliteraltype; };
    auto is_declid_literal = [](Type *type) { return type == &BuiltinModule::declidliteraltype; };
    auto is_typeid_literal = [](Type *type) { return type == &BuiltinModule::typeidliteraltype; };
    auto is_ptr_literal = [](Type *type) { return type == &BuiltinModule::ptrliteraltype; };

    auto is_int = [&](Type *type) { return is_int_type(type) || is_int_literal(type); };
    auto is_float = [&](Type *type) { return is_float_type(type) || is_float_literal(type); };
    auto is_numeric = [&](Type *type) { return is_int(type) || is_float(type); };
    auto is_enum = [&](Type *type) { return is_enum_type(type); };
    auto is_bool = [&](Type *type) { return is_bool_type(type); };
    auto is_char = [&](Type *type) { return is_char_type(type); };
    auto is_pointer = [&](Type *type) { return is_pointer_type(type); };
    auto is_reference = [&](Type *type) { return is_reference_type(type); };

    auto base_type = [&](Type *type) {
      while (is_tag_type(type) && decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->basetype && (type_cast<TagType>(type)->decl->flags & TagDecl::PublicBase))
        type = type_cast<TagType>(type)->fields[0];

      return type;
    };

    auto find_type = [&](Decl *decl) { return std::find_if(typeargs.begin(), typeargs.end(), [&](auto &k) { return k.first == decl; }); };

    auto tuple_ex_match = [&](TupleType *lhs, TupleType *rhs) {

      if (lhs->fields.size() != rhs->fields.size())
        return false;

      for (size_t index = 0; index < lhs->fields.size(); ++index)
      {
        auto lhsfield = remove_const_type(lhs->fields[index]);
        auto rhsfield = remove_const_type(rhs->fields[index]);

        if (is_reference_type(lhs->defns[index]))
          lhsfield = remove_const_type(remove_reference_type(lhsfield));

        if (is_reference_type(rhs->defns[index]))
          rhsfield = remove_const_type(remove_reference_type(rhsfield));

        while (is_pointference_type(lhsfield) && is_pointference_type(rhsfield))
        {
          lhsfield = remove_const_type(remove_pointference_type(lhsfield));
          rhsfield = remove_const_type(remove_pointference_type(rhsfield));
        }

        if (rhsfield == type(Builtin::Type_IntLiteral) && (is_int_type(lhsfield) || is_char_type(lhsfield)))
          continue;

        if (rhsfield == type(Builtin::Type_FloatLiteral) && is_float_type(lhsfield))
          continue;

        if (rhsfield == type(Builtin::Type_PtrLiteral) && is_pointer_type(lhsfield))
          continue;

        if (lhsfield != rhsfield)
          return false;
      }

      return true;
    };

    auto fn = decl_cast<FunctionDecl>(decl);

    switch (fn->builtin)
    {
      case Builtin::Type_Ptr:
      case Builtin::Type_PtrLiteral:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_pointer_type(remove_const_type(T->second)) || is_ptr_literal(T->second);
        break;

      case Builtin::Type_Ref:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_reference_type(remove_const_type(T->second));
        break;

      case Builtin::Array_Constructor:
      case Builtin::Array_Copytructor:
      case Builtin::Array_Assignment:
      case Builtin::Array_Destructor:
      case Builtin::ArrayEq:
      case Builtin::ArrayCmp:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_array_type(T->second);
        break;

      case Builtin::ArrayLen:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_array_type(T->second) || is_array_type(base_type(T->second));
        break;

      case Builtin::SliceLen:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_slice_type(T->second);
        break;

      case Builtin::Tuple_Constructor:
      case Builtin::Tuple_Copytructor:
      case Builtin::Tuple_Assignment:
      case Builtin::Tuple_Destructor:
      case Builtin::TupleEq:
      case Builtin::TupleCmp:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_tuple_type(T->second);
        break;

      case Builtin::Tuple_CopytructorEx:
      case Builtin::Tuple_AssignmentEx:
      case Builtin::TupleEqEx:
      case Builtin::TupleCmpEx:
        if (auto T = find_type(fn->args[0]), U = find_type(fn->args[1]); T != typeargs.end() && U != typeargs.end())
          return is_tuple_type(T->second) && is_tuple_type(U->second) && T->second != U->second && tuple_ex_match(type_cast<TupleType>(T->second), type_cast<TupleType>(U->second));
        break;

      case Builtin::TupleLen:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_tuple_type(T->second) || is_tuple_type(base_type(T->second));
        break;

      case Builtin::Bool:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_bool(T->second) || is_pointer(T->second) || is_reference(T->second) || is_ptr_literal(T->second) || is_int_literal(T->second) || is_declid_literal(T->second) || is_typeid_literal(T->second);
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
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_numeric(T->second) || is_char(T->second);
        break;

      case Builtin::LT:
      case Builtin::GT:
      case Builtin::LE:
      case Builtin::GE:
      case Builtin::EQ:
      case Builtin::NE:
      case Builtin::Cmp:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_builtin(T->second) || is_enum(T->second) || is_pointer(T->second) || is_reference(T->second);
        break;

      case Builtin::OffsetAdd:
      case Builtin::OffsetSub:
      case Builtin::OffsetAddAssign:
      case Builtin::OffsetSubAssign:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_pointer(T->second);
        break;

      case Builtin::Not:
      case Builtin::And:
      case Builtin::Or:
      case Builtin::Xor:
      case Builtin::AndAssign:
      case Builtin::OrAssign:
      case Builtin::XorAssign:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_int(T->second) || is_char(T->second) || is_bool(T->second);
        break;

      case Builtin::Shl:
      case Builtin::Shr:
      case Builtin::ShlAssign:
      case Builtin::ShrAssign:
        if (auto T = find_type(fn->args[0]), U = find_type(fn->args[1]); T != typeargs.end() && U != typeargs.end())
          return (is_int(T->second) || is_char(T->second)) && (is_int(U->second) || is_char(U->second));
        break;

      case Builtin::clz:
      case Builtin::ctz:
      case Builtin::popcnt:
      case Builtin::byteswap:
      case Builtin::bitreverse:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_int(T->second) || is_char(T->second) || is_bool(T->second);
        break;

      case Builtin::signbit:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_int(T->second) || is_float(T->second);
        break;

      case Builtin::PreInc:
      case Builtin::PreDec:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_numeric(T->second) || is_pointer(T->second) || is_char(T->second);
        break;

      case Builtin::Assign:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_builtin(T->second) || is_enum(T->second) || is_pointer(T->second) || is_reference(T->second);
        break;

      case Builtin::is_const:
      case Builtin::is_rvalue:
      case Builtin::is_array:
      case Builtin::is_tuple:
      case Builtin::is_union:
      case Builtin::is_struct:
      case Builtin::is_vtable:
      case Builtin::is_lambda:
      case Builtin::is_slice:
      case Builtin::is_builtin:
      case Builtin::is_pointer:
      case Builtin::is_reference:
      case Builtin::is_trivial_copy:
      case Builtin::is_trivial_assign:
      case Builtin::is_trivial_destroy:
      case Builtin::is_integral:
      case Builtin::is_unsigned:
      case Builtin::is_floating_point:
      case Builtin::is_arithmetic:
        return typeargs.size() == 1;

      case Builtin::is_same:
      case Builtin::is_match:
        return typeargs.size() == 2;

      case Builtin::array_len:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_array_type(remove_const_type(T->second));
        break;

      case Builtin::tuple_len:
        if (auto T = find_type(fn->args[0]); T != typeargs.end())
          return is_compound_type(remove_const_type(T->second));
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
