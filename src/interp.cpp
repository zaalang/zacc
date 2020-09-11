//
// interp.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "interp.h"
#include "diag.h"
#include "numeric.h"
#include <iostream>
#include <algorithm>
#include <cstring>
#include <climits>
#include <cstdio>
#include <cmath>

using namespace std;

namespace
{
  struct EvalContext
  {
    Scope dx;
    Diag &diag;

    TypeTable &typetable;

    vector<vector<uint8_t>> memory;

    bool exception;

    Type *voidtype;
    Type *booltype;
    Type *chartype;
    Type *intliteraltype;
    Type *floatliteraltype;
    Type *stringliteraltype;
    Type *ptrliteraltype;

    template<typename T, typename ...Args>
    T *make_expr(Args&&... args)
    {
      return new T(std::forward<Args>(args)...);
    }

    EvalContext(Scope const &dx, TypeTable &typetable, Diag &diag)
      : dx(dx),
        diag(diag),
        typetable(typetable)
    {
      exception = false;

      voidtype = type(Builtin::Type_Void);
      booltype = type(Builtin::Type_Bool);
      chartype = type(Builtin::Type_Char);
      intliteraltype = type(Builtin::Type_IntLiteral);
      floatliteraltype = type(Builtin::Type_FloatLiteral);
      stringliteraltype = type(Builtin::Type_StringLiteral);
      ptrliteraltype = type(Builtin::Type_PtrLiteral);
    }
  };

  struct FunctionContext
  {
    Scope scope;

    struct Local
    {
      Type *type = nullptr;

      size_t size = 0;
      void *alloc = nullptr;
    };

    vector<Local> locals;

    size_t errorarg = 0;
  };

  struct Range
  {
    uint64_t beg;
    uint64_t end;
  };

  template <typename T>
  struct Slice
  {
    uint64_t len;
    T *data;
  };

  bool is_int(Type const *type)
  {
    return is_int_type(type) || is_bool_type(type) || is_char_type(type) || is_enum_type(type);
  }

  bool is_float(Type const *type)
  {
    return is_float_type(type);
  }

  bool eval_function(EvalContext &ctx, Scope const &scope, MIR const &mir, FunctionContext::Local &returnvalue, vector<FunctionContext::Local> const &args = {});

  //|///////////////////// type_resolved ////////////////////////////////////
  bool type_resolved(Type const *type)
  {
    switch(type->klass())
    {
      case Type::Builtin:
        return true;

      case Type::Const:
        return type_resolved(type_cast<ConstType>(type)->type);

      case Type::Pointer:
        return type_resolved(type_cast<PointerType>(type)->type);

      case Type::Reference:
        return type_resolved(type_cast<ReferenceType>(type)->type);

      case Type::Array:

        if (type_cast<ArrayType>(type)->size->klass() != Type::TypeLit || type_cast<TypeLitType>(type_cast<ArrayType>(type)->size)->value->kind() != Expr::IntLiteral)
          return false;

        return type_resolved(type_cast<ArrayType>(type)->type);

      case Type::Tuple:

        for(auto &field : type_cast<TupleType>(type)->fields)
          if (!type_resolved(field))
            return false;

        return true;

      case Type::Tag:

        for(auto &field : type_cast<TagType>(type)->fields)
          if (!type_resolved(field))
            return false;

        return true;

      case Type::TypeArg:
      case Type::QualArg:
      case Type::TypeRef:
        return false;

      default:
        assert(false);
    }

    return false;
  }

  //|///////////////////// alloc ////////////////////////////////////////////
  FunctionContext::Local alloc(EvalContext &ctx, MIR::Local const &local)
  {
    FunctionContext::Local result;

    auto type = local.type;

    if (local.flags & MIR::Local::Reference)
      type = ctx.typetable.find_or_create<PointerType>(type);

    result.type = type;
    result.size = sizeof_type(type);

    ctx.memory.push_back(vector<uint8_t>(result.size));

    result.alloc = ctx.memory.back().data();

    return result;
  }

  //|///////////////////// load /////////////////////////////////////////////
  void *load_ptr(EvalContext &ctx, void *alloc, Type *type)
  {
    void *value;

    assert(is_pointference_type(type));

    memcpy(&value, alloc, sizeof(value));

    return value;
  }

  template<typename T = void>
  T* load_ptr(EvalContext &ctx, FunctionContext &fx, size_t src)
  {
    return static_cast<T*>(load_ptr(ctx, fx.locals[src].alloc, fx.locals[src].type));
  }

  //|///////////////////// load /////////////////////////////////////////////
  Numeric::Int load_int(EvalContext &ctx, void *alloc, Type *type)
  {
    Numeric::Int value;

    union {
      int8_t value_i8;
      int16_t value_i16;
      int32_t value_i32;
      int64_t value_i64;
      uint8_t value_u8;
      uint16_t value_u16;
      uint32_t value_u32;
      uint64_t value_u64;
    };

    if (is_enum_type(type))
      type = type_cast<TagType>(type)->fields[0];

    switch (type_cast<BuiltinType>(type)->kind())
    {
      case BuiltinType::I8:
        memcpy(&value_i8, alloc, sizeof(value_i8));
        value = Numeric::int_literal(value_i8);
        break;

      case BuiltinType::I16:
        memcpy(&value_i16, alloc, sizeof(value_i16));
        value = Numeric::int_literal(value_i16);
        break;

      case BuiltinType::I32:
        memcpy(&value_i32, alloc, sizeof(value_i32));
        value = Numeric::int_literal(value_i32);
        break;

      case BuiltinType::I64:
      case BuiltinType::ISize:
        memcpy(&value_i64, alloc, sizeof(value_i64));
        value = Numeric::int_literal(value_i64);
        break;

      case BuiltinType::U8:
      case BuiltinType::Bool:
        memcpy(&value_u8, alloc, sizeof(value_u8));
        value = Numeric::int_literal(1, value_u8);
        break;

      case BuiltinType::U16:
        memcpy(&value_u16, alloc, sizeof(value_u16));
        value = Numeric::int_literal(1, value_u16);
        break;

      case BuiltinType::U32:
      case BuiltinType::Char:
        memcpy(&value_u32, alloc, sizeof(value_u32));
        value = Numeric::int_literal(1, value_u32);
        break;

      case BuiltinType::U64:
      case BuiltinType::USize:
        memcpy(&value_u64, alloc, sizeof(value_u64));
        value = Numeric::int_literal(1, value_u64);
        break;

      case BuiltinType::IntLiteral:
        memcpy(&value, alloc, sizeof(value));
        break;

      default:
        assert(false);
    }

    return value;
  }

  Numeric::Int load_int(EvalContext &ctx, FunctionContext &fx, size_t src)
  {
    return load_int(ctx, fx.locals[src].alloc, fx.locals[src].type);
  }

  //|///////////////////// load /////////////////////////////////////////////
  Numeric::Float load_float(EvalContext &ctx, void *alloc, Type *type)
  {
    Numeric::Float value;

    union {
      float value_f32;
      double value_f64;
    };

    switch (type_cast<BuiltinType>(type)->kind())
    {
      case BuiltinType::F32:
        memcpy(&value_f32, alloc, sizeof(value_f32));
        value = Numeric::float_literal(value_f32);
        break;

      case BuiltinType::F64:
        memcpy(&value_f64, alloc, sizeof(value_f64));
        value = Numeric::float_literal(value_f64);
        break;

      case BuiltinType::FloatLiteral:
        memcpy(&value, alloc, sizeof(value));
        break;

      default:
        assert(false);
    }

    return value;
  }

  Numeric::Float load_float(EvalContext &ctx, FunctionContext &fx, size_t src)
  {
    return load_float(ctx, fx.locals[src].alloc, fx.locals[src].type);
  }

  //|///////////////////// load /////////////////////////////////////////////
  bool load_bool(EvalContext &ctx, void *alloc, Type *type)
  {
    bool value;

    assert(is_bool_type(type));

    memcpy(&value, alloc, sizeof(value));

    return value;
  }

  bool load_bool(EvalContext &ctx, FunctionContext &fx, size_t src)
  {
    return load_bool(ctx, fx.locals[src].alloc, fx.locals[src].type);
  }

  //|///////////////////// load /////////////////////////////////////////////
  string_view load_string(EvalContext &ctx, void *alloc, Type *type)
  {
    Slice<const char> value;

    assert(is_string_type(type));

    memcpy(&value, alloc, sizeof(value));

    return string_view(value.data, value.len);
  }

  string_view load_string(EvalContext &ctx, FunctionContext &fx, size_t src)
  {
    return load_string(ctx, fx.locals[src].alloc, fx.locals[src].type);
  }

  //|///////////////////// load /////////////////////////////////////////////
  Range load_range(EvalContext &ctx, void *alloc, Type *type)
  {
    Range value;

    assert(is_tuple_type(type));

    memcpy(&value, alloc, sizeof(value));

    return value;
  }

  Range load_range(EvalContext &ctx, FunctionContext &fx, size_t src)
  {
    return load_range(ctx, fx.locals[src].alloc, fx.locals[src].type);
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, void *value)
  {
    assert(is_pointference_type(type));

    memcpy(alloc, &value, sizeof(void*));
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, Numeric::Int const &value)
  {
    union {
      int8_t value_i8;
      int16_t value_i16;
      int32_t value_i32;
      int64_t value_i64;
      uint8_t value_u8;
      uint16_t value_u16;
      uint32_t value_u32;
      uint64_t value_u64;
    };

    if (is_enum_type(type))
      type = type_cast<TagType>(type)->fields[0];

    switch (type_cast<BuiltinType>(type)->kind())
    {
      case BuiltinType::I8:
        value_i8 = value.sign * static_cast<int8_t>(value.value);
        memcpy(alloc, &value_i8, sizeof(value_i8));
        break;

      case BuiltinType::I16:
        value_i16 = value.sign * static_cast<int16_t>(value.value);;
        memcpy(alloc, &value_i16, sizeof(value_i16));
        break;

      case BuiltinType::I32:
        value_i32 = value.sign * static_cast<int32_t>(value.value);
        memcpy(alloc, &value_i32, sizeof(value_i32));
        break;

      case BuiltinType::I64:
      case BuiltinType::ISize:
        value_i64 = value.sign * static_cast<int64_t>(value.value);;
        memcpy(alloc, &value_i64, sizeof(value_i64));
        break;

      case BuiltinType::U8:
      case BuiltinType::Bool:
        value_u8 = static_cast<uint8_t>(value.sign * value.value);
        memcpy(alloc, &value_u8, sizeof(value_u8));
        break;

      case BuiltinType::U16:
        value_u16 = static_cast<uint16_t>(value.sign * value.value);
        memcpy(alloc, &value_u16, sizeof(value_u16));
        break;

      case BuiltinType::U32:
      case BuiltinType::Char:
        value_u32 = static_cast<uint32_t>(value.sign * value.value);
        memcpy(alloc, &value_u32, sizeof(value_u32));
        break;

      case BuiltinType::U64:
      case BuiltinType::USize:
        value_u64 = static_cast<uint64_t>(value.sign * value.value);
        memcpy(alloc, &value_u64, sizeof(value_u64));
        break;

      case BuiltinType::IntLiteral:
        memcpy(alloc, &value, sizeof(value));
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, Numeric::Float const &value)
  {
    union {
      float value_f32;
      double value_f64;
    };

    switch (type_cast<BuiltinType>(type)->kind())
    {
      case BuiltinType::F32:
        value_f32 = static_cast<float>(value.value);
        memcpy(alloc, &value_f32, sizeof(value_f32));
        break;

      case BuiltinType::F64:
        value_f64 = static_cast<double>(value.value);
        memcpy(alloc, &value_f64, sizeof(value_f64));
        break;

      case BuiltinType::FloatLiteral:
        memcpy(alloc, &value, sizeof(value));
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, bool value)
  {
    assert(is_bool_type(type));

    memcpy(alloc, &value, sizeof(value));
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, Slice<const char> const &value)
  {
    assert(is_string_type(type));

    memcpy(alloc, &value, sizeof(value));
  }

  void store(EvalContext &ctx, void *alloc, Type *type, Expr *value);

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, StringLiteralExpr const *value)
  {
    store(ctx, alloc, type, Slice<const char>{ value->value().size(), value->value().data() });
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, ArrayLiteralExpr const *value)
  {
    assert(is_array_type(type));

    auto address = alloc;
    auto elemtype = type_cast<ArrayType>(type)->type;
    auto elemsize = sizeof_type(elemtype);
    auto arraylen = array_len(type_cast<ArrayType>(type));

    for(auto &element : value->elements)
    {      
      store(ctx, address, elemtype, element);

      address = (void*)((size_t)address + elemsize);
    }

    for(size_t i = value->elements.size(); i < arraylen; ++i)
    {
      memcpy(address, alloc, elemsize);

      address = (void*)((size_t)address + elemsize);
    }
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, CompoundLiteralExpr const *value)
  {
    assert(is_compound_type(type));

    auto address = alloc;
    auto &fields = type_cast<CompoundType>(type)->fields;

    assert(fields.size() == value->fields.size());

    for(size_t i = 0; i < fields.size(); ++i)
    {
      store(ctx, address, fields[i], value->fields[i]);

      address = (void*)((size_t)address + sizeof_type(fields[i]));
    }
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, Expr *value)
  {
    switch(value->kind())
    {
      case Expr::VoidLiteral:
        break;

      case Expr::BoolLiteral:
        store(ctx, alloc, type, expr_cast<BoolLiteralExpr>(value)->value());
        break;

      case Expr::CharLiteral:
        store(ctx, alloc, type, expr_cast<CharLiteralExpr>(value)->value());
        break;

      case Expr::IntLiteral:
        store(ctx, alloc, type, expr_cast<IntLiteralExpr>(value)->value());
        break;

      case Expr::FloatLiteral:
        store(ctx, alloc, type, expr_cast<FloatLiteralExpr>(value)->value());
        break;

      case Expr::PtrLiteral:
        store(ctx, alloc, type, (void*)nullptr);
        break;

      case Expr::StringLiteral:
        store(ctx, alloc, type, expr_cast<StringLiteralExpr>(value));
        break;

      case Expr::ArrayLiteral:
        store(ctx, alloc, type, expr_cast<ArrayLiteralExpr>(value));
        break;

      case Expr::CompoundLiteral:
        store(ctx, alloc, type, expr_cast<CompoundLiteralExpr>(value));
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, VoidLiteralExpr const *literal)
  {
    auto type = fx.locals[dst].type;

    if (!is_void_type(type))
    {
      ctx.diag.error("literal type incompatible with required type", fx.scope, literal->loc());
      ctx.diag << "  literal type: 'void' required type: '" << *type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, BoolLiteralExpr const *literal)
  {
    auto type = fx.locals[dst].type;

    if (!is_bool_type(type))
    {
      ctx.diag.error("literal type incompatible with required type", fx.scope, literal->loc());
      ctx.diag << "  literal type: 'bool' required type: '" << *type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal->value());

    return true;
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, CharLiteralExpr const *literal)
  {
    auto type = fx.locals[dst].type;

    if (!literal_valid(type_cast<BuiltinType>(type)->kind(), literal->value()))
    {
      ctx.diag.error("literal value out of range for required type", fx.scope, literal->loc());
      ctx.diag << "  literal value: '" << literal->value() << "' required type: '" << *type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal->value());

    return true;
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, IntLiteralExpr const *literal)
  {
    auto type = fx.locals[dst].type;

    if (is_enum_type(type))
      type = type_cast<TagType>(type)->fields[0];

    if (!literal_valid(type_cast<BuiltinType>(type)->kind(), literal->value()))
    {
      ctx.diag.error("literal value out of range for required type", fx.scope, literal->loc());
      ctx.diag << "  literal value: '" << literal->value() << "' required type: '" << *type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal->value());

    return true;
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, FloatLiteralExpr const *literal)
  {
    auto type = fx.locals[dst].type;

    if (!literal_valid(type_cast<BuiltinType>(type)->kind(), literal->value()))
    {
      ctx.diag.error("literal value out of range for required type", fx.scope, literal->loc());
      ctx.diag << "  literal value: '" << literal->value() << "' required type: '" << *type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal->value());

    return true;
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, PointerLiteralExpr const *literal)
  {
    auto type = fx.locals[dst].type;

    if (type == ctx.ptrliteraltype)
      return true;

    if (!is_pointference_type(type))
    {
      ctx.diag.error("literal type incompatible with required type", fx.scope, literal->loc());
      ctx.diag << "  literal type: 'null' required type: '" << *type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, (void*)nullptr);

    return true;
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, StringLiteralExpr const *literal)
  {
    auto type = fx.locals[dst].type;

    if (!is_string_type(type))
    {
      ctx.diag.error("literal type incompatible with required type", fx.scope, literal->loc());
      ctx.diag << "  literal type: '#string' required type: '" << *type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal);

    return true;
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, ArrayLiteralExpr const *literal)
  {
    auto type = fx.locals[dst].type;

    if (!is_array_type(type))
    {
      ctx.diag.error("literal type incompatible with required type", fx.scope, literal->loc());
      ctx.diag << "  literal type: '#array' required type: '" << *type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal);

    return true;
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, CompoundLiteralExpr const *literal)
  {
    auto type = fx.locals[dst].type;

    if (!is_compound_type(type))
    {
      ctx.diag.error("literal type incompatible with required type", fx.scope, literal->loc());
      ctx.diag << "  literal type: '#struct' required type: '" << *type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal);

    return true;
  }

  //|///////////////////// eval_constant ////////////////////////////////////
  bool eval_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::ConstantData const &constant)
  {
    return std::visit([&](auto &v) { return eval_constant(ctx, fx, dst, v); }, constant);
  }

  //|///////////////////// eval_fields //////////////////////////////////////
  void *eval_fields(EvalContext &ctx, FunctionContext &fx, MIR::local_t arg, vector<MIR::RValue::Field> const &fields)
  {
    auto address = fx.locals[arg].alloc;
    auto vartype = fx.locals[arg].type;

    for(auto &field : fields)
    {
      if (field.op == MIR::RValue::Val)
      {
        address = load_ptr(ctx, address, vartype);
        vartype = remove_pointference_type(vartype);
      }

      address = (void*)((size_t)address + offsetof_type(vartype, field.index));

      switch(vartype = remove_const_type(vartype); vartype->klass())
      {
        case Type::Tag:
          vartype = type_cast<TagType>(vartype)->fields[field.index];
          break;

        case Type::Tuple:
          vartype = type_cast<TupleType>(vartype)->fields[field.index];
          break;

        case Type::Array:
          vartype = type_cast<ArrayType>(vartype)->type;
          break;

        default:
          assert(false);
      }
    }

    return address;
  }

  //|///////////////////// eval_cpy_value ///////////////////////////////////
  bool eval_cpy_value(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    if (fields.size() != 0)
    {
      auto src = eval_fields(ctx, fx, arg, fields);

      memcpy(fx.locals[dst].alloc, src, fx.locals[dst].size);
    }
    else
    {
      assert(fx.locals[dst].size == fx.locals[arg].size);

      memcpy(fx.locals[dst].alloc, fx.locals[arg].alloc, fx.locals[dst].size);
    }

    return true;
  }

  //|///////////////////// eval_ref_value ///////////////////////////////////
  bool eval_ref_value(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    if (fields.size() != 0)
    {
      auto src = eval_fields(ctx, fx, arg, fields);

      memcpy(fx.locals[dst].alloc, &src, fx.locals[dst].size);
    }
    else
    {
      memcpy(fx.locals[dst].alloc, &fx.locals[arg].alloc, fx.locals[dst].size);
    }

    return true;
  }

  //|///////////////////// eval_fer_value ///////////////////////////////////
  bool eval_fer_value(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    if (fields.size() != 0)
    {
      void *src;
      memcpy(&src, eval_fields(ctx, fx, arg, fields), sizeof(src));

      memcpy(fx.locals[dst].alloc, src, fx.locals[dst].size);
    }
    else
    {
      memcpy(fx.locals[dst].alloc, load_ptr(ctx, fx, arg), fx.locals[dst].size);
    }

    return true;
  }

  //|///////////////////// eval_variable ////////////////////////////////////
  bool eval_variable(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    switch(op)
    {
      case MIR::RValue::Val:
        return eval_cpy_value(ctx, fx, dst, variable);

      case MIR::RValue::Ref:
        return eval_ref_value(ctx, fx, dst, variable);

      case MIR::RValue::Fer:
        return eval_fer_value(ctx, fx, dst, variable);

      default:
        assert(false);
        return false;
    }
  }

  //|///////////////////// unary_arithmetic /////////////////////////////////
  bool eval_builtin_unary_arithmetic(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_int(fx.locals[args[0]].type))
    {     
      bool ok = false;
      Numeric::Int result;

      auto lhs = load_int(ctx, fx, args[0]);

      switch(callee.fn->builtin)
      {
        case Builtin::Plus:
          result = lhs;
          break;

        case Builtin::Minus:
          result = -lhs;
          if (!is_signed_type(fx.locals[args[0]].type))
            ok = true;
          break;

        case Builtin::Not:
          result = ~lhs;
          ok = true;
          break;

        case Builtin::abs:
          result = abs(lhs);
          break;

        case Builtin::floor:
        case Builtin::ceil:
        case Builtin::round:
        case Builtin::trunc:
          result = lhs;
          break;

        default:
          assert(false);
      }

      if (!ok && !literal_valid(type_cast<BuiltinType>(fx.locals[dst].type)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *fx.locals[dst].type << "'\n";
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else if (is_float(fx.locals[args[0]].type))
    {
      Numeric::Float result;

      auto lhs = load_float(ctx, fx, args[0]);

      switch(callee.fn->builtin)
      {
        case Builtin::Plus:
          result = lhs;
          break;

        case Builtin::Minus:
          result = -lhs;
          break;

        case Builtin::abs:
          result = abs(lhs);
          break;

        case Builtin::floor:
          result = floor(lhs);
          break;

        case Builtin::ceil:
          result = ceil(lhs);
          break;

        case Builtin::round:
          result = round(lhs);
          break;

        case Builtin::trunc:
          result = trunc(lhs);
          break;

        case Builtin::sqrt:
          result = sqrt(lhs);
          break;

        default:
          assert(false);
      }

      if (!literal_valid(type_cast<BuiltinType>(fx.locals[dst].type)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *fx.locals[dst].type << "'\n";
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else
    {
      ctx.diag.error("invalid unary arithmetic arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// unary_arithmetic_assign //////////////////////////
  bool eval_builtin_unary_arithmetic_assign(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto arg = load_ptr(ctx, fx, args[0]);
    auto argtype = remove_pointference_type(fx.locals[args[0]].type);

    if (is_int(argtype))
    {
      Numeric::Int result;

      auto lhs = load_int(ctx, arg, argtype);

      switch(callee.fn->builtin)
      {
        case Builtin::PreInc:
          result = lhs + Numeric::int_literal(1, 1);
          break;

        case Builtin::PreDec:
          result = lhs - Numeric::int_literal(1, 1);
          break;

        default:
          assert(false);
      }

      if (!literal_valid(type_cast<BuiltinType>(argtype)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *argtype << "'\n";
        return false;
      }

      store(ctx, arg, argtype, result);
    }
    else if (is_float(argtype))
    {
      Numeric::Float result;

      auto lhs = load_float(ctx, arg, argtype);

      switch(callee.fn->builtin)
      {
        case Builtin::PreInc:
          result = lhs + Numeric::float_literal(1.0);
          break;

        case Builtin::PreDec:
          result = lhs - Numeric::float_literal(1.0);
          break;

        default:
          assert(false);
      }

      if (!literal_valid(type_cast<BuiltinType>(argtype)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *argtype << "'\n";
        return false;
      }

      store(ctx, arg, argtype, result);
    }
    else if (is_pointference_type(argtype))
    {
      void *result;

      auto lhs = load_ptr(ctx, arg, argtype);

      switch(callee.fn->builtin)
      {
        case Builtin::PreInc:
          result = (void*)((size_t)lhs + sizeof_type(remove_pointference_type(argtype)));
          break;

        case Builtin::PreDec:
          result = (void*)((size_t)lhs - sizeof_type(remove_pointference_type(argtype)));
          break;

        default:
          assert(false);
      }

      store(ctx, arg, argtype, result);
    }
    else
    {
      ctx.diag.error("invalid unary arithmetic assign arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, arg);

    return true;
  }

  //|///////////////////// binary_arithmetic ////////////////////////////////
  bool eval_builtin_binary_arithmetic(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_int(fx.locals[args[0]].type) && is_int(fx.locals[args[1]].type))
    {
      bool ok = false;
      Numeric::Int result;

      auto lhs = load_int(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      switch(callee.fn->builtin)
      {
        case Builtin::Add:
          result = lhs + rhs;
          break;

        case Builtin::Sub:
          result = lhs - rhs;
          break;

        case Builtin::Div:

          if (rhs.value == 0)
          {
            ctx.diag.error("division by zero", fx.scope, loc);
            return false;
          }

          result = lhs / rhs;
          break;

        case Builtin::Mul:
          result = lhs * rhs;
          break;

        case Builtin::Rem:

          if (rhs.value == 0)
          {
            ctx.diag.error("division by zero", fx.scope, loc);
            return false;
          }

          result = lhs % rhs;
          break;

        case Builtin::Shl:

          if (rhs.sign < 0)
          {
            ctx.diag.error("negative shift", fx.scope, loc);
            return false;
          }

          result = lhs << rhs;
          ok = true;
          break;

        case Builtin::Shr:

          if (rhs.sign < 0)
          {
            ctx.diag.error("negative shift", fx.scope, loc);
            return false;
          }

          result = lhs >> rhs;
          break;

        case Builtin::And:
          result = lhs & rhs;
          break;

        case Builtin::Or:
          result = lhs | rhs;
          break;

        case Builtin::Xor:
          result = lhs ^ rhs;
          break;

        case Builtin::copysign:
          result = lhs.sign == rhs.sign ? lhs : -lhs;
          break;

        case Builtin::min:
          result = rhs < lhs ? rhs : lhs;
          break;

        case Builtin::max:
          result = lhs < rhs ? rhs : lhs;
          break;

        default:
          assert(false);
      }

      if (!ok && !literal_valid(type_cast<BuiltinType>(fx.locals[dst].type)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *fx.locals[dst].type << "'\n";
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else if (is_float(fx.locals[args[0]].type) && is_float(fx.locals[args[1]].type))
    {
      Numeric::Float result;

      auto lhs = load_float(ctx, fx, args[0]);
      auto rhs = load_float(ctx, fx, args[1]);

      switch(callee.fn->builtin)
      {
        case Builtin::Add:
          result = lhs + rhs;
          break;

        case Builtin::Sub:
          result = lhs - rhs;
          break;

        case Builtin::Div:
          result = lhs / rhs;
          break;

        case Builtin::Mul:
          result = lhs * rhs;
          break;

        case Builtin::Rem:
          result = lhs % rhs;
          break;

        case Builtin::copysign:
          result = signbit(lhs.value) == signbit(rhs.value) ? lhs : -lhs;
          break;

        case Builtin::min:
          result = rhs < lhs ? rhs : lhs;
          break;

        case Builtin::max:
          result = lhs < rhs ? rhs : lhs;
          break;

        default:
          assert(false);
      }

      if (!literal_valid(type_cast<BuiltinType>(fx.locals[dst].type)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *fx.locals[dst].type << "'\n";
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else if (is_pointference_type(fx.locals[args[0]].type) && is_int_type(fx.locals[args[1]].type))
    {
      void *result;

      auto lhs = load_ptr(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      auto size = sizeof_type(remove_pointference_type(fx.locals[args[0]].type));

      if (size == 0)
      {
        ctx.diag.error("zero sized type", fx.scope, loc);
        return false;
      }

      switch(callee.fn->builtin)
      {
        case Builtin::OffsetAdd:
          result = (void*)((size_t)lhs + rhs.value * size);
          break;

        case Builtin::OffsetSub:
          result = (void*)((size_t)lhs - rhs.value * size);
          break;

        default:
          assert(false);
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else if (is_pointference_type(fx.locals[args[0]].type) && is_pointference_type(fx.locals[args[1]].type))
    {
      auto lhs = load_ptr(ctx, fx, args[0]);
      auto rhs = load_ptr(ctx, fx, args[1]);

      auto size = sizeof_type(remove_pointer_type(fx.locals[args[0]].type));

      if (size == 0)
      {
        ctx.diag.error("zero sized type", fx.scope, loc);
        return false;
      }

      assert(callee.fn->builtin == Builtin::Difference);

      if ((size_t)lhs < (size_t)rhs)
      {
        ctx.diag.error("pointer difference overflow", fx.scope, loc);
        return false;
      }

      auto result = Numeric::int_literal(+1, ((size_t)lhs - (size_t)(rhs)) / size);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else
    {
      ctx.diag.error("invalid binary arithmetic arguments", fx.scope, loc);
      ctx.diag << "  lhs type: '" << *fx.locals[args[0]].type << "' rhs type: '" << *fx.locals[args[1]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// binary_arithmetic_carry //////////////////////////
  bool eval_builtin_binary_arithmetic_carry(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_int(fx.locals[args[0]].type) && is_int(fx.locals[args[1]].type))
    {
      Numeric::Int result, carry;

      auto lhs = load_int(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      auto width = 8*sizeof_type(fx.locals[args[0]].type);
      auto is_signed = is_signed_type(fx.locals[args[0]].type);

      switch(callee.fn->builtin)
      {
        case Builtin::AddCarry:
          add_with_carry(lhs, rhs, width, is_signed, result, carry);
          break;

        case Builtin::SubCarry:
          sub_with_carry(lhs, rhs, width, is_signed, result, carry);
          break;

        case Builtin::MulCarry:
          mul_with_carry(lhs, rhs, width, is_signed, result, carry);
          break;

        default:
          assert(false);
      }

      auto tupletype = type_cast<TupleType>(fx.locals[dst].type);

      store(ctx, fx.locals[dst].alloc, tupletype->fields[0], result);
      store(ctx, (void*)((size_t)fx.locals[dst].alloc + offsetof_type(tupletype, 1)), tupletype->fields[1], carry);
    }
    else
    {
      ctx.diag.error("invalid binary arithmetic arguments", fx.scope, loc);
      ctx.diag << "  lhs type: '" << *fx.locals[args[0]].type << "' rhs type: '" << *fx.locals[args[1]].type << "'\n";
    }

    return true;
  }

  //|///////////////////// binary_arithmetic_assign /////////////////////////
  bool eval_builtin_binary_arithmetic_assign(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto arg = load_ptr(ctx, fx, args[0]);
    auto argtype = remove_pointference_type(fx.locals[args[0]].type);

    if (is_int(argtype) && is_int(fx.locals[args[1]].type))
    {
      bool ok = false;
      Numeric::Int result;

      auto lhs = load_int(ctx, arg, argtype);
      auto rhs = load_int(ctx, fx, args[1]);

      switch(callee.fn->builtin)
      {
        case Builtin::AddAssign:
          result = lhs + rhs;
          break;

        case Builtin::SubAssign:
          result = lhs - rhs;
          break;

        case Builtin::DivAssign:

          if (rhs.value == 0)
          {
            ctx.diag.error("division by zero", fx.scope, loc);
            return false;
          }

          result = lhs / rhs;
          break;

        case Builtin::MulAssign:
          result = lhs * rhs;
          break;

        case Builtin::RemAssign:

          if (rhs.value == 0)
          {
            ctx.diag.error("division by zero", fx.scope, loc);
            return false;
          }

          result = lhs % rhs;
          break;

        case Builtin::ShlAssign:

          if (rhs.sign < 0)
          {
            ctx.diag.error("negative shift", fx.scope, loc);
            return false;
          }

          result = lhs << rhs;
          ok = true;
          break;

        case Builtin::ShrAssign:

          if (rhs.sign < 0)
          {
            ctx.diag.error("negative shift", fx.scope, loc);
            return false;
          }

          result = lhs >> rhs;
          break;

        case Builtin::AndAssign:
          result = lhs & rhs;
          break;

        case Builtin::OrAssign:
          result = lhs | rhs;
          break;

        case Builtin::XorAssign:
          result = lhs ^ rhs;
          break;

        default:
          assert(false);
      }

      if (!ok && !literal_valid(type_cast<BuiltinType>(argtype)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *argtype << "'\n";
        return false;
      }

      store(ctx, arg, argtype, result);
    }
    else if (is_float(argtype) && is_float(fx.locals[args[1]].type))
    {
      Numeric::Float result;

      auto lhs = load_float(ctx, arg, argtype);
      auto rhs = load_float(ctx, fx, args[1]);

      switch(callee.fn->builtin)
      {
        case Builtin::AddAssign:
          result = lhs + rhs;
          break;

        case Builtin::SubAssign:
          result = lhs - rhs;
          break;

        case Builtin::DivAssign:

          if (rhs.value == 0)
          {
            ctx.diag.error("division by zero", fx.scope, loc);
            return false;
          }

          result = lhs / rhs;
          break;

        case Builtin::MulAssign:
          result = lhs * rhs;
          break;

        case Builtin::RemAssign:

          if (rhs.value == 0)
          {
            ctx.diag.error("division by zero", fx.scope, loc);
            return false;
          }

          result = lhs % rhs;
          break;

        default:
          assert(false);
      }

      if (!literal_valid(type_cast<BuiltinType>(argtype)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *argtype << "'\n";
        return false;
      }

      store(ctx, arg, argtype, result);
    }
    else if (is_pointference_type(argtype) && is_int_type(fx.locals[args[1]].type))
    {      
      void *result;

      auto lhs = load_ptr(ctx, arg, argtype);
      auto rhs = load_int(ctx, fx, args[1]);

      auto size = sizeof_type(remove_pointference_type(argtype));

      if (size == 0)
      {
        ctx.diag.error("zero sized type", fx.scope, loc);
        return false;
      }

      switch(callee.fn->builtin)
      {
        case Builtin::OffsetAddAssign:
          result = (void*)((size_t)lhs + rhs.value * size);
          break;

        case Builtin::OffsetSubAssign:
          result = (void*)((size_t)lhs - rhs.value * size);
          break;

        default:
          assert(false);
      }

      store(ctx, arg, argtype, result);
    }
    else
    {
      ctx.diag.error("invalid binary arithmetic assign arguments", fx.scope, loc);
      ctx.diag << "  lhs type: '" << *fx.locals[args[0]].type << "' rhs type: '" << *fx.locals[args[1]].type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, arg);

    return true;
  }

  //|///////////////////// lnot /////////////////////////////////////////////
  bool eval_builtin_lnot(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto result = !load_bool(ctx, fx, args[0]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);

    return true;
  }

  //|///////////////////// land /////////////////////////////////////////////
  bool eval_builtin_land(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_bool(ctx, fx, args[0]);
    auto rhs = load_bool(ctx, fx, args[1]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs && rhs);

    return true;
  }

  //|///////////////////// lor //////////////////////////////////////////////
  bool eval_builtin_lor(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_bool(ctx, fx, args[0]);
    auto rhs = load_bool(ctx, fx, args[1]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs || rhs);

    return true;
  }

  //|///////////////////// binary_compare ///////////////////////////////////
  bool eval_builtin_binary_compare(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_int(fx.locals[args[0]].type) && is_int(fx.locals[args[1]].type))
    {
      bool result;

      auto lhs = load_int(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      switch(callee.fn->builtin)
      {
        case Builtin::LT:
          result = lhs < rhs;
          break;

        case Builtin::GT:
          result = lhs > rhs;
          break;

        case Builtin::LE:
          result = lhs <= rhs;
          break;

        case Builtin::GE:
          result = lhs >= rhs;
          break;

        case Builtin::EQ:
          result = lhs == rhs;
          break;

        case Builtin::NE:
          result = lhs != rhs;
          break;

        default:
          assert(false);
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else if (is_float(fx.locals[args[0]].type) && is_float(fx.locals[args[1]].type))
    {
      bool result;

      auto lhs = load_float(ctx, fx, args[0]);
      auto rhs = load_float(ctx, fx, args[1]);

      switch(callee.fn->builtin)
      {
        case Builtin::LT:
          result = lhs < rhs;
          break;

        case Builtin::GT:
          result = lhs > rhs;
          break;

        case Builtin::LE:
          result = lhs <= rhs;
          break;

        case Builtin::GE:
          result = lhs >= rhs;
          break;

        case Builtin::EQ:
          result = lhs == rhs;
          break;

        case Builtin::NE:
          result = lhs != rhs;
          break;

        default:
          assert(false);
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else if (is_pointference_type(fx.locals[args[0]].type) && is_pointference_type(fx.locals[args[1]].type))
    {
      bool result;

      auto lhs = load_ptr(ctx, fx, args[0]);
      auto rhs = load_ptr(ctx, fx, args[1]);

      switch(callee.fn->builtin)
      {
        case Builtin::LT:
          result = lhs < rhs;
          break;

        case Builtin::GT:
          result = lhs > rhs;
          break;

        case Builtin::LE:
          result = lhs <= rhs;
          break;

        case Builtin::GE:
          result = lhs >= rhs;
          break;

        case Builtin::EQ:
          result = lhs == rhs;
          break;

        case Builtin::NE:
          result = lhs != rhs;
          break;

        default:
          assert(false);
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else
    {
      ctx.diag.error("invalid binary compare arguments", fx.scope, loc);
      ctx.diag << "  lhs type: '" << *fx.locals[args[0]].type << "' rhs type: '" << *fx.locals[args[1]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// cmp //////////////////////////////////////////////
  bool eval_builtin_cmp(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    int result = 0;

    if (is_int(fx.locals[args[0]].type) && is_int(fx.locals[args[1]].type))
    {
      auto lhs = load_int(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      result = (lhs == rhs) ? 0 : (lhs < rhs) ? -1 : +1;
    }
    else if (is_float(fx.locals[args[0]].type) && is_float(fx.locals[args[1]].type))
    {
      auto lhs = load_float(ctx, fx, args[0]);
      auto rhs = load_float(ctx, fx, args[1]);

      result = (lhs == rhs) ? 0 : (lhs < rhs) ? -1 : +1;
    }
    else if (is_pointference_type(fx.locals[args[0]].type) && is_pointference_type(fx.locals[args[1]].type))
    {
      auto lhs = load_ptr(ctx, fx, args[0]);
      auto rhs = load_ptr(ctx, fx, args[1]);

      result = (lhs == rhs) ? 0 : (lhs < rhs) ? -1 : +1;
    }
    else
    {
      ctx.diag.error("invalid compare arguments", fx.scope, loc);
      ctx.diag << "  lhs type: '" << *fx.locals[args[0]].type << "' rhs type: '" << *fx.locals[args[1]].type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(result));

    return true;
  }

  //|///////////////////// deref ////////////////////////////////////////////
  bool eval_builtin_deref(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, load_ptr(ctx, fx, args[0]));

    return true;
  }

  //|///////////////////// range ////////////////////////////////////////////
  bool eval_builtin_range(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto tupletype = type_cast<TupleType>(fx.locals[dst].type);

    memcpy(fx.locals[dst].alloc, fx.locals[args[0]].alloc, fx.locals[args[0]].size);
    memcpy((void*)((size_t)fx.locals[dst].alloc + offsetof_type(tupletype, 1)), fx.locals[args[1]].alloc, fx.locals[args[1]].size);

    return true;
  }

  //|///////////////////// assign ///////////////////////////////////////////
  bool eval_builtin_assign(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);

    memcpy(lhs, fx.locals[args[1]].alloc, fx.locals[args[1]].size);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs);

    return true;
  }

  //|///////////////////// slice_len ////////////////////////////////////////
  bool eval_builtin_slice_len(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto src = load_string(ctx, fx, args[0]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(1, src.length()));

    return true;
  }

  //|///////////////////// slice_data ///////////////////////////////////////
  bool eval_builtin_slice_data(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto src = load_string(ctx, fx, args[0]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, (void*)src.data());

    return true;
  }

  //|///////////////////// string_slice /////////////////////////////////////
  bool eval_builtin_string_slice(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto src = load_string(ctx, fx, args[0]);
    auto range = load_range(ctx, fx, args[1]);

    if (src.length() < range.beg)
    {
      ctx.diag.error("string slice begin overflow", fx.scope, loc);
      return false;
    }

    if (range.end < range.beg || src.length() < range.end)
    {
      ctx.diag.error("string slice end overflow", fx.scope, loc);
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Slice<const char>{ range.end - range.beg, src.data() + range.beg });

    return true;
  }

  //|///////////////////// string_append ////////////////////////////////////
  bool eval_builtin_string_append(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_string(ctx, fx, args[0]);
    auto rhs = load_string(ctx, fx, args[1]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<StringLiteralExpr>(string(lhs) + string(rhs), loc));

    return true;
  }

  //|///////////////////// string_create ////////////////////////////////////
  bool eval_builtin_string_create(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto data = load_ptr(ctx, fx, args[0]);
    auto length = load_int(ctx, fx, args[1]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<StringLiteralExpr>(string_view((char*)data, length.value), loc));

    return true;
  }

  //|///////////////////// array_data ///////////////////////////////////////
  bool eval_builtin_array_data(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs);

    return true;
  }

  //|///////////////////// array_index //////////////////////////////////////
  bool eval_builtin_array_index(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);
    auto rhs = load_int(ctx, fx, args[1]);

    auto arraytype = type_cast<ArrayType>(remove_const_type(remove_pointer_type(fx.locals[args[0]].type)));

    if (rhs.value >= array_len(arraytype))
    {
      ctx.diag.error("array subscript overflow", fx.scope, loc);
      return false;
    }

    auto result = (void*)((size_t)lhs + rhs.value * sizeof_type(arraytype->type));

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);

    return true;
  }

  //|///////////////////// array_end ////////////////////////////////////////
  bool eval_builtin_array_end(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);

    auto arraytype = type_cast<ArrayType>(remove_const_type(remove_pointer_type(fx.locals[args[0]].type)));

    auto result = (void*)((size_t)lhs + array_len(arraytype) * sizeof_type(arraytype->type));

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);

    return true;
  }

  //|///////////////////// bool /////////////////////////////////////////////
  bool eval_builtin_bool(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_int_type(fx.locals[args[0]].type))
    {
      auto lhs = load_int(ctx, fx, args[0]);

      if (lhs.sign < 0 || lhs.value > 1)
        ctx.diag.error("bool implicit cast must be 0 or 1", fx.scope, loc);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs.value != 0);
    }
    else if (is_pointference_type(fx.locals[args[0]].type))
    {
      auto lhs = load_ptr(ctx, fx, args[0]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs != nullptr);
    }
    else if (fx.locals[args[0]].type == ctx.ptrliteraltype)
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, false);
    }
    else
    {
      ctx.diag.error("invalid bool arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// is_same //////////////////////////////////////////
  bool eval_builtin_is_same(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto T = callee.find_type(callee.fn->args[0])->second;
    auto U = callee.find_type(callee.fn->args[1])->second;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, T == U);

    return true;
  }

  //|///////////////////// is_const /////////////////////////////////////////
  bool eval_builtin_is_const(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto T = callee.find_type(callee.fn->args[0])->second;

    bool is_const = is_const_type(T) || (is_qualarg_type(T) && (type_cast<QualArgType>(T)->qualifiers & QualArgType::Const));

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, is_const);

    return true;
  }

  //|///////////////////// is_rvalue ////////////////////////////////////////
  bool eval_builtin_is_rvalue(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto T = callee.find_type(callee.fn->args[0])->second;

    bool is_rvalue = is_qualarg_type(T) && (type_cast<QualArgType>(T)->qualifiers & QualArgType::RValue);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, is_rvalue);

    return true;
  }

  //|///////////////////// array_len ////////////////////////////////////////
  bool eval_builtin_array_len(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto arraytype = type_cast<ArrayType>(callee.find_type(callee.fn->args[0])->second);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, array_len(arraytype));

    return true;
  }

  //|///////////////////// tuple_len ////////////////////////////////////////
  bool eval_builtin_tuple_len(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto tupletype = type_cast<TupleType>(callee.find_type(callee.fn->args[0])->second);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(1, tuple_len(tupletype)));

    return true;
  }

  //|///////////////////// classify /////////////////////////////////////////
  bool eval_builtin_classify(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    bool result;

    if (is_int(fx.locals[args[0]].type))
    {
      switch(callee.fn->builtin)
      {
        case Builtin::is_nan:
        case Builtin::is_finite:
          result = false;
          break;

        case Builtin::is_normal:
          result = true;
          break;

        default:
          assert(false);
      }
    }
    else if (is_float(fx.locals[args[0]].type))
    {
      auto lhs = load_float(ctx, fx, args[0]);

      switch(callee.fn->builtin)
      {
        case Builtin::is_nan:
          result = isnan(lhs.value);
          break;

        case Builtin::is_finite:
          result = isfinite(lhs.value);
          break;

        case Builtin::is_normal:
          result = isnormal(lhs.value);
          if (fx.locals[args[0]].type == type(Builtin::Type_F32))
            result = isnormal(float(lhs.value));
          break;

        default:
          assert(false);
      }
    }
    else
    {
      ctx.diag.error("invalid classify arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);

    return true;
  }

  //|///////////////////// nan //////////////////////////////////////////////
  bool eval_builtin_nan(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::float_literal(std::numeric_limits<double>::quiet_NaN()));

    return true;
  }

  //|///////////////////// inf //////////////////////////////////////////////
  bool eval_builtin_inf(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::float_literal(std::numeric_limits<double>::infinity()));

    return true;
  }

  //|///////////////////// is_integral //////////////////////////////////////
  bool eval_builtin_is_integral(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto T = callee.find_type(callee.fn->args[0])->second;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, is_int_type(T) || is_char_type(T));

    return true;
  }

  //|///////////////////// is_floating_point ////////////////////////////////
  bool eval_builtin_is_floating_point(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto T = callee.find_type(callee.fn->args[0])->second;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, is_float_type(T));

    return true;
  }

  //|///////////////////// is_arithmetic ////////////////////////////////////
  bool eval_builtin_is_arithmetic(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto T = callee.find_type(callee.fn->args[0])->second;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, is_int_type(T) || is_char_type(T) || is_float_type(T));

    return true;
  }

  //|///////////////////// clz //////////////////////////////////////////////
  bool eval_builtin_clz(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_int(ctx, fx, args[0]);

    uint64_t result = 0;

    if (lhs.sign > 0 || lhs.value == 0)
    {
      auto T = callee.find_type(callee.fn->args[0])->second;

      if (!is_concrete_type(T))
      {
        ctx.diag.error("concrete type required", fx.scope, loc);
        return false;
      }

      result = 8*sizeof_type(fx.locals[args[0]].type);

      while (lhs.value != 0)
      {
        result -= 1;
        lhs.value >>= 1;
      }
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(1, result));

    return true;
  }

  //|///////////////////// ctz //////////////////////////////////////////////
  bool eval_builtin_ctz(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_int(ctx, fx, args[0]);

    uint64_t result = 0;

    if (lhs.value == 0)
    {
      result = 8*sizeof_type(fx.locals[args[0]].type);
    }

    if (lhs.value != 0)
    {
      lhs = Numeric::int_cast<uint64_t>(lhs);

      while ((lhs.value & 0x1) == 0)
      {
        result += 1;
        lhs.value >>= 1;
      }
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(1, result));

    return true;
  }

  //|///////////////////// popcnt ///////////////////////////////////////////
  bool eval_builtin_popcnt(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_int(ctx, fx, args[0]);

    uint64_t result = 0;

    if (lhs.sign < 0)
    {
      auto T = callee.find_type(callee.fn->args[0])->second;

      if (!is_concrete_type(T))
      {
        ctx.diag.error("concrete type required", fx.scope, loc);
        return false;
      }

      lhs = Numeric::int_cast<uint64_t>(lhs);
      lhs.value &= (0xFFFFFFFFFFFFFFFF >> (64 - 8*sizeof_type(fx.locals[args[0]].type)));
    }

    while (lhs.value != 0)
    {
      if ((lhs.value & 0x1) == 1)
        result += 1;

      lhs.value >>= 1;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(1, result));

    return true;
  }

  //|///////////////////// signbit //////////////////////////////////////////
  bool eval_builtin_signbit(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_int(fx.locals[args[0]].type))
    {
      auto lhs = load_int(ctx, fx, args[0]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(1, lhs.sign < 0 ? 1 : 0));
    }
    else if (is_float(fx.locals[args[0]].type))
    {
      auto lhs = load_float(ctx, fx, args[0]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(1, lhs.value < 0 ? 1 : 0));
    }
    else
    {
      ctx.diag.error("invalid signbit arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// frexp ////////////////////////////////////////////
  bool eval_builtin_frexp(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_float(fx.locals[args[0]].type))
    {
      auto lhs = load_float(ctx, fx, args[0]);

      int exponent;
      auto fraction = std::frexp(lhs.value, &exponent);

      auto tupletype = type_cast<TupleType>(fx.locals[dst].type);

      store(ctx, fx.locals[dst].alloc, tupletype->fields[0], Numeric::float_literal(fraction));
      store(ctx, (void*)((size_t)fx.locals[dst].alloc + offsetof_type(tupletype, 1)), tupletype->fields[1], Numeric::int_literal(exponent));
    }
    else
    {
      ctx.diag.error("invalid frexp arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// ldexp ////////////////////////////////////////////
  bool eval_builtin_ldexp(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_float(fx.locals[args[0]].type))
    {
      auto lhs = load_float(ctx, fx, args[0]);
      auto exp = load_int(ctx, fx, args[1]);

      auto result = std::ldexp(lhs.value, exp.sign * exp.value);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::float_literal(result));
    }
    else
    {
      ctx.diag.error("invalid ldexp arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// memset ///////////////////////////////////////////
  bool eval_builtin_memset(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto dest = load_ptr(ctx, fx, args[0]);
    auto value = load_int(ctx, fx, args[1]);
    auto count = load_int(ctx, fx, args[2]);

    memset(dest, value.value, count.value);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, dest);

    return true;
  }

  //|///////////////////// memcpy ///////////////////////////////////////////
  bool eval_builtin_memcpy(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto dest = load_ptr(ctx, fx, args[0]);
    auto source = load_ptr(ctx, fx, args[1]);
    auto count = load_int(ctx, fx, args[2]);

    memcpy(dest, source, count.value);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, dest);

    return true;
  }

  //|///////////////////// memmove //////////////////////////////////////////
  bool eval_builtin_memmove(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto dest = load_ptr(ctx, fx, args[0]);
    auto source = load_ptr(ctx, fx, args[1]);
    auto count = load_int(ctx, fx, args[2]);

    memmove(dest, source, count.value);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, dest);

    return true;
  }

  //|///////////////////// memfind //////////////////////////////////////////
  bool eval_builtin_memfind(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto source = load_ptr(ctx, fx, args[0]);
    auto value = load_int(ctx, fx, args[1]);
    auto size = load_int(ctx, fx, args[2]);

    auto result = size;

    if (auto ptr = memchr(source, value.value, size.value))
      result = Numeric::int_literal(1, (size_t)ptr - (size_t)source);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);

    return true;
  }

  //|///////////////////// eval_runtime_fd_open /////////////////////////////
  bool eval_runtime_fd_open(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    enum flags
    {
      open = 0x0,
      create = 0x01,
      exclusive = 0x02,
      trunc = 0x04,

      read = 0x01,
      write = 0x02,

      append = 0x01,
    };

    struct string
    {
      char const *data;
      uint64_t len;
    };

    string path = {};

    auto fd = load_ptr(ctx, fx, args[0]);
    memcpy(&path, fx.locals[args[1]].alloc, sizeof(path));
    auto oflags = load_int(ctx, fx, args[2]);
    //auto rights = load_int(ctx, fx, args[3]);
    auto fdflags = load_int(ctx, fx, args[4]);

    const char *mode = "r+";

    if (oflags.value & flags::create)
      mode = "w+";

    if (fdflags.value & flags::append)
      mode = "a+";

    if (oflags.value & flags::exclusive)
      mode = "w";

    auto file = fopen(std::string(path.data, path.len).c_str(), mode);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(file ? 0 : errno));

    memcpy(fd, &file, sizeof(file));

    return true;
  }

  //|///////////////////// eval_runtime_fd_readv ////////////////////////////
  bool eval_runtime_fd_readv(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    struct iovec
    {
      char *data;
      uint64_t len;
    };

    struct fd_result
    {
      uint32_t erno;
      uint64_t length;
    };

    auto fd = load_int(ctx, fx, args[0]);
    auto iovs = (iovec*)load_ptr(ctx, fx, args[1]);
    auto n = load_int(ctx, fx, args[2]);

    fd_result result = {};

    for(size_t i = 0; i < n.value; ++i)
    {
      auto cnt = fread(iovs[i].data, 1, iovs[i].len, (FILE*)fd.value);

      result.length += cnt;

      if (cnt != iovs[i].len)
        break;
    }

    memcpy(fx.locals[dst].alloc, &result, fx.locals[dst].size);

    return true;
  }

  //|///////////////////// eval_runtime_fd_preadv ///////////////////////////
  bool eval_runtime_fd_preadv(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto fd = load_int(ctx, fx, args[0]);
    auto offset = load_int(ctx, fx, args[3]);

    fseek((FILE*)fd.value, offset.value, SEEK_SET);

    return eval_runtime_fd_readv(ctx, fx, dst, call);
  }

  //|///////////////////// eval_runtime_fd_writev ///////////////////////////
  bool eval_runtime_fd_writev(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    struct ciovec
    {
      char const *data;
      uint64_t len;
    };

    struct fd_result
    {
      uint32_t erno;
      uint64_t length;
    };

    auto fd = load_int(ctx, fx, args[0]);
    auto iovs = (ciovec*)load_ptr(ctx, fx, args[1]);
    auto n = load_int(ctx, fx, args[2]);

    fd_result result = {};

    for(size_t i = 0; i < n.value; ++i)
    {
      if (fd.value == 1 || fd.value == 2)
      {
        ctx.diag << string_view(iovs[i].data, iovs[i].len);

        result.length += iovs[i].len;
      }
      else
      {
        result.length += fwrite(iovs[i].data, 1, iovs[i].len, (FILE*)fd.value);
      }
    }

    memcpy(fx.locals[dst].alloc, &result, fx.locals[dst].size);

    return true;
  }

  //|///////////////////// eval_runtime_fd_pwritev //////////////////////////
  bool eval_runtime_fd_pwritev(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto fd = load_int(ctx, fx, args[0]);
    auto offset = load_int(ctx, fx, args[3]);

    fseek((FILE*)fd.value, offset.value, SEEK_SET);

    return eval_runtime_fd_writev(ctx, fx, dst, call);
  }

  //|///////////////////// eval_runtime_fd_close ////////////////////////////
  bool eval_runtime_fd_close(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto fd = load_int(ctx, fx, args[0]);

    int result = fclose((FILE*)fd.value);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(result));

    return true;
  }

  //|///////////////////// eval_runtime_proc_exit ///////////////////////////
  bool eval_runtime_proc_exit(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    ctx.diag.error("Compile Time Exit Called", fx.scope, loc);

    return false;
  }

  //|///////////////////// eval_call ////////////////////////////////////////
  bool eval_call(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (!type_resolved(callee.returntype))
    {
      ctx.diag.error("unresolved return type", fx.scope, loc);
      return false;
    }

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch(callee.fn->builtin)
      {
        case Builtin::Plus:
        case Builtin::Minus:
        case Builtin::Not:
          return eval_builtin_unary_arithmetic(ctx, fx, dst, call);

        case Builtin::Add:
        case Builtin::Sub:
        case Builtin::Div:
        case Builtin::Mul:
        case Builtin::Rem:
        case Builtin::Shl:
        case Builtin::Shr:
        case Builtin::And:
        case Builtin::Or:
        case Builtin::Xor:
          return eval_builtin_binary_arithmetic(ctx, fx, dst, call);

        case Builtin::AddAssign:
        case Builtin::SubAssign:
        case Builtin::DivAssign:
        case Builtin::MulAssign:
        case Builtin::RemAssign:
        case Builtin::ShlAssign:
        case Builtin::ShrAssign:
        case Builtin::AndAssign:
        case Builtin::OrAssign:
        case Builtin::XorAssign:
          return eval_builtin_binary_arithmetic_assign(ctx, fx, dst, call);

        case Builtin::LNot:
          return eval_builtin_lnot(ctx, fx, dst, call);

        case Builtin::LAnd:
          return eval_builtin_land(ctx, fx, dst, call);

        case Builtin::LOr:
          return eval_builtin_lor(ctx, fx, dst, call);

        case Builtin::LT:
        case Builtin::GT:
        case Builtin::LE:
        case Builtin::GE:
        case Builtin::EQ:
        case Builtin::NE:
          return eval_builtin_binary_compare(ctx, fx, dst, call);

        case Builtin::Cmp:
          return eval_builtin_cmp(ctx, fx, dst, call);

        case Builtin::PreInc:
        case Builtin::PreDec:
          return eval_builtin_unary_arithmetic_assign(ctx, fx, dst, call);

        case Builtin::DeRef:
          return eval_builtin_deref(ctx, fx, dst, call);

        case Builtin::Range:
          return eval_builtin_range(ctx, fx, dst, call);

        case Builtin::Bool:
          return eval_builtin_bool(ctx, fx, dst, call);

        case Builtin::Assign:
          return eval_builtin_assign(ctx, fx, dst, call);

        case Builtin::OffsetAdd:
        case Builtin::OffsetSub:
        case Builtin::Difference:
          return eval_builtin_binary_arithmetic(ctx, fx, dst, call);

        case Builtin::OffsetAddAssign:
        case Builtin::OffsetSubAssign:
          return eval_builtin_binary_arithmetic_assign(ctx, fx, dst, call);

        case Builtin::AddCarry:
        case Builtin::SubCarry:
        case Builtin::MulCarry:
          return eval_builtin_binary_arithmetic_carry(ctx, fx, dst, call);

        case Builtin::StringLen:
          return eval_builtin_slice_len(ctx, fx, dst, call);

        case Builtin::StringData:
          return eval_builtin_slice_data(ctx, fx, dst, call);

        case Builtin::StringSlice:
          return eval_builtin_string_slice(ctx, fx, dst, call);

        case Builtin::StringAppend:
          return eval_builtin_string_append(ctx, fx, dst, call);

        case Builtin::StringCreate:
          return eval_builtin_string_create(ctx, fx, dst, call);

        case Builtin::ArrayData:
        case Builtin::ArrayBegin:
          return eval_builtin_array_data(ctx, fx, dst, call);

        case Builtin::ArrayIndex:
          return eval_builtin_array_index(ctx, fx, dst, call);

        case Builtin::ArrayEnd:
          return eval_builtin_array_end(ctx, fx, dst, call);

        case Builtin::is_same:
          return eval_builtin_is_same(ctx, fx, dst, call);

        case Builtin::is_const:
          return eval_builtin_is_const(ctx, fx, dst, call);

        case Builtin::is_rvalue:
          return eval_builtin_is_rvalue(ctx, fx, dst, call);

        case Builtin::array_len:
          return eval_builtin_array_len(ctx, fx, dst, call);

        case Builtin::tuple_len:
          return eval_builtin_tuple_len(ctx, fx, dst, call);

        case Builtin::is_nan:
        case Builtin::is_finite:
        case Builtin::is_normal:
          return eval_builtin_classify(ctx, fx, dst, call);

        case Builtin::nan:
          return eval_builtin_nan(ctx, fx, dst, call);

        case Builtin::inf:
          return eval_builtin_inf(ctx, fx, dst, call);

        case Builtin::is_integral:
          return eval_builtin_is_integral(ctx, fx, dst, call);

        case Builtin::is_floating_point:
          return eval_builtin_is_floating_point(ctx, fx, dst, call);

        case Builtin::is_arithmetic:
          return eval_builtin_is_arithmetic(ctx, fx, dst, call);

        case Builtin::clz:
          return eval_builtin_clz(ctx, fx, dst, call);

        case Builtin::ctz:
          return eval_builtin_ctz(ctx, fx, dst, call);

        case Builtin::popcnt:
          return eval_builtin_popcnt(ctx, fx, dst, call);

        case Builtin::signbit:
          return eval_builtin_signbit(ctx, fx, dst, call);

        case Builtin::frexp:
          return eval_builtin_frexp(ctx, fx, dst, call);

        case Builtin::ldexp:
          return eval_builtin_ldexp(ctx, fx, dst, call);

        case Builtin::abs:
        case Builtin::floor:
        case Builtin::ceil:
        case Builtin::round:
        case Builtin::trunc:
        case Builtin::sqrt:
          return eval_builtin_unary_arithmetic(ctx, fx, dst, call);

        case Builtin::min:
        case Builtin::max:
        case Builtin::copysign:
          return eval_builtin_binary_arithmetic(ctx, fx, dst, call);

        case Builtin::memset:
          return eval_builtin_memset(ctx, fx, dst, call);

        case Builtin::memcpy:
          return eval_builtin_memcpy(ctx, fx, dst, call);

        case Builtin::memmove:
          return eval_builtin_memmove(ctx, fx, dst, call);

        case Builtin::memfind:
          return eval_builtin_memfind(ctx, fx, dst, call);

        default:
          assert(false);
      }

      return false;
    }
    else if (callee.fn->flags & FunctionDecl::ExternC)
    {
      if (callee.fn->name == "fd_open")
        return eval_runtime_fd_open(ctx, fx, dst, call);

      if (callee.fn->name == "fd_readv")
        return eval_runtime_fd_readv(ctx, fx, dst, call);

      if (callee.fn->name == "fd_preadv")
        return eval_runtime_fd_preadv(ctx, fx, dst, call);

      if (callee.fn->name == "fd_writev")
        return eval_runtime_fd_writev(ctx, fx, dst, call);

      if (callee.fn->name == "fd_pwritev")
        return eval_runtime_fd_pwritev(ctx, fx, dst, call);

      if (callee.fn->name == "fd_close")
        return eval_runtime_fd_close(ctx, fx, dst, call);

      if (callee.fn->name == "proc_exit")
        return eval_runtime_proc_exit(ctx, fx, dst, call);

      ctx.diag.error("invalid compille time call", fx.scope, loc);

      return false;
    }
    else
    {
      auto mir = lower(callee, ctx.typetable, ctx.diag);

#if 0
      dump_mir(mir);
#endif

      vector<FunctionContext::Local> parms;

      if (callee.throwtype)
      {
        parms.push_back(fx.locals[fx.errorarg]);
      }

      for(auto &arg : args)
      {
        parms.push_back(fx.locals[arg]);
      }

      return eval_function(ctx, callee.fn, mir, fx.locals[dst], parms);
    }
  }

  //|///////////////////// eval_cast ////////////////////////////////////////
  bool eval_cast(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CastData const &cast)
  {
    auto &[arg, loc] = cast;

    if (is_int(fx.locals[dst].type) && is_int(fx.locals[arg].type))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, load_int(ctx, fx.locals[arg].alloc, fx.locals[arg].type));
    }
    else if (is_float(fx.locals[dst].type) && is_float(fx.locals[arg].type))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, load_float(ctx, fx.locals[arg].alloc, fx.locals[arg].type));
    }
    else if (is_int(fx.locals[dst].type) && is_float(fx.locals[arg].type))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_cast<uint64_t>(load_float(ctx, fx.locals[arg].alloc, fx.locals[arg].type)));
    }
    else if (is_float(fx.locals[dst].type) && is_int(fx.locals[arg].type))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::float_cast<double>(load_int(ctx, fx.locals[arg].alloc, fx.locals[arg].type)));
    }
    else if (is_pointference_type(fx.locals[dst].type) && is_pointference_type(fx.locals[arg].type))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, load_ptr(ctx, fx.locals[arg].alloc, fx.locals[arg].type));
    }
    else if (is_pointference_type(fx.locals[dst].type) && is_int_type(fx.locals[arg].type))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, (void*)(load_int(ctx, fx.locals[arg].alloc, fx.locals[arg].type).value));
    }
    else if (is_int_type(fx.locals[dst].type) && is_pointference_type(fx.locals[arg].type))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(1, (size_t)load_ptr(ctx, fx.locals[arg].alloc, fx.locals[arg].type)));
    }
    else
    {
      ctx.diag.error("invalid static cast", fx.scope, loc);
      ctx.diag << "  src type: '" << *fx.locals[arg].type << "' dst type: '" << *fx.locals[dst].type << "'\n";
    }

    return true;
  }

  //|///////////////////// eval_assign_statement ////////////////////////////
  bool eval_assign_statement(EvalContext &ctx, FunctionContext &fx, MIR::Statement const &statement)
  {
    auto &src = statement.src;
    auto &dst = statement.dst;

    switch (src.kind())
    {
      case MIR::RValue::Empty:
        return true;

      case MIR::RValue::Constant:
        return eval_constant(ctx, fx, dst, src.get<MIR::RValue::Constant>());

      case MIR::RValue::Variable:
        return eval_variable(ctx, fx, dst, src.get<MIR::RValue::Variable>());

      case MIR::RValue::Call:
        return eval_call(ctx, fx, dst, src.get<MIR::RValue::Call>());

      case MIR::RValue::Cast:
        return eval_cast(ctx, fx, dst, src.get<MIR::RValue::Cast>());

      default:
        assert(false);
        return false;
    }
  }

  //|///////////////////// eval_construct_statement ////////////////////////////
  bool eval_construct_statement(EvalContext &ctx, FunctionContext &fx, MIR::Statement const &statement)
  {
    auto dst = statement.dst;

    FunctionContext::Local dest;
    dest.type = remove_pointer_type(fx.locals[dst].type);
    dest.alloc = load_ptr(ctx, fx.locals[dst - 1].alloc, fx.locals[dst - 1].type);
    dest.size = sizeof_type(dest.type);

    swap(fx.locals[dst], dest);

    eval_assign_statement(ctx, fx, statement);

    swap(dest, fx.locals[dst]);

    return true;
  }

  //|///////////////////// eval_function ////////////////////////////////////
  bool eval_function(EvalContext &ctx, Scope const &scope, MIR const &mir, FunctionContext::Local &returnvalue, vector<FunctionContext::Local> const &args)
  {
    FunctionContext fx;

    fx.scope = scope;

    fx.locals.push_back(returnvalue);

    for(auto &arg : args)
    {
      fx.locals.push_back(arg);
    }

    for(size_t i = mir.args_end, end = mir.locals.size(); i != end; ++i)
    {
      if (!type_resolved(mir.locals[i].type))
        continue;

      fx.locals.push_back(alloc(ctx, mir.locals[i]));
    }

    for(size_t block = 0; block < mir.blocks.size(); )
    {
      if (auto &terminator = mir.blocks[block].terminator; terminator.kind == MIR::Terminator::Catch)
        fx.errorarg = terminator.value;

      for(auto &statement : mir.blocks[block].statements)
      {
        switch (statement.kind)
        {
          case MIR::Statement::NoOp:
            break;

          case MIR::Statement::Assign:
            if (!eval_assign_statement(ctx, fx, statement))
              return false;
            break;

          case MIR::Statement::Construct:
            if (!eval_construct_statement(ctx, fx, statement))
              return false;
            break;

          case MIR::Statement::StorageLive:
            break;

          case MIR::Statement::StorageDead:
            break;
        }
      }

      switch(auto &terminator = mir.blocks[block].terminator; terminator.kind)
      {
        case MIR::Terminator::Goto:
          block = terminator.blockid;
          break;

        case MIR::Terminator::Switch:
          if (is_bool_type(fx.locals[terminator.value].type))
          {
            auto cond = load_bool(ctx, fx.locals[terminator.value].alloc, fx.locals[terminator.value].type);

            block = cond ? terminator.blockid : get<1>(terminator.targets[0]);
          }
          break;

        case MIR::Terminator::Catch:
          block = ctx.exception ? terminator.blockid : terminator.blockid + 1;
          ctx.exception = (mir.throws && terminator.value == 1 && ctx.exception);
          break;

        case MIR::Terminator::Throw:
          block = terminator.blockid;
          ctx.exception = (mir.throws && terminator.value == 1);
          break;

        case MIR::Terminator::Return:
          block = mir.blocks.size();
          break;
      }
    }

    return true;
  }

  //|///////////////////// eval_function ////////////////////////////////////
  bool eval_function(EvalContext &ctx, Scope const &scope, FnSig const &callee, FunctionContext::Local &returnvalue, vector<EvalResult> const &parms, SourceLocation loc)
  {
    FunctionContext fx;

    fx.scope = scope;

    fx.locals.push_back(returnvalue);

    if (callee.throwtype)
    {
      fx.locals.push_back(alloc(ctx, callee.throwtype));
    }

    vector<MIR::local_t> args;

    for(size_t k = 0; k < parms.size(); ++k)
    {
      args.push_back(fx.locals.size());

      fx.locals.push_back(alloc(ctx, parms[k].type));

      if (is_reference_type(parms[k].type))
      {
        fx.locals.push_back(alloc(ctx, remove_const_type(remove_reference_type(parms[k].type))));

        eval_constant(ctx, fx, args.back() + 1, MIR::RValue::literal(parms[k].value));

        store(ctx, fx.locals[args.back()].alloc, fx.locals[args.back()].type, fx.locals[args.back() + 1].alloc);
      }
      else
      {
        eval_constant(ctx, fx, args.back(), MIR::RValue::literal(parms[k].value));
      }
    }

    if (ctx.diag.has_errored())
      return false;

    return eval_call(ctx, fx, 0, MIR::RValue::call(callee, args, loc));
  }

  //|///////////////////// eval_result //////////////////////////////////////
  Expr *make_expr(EvalContext &ctx, void *alloc, Type *type, SourceLocation loc)
  {
    // TODO: this needs an allocator that is attached to the parent mir somehow

    if (type == ctx.voidtype)
    {
      return ctx.make_expr<VoidLiteralExpr>(loc);
    }
    else if (type == ctx.ptrliteraltype)
    {
      return ctx.make_expr<PointerLiteralExpr>(loc);
    }
    else if (is_bool_type(type))
    {
      return ctx.make_expr<BoolLiteralExpr>(load_bool(ctx, alloc, type), loc);
    }
    else if (is_char_type(type))
    {
      return ctx.make_expr<CharLiteralExpr>(load_int(ctx, alloc, type), loc);
    }
    else if (is_int_type(type))
    {
      return ctx.make_expr<IntLiteralExpr>(load_int(ctx, alloc, type), loc);
    }
    else if (is_float_type(type))
    {
      return ctx.make_expr<FloatLiteralExpr>(load_float(ctx, alloc, type), loc);
    }
    else if (is_enum_type(type))
    {
      return ctx.make_expr<IntLiteralExpr>(load_int(ctx, alloc, type), loc);
    }
    else if (is_string_type(type))
    {
      return ctx.make_expr<StringLiteralExpr>(load_string(ctx, alloc, type), loc);
    }
    else if (is_array_type(type) && is_trivial_copy_type(type))
    {
      vector<Expr*> elements;

      auto elemtype = type_cast<ArrayType>(type)->type;
      auto elemsize = sizeof_type(elemtype);
      auto arraylen = array_len(type_cast<ArrayType>(type));

      for(size_t i = 0; i < arraylen; ++i)
      {
        elements.push_back(make_expr(ctx, alloc, elemtype, loc));

        alloc = (void*)((size_t)alloc + elemsize);
      }

      if (any_of(elements.begin(), elements.end(), [](auto &k) { return !k; }))
        return nullptr;

      return ctx.make_expr<ArrayLiteralExpr>(elements, type_cast<ArrayType>(type)->size, loc);
    }
    else if (is_compound_type(type) && is_trivial_copy_type(type))
    {
      vector<Expr*> fields;

      for(auto &field : type_cast<CompoundType>(type)->fields)
      {
        fields.push_back(make_expr(ctx, alloc, field, loc));

        alloc = (void*)((size_t)alloc + sizeof_type(field));
      }

      if (any_of(fields.begin(), fields.end(), [](auto &k) { return !k; }))
        return nullptr;

      return ctx.make_expr<CompoundLiteralExpr>(fields, loc);
    }
    else
    {
      ctx.diag.error("invalid literal type", ctx.dx, loc);
    }

    return nullptr;
  }

  Expr *make_expr(EvalContext &ctx, FunctionContext::Local &value, SourceLocation loc)
  {
    return make_expr(ctx, value.alloc, value.type, loc);
  }
}

//|--------------------- Evaluate -------------------------------------------
//|--------------------------------------------------------------------------

EvalResult evaluate(Scope const &scope, MIR const &mir, TypeTable &typetable, Diag &diag, SourceLocation loc)
{
  EvalResult result = {};

  EvalContext ctx(scope, typetable, diag);

  if (ctx.diag.has_errored())
    return result;

  if (!type_resolved(mir.locals[0].type))
  {
    ctx.diag.error("unresolved expression type", scope, loc);
    return result;
  }

  auto returnvalue = alloc(ctx, mir.locals[0]);

  if (!eval_function(ctx, scope, mir, returnvalue))
    return result;

  result.type = returnvalue.type;
  result.value = make_expr(ctx, returnvalue, loc);

  return result;
}

EvalResult evaluate(Scope const &scope, FnSig const &callee, vector<EvalResult> const &parms, TypeTable &typetable, Diag &diag, SourceLocation loc)
{
  EvalResult result = {};

  EvalContext ctx(scope, typetable, diag);

  if (!type_resolved(callee.returntype))
  {
    ctx.diag.error("unresolved return type", scope, loc);
    return result;
  }

  auto returnvalue = alloc(ctx, callee.returntype);

  if (!eval_function(ctx, scope, callee, returnvalue, parms, loc))
    return result;

  if (ctx.exception)
  {
    ctx.diag.error("exception occured in compile time context", scope, loc);
    return result;
  }

  result.type = returnvalue.type;
  result.value = make_expr(ctx, returnvalue, loc);

  return result;
}

EvalResult evaluate(Scope const &scope, Expr *expr, unordered_map<Decl*, MIR::Fragment> const &symbols, TypeTable &typetable, Diag &diag, SourceLocation loc)
{
  return evaluate(scope, lower(scope, expr, symbols, typetable, diag), typetable, diag, loc);
}