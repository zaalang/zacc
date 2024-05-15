//
// interp.cpp
//
// Copyright (c) 2020-2024 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "interp.h"
#include "sema.h"
#include "diag.h"
#include "copier.h"
#include "numeric.h"
#include "semantic.h"
#include "typer.h"
#include <iostream>
#include <algorithm>
#include <cstring>
#include <climits>
#include <cstdio>
#include <cmath>
#include <memory>
#include <chrono>
#include <sys/stat.h>

#if defined _MSC_VER
#define environ _environ
#else
#include <unistd.h>
#endif

using namespace std;

namespace
{
#ifdef NDEBUG
  struct uninit_t
  {
    union { uint8_t ch; };

    uninit_t() { }
  };
#else
  using uninit_t = uint8_t;
#endif

  struct FunctionContext
  {
    Scope scope;

    struct Local
    {
      long flags;
      Type *type;

      size_t size;
      void *alloc;
    };

    Local *locals;

    size_t errorarg = 0;
  };

  struct EvalContext
  {
    Scope dx;
    Diag diag;

    TypeTable &typetable;

    void *stackp;
    vector<vector<uninit_t>> memory;

    map<tuple<Type*, ArrayLiteralExpr const *>, void*> arrayliterals;
    map<tuple<Type*, CompoundLiteralExpr const *>, void*> compoundliterals;

    bool exception;

    vector<Decl*> fragments;

    template<typename T>
    T *push(size_t count = 1)
    {
      auto sp = new(stackp) T[count];

      stackp = (void*)(((uintptr_t)(stackp) + count * sizeof(T) + alignof(void*) - 1) & -alignof(void*));

      if (stackp >= memory[0].data() + memory[0].size())
        throw runtime_error("interpreter stack overrun");

      return sp;
    }

    void *allocate(size_t size, size_t alignment)
    {
      auto page = &memory.back();

      if (page->capacity() - page->size() < size + alignment)
      {
        memory.push_back({});
        memory.back().reserve(max(size + alignment, size_t(4096)));
        page = &memory.back();
      }

      auto sz = page->capacity() - page->size();
      auto ptr = static_cast<void*>(page->data() + page->size());

      std::align(alignment, size, ptr, sz);

      page->resize(page->capacity() - sz + size);

      return ptr;
    }

    template<typename T, typename ...Args>
    T *make_expr(Args&&... args)
    {
      return new T(std::forward<Args>(args)...);
    }

    Diag &outdiag;

    EvalContext(Scope const &dx, TypeTable &typetable, Diag &diag)
      : dx(dx),
        diag(diag.leader()),
        typetable(typetable),
        outdiag(diag)
    {
      exception = false;

      memory.resize(1);
      memory.back().reserve(768*1024);

      stackp = allocate(512*1024, 16);
    }

    ~EvalContext()
    {
      outdiag << diag;
    }
  };

  template <typename T>
  struct Range
  {
    T beg;
    T end;
  };

  template <typename T>
  struct Slice
  {
    uint64_t len;
    T *data;
  };

  bool is_int(Type const *type)
  {
    return is_int_type(type) || is_bool_type(type) || is_char_type(type) || is_enum_type(type) || is_declid_type(type) || is_typeid_type(type);
  }

  bool is_float(Type const *type)
  {
    return is_float_type(type);
  }

  bool is_typed_literal(Type const *type)
  {
    if (type->klass() == Type::Builtin)
    {
      auto kind = type_cast<BuiltinType>(type)->kind();

      return kind == BuiltinType::IntLiteral || kind == BuiltinType::FloatLiteral || kind == BuiltinType::StringLiteral || kind == BuiltinType::PtrLiteral || kind == BuiltinType::Void || kind == BuiltinType::Bool || kind == BuiltinType::Char;
    }

    if (is_slice_type(type))
      return true;

    return false;
  }

  void store(EvalContext &ctx, void *alloc, Type *type, Numeric::Int const &value);
  void store(EvalContext &ctx, void *alloc, Type *type, Numeric::Float const &value);
  void store(EvalContext &ctx, void *alloc, Type *type, Expr *value);
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, Expr *value);
  bool eval_function(EvalContext &ctx, Scope const &scope, MIR const &mir, FunctionContext::Local *locals);

  //|///////////////////// alloc ////////////////////////////////////////////
  FunctionContext::Local alloc(EvalContext &ctx, MIR::Local const &local)
  {
    FunctionContext::Local result;

    result.type = local.type;
    result.flags = local.flags;
    result.size = (local.flags & MIR::Local::Reference) ? sizeof(void*) : sizeof_type(local.type);
    result.alloc = ctx.push<uint8_t>(result.size);

    return result;
  }

  //|///////////////////// load /////////////////////////////////////////////
  void *load_ptr(EvalContext &ctx, void *alloc)
  {
    void *value;

    memcpy(&value, alloc, sizeof(value));

    return value;
  }

  template<typename T = void>
  T* load_ptr(EvalContext &ctx, FunctionContext &fx, size_t src)
  {
    return static_cast<T*>(load_ptr(ctx, fx.locals[src].alloc));
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
        value = Numeric::int_literal(+1, value_u8);
        break;

      case BuiltinType::U16:
        memcpy(&value_u16, alloc, sizeof(value_u16));
        value = Numeric::int_literal(+1, value_u16);
        break;

      case BuiltinType::U32:
      case BuiltinType::Char:
        memcpy(&value_u32, alloc, sizeof(value_u32));
        value = Numeric::int_literal(+1, value_u32);
        break;

      case BuiltinType::U64:
      case BuiltinType::USize:
        memcpy(&value_u64, alloc, sizeof(value_u64));
        value = Numeric::int_literal(+1, value_u64);
        break;

      case BuiltinType::IntLiteral:
      case BuiltinType::DeclidLiteral:
      case BuiltinType::TypeidLiteral:
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
  template <typename T>
  Slice<T> load_slice(EvalContext &ctx, void *alloc, Type *type)
  {
    Slice<T> value;

    memcpy(&value, alloc, sizeof(value));

    return value;
  }

  template <typename T>
  Slice<T> load_slice(EvalContext &ctx, FunctionContext &fx, size_t src)
  {
    return load_slice<T>(ctx, fx.locals[src].alloc, fx.locals[src].type);
  }

  //|///////////////////// load /////////////////////////////////////////////
  template <typename T>
  Range<T> load_range(EvalContext &ctx, void *alloc, Type *type)
  {
    Range<T> value;

    assert(is_tuple_type(type));

    memcpy(&value, alloc, sizeof(value));

    return value;
  }

  template <typename T>
  Range<T> load_range(EvalContext &ctx, FunctionContext &fx, size_t src)
  {
    return load_range<T>(ctx, fx.locals[src].alloc, fx.locals[src].type);
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, void const *value)
  {
    memcpy(alloc, &value, sizeof(value));
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
      case BuiltinType::DeclidLiteral:
      case BuiltinType::TypeidLiteral:
        memcpy(alloc, &value, sizeof(value));
        break;

      case BuiltinType::F32:
      case BuiltinType::F64:
      case BuiltinType::FloatLiteral:
        store(ctx, alloc, type, Numeric::float_cast<double>(value));
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

      case BuiltinType::I8:
      case BuiltinType::I16:
      case BuiltinType::I32:
      case BuiltinType::I64:
      case BuiltinType::ISize:
      case BuiltinType::U8:
      case BuiltinType::Bool:
      case BuiltinType::U16:
      case BuiltinType::U32:
      case BuiltinType::Char:
      case BuiltinType::U64:
      case BuiltinType::USize:
      case BuiltinType::IntLiteral:
        store(ctx, alloc, type, Numeric::int_cast<double>(value));
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
  template<typename T>
  void store(EvalContext &ctx, void *alloc, Type *type, Slice<T> const &value)
  {
    memcpy(alloc, &value, sizeof(value));
  }

  //|///////////////////// store ////////////////////////////////////////////
  template<typename T>
  void store(EvalContext &ctx, void *alloc, Type *type, Range<T> const &value)
  {
    memcpy(alloc, &value, sizeof(value));
  }

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

    for (auto &element : value->elements)
    {
      store(ctx, address, remove_const_type(elemtype), element);

      address = (void*)((size_t)address + elemsize);
    }

    for (size_t i = value->elements.size(); i < arraylen; ++i)
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
    auto dsttype = type_cast<CompoundType>(type);

    if (is_union_type(type))
    {
      auto active = expr_cast<IntLiteralExpr>(value->fields[0])->value().value;

      store(ctx, address, dsttype->fields[0], value->fields[0]);
      store(ctx, (void*)((size_t)address + offsetof_field(dsttype, active)), remove_const_type(dsttype->fields[active]), value->fields[1]);
    }

    if (is_compound_type(type))
    {
      assert(dsttype->fields.size() == value->fields.size());

      for (size_t i = 0; i < value->fields.size(); ++i)
      {
        auto alignment = alignof_field(dsttype, i);

        address = (void*)(((size_t)address + alignment - 1) & -alignment);

        store(ctx, address, remove_const_type(dsttype->fields[i]), value->fields[i]);

        address = (void*)((size_t)address + sizeof_type(dsttype->fields[i]));
      }
    }
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(EvalContext &ctx, void *alloc, Type *type, Expr *value)
  {
    switch (value->kind())
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

      case Expr::PointerLiteral:
        store(ctx, alloc, nullptr);
        break;

      case Expr::FunctionPointer:
        store(ctx, alloc, value);
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

  //|///////////////////// eval_result //////////////////////////////////////
  Expr *make_expr(EvalContext &ctx, void *alloc, Type *type, SourceLocation loc)
  {
    // TODO: this needs an allocator that is attached to the parent mir somehow

    if (is_void_type(type))
    {
      return ctx.make_expr<VoidLiteralExpr>(loc);
    }
    else if (is_null_type(type))
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
    else if (is_pointer_type(type))
    {
      auto ptr = load_ptr(ctx, alloc);

      if (ptr == 0)
        return ctx.make_expr<PointerLiteralExpr>(loc);

      if (is_function_type(remove_const_type(remove_pointer_type(type))))
        return static_cast<FunctionPointerExpr*>(ptr);

      ctx.diag.error("invalid literal pointer", ctx.dx, loc);
    }
    else if (is_reference_type(type))
    {
      auto ptr = load_ptr(ctx, alloc);

      if (is_function_type(remove_const_type(remove_reference_type(type))))
        return static_cast<FunctionPointerExpr*>(ptr);

      ctx.diag.error("invalid literal pointer", ctx.dx, loc);
    }
    else if (is_string_type(type))
    {
      return ctx.make_expr<StringLiteralExpr>(load_string(ctx, alloc, type), loc);
    }
    else if (is_declid_type(type))
    {
      return ctx.make_expr<IntLiteralExpr>(load_int(ctx, alloc, type), loc);
    }
    else if (is_typeid_type(type))
    {
      return ctx.make_expr<IntLiteralExpr>(load_int(ctx, alloc, type), loc);
    }
    else if (is_slice_type(type))
    {
      auto span = load_slice<void>(ctx, alloc, type);

      auto elemtype = type_cast<SliceType>(type)->type;
      auto elemsize = sizeof_type(elemtype);
      auto arraylen = span.len;
      auto sizetype = ctx.typetable.find_or_create<TypeLitType>(ctx.make_expr<IntLiteralExpr>(Numeric::int_literal(arraylen), loc));

      auto elements = vector<Expr*>(arraylen);

      for (size_t i = 0; i < elements.size(); ++i)
      {
        elements[i] = make_expr(ctx, (void*)((size_t)span.data + i * elemsize), elemtype, loc);
      }

      if (any_of(elements.begin(), elements.end(), [](auto &k) { return !k; }))
        return nullptr;

      return ctx.make_expr<ArrayLiteralExpr>(elements, sizetype, loc);
    }
    else if (is_array_type(type))
    {
      auto elemtype = type_cast<ArrayType>(type)->type;
      auto elemsize = sizeof_type(elemtype);
      auto arraylen = array_len(type_cast<ArrayType>(type));

      auto elements = vector<Expr*>(arraylen);

      for (size_t i = 0; i < elements.size(); ++i)
      {
        elements[i] = make_expr(ctx, (void*)((size_t)alloc + i * elemsize), elemtype, loc);
      }

      if (any_of(elements.begin(), elements.end(), [](auto &k) { return !k; }))
        return nullptr;

      return ctx.make_expr<ArrayLiteralExpr>(elements, type_cast<ArrayType>(type)->size, loc);
    }
    else if (is_union_type(type))
    {
      auto compoundtype = type_cast<CompoundType>(type);
      auto active = load_int(ctx, alloc, type_cast<CompoundType>(type)->fields[0]).value;

      auto fields = vector<Expr*>(2);

      fields[0] = make_expr(ctx, alloc, compoundtype->fields[0], loc);
      fields[1] = make_expr(ctx, (void*)((size_t)alloc + offsetof_field(compoundtype, active)), compoundtype->fields[active], loc);

      if (any_of(fields.begin(), fields.end(), [](auto &k) { return !k; }))
        return nullptr;

      return ctx.make_expr<CompoundLiteralExpr>(fields, loc);
    }
    else if (is_compound_type(type) && is_literal_copy_type(type))
    {
      auto compoundtype = type_cast<CompoundType>(type);
      auto fieldslen = compoundtype->fields.size();

      auto fields = vector<Expr*>(fieldslen);

      for (size_t i = 0; i < fields.size(); ++i)
      {
        auto alignment = alignof_field(compoundtype, i);

        alloc = (void*)(((size_t)alloc + alignment - 1) & -alignment);

        fields[i] = make_expr(ctx, alloc, compoundtype->fields[i], loc);

        alloc = (void*)((size_t)alloc + sizeof_field(compoundtype, i));
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

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, VoidLiteralExpr *value)
  {
    if (is_void_type(type))
      return true;

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: 'void' required type: '" << *type << "'\n";

    return false;
  }

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, BoolLiteralExpr *value)
  {
    if (is_bool_type(type))
      return true;

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: 'bool' required type: '" << *type << "'\n";

    return false;
  }

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, CharLiteralExpr *value)
  {
    if (is_char_type(type) || is_int_type(type))
    {
      if (!is_literal_valid(type_cast<BuiltinType>(type)->kind(), expr_cast<CharLiteralExpr>(value)->value()))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, value->loc());
        ctx.diag << "  literal value: '" << expr_cast<CharLiteralExpr>(value)->value() << "' required type: '" << *type << "'\n";
        return false;
      }

      return true;
    }

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: '#char' required type: '" << *type << "'\n";

    return false;
  }

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, IntLiteralExpr *value)
  {
    if (is_enum_type(type))
    {
      type = type_cast<TagType>(type)->fields[0];
    }

    if (is_bool_type(type) || is_int_type(type) || is_char_type(type) || is_declid_type(type) || is_typeid_type(type))
    {
      if (!is_literal_valid(type_cast<BuiltinType>(type)->kind(), expr_cast<IntLiteralExpr>(value)->value()))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, value->loc());
        ctx.diag << "  literal value: '" << expr_cast<IntLiteralExpr>(value)->value() << "' required type: '" << *type << "'\n";
        return false;
      }

      return true;
    }

    if (is_float_type(type))
    {
      if (!is_literal_valid(type_cast<BuiltinType>(type)->kind(), Numeric::float_cast<double>(expr_cast<IntLiteralExpr>(value)->value())))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, value->loc());
        ctx.diag << "  literal value: '" << expr_cast<IntLiteralExpr>(value)->value() << "' required type: '" << *type << "'\n";
        return false;
      }

      return true;
    }

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: '#int' required type: '" << *type << "'\n";

    return false;
  }

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, FloatLiteralExpr *value)
  {
    if (is_bool_type(type) || is_int_type(type) || is_char_type(type))
    {
      if (!is_literal_valid(type_cast<BuiltinType>(type)->kind(), Numeric::int_cast<double>(expr_cast<FloatLiteralExpr>(value)->value())))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, value->loc());
        ctx.diag << "  literal value: '" << expr_cast<FloatLiteralExpr>(value)->value() << "' required type: '" << *type << "'\n";
        return false;
      }

      return true;
    }

    if (is_float_type(type))
    {
      if (!is_literal_valid(type_cast<BuiltinType>(type)->kind(), expr_cast<FloatLiteralExpr>(value)->value()))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, value->loc());
        ctx.diag << "  literal value: '" << expr_cast<FloatLiteralExpr>(value)->value() << "' required type: '" << *type << "'\n";
        return false;
      }

      return true;
    }

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: '#float' required type: '" << *type << "'\n";

    return false;
  }

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, PointerLiteralExpr *value)
  {
    if (is_null_type(type) || is_pointer_type(type))
      return true;

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: 'null' required type: '" << *type << "'\n";

    return false;
  }
  
  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, FunctionPointerExpr *value)
  {
    if (is_pointference_type(type))
      return true;

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: 'fn' required type: '" << *type << "'\n";

    return false;
  }

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, StringLiteralExpr *value)
  {
    if (is_string_type(type))
      return true;

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: '#string' required type: '" << *type << "'\n";

    return false;
  }

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, ArrayLiteralExpr *value)
  {
    if (is_array_type(type))
    {
      for (auto &element : expr_cast<ArrayLiteralExpr>(value)->elements)
      {
        if (!eval_validate_literal(ctx, fx, remove_const_type(type_cast<ArrayType>(type)->type), element))
          return false;
      }

      return true;
    }

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: '#array' required type: '" << *type << "'\n";

    return false;
  }

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, CompoundLiteralExpr *value)
  {
    if (is_union_type(type))
    {
      auto active = expr_cast<IntLiteralExpr>(expr_cast<CompoundLiteralExpr>(value)->fields[0])->value().value;

      if (!eval_validate_literal(ctx, fx, type_cast<CompoundType>(type)->fields[0], expr_cast<CompoundLiteralExpr>(value)->fields[0]))
        return false;

      if (!eval_validate_literal(ctx, fx, remove_const_type(type_cast<CompoundType>(type)->fields[active]), expr_cast<CompoundLiteralExpr>(value)->fields[1]))
        return false;

      return true;
    }

    if (is_compound_type(type))
    {
      auto &fields = type_cast<CompoundType>(type)->fields;

      if (fields.size() != expr_cast<CompoundLiteralExpr>(value)->fields.size())
        return false;

      for (size_t i = 0; i < fields.size(); ++i)
      {
        if (!eval_validate_literal(ctx, fx, remove_const_type(fields[i]), expr_cast<CompoundLiteralExpr>(value)->fields[i]))
          return false;
      }

      return true;
    }

    ctx.diag.error("literal type incompatible with required type", fx.scope, value->loc());
    ctx.diag << "  literal type: '#struct' required type: '" << *type << "'\n";

    return false;
  }

  //|///////////////////// eval_validate_literal ////////////////////////////
  bool eval_validate_literal(EvalContext &ctx, FunctionContext &fx, Type *type, Expr *value)
  {
    switch (value->kind())
    {
      case Expr::VoidLiteral:
        return eval_validate_literal(ctx, fx, type, expr_cast<VoidLiteralExpr>(value));

      case Expr::BoolLiteral:
        return eval_validate_literal(ctx, fx, type, expr_cast<BoolLiteralExpr>(value));

      case Expr::CharLiteral:
        return eval_validate_literal(ctx, fx, type, expr_cast<CharLiteralExpr>(value));

      case Expr::IntLiteral:
        return eval_validate_literal(ctx, fx, type, expr_cast<IntLiteralExpr>(value));

      case Expr::FloatLiteral:
        return eval_validate_literal(ctx, fx, type, expr_cast<FloatLiteralExpr>(value));

      case Expr::PointerLiteral:
        return eval_validate_literal(ctx, fx, type, expr_cast<PointerLiteralExpr>(value));

      case Expr::FunctionPointer:
        return eval_validate_literal(ctx, fx, type, expr_cast<FunctionPointerExpr>(value));

      case Expr::StringLiteral:
        return eval_validate_literal(ctx, fx, type, expr_cast<StringLiteralExpr>(value));

      case Expr::ArrayLiteral:
        return eval_validate_literal(ctx, fx, type, expr_cast<ArrayLiteralExpr>(value));

      case Expr::CompoundLiteral:
        return eval_validate_literal(ctx, fx, type, expr_cast<CompoundLiteralExpr>(value));

      default:
        assert(false);
    }

    throw logic_error("invalid literal expression");
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, VoidLiteralExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, BoolLiteralExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal->value());

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, CharLiteralExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal->value());

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, IntLiteralExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal->value());

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, FloatLiteralExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal->value());

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, PointerLiteralExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    store(ctx, fx.locals[dst].alloc, nullptr);

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, FunctionPointerExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    store(ctx, fx.locals[dst].alloc, literal);

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, StringLiteralExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, literal);

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, ArrayLiteralExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    auto j = ctx.arrayliterals.find(make_tuple(type, literal));

    if (j == ctx.arrayliterals.end())
    {
      auto storage = ctx.allocate(fx.locals[dst].size, alignof(void*));

      store(ctx, storage, fx.locals[dst].type, literal);

      j = ctx.arrayliterals.emplace(make_tuple(type, literal), storage).first;
    }

    fx.locals[dst].alloc = j->second;

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, CompoundLiteralExpr *literal)
  {
    auto type = fx.locals[dst].type;

    if (!eval_validate_literal(ctx, fx, type, literal))
      return false;

    auto j = ctx.compoundliterals.find(make_tuple(fx.locals[dst].type, literal));

    if (j == ctx.compoundliterals.end())
    {
      auto storage = ctx.allocate(fx.locals[dst].size, alignof(void*));

      store(ctx, storage, fx.locals[dst].type, literal);

      j = ctx.compoundliterals.emplace(make_tuple(fx.locals[dst].type, literal), storage).first;
    }

    fx.locals[dst].alloc = j->second;

    return true;
  }

  //|///////////////////// eval_assign_constant /////////////////////////////
  bool eval_assign_constant(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::ConstantData const &constant)
  {
    return std::visit([&](auto &v) { return eval_assign_constant(ctx, fx, dst, v); }, constant);
  }

  //|///////////////////// eval_assign_variable /////////////////////////////
  bool eval_assign_variable(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    auto rhs = fx.locals[arg].type;
    auto src = fx.locals[arg].alloc;

    for (auto &field : fields)
    {
      if (field.op == MIR::RValue::Val)
      {
        src = load_ptr(ctx, src);

        if (&field != &fields.front() || !(fx.locals[arg].flags & MIR::Local::Reference))
          rhs = remove_pointference_type(rhs);
      }

      switch (rhs = remove_const_type(rhs); rhs->klass())
      {
        case Type::Tag:
        case Type::Tuple:
          src = (void*)((size_t)src + offsetof_field(type_cast<CompoundType>(rhs), field.index));
          rhs = type_cast<CompoundType>(rhs)->fields[field.index];
          break;

        case Type::Array:
          src = (void*)((size_t)src + sizeof_type(type_cast<ArrayType>(rhs)->type) * field.index);
          rhs = type_cast<ArrayType>(rhs)->type;
          break;

        default:
          assert(false);
      }
    }

    switch (op)
    {
      case MIR::RValue::Ref:
        memcpy(fx.locals[dst].alloc, &src, fx.locals[dst].size);
        break;

      case MIR::RValue::Val:
        memcpy(fx.locals[dst].alloc, src, fx.locals[dst].size);
        break;

      case MIR::RValue::Fer:
        memcpy(fx.locals[dst].alloc, *(void**)src, fx.locals[dst].size);
        break;

      case MIR::RValue::Idx:
        assert(false);
        break;
    }

    return true;
  }

  //|///////////////////// unary_arithmetic /////////////////////////////////
  bool eval_builtin_unary_arithmetic(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhstype = fx.locals[args[0]].type;

    if (is_int(lhstype))
    {
      Numeric::Int result;

      auto lhs = load_int(ctx, fx, args[0]);

      switch (callee.fn->builtin)
      {
        case Builtin::Plus:
          result = lhs;
          break;

        case Builtin::Minus:
          result = -lhs;
          if (!is_signed_type(lhstype))
            result.maybe_unsigned = true;
          break;

        case Builtin::Not:
          result = ~lhs;
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

      if (!is_literal_valid(type_cast<BuiltinType>(fx.locals[dst].type)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *fx.locals[dst].type << "'\n";
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else if (is_float(lhstype))
    {
      Numeric::Float result;

      auto lhs = load_float(ctx, fx, args[0]);

      switch (callee.fn->builtin)
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

      if (!is_literal_valid(type_cast<BuiltinType>(fx.locals[dst].type)->kind(), result))
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
      ctx.diag << "  operand type: '" << *lhstype << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// unary_arithmetic_assign //////////////////////////
  bool eval_builtin_unary_arithmetic_assign(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto arg = load_ptr(ctx, fx, args[0]);
    auto lhstype = fx.locals[args[0]].type;

    if (is_int(lhstype))
    {
      Numeric::Int result;

      auto lhs = load_int(ctx, arg, lhstype);

      switch (callee.fn->builtin)
      {
        case Builtin::PreInc:
          result = lhs + Numeric::int_literal(+1, 1);
          break;

        case Builtin::PreDec:
          result = lhs - Numeric::int_literal(+1, 1);
          break;

        default:
          assert(false);
      }

      if (!is_literal_valid(type_cast<BuiltinType>(lhstype)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *lhstype << "'\n";
        return false;
      }

      store(ctx, arg, lhstype, result);
    }
    else if (is_float(lhstype))
    {
      Numeric::Float result;

      auto lhs = load_float(ctx, arg, lhstype);

      switch (callee.fn->builtin)
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

      if (!is_literal_valid(type_cast<BuiltinType>(lhstype)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *lhstype << "'\n";
        return false;
      }

      store(ctx, arg, lhstype, result);
    }
    else if (is_pointference_type(lhstype))
    {
      void *result;

      auto lhs = load_ptr(ctx, arg);

      switch (callee.fn->builtin)
      {
        case Builtin::PreInc:
          result = (void*)((size_t)lhs + sizeof_type(remove_pointference_type(lhstype)));
          break;

        case Builtin::PreDec:
          result = (void*)((size_t)lhs - sizeof_type(remove_pointference_type(lhstype)));
          break;

        default:
          assert(false);
      }

      store(ctx, arg, result);
    }
    else
    {
      ctx.diag.error("invalid unary arithmetic assign arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *lhstype << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, arg);

    return true;
  }

  //|///////////////////// binary_arithmetic ////////////////////////////////
  bool eval_builtin_binary_arithmetic(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhstype = fx.locals[args[0]].type;
    auto rhstype = fx.locals[args[1]].type;

    if (is_int(lhstype) && is_int(rhstype))
    {
      Numeric::Int result;

      auto lhs = load_int(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      switch (callee.fn->builtin)
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

          if (is_concrete_type(lhstype))
          {
            lhs.value &= (0xffffffffffffffff >> (64 - 8*sizeof_type(lhstype) + rhs.value));
          }

          result = lhs << rhs;
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

      if (!is_literal_valid(type_cast<BuiltinType>(fx.locals[dst].type)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *fx.locals[dst].type << "'\n";
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else if (is_float(lhstype) && is_float(rhstype))
    {
      Numeric::Float result;

      auto lhs = load_float(ctx, fx, args[0]);
      auto rhs = load_float(ctx, fx, args[1]);

      switch (callee.fn->builtin)
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

      if (!is_literal_valid(type_cast<BuiltinType>(fx.locals[dst].type)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *fx.locals[dst].type << "'\n";
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);
    }
    else if (is_pointference_type(lhstype) && is_int_type(rhstype))
    {
      void *result;

      auto lhs = load_ptr(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      auto size = sizeof_type(remove_pointference_type(lhstype));

      if (size == 0)
      {
        ctx.diag.error("zero sized type", fx.scope, loc);
        return false;
      }

      switch (callee.fn->builtin)
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

      store(ctx, fx.locals[dst].alloc, result);
    }
    else if (is_pointference_type(lhstype) && is_pointference_type(rhstype))
    {
      void *result;

      auto lhs = load_ptr(ctx, fx, args[0]);
      auto rhs = load_ptr(ctx, fx, args[1]);

      switch (callee.fn->builtin)
      {
        case Builtin::min:
          result = rhs < lhs ? rhs : lhs;
          break;

        case Builtin::max:
          result = lhs < rhs ? rhs : lhs;
          break;

        default:
          assert(false);
      }

      store(ctx, fx.locals[dst].alloc, result);
    }
    else
    {
      ctx.diag.error("invalid binary arithmetic arguments", fx.scope, loc);
      ctx.diag << "  lhs type: '" << *lhstype << "' rhs type: '" << *rhstype << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// pointer_difference ///////////////////////////////
  bool eval_builtin_pointer_difference(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);
    auto rhs = load_ptr(ctx, fx, args[1]);

    auto size = sizeof_type(remove_pointer_type(fx.locals[args[0]].type));

    if (size == 0)
    {
      ctx.diag.error("zero sized type", fx.scope, loc);
      return false;
    }

    if ((size_t)lhs < (size_t)rhs)
    {
      ctx.diag.error("pointer difference overflow", fx.scope, loc);
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(+1, ((size_t)lhs - (size_t)(rhs)) / size));

    return true;
  }

  //|///////////////////// binary_arithmetic_carry //////////////////////////
  bool eval_builtin_binary_arithmetic_carry(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhstype = fx.locals[args[0]].type;
    auto rhstype = fx.locals[args[1]].type;

    if (is_int(lhstype) && is_int(rhstype))
    {
      Numeric::Int result, carry;

      auto lhs = load_int(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      auto width = 8*sizeof_type(lhstype);
      auto is_signed = is_signed_type(lhstype);

      switch (callee.fn->builtin)
      {
        case Builtin::AddCarry:
          add_with_carry(lhs, rhs, width, is_signed, result, carry);
          break;

        case Builtin::SubBorrow:
          sub_with_borrow(lhs, rhs, width, is_signed, result, carry);
          break;

        case Builtin::MulCarry:
          mul_with_carry(lhs, rhs, width, is_signed, result, carry);
          break;

        default:
          assert(false);
      }

      auto tupletype = type_cast<TupleType>(fx.locals[dst].type);

      store(ctx, fx.locals[dst].alloc, tupletype->fields[0], result);
      store(ctx, (void*)((size_t)fx.locals[dst].alloc + offsetof_field(tupletype, 1)), tupletype->fields[1], carry);
    }
    else
    {
      ctx.diag.error("invalid binary arithmetic arguments", fx.scope, loc);
      ctx.diag << "  lhs type: '" << *lhstype << "' rhs type: '" << *rhstype << "'\n";
    }

    return true;
  }

  //|///////////////////// binary_arithmetic_assign /////////////////////////
  bool eval_builtin_binary_arithmetic_assign(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto arg = load_ptr(ctx, fx, args[0]);
    auto lhstype = fx.locals[args[0]].type;
    auto rhstype = fx.locals[args[1]].type;

    if (is_int(lhstype) && is_int(rhstype))
    {
      Numeric::Int result;

      auto lhs = load_int(ctx, arg, lhstype);
      auto rhs = load_int(ctx, fx, args[1]);

      switch (callee.fn->builtin)
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

          if (is_concrete_type(lhstype))
          {
            lhs.value &= (0xffffffffffffffff >> (64 - 8*sizeof_type(lhstype) + rhs.value));
          }

          result = lhs << rhs;
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

      if (!is_literal_valid(type_cast<BuiltinType>(lhstype)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *lhstype << "'\n";
        return false;
      }

      store(ctx, arg, lhstype, result);
    }
    else if (is_float(lhstype) && is_float(rhstype))
    {
      Numeric::Float result;

      auto lhs = load_float(ctx, arg, lhstype);
      auto rhs = load_float(ctx, fx, args[1]);

      switch (callee.fn->builtin)
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

      if (!is_literal_valid(type_cast<BuiltinType>(lhstype)->kind(), result))
      {
        ctx.diag.error("literal value out of range for required type", fx.scope, loc);
        ctx.diag << "  literal value: '" << result << "' required type: '" << *lhstype << "'\n";
        return false;
      }

      store(ctx, arg, lhstype, result);
    }
    else if (is_pointference_type(lhstype) && is_int_type(rhstype))
    {
      void *result;

      auto lhs = load_ptr(ctx, arg);
      auto rhs = load_int(ctx, fx, args[1]);

      auto size = sizeof_type(remove_pointference_type(lhstype));

      if (size == 0)
      {
        ctx.diag.error("zero sized type", fx.scope, loc);
        return false;
      }

      switch (callee.fn->builtin)
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

      store(ctx, arg, result);
    }
    else
    {
      ctx.diag.error("invalid binary arithmetic assign arguments", fx.scope, loc);
      ctx.diag << "  lhs type: '" << *lhstype << "' rhs type: '" << *rhstype << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, arg);

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

    auto lhstype = fx.locals[args[0]].type;
    auto rhstype = fx.locals[args[1]].type;

    if (is_int(lhstype) && is_int(rhstype))
    {
      bool result;

      auto lhs = load_int(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      switch (callee.fn->builtin)
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
    else if (is_float(lhstype) && is_float(rhstype))
    {
      bool result;

      auto lhs = load_float(ctx, fx, args[0]);
      auto rhs = load_float(ctx, fx, args[1]);

      switch (callee.fn->builtin)
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
    else if (is_void_type(lhstype) && is_void_type(rhstype))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, callee.fn->builtin == Builtin::EQ);
    }
    else if (is_null_type(lhstype) && is_null_type(rhstype))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, callee.fn->builtin == Builtin::EQ);
    }
    else if (is_string_type(lhstype) && is_string_type(rhstype))
    {
      bool result;

      auto lhs = load_string(ctx, fx, args[0]);
      auto rhs = load_string(ctx, fx, args[1]);

      switch (callee.fn->builtin)
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
    else if (is_pointference_type(lhstype) && is_pointference_type(rhstype))
    {
      bool result;

      auto lhs = load_ptr(ctx, fx, args[0]);
      auto rhs = load_ptr(ctx, fx, args[1]);

      switch (callee.fn->builtin)
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
      ctx.diag << "  lhs type: '" << *lhstype << "' rhs type: '" << *rhstype << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// cmp //////////////////////////////////////////////
  bool eval_builtin_cmp(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhstype = fx.locals[args[0]].type;
    auto rhstype = fx.locals[args[1]].type;

    int result = 0;

    if (is_int(lhstype) && is_int(rhstype))
    {
      auto lhs = load_int(ctx, fx, args[0]);
      auto rhs = load_int(ctx, fx, args[1]);

      result = (lhs == rhs) ? 0 : (lhs < rhs) ? -1 : +1;
    }
    else if (is_float(lhstype) && is_float(rhstype))
    {
      auto lhs = load_float(ctx, fx, args[0]);
      auto rhs = load_float(ctx, fx, args[1]);

      result = (lhs == rhs) ? 0 : (lhs < rhs) ? -1 : +1;
    }
    else if (is_string_type(lhstype) && is_string_type(rhstype))
    {
      auto lhs = load_string(ctx, fx, args[0]);
      auto rhs = load_string(ctx, fx, args[1]);

      result = (lhs == rhs) ? 0 : (lhs < rhs) ? -1 : +1;
    }
    else if (is_pointference_type(lhstype) && is_pointference_type(rhstype))
    {
      auto lhs = load_ptr(ctx, fx, args[0]);
      auto rhs = load_ptr(ctx, fx, args[1]);

      result = (lhs == rhs) ? 0 : (lhs < rhs) ? -1 : +1;
    }
    else
    {
      ctx.diag.error("invalid compare arguments", fx.scope, loc);
      ctx.diag << "  lhs type: '" << *lhstype << "' rhs type: '" << *rhstype << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(result));

    return true;
  }

  //|///////////////////// deref ////////////////////////////////////////////
  bool eval_builtin_deref(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);

    if (lhs == nullptr)
    {
      ctx.diag.error("null pointer dereference", fx.scope, loc);
      return false;
    }

    store(ctx, fx.locals[dst].alloc, lhs);

    return true;
  }

  //|///////////////////// range ////////////////////////////////////////////
  bool eval_builtin_range(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto tupletype = type_cast<TupleType>(fx.locals[dst].type);

    memcpy(fx.locals[dst].alloc, fx.locals[args[0]].alloc, fx.locals[args[0]].size);
    memcpy((void*)((size_t)fx.locals[dst].alloc + offsetof_field(tupletype, 1)), fx.locals[args[1]].alloc, fx.locals[args[1]].size);

    return true;
  }

  //|///////////////////// assign ///////////////////////////////////////////
  bool eval_builtin_assign(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);

    memcpy(lhs, fx.locals[args[1]].alloc, fx.locals[args[1]].size);

    store(ctx, fx.locals[dst].alloc, lhs);

    return true;
  }

  //|///////////////////// slice_len ////////////////////////////////////////
  bool eval_builtin_slice_len(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_slice<void>(ctx, fx, args[0]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(+1, lhs.len));

    return true;
  }

  //|///////////////////// slice_data ///////////////////////////////////////
  bool eval_builtin_slice_data(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_slice<void>(ctx, fx, args[0]);

    store(ctx, fx.locals[dst].alloc, lhs.data);

    return true;
  }

  //|///////////////////// slice_end ////////////////////////////////////////
  bool eval_builtin_slice_end(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_slice<void>(ctx, fx, args[0]);
    auto elemsize = sizeof_type(remove_const_type(remove_pointer_type((fx.locals[dst].type))));

    store(ctx, fx.locals[dst].alloc, (void*)((size_t)lhs.data + lhs.len * elemsize));

    return true;
  }

  //|///////////////////// slice_index //////////////////////////////////////
  bool eval_builtin_slice_index(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_slice<void>(ctx, fx, args[0]);
    auto elemsize = sizeof_type(remove_const_type(remove_pointer_type((fx.locals[dst].type))));

    if (is_int_type(fx.locals[args[1]].type))
    {
      auto rhs = load_int(ctx, fx, args[1]);

      if (rhs.value >= lhs.len)
      {
        ctx.diag.error("slice subscript overflow", fx.scope, loc);
        return false;
      }

      store(ctx, fx.locals[dst].alloc, (void*)((size_t)lhs.data + rhs.value * elemsize));
    }

    if (is_pointer_type(fx.locals[args[1]].type))
    {
      auto rhs = load_ptr(ctx, fx, args[1]);

      if (rhs < lhs.data || (void*)((size_t)lhs.data + lhs.len * elemsize) <= rhs)
      {
        ctx.diag.error("slice subscript overflow", fx.scope, loc);
        return false;
      }

      store(ctx, fx.locals[dst].alloc, rhs);
    }

    return true;
  }

  //|///////////////////// slice_slice //////////////////////////////////////
  bool eval_builtin_slice_slice(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto src = load_slice<void>(ctx, fx, args[0]);
    auto range = load_range<uint64_t>(ctx, fx, args[1]);

    if (src.len < range.beg)
    {
      ctx.diag.error("string slice begin overflow", fx.scope, loc);
      return false;
    }

    if (type_cast<TupleType>(fx.locals[args[1]].type)->fields.size() == 3)
      range.end += 1;

    if (range.end < range.beg || src.len < range.end)
    {
      ctx.diag.error("string slice end overflow", fx.scope, loc);
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Slice<void>{ range.end - range.beg, (void*)((size_t)src.data + range.beg) });

    return true;
  }

  //|///////////////////// string_append ////////////////////////////////////
  bool eval_builtin_string_append(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_string(ctx, fx, args[0]);
    auto rhs = load_string(ctx, fx, args[1]);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<StringLiteralExpr>(string(lhs) + string(rhs), loc));

    auto data = ctx.allocate(lhs.size() + rhs.size(), alignof(uintptr_t));

    memcpy(data, lhs.data(), lhs.size());
    memcpy((void*)((size_t)data + lhs.size()), rhs.data(), rhs.size());

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Slice<void>{ lhs.size() + rhs.size(), data });

    return true;
  }

  //|///////////////////// string_create ////////////////////////////////////
  bool eval_builtin_string_create(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto ptr = load_ptr(ctx, fx, args[0]);
    auto length = load_int(ctx, fx, args[1]);

    auto data = ctx.allocate(length.value, alignof(uintptr_t));

    memcpy(data, ptr, length.value);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Slice<void>{ length.value, data });

    return true;
  }

  //|///////////////////// array_data ///////////////////////////////////////
  bool eval_builtin_array_data(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);

    store(ctx, fx.locals[dst].alloc, lhs);

    return true;
  }

  //|///////////////////// array_index //////////////////////////////////////
  bool eval_builtin_array_index(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);
    auto arraytype = type_cast<ArrayType>(remove_const_type(remove_pointer_type(fx.locals[args[0]].type)));

    if (is_int_type(fx.locals[args[1]].type))
    {
      auto rhs = load_int(ctx, fx, args[1]);

      if (rhs.value >= array_len(arraytype))
      {
        ctx.diag.error("array subscript overflow", fx.scope, loc);
        return false;
      }

      store(ctx, fx.locals[dst].alloc, (void*)((size_t)lhs + rhs.value * sizeof_type(arraytype->type)));
    }

    if (is_pointer_type(fx.locals[args[1]].type))
    {
      auto rhs = load_ptr(ctx, fx, args[1]);

      if (rhs < lhs || (void*)((size_t)lhs + array_len(arraytype) * sizeof_type(arraytype->type)) <= rhs)
      {
        ctx.diag.error("array subscript overflow", fx.scope, loc);
        return false;
      }

      store(ctx, fx.locals[dst].alloc, rhs);
    }

    return true;
  }

  //|///////////////////// array_end ////////////////////////////////////////
  bool eval_builtin_array_end(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_ptr(ctx, fx, args[0]);
    auto arraytype = type_cast<ArrayType>(remove_const_type(remove_pointer_type(fx.locals[args[0]].type)));

    store(ctx, fx.locals[dst].alloc, (void*)((size_t)lhs + array_len(arraytype) * sizeof_type(arraytype->type)));

    return true;
  }

  //|///////////////////// array_create /////////////////////////////////////
  bool eval_builtin_array_create(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto ptr = load_ptr(ctx, fx, args[0]);
    auto length = load_int(ctx, fx, args[1]);
    auto elemsize = sizeof_type(remove_pointer_type(fx.locals[args[0]].type));

    auto data = ctx.allocate(length.value * elemsize, alignof(uintptr_t));

    memcpy(data, ptr, length.value * elemsize);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Slice<void>{ length.value, data });

    return true;
  }

  //|///////////////////// match_range //////////////////////////////////////
  bool eval_builtin_match_range(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto type = callee.find_type(callee.fn->args[0])->second;

    if (is_int_type(type) || is_char_type(type) || is_enum_type(type))
    {
      auto beg = load_int(ctx, (void*)((size_t)fx.locals[args[0]].alloc + offsetof_field(type_cast<TupleType>(fx.locals[args[0]].type), 0)), type);
      auto end = load_int(ctx, (void*)((size_t)fx.locals[args[0]].alloc + offsetof_field(type_cast<TupleType>(fx.locals[args[0]].type), 1)), type);
      auto value = load_int(ctx, fx, args[1]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, beg <= value && value < end);
    }
    else if (is_float_type(type))
    {
      auto beg = load_float(ctx, (void*)((size_t)fx.locals[args[0]].alloc + offsetof_field(type_cast<TupleType>(fx.locals[args[0]].type), 0)), type);
      auto end = load_float(ctx, (void*)((size_t)fx.locals[args[0]].alloc + offsetof_field(type_cast<TupleType>(fx.locals[args[0]].type), 1)), type);
      auto value = load_float(ctx, fx, args[1]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, beg <= value && value < end);
    }
    else
    {
      ctx.diag.error("invalid match arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// match_range_eq ///////////////////////////////////
  bool eval_builtin_match_range_eq(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto type = callee.find_type(callee.fn->args[0])->second;

    if (is_int_type(type) || is_char_type(type) || is_enum_type(type))
    {
      auto beg = load_int(ctx, (void*)((size_t)fx.locals[args[0]].alloc + offsetof_field(type_cast<TupleType>(fx.locals[args[0]].type), 0)), type);
      auto end = load_int(ctx, (void*)((size_t)fx.locals[args[0]].alloc + offsetof_field(type_cast<TupleType>(fx.locals[args[0]].type), 1)), type);
      auto value = load_int(ctx, fx, args[1]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, beg <= value && value <= end);
    }
    else if (is_float_type(type))
    {
      auto beg = load_float(ctx, (void*)((size_t)fx.locals[args[0]].alloc + offsetof_field(type_cast<TupleType>(fx.locals[args[0]].type), 0)), type);
      auto end = load_float(ctx, (void*)((size_t)fx.locals[args[0]].alloc + offsetof_field(type_cast<TupleType>(fx.locals[args[0]].type), 1)), type);
      auto value = load_float(ctx, fx, args[1]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, beg <= value && value <= end);
    }
    else
    {
      ctx.diag.error("invalid match arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// callop ///////////////////////////////////////////
  bool eval_builtin_callop(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &callop)
  {
    auto &[callee, args, loc] = callop;

    auto fn = load_ptr(ctx, fx, args[0]);
    auto rhs = load_ptr(ctx, fx, args[1]);

    if (!fn)
    {
      ctx.diag.error("null funciton pointer dereference", fx.scope, loc);
      return false;
    }

    auto &mir = lower(static_cast<FunctionPointerExpr*>(fn)->value(), ctx.typetable, ctx.diag);

    if (ctx.diag.has_errored())
      return false;

    auto stackframe = ctx.push<FunctionContext::Local>(mir.locals.size());

    stackframe[0] = fx.locals[dst];

    if (callee.throwtype)
    {
      stackframe[1] = fx.locals[fx.errorarg];
    }

    auto paramtuple = type_cast<TupleType>(remove_const_type(remove_pointer_type(fx.locals[args[1]].type)));

    for (size_t i = 0; i < paramtuple->fields.size(); ++i)
    {
      auto argtype = remove_const_type(remove_reference_type(paramtuple->fields[i]));

      auto ptr = load_ptr(ctx, (void*)((size_t)rhs + offsetof_field(paramtuple, i)));

      stackframe[mir.args_beg + i] = { 0, argtype, sizeof_type(argtype), ptr };
    }

    return eval_function(ctx, mir.fx.fn, mir, stackframe);
  }

  //|///////////////////// bool /////////////////////////////////////////////
  bool eval_builtin_bool(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhstype = fx.locals[args[0]].type;

    if (is_int_type(lhstype))
    {
      auto lhs = load_int(ctx, fx, args[0]);

      if (lhs.sign < 0 || lhs.value > 1)
      {
        ctx.diag.error("bool implicit cast must be 0 or 1", fx.scope, loc);
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs.value != 0);
    }
    else if (is_pointference_type(lhstype))
    {
      auto lhs = load_ptr(ctx, fx, args[0]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs != nullptr);
    }
    else if (is_null_type(lhstype))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, false);
    }
    else if (is_declid_type(lhstype))
    {
      auto lhs = load_int(ctx, fx, args[0]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs.value != 0);
    }
    else if (is_typeid_type(lhstype))
    {
      auto lhs = load_int(ctx, fx, args[0]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs.value != 0);
    }
    else
    {
      ctx.diag.error("invalid bool arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *lhstype << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// classify /////////////////////////////////////////
  bool eval_builtin_classify(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    bool result;

    if (is_int(fx.locals[args[0]].type))
    {
      switch (callee.fn->builtin)
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

      switch (callee.fn->builtin)
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

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(+1, result));

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

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(+1, result));

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
      lhs.value &= (0xffffffffffffffff >> (64 - 8*sizeof_type(fx.locals[args[0]].type)));
    }

    while (lhs.value != 0)
    {
      if ((lhs.value & 0x1) == 1)
        result += 1;

      lhs.value >>= 1;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(+1, result));

    return true;
  }

  //|///////////////////// signbit //////////////////////////////////////////
  bool eval_builtin_signbit(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_int(fx.locals[args[0]].type))
    {
      auto lhs = load_int(ctx, fx, args[0]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(+1, lhs.sign < 0 ? 1 : 0));
    }
    else if (is_float(fx.locals[args[0]].type))
    {
      auto lhs = load_float(ctx, fx, args[0]);

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(+1, lhs.value < 0 ? 1 : 0));
    }
    else
    {
      ctx.diag.error("invalid signbit arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// byteswap /////////////////////////////////////////
  bool eval_builtin_byteswap(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_int(ctx, fx, args[0]);
    auto width = 8*sizeof_type(fx.locals[args[0]].type);

    auto result = Numeric::int_literal(+1, 0);

    for (size_t i = 0; i < width; i += 8)
      result.value |= ((lhs.value >> i) & 0xff) << (width - 8 - i);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);

    return true;
  }

  //|///////////////////// bitreverse ///////////////////////////////////////
  bool eval_builtin_bitreverse(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load_int(ctx, fx, args[0]);
    auto width = 8*sizeof_type(fx.locals[args[0]].type);

    auto result = Numeric::int_literal(+1, 0);

    for (size_t i = 0; i < width; i += 1)
      result.value |= ((lhs.value >> i) & 0x1) << (width - 1 - i);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);

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
      store(ctx, (void*)((size_t)fx.locals[dst].alloc + offsetof_field(tupletype, 1)), tupletype->fields[1], Numeric::int_literal(exponent));
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

    store(ctx, fx.locals[dst].alloc, dest);

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

    store(ctx, fx.locals[dst].alloc, dest);

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

    store(ctx, fx.locals[dst].alloc, dest);

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
      result = Numeric::int_literal(+1, (size_t)ptr - (size_t)source);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);

    return true;
  }

  //|///////////////////// alloca ///////////////////////////////////////////
  bool eval_builtin_alloca(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto size = load_int(ctx, fx, args[0]);
    auto align = expr_cast<IntLiteralExpr>(type_cast<TypeLitType>(callee.find_type(callee.fn->parms[1])->second)->value);

    auto result = ctx.allocate(size.value, align->value().value);

    store(ctx, fx.locals[dst].alloc, result);

    return true;
  }

  //|///////////////////// atomic_load //////////////////////////////////////
  bool eval_builtin_atomic_load(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto src = load_ptr(ctx, fx, args[0]);

    memcpy(fx.locals[dst].alloc, src, fx.locals[dst].size);

    return true;
  }

  //|///////////////////// atomic_store /////////////////////////////////////
  bool eval_builtin_atomic_store(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto ptr = load_ptr(ctx, fx, args[0]);

    memcpy(ptr, fx.locals[args[1]].alloc, fx.locals[args[1]].size);

    return true;
  }

  //|///////////////////// atomic_arithmatic ////////////////////////////////
  bool eval_builtin_atomic_arithmatic(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (is_int(fx.locals[args[1]].type))
    {
      Numeric::Int result;

      auto ptr = load_ptr(ctx, fx, args[0]);
      auto lhs = load_int(ctx, ptr, fx.locals[args[1]].type);
      auto rhs = load_int(ctx, fx, args[1]);

      switch (callee.fn->builtin)
      {
        case Builtin::atomic_xchg:
          result = rhs;
          break;

        case Builtin::atomic_fetch_add:
          result = lhs + rhs;
          break;

        case Builtin::atomic_fetch_sub:
          result = lhs - rhs;
          break;

        case Builtin::atomic_fetch_and:
          result = lhs & rhs;
          break;

        case Builtin::atomic_fetch_xor:
          result = lhs ^ rhs;
          break;

        case Builtin::atomic_fetch_or:
          result = lhs | rhs;
          break;

        case Builtin::atomic_fetch_nand:
          result = ~(lhs & rhs);
          break;

        default:
          assert(false);
      }

      store(ctx, ptr, fx.locals[dst].type, result);
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, lhs);
    }
    else if (is_pointer_type(fx.locals[args[1]].type))
    {
      void *result;

      auto ptr = load_ptr(ctx, fx, args[0]);
      auto lhs = load_ptr(ctx, ptr);
      auto rhs = load_ptr(ctx, fx, args[1]);

      switch (callee.fn->builtin)
      {
        case Builtin::atomic_xchg:
          result = rhs;
          break;

        case Builtin::atomic_fetch_add:
          result = (void*)((uintptr_t)lhs + (uintptr_t)rhs);
          break;

        case Builtin::atomic_fetch_sub:
          result = (void*)((uintptr_t)lhs - (uintptr_t)rhs);
          break;

        case Builtin::atomic_fetch_and:
          result = (void*)((uintptr_t)lhs & (uintptr_t)rhs);
          break;

        case Builtin::atomic_fetch_xor:
          result = (void*)((uintptr_t)lhs ^ (uintptr_t)rhs);
          break;

        case Builtin::atomic_fetch_or:
          result = (void*)((uintptr_t)lhs | (uintptr_t)rhs);
          break;

        case Builtin::atomic_fetch_nand:
          result = (void*)(~((uintptr_t)lhs & (uintptr_t)rhs));
          break;

        default:
          assert(false);
      }

      store(ctx, ptr, result);
      store(ctx, fx.locals[dst].alloc, lhs);
    }
    else
    {
      ctx.diag.error("invalid atomic arithmetic arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    return true;
  }

  //|///////////////////// atomic_cmpxchg ///////////////////////////////////
  bool eval_builtin_atomic_cmpxchg(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    bool result = false;

    if (is_int(fx.locals[args[1]].type))
    {
      auto ptr = load_ptr(ctx, fx, args[0]);
      auto lhs = load_int(ctx, ptr, fx.locals[args[1]].type);
      auto rhs = load_int(ctx, fx, args[1]);

      if (lhs == rhs)
      {
        store(ctx, ptr, fx.locals[args[1]].type, load_int(ctx, fx, args[2]));
        result = true;
      }
    }
    else if (is_pointer_type(fx.locals[args[1]].type))
    {
      auto ptr = load_ptr(ctx, fx, args[0]);
      auto lhs = load_ptr(ctx, ptr);
      auto rhs = load_ptr(ctx, fx, args[1]);

      if (lhs == rhs)
      {
        store(ctx, ptr, load_ptr(ctx, fx, args[2]));
        result = true;
      }
    }
    else
    {
      ctx.diag.error("invalid atomic cmpxchg arguments", fx.scope, loc);
      ctx.diag << "  operand type: '" << *fx.locals[args[0]].type << "'\n";
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, result);

    return true;
  }

  //|///////////////////// decl_kind ////////////////////////////////////////
  bool eval_builtin_decl_kind(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto declid = reinterpret_cast<Decl*>(load_int(ctx, fx, args[0]).value);

    if (!declid)
    {
      ctx.diag.error("invalid declid for decl_kind", fx.scope, loc);
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<IntLiteralExpr>(Numeric::int_literal(declid->kind()), loc));

    return true;
  }

  //|///////////////////// decl_name ////////////////////////////////////////
  bool eval_builtin_decl_name(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto declid = reinterpret_cast<Decl*>(load_int(ctx, fx, args[0]).value);

    if (!declid)
    {
      ctx.diag.error("invalid declid for decl_name", fx.scope, loc);
      return false;
    }

    Ident *result = nullptr;

    switch (declid->kind())
    {
      case Decl::TranslationUnit:
        result = Ident::op_scope;
        break;

      case Decl::Module:
        result = decl_cast<ModuleDecl>(declid)->name;
        break;

      case Decl::Function:
        result = decl_cast<FunctionDecl>(declid)->name;
        break;

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Concept:
      case Decl::Enum:
        result = decl_cast<TagDecl>(declid)->name;
        break;

      case Decl::VoidVar:
      case Decl::StmtVar:
      case Decl::ParmVar:
      case Decl::FieldVar:
      case Decl::ThisVar:
      case Decl::ErrorVar:
        result = decl_cast<VarDecl>(declid)->name;
        break;

      case Decl::EnumConstant:
        result = decl_cast<EnumConstantDecl>(declid)->name;
        break;

      case Decl::TypeAlias:
        result = decl_cast<TypeAliasDecl>(declid)->name;
        break;

      case Decl::TypeArg:
        result = decl_cast<TypeArgDecl>(declid)->name;
        break;

      case Decl::Import:
        result = Ident::kw_import;
        break;

      case Decl::Using:
        result = Ident::kw_using;
        break;

      case Decl::Run:
        result = Ident::op_run;
        break;

      default:
        break;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<StringLiteralExpr>(result ? result->str() : string(), loc));

    return true;
  }

  //|///////////////////// decl_flags ///////////////////////////////////////
  bool eval_builtin_decl_flags(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto declid = reinterpret_cast<Decl*>(load_int(ctx, fx, args[0]).value);

    if (!declid)
    {
      ctx.diag.error("invalid declid for decl_flags", fx.scope, loc);
      return false;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<IntLiteralExpr>(Numeric::int_literal(declid->flags), loc));

    return true;
  }

  //|///////////////////// decl_parent //////////////////////////////////////
  bool eval_builtin_decl_parent(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto declid = reinterpret_cast<Decl*>(load_int(ctx, fx, args[0]).value);

    if (!declid)
    {
      ctx.diag.error("invalid declid for decl_parent", fx.scope, loc);
      return false;
    }

    Decl *result = nullptr;

    for (auto sx = parent_scope(declid); sx; sx = parent_scope(std::move(sx)))
    {
      if (is_decl_scope(sx))
      {
        result = get<Decl*>(sx.owner);
        break;
      }
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<IntLiteralExpr>(Numeric::int_literal(+1, reinterpret_cast<uintptr_t>(result)), loc));

    return true;
  }

  //|///////////////////// decl_children ////////////////////////////////////
  bool eval_builtin_decl_children(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto declid = reinterpret_cast<Decl*>(load_int(ctx, fx, args[0]).value);
    auto filter = load_int(ctx, fx, args[1]).value;

    if (!declid)
    {
      ctx.diag.error("invalid declid for decl_children", fx.scope, loc);
      return false;
    }

    vector<Decl*> results;

    switch (declid->kind())
    {
      case Decl::TranslationUnit:
        results = decl_cast<TranslationUnitDecl>(declid)->decls;
        break;

      case Decl::Module:
        results = decl_cast<ModuleDecl>(declid)->decls;
        break;

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Concept:
      case Decl::Enum:
        results = decl_cast<TagDecl>(declid)->decls;
        break;

      default:
        break;
    }

    size_t size = 0;
    Numeric::Int *data = (Numeric::Int*)ctx.allocate(results.size() * sizeof(Numeric::Int), alignof(uintptr_t));

    for (size_t i = 0; i < results.size(); ++i)
    {
      if (filter == 0 || filter == results[i]->kind())
        data[size++] = Numeric::int_literal(+1, reinterpret_cast<uintptr_t>(results[i]));
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Slice<Numeric::Int>{ size, data });

    return true;
  }

  //|///////////////////// decl_site ////////////////////////////////////////
  bool eval_builtin_decl_site(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto declid = reinterpret_cast<Decl*>(load_int(ctx, fx, args[0]).value);

    if (!declid)
    {
      ctx.diag.error("invalid declid for decl_site", fx.scope, loc);
      return false;
    }

    vector<Expr*> fields;

    fields.push_back(ctx.make_expr<StringLiteralExpr>(get_module(declid)->file(), loc));
    fields.push_back(ctx.make_expr<IntLiteralExpr>(Numeric::int_literal(declid->loc().lineno), loc));
    fields.push_back(ctx.make_expr<IntLiteralExpr>(Numeric::int_literal(declid->loc().charpos), loc));
    fields.push_back(ctx.make_expr<StringLiteralExpr>("", loc));

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<CompoundLiteralExpr>(fields, loc));

    return true;
  }

  //|///////////////////// decl_attr ////////////////////////////////////////
  bool eval_builtin_decl_attr(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto declid = reinterpret_cast<Decl*>(load_int(ctx, fx, args[0]).value);

    if (!declid)
    {
      ctx.diag.error("invalid declid for decl_attr", fx.scope, loc);
      return false;
    }

    Decl *result = nullptr;
    vector<Decl*> attributes;

    switch (declid->kind())
    {
      case Decl::Function:
        attributes = decl_cast<FunctionDecl>(declid)->attributes;
        break;

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Concept:
      case Decl::Enum:
        attributes = decl_cast<TagDecl>(declid)->attributes;
        break;

      case Decl::FieldVar:
        attributes = decl_cast<FieldVarDecl>(declid)->attributes;
        break;

      default:
        break;
    }

    auto name = load_string(ctx, fx, args[1]);

    for (auto attr : attributes)
    {
      auto attribute = decl_cast<AttributeDecl>(attr);

      if (attribute->name == name)
        result = attribute;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<IntLiteralExpr>(Numeric::int_literal(+1, reinterpret_cast<uintptr_t>(result)), loc));

    return true;
  }

  //|///////////////////// attr_text ////////////////////////////////////////
  bool eval_builtin_attr_text(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto declid = reinterpret_cast<Decl*>(load_int(ctx, fx, args[0]).value);

    if (!declid || declid->kind() != Decl::Attribute)
    {
      ctx.diag.error("invalid declid for decl_attr", fx.scope, loc);
      return false;
    }

    auto attribute = decl_cast<AttributeDecl>(declid);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<StringLiteralExpr>(attribute->options, loc));

    return true;
  }

  //|///////////////////// type_decl ////////////////////////////////////////
  bool eval_builtin_type_decl(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto typid = reinterpret_cast<Type*>(load_int(ctx, fx, args[0]).value);

    if (!typid)
    {
      ctx.diag.error("invalid typeid for type_decl", fx.scope, loc);
      return false;
    }

    Decl *result = nullptr;

    switch (typid->klass())
    {
      case Type::Tag:
        result = type_cast<TagType>(typid)->decl;
        break;

      default:
        break;
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<IntLiteralExpr>(Numeric::int_literal(+1, reinterpret_cast<uintptr_t>(result)), loc));

    return true;
  }

  //|///////////////////// type_name ////////////////////////////////////////
  bool eval_builtin_type_name(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto typid = reinterpret_cast<Type*>(load_int(ctx, fx, args[0]).value);

    if (!typid)
    {
      ctx.diag.error("invalid typeid for type_children", fx.scope, loc);
      return false;
    }

    std::stringstream ss;

    ss << *typid;

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<StringLiteralExpr>(ss.str(), loc));

    return true;
  }

  //|///////////////////// type_children ////////////////////////////////////
  bool eval_builtin_type_children(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto typid = reinterpret_cast<Type*>(load_int(ctx, fx, args[0]).value);
    auto filter = load_int(ctx, fx, args[1]).value;

    if (!typid)
    {
      ctx.diag.error("invalid typeid for type_children", fx.scope, loc);
      return false;
    }

    size_t size = 0;
    Numeric::Int *data = nullptr;

    if (auto type = remove_const_type(remove_reference_type(typid)); is_tag_type(type))
    {
      auto tagtype = type_cast<TagType>(type);

      data = (Numeric::Int*)ctx.allocate(tagtype->decls.size() * sizeof(Numeric::Int), alignof(uintptr_t));

      for (size_t i = 0; i < tagtype->decls.size(); ++i)
      {
        if (filter == 0 || filter == tagtype->decls[i]->kind())
          data[size++] = Numeric::int_literal(+1, reinterpret_cast<uintptr_t>(tagtype->decls[i]));
      }
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Slice<Numeric::Int>{ size, data });

    return true;
  }

  //|///////////////////// type_query ///////////////////////////////////////
  bool eval_builtin_type_query(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto params = static_cast<char*>(load_ptr(ctx, fx, args[1]));

    Type *result = nullptr;

    switch (load_int(ctx, fx, args[0]).value)
    {
      case 0x01: // is_enum
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          if (is_enum_type(typid))
            result = typid;
        break;

      case 0x02: // is_array
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          if (is_array_type(typid))
            result = typid;
        break;

      case 0x03: // is_tuple
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          if (is_tuple_type(typid))
            result = typid;
        break;

      case 0x04: // is_union
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          if (is_union_type(typid))
            result = typid;
        break;

      case 0x05: // is_struct
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          if (is_struct_type(typid))
            result = typid;
        break;

      case 0x016: // is_vtable
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          if (is_vtable_type(typid))
            result = typid;
        break;

      case 0x07: // is_builtin
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          if (is_builtin_type(typid))
            result = typid;
        break;

      case 0xcd: // add_const
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          result = ctx.typetable.find_or_create<ConstType>(typid);
        break;

      case 0x95: // remove_const
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          result = remove_const_type(typid);
        break;

      case 0xfa: // add_pointer
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          result = ctx.typetable.find_or_create<PointerType>(typid);
        break;

      case 0x73: // remove_pointer
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          result = is_pointference_type(remove_const_type(typid)) ? remove_pointference_type(remove_const_type(typid)) : typid;
        break;

      case 0xeb: // add_reference
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          result = ctx.typetable.find_or_create<ReferenceType>(typid);
        break;

      case 0xfc: // remove_reference
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
          result = is_reference_type(remove_const_type(typid)) ? remove_reference_type(remove_const_type(typid)) : typid;
        break;

      case 0x41: // field_type
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
        {
          auto i = load_int(ctx, params + sizeof(Numeric::Int), type(Builtin::Type_USize));

          if (is_compound_type(typid) && i.value < type_cast<CompoundType>(typid)->fields.size())
            result = type_cast<CompoundType>(typid)->fields[i.value];
        }
        break;

      case 0xc8: // return_type
        if (auto declid = reinterpret_cast<Decl*>(load_int(ctx, params, type(Builtin::Type_DeclidLiteral)).value))
        {
          if (declid->kind() == Decl::Function)
            result = decl_cast<FunctionDecl>(declid)->returntype;
        }
        break;

      case 0x93: // parameters_type
        if (auto declid = reinterpret_cast<Decl*>(load_int(ctx, params, type(Builtin::Type_DeclidLiteral)).value))
        {
          if (declid->kind() == Decl::Function)
          {
            vector<Type*> fields;

            for (auto &parm : decl_cast<FunctionDecl>(declid)->parms)
              fields.push_back(decl_cast<ParmVarDecl>(parm)->type);

            result = ctx.typetable.find_or_create<TupleType>(vector<Type*>(fields), vector<Type*>(fields));
          }
        }
        break;

      case 0x18: // type_size
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
        {
          auto ptr = load_ptr(ctx, params + sizeof(Numeric::Int));

          store(ctx, ptr, type(Builtin::Type_USize), Numeric::int_literal(+1, sizeof_type(typid)));

          result = typid;
        }
        break;

      case 0x19: // type_align
        if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value))
        {
          auto ptr = load_ptr(ctx, params + sizeof(Numeric::Int));

          store(ctx, ptr, type(Builtin::Type_USize), Numeric::int_literal(+1, alignof_type(typid)));

          result = typid;
        }
        break;

      case 0xe4: // tuple_append
        if (auto tuple = reinterpret_cast<Type*>(load_int(ctx, params, type(Builtin::Type_TypeidLiteral)).value); tuple && is_tuple_type(remove_const_type(tuple)))
        {
          auto fields = type_cast<TupleType>(remove_const_type(tuple))->fields;

          if (auto typid = reinterpret_cast<Type*>(load_int(ctx, params + sizeof(Numeric::Int), type(Builtin::Type_TypeidLiteral)).value))
          {
            fields.push_back(typid);
          }

          result = ctx.typetable.find_or_create<TupleType>(vector<Type*>(fields), vector<Type*>(fields));
        }
        break;

      default:
        assert(false);
    }

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<IntLiteralExpr>(Numeric::int_literal(+1, reinterpret_cast<uintptr_t>(result)), loc));

    return true;
  }

  //|///////////////////// cfg //////////////////////////////////////////////
  bool eval_builtin_cfg(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto unit = get_unit(ctx.dx);
    auto str = expr_cast<StringLiteralExpr>(type_cast<TypeLitType>(callee.find_type(callee.fn->parms[0])->second)->value);
    auto cfg = std::find(unit->cfgs.begin(), unit->cfgs.end(), str->value());

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, cfg != unit->cfgs.end());

    return true;
  }

  //|///////////////////// __cfg__ //////////////////////////////////////////
  bool eval_builtin_cfgs(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    std::string config;
    for (auto &cfg : get_unit(ctx.dx)->cfgs)
      config += cfg + '\0';

    if (!config.empty())
      config.pop_back();

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<StringLiteralExpr>(config, loc));

    return true;
  }

  //|///////////////////// __srcdir__ ///////////////////////////////////////
  bool eval_builtin_srcdir(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto path = dirname(get_module(ctx.dx)->file());

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<StringLiteralExpr>(path, loc));

    return true;
  }

  //|///////////////////// __bindir__ ///////////////////////////////////////
  bool eval_builtin_bindir(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto path = std::string();

    for (auto &cfg : get_unit(ctx.dx)->cfgs)
      if (cfg.substr(0, 16) == "zaa.build.outdir")
        path = cfg.substr(17);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, ctx.make_expr<StringLiteralExpr>(path, loc));

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

  //|///////////////////// eval_runtime_fd_stat /////////////////////////////
  bool eval_runtime_fd_stat(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    struct filestat
    {
      uint8_t type;
      uint64_t size;
      uint64_t atime;
      uint64_t mtime;
      uint64_t ctime;
    };

    auto fd = load_int(ctx, fx, args[0]);
    auto fs = load_ptr(ctx, fx, args[1]);

    struct stat buf;
    auto res = fstat(fileno((FILE*)fd.value), &buf);

    store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal((res == 0) ? 0 : errno));

    filestat result = {};

    if ((buf.st_mode & S_IFDIR) == S_IFDIR)
      result.type = 3;

    if ((buf.st_mode & S_IFREG) == S_IFREG)
      result.type = 4;

    result.size = buf.st_size;

    result.atime = (uint64_t)buf.st_atime * (uint64_t)1000000000;
    result.ctime = (uint64_t)buf.st_ctime * (uint64_t)1000000000;
    result.mtime = (uint64_t)buf.st_mtime * (uint64_t)1000000000;

    memcpy(fs, &result, sizeof(result));

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

    for (size_t i = 0; i < n.value; ++i)
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

    for (size_t i = 0; i < n.value; ++i)
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

  //|///////////////////// eval_runtime_mem_alloc ///////////////////////////
  bool eval_runtime_mem_alloc(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto size = load_int(ctx, fx, args[0]);

    struct mem_result
    {
      uint32_t erno;
      uint64_t size;
      void *addr;
    };

    mem_result result = {};

    result.size = size.value;
    result.addr = ctx.allocate(size.value, 4096);

    memcpy(fx.locals[dst].alloc, &result, fx.locals[dst].size);

    return true;
  }

  //|///////////////////// eval_runtime_mem_free ////////////////////////////
  bool eval_runtime_mem_free(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    //auto &[callee, args, loc] = call;

    //auto addr = load_ptr(ctx, fx, args[0]);
    //auto size = load_int(ctx, fx, args[1]);

    return true;
  }

  //|///////////////////// eval_runtime_clk_getres //////////////////////////
  bool eval_runtime_clk_getres(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto id = load_int(ctx, fx, args[0]);

    struct clock_result
    {
      uint32_t erno;
      uint64_t timestamp;
    };

    clock_result result = {};

    switch (id.value)
    {
      case 0:
        result.timestamp = 1000000000 * std::chrono::system_clock::period::num / std::chrono::system_clock::period::den;
        break;

      case 1:
        result.timestamp = 1000000000 * std::chrono::steady_clock::period::num / std::chrono::steady_clock::period::den;
        break;
    }

    memcpy(fx.locals[dst].alloc, &result, fx.locals[dst].size);

    return true;
  }

  //|///////////////////// eval_runtime_clk_gettime /////////////////////////
  bool eval_runtime_clk_gettime(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto id = load_int(ctx, fx, args[0]);

    struct clock_result
    {
      uint32_t erno;
      uint64_t timestamp;
    };

    clock_result result = {};

    switch (id.value)
    {
      case 0:
        result.timestamp = std::chrono::nanoseconds(std::chrono::system_clock::now().time_since_epoch()).count();
        break;

      case 1:
        result.timestamp = std::chrono::nanoseconds(std::chrono::steady_clock::now().time_since_epoch()).count();
        break;
    }

    memcpy(fx.locals[dst].alloc, &result, fx.locals[dst].size);

    return true;
  }

  //|///////////////////// eval_runtime_exit ////////////////////////////////
  bool eval_runtime_exit(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    ctx.diag.error("Compile Time Exit Called", fx.scope, loc);

    return false;
  }

  //|///////////////////// __argc__ /////////////////////////////////////////
  bool eval_builtin_argc(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    ctx.diag.error("not implemented", fx.scope, loc);

    return false;
  }

  //|///////////////////// __argv__ /////////////////////////////////////////
  bool eval_builtin_argv(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    ctx.diag.error("not implemented", fx.scope, loc);

    return false;
  }

  //|///////////////////// __envp__ /////////////////////////////////////////
  bool eval_builtin_envp(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    store(ctx, fx.locals[dst].alloc, environ);

    return true;
  }

  //|///////////////////// eval_call ////////////////////////////////////////
  bool eval_call(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch (callee.fn->builtin)
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
          return eval_builtin_binary_arithmetic(ctx, fx, dst, call);

        case Builtin::Difference:
          return eval_builtin_pointer_difference(ctx, fx, dst, call);

        case Builtin::OffsetAddAssign:
        case Builtin::OffsetSubAssign:
          return eval_builtin_binary_arithmetic_assign(ctx, fx, dst, call);

        case Builtin::AddCarry:
        case Builtin::SubBorrow:
        case Builtin::MulCarry:
          return eval_builtin_binary_arithmetic_carry(ctx, fx, dst, call);

        case Builtin::SliceLen:
        case Builtin::StringLen:
          return eval_builtin_slice_len(ctx, fx, dst, call);

        case Builtin::SliceData:
        case Builtin::StringData:
        case Builtin::SliceBegin:
        case Builtin::StringBegin:
          return eval_builtin_slice_data(ctx, fx, dst, call);

        case Builtin::SliceEnd:
        case Builtin::StringEnd:
          return eval_builtin_slice_end(ctx, fx, dst, call);

        case Builtin::SliceIndex:
        case Builtin::StringIndex:
          return eval_builtin_slice_index(ctx, fx, dst, call);

        case Builtin::SliceSlice:
        case Builtin::StringSlice:
          return eval_builtin_slice_slice(ctx, fx, dst, call);

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

        case Builtin::ArrayCreate:
          return eval_builtin_array_create(ctx, fx, dst, call);

        case Builtin::MatchRange:
          return eval_builtin_match_range(ctx, fx, dst, call);

        case Builtin::MatchRangeEq:
          return eval_builtin_match_range_eq(ctx, fx, dst, call);

        case Builtin::CallOp:
          return eval_builtin_callop(ctx, fx, dst, call);

        case Builtin::is_nan:
        case Builtin::is_finite:
        case Builtin::is_normal:
          return eval_builtin_classify(ctx, fx, dst, call);

        case Builtin::nan:
          return eval_builtin_nan(ctx, fx, dst, call);

        case Builtin::inf:
          return eval_builtin_inf(ctx, fx, dst, call);

        case Builtin::clz:
          return eval_builtin_clz(ctx, fx, dst, call);

        case Builtin::ctz:
          return eval_builtin_ctz(ctx, fx, dst, call);

        case Builtin::popcnt:
          return eval_builtin_popcnt(ctx, fx, dst, call);

        case Builtin::signbit:
          return eval_builtin_signbit(ctx, fx, dst, call);

        case Builtin::byteswap:
          return eval_builtin_byteswap(ctx, fx, dst, call);

        case Builtin::bitreverse:
          return eval_builtin_bitreverse(ctx, fx, dst, call);

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

        case Builtin::alloca:
          return eval_builtin_alloca(ctx, fx, dst, call);

        case Builtin::atomic_load:
          return eval_builtin_atomic_load(ctx, fx, dst, call);

        case Builtin::atomic_store:
          return eval_builtin_atomic_store(ctx, fx, dst, call);

        case Builtin::atomic_cmpxchg:
          return eval_builtin_atomic_cmpxchg(ctx, fx, dst, call);

        case Builtin::atomic_xchg:
        case Builtin::atomic_fetch_add:
        case Builtin::atomic_fetch_sub:
        case Builtin::atomic_fetch_and:
        case Builtin::atomic_fetch_xor:
        case Builtin::atomic_fetch_or:
        case Builtin::atomic_fetch_nand:
          return eval_builtin_atomic_arithmatic(ctx, fx, dst, call);

        case Builtin::atomic_thread_fence:
          return true;

        case Builtin::relax:
          return true;

        case Builtin::__argc__:
          return eval_builtin_argc(ctx, fx, dst, call);

        case Builtin::__argv__:
          return eval_builtin_argv(ctx, fx, dst, call);

        case Builtin::__envp__:
          return eval_builtin_envp(ctx, fx, dst, call);

        case Builtin::decl_kind:
          return eval_builtin_decl_kind(ctx, fx, dst, call);

        case Builtin::decl_name:
          return eval_builtin_decl_name(ctx, fx, dst, call);

        case Builtin::decl_flags:
          return eval_builtin_decl_flags(ctx, fx, dst, call);

        case Builtin::decl_parent:
          return eval_builtin_decl_parent(ctx, fx, dst, call);

        case Builtin::decl_children:
          return eval_builtin_decl_children(ctx, fx, dst, call);

        case Builtin::decl_site:
          return eval_builtin_decl_site(ctx, fx, dst, call);

        case Builtin::decl_attr:
          return eval_builtin_decl_attr(ctx, fx, dst, call);

        case Builtin::attr_text:
          return eval_builtin_attr_text(ctx, fx, dst, call);

        case Builtin::type_decl:
          return eval_builtin_type_decl(ctx, fx, dst, call);

        case Builtin::type_name:
          return eval_builtin_type_name(ctx, fx, dst, call);

        case Builtin::type_children:
          return eval_builtin_type_children(ctx, fx, dst, call);

        case Builtin::type_query:
          return eval_builtin_type_query(ctx, fx, dst, call);

        case Builtin::__cfg:
          return eval_builtin_cfg(ctx, fx, dst, call);

        case Builtin::__cfg__:
          return eval_builtin_cfgs(ctx, fx, dst, call);

        case Builtin::__srcdir__:
          return eval_builtin_srcdir(ctx, fx, dst, call);

        case Builtin::__bindir__:
          return eval_builtin_bindir(ctx, fx, dst, call);

        case Builtin::is_const_eval:
          store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, true);
          return true;

        default:
          assert(false);
      }

      return false;
    }
    else if (callee.fn->flags & FunctionDecl::ExternC)
    {
      if (callee.fn->name == "fd_open"sv)
        return eval_runtime_fd_open(ctx, fx, dst, call);

      if (callee.fn->name == "fd_stat"sv)
        return eval_runtime_fd_stat(ctx, fx, dst, call);

      if (callee.fn->name == "fd_readv"sv)
        return eval_runtime_fd_readv(ctx, fx, dst, call);

      if (callee.fn->name == "fd_preadv"sv)
        return eval_runtime_fd_preadv(ctx, fx, dst, call);

      if (callee.fn->name == "fd_writev"sv)
        return eval_runtime_fd_writev(ctx, fx, dst, call);

      if (callee.fn->name == "fd_pwritev"sv)
        return eval_runtime_fd_pwritev(ctx, fx, dst, call);

      if (callee.fn->name == "fd_close"sv)
        return eval_runtime_fd_close(ctx, fx, dst, call);

      if (callee.fn->name == "mem_alloc"sv)
        return eval_runtime_mem_alloc(ctx, fx, dst, call);

      if (callee.fn->name == "mem_free"sv)
        return eval_runtime_mem_free(ctx, fx, dst, call);

      if (callee.fn->name == "clk_getres"sv)
        return eval_runtime_clk_getres(ctx, fx, dst, call);

      if (callee.fn->name == "clk_gettime"sv)
        return eval_runtime_clk_gettime(ctx, fx, dst, call);

      if (callee.fn->name == "exit"sv)
        return eval_runtime_exit(ctx, fx, dst, call);

      ctx.diag.error("invalid compille time call", fx.scope, loc);

      return false;
    }
    else
    {
      auto &mir = lower(callee, ctx.typetable, ctx.diag);

#if 0
      dump_mir(mir);
#endif

      if (ctx.diag.has_errored())
        return false;

      auto stackframe = ctx.push<FunctionContext::Local>(mir.locals.size());

      if (remove_qualifiers_type(fx.locals[dst].type) != remove_qualifiers_type(mir.locals[0].type))
      {
        ctx.diag.error("type mismatch", fx.scope, loc);
        ctx.diag << "  return type: '" << *mir.locals[0].type << "' wanted: '" << *fx.locals[dst].type << "'\n";
        return false;
      }

      stackframe[0] = fx.locals[dst];

      if (callee.throwtype)
      {
        stackframe[1] = fx.locals[fx.errorarg];
      }

      for (size_t i = 0; i < args.size(); ++i)
      {
        stackframe[mir.args_beg + i] = fx.locals[args[i]];
      }

      return eval_function(ctx, callee.fn, mir, stackframe);
    }
  }

  //|///////////////////// eval_cast ////////////////////////////////////////
  bool eval_cast(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CastData const &cast)
  {
    auto &[arg, loc] = cast;

    auto lhstype = fx.locals[dst].type;
    auto rhstype = fx.locals[arg].type;

    if (fx.locals[dst].flags & MIR::Local::Reference)
      lhstype = ctx.typetable.find_or_create<ReferenceType>(lhstype);

    if (fx.locals[arg].flags & MIR::Local::Reference)
      rhstype = ctx.typetable.find_or_create<ReferenceType>(rhstype);

    if (is_int(lhstype) && is_int(rhstype))
    {
      auto value = load_int(ctx, fx.locals[arg].alloc, fx.locals[arg].type);

      if (is_enum_type(lhstype))
        lhstype = type_cast<TagType>(lhstype)->fields[0];

      if (!is_literal_valid(type_cast<BuiltinType>(lhstype)->kind(), value))
      {
        ctx.diag.error("value out of range for required type", fx.scope, loc);
        ctx.diag << "  cast value: '" << value << "' required type: '" << *lhstype << "'\n";
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, value);
    }
    else if (is_float(lhstype) && is_float(rhstype))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, load_float(ctx, fx.locals[arg].alloc, fx.locals[arg].type));
    }
    else if (is_int(lhstype) && is_float(rhstype))
    {
      auto value = Numeric::int_cast<double>(load_float(ctx, fx.locals[arg].alloc, fx.locals[arg].type));

      if (is_enum_type(lhstype))
        lhstype = type_cast<TagType>(lhstype)->fields[0];

      if (!is_literal_valid(type_cast<BuiltinType>(lhstype)->kind(), value))
      {
        ctx.diag.error("value out of range for required type", fx.scope, loc);
        ctx.diag << "  cast value: '" << value << "' required type: '" << *lhstype << "'\n";
        return false;
      }

      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, value);
    }
    else if (is_float(lhstype) && is_int(rhstype))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::float_cast<double>(load_int(ctx, fx.locals[arg].alloc, fx.locals[arg].type)));
    }
    else if (is_pointference_type(lhstype) && is_null_type(rhstype))
    {
      store(ctx, fx.locals[dst].alloc, nullptr);
    }
    else if (is_pointference_type(lhstype) && is_pointference_type(rhstype))
    {
      store(ctx, fx.locals[dst].alloc, load_ptr(ctx, fx.locals[arg].alloc));
    }
    else if (is_pointference_type(lhstype) && is_int_type(rhstype))
    {
      store(ctx, fx.locals[dst].alloc, (void*)(load_int(ctx, fx.locals[arg].alloc, fx.locals[arg].type).value));
    }
    else if (is_int_type(lhstype) && is_pointference_type(rhstype))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, Numeric::int_literal(+1, (size_t)load_ptr(ctx, fx.locals[arg].alloc)));
    }
    else if (is_bool_type(lhstype) && is_pointference_type(rhstype))
    {
      store(ctx, fx.locals[dst].alloc, fx.locals[dst].type, load_ptr(ctx, fx.locals[arg].alloc) != nullptr);
    }
    else
    {
      ctx.diag.error("invalid static cast", fx.scope, loc);
      ctx.diag << "  src type: '" << *rhstype << "' dst type: '" << *lhstype << "'\n";
    }

    return true;
  }

  //|///////////////////// eval_injection ///////////////////////////////////
  bool eval_injection(EvalContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::InjectionData const &injection)
  {
    auto &[expr, args, loc] = injection;

    vector<Expr*> substitutions;

    for (auto &arg : args)
    {
      auto value = make_expr(ctx, fx.locals[arg].alloc, fx.locals[arg].type, loc);

      if (!is_typed_literal(fx.locals[arg].type))
        value = ctx.make_expr<CastExpr>(fx.locals[arg].type, value, loc);

      substitutions.push_back(value);
    }

    if (any_of(substitutions.begin(), substitutions.end(), [](auto &k) { return !k; }))
      return false;

    Sema sema;

    for (auto &decl : expr->decls)
    {
      auto fragment = copier(decl, substitutions, ctx.diag);

      if (fragment->kind() == Decl::EnumConstant && (!is_decl_scope(ctx.dx) || get<Decl*>(ctx.dx.owner)->kind() != Decl::Enum))
        ctx.diag.error("invalid constant fragment in non-enum", fx.scope, loc);

      if (fragment->kind() == Decl::Requires && (!is_decl_scope(ctx.dx) || get<Decl*>(ctx.dx.owner)->kind() != Decl::Concept))
        ctx.diag.error("invalid requires fragment in non-concept", fx.scope, loc);

      if (fragment->kind() == Decl::Case && (!is_stmt_scope(ctx.dx) || get<Stmt*>(ctx.dx.owner)->kind() != Stmt::Switch))
        ctx.diag.error("invalid case fragment in non-switch", fx.scope, loc);

      if (ctx.diag.has_errored())
        continue;

      semantic(ctx.dx, fragment, sema, ctx.diag);

      ctx.fragments.push_back(fragment);
    }

    return true;
  }

  //|///////////////////// eval_assign_statement ////////////////////////////
  bool eval_assign_statement(EvalContext &ctx, FunctionContext &fx, MIR::Statement const &statement)
  {
    auto &src = statement.src;
    auto &dst = statement.dst;

    if (!fx.locals[dst].type)
    {
      ctx.diag.error("unresolved destination type");
      return false;
    }

    switch (src.kind())
    {
      case MIR::RValue::Empty:
        return true;

      case MIR::RValue::Constant:
        return eval_assign_constant(ctx, fx, dst, src.get<MIR::RValue::Constant>());

      case MIR::RValue::Variable:
        return eval_assign_variable(ctx, fx, dst, src.get<MIR::RValue::Variable>());

      case MIR::RValue::Call:
        return eval_call(ctx, fx, dst, src.get<MIR::RValue::Call>());

      case MIR::RValue::Cast:
        return eval_cast(ctx, fx, dst, src.get<MIR::RValue::Cast>());

      case MIR::RValue::Injection:
        return eval_injection(ctx, fx, dst, src.get<MIR::RValue::Injection>());

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
    dest.type = fx.locals[dst].type;
    dest.flags = fx.locals[dst - 1].flags;
    dest.alloc = load_ptr(ctx, fx.locals[dst - 1].alloc);
    dest.size = sizeof_type(dest.type);

    if (dest.alloc == nullptr)
    {
      ctx.diag.error("null pointer dereference");
      return false;
    }

    swap(fx.locals[dst], dest);

    eval_assign_statement(ctx, fx, statement);

    swap(dest, fx.locals[dst]);

    store(ctx, fx.locals[dst].alloc, dest.alloc);

    return true;
  }

  //|///////////////////// eval_function ////////////////////////////////////
  bool eval_function(EvalContext &ctx, Scope const &scope, MIR const &mir, FunctionContext::Local *locals)
  {
    FunctionContext fx;

    fx.scope = scope;
    fx.locals = locals;

    for (size_t i = mir.args_end, end = mir.locals.size(); i != end; ++i)
    {
      if (is_unresolved_type(mir.locals[i].type))
        continue;

      fx.locals[i] = alloc(ctx, mir.locals[i]);
    }

    for (auto &[arg, value] : mir.statics)
    {
      eval_assign_constant(ctx, fx, arg, value.get<MIR::RValue::Constant>());
    }

    for (size_t block = 0; block < mir.blocks.size(); )
    {
      if (auto &terminator = mir.blocks[block].terminator; terminator.kind == MIR::Terminator::Catch)
        fx.errorarg = terminator.value;

      for (auto &statement : mir.blocks[block].statements)
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

          case MIR::Statement::StorageLoop:
            break;
        }
      }

      switch (auto &terminator = mir.blocks[block].terminator; terminator.kind)
      {
        case MIR::Terminator::Goto:
          block = terminator.blockid;
          break;

        case MIR::Terminator::Switch: {
          block = terminator.blockid;

          auto cond = load_int(ctx, fx.locals[terminator.value].alloc, fx.locals[terminator.value].type);

          for (auto &[k, v] : terminator.targets)
          {
            if (cond.sign * cond.value == k)
              block = v;
          }

          break;
        }

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

        case MIR::Terminator::Unreachable:
          assert(false);
          break;
      }
    }

    ctx.stackp = (uint8_t*)locals;

    return true;
  }

  //|///////////////////// eval_callee //////////////////////////////////////
  EvalResult eval_callee_fast(FnSig const &callee, Type *returntype, vector<EvalResult> const &parms, SourceLocation loc)
  {
    EvalResult result = {};

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch (callee.fn->builtin)
      {
        case Builtin::And:
          if (is_int_type(returntype))
            result.value = new IntLiteralExpr(expr_cast<IntLiteralExpr>(parms[0].value)->value() & expr_cast<IntLiteralExpr>(parms[1].value)->value(), loc);
          break;

        case Builtin::Or:
          if (is_int_type(returntype))
            result.value = new IntLiteralExpr(expr_cast<IntLiteralExpr>(parms[0].value)->value() | expr_cast<IntLiteralExpr>(parms[1].value)->value(), loc);
          break;

        case Builtin::Xor:
          if (is_int_type(returntype))
            result.value = new IntLiteralExpr(expr_cast<IntLiteralExpr>(parms[0].value)->value() ^ expr_cast<IntLiteralExpr>(parms[1].value)->value(), loc);
          break;

        case Builtin::Add:
          if (is_int_type(returntype))
            result.value = new IntLiteralExpr(expr_cast<IntLiteralExpr>(parms[0].value)->value() + expr_cast<IntLiteralExpr>(parms[1].value)->value(), loc);
          if (is_float_type(returntype))
            result.value = new FloatLiteralExpr(expr_cast<FloatLiteralExpr>(parms[0].value)->value() + expr_cast<FloatLiteralExpr>(parms[1].value)->value(), loc);
          break;

        case Builtin::Sub:
          if (is_int_type(returntype))
            result.value = new IntLiteralExpr(expr_cast<IntLiteralExpr>(parms[0].value)->value() - expr_cast<IntLiteralExpr>(parms[1].value)->value(), loc);
          if (is_float_type(returntype))
            result.value = new FloatLiteralExpr(expr_cast<FloatLiteralExpr>(parms[0].value)->value() - expr_cast<FloatLiteralExpr>(parms[1].value)->value(), loc);
          break;

        case Builtin::Mul:
          if (is_int_type(returntype))
            result.value = new IntLiteralExpr(expr_cast<IntLiteralExpr>(parms[0].value)->value() * expr_cast<IntLiteralExpr>(parms[1].value)->value(), loc);
          if (is_float_type(returntype))
            result.value = new FloatLiteralExpr(expr_cast<FloatLiteralExpr>(parms[0].value)->value() * expr_cast<FloatLiteralExpr>(parms[1].value)->value(), loc);
          break;

        case Builtin::Shl:
          if (is_builtin_type(returntype) && type_cast<BuiltinType>(returntype)->kind() == BuiltinType::IntLiteral)
            result.value = new IntLiteralExpr(expr_cast<IntLiteralExpr>(parms[0].value)->value() << expr_cast<IntLiteralExpr>(parms[1].value)->value(), loc);
          break;

        case Builtin::Shr:
          if (is_builtin_type(returntype) && type_cast<BuiltinType>(returntype)->kind() == BuiltinType::IntLiteral)
            result.value = new IntLiteralExpr(expr_cast<IntLiteralExpr>(parms[0].value)->value() >> expr_cast<IntLiteralExpr>(parms[1].value)->value(), loc);
          break;

        default:
          break;
      }
    }

    if ((callee.fn->flags & FunctionDecl::DeclType) == FunctionDecl::ConstDecl)
    {
      if (auto expr = stmt_cast<ReturnStmt>(callee.fn->body)->expr; is_literal_expr(expr))
        result.value = expr;
    }

    result.type = returntype;

    return result;
  }

  //|///////////////////// make_result //////////////////////////////////////
  EvalResult make_result(EvalContext &ctx, FunctionContext::Local &value, SourceLocation loc)
  {
    EvalResult result;

    result.type = value.type;
    result.value = make_expr(ctx, value.alloc, value.type, loc);

    if (is_slice_type(result.type))
    {
      result.type = ctx.typetable.find_or_create<ArrayType>(type_cast<SliceType>(result.type)->type, expr_cast<ArrayLiteralExpr>(result.value)->size);
    }

    if (ctx.fragments.size() != 0)
    {
      if (!is_void_type(result.type))
        ctx.diag.error("invalid fragment in non-void function", ctx.dx, loc);

      result.value = ctx.make_expr<FragmentExpr>(ctx.fragments, loc);
    }

    return result;
  }

  EvalResult evaluate(EvalContext &ctx, Scope const &scope, MIR const &mir, SourceLocation loc)
  {
    EvalResult result = {};

    auto stackframe = ctx.push<FunctionContext::Local>(mir.locals.size());

    if (is_unresolved_type(mir.locals[0].type))
    {
      ctx.diag.error("unresolved expression type", ctx.dx, loc);
      return result;
    }

    stackframe[0] = alloc(ctx, mir.locals[0]);

    if (eval_function(ctx, scope, mir, stackframe))
    {
      if (ctx.exception)
      {
        ctx.diag.error("exception occured in compile time context", ctx.dx, loc);
        return result;
      }

      if (mir.locals[0].flags & MIR::Local::Reference)
      {
        stackframe[0].alloc = load_ptr(ctx, stackframe[0].alloc);
        stackframe[0].type = remove_const_type(remove_pointer_type(stackframe[0].type));
        stackframe[0].size = sizeof_type(stackframe[0].type);
      }

      result = make_result(ctx, stackframe[0], loc);
    }

    return result;
  }
}

//|--------------------- Evaluate -------------------------------------------
//|--------------------------------------------------------------------------

EvalResult evaluate(Scope const &scope, FnSig const &callee, Type *returntype, vector<EvalResult> const &parms, TypeTable &typetable, Diag &diag, SourceLocation loc)
{
  // optimisation: attempt some direct literal maths
  if (auto result = eval_callee_fast(callee, returntype, parms, loc))
    return result;

  EvalContext ctx(scope, typetable, diag);

  MIR mir = {};
  mir.add_local(MIR::Local(returntype));

  if ((mir.throws = callee.throwtype))
    mir.add_local(MIR::Local(callee.throwtype));

  mir.args_beg = mir.args_end = mir.locals.size();

  mir.add_block(MIR::Block());

  std::vector<MIR::local_t> args;

  for (auto const &[parm, expr] : zip(callee.parameters(), parms))
  {
    auto arg = mir.add_local(MIR::Local(expr.type));

    mir.add_statement(MIR::Statement::assign(arg, MIR::RValue::literal(expr.value)));

    if (is_reference_type(decl_cast<ParmVarDecl>(parm)->type))
    {
      arg = mir.add_local(MIR::Local(expr.type, MIR::Local::Reference));

      mir.add_statement(MIR::Statement::assign(arg, MIR::RValue::local(MIR::RValue::Ref, arg - 1, loc)));
    }

    args.push_back(arg);
  }

  mir.add_statement(MIR::Statement::assign(0, MIR::RValue::call(callee, std::move(args), loc)));

  return evaluate(ctx, scope, mir, loc);
}

EvalResult evaluate(Scope const &scope, Expr *expr, unordered_map<Decl*, MIR::Fragment> const &symbols, TypeTable &typetable, Diag &diag, SourceLocation loc)
{
  EvalContext ctx(scope, typetable, diag);

  auto mir = lower(scope, expr, symbols, typetable, ctx.diag);

  if (ctx.diag.has_errored())
    return {};

  return evaluate(ctx, scope, mir, loc);
}

EvalResult evaluate(Scope const &scope, MIR const &mir, TypeTable &typetable, Diag &diag, SourceLocation loc)
{
  EvalContext ctx(scope, typetable, diag);

  return evaluate(ctx, scope, mir, loc);
}
