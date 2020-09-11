//
// codegen.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "codegen.h"
#include "diag.h"
#include "mangle.h"
#include "lower.h"
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/AssemblyAnnotationWriter.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/CodeGen/MachineFunctionPass.h>
#include <llvm/Transforms/IPO.h>
#include <llvm/Transforms/IPO/AlwaysInliner.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/TargetTransformInfo.h>
#include <llvm/IR/DIBuilder.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/TargetRegistry.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/FileSystem.h>
#include <sstream>
#include <climits>

using namespace std;

namespace
{
  struct GenContext
  {
    AST *ast;
    Diag &diag;

    GenOpts genopts;

    llvm::LLVMContext context;
    llvm::Module module;
    llvm::Triple triple;
    llvm::IRBuilder<> builder;

    TypeTable typetable;

    FunctionDecl *main = nullptr;

    unordered_map<FnSig, llvm::Function*> functions;
    unordered_map<Type*, llvm::StructType*> slicetypes;
    unordered_map<Type*, llvm::StructType*> structtypes;

    llvm::DIBuilder di;
    llvm::DIFile *difile;
    llvm::DICompileUnit *diunit;
    unordered_map<Type*, llvm::DIType*> ditypes;
    llvm::SmallString<128> current_directory;

    llvm::Function *assert_div0 = nullptr;
    llvm::Function *assert_carry = nullptr;
    llvm::Function *assert_deref = nullptr;
    llvm::Function *div0_chk_fail = nullptr;
    llvm::Function *carry_chk_fail = nullptr;
    llvm::Function *null_chk_fail = nullptr;

    Type *voidtype;
    Type *booltype;

    GenContext(AST *ast, GenOpts const &genopts, Diag &diag)
      : ast(ast),
        diag(diag),
        genopts(genopts),
        module(genopts.modulename, context),
        builder(context),
        di(module)
    {
      triple = llvm::Triple(genopts.triple);

      module.setTargetTriple(genopts.triple);

#ifndef NDEBUG
      string error;
      auto target = llvm::TargetRegistry::lookupTarget(genopts.triple, error);

      if (!target)
      {
        diag << error << '\n';
        return;
      }

      auto machine = target->createTargetMachine(genopts.triple, genopts.cpu, genopts.features, {}, {});

      if (!machine)
      {
        diag << "could not create target machine" << '\n';
        return;
      }

      module.setDataLayout(machine->createDataLayout());
#endif

      voidtype = type(Builtin::Type_Void);
      booltype = type(Builtin::Type_Bool);
    }
  };

  struct FunctionContext
  {
    MIR mir;

    FunctionDecl *fn;

    struct Local
    {
      int writes = 0;

      bool addressable = false;
      bool firstarg_return = false;
      bool passarg_pointer = false;

      llvm::Value *value = nullptr;
      llvm::Value *alloca = nullptr;

      MIR::VarInfo *info = nullptr;
    };

    vector<Local> locals;

    struct Block
    {
      llvm::BasicBlock *bx = nullptr;
    };

    vector<Block> blocks;

    size_t currentblockid;
    size_t currentlineinfo = 0;

    llvm::Value *lastcall;
    llvm::Value *errorresult;

    bool firstarg_return = false;

    llvm::DIFile *difile;
    vector<llvm::DIScope*> discopes;

    FunctionContext(FnSig const &sig)
    {
      fn = sig.fn;
    }
  };

  enum class TypeCategory
  {
    Void,
    Bool,
    SignedInteger,
    UnsignedInteger,
    FloatingPoint,
    Struct,
    Pointer,
    Array,
    Slice,
    Null,
    Unresolved,
  };

  //|///////////////////// type_category ///////////////////////////////
  TypeCategory type_category(Type const *type)
  {
    switch(type->klass())
    {
      case Type::Builtin:
        switch (type_cast<BuiltinType>(type)->kind())
        {
          case BuiltinType::Void:
            return TypeCategory::Void;

          case BuiltinType::Bool:
            return TypeCategory::Bool;

          case BuiltinType::Char:
            return TypeCategory::UnsignedInteger;

          case BuiltinType::I8:
          case BuiltinType::I16:
          case BuiltinType::I32:
          case BuiltinType::I64:
          case BuiltinType::ISize:
            return TypeCategory::SignedInteger;

          case BuiltinType::U8:
          case BuiltinType::U16:
          case BuiltinType::U32:
          case BuiltinType::U64:
          case BuiltinType::USize:
            return TypeCategory::UnsignedInteger;

          case BuiltinType::F32:
          case BuiltinType::F64:
            return TypeCategory::FloatingPoint;

          case BuiltinType::PtrLiteral:
            return TypeCategory::Null;

          case BuiltinType::StringLiteral:
            return TypeCategory::Slice;

          case BuiltinType::IntLiteral:
          case BuiltinType::FloatLiteral:
            return TypeCategory::Unresolved;
        }
        break;

      case Type::Const:
        return type_category(type_cast<ConstType>(type)->type);

      case Type::QualArg:
        return type_category(type_cast<QualArgType>(type)->type);

      case Type::Pointer:
      case Type::Reference:
        return TypeCategory::Pointer;

      case Type::Array:
        return TypeCategory::Array;

      case Type::Tuple:
        return TypeCategory::Struct;

      case Type::Tag:
        switch (type_cast<TagType>(type)->decl->kind())
        {
          case Decl::Struct:
          case Decl::Lambda:
            return TypeCategory::Struct;

          case Decl::Enum:
            return type_category(type_cast<TagType>(type)->fields[0]);

          default:
            assert(false);
        }
        break;

        return TypeCategory::Struct;

      case Type::Function:
        return TypeCategory::Pointer;

      case Type::TypeArg:
      case Type::TypeRef:
        return TypeCategory::Unresolved;

      default:
        assert(false);
    }

    return TypeCategory::Unresolved;
  }

  llvm::Type *llvm_type(GenContext &ctx, Type *type, bool addressable);
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, Expr *literal);

  //|///////////////////// is_firstarg_return ///////////////////////////////
  bool is_firstarg_return(GenContext &ctx, FnSig const &fx, MIR::Local const &returntype)
  {
    if (fx.throwtype)
      return true;

    if (fx.fn->flags & FunctionDecl::Constructor)
      return true;

    if (returntype.flags & MIR::Local::Reference)
      return false;

    if (!is_concrete_type(returntype.type))
      return false;

    if (is_tuple_type(returntype.type) && returntype.zerosized())
      return true;

    if (is_array_type(returntype.type) && returntype.zerosized())
      return true;

    if (ctx.triple.getOS() == llvm::Triple::Win32)
    {
      if (fx.fn->flags & FunctionDecl::ExternC)
        return sizeof_type(returntype.type) > 8;
    }

    return sizeof_type(returntype.type) > 16;
  }

  //|///////////////////// is_passarg_pointer ///////////////////////////////
  bool is_passarg_pointer(GenContext &ctx, FnSig const &fx, MIR::Local const &argtype)
  {
    if (!is_concrete_type(argtype.type))
      return false;

    if (argtype.flags & MIR::Local::Reference)
      return false;

    if (ctx.triple.getOS() == llvm::Triple::Win32)
    {
      if (fx.fn->flags & FunctionDecl::ExternC)
        return sizeof_type(argtype.type) > 8;
    }

    return sizeof_type(argtype.type) > 16;
  }

  //|///////////////////// llvm_identifier //////////////////////////////////
  string llvm_identifier(string const &prefix, Type *type)
  {
    stringstream ss;

    switch(type->klass())
    {
      case Type::Builtin:
        ss << prefix << '.' << type_cast<BuiltinType>(type)->name();
        break;

      case Type::Tag:
        ss << prefix << '.' << decl_cast<TagDecl>(type_cast<TagType>(type)->decl)->name << '.' << hex << static_cast<void*>(type);
        break;

      case Type::Tuple:
        ss << prefix << '.' << hex << static_cast<void*>(type);
        break;

      default:
        assert(false);
    }

    return ss.str();
  }

  //|///////////////////// llvm_void ////////////////////////////////////////
  llvm::Type *llvm_void(GenContext &ctx, Type *type)
  {
    if (auto j = ctx.structtypes.find(type); j != ctx.structtypes.end())
      return j->second;

    auto strct = llvm::StructType::create(ctx.context, "void");

    strct->setBody(vector<llvm::Type*>{});

    ctx.structtypes.emplace(type, strct);

    return strct;
  }

  //|///////////////////// llvm_slice ///////////////////////////////////////
  llvm::Type *llvm_slice(GenContext &ctx, Type *type)
  {
    if (auto j = ctx.slicetypes.find(type); j != ctx.slicetypes.end())
      return j->second;

    auto strct = llvm::StructType::create(ctx.context, llvm_identifier("slice", type));

    vector<llvm::Type*> elements;

    elements.push_back(ctx.builder.getInt64Ty());
    elements.push_back(llvm_type(ctx, type, true)->getPointerTo());

    strct->setBody(elements);

    ctx.slicetypes.emplace(type, strct);

    return strct;
  }

  //|///////////////////// llvm_array ///////////////////////////////////////
  llvm::Type *llvm_array(GenContext &ctx, ArrayType *type)
  {
    auto elemtype = type->type;
    auto arraylen = array_len(type);

    auto array = llvm::ArrayType::get(llvm_type(ctx, elemtype, true), arraylen);

    assert(ctx.module.getDataLayout().getTypeAllocSize(array) == sizeof_type(type));
    assert(ctx.module.getDataLayout().getABITypeAlignment(array) == alignof_type(type));

    return array;
  }

  //|///////////////////// llvm_struct //////////////////////////////////////
  llvm::Type *llvm_struct(GenContext &ctx, TagType *type)
  {
    if (auto j = ctx.structtypes.find(type); j != ctx.structtypes.end())
      return j->second;

    auto strct = llvm::StructType::create(ctx.context, llvm_identifier("struct", type));

    ctx.structtypes.emplace(type, strct);

    vector<llvm::Type*> elements;

    for(auto &field: type->fields)
    {
      elements.push_back(llvm_type(ctx, field, true));
    }

    strct->setBody(elements);

    assert(ctx.module.getDataLayout().getTypeAllocSize(strct) == sizeof_type(type));
    assert(ctx.module.getDataLayout().getABITypeAlignment(strct) == alignof_type(type));

    return strct;
  }

  //|///////////////////// llvm_struct //////////////////////////////////////
  llvm::Type *llvm_struct(GenContext &ctx, TupleType *type)
  {
    if (auto j = ctx.structtypes.find(type); j != ctx.structtypes.end())
      return j->second;

    vector<llvm::Type*> elements;

    for(auto &field: type->fields)
    {
      elements.push_back(llvm_type(ctx, field, true));
    }

    auto strct = llvm::StructType::get(ctx.context, elements);

    assert(ctx.module.getDataLayout().getTypeAllocSize(strct) == sizeof_type(type));
    assert(ctx.module.getDataLayout().getABITypeAlignment(strct) == alignof_type(type));

    ctx.structtypes.emplace(type, strct);

    return strct;
  }

  //|///////////////////// llvm_fntype //////////////////////////////////////
  llvm::Type *llvm_fntype(GenContext &ctx, FunctionType *type)
  {
    auto returntype = llvm_type(ctx, type->returntype, false);

    vector<llvm::Type*> params;

    for(auto &parm : type_cast<TupleType>(type->paramtuple)->fields)
    {
      params.push_back(llvm_type(ctx, parm, false));
    }

    return llvm::FunctionType::get(returntype, params, false);
  }

  //|///////////////////// llvm_type ////////////////////////////////////////
  llvm::Type *llvm_type(GenContext &ctx, Type *type, bool addressable = false)
  {
    switch (type->klass())
    {
      case Type::Builtin:
        switch (type_cast<BuiltinType>(type)->kind())
        {
          case BuiltinType::Bool:
            return addressable ? ctx.builder.getInt8Ty() : ctx.builder.getInt1Ty();
          case BuiltinType::Char:
            return ctx.builder.getInt32Ty();
          case BuiltinType::I8:
            return ctx.builder.getInt8Ty();
          case BuiltinType::I16:
            return ctx.builder.getInt16Ty();
          case BuiltinType::I32:
            return ctx.builder.getInt32Ty();
          case BuiltinType::I64:
            return ctx.builder.getInt64Ty();
          case BuiltinType::ISize:
            return ctx.builder.getInt64Ty();
          case BuiltinType::U8:
            return ctx.builder.getInt8Ty();
          case BuiltinType::U16:
            return ctx.builder.getInt16Ty();
          case BuiltinType::U32:
            return ctx.builder.getInt32Ty();
          case BuiltinType::U64:
            return ctx.builder.getInt64Ty();
          case BuiltinType::USize:
            return ctx.builder.getInt64Ty();
          case BuiltinType::F32:
            return ctx.builder.getFloatTy();
          case BuiltinType::F64:
            return ctx.builder.getDoubleTy();

          case BuiltinType::Void:
          case BuiltinType::PtrLiteral:
            return addressable ? llvm_void(ctx, type) : ctx.builder.getVoidTy();

          case BuiltinType::StringLiteral:
            return llvm_slice(ctx, Builtin::type(Builtin::Type_U8));

          case BuiltinType::IntLiteral:
          case BuiltinType::FloatLiteral:
            break;
        }
        break;

      case Type::Const:
        return llvm_type(ctx, type_cast<ConstType>(type)->type, addressable);

      case Type::QualArg:
        return llvm_type(ctx, type_cast<QualArgType>(type)->type, addressable);

      case Type::Pointer:
        return llvm_type(ctx, type_cast<PointerType>(type)->type, true)->getPointerTo();

      case Type::Reference:
        return llvm_type(ctx, type_cast<ReferenceType>(type)->type, true)->getPointerTo();

      case Type::Array:
        return llvm_array(ctx, type_cast<ArrayType>(type));

      case Type::Tuple:
        return llvm_struct(ctx, type_cast<TupleType>(type));

      case Type::Tag:
        switch (type_cast<TagType>(type)->decl->kind())
        {
          case Decl::Struct:
          case Decl::Lambda:
            return llvm_struct(ctx, type_cast<TagType>(type));

          case Decl::Enum:
            return llvm_type(ctx, type_cast<TagType>(type)->fields[0]);

          default:
            assert(false);
        }
        break;

      case Type::Function:
        return llvm_fntype(ctx, type_cast<FunctionType>(type));

      default:
        assert(false);
    }

    throw logic_error("invalid type");
  }

  llvm::Type *llvm_type(GenContext &ctx, Type *type, long flags, bool addressable = false)
  {
    if (flags & MIR::Local::Reference)
      return llvm_type(ctx, type, true)->getPointerTo();

    return llvm_type(ctx, type, addressable);
  }

  //|///////////////////// alloc ////////////////////////////////////////////
  llvm::Value *alloc(GenContext &ctx, FunctionContext &fx, Type *type, long flags = 0)
  {
    auto alloctype = llvm_type(ctx, type, flags, true);

    auto alloca = ctx.builder.CreateAlloca(alloctype);

    auto align = (flags & MIR::Local::Reference) ? alignof(void*) : alignof_type(type);

    alloca->setAlignment(llvm::Align(align));

    return alloca;
  }

  //|///////////////////// load /////////////////////////////////////////////
  llvm::Value *load(GenContext &ctx, FunctionContext &fx, llvm::Value *src, Type *type, long flags = 0)
  {
    assert(src);

    auto align = (flags & MIR::Local::Reference) ? alignof(void*) : alignof_type(type);

    llvm::Value *value = ctx.builder.CreateAlignedLoad(src->getType()->getPointerElementType(), src, llvm::Align(align));

    if (type == ctx.booltype && !value->getType()->isPointerTy())
      value = ctx.builder.CreateTrunc(value, ctx.builder.getInt1Ty());

    return value;
  }

  //|///////////////////// load /////////////////////////////////////////////
  llvm::Value *load(GenContext &ctx, FunctionContext &fx, MIR::local_t src)
  {
    if (fx.locals[src].alloca && (!fx.locals[src].value || !(fx.mir.locals[src].flags & MIR::Local::Const) || (fx.mir.locals[src].flags & MIR::Local::Reference)))
    {
      fx.locals[src].value = load(ctx, fx, fx.locals[src].alloca, fx.mir.locals[src].type, fx.mir.locals[src].flags);
    }

    return fx.locals[src].value;
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(GenContext &ctx, FunctionContext &fx, llvm::Value *dst, Type *type, llvm::Value *src, long flags = 0)
  {
    auto align = (flags & MIR::Local::Reference) ? alignof(void*) : alignof_type(type);

    if (type == ctx.booltype && !src->getType()->isPointerTy())
      src = ctx.builder.CreateZExt(src, ctx.builder.getInt8Ty());

    assert(dst->getType()->getPointerElementType() == src->getType());

    ctx.builder.CreateAlignedStore(src, dst, llvm::Align(align));
  }

  //|///////////////////// store ////////////////////////////////////////////
  void store(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, llvm::Value *src)
  {
    fx.locals[dst].value = src;

    if (fx.locals[dst].alloca)
    {
      store(ctx, fx, fx.locals[dst].alloca, fx.mir.locals[dst].type, src, fx.mir.locals[dst].flags);
    }
  }

  //|///////////////////// llvm_zero ////////////////////////////////////////
  llvm::Constant *llvm_zero(llvm::Type *type)
  {
    return llvm::Constant::getNullValue(type);
  }

  //|///////////////////// llvm_int /////////////////////////////////////////
  llvm::Constant *llvm_int(llvm::Type *type, uint64_t value)
  {
    return llvm::ConstantInt::get(type, value);
  }

  //|///////////////////// llvm_float ///////////////////////////////////////
  llvm::Constant *llvm_float(llvm::Type *type, double value)
  {
    return llvm::ConstantFP::get(type, value);
  }

  //|///////////////////// llvm_discope /////////////////////////////////////
  llvm::DIFile *llvm_difile(GenContext &ctx, Decl *decl)
  {
    return ctx.di.createFile(get_module(decl)->file(), ctx.current_directory);
  }

  //|///////////////////// llvm_discope /////////////////////////////////////
  llvm::DIScope *llvm_discope(GenContext &ctx, std::variant<Decl*, Stmt*> scope)
  {
    while (scope != std::variant<Decl*, Stmt*>())
    {
      if (auto decl = get_if<Decl*>(&scope); decl && *decl && (*decl)->kind() == Decl::Module)
      {
        return ctx.di.createFile(decl_cast<ModuleDecl>(*decl)->file(), ctx.current_directory);
      }

      scope = std::visit([](auto &v) { return v->owner; }, scope);
    }

    return ctx.diunit;
  }

  //|///////////////////// llvm_ditype //////////////////////////////////////
  llvm::DIType *llvm_ditype(GenContext &ctx, MIR::Local const &local)
  {
    if (local.flags & MIR::Local::Reference)
    {
      return ctx.di.createReferenceType(llvm::dwarf::DW_TAG_reference_type, llvm_ditype(ctx, local.type));
    }

    if (auto j = ctx.ditypes.find(local.type); j != ctx.ditypes.end())
      return j->second;

    llvm::DIType *ditype = nullptr;

    if (is_builtin_type(local.type))
    {
      auto type = type_cast<BuiltinType>(local.type);

      if (is_void_type(type))
        ditype = ctx.di.createUnspecifiedType("void");

      else if (type->is_bool_type())
        ditype = ctx.di.createBasicType(type->name(), sizeof_type(type) * 8, llvm::dwarf::DW_ATE_boolean);

      else if (type->is_char_type())
        ditype = ctx.di.createBasicType(type->name(), sizeof_type(type) * 8, llvm::dwarf::DW_ATE_UTF);

      else if (type->is_int_type())
        ditype = ctx.di.createBasicType(type->name(), sizeof_type(type) * 8, type->is_signed_type() ? llvm::dwarf::DW_ATE_signed : llvm::dwarf::DW_ATE_unsigned);

      else if (type->is_float_type())
        ditype = ctx.di.createBasicType(type->name(), sizeof_type(type) * 8, llvm::dwarf::DW_ATE_float);

      else if (type->kind() == BuiltinType::StringLiteral)
        ditype = ctx.di.createUnspecifiedType("string");

      else if (type->kind() == BuiltinType::PtrLiteral)
        ditype = ctx.di.createNullPtrType();
    }

    if (is_reference_type(local.type))
    {
      ditype = ctx.di.createReferenceType(llvm::dwarf::DW_TAG_reference_type, llvm_ditype(ctx, remove_reference_type(local.type)));
    }

    if (is_pointer_type(local.type))
    {
      ditype = ctx.di.createPointerType(llvm_ditype(ctx, remove_pointer_type(local.type)), sizeof_type(local.type) * 8);
    }

    if (is_const_type(local.type))
    {
      ditype = ctx.di.createQualifiedType(llvm::dwarf::DW_TAG_const_type, llvm_ditype(ctx, remove_const_type(local.type)));
    }

    if (is_qualarg_type(local.type))
    {
      ditype = llvm_ditype(ctx, remove_const_type(local.type));
    }

    if (is_array_type(local.type))
    {
      ditype = ctx.di.createUnspecifiedType("array");
    }

    if (is_struct_type(local.type) || is_lambda_type(local.type))
    {
      auto type = type_cast<TagType>(local.type);
      auto decl = decl_cast<TagDecl>(type->decl);
      auto difile = llvm_difile(ctx, decl);

      auto distruct = ctx.di.createStructType(llvm_discope(ctx, decl), decl->name, difile, decl->loc().lineno, sizeof_type(type) * 8, alignof_type(type) * 8, llvm::DINode::FlagZero, nullptr, ctx.di.getOrCreateArray({}));

      ctx.ditypes.emplace(type, distruct);

      vector<llvm::Metadata*> elements;

      for(size_t index = 0; index < type->fields.size(); ++index)
      {
        auto vardecl = decl_cast<FieldVarDecl>(type->fieldvars[index]);

        auto field = ctx.di.createMemberType(distruct, vardecl->name, difile, vardecl->loc().lineno, sizeof_type(type->fields[index]) * 8, alignof_type(type->fields[index]) * 8, offsetof_type(type, index) * 8, llvm::DINode::FlagZero, llvm_ditype(ctx, type->fields[index]));

        elements.push_back(field);
      }

      ctx.di.replaceArrays(distruct, ctx.di.getOrCreateArray(elements));

      ditype = distruct;
    }

    if (is_tuple_type(local.type))
    {
      ditype = ctx.di.createUnspecifiedType("tuple");
    }

    if (is_enum_type(local.type))
    {
      ditype = ctx.di.createUnspecifiedType("enum");
    }

    if (is_function_type(local.type))
    {
      ditype = ctx.di.createUnspecifiedType("function");
    }

    assert(ditype);

    ctx.ditypes.emplace(local.type, ditype);

    return ditype;
  }

  //|///////////////////// llvm_diloc ///////////////////////////////////////
  llvm::DILocation *llvm_diloc(GenContext &ctx, FunctionContext &fx, SourceLocation loc)
  {
    return llvm::DILocation::get(ctx.context, loc.lineno, loc.charpos, fx.discopes.back());
  }

  //|///////////////////// llvm_constant ////////////////////////////////////
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, BoolLiteralExpr *literal, bool addressable = false)
  {
    if (is_bool_type(type))
    {
      return llvm_int(llvm_type(ctx, type, addressable), literal->value());
    }
    else
    {
      ctx.diag.error("literal type incompatible with required type", fx.fn, literal->loc());
      ctx.diag << "  literal type: 'bool' required type: '" << *type << "'\n";
      return nullptr;
    }
  }

  //|///////////////////// llvm_constant ////////////////////////////////////
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, CharLiteralExpr *literal)
  {
    if (is_char_type(type))
    {
      if (!literal_valid(type_cast<BuiltinType>(type)->kind(), literal->value()))
      {
        ctx.diag.error("literal value out of range for required type", fx.fn, literal->loc());
        ctx.diag << "  literal value: '" << literal->value() << "' required type: '" << *type << "'\n";
        return nullptr;
      }

      return llvm_int(llvm_type(ctx, type), literal->value().sign * literal->value().value);
    }
    else
    {
      ctx.diag.error("literal type incompatible with required type", fx.fn, literal->loc());
      ctx.diag << "  literal type: '#char' required type: '" << *type << "'\n";
      return nullptr;
    }
  }

  //|///////////////////// llvm_constant ////////////////////////////////////
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, IntLiteralExpr *literal)
  {
    if (is_enum_type(type))
    {
      type = type_cast<TagType>(type)->fields[0];
    }

    if (is_int_type(type) || is_char_type(type))
    {
      if (!literal_valid(type_cast<BuiltinType>(type)->kind(), literal->value()))
      {
        ctx.diag.error("literal value out of range for required type", fx.fn, literal->loc());
        ctx.diag << "  literal value: '" << literal->value() << "' required type: '" << *type << "'\n";
        return nullptr;
      }

      return llvm_int(llvm_type(ctx, type), literal->value().sign * literal->value().value);
    }
    else if (is_pointer_type(type))
    {
      auto value = llvm_int(ctx.builder.getInt64Ty(), literal->value().sign * literal->value().value);

      return llvm::ConstantExpr::getIntToPtr(value, llvm_type(ctx, type));
    }
    else
    {
      ctx.diag.error("literal type incompatible with required type", fx.fn, literal->loc());
      ctx.diag << "  literal type: '#int' required type: '" << *type << "'\n";
      return nullptr;
    }
  }

  //|///////////////////// llvm_constant ////////////////////////////////////
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, FloatLiteralExpr *literal)
  {
    if (is_float_type(type))
    {
      if (!literal_valid(type_cast<BuiltinType>(type)->kind(), literal->value()))
      {
        ctx.diag.error("literal value out of range for required type", fx.fn, literal->loc());
        ctx.diag << "  literal value: '" << literal->value() << "' required type: '" << *type << "'\n";
        return nullptr;
      }

      return llvm_float(llvm_type(ctx, type), literal->value().value);
    }
    else
    {
      ctx.diag.error("literal type incompatible with required type", fx.fn, literal->loc());
      ctx.diag << "  literal type: '#float' required type: '" << *type << "'\n";
      return nullptr;
    }
  }

  //|///////////////////// llvm_constant ////////////////////////////////////
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, PointerLiteralExpr *literal)
  {
    if (is_pointer_type(type))
    {
      return llvm_zero(llvm_type(ctx, type));
    }
    else
    {
      ctx.diag.error("literal type incompatible with required type", fx.fn, literal->loc());
      ctx.diag << "  literal type: '#ptr' required type: '" << *type << "'\n";
      return nullptr;
    }
  }

  //|///////////////////// llvm_constant ////////////////////////////////////
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, StringLiteralExpr *literal)
  {
    if (is_string_type(type))
    {
      auto len = ctx.builder.getInt64(literal->value().size());
      auto str = ctx.builder.CreateGlobalStringPtr(literal->value());

      vector<llvm::Constant*> elements = { len, str };

      return llvm::ConstantStruct::get(llvm::cast<llvm::StructType>(llvm_type(ctx, type)), elements);
    }
    else
    {
      ctx.diag.error("literal type incompatible with required type", fx.fn, literal->loc());
      ctx.diag << "  literal type: '#string' required type: '" << *type << "'\n";
      return nullptr;
    }
  }

  //|///////////////////// llvm_constant ////////////////////////////////////
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, ArrayLiteralExpr *literal)
  {
    if (is_array_type(type))
    {
      vector<llvm::Constant*> elements;

      auto elemtype = type_cast<ArrayType>(type)->type;
      auto arraylen = array_len(type_cast<ArrayType>(type));

      for(auto &element : literal->elements)
      {
        elements.push_back(llvm_constant(ctx, fx, elemtype, element));
      }

      if (any_of(elements.begin(), elements.end(), [](auto &k) { return !k; }))
        return nullptr;


      for(size_t i = elements.size(); i < arraylen; ++i)
        elements.push_back(elements.back());

      return llvm::ConstantArray::get(llvm::cast<llvm::ArrayType>(llvm_type(ctx, type)), elements);
    }
    else
    {
      ctx.diag.error("literal type incompatible with required type", fx.fn, literal->loc());
      ctx.diag << "  literal type: '#array' required type: '" << *type << "'\n";
      return nullptr;
    }
  }

  //|///////////////////// llvm_constant ////////////////////////////////////
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, CompoundLiteralExpr *literal)
  {
    if (is_compound_type(type))
    {
      vector<llvm::Constant*> elements;

      auto &fields = type_cast<CompoundType>(type)->fields;

      assert(fields.size() == literal->fields.size());

      for(size_t i = 0; i < fields.size(); ++i)
      {
        elements.push_back(llvm_constant(ctx, fx, fields[i], literal->fields[i]));
      }

      if (any_of(elements.begin(), elements.end(), [](auto &k) { return !k; }))
        return nullptr;

      return llvm::ConstantStruct::get(llvm::cast<llvm::StructType>(llvm_type(ctx, type)), elements);
    }
    else
    {
      ctx.diag.error("literal type incompatible with required type", fx.fn, literal->loc());
      ctx.diag << "  literal type: '#struct' required type: '" << *type << "'\n";
      return nullptr;
    }
  }

  //|///////////////////// llvm_constant ////////////////////////////////////
  llvm::Constant *llvm_constant(GenContext &ctx, FunctionContext &fx, Type *type, Expr *literal)
  {
    switch(literal->kind())
    {
      case Expr::VoidLiteral:
        return llvm_zero(llvm_type(ctx, type, true));

      case Expr::BoolLiteral:
        return llvm_constant(ctx, fx, type, expr_cast<BoolLiteralExpr>(literal), true);

      case Expr::CharLiteral:
        return llvm_constant(ctx, fx, type, expr_cast<CharLiteralExpr>(literal));

      case Expr::IntLiteral:
        return llvm_constant(ctx, fx, type, expr_cast<IntLiteralExpr>(literal));

      case Expr::FloatLiteral:
        return llvm_constant(ctx, fx, type, expr_cast<FloatLiteralExpr>(literal));

      case Expr::PtrLiteral:
        return llvm_constant(ctx, fx, type, expr_cast<PointerLiteralExpr>(literal));

      case Expr::StringLiteral:
        return llvm_constant(ctx, fx, type, expr_cast<StringLiteralExpr>(literal));

      case Expr::ArrayLiteral:
        return llvm_constant(ctx, fx, type, expr_cast<ArrayLiteralExpr>(literal));

      case Expr::CompoundLiteral:
        return llvm_constant(ctx, fx, type, expr_cast<CompoundLiteralExpr>(literal));

      default:
        assert(false);
    }

    throw logic_error("invalid literal expression");
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, VoidLiteralExpr *literal)
  {
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, BoolLiteralExpr *literal)
  {
    if (!is_concrete_type(fx.mir.locals[dst].type))
    {
      ctx.diag.error("unresolved literal type", fx.fn, literal->loc());
      return;
    }

    if (auto value = llvm_constant(ctx, fx, fx.mir.locals[dst].type, literal))
    {
      store(ctx, fx, dst, value);
    }
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, CharLiteralExpr *literal)
  {
    if (!is_concrete_type(fx.mir.locals[dst].type))
    {
      ctx.diag.error("unresolved literal type", fx.fn, literal->loc());
      return;
    }

    if (auto value = llvm_constant(ctx, fx, fx.mir.locals[dst].type, literal))
    {
      store(ctx, fx, dst, value);
    }
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, IntLiteralExpr *literal)
  {
    if (!is_concrete_type(fx.mir.locals[dst].type))
    {
      ctx.diag.error("unresolved literal type", fx.fn, literal->loc());
      return;
    }

    if (auto value = llvm_constant(ctx, fx, fx.mir.locals[dst].type, literal))
    {
      store(ctx, fx, dst, value);
    }
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, FloatLiteralExpr *literal)
  {
    if (!is_concrete_type(fx.mir.locals[dst].type))
    {
      ctx.diag.error("unresolved literal type", fx.fn, literal->loc());
      return;
    }

    if (auto value = llvm_constant(ctx, fx, fx.mir.locals[dst].type, literal))
    {
      store(ctx, fx, dst, value);
    }
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, PointerLiteralExpr *literal)
  {
    if (!is_concrete_type(fx.mir.locals[dst].type))
    {
      ctx.diag.error("unresolved literal type", fx.fn, literal->loc());
      return;
    }

    if (auto value = llvm_constant(ctx, fx, fx.mir.locals[dst].type, literal))
    {
      store(ctx, fx, dst, value);
    }
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, StringLiteralExpr *literal)
  {
    if (!is_concrete_type(fx.mir.locals[dst].type))
    {
      ctx.diag.error("unresolved literal type", fx.fn, literal->loc());
      return;
    }

    if (auto value = llvm_constant(ctx, fx, fx.mir.locals[dst].type, literal))
    {
      store(ctx, fx, dst, value);
    }
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, ArrayLiteralExpr *literal)
  {
    if (!is_concrete_type(fx.mir.locals[dst].type))
    {
      ctx.diag.error("unresolved literal type", fx.fn, literal->loc());
      return;
    }

    assert(fx.mir.locals[dst].flags & MIR::Local::Const);

    if (auto value = llvm_constant(ctx, fx, fx.mir.locals[dst].type, literal))
    {
      auto global = new llvm::GlobalVariable(ctx.module, value->getType(), true, llvm::GlobalValue::PrivateLinkage, value);

      global->setAlignment(llvm::Align(16));

      if (fx.locals[dst].alloca)
        llvm::cast<llvm::AllocaInst>(fx.locals[dst].alloca)->eraseFromParent();

      fx.locals[dst].alloca = global;
    }
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, CompoundLiteralExpr *literal)
  {    
    if (!is_concrete_type(fx.mir.locals[dst].type))
    {
      ctx.diag.error("unresolved literal type", fx.fn, literal->loc());
      return;
    }

    assert(fx.mir.locals[dst].flags & MIR::Local::Const);

    if (auto value = llvm_constant(ctx, fx, fx.mir.locals[dst].type, literal))
    {
      auto global = new llvm::GlobalVariable(ctx.module, value->getType(), true, llvm::GlobalValue::PrivateLinkage, value);

      global->setAlignment(llvm::Align(16));

      if (fx.locals[dst].alloca)
        llvm::cast<llvm::AllocaInst>(fx.locals[dst].alloca)->eraseFromParent();

      fx.locals[dst].alloca = global;
    }
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::ConstantData const &constant)
  {
    std::visit([&](auto &v) { codegen_constant(ctx, fx, dst, v); }, constant);
  }

  //|///////////////////// codegen_constant /////////////////////////////////
  void codegen_constant(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::FunctionData const &constant)
  {
    auto &[pointee, loc] = constant;

    assert(ctx.functions.find(pointee) != ctx.functions.end());

    store(ctx, fx, dst, ctx.functions[pointee]);
  }

  //|///////////////////// codegen_fields ///////////////////////////////////
  llvm::Value *codegen_fields(GenContext &ctx, FunctionContext &fx, MIR::local_t arg, vector<MIR::RValue::Field> const &fields)
  {
    auto base = fx.locals[arg].alloca;
    auto index = vector<llvm::Value*>{ ctx.builder.getInt32(0) };

    if (fields[0].op == MIR::RValue::Val)
    {
      base = load(ctx, fx, arg);
    }

    index.push_back(ctx.builder.getInt32(fields[0].index));

    for(size_t i = 1; i < fields.size(); ++i)
    {
      if (fields[i].op == MIR::RValue::Val)
      {
        base = load(ctx, fx, ctx.builder.CreateInBoundsGEP(base, index), ctx.voidtype, MIR::Local::Reference);
        index.resize(1);
      }

      index.push_back(ctx.builder.getInt32(fields[i].index));
    }

    return ctx.builder.CreateInBoundsGEP(base, index);
  }

  //|///////////////////// codegen_cpy_value ////////////////////////////////
  void codegen_cpy_value(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    if (fields.size() != 0)
    {
      auto src = codegen_fields(ctx, fx, arg, fields);

      store(ctx, fx, dst, load(ctx, fx, src, fx.mir.locals[dst].type, fx.mir.locals[dst].flags));
    }
    else
    {
      store(ctx, fx, dst, load(ctx, fx, arg));
    }
  }

  //|///////////////////// codegen_ref_value ////////////////////////////////
  void codegen_ref_value(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    if (fields.size() != 0)
    {
      auto src = codegen_fields(ctx, fx, arg, fields);

      store(ctx, fx, dst, src);
    }
    else
    {
      store(ctx, fx, dst, fx.locals[arg].alloca);
    }
  }

  //|///////////////////// codegen_fer_value ////////////////////////////////
  void codegen_fer_value(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    if (fields.size() != 0)
    {
      auto ptr = codegen_fields(ctx, fx, arg, fields);
      auto src = load(ctx, fx, ptr, fx.mir.locals[dst].type, MIR::Local::Reference);

      store(ctx, fx, dst, load(ctx, fx, src, fx.mir.locals[dst].type, fx.mir.locals[dst].flags));
    }
    else
    {
      store(ctx, fx, dst, load(ctx, fx, load(ctx, fx, arg), fx.mir.locals[dst].type, fx.mir.locals[dst].flags));
    }
  }

  //|///////////////////// codegen_variable /////////////////////////////////
  void codegen_variable(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::VariableData const &variable)
  {
    auto &[op, arg, fields, loc] = variable;

    if (fx.mir.locals[dst].zerosized())
      return;

    switch(op)
    {
      case MIR::RValue::Val:
        codegen_cpy_value(ctx, fx, dst, variable);
        break;

      case MIR::RValue::Ref:
        codegen_ref_value(ctx, fx, dst, variable);
        break;

      case MIR::RValue::Fer:
        codegen_fer_value(ctx, fx, dst, variable);
        break;

      case MIR::RValue::Idx:
        assert(false);
        break;
    }
  }

  //|///////////////////// assert ///////////////////////////////////////////
  void codegen_assert_div0(GenContext &ctx, FunctionContext &fx, llvm::Value *value)
  {
    ctx.builder.CreateCall(ctx.assert_div0, { value } );
  }

  //|///////////////////// assert ///////////////////////////////////////////
  void codegen_assert_carry(GenContext &ctx, FunctionContext &fx, llvm::Value *value)
  {
    ctx.builder.CreateCall(ctx.assert_carry, { value } );
  }

  //|///////////////////// assert ///////////////////////////////////////////
  void codegen_assert_deref(GenContext &ctx, FunctionContext &fx, llvm::Value *value)
  {
    ctx.builder.CreateCall(ctx.assert_deref, { value } );
  }

  //|///////////////////// checked //////////////////////////////////////////
  llvm::Value *codegen_checked(GenContext &ctx, FunctionContext &fx, llvm::Intrinsic::ID fn, llvm::Value *lhs, llvm::Value *rhs)
  {
    auto value = ctx.builder.CreateBinaryIntrinsic(fn, lhs, rhs);

    codegen_assert_carry(ctx, fx, ctx.builder.CreateExtractValue(value, 1));

    return ctx.builder.CreateExtractValue(value, 0);
  }

  //|///////////////////// unary_arithmetic /////////////////////////////////
  void codegen_builtin_unary_arithmetic(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);

    if (lhscat == TypeCategory::Bool)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::Not:
          result = ctx.builder.CreateNot(lhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::UnsignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::Plus:
          result = lhs;
          break;

        case Builtin::Minus:
          result = ctx.builder.CreateNeg(lhs);
          break;

        case Builtin::Not:
          result = ctx.builder.CreateNot(lhs);
          break;

        case Builtin::abs:
          result = lhs;
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

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::SignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::Plus:
          result = lhs;
          break;

        case Builtin::Minus:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::ssub_with_overflow, llvm_zero(lhs->getType()), lhs);
          else
            result = ctx.builder.CreateNeg(lhs);
          break;

        case Builtin::Not:
          result = ctx.builder.CreateNot(lhs);
          break;

        case Builtin::abs:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
          {
            if (auto constant = llvm::dyn_cast<llvm::ConstantInt>(lhs); !constant || constant->isMinValue(true))
              codegen_assert_carry(ctx, fx, ctx.builder.CreateICmpEQ(lhs, llvm_int(lhs->getType(), ~0ull << (llvm::cast<llvm::IntegerType>(lhs->getType())->getBitWidth() - 1))));
          }
          result = ctx.builder.CreateSelect(ctx.builder.CreateICmpSLT(lhs, llvm_zero(lhs->getType())), ctx.builder.CreateNeg(lhs), lhs);
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

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::FloatingPoint)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::Plus:
          result = lhs;
          break;

        case Builtin::Minus:
          result = ctx.builder.CreateFNeg(lhs);
          break;

        case Builtin::abs:
          result = ctx.builder.CreateUnaryIntrinsic(llvm::Intrinsic::fabs, lhs);
          break;

        case Builtin::floor:
          result = ctx.builder.CreateUnaryIntrinsic(llvm::Intrinsic::floor, lhs);
          break;

        case Builtin::ceil:
          result = ctx.builder.CreateUnaryIntrinsic(llvm::Intrinsic::ceil, lhs);
          break;

        case Builtin::round:
          result = ctx.builder.CreateUnaryIntrinsic(llvm::Intrinsic::round, lhs);
          break;

        case Builtin::trunc:
          result = ctx.builder.CreateUnaryIntrinsic(llvm::Intrinsic::trunc, lhs);
          break;

        case Builtin::sqrt:
          result = ctx.builder.CreateUnaryIntrinsic(llvm::Intrinsic::sqrt, lhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, dst, result);
    }
    else
    {
      ctx.diag.error("invalid unary arithmetic arguments", fx.fn, loc);
      ctx.diag << "  operand type: '" << *fx.mir.locals[args[0]].type << "'\n";
    }
  }

  //|///////////////////// unary_arithmetic_assign //////////////////////////
  void codegen_builtin_unary_arithmetic_assign(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    assert(fx.mir.locals[args[0]].flags & MIR::Local::Reference);

    auto lhs = load(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);

    if (lhscat == TypeCategory::UnsignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::PreInc:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::uadd_with_overflow, lhs, llvm_int(lhs->getType(), 1));
          else
            result = ctx.builder.CreateAdd(lhs, llvm_int(lhs->getType(), 1));
          break;

        case Builtin::PreDec:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::usub_with_overflow, lhs, llvm_int(lhs->getType(), 1));
          else
            result = ctx.builder.CreateSub(lhs, llvm_int(lhs->getType(), 1));
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else if (lhscat == TypeCategory::SignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::PreInc:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::sadd_with_overflow, lhs, llvm_int(lhs->getType(), 1));
          else
            result = ctx.builder.CreateAdd(lhs, llvm_int(lhs->getType(), 1));
          break;

        case Builtin::PreDec:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::ssub_with_overflow, lhs, llvm_int(lhs->getType(), 1));
          else
            result = ctx.builder.CreateSub(lhs, llvm_int(lhs->getType(), 1));
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else if (lhscat == TypeCategory::FloatingPoint)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::PreInc:
          result = ctx.builder.CreateFAdd(lhs, llvm::ConstantFP::get(lhs->getType(), 1));
          break;

        case Builtin::PreDec:
          result = ctx.builder.CreateFAdd(lhs, llvm::ConstantFP::get(lhs->getType(), -1));
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else if (lhscat == TypeCategory::Pointer)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::PreInc:
          result = ctx.builder.CreateInBoundsGEP(lhs, llvm_int(ctx.builder.getInt32Ty(), 1));
          break;

        case Builtin::PreDec:
          result = ctx.builder.CreateInBoundsGEP(lhs, llvm_int(ctx.builder.getInt32Ty(), -1));
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else
    {
      ctx.diag.error("invalid unary arithmetic assign arguments", fx.fn, loc);
      ctx.diag << "  operand type: '" << *fx.mir.locals[args[0]].type << "'\n";
    }

    store(ctx, fx, dst, fx.locals[args[0]].value);
  }

  //|///////////////////// binary_arithmetic ////////////////////////////////
  void codegen_builtin_binary_arithmetic(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);
    auto rhs = load(ctx, fx, args[1]);
    auto rhscat = type_category(fx.mir.locals[args[1]].type);

    if (lhscat == TypeCategory::Bool && rhscat == TypeCategory::Bool)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::And:
          result = ctx.builder.CreateAnd(lhs, rhs);
          break;

        case Builtin::Or:
          result = ctx.builder.CreateOr(lhs, rhs);
          break;

        case Builtin::Xor:
          result = ctx.builder.CreateXor(lhs, rhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::UnsignedInteger && rhscat == TypeCategory::UnsignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::Add:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::uadd_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNUWAdd(lhs, rhs);
          break;

        case Builtin::Sub:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::usub_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNUWSub(lhs, rhs);
          break;

        case Builtin::Div:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
          {
            if (auto constant = llvm::dyn_cast<llvm::Constant>(rhs); !constant || constant->isZeroValue())
              codegen_assert_div0(ctx, fx, ctx.builder.CreateICmpEQ(rhs, llvm_zero(rhs->getType())));
          }
          result = ctx.builder.CreateUDiv(lhs, rhs);
          break;

        case Builtin::Mul:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::umul_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNUWMul(lhs, rhs);
          break;

        case Builtin::Rem:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
          {
            if (auto constant = llvm::dyn_cast<llvm::Constant>(rhs); !constant || constant->isZeroValue())
              codegen_assert_div0(ctx, fx, ctx.builder.CreateICmpEQ(rhs, llvm_zero(rhs->getType())));
          }
          result = ctx.builder.CreateURem(lhs, rhs);
          break;

        case Builtin::And:
          result = ctx.builder.CreateAnd(lhs, rhs);
          break;

        case Builtin::Or:
          result = ctx.builder.CreateOr(lhs, rhs);
          break;

        case Builtin::Xor:
          result = ctx.builder.CreateXor(lhs, rhs);
          break;

        case Builtin::copysign:
          result = lhs;
          break;

        case Builtin::min:
          result = ctx.builder.CreateSelect(ctx.builder.CreateICmpULT(rhs, lhs), rhs, lhs);
          break;

        case Builtin::max:
          result = ctx.builder.CreateSelect(ctx.builder.CreateICmpULT(lhs, rhs), rhs, lhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::UnsignedInteger && rhscat == TypeCategory::SignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::Shl:
          result = ctx.builder.CreateShl(lhs, ctx.builder.CreateIntCast(rhs, lhs->getType(), true));
          break;

        case Builtin::Shr:
          result = ctx.builder.CreateLShr(lhs, ctx.builder.CreateIntCast(rhs, lhs->getType(), true));
          break;

        default:
          assert(false);
      }

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::SignedInteger && rhscat == TypeCategory::SignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::Add:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::sadd_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNSWAdd(lhs, rhs);
          break;

        case Builtin::Sub:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::ssub_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNSWSub(lhs, rhs);
          break;

        case Builtin::Div:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
          {
            if (auto constant = llvm::dyn_cast<llvm::Constant>(rhs); !constant || constant->isZeroValue())
              codegen_assert_div0(ctx, fx, ctx.builder.CreateICmpEQ(rhs, llvm_zero(rhs->getType())));

            if (auto constant = llvm::dyn_cast<llvm::ConstantInt>(rhs); !constant || constant->isMinusOne())
            {
              auto minusone = llvm_int(rhs->getType(), -1);
              auto minusmin = llvm_int(lhs->getType(), ~0ull << (llvm::cast<llvm::IntegerType>(lhs->getType())->getBitWidth() - 1));
              codegen_assert_carry(ctx, fx, ctx.builder.CreateAnd(ctx.builder.CreateICmpEQ(lhs, minusmin), ctx.builder.CreateICmpEQ(rhs, minusone)));
            }
          }
          result = ctx.builder.CreateSDiv(lhs, rhs);
          break;

        case Builtin::Mul:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::smul_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNSWMul(lhs, rhs);
          break;

        case Builtin::Rem:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
          {
            if (auto constant = llvm::dyn_cast<llvm::Constant>(rhs); !constant || constant->isZeroValue())
              codegen_assert_div0(ctx, fx, ctx.builder.CreateICmpEQ(rhs, llvm_zero(rhs->getType())));
          }
          result = ctx.builder.CreateSRem(lhs, rhs);
          break;

        case Builtin::Shl:
          result = ctx.builder.CreateShl(lhs, ctx.builder.CreateIntCast(rhs, lhs->getType(), true));
          break;

        case Builtin::Shr:
          result = ctx.builder.CreateAShr(lhs, ctx.builder.CreateIntCast(rhs, lhs->getType(), true));
          break;

        case Builtin::And:
          result = ctx.builder.CreateAnd(lhs, rhs);
          break;

        case Builtin::Or:
          result = ctx.builder.CreateOr(lhs, rhs);
          break;

        case Builtin::Xor:
          result = ctx.builder.CreateXor(lhs, rhs);
          break;

        case Builtin::copysign: {
          auto cmp = ctx.builder.CreateICmpEQ(ctx.builder.CreateICmpSLT(lhs, llvm_zero(lhs->getType())), ctx.builder.CreateICmpSLT(rhs, llvm_zero(rhs->getType())));
          result = ctx.builder.CreateSelect(cmp, lhs, ctx.builder.CreateNeg(lhs));
          break;
        }

        case Builtin::min:
          result = ctx.builder.CreateSelect(ctx.builder.CreateICmpSLT(rhs, lhs), rhs, lhs);
          break;

        case Builtin::max:
          result = ctx.builder.CreateSelect(ctx.builder.CreateICmpSLT(lhs, rhs), rhs, lhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::FloatingPoint && rhscat == TypeCategory::FloatingPoint)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::Add:
          result = ctx.builder.CreateFAdd(lhs, rhs);
          break;

        case Builtin::Sub:
          result = ctx.builder.CreateFSub(lhs, rhs);
          break;

        case Builtin::Div:
          result = ctx.builder.CreateFDiv(lhs, rhs);
          break;

        case Builtin::Mul:
          result = ctx.builder.CreateFMul(lhs, rhs);
          break;

        case Builtin::Rem:
          result = ctx.builder.CreateFRem(lhs, rhs);
          break;

        case Builtin::copysign:
          result = ctx.builder.CreateBinaryIntrinsic(llvm::Intrinsic::copysign, lhs, rhs);
          break;

        case Builtin::min:
          result = ctx.builder.CreateSelect(ctx.builder.CreateFCmpOLT(rhs, lhs), rhs, lhs);
          break;

        case Builtin::max:
          result = ctx.builder.CreateSelect(ctx.builder.CreateFCmpOLT(lhs, rhs), rhs, lhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::Pointer && (rhscat == TypeCategory::SignedInteger || rhscat == TypeCategory::UnsignedInteger))
    {
      llvm::Value *result;

      if (remove_pointer_type(fx.mir.locals[args[0]].type)->flags & Type::ZeroSized)
      {
        ctx.diag.error("zero sized type", fx.fn, loc);
        return;
      }

      switch(callee.fn->builtin)
      {
        case Builtin::OffsetAdd:
          result = ctx.builder.CreateInBoundsGEP(lhs, rhs);
          break;

        case Builtin::OffsetSub:
          result = ctx.builder.CreateInBoundsGEP(lhs, ctx.builder.CreateNeg(rhs));
          break;

        default:
          assert(false);
      }

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::Pointer && rhscat == TypeCategory::Pointer)
    {
      auto size = sizeof_type(remove_pointer_type(fx.mir.locals[args[0]].type));

      if (size == 0)
      {
        ctx.diag.error("zero sized type", fx.fn, loc);
        return;
      }

      assert(callee.fn->builtin == Builtin::Difference);

      auto i = ctx.builder.CreatePointerCast(lhs, ctx.builder.getInt64Ty());
      auto j = ctx.builder.CreatePointerCast(rhs, ctx.builder.getInt64Ty());

      if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
        codegen_assert_carry(ctx, fx, ctx.builder.CreateICmpULT(i, j));

      auto result = ctx.builder.CreateNUWSub(i, j);

      if (size != 1)
      {
        result = ctx.builder.CreateExactUDiv(result, ctx.builder.getInt64(size));
      }

      store(ctx, fx, dst, result);
    }
    else
    {
      ctx.diag.error("invalid binary arithmetic arguments", fx.fn, loc);
      ctx.diag << "  lhs type: '" << *fx.mir.locals[args[0]].type << "' rhs type: '" << *fx.mir.locals[args[1]].type << "'\n";
    }
  }

  //|///////////////////// binary_arithmetic_carry //////////////////////////
  void codegen_builtin_binary_arithmetic_carry(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);
    auto rhs = load(ctx, fx, args[1]);
    auto rhscat = type_category(fx.mir.locals[args[1]].type);

    if (lhscat == TypeCategory::UnsignedInteger && rhscat == TypeCategory::UnsignedInteger)
    {
      llvm::Value *result, *lo, *hi;

      auto width = llvm::cast<llvm::IntegerType>(lhs->getType())->getBitWidth();

      switch(callee.fn->builtin)
      {
        case Builtin::AddCarry:
          result = ctx.builder.CreateBinaryIntrinsic(llvm::Intrinsic::uadd_with_overflow, lhs, rhs);
          lo = ctx.builder.CreateExtractValue(result, 0);
          hi = ctx.builder.CreateIntCast(ctx.builder.CreateExtractValue(result, 1), lhs->getType(), false);
          break;

        case Builtin::SubCarry:
          result = ctx.builder.CreateBinaryIntrinsic(llvm::Intrinsic::usub_with_overflow, lhs, rhs);
          lo = ctx.builder.CreateExtractValue(result, 0);
          hi = ctx.builder.CreateIntCast(ctx.builder.CreateExtractValue(result, 1), lhs->getType(), false);
          break;

        case Builtin::MulCarry:
          result = ctx.builder.CreateMul(ctx.builder.CreateIntCast(lhs, ctx.builder.getInt128Ty(), false), ctx.builder.CreateIntCast(rhs, ctx.builder.getInt128Ty(), false));
          hi = ctx.builder.CreateIntCast(ctx.builder.CreateLShr(result, ctx.builder.getIntN(128, width)), lhs->getType(), false);
          lo = ctx.builder.CreateIntCast(ctx.builder.CreateAnd(result, ctx.builder.getIntN(128, 0xFFFFFFFFFFFFFFFF >> (64 - width))), lhs->getType(), false);
          break;

        default:
          assert(false);
      }

      auto insert0 = llvm::UndefValue::get(llvm_type(ctx, fx.mir.locals[dst].type));
      auto insert1 = ctx.builder.CreateInsertValue(insert0, lo, 0);
      auto insert2 = ctx.builder.CreateInsertValue(insert1, hi, 1);

      store(ctx, fx, dst, insert2);
    }
    else if (lhscat == TypeCategory::SignedInteger && rhscat == TypeCategory::SignedInteger)
    {
      llvm::Value *result, *lo, *hi;

      auto width = llvm::cast<llvm::IntegerType>(lhs->getType())->getBitWidth();

      switch(callee.fn->builtin)
      {
        case Builtin::AddCarry:
          result = ctx.builder.CreateBinaryIntrinsic(llvm::Intrinsic::sadd_with_overflow, lhs, rhs);
          lo = ctx.builder.CreateExtractValue(result, 0);
          hi = ctx.builder.CreateIntCast(ctx.builder.CreateExtractValue(result, 1), lhs->getType(), false);
          break;

        case Builtin::SubCarry:
          result = ctx.builder.CreateBinaryIntrinsic(llvm::Intrinsic::ssub_with_overflow, lhs, rhs);
          lo = ctx.builder.CreateExtractValue(result, 0);
          hi = ctx.builder.CreateIntCast(ctx.builder.CreateExtractValue(result, 1), lhs->getType(), false);
          break;

        case Builtin::MulCarry:
          result = ctx.builder.CreateMul(ctx.builder.CreateIntCast(lhs, ctx.builder.getInt128Ty(), true), ctx.builder.CreateIntCast(rhs, ctx.builder.getInt128Ty(), true));
          hi = ctx.builder.CreateIntCast(ctx.builder.CreateAShr(result, ctx.builder.getIntN(128, width)), lhs->getType(), false);
          lo = ctx.builder.CreateIntCast(ctx.builder.CreateAnd(result, ctx.builder.getIntN(128, 0xFFFFFFFFFFFFFFFF >> (64 - width))), lhs->getType(), false);
          break;

        default:
          assert(false);
      }

      auto insert0 = llvm::UndefValue::get(llvm_type(ctx, fx.mir.locals[dst].type));
      auto insert1 = ctx.builder.CreateInsertValue(insert0, lo, 0);
      auto insert2 = ctx.builder.CreateInsertValue(insert1, hi, 1);

      store(ctx, fx, dst, insert2);
    }
    else
    {
      ctx.diag.error("invalid binary arithmetic arguments", fx.fn, loc);
      ctx.diag << "  lhs type: '" << *fx.mir.locals[args[0]].type << "' rhs type: '" << *fx.mir.locals[args[1]].type << "'\n";
    }
  }

  //|///////////////////// binary_arithmetic_assign /////////////////////////
  void codegen_builtin_binary_arithmetic_assign(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    assert(fx.mir.locals[args[0]].flags & MIR::Local::Reference);

    auto lhs = load(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);
    auto rhs = load(ctx, fx, args[1]);
    auto rhscat = type_category(fx.mir.locals[args[1]].type);

    if (lhscat == TypeCategory::Bool && rhscat == TypeCategory::Bool)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::AndAssign:
          result = ctx.builder.CreateAnd(lhs, rhs);
          break;

        case Builtin::OrAssign:
          result = ctx.builder.CreateOr(lhs, rhs);
          break;

        case Builtin::XorAssign:
          result = ctx.builder.CreateXor(lhs, rhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else if (lhscat == TypeCategory::UnsignedInteger && rhscat == TypeCategory::UnsignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::AddAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::uadd_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNUWAdd(lhs, rhs);
          break;

        case Builtin::SubAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::usub_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNUWSub(lhs, rhs);
          break;

        case Builtin::DivAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
          {
            if (auto constant = llvm::dyn_cast<llvm::Constant>(rhs); !constant || constant->isZeroValue())
              codegen_assert_div0(ctx, fx, ctx.builder.CreateICmpEQ(rhs, llvm_zero(rhs->getType())));
          }
          result = ctx.builder.CreateUDiv(lhs, rhs);
          break;

        case Builtin::MulAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::umul_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNUWMul(lhs, rhs);
          break;

        case Builtin::RemAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
          {
            if (auto constant = llvm::dyn_cast<llvm::Constant>(rhs); !constant || constant->isZeroValue())
              codegen_assert_div0(ctx, fx, ctx.builder.CreateICmpEQ(rhs, llvm_zero(rhs->getType())));
          }
          result = ctx.builder.CreateURem(lhs, rhs);
          break;

        case Builtin::AndAssign:
          result = ctx.builder.CreateAnd(lhs, rhs);
          break;

        case Builtin::OrAssign:
          result = ctx.builder.CreateOr(lhs, rhs);
          break;

        case Builtin::XorAssign:
          result = ctx.builder.CreateXor(lhs, rhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else if (lhscat == TypeCategory::UnsignedInteger && rhscat == TypeCategory::SignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::ShlAssign:
          result = ctx.builder.CreateShl(lhs, ctx.builder.CreateIntCast(rhs, lhs->getType(), true));
          break;

        case Builtin::ShrAssign:
          result = ctx.builder.CreateLShr(lhs, ctx.builder.CreateIntCast(rhs, lhs->getType(), true));
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else if (lhscat == TypeCategory::FloatingPoint && rhscat == TypeCategory::FloatingPoint)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::AddAssign:
          result = ctx.builder.CreateFAdd(lhs, rhs);
          break;

        case Builtin::SubAssign:
          result = ctx.builder.CreateFSub(lhs, rhs);
          break;

        case Builtin::DivAssign:
          result = ctx.builder.CreateFDiv(lhs, rhs);
          break;

        case Builtin::MulAssign:
          result = ctx.builder.CreateFMul(lhs, rhs);
          break;

        case Builtin::RemAssign:
          result = ctx.builder.CreateFRem(lhs, rhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else if (lhscat == TypeCategory::SignedInteger && rhscat == TypeCategory::SignedInteger)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::AddAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::sadd_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNSWAdd(lhs, rhs);
          break;

        case Builtin::SubAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::ssub_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNSWSub(lhs, rhs);
          break;

        case Builtin::DivAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
          {
            if (auto constant = llvm::dyn_cast<llvm::Constant>(rhs); !constant || constant->isZeroValue())
              codegen_assert_div0(ctx, fx, ctx.builder.CreateICmpEQ(rhs, llvm_zero(rhs->getType())));

            if (auto constant = llvm::dyn_cast<llvm::ConstantInt>(rhs); !constant || constant->isMinusOne())
            {
              auto minusone = llvm_int(rhs->getType(), -1);
              auto minusmin = llvm_int(lhs->getType(), ~0ull << (llvm::cast<llvm::IntegerType>(lhs->getType())->getBitWidth() - 1));
              codegen_assert_carry(ctx, fx, ctx.builder.CreateAnd(ctx.builder.CreateICmpEQ(lhs, minusmin), ctx.builder.CreateICmpEQ(rhs, minusone)));
            }
          }
          result = ctx.builder.CreateSDiv(lhs, rhs);
          break;

        case Builtin::MulAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
            result = codegen_checked(ctx, fx, llvm::Intrinsic::smul_with_overflow, lhs, rhs);
          else
            result = ctx.builder.CreateNSWMul(lhs, rhs);
          break;

        case Builtin::RemAssign:
          if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
          {
            if (auto constant = llvm::dyn_cast<llvm::Constant>(rhs); !constant || constant->isZeroValue())
              codegen_assert_div0(ctx, fx, ctx.builder.CreateICmpEQ(rhs, llvm_zero(rhs->getType())));
          }
          result = ctx.builder.CreateSRem(lhs, rhs);
          break;

        case Builtin::ShlAssign:
          result = ctx.builder.CreateShl(lhs, ctx.builder.CreateIntCast(rhs, lhs->getType(), true));
          break;

        case Builtin::ShrAssign:
          result = ctx.builder.CreateAShr(lhs, ctx.builder.CreateIntCast(rhs, lhs->getType(), true));
          break;

        case Builtin::AndAssign:
          result = ctx.builder.CreateAnd(lhs, rhs);
          break;

        case Builtin::OrAssign:
          result = ctx.builder.CreateOr(lhs, rhs);
          break;

        case Builtin::XorAssign:
          result = ctx.builder.CreateXor(lhs, rhs);
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else if (lhscat == TypeCategory::Pointer && (rhscat == TypeCategory::SignedInteger || rhscat == TypeCategory::UnsignedInteger))
    {
      llvm::Value *result;

      if (remove_pointer_type(fx.mir.locals[args[0]].type)->flags & Type::ZeroSized)
      {
        ctx.diag.error("zero sized type", fx.fn, loc);
        return;
      }

      switch(callee.fn->builtin)
      {
        case Builtin::OffsetAddAssign:
          result = ctx.builder.CreateInBoundsGEP(lhs, rhs);
          break;

        case Builtin::OffsetSubAssign:
          result = ctx.builder.CreateInBoundsGEP(lhs, ctx.builder.CreateNeg(rhs));
          break;

        default:
          assert(false);
      }

      store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, result);
    }
    else
    {
      ctx.diag.error("invalid binary arithmetic assign arguments", fx.fn, loc);
      ctx.diag << "  lhs type: '" << *fx.mir.locals[args[0]].type << "' rhs type: '" << *fx.mir.locals[args[1]].type << "'\n";
    }

    store(ctx, fx, dst, fx.locals[args[0]].value);
  }

  //|///////////////////// lnot /////////////////////////////////////////////
  void codegen_builtin_lnot(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    store(ctx, fx, dst, ctx.builder.CreateXor(lhs, ctx.builder.getTrue()));
  }

  //|///////////////////// land /////////////////////////////////////////////
  void codegen_builtin_land(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto rhs = load(ctx, fx, args[0]);

    store(ctx, fx, dst, ctx.builder.CreateAnd(lhs, rhs));
  }

  //|///////////////////// lor //////////////////////////////////////////////
  void codegen_builtin_lor(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto rhs = load(ctx, fx, args[0]);

    store(ctx, fx, dst, ctx.builder.CreateOr(lhs, rhs));
  }

  //|///////////////////// binary_compare ///////////////////////////////////
  void codegen_builtin_binary_compare(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);
    auto rhs = load(ctx, fx, args[1]);
    auto rhscat = type_category(fx.mir.locals[args[1]].type);

    if (lhscat == TypeCategory::Bool && rhscat == TypeCategory::Bool)
    {
      switch(callee.fn->builtin)
      {
        case Builtin::LT:
          store(ctx, fx, dst, ctx.builder.CreateICmpULT(lhs, rhs));
          break;

        case Builtin::GT:
          store(ctx, fx, dst, ctx.builder.CreateICmpUGT(lhs, rhs));
          break;

        case Builtin::LE:
          store(ctx, fx, dst, ctx.builder.CreateICmpULE(lhs, rhs));
          break;

        case Builtin::GE:
          store(ctx, fx, dst, ctx.builder.CreateICmpUGE(lhs, rhs));
          break;

        case Builtin::EQ:
          store(ctx, fx, dst, ctx.builder.CreateICmpEQ(lhs, rhs));
          break;

        case Builtin::NE:
          store(ctx, fx, dst, ctx.builder.CreateICmpNE(lhs, rhs));
          break;

        default:
          assert(false);
      }
    }
    else if (lhscat == TypeCategory::UnsignedInteger && rhscat == TypeCategory::UnsignedInteger)
    {
      switch(callee.fn->builtin)
      {
        case Builtin::LT:
          store(ctx, fx, dst, ctx.builder.CreateICmpULT(lhs, rhs));
          break;

        case Builtin::GT:
          store(ctx, fx, dst, ctx.builder.CreateICmpUGT(lhs, rhs));
          break;

        case Builtin::LE:
          store(ctx, fx, dst, ctx.builder.CreateICmpULE(lhs, rhs));
          break;

        case Builtin::GE:
          store(ctx, fx, dst, ctx.builder.CreateICmpUGE(lhs, rhs));
          break;

        case Builtin::EQ:
          store(ctx, fx, dst, ctx.builder.CreateICmpEQ(lhs, rhs));
          break;

        case Builtin::NE:
          store(ctx, fx, dst, ctx.builder.CreateICmpNE(lhs, rhs));
          break;

        default:
          assert(false);
      }
    }
    else if (lhscat == TypeCategory::SignedInteger && rhscat == TypeCategory::SignedInteger)
    {
      switch(callee.fn->builtin)
      {
        case Builtin::LT:
          store(ctx, fx, dst, ctx.builder.CreateICmpSLT(lhs, rhs));
          break;

        case Builtin::GT:
          store(ctx, fx, dst, ctx.builder.CreateICmpSGT(lhs, rhs));
          break;

        case Builtin::LE:
          store(ctx, fx, dst, ctx.builder.CreateICmpSLE(lhs, rhs));
          break;

        case Builtin::GE:
          store(ctx, fx, dst, ctx.builder.CreateICmpSGE(lhs, rhs));
          break;

        case Builtin::EQ:
          store(ctx, fx, dst, ctx.builder.CreateICmpEQ(lhs, rhs));
          break;

        case Builtin::NE:
          store(ctx, fx, dst, ctx.builder.CreateICmpNE(lhs, rhs));
          break;

        default:
          assert(false);
      }
    }
    else if (lhscat == TypeCategory::FloatingPoint && rhscat == TypeCategory::FloatingPoint)
    {
      switch(callee.fn->builtin)
      {
        case Builtin::LT:
          store(ctx, fx, dst, ctx.builder.CreateFCmpOLT(lhs, rhs));
          break;

        case Builtin::GT:
          store(ctx, fx, dst, ctx.builder.CreateFCmpOGT(lhs, rhs));
          break;

        case Builtin::LE:
          store(ctx, fx, dst, ctx.builder.CreateFCmpOLE(lhs, rhs));
          break;

        case Builtin::GE:
          store(ctx, fx, dst, ctx.builder.CreateFCmpOGE(lhs, rhs));
          break;

        case Builtin::EQ:
          store(ctx, fx, dst, ctx.builder.CreateFCmpOEQ(lhs, rhs));
          break;

        case Builtin::NE:
          store(ctx, fx, dst, ctx.builder.CreateFCmpUNE(lhs, rhs));
          break;

        default:
          assert(false);
      }
    }
    else if (lhscat == TypeCategory::Pointer && rhscat == TypeCategory::Pointer)
    {
      switch(callee.fn->builtin)
      {
        case Builtin::LT:
          store(ctx, fx, dst, ctx.builder.CreateICmpULT(lhs, rhs));
          break;

        case Builtin::GT:
          store(ctx, fx, dst, ctx.builder.CreateICmpUGT(lhs, rhs));
          break;

        case Builtin::LE:
          store(ctx, fx, dst, ctx.builder.CreateICmpULE(lhs, rhs));
          break;

        case Builtin::GE:
          store(ctx, fx, dst, ctx.builder.CreateICmpUGE(lhs, rhs));
          break;

        case Builtin::EQ:
          store(ctx, fx, dst, ctx.builder.CreateICmpEQ(lhs, rhs));
          break;

        case Builtin::NE:
          store(ctx, fx, dst, ctx.builder.CreateICmpNE(lhs, rhs));
          break;

        default:
          assert(false);
      }
    }
    else
    {
      ctx.diag.error("invalid binary compare arguments", fx.fn, loc);
      ctx.diag << "  lhs type: '" << *fx.mir.locals[args[0]].type << "' rhs type: '" << *fx.mir.locals[args[1]].type << "'\n";
    }
  }

  //|///////////////////// cmp //////////////////////////////////////////////
  void codegen_builtin_cmp(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);
    auto rhs = load(ctx, fx, args[1]);
    auto rhscat = type_category(fx.mir.locals[args[1]].type);

    if (lhscat == TypeCategory::Bool && rhscat == TypeCategory::Bool)
    {
       store(ctx, fx, dst, ctx.builder.CreateNSWSub(ctx.builder.CreateIntCast(lhs, ctx.builder.getInt32Ty(), false), ctx.builder.CreateIntCast(rhs, ctx.builder.getInt32Ty(), false)));
    }
    else if (fx.mir.locals[args[0]].type == type(Builtin::Type_U8) && fx.mir.locals[args[1]].type == type(Builtin::Type_U8))
    {
       store(ctx, fx, dst, ctx.builder.CreateNSWSub(ctx.builder.CreateIntCast(lhs, ctx.builder.getInt32Ty(), false), ctx.builder.CreateIntCast(rhs, ctx.builder.getInt32Ty(), false)));
    }
    else if (fx.mir.locals[args[0]].type == type(Builtin::Type_I8) && fx.mir.locals[args[1]].type == type(Builtin::Type_I8))
    {
       store(ctx, fx, dst, ctx.builder.CreateNSWSub(ctx.builder.CreateIntCast(lhs, ctx.builder.getInt32Ty(), true), ctx.builder.CreateIntCast(rhs, ctx.builder.getInt32Ty(), true)));
    }
    else if (lhscat == TypeCategory::UnsignedInteger && rhscat == TypeCategory::UnsignedInteger)
    {
      auto eq = ctx.builder.CreateICmpEQ(lhs, rhs);
      auto lt = ctx.builder.CreateICmpULT(lhs, rhs);
      auto result = ctx.builder.CreateSelect(eq, ctx.builder.getInt32(0), ctx.builder.CreateSelect(lt, ctx.builder.getInt32(-1), ctx.builder.getInt32(1)));

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::SignedInteger && rhscat == TypeCategory::SignedInteger)
    {
       auto eq = ctx.builder.CreateICmpEQ(lhs, rhs);
       auto lt = ctx.builder.CreateICmpSLT(lhs, rhs);
       auto result = ctx.builder.CreateSelect(eq, ctx.builder.getInt32(0), ctx.builder.CreateSelect(lt, ctx.builder.getInt32(-1), ctx.builder.getInt32(1)));

       store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::FloatingPoint && rhscat == TypeCategory::FloatingPoint)
    {
      auto eq = ctx.builder.CreateFCmpOEQ(lhs, rhs);
      auto lt = ctx.builder.CreateFCmpOLT(lhs, rhs);
      auto result = ctx.builder.CreateSelect(eq, ctx.builder.getInt32(0), ctx.builder.CreateSelect(lt, ctx.builder.getInt32(-1), ctx.builder.getInt32(1)));

      store(ctx, fx, dst, result);
    }
    else if (lhscat == TypeCategory::Pointer && rhscat == TypeCategory::Pointer)
    {
      auto eq = ctx.builder.CreateICmpEQ(lhs, rhs);
      auto lt = ctx.builder.CreateICmpULT(lhs, rhs);
      auto result = ctx.builder.CreateSelect(eq, ctx.builder.getInt32(0), ctx.builder.CreateSelect(lt, ctx.builder.getInt32(-1), ctx.builder.getInt32(1)));

      store(ctx, fx, dst, result);
    }
    else
    {
      ctx.diag.error("invalid compare arguments", fx.fn, loc);
      ctx.diag << "  lhs type: '" << *fx.mir.locals[args[0]].type << "' rhs type: '" << *fx.mir.locals[args[1]].type << "'\n";
    }
  }

  //|///////////////////// deref ////////////////////////////////////////////
  void codegen_builtin_deref(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
      codegen_assert_deref(ctx, fx, ctx.builder.CreateICmpEQ(lhs, llvm_zero(lhs->getType())));

    store(ctx, fx, dst, lhs);
  }

  //|///////////////////// range ////////////////////////////////////////////
  void codegen_builtin_range(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto rhs = load(ctx, fx, args[1]);

    auto insert0 = llvm::UndefValue::get(llvm_type(ctx, fx.mir.locals[dst].type));
    auto insert1 = ctx.builder.CreateInsertValue(insert0, lhs, 0);
    auto insert2 = ctx.builder.CreateInsertValue(insert1, rhs, 1);

    store(ctx, fx, dst, insert2);
  }

  //|///////////////////// assign ///////////////////////////////////////////
  void codegen_builtin_assign(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    assert(fx.mir.locals[args[0]].flags & MIR::Local::Reference);

    if (is_void_type(fx.mir.locals[args[1]].type))
      return;

    store(ctx, fx, fx.locals[args[0]].value, fx.mir.locals[args[0]].type, load(ctx, fx, args[1]));

    store(ctx, fx, dst, fx.locals[args[0]].value);
  }

  //|///////////////////// slice_len ////////////////////////////////////////
  void codegen_builtin_slice_len(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    store(ctx, fx, dst, ctx.builder.CreateExtractValue(lhs, 0));
  }

  //|///////////////////// slice_data ///////////////////////////////////////
  void codegen_builtin_slice_data(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    store(ctx, fx, dst, ctx.builder.CreateExtractValue(lhs, 1));
  }

/*
  //|///////////////////// string_slice /////////////////////////////////////
  void codegen_builtin_string_slice(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto src = load(ctx, fx, args[0]);
    auto rng = load(ctx, fx, args[1]);
    auto beg = ctx.builder.CreateExtractValue(rng, 0);
    auto end = ctx.builder.CreateExtractValue(rng, 1);

    if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
    {
      auto len = ctx.builder.CreateExtractValue(src, 0);
      auto beglen = ctx.builder.CreateICmpUGT(beg, len);
      auto endlen = ctx.builder.CreateICmpUGT(end, len);
      auto begend = ctx.builder.CreateICmpUGT(beg, end);

      codegen_assert_carry(ctx, fx, ctx.builder.CreateOr(beglen, ctx.builder.CreateOr(endlen, begend)));
    }

    auto len = ctx.builder.CreateNUWSub(end, beg);
    auto str = ctx.builder.CreateInBoundsGEP(ctx.builder.CreateExtractValue(src, 1), beg);

    auto insert0 = llvm::UndefValue::get(llvm_type(ctx, fx.mir.locals[dst].type));
    auto insert1 = ctx.builder.CreateInsertValue(insert0, len, 0);
    auto insert2 = ctx.builder.CreateInsertValue(insert1, str, 1);

    store(ctx, fx, dst, insert2);
  }
*/

  //|///////////////////// array_data ///////////////////////////////////////
  void codegen_builtin_array_data(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    store(ctx, fx, dst, ctx.builder.CreatePointerCast(lhs, llvm_type(ctx, fx.mir.locals[dst].type)));
  }

  //|///////////////////// array_index //////////////////////////////////////
  void codegen_builtin_array_index(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto rhs = load(ctx, fx, args[1]);

    auto arraylen = array_len(type_cast<ArrayType>(fx.mir.locals[args[0]].type));

    if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
      codegen_assert_carry(ctx, fx, ctx.builder.CreateICmpUGE(rhs, llvm_int(rhs->getType(), arraylen)));

    auto result = ctx.builder.CreateInBoundsGEP(lhs, { ctx.builder.getInt32(0), rhs });

    store(ctx, fx, dst, result);
  }

  //|///////////////////// array_end ////////////////////////////////////////
  void codegen_builtin_array_end(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    auto arraylen = array_len(type_cast<ArrayType>(fx.mir.locals[args[0]].type));

    auto result = ctx.builder.CreateInBoundsGEP(lhs, { ctx.builder.getInt32(0), ctx.builder.getInt32(arraylen) });

    store(ctx, fx, dst, result);
  }

  //|///////////////////// bool /////////////////////////////////////////////
  void codegen_builtin_bool(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    store(ctx, fx, dst, ctx.builder.CreateICmpNE(lhs, llvm_zero(lhs->getType())));
  }

  //|///////////////////// callop ///////////////////////////////////////////
  void codegen_builtin_callop(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto fn = load(ctx, fx, args[0]);
    auto rhs = load(ctx, fx, args[1]);

    vector<llvm::Value*> parms;

    auto paramtuple = type_cast<TupleType>(fx.mir.locals[args[1]].type);

    for(size_t index = 0; index < paramtuple->fields.size(); ++index)
    {
      auto ptr = ctx.builder.CreateInBoundsGEP(rhs, { ctx.builder.getInt32(0), ctx.builder.getInt32(index) });
      auto src = load(ctx, fx, ptr, paramtuple->fields[index], MIR::Local::Reference);

      parms.push_back(load(ctx, fx, src, paramtuple->fields[index]));
    }

    store(ctx, fx, dst, ctx.builder.CreateCall(fn, parms));
  }

  //|///////////////////// classify /////////////////////////////////////////
  void codegen_builtin_classify(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);

    if (lhscat == TypeCategory::UnsignedInteger || lhscat == TypeCategory::SignedInteger)
    {
      bool result;

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

      store(ctx, fx, dst, ctx.builder.getInt1(result));
    }
    else if (lhscat == TypeCategory::FloatingPoint)
    {
      llvm::Value *result;

      switch(callee.fn->builtin)
      {
        case Builtin::is_nan:
          result = ctx.builder.CreateFCmpUNO(lhs, lhs);
          break;

        case Builtin::is_finite:
          result = ctx.builder.CreateUnaryIntrinsic(llvm::Intrinsic::fabs, lhs);
          result = ctx.builder.CreateFCmpONE(result, llvm_float(lhs->getType(), std::numeric_limits<double>::infinity()));
          break;

        case Builtin::is_normal: {
          auto oeq = ctx.builder.CreateFCmpOEQ(lhs, lhs);
          auto abs = ctx.builder.CreateUnaryIntrinsic(llvm::Intrinsic::fabs, lhs);
          auto ult = ctx.builder.CreateFCmpULT(abs, llvm_float(lhs->getType(), std::numeric_limits<double>::infinity()));
          auto uge = ctx.builder.CreateFCmpUGE(abs, llvm_float(lhs->getType(), lhs->getType()->isFloatTy() ? std::numeric_limits<float>::min() : std::numeric_limits<double>::min()));
          result = ctx.builder.CreateAnd(oeq, ult);
          result = ctx.builder.CreateAnd(result, uge);
          break;
        }

        default:
          assert(false);
      }

      store(ctx, fx, dst, result);
    }
    else
    {
      ctx.diag.error("invalid classify arguments", fx.fn, loc);
      ctx.diag << "  operand type: '" << *fx.mir.locals[args[0]].type << "'\n";
    }
  }

  //|///////////////////// clz //////////////////////////////////////////////
  void codegen_builtin_clz(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    auto result = ctx.builder.CreateBinaryIntrinsic(llvm::Intrinsic::ctlz, lhs, ctx.builder.getInt1(false));

    store(ctx, fx, dst, ctx.builder.CreateIntCast(result, ctx.builder.getInt32Ty(), true));
  }

  //|///////////////////// ctz //////////////////////////////////////////////
  void codegen_builtin_ctz(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    auto result = ctx.builder.CreateBinaryIntrinsic(llvm::Intrinsic::cttz, lhs, ctx.builder.getInt1(false));

    store(ctx, fx, dst, ctx.builder.CreateIntCast(result, ctx.builder.getInt32Ty(), true));
  }

  //|///////////////////// popcnt ///////////////////////////////////////////
  void codegen_builtin_popcnt(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);

    auto result = ctx.builder.CreateUnaryIntrinsic(llvm::Intrinsic::ctpop, lhs);

    store(ctx, fx, dst, ctx.builder.CreateIntCast(result, ctx.builder.getInt32Ty(), true));
  }

  //|///////////////////// signbit //////////////////////////////////////////
  void codegen_builtin_signbit(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);

    if (lhscat == TypeCategory::UnsignedInteger)
    {
      store(ctx, fx, dst, ctx.builder.getInt32(0));
    }
    else if (lhscat == TypeCategory::SignedInteger)
    {
      auto cmp = ctx.builder.CreateICmpSLT(lhs, llvm_zero(lhs->getType()));

      store(ctx, fx, dst, ctx.builder.CreateZExt(cmp, ctx.builder.getInt32Ty()));
    }
    else if (lhscat == TypeCategory::FloatingPoint)
    {
      auto bits = ctx.builder.CreateBitCast(lhs, lhs->getType()->isFloatTy() ? ctx.builder.getInt32Ty() : ctx.builder.getInt64Ty());

      auto cmp = ctx.builder.CreateICmpSLT(bits, llvm_zero(bits->getType()));

      store(ctx, fx, dst, ctx.builder.CreateZExt(cmp, ctx.builder.getInt32Ty()));
    }
    else
    {
      ctx.diag.error("invalid signbit arguments", fx.fn, loc);
      ctx.diag << "  operand type: '" << *fx.mir.locals[args[0]].type << "'\n";
    }
  }

  //|///////////////////// frexp ////////////////////////////////////////////
  void codegen_builtin_frexp(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);

    if (lhscat == TypeCategory::FloatingPoint)
    {
      llvm::Function *frexp = nullptr;

      if (lhs->getType()->isFloatTy())
      {
        if (!(frexp = ctx.module.getFunction("frexpf")))
        {
          auto fntype = llvm::FunctionType::get(ctx.builder.getFloatTy(), { ctx.builder.getFloatTy(), ctx.builder.getInt32Ty()->getPointerTo() }, false);
          auto fnprot = llvm::Function::Create(fntype, llvm::Function::ExternalLinkage, "frexpf", ctx.module);

          frexp = fnprot;
        }
      }

      if (lhs->getType()->isDoubleTy())
      {
        if (!(frexp = ctx.module.getFunction("frexp")))
        {
          auto fntype = llvm::FunctionType::get(ctx.builder.getDoubleTy(), { ctx.builder.getDoubleTy(), ctx.builder.getInt32Ty()->getPointerTo() }, false);
          auto fnprot = llvm::Function::Create(fntype, llvm::Function::ExternalLinkage, "frexp", ctx.module);

          frexp = fnprot;
        }
      }

      if (!fx.locals[dst].alloca)
      {
        ctx.builder.SetInsertPoint(fx.blocks[0].bx, fx.blocks[0].bx->begin());
        fx.locals[dst].alloca = alloc(ctx, fx, fx.mir.locals[dst].type, fx.mir.locals[dst].flags);
        ctx.builder.SetInsertPoint(fx.blocks[fx.currentblockid].bx);
      }

      auto exp = ctx.builder.CreateStructGEP(fx.locals[dst].alloca, 1);
      auto fract = ctx.builder.CreateStructGEP(fx.locals[dst].alloca, 0);

      auto result = ctx.builder.CreateCall(frexp, { lhs, exp } );

      store(ctx, fx, fract, fx.mir.locals[args[0]].type, result);
    }
    else
    {
      ctx.diag.error("invalid frexp arguments", fx.fn, loc);
      ctx.diag << "  operand type: '" << *fx.mir.locals[args[0]].type << "'\n";
    }
  }

  //|///////////////////// ldexp ////////////////////////////////////////////
  void codegen_builtin_ldexp(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto lhs = load(ctx, fx, args[0]);
    auto exp = load(ctx, fx, args[1]);
    auto lhscat = type_category(fx.mir.locals[args[0]].type);

    if (lhscat == TypeCategory::FloatingPoint)
    {
      llvm::Function *ldexp = nullptr;

      if (lhs->getType()->isFloatTy())
      {
        if (!(ldexp = ctx.module.getFunction("ldexpf")))
        {
          auto fntype = llvm::FunctionType::get(ctx.builder.getFloatTy(), { ctx.builder.getFloatTy(), ctx.builder.getInt32Ty() }, false);
          auto fnprot = llvm::Function::Create(fntype, llvm::Function::ExternalLinkage, "ldexpf", ctx.module);

          ldexp = fnprot;
        }
      }

      if (lhs->getType()->isDoubleTy())
      {
        if (!(ldexp = ctx.module.getFunction("ldexp")))
        {
          auto fntype = llvm::FunctionType::get(ctx.builder.getDoubleTy(), { ctx.builder.getDoubleTy(), ctx.builder.getInt32Ty() }, false);
          auto fnprot = llvm::Function::Create(fntype, llvm::Function::ExternalLinkage, "ldexp", ctx.module);

          ldexp = fnprot;
        }
      }

      store(ctx, fx, dst, ctx.builder.CreateCall(ldexp, { lhs, exp }));
    }
    else
    {
      ctx.diag.error("invalid ldexp arguments", fx.fn, loc);
      ctx.diag << "  operand type: '" << *fx.mir.locals[args[0]].type << "'\n";
    }
  }

  //|///////////////////// memset ///////////////////////////////////////////
  void codegen_builtin_memset(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto dest = load(ctx, fx, args[0]);
    auto value = load(ctx, fx, args[1]);
    auto count = load(ctx, fx, args[2]);

    ctx.builder.CreateMemSet(dest, value, count, llvm::Align(1));

    store(ctx, fx, dst, dest);
  }

  //|///////////////////// memcpy ///////////////////////////////////////////
  void codegen_builtin_memcpy(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto dest = load(ctx, fx, args[0]);
    auto source = load(ctx, fx, args[1]);
    auto count = load(ctx, fx, args[2]);

    ctx.builder.CreateMemCpy(dest, llvm::Align(1), source, llvm::Align(1), count);

    store(ctx, fx, dst, dest);
  }

  //|///////////////////// memmove //////////////////////////////////////////
  void codegen_builtin_memmove(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto dest = load(ctx, fx, args[0]);
    auto source = load(ctx, fx, args[1]);
    auto count = load(ctx, fx, args[2]);

    ctx.builder.CreateMemMove(dest, llvm::Align(1), source, llvm::Align(1), count);

    store(ctx, fx, dst, dest);
  }

  //|///////////////////// memfind //////////////////////////////////////////
  void codegen_builtin_memfind(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    auto source = load(ctx, fx, args[0]);
    auto value = load(ctx, fx, args[1]);
    auto size = load(ctx, fx, args[2]);

    llvm::Function *memfind = nullptr;

    if (!(memfind = ctx.module.getFunction("memfind")))
    {
      auto fntype = llvm::FunctionType::get(ctx.builder.getInt64Ty(), { ctx.builder.getVoidTy()->getPointerTo(), ctx.builder.getInt32Ty(), ctx.builder.getInt64Ty() }, false);
      auto fnprot = llvm::Function::Create(fntype, llvm::Function::ExternalLinkage, "memfind", ctx.module);

      memfind = fnprot;
    }

    source = ctx.builder.CreatePointerCast(source, memfind->getArg(0)->getType());
    value = ctx.builder.CreateIntCast(value, memfind->getArg(1)->getType(), false);

    store(ctx, fx, dst, ctx.builder.CreateCall(memfind, { source, value, size }));
  }

  //|///////////////////// codegen_call /////////////////////////////////////
  void codegen_call(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CallData const &call)
  {
    auto &[callee, args, loc] = call;

    if (callee.fn->flags & FunctionDecl::Builtin)
    {
      switch(callee.fn->builtin)
      {
        case Builtin::Plus:
        case Builtin::Minus:
        case Builtin::Not:
          codegen_builtin_unary_arithmetic(ctx, fx, dst, call);
          break;

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
          codegen_builtin_binary_arithmetic(ctx, fx, dst, call);
          break;

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
          codegen_builtin_binary_arithmetic_assign(ctx, fx, dst, call);
          break;

        case Builtin::LNot:
          codegen_builtin_lnot(ctx, fx, dst, call);
          break;

        case Builtin::LAnd:
          codegen_builtin_land(ctx, fx, dst, call);
          break;

        case Builtin::LOr:
          codegen_builtin_lor(ctx, fx, dst, call);
          break;

        case Builtin::LT:
        case Builtin::GT:
        case Builtin::LE:
        case Builtin::GE:
        case Builtin::EQ:
        case Builtin::NE:
          codegen_builtin_binary_compare(ctx, fx, dst, call);
          break;

        case Builtin::Cmp:
          codegen_builtin_cmp(ctx, fx, dst, call);
          break;

        case Builtin::PreInc:
        case Builtin::PreDec:
          codegen_builtin_unary_arithmetic_assign(ctx, fx, dst, call);
          break;

        case Builtin::DeRef:
          codegen_builtin_deref(ctx, fx, dst, call);
          break;

        case Builtin::Range:
          codegen_builtin_range(ctx, fx, dst, call);
          break;

        case Builtin::Bool:
          codegen_builtin_bool(ctx, fx, dst, call);
          break;

        case Builtin::Assign:
          codegen_builtin_assign(ctx, fx, dst, call);
          break;

        case Builtin::OffsetAdd:
        case Builtin::OffsetSub:
        case Builtin::Difference:
          codegen_builtin_binary_arithmetic(ctx, fx, dst, call);
          break;

        case Builtin::OffsetAddAssign:
        case Builtin::OffsetSubAssign:
          codegen_builtin_binary_arithmetic_assign(ctx, fx, dst, call);
          break;

        case Builtin::AddCarry:
        case Builtin::SubCarry:
        case Builtin::MulCarry:
          codegen_builtin_binary_arithmetic_carry(ctx, fx, dst, call);
          break;

        case Builtin::StringLen:
          codegen_builtin_slice_len(ctx, fx, dst, call);
          break;

        case Builtin::StringData:
          codegen_builtin_slice_data(ctx, fx, dst, call);
          break;

        case Builtin::ArrayData:
        case Builtin::ArrayBegin:
          codegen_builtin_array_data(ctx, fx, dst, call);
          break;

        case Builtin::ArrayIndex:
          codegen_builtin_array_index(ctx, fx, dst, call);
          break;

        case Builtin::ArrayEnd:
          codegen_builtin_array_end(ctx, fx, dst, call);
          break;

        case Builtin::CallOp:
          codegen_builtin_callop(ctx, fx, dst, call);
          break;

        case Builtin::is_nan:
        case Builtin::is_finite:
        case Builtin::is_normal:
          return codegen_builtin_classify(ctx, fx, dst, call);

        case Builtin::clz:
          codegen_builtin_clz(ctx, fx, dst, call);
          break;

        case Builtin::ctz:
          codegen_builtin_ctz(ctx, fx, dst, call);
          break;

        case Builtin::popcnt:
          codegen_builtin_popcnt(ctx, fx, dst, call);
          break;

        case Builtin::signbit:
          codegen_builtin_signbit(ctx, fx, dst, call);
          break;

        case Builtin::frexp:
          codegen_builtin_frexp(ctx, fx, dst, call);
          break;

        case Builtin::ldexp:
          codegen_builtin_ldexp(ctx, fx, dst, call);
          break;

        case Builtin::abs:
        case Builtin::floor:
        case Builtin::ceil:
        case Builtin::round:
        case Builtin::trunc:
        case Builtin::sqrt:
          codegen_builtin_unary_arithmetic(ctx, fx, dst, call);
          break;

        case Builtin::min:
        case Builtin::max:
        case Builtin::copysign:
          codegen_builtin_binary_arithmetic(ctx, fx, dst, call);
          break;

        case Builtin::memset:
          codegen_builtin_memset(ctx, fx, dst, call);
          break;

        case Builtin::memcpy:
          codegen_builtin_memcpy(ctx, fx, dst, call);
          break;

        case Builtin::memmove:
          codegen_builtin_memmove(ctx, fx, dst, call);
          break;

        case Builtin::memfind:
          codegen_builtin_memfind(ctx, fx, dst, call);
          break;

        case Builtin::StringSlice:
        case Builtin::StringAppend:
        case Builtin::StringCreate:
          ctx.diag.error("function not callable in runtime context", fx.fn, loc);
          break;

        default:
          assert(false);
      }
    }
    else
    {
      vector<llvm::Value*> parms;

      if (fx.locals[dst].firstarg_return)
      {
        parms.push_back(fx.locals[dst].alloca);
      }

      if (callee.throwtype)
      {
        parms.push_back(fx.locals[fx.mir.blocks[fx.currentblockid].terminator.value].alloca);
      }

      for(auto &arg : args)
      {
        if (fx.mir.locals[arg].zerosized())
          continue;

        if (fx.locals[arg].passarg_pointer)
          parms.push_back(fx.locals[arg].alloca);
        else
          parms.push_back(load(ctx, fx, arg));
      }

      assert(ctx.functions.find(callee) != ctx.functions.end());

#if 0
      auto func = ctx.functions[callee];

      string buf;
      llvm::raw_string_ostream os(buf);

      os << "Calling: " << func->getName();
      os << " -> ";
      func->getReturnType()->print(os, true);
      os << '\n';

      for(size_t i = 0; i < func->getFunctionType()->getNumParams(); ++i)
      {
        os << "  " << i << ": ";
        func->getFunctionType()->getParamType(i)->print(os, true);
        os << " with ";
        parms[i]->getType()->print(os, true);
        os << '\n';
      }

      os.flush();
      cout << buf.c_str() << endl;
#endif

      auto call = ctx.builder.CreateCall(ctx.functions[callee], parms);

      if (!fx.locals[dst].firstarg_return && !fx.mir.locals[dst].zerosized())
        store(ctx, fx, dst, call);

      fx.lastcall = call;
    }
  }

  //|///////////////////// codegen_cast /////////////////////////////////////
  void codegen_cast(GenContext &ctx, FunctionContext &fx, MIR::local_t dst, MIR::RValue::CastData const &cast)
  {
    auto &[arg, loc] = cast;

    if (fx.mir.locals[arg].zerosized())
      return;

    auto src = load(ctx, fx, arg);
    auto srccat = type_category(fx.mir.locals[arg].type);
    auto dstcat = type_category(fx.mir.locals[dst].type);

    if (fx.mir.locals[dst].flags & MIR::Local::Reference)
    {
      store(ctx, fx, dst, ctx.builder.CreateBitCast(src, llvm_type(ctx, fx.mir.locals[dst].type)->getPointerTo()));
    }
    else if (fx.mir.locals[arg].flags & MIR::Local::Reference)
    {
      store(ctx, fx, dst, ctx.builder.CreatePointerCast(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else if (dstcat == TypeCategory::Bool && srccat == TypeCategory::Pointer)
    {
      store(ctx, fx, dst, ctx.builder.CreateICmpNE(src, llvm_zero(src->getType())));
    }
    else if (dstcat == TypeCategory::Pointer && srccat == TypeCategory::Array)
    {
      store(ctx, fx, dst, ctx.builder.CreatePointerCast(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else if (dstcat == TypeCategory::Pointer && srccat == TypeCategory::Pointer)
    {
      store(ctx, fx, dst, ctx.builder.CreatePointerCast(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else if (dstcat == TypeCategory::Pointer && fx.mir.locals[arg].type == type(Builtin::Type_USize))
    {
      store(ctx, fx, dst, ctx.builder.CreateIntToPtr(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else if (fx.mir.locals[dst].type == type(Builtin::Type_USize) && srccat == TypeCategory::Pointer)
    {
      store(ctx, fx, dst, ctx.builder.CreatePtrToInt(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else if (dstcat == TypeCategory::Bool && (srccat == TypeCategory::Bool || srccat == TypeCategory::SignedInteger || srccat == TypeCategory::UnsignedInteger))
    {
      store(ctx, fx, dst, ctx.builder.CreateICmpNE(src, llvm_zero(src->getType())));
    }
    else if (dstcat == TypeCategory::UnsignedInteger && (srccat == TypeCategory::Bool || srccat == TypeCategory::SignedInteger || srccat == TypeCategory::UnsignedInteger))
    {
      if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
      {
        auto srctype = src->getType();
        auto srcwidth = llvm::cast<llvm::IntegerType>(srctype)->getBitWidth();
        auto dsttype = llvm_type(ctx, fx.mir.locals[dst].type);
        auto dstwidth = llvm::cast<llvm::IntegerType>(dsttype)->getBitWidth();

        if (srccat == TypeCategory::SignedInteger)
        {
          codegen_assert_carry(ctx, fx, ctx.builder.CreateICmpSLT(src, llvm_zero(srctype)));

          if (dstwidth < srcwidth)
            codegen_assert_carry(ctx, fx, ctx.builder.CreateICmpSGT(src, llvm_int(srctype, ~0ull >> (64 - dstwidth))));
        }

        if (srccat == TypeCategory::UnsignedInteger)
        {
          if (dstwidth < srcwidth)
            codegen_assert_carry(ctx, fx, ctx.builder.CreateICmpUGT(src, llvm_int(srctype, ~0ull >> (64 - dstwidth))));
        }
      }

      store(ctx, fx, dst, ctx.builder.CreateIntCast(src, llvm_type(ctx, fx.mir.locals[dst].type), srccat == TypeCategory::SignedInteger));
    }
    else if (dstcat == TypeCategory::SignedInteger && (srccat == TypeCategory::Bool || srccat == TypeCategory::SignedInteger || srccat == TypeCategory::UnsignedInteger))
    {
      if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
      {
        auto srctype = src->getType();
        auto srcwidth = llvm::cast<llvm::IntegerType>(srctype)->getBitWidth();
        auto dsttype = llvm_type(ctx, fx.mir.locals[dst].type);
        auto dstwidth = llvm::cast<llvm::IntegerType>(dsttype)->getBitWidth();

        if (srccat == TypeCategory::SignedInteger)
        {
          if (dstwidth < srcwidth)
            codegen_assert_carry(ctx, fx, ctx.builder.CreateICmpSLT(src, llvm_int(srctype, ~0ull << (dstwidth - 1))));

          if (dstwidth < srcwidth)
            codegen_assert_carry(ctx, fx, ctx.builder.CreateICmpSGT(src, llvm_int(srctype, ~0ull >> (64 - dstwidth + 1))));
        }

        if (srccat == TypeCategory::UnsignedInteger)
        {
          if (dstwidth <= srcwidth)
            codegen_assert_carry(ctx, fx, ctx.builder.CreateICmpUGT(src, llvm_int(srctype, ~0ull >> (64 - dstwidth + 1))));
        }
      }

      store(ctx, fx, dst, ctx.builder.CreateIntCast(src, llvm_type(ctx, fx.mir.locals[dst].type), srccat == TypeCategory::SignedInteger));
    }
    else if (dstcat == TypeCategory::Bool && srccat == TypeCategory::FloatingPoint)
    {
      store(ctx, fx, dst, ctx.builder.CreateFCmpUNE(src, llvm_zero(src->getType())));
    }
    else if (dstcat == TypeCategory::UnsignedInteger && srccat == TypeCategory::FloatingPoint)
    {
      if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
        codegen_assert_carry(ctx, fx, ctx.builder.CreateFCmpOLT(src, llvm_zero(src->getType())));

      store(ctx, fx, dst, ctx.builder.CreateFPToUI(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else if (dstcat == TypeCategory::SignedInteger && srccat == TypeCategory::FloatingPoint)
    {
      store(ctx, fx, dst, ctx.builder.CreateFPToSI(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else if (dstcat == TypeCategory::FloatingPoint && (srccat == TypeCategory::Bool || srccat == TypeCategory::UnsignedInteger))
    {
      store(ctx, fx, dst, ctx.builder.CreateUIToFP(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else if (dstcat == TypeCategory::FloatingPoint && srccat == TypeCategory::SignedInteger)
    {
      store(ctx, fx, dst, ctx.builder.CreateSIToFP(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else if (dstcat == TypeCategory::FloatingPoint && srccat == TypeCategory::FloatingPoint)
    {
      store(ctx, fx, dst, ctx.builder.CreateFPCast(src, llvm_type(ctx, fx.mir.locals[dst].type)));
    }
    else
    {
      ctx.diag.error("invalid static cast", fx.fn, loc);
      ctx.diag << "  src type: '" << *fx.mir.locals[arg].type << "' dst type: '" << *fx.mir.locals[dst].type << "'\n";
    }
  }

  //|///////////////////// codegen_return_terminator ////////////////////////
  void codegen_return_terminator(GenContext &ctx, FunctionContext &fx)
  {
    if (fx.mir.throws)
    {
      ctx.builder.CreateRet(load(ctx, fx, fx.errorresult, ctx.booltype));
    }
    else if (is_void_type(fx.mir.locals[0].type) || fx.firstarg_return)
    {
      ctx.builder.CreateRetVoid();
    }
    else
    {
      ctx.builder.CreateRet(load(ctx, fx, 0));
    }
  }

  //|///////////////////// codegen_goto_terminator //////////////////////////
  void codegen_goto_terminator(GenContext &ctx, FunctionContext &fx, MIR::block_t blockid)
  {
    ctx.builder.CreateBr(fx.blocks[blockid].bx);
  }

  //|///////////////////// codegen_switch_terminator ////////////////////////
  void codegen_switch_terminator(GenContext &ctx, FunctionContext &fx, MIR::local_t value, vector<tuple<int, MIR::block_t>> const &targets, MIR::block_t blockid)
  {
    auto cond = load(ctx, fx, value);

    auto type = fx.mir.locals[value].type;

    if (is_bool_type(type))
    {
      assert(targets.size() == 1 && get<0>(targets[0]) == 0);

      if (auto constant = llvm::dyn_cast<llvm::ConstantInt>(cond); constant)
        ctx.builder.CreateBr(constant->isOne() ? fx.blocks[blockid].bx : fx.blocks[get<1>(targets[0])].bx);
      else
        ctx.builder.CreateCondBr(cond, fx.blocks[blockid].bx, fx.blocks[get<1>(targets[0])].bx);
    }
    else
    {
      ctx.diag.error("invalid type on conditional");
      return;
    }
  }

  //|///////////////////// codegen_catch_terminator /////////////////////////
  void codegen_catch_terminator(GenContext &ctx, FunctionContext &fx, MIR::local_t value, MIR::block_t blockid)
  {
    ctx.builder.CreateCondBr(fx.lastcall, fx.blocks[blockid].bx, fx.blocks[blockid + 1].bx);

    if (fx.mir.throws && value == 1)
    {
      ctx.builder.SetInsertPoint(fx.blocks[blockid].bx);

      store(ctx, fx, fx.errorresult, ctx.booltype, ctx.builder.getInt1(1));
    }
  }

  //|///////////////////// codegen_throw_terminator /////////////////////////
  void codegen_throw_terminator(GenContext &ctx, FunctionContext &fx, MIR::local_t value, MIR::block_t blockid)
  {
    if (fx.mir.throws && value == 1)
    {
      store(ctx, fx, fx.errorresult, ctx.booltype, ctx.builder.getInt1(1));
    }

    ctx.builder.CreateBr(fx.blocks[blockid].bx);
  }

  //|///////////////////// codegen_terminator ////////////////////////////////
  void codegen_terminator(GenContext &ctx, FunctionContext &fx, MIR::Terminator const &terminator)
  {
    switch (terminator.kind)
    {
      case MIR::Terminator::Return:
        codegen_return_terminator(ctx, fx);
        break;

      case MIR::Terminator::Goto:
        codegen_goto_terminator(ctx, fx, terminator.blockid);
        break;

      case MIR::Terminator::Switch:
        codegen_switch_terminator(ctx, fx, terminator.value, terminator.targets, terminator.blockid);
        break;

      case MIR::Terminator::Catch:
        codegen_catch_terminator(ctx, fx, terminator.value, terminator.blockid);
        break;

      case MIR::Terminator::Throw:
        codegen_throw_terminator(ctx, fx, terminator.value, terminator.blockid);
        break;
    }
  }

  //|///////////////////// codegen_assign_statement /////////////////////////
  void codegen_assign_statement(GenContext &ctx, FunctionContext &fx, MIR::Statement const &statement)
  {
    auto &src = statement.src;
    auto &dst = statement.dst;

    switch (src.kind())
    {
      case MIR::RValue::Empty:
        break;

      case MIR::RValue::Constant:
        codegen_constant(ctx, fx, dst, src.get<MIR::RValue::Constant>());
        break;

      case MIR::RValue::Function:
        codegen_constant(ctx, fx, dst, src.get<MIR::RValue::Function>());
        break;

      case MIR::RValue::Variable:
        codegen_variable(ctx, fx, dst, src.get<MIR::RValue::Variable>());
        break;

      case MIR::RValue::Call:
        codegen_call(ctx, fx, dst, src.get<MIR::RValue::Call>());
        break;

      case MIR::RValue::Cast:
        codegen_cast(ctx, fx, dst, src.get<MIR::RValue::Cast>());
        break;
    }
  }

  //|///////////////////// codegen_construct_statement //////////////////////
  void codegen_construct_statement(GenContext &ctx, FunctionContext &fx, MIR::Statement const &statement)
  {
    auto dst = statement.dst;

    fx.locals[dst].alloca = ctx.builder.CreatePointerCast(load(ctx, fx, dst - 1), llvm_type(ctx, fx.mir.locals[dst].type, true)->getPointerTo());

    codegen_assign_statement(ctx, fx, statement);

    fx.locals[dst].value = fx.locals[dst].alloca;
    fx.locals[dst].alloca = nullptr;
  }

  //|///////////////////// codegen_storage_live /////////////////////////////
  void codegen_storage_live(GenContext &ctx, FunctionContext &fx, MIR::Statement const &statement)
  {
    if (ctx.genopts.debuginfo == GenOpts::DebugInfo::Yes)
    {
      auto i = statement.dst;

      if (fx.locals[i].info && fx.locals[i].alloca)
      {
        fx.discopes.push_back(ctx.di.createLexicalBlock(fx.discopes.back(), fx.difile, fx.locals[i].info->loc.lineno, fx.locals[i].info->loc.charpos));

        auto autovar = ctx.di.createAutoVariable(fx.discopes.back(), fx.locals[i].info->name, fx.difile, fx.locals[i].info->loc.lineno, llvm_ditype(ctx, fx.mir.locals[i]));

        ctx.di.insertDeclare(fx.locals[i].alloca, autovar, ctx.di.createExpression(), llvm_diloc(ctx, fx, fx.locals[i].info->loc), ctx.builder.GetInsertBlock());
      }
    }
  }

  //|///////////////////// codegen_statement ////////////////////////////////
  void codegen_statement(GenContext &ctx, FunctionContext &fx, MIR::Statement const &statement)
  {
    switch (statement.kind)
    {
      case MIR::Statement::NoOp:
        break;

      case MIR::Statement::Assign:
        codegen_assign_statement(ctx, fx, statement);
        break;

      case MIR::Statement::Construct:
        codegen_construct_statement(ctx, fx, statement);
        break;

      case MIR::Statement::StorageLive:
        codegen_storage_live(ctx, fx, statement);
        break;

      case MIR::Statement::StorageDead:
        break;
    }
  }

  //|///////////////////// codegen_block ////////////////////////////////////
  void codegen_block(GenContext &ctx, FunctionContext &fx, MIR::Block const &block)
  {
    fx.currentblockid = &block - &fx.mir.blocks[0];

    ctx.builder.SetInsertPoint(fx.blocks[fx.currentblockid].bx);

    for(auto &statement : block.statements)
    {
      if (ctx.genopts.debuginfo == GenOpts::DebugInfo::Yes)
      {
        while (fx.currentlineinfo < fx.mir.lineinfos.size() && fx.mir.lineinfos[fx.currentlineinfo].block == fx.currentblockid && fx.mir.lineinfos[fx.currentlineinfo].statement == size_t(&statement - &block.statements[0]))
        {
          ctx.builder.SetCurrentDebugLocation(llvm_diloc(ctx, fx, SourceLocation{ fx.mir.lineinfos[fx.currentlineinfo].lineno, 0 }));

          ++fx.currentlineinfo;
        }
      }

      codegen_statement(ctx, fx, statement);

      if (ctx.diag.has_errored())
        return;
    }

    if (ctx.genopts.debuginfo == GenOpts::DebugInfo::Yes)
    {
      while (fx.currentlineinfo < fx.mir.lineinfos.size() && fx.mir.lineinfos[fx.currentlineinfo].block == fx.currentblockid)
      {
        ctx.builder.SetCurrentDebugLocation(llvm_diloc(ctx, fx, SourceLocation{ fx.mir.lineinfos[fx.currentlineinfo].lineno, 0 }));

        ++fx.currentlineinfo;
      }
    }

    codegen_terminator(ctx, fx, block.terminator);
  }

  //|///////////////////// codegen_function /////////////////////////////////
  void codegen_function(GenContext &ctx, FnSig const &sig)
  {
    if (sig.fn->flags & FunctionDecl::Builtin)
      return;

    if (sig.fn->flags & FunctionDecl::ExternMask)
      if (auto func = ctx.module.getFunction(sig.fn->name))
        ctx.functions.emplace(sig, func);

    if (ctx.functions.find(sig) != ctx.functions.end())
      return;

    FunctionContext fx(sig);

    auto name = get_mangled_name(fx.fn);

#if 0
    if (auto func = ctx.module.getFunction(name))
    {
#ifndef NDEBUG
      ctx.diag << "DEBUG: found duplicate function name... will de-duplicate" << '\n';
      ctx.diag << "DEBUG:   function : " << *fx.fn << " mangled name : " << name << '\n';
#endif

      ctx.functions.emplace(sig, func);
      return;
    }
#endif

    fx.mir = lower(sig, ctx.typetable, ctx.diag, LowerFlags::Runtime);

    if (ctx.genopts.dump_mir)
      dump_mir(fx.mir);

    if (ctx.diag.has_errored())
      return;

    if (!is_concrete_type(fx.mir.locals[0].type))
    {
      ctx.diag.error("unresolved return type", fx.fn, fx.fn->loc());
      return;
    }

    size_t firstarg = 0;

    fx.locals.resize(fx.mir.locals.size());

    // prototype

    auto returntype = llvm_type(ctx, fx.mir.locals[0].type, fx.mir.locals[0].flags);

    vector<llvm::Type*> parmtypes;

    if (is_firstarg_return(ctx, sig, fx.mir.locals[0]))
    {
      firstarg += 1;
      parmtypes.push_back(llvm_type(ctx, fx.mir.locals[0].type, fx.mir.locals[0].flags, true)->getPointerTo());
      returntype = ctx.builder.getVoidTy();
      fx.firstarg_return = true;

      if (fx.mir.throws)
      {
        if (!is_concrete_type(fx.mir.locals[1].type))
        {
          ctx.diag.error("unresolved exception type", fx.fn, fx.fn->loc());
          return;
        }

        firstarg += 1;
        parmtypes.push_back(llvm_type(ctx, fx.mir.locals[1].type, true)->getPointerTo());
        returntype = ctx.builder.getInt1Ty();
      }
    }

    for(size_t i = fx.mir.args_beg, end = fx.mir.args_end; i != end; ++i)
    {
      if (!is_concrete_type(fx.mir.locals[i].type))
      {
        ctx.diag.error("unresolved parameter type", fx.fn, fx.fn->loc());
        return;
      }

      if (fx.mir.locals[i].zerosized())
        continue;

      auto argtype = llvm_type(ctx, fx.mir.locals[i].type, fx.mir.locals[i].flags);

      if (is_passarg_pointer(ctx, sig, fx.mir.locals[i]))
      {
        argtype = argtype->getPointerTo();

        fx.locals[i].passarg_pointer = true;
      }

      parmtypes.push_back(argtype);
    }

    auto linkage = (fx.fn->flags & FunctionDecl::ExternMask) ? llvm::Function::ExternalLinkage : llvm::Function::InternalLinkage;

    auto fntype = llvm::FunctionType::get(returntype, parmtypes, false);
    auto fnprot = llvm::Function::Create(fntype, linkage, name, ctx.module);

    fnprot->addFnAttr(llvm::Attribute::NoUnwind);

    if (ctx.triple.getOS() == llvm::Triple::Win32)
      fnprot->addFnAttr(llvm::Attribute::UWTable);

    fnprot->addFnAttr("frame-pointer", "all");

    if ((fx.fn->flags & FunctionDecl::DeclType) == FunctionDecl::ConstDecl)
      fnprot->addFnAttr(llvm::Attribute::AlwaysInline);

    if (ctx.genopts.debuginfo == GenOpts::DebugInfo::Yes)
      fnprot->addFnAttr("frame-pointer", "all");

    fnprot->addFnAttr(llvm::Attribute::StackProtect);

#if 0
    string buf;
    llvm::raw_string_ostream os(buf);

    os << "Defining: " << fnprot->getName();
    os << " -> ";
    fnprot->getReturnType()->print(os, true);
    os << '\n';

    for(size_t i = 0; i < fnprot->getFunctionType()->getNumParams(); ++i)
    {
      os << "  " << i << ": ";
      fnprot->getFunctionType()->getParamType(i)->print(os, true);
      os << '\n';
    }

    os.flush();
    cout << buf.c_str() << endl;
#endif

    ctx.functions.emplace(sig, fnprot);

    if (fx.fn->flags & FunctionDecl::ExternMask)
      return;

    if (!fx.fn->body && !(fx.fn->flags & FunctionDecl::Defaulted))
    {
      ctx.diag.error("missing function body", fx.fn, fx.fn->loc());
    }

    if (ctx.diag.has_errored())
      return;

    // determine local usage

    for(auto &block : fx.mir.blocks)
    {
      for(auto &statement : block.statements)
      {
        if (statement.kind == MIR::Statement::NoOp)
          continue;

        if (statement.src.kind() == MIR::RValue::Constant)
        {
          fx.locals[statement.dst].writes += 1;
        }

        if (statement.src.kind() == MIR::RValue::Function)
        {
          auto &[pointee, loc] = statement.src.get<MIR::RValue::Function>();

          fx.locals[statement.dst].writes += 1;

          codegen_function(ctx, pointee);
        }

        if (statement.src.kind() == MIR::RValue::Variable)
        {
          auto &[op, arg, fields, loc] = statement.src.get<MIR::RValue::Variable>();

          if (fields.size() == 0 && op == MIR::RValue::Ref)
            fx.locals[arg].addressable = true;

          if (fields.size() != 0 && fields[0].op != MIR::RValue::Val)
            fx.locals[arg].addressable = true;

          fx.locals[statement.dst].writes += 1;
        }

        if (statement.src.kind() == MIR::RValue::Call)
        {
          auto &[callee, args, loc] = statement.src.get<MIR::RValue::Call>();

          auto dst = fx.mir.locals[statement.dst];

          if (statement.kind == MIR::Statement::Construct)
            dst.flags &= ~MIR::Local::Reference;

          if (!is_concrete_type(callee.returntype))
          {
            ctx.diag.error("unresolved return type", fx.fn, loc);
          }

          if (is_firstarg_return(ctx, callee, dst))
          {
            fx.locals[statement.dst].addressable = true;
            fx.locals[statement.dst].firstarg_return = true;
          }

          for(auto &arg : args)
          {
            if (!is_concrete_type(fx.mir.locals[arg].type))
            {
              ctx.diag.error("unresolved parameter type", fx.fn, loc);
              ctx.diag << "  parameter " << &arg - &args.front() + 1 << " type: '" << *fx.mir.locals[arg].type << "'\n";
              return;
            }

            if (is_passarg_pointer(ctx, callee, fx.mir.locals[arg]))
            {
              fx.locals[arg].addressable = true;
              fx.locals[arg].passarg_pointer = true;
            }
          }

          fx.locals[statement.dst].writes += 1;

          codegen_function(ctx, callee);
        }

        if (statement.src.kind() == MIR::RValue::Cast)
        {
          fx.locals[statement.dst].writes += 1;
        }
      }

      if (block.terminator.kind == MIR::Terminator::Catch)
      {
        fx.locals[block.terminator.value].addressable = true;
      }
    }

    for(auto &var : fx.mir.varinfos)
    {
      fx.locals[var.local].info = &var;
    }

    if (ctx.diag.has_errored())
      return;

    // debuginfo

    if (ctx.genopts.debuginfo == GenOpts::DebugInfo::Yes)
    {
      fx.difile = llvm_difile(ctx, fx.fn);

      vector<llvm::Metadata*> parameters;

      parameters.push_back(llvm_ditype(ctx, fx.mir.locals[0]));

      for(size_t i = fx.mir.args_beg, end = fx.mir.args_end; i != end; ++i)
        parameters.push_back(llvm_ditype(ctx, fx.mir.locals[i]));

      auto fnloc = fx.fn->loc().lineno;
      auto scopeloc = fx.fn->body ? fx.fn->body->loc().lineno : fnloc;

      auto dity = ctx.di.createSubroutineType(ctx.di.getOrCreateTypeArray(parameters));
      auto difn = ctx.di.createFunction(llvm_discope(ctx, fx.fn), fx.fn->name, llvm::StringRef(), fx.difile, fnloc, dity, scopeloc, llvm::DINode::FlagPrototyped, llvm::DISubprogram::SPFlagDefinition);

      fnprot->setSubprogram(difn);

      fx.discopes.push_back(difn);
    }

    // entry

    fx.blocks.resize(fx.mir.blocks.size());

    fx.blocks[0].bx = llvm::BasicBlock::Create(ctx.context, "entry", fnprot);

    ctx.builder.SetInsertPoint(fx.blocks[0].bx);

    // locals

    if (fx.firstarg_return)
    {
      fx.locals[0].alloca = fnprot->arg_begin();

      if (fx.mir.throws)
      {
        fx.locals[1].alloca = fnprot->arg_begin() + firstarg - 1;

        fx.errorresult = alloc(ctx, fx, ctx.booltype);
        store(ctx, fx, fx.errorresult, ctx.booltype, ctx.builder.getInt1(0));
      }
    }

    for(size_t i = firstarg; i < 1; ++i)
    {
      if (!fx.locals[i].addressable && fx.locals[i].writes <= 1)
        continue;

      fx.locals[i].alloca = alloc(ctx, fx, fx.mir.locals[i].type, fx.mir.locals[i].flags);
    }

    for(size_t i = fx.mir.args_beg, j = firstarg, end = fx.mir.args_end; i != end; ++i)
    {
      if (fx.locals[i].passarg_pointer)
      {
        fx.locals[i].alloca = fnprot->getArg(j++);
        continue;
      }

      if (fx.locals[i].addressable || fx.locals[i].writes > 1)
        fx.locals[i].alloca = alloc(ctx, fx, fx.mir.locals[i].type, fx.mir.locals[i].flags);

      if (fx.mir.locals[i].zerosized())
        continue;

      store(ctx, fx, i, fnprot->getArg(j++));
    }

    for(size_t i = fx.mir.args_end, end = fx.locals.size(); i != end; ++i)
    {
      if (type_category(fx.mir.locals[i].type) == TypeCategory::Unresolved)
        continue;

      if (!fx.locals[i].addressable && fx.locals[i].writes <= 1 && !(ctx.genopts.debuginfo == GenOpts::DebugInfo::Yes && fx.locals[i].info))
        continue;

      fx.locals[i].alloca = alloc(ctx, fx, fx.mir.locals[i].type, fx.mir.locals[i].flags);
    }

    if (ctx.genopts.debuginfo == GenOpts::DebugInfo::Yes)
    {
      for(size_t i = fx.mir.args_beg, end = fx.mir.args_end; i != end; ++i)
      {
        auto parmvar = ctx.di.createParameterVariable(fx.discopes.back(), fx.locals[i].info->name, i, fx.difile, fx.fn->loc().lineno, llvm_ditype(ctx, fx.mir.locals[i]));

        if (fx.locals[i].alloca)
          ctx.di.insertDeclare(fx.locals[i].alloca, parmvar, ctx.di.createExpression(), llvm_diloc(ctx, fx, fx.fn->loc()), fx.blocks[0].bx);
        else if (fx.locals[i].value)
          ctx.di.insertDbgValueIntrinsic(fx.locals[i].value, parmvar, ctx.di.createExpression(), llvm_diloc(ctx, fx, fx.fn->loc()), fx.blocks[0].bx);
      }
    }

    // blocks

    for(size_t i = 1; i < fx.mir.blocks.size(); ++i)
    {
      fx.blocks[i].bx = llvm::BasicBlock::Create(ctx.context, "bb" + to_string(i), fnprot);
    }

    for(auto &block : fx.mir.blocks)
    {
      codegen_block(ctx, fx, block);

      if (ctx.diag.has_errored())
        return;
    }

    ctx.builder.SetCurrentDebugLocation({});

    llvm::verifyFunction(*fnprot);
  }

  //|///////////////////// codegen_entry_point //////////////////////////////
  void codegen_entry_point(GenContext &ctx, FnSig const &main)
  {
    auto resulttype = ctx.builder.getInt32Ty();

    auto fntype = llvm::FunctionType::get(resulttype, false);
    auto fnprot = llvm::Function::Create(fntype, llvm::Function::ExternalLinkage, "main", ctx.module);

    fnprot->addFnAttr(llvm::Attribute::NoInline);
    fnprot->addFnAttr(llvm::Attribute::NoRecurse);
    fnprot->addFnAttr(llvm::Attribute::NoUnwind);

    if (ctx.triple.getOS() == llvm::Triple::Win32)
      fnprot->addFnAttr(llvm::Attribute::UWTable);

    fnprot->addFnAttr("frame-pointer", "all");

    fnprot->setDSOLocal(true);

    ctx.builder.SetInsertPoint(llvm::BasicBlock::Create(ctx.context, "entry", fnprot));

    if (ctx.functions.find(main) != ctx.functions.end())
    {
      auto retval = ctx.builder.CreateCall(ctx.functions[main]);

      switch (retval->getFunctionType()->getReturnType()->getTypeID())
      {
        case llvm::Type::IntegerTyID:
          if (retval->getFunctionType()->getReturnType()->getIntegerBitWidth() > 32)
            goto invalid;
          ctx.builder.CreateRet(ctx.builder.CreateZExt(retval, resulttype));
          break;

        case llvm::Type::VoidTyID:
          ctx.builder.CreateRet(ctx.builder.getInt32(0));
          break;

        default:
        invalid:
          ctx.diag.error("invalid main return type");
          return;
      }
    }
  }

  //|///////////////////// codegen_init //////////////////////////////////////
  void codegen_init(GenContext &ctx, string const &target)
  {
    llvm::sys::fs::current_path(ctx.current_directory);

    ctx.difile = ctx.di.createFile(target, ctx.current_directory);
    ctx.diunit = ctx.di.createCompileUnit(llvm::dwarf::DW_LANG_C_plus_plus, ctx.difile, "zacc 0.0", 0, "", 0);

    if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
    {
      // div0_chk_fail

      auto fntype = llvm::FunctionType::get(ctx.builder.getVoidTy(), false);
      auto fnprot = llvm::Function::Create(fntype, llvm::Function::ExternalLinkage, "__div0_chk_fail", ctx.module);

      ctx.div0_chk_fail = fnprot;
    }

    if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
    {
      // carry_chk_fail

      auto fntype = llvm::FunctionType::get(ctx.builder.getVoidTy(), false);
      auto fnprot = llvm::Function::Create(fntype, llvm::Function::ExternalLinkage, "__carry_chk_fail", ctx.module);

      ctx.carry_chk_fail = fnprot;
    }

    if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
    {
      // null_chk_fail

      auto fntype = llvm::FunctionType::get(ctx.builder.getVoidTy(), false);
      auto fnprot = llvm::Function::Create(fntype, llvm::Function::ExternalLinkage, "__null_chk_fail", ctx.module);

      ctx.null_chk_fail = fnprot;
    }

    if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
    {
      // assert div

      auto fntype = llvm::FunctionType::get(ctx.builder.getVoidTy(), { ctx.builder.getInt1Ty() }, false);
      auto fnprot = llvm::Function::Create(fntype, llvm::Function::InternalLinkage, "checked", ctx.module);

      auto sx = llvm::BasicBlock::Create(ctx.context, "entry", fnprot);
      auto ax = llvm::BasicBlock::Create(ctx.context, "panic", fnprot);
      auto bx = llvm::BasicBlock::Create(ctx.context, "rturn", fnprot);

      ctx.builder.SetInsertPoint(sx);
      ctx.builder.CreateCondBr(fnprot->arg_begin(), ax, bx);

      ctx.builder.SetInsertPoint(ax);
      ctx.builder.CreateCall(ctx.div0_chk_fail);
      ctx.builder.CreateUnreachable();

      ctx.builder.SetInsertPoint(bx);
      ctx.builder.CreateRetVoid();

      fnprot->addFnAttr(llvm::Attribute::AlwaysInline);

      ctx.assert_div0 = fnprot;
    }

    if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
    {
      // assert carry

      auto fntype = llvm::FunctionType::get(ctx.builder.getVoidTy(), { ctx.builder.getInt1Ty() }, false);
      auto fnprot = llvm::Function::Create(fntype, llvm::Function::InternalLinkage, "checked", ctx.module);

      auto sx = llvm::BasicBlock::Create(ctx.context, "entry", fnprot);
      auto ax = llvm::BasicBlock::Create(ctx.context, "panic", fnprot);
      auto bx = llvm::BasicBlock::Create(ctx.context, "rturn", fnprot);

      ctx.builder.SetInsertPoint(sx);
      ctx.builder.CreateCondBr(fnprot->arg_begin(), ax, bx);

      ctx.builder.SetInsertPoint(ax);
      ctx.builder.CreateCall(ctx.carry_chk_fail);
      ctx.builder.CreateUnreachable();

      ctx.builder.SetInsertPoint(bx);
      ctx.builder.CreateRetVoid();

      fnprot->addFnAttr(llvm::Attribute::AlwaysInline);

      ctx.assert_carry = fnprot;
    }

    if (ctx.genopts.checkmode == GenOpts::CheckedMode::Checked)
    {
      // assert deref

      auto fntype = llvm::FunctionType::get(ctx.builder.getVoidTy(), { ctx.builder.getInt1Ty() }, false);
      auto fnprot = llvm::Function::Create(fntype, llvm::Function::InternalLinkage, "checked", ctx.module);

      auto sx = llvm::BasicBlock::Create(ctx.context, "entry", fnprot);
      auto ax = llvm::BasicBlock::Create(ctx.context, "panic", fnprot);
      auto bx = llvm::BasicBlock::Create(ctx.context, "rturn", fnprot);

      ctx.builder.SetInsertPoint(sx);
      ctx.builder.CreateCondBr(fnprot->arg_begin(), ax, bx);

      ctx.builder.SetInsertPoint(ax);
      ctx.builder.CreateCall(ctx.null_chk_fail);
      ctx.builder.CreateUnreachable();

      ctx.builder.SetInsertPoint(bx);
      ctx.builder.CreateRetVoid();

      fnprot->addFnAttr(llvm::Attribute::AlwaysInline);

      ctx.assert_deref = fnprot;
    }
  }

  //|///////////////////// write_module /////////////////////////////////////
  bool write_module(GenContext &ctx, string const &file)
  {
    string error;
    string triple = ctx.genopts.triple;
    auto target = llvm::TargetRegistry::lookupTarget(triple, error);

    if (!target)
    {
      ctx.diag << error << '\n';
      return false;
    }

    auto cpu = ctx.genopts.cpu;
    auto features = ctx.genopts.features;

    auto options = llvm::TargetOptions();
    options.ThreadModel = llvm::ThreadModel::POSIX;
    options.FloatABIType = llvm::FloatABI::Default;
    options.AllowFPOpFusion = llvm::FPOpFusion::Standard;
    options.ExceptionModel = llvm::ExceptionHandling::None;

    auto relocmodel = llvm::Optional<llvm::Reloc::Model>();
    auto codemodel = llvm::Optional<llvm::CodeModel::Model>();
    auto optlevel = llvm::CodeGenOpt::None;

    switch (ctx.genopts.reloc)
    {
      case GenOpts::Reloc::None:
        break;

      case GenOpts::Reloc::PIC:
        relocmodel = llvm::Reloc::PIC_;
        break;
    }

    switch (ctx.genopts.optlevel)
    {
      case GenOpts::OptLevel::None:
        optlevel = llvm::CodeGenOpt::None;
        break;

      case GenOpts::OptLevel::Less:
        optlevel = llvm::CodeGenOpt::Less;
        break;

      case GenOpts::OptLevel::Default:
        optlevel = llvm::CodeGenOpt::Default;
        break;

      case GenOpts::OptLevel::Aggressive:
        optlevel = llvm::CodeGenOpt::Aggressive;
        break;
    }

    auto machine = target->createTargetMachine(triple, cpu, features, options, relocmodel, codemodel, optlevel);

    if (!machine)
    {
      ctx.diag << "could not create target machine" << '\n';
      return false;
    }

    ctx.module.setDataLayout(machine->createDataLayout());

    if (ctx.genopts.debuginfo == GenOpts::DebugInfo::Yes)
    {
      ctx.module.addModuleFlag(llvm::Module::Warning, "Debug Info Version", llvm::DEBUG_METADATA_VERSION);
      ctx.module.addModuleFlag(llvm::Module::Warning, "Dwarf Version", llvm::dwarf::DWARF_VERSION);
    }

    error_code errorcode;
    auto outstream = llvm::raw_fd_ostream(file, errorcode);

    if (errorcode)
    {
      ctx.diag << "could not get output stream '" << errorcode.message() << "'\n";
      return false;
    }

    auto PMBuilder = llvm::PassManagerBuilder();

    PMBuilder.OptLevel = machine->getOptLevel();
    PMBuilder.LibraryInfo = new llvm::TargetLibraryInfoImpl(llvm::Triple(triple));

    if (optlevel <= 1)
      PMBuilder.Inliner = llvm::createAlwaysInlinerLegacyPass();
    else
      PMBuilder.Inliner = llvm::createFunctionInliningPass(PMBuilder.OptLevel, PMBuilder.SizeLevel, false);

    auto TLII = llvm::TargetLibraryInfoImpl(llvm::Triple(triple));

    auto FPM = llvm::legacy::FunctionPassManager(&ctx.module);
    FPM.add(new llvm::TargetLibraryInfoWrapperPass(TLII));
    FPM.add(llvm::createTargetTransformInfoWrapperPass(machine->getTargetIRAnalysis()));
    PMBuilder.populateFunctionPassManager(FPM);

    auto MPM = llvm::legacy::PassManager();
    MPM.add(new llvm::TargetLibraryInfoWrapperPass(TLII));
    MPM.add(llvm::createTargetTransformInfoWrapperPass(machine->getTargetIRAnalysis()));
    PMBuilder.populateModulePassManager(MPM);

    FPM.doInitialization();

    for(auto &func : ctx.module)
      if (!func.isDeclaration())
        FPM.run(func);

    FPM.doFinalization();

    switch(ctx.genopts.outputtype)
    {
      case GenOpts::OutputType::EmitAsm:
        machine->addPassesToEmitFile(MPM, outstream, nullptr, llvm::CodeGenFileType::CGFT_AssemblyFile, false);
        MPM.run(ctx.module);
        break;

      case GenOpts::OutputType::EmitObj:
        machine->addPassesToEmitFile(MPM, outstream, nullptr, llvm::CodeGenFileType::CGFT_ObjectFile, false);
        MPM.run(ctx.module);
        break;

      case GenOpts::OutputType::EmitLL:
        ctx.module.print(outstream, nullptr);
        break;
    }

    return true;
  }
}

//|--------------------- CodeGen --------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// get_default_triple /////////////////////////////////
string get_default_triple()
{
  return llvm::sys::getDefaultTargetTriple();
}

//|///////////////////// codegen ////////////////////////////////////////////
void codegen(AST *ast, string const &target, GenOpts const &genopts, Diag &diag)
{
  llvm::InitializeNativeTarget();
  //llvm::InitializeAllTargetMCs();
  llvm::InitializeNativeTargetAsmPrinter();
  llvm::InitializeNativeTargetAsmParser();

  GenContext ctx(ast, genopts, diag);

  codegen_init(ctx, decl_cast<ModuleDecl>(decl_cast<TranslationUnitDecl>(ast->root)->mainmodule)->file());

  auto root = decl_cast<TranslationUnitDecl>(ast->root);

  for(auto &decl : decl_cast<ModuleDecl>(root->mainmodule)->decls)
  {
    if (decl->kind() == Decl::Function)
    {
      auto fn = decl_cast<FunctionDecl>(decl);

      if (/*export*/false)
      {
        codegen_function(ctx, fn);
      }

      if (fn->name == "main")
      {
        ctx.main = fn;
        codegen_function(ctx, fn);
      }
    }
  }

  if (ctx.main)
  {
    codegen_entry_point(ctx, ctx.main);
  }

  if (diag.has_errored())
    return;

  ctx.di.finalize();

  llvm::verifyModule(ctx.module);

  write_module(ctx, target);

#if 0
  ctx.module.print(llvm::outs(), nullptr);
  cout << "--" << endl;
#endif
}