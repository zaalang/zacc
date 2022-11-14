//
// typer.cpp
//
// Copyright (C) 2020-2022 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "typer.h"
#include "diag.h"
#include "query.h"
#include "numeric.h"
#include "sema.h"
#include <iostream>
#include <algorithm>

using namespace std;

#define DEFAULT_SUBSTITUTION 1

namespace
{
  struct TyperContext
  {
    Diag &diag;

    string file;

    vector<Scope> stack;

    unordered_map<Decl*, Type*> typetable;

    TyperContext(Diag &diag)
      : diag(diag)
    {
    }
  };

  const long IllSpecified = 0x40000000;

  void resolve_type(TyperContext &ctx, Scope const &scope, Type *&type, Sema &sema);
  void resolve_expr(TyperContext &ctx, Scope const &scope, Expr *&expr, Sema &sema);
  void resolve_decl(TyperContext &ctx, Scope const &scope, Decl *&decl, Sema &sema);
  Type *resolve_alias(TyperContext &ctx, Scope const &scope, Type *type, Sema &sema);
  Type *resolve_typearg(TyperContext &ctx, Decl *decl, Sema &sema);
  void typer_decl(TyperContext &ctx, Decl *decl, Sema &sema);
  void typer_statement(TyperContext &ctx, Stmt *stmt, Sema &sema);

  //|///////////////////// make_typearg /////////////////////////////////////
  TypeArgDecl *make_typearg(TyperContext &ctx, Ident *name, SourceLocation loc, Sema &sema)
  {
    auto arg = sema.make_typearg(name, loc);

    arg->owner = ctx.stack.back().owner;

    return arg;
  }

  //|///////////////////// child_scope //////////////////////////////////////
  Scope child_scope(TyperContext &ctx, Scope const &parent, Decl *decl, vector<Decl*> const &declargs, size_t &k, vector<Type*> const &args, map<Ident*, Type*> const &namedargs, Sema &sema)
  {
    Scope sx(decl, parent.typeargs);

    for(size_t i = 0; i < declargs.size(); ++i)
    {
      auto arg = decl_cast<TypeArgDecl>(declargs[i]);

      if (arg->flags & TypeArgDecl::Pack)
      {
        vector<Type*> fields;

        for( ; k < args.size(); ++k)
        {
          fields.push_back(args[k]);
        }

        sx.set_type(arg, sema.make_tuple(fields));
      }

      else if (arg->flags & TypeArgDecl::SplitFn)
      {
        i += 1;

        if (k < args.size() && is_function_type(args[k]))
        {
          sx.set_type(arg, type_cast<FunctionType>(args[k])->returntype);
          sx.set_type(decl_cast<TypeArgDecl>(declargs[i]), type_cast<FunctionType>(args[k])->paramtuple);

          k += 1;
        }
      }

      else if (arg->flags & TypeArgDecl::SplitArray)
      {
        i += 1;

        if (k < args.size() && is_array_type(args[k]))
        {
          sx.set_type(arg, type_cast<ArrayType>(args[k])->type);
          sx.set_type(decl_cast<TypeArgDecl>(declargs[i]), type_cast<ArrayType>(args[k])->size);

          k += 1;
        }
      }

      else if (k < args.size())
      {
        sx.set_type(arg, args[k]);

        k += 1;
      }

      else if (auto j = namedargs.find(arg->name); j != namedargs.end())
      {
        sx.set_type(arg, j->second);

        k += 1;
      }

      else if (arg->defult)
      {
#if !DEFAULT_SUBSTITUTION
        sx.set_type(arg, arg->defult);
#endif
      }

      else
        k |= IllSpecified;
    }

    for(auto &[decl, arg] : sx.typeargs)
    {
      if (arg->klass() == Type::Unpack)
        k |= IllSpecified;
    }

    return sx;
  }

  template<typename T>
  Scope child_scope(TyperContext &ctx, Scope const &parent, T *decl, size_t &k, vector<Type*> const &args, map<Ident*, Type*> const &namedargs, Sema &sema)
  {
    return child_scope(ctx, parent, decl, decl->args, k, args, namedargs, sema);
  }

  //|///////////////////// decl_scope ///////////////////////////////////////
  Scope decl_scope(TyperContext &ctx, Scope const &scope, Decl *decl, size_t &k, vector<Type*> const &args, map<Ident*, Type*> const &namedargs, Sema &sema)
  {
    switch(decl->kind())
    {
      case Decl::Module:
        return Scope(decl);

      case Decl::Import:
        return Scope(decl_cast<ImportDecl>(decl)->decl);

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Lambda:
      case Decl::Concept:
      case Decl::Enum:
        return child_scope(ctx, scope, decl_cast<TagDecl>(decl), k, args, namedargs, sema);

      case Decl::Function:
        return child_scope(ctx, scope, decl_cast<FunctionDecl>(decl), k, args, namedargs, sema);

      case Decl::TypeAlias:
        if (auto j = resolve_alias(ctx, child_scope(ctx, scope, decl_cast<TypeAliasDecl>(decl), k, args, namedargs, sema), decl_cast<TypeAliasDecl>(decl)->type, sema); j && is_tag_type(j))
          return Scope(type_cast<TagType>(j)->decl, type_cast<TagType>(j)->args);
        break;

      case Decl::TypeArg:
      case Decl::Run:
        break;

      default:
        assert(false);
    }

    return child_scope(scope, decl);
  }

  //|///////////////////// diag_args ////////////////////////////////////////
  void diag_args(TyperContext &ctx, DeclRefDecl *declref, Decl *decl, Sema &sema)
  {
    vector<Decl*> *declargs = nullptr;

    switch(decl->kind())
    {
      case Decl::Module:
      case Decl::Import:
      case Decl::Using:
      case Decl::TypeArg:
        if (declref->args.size() != 0 || declref->namedargs.size() != 0)
          ctx.diag.error("invalid type arguments", ctx.file, declref->loc());
        break;

      case Decl::TypeAlias:
        declargs = &decl_cast<TypeAliasDecl>(decl)->args;
        break;

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
        declargs = &decl_cast<TagDecl>(decl)->args;
        break;

      case Decl::Concept:
        declargs = &decl_cast<ConceptDecl>(decl)->args;
        break;

      default:
        assert(false);
    }

    if (declargs)
    {
      size_t k = 0;

      for(size_t i = 0; i < declargs->size(); ++i)
      {
        auto arg = decl_cast<TypeArgDecl>((*declargs)[i]);

        if (arg->flags & TypeArgDecl::Pack)
        {
          k = declref->args.size();

          continue;
        }

        else if (k < declref->args.size())
        {
          k += 1;

          continue;
        }

        else if (auto j = declref->namedargs.find(arg->name); j != declref->namedargs.end())
        {
          continue;
        }

        else if (arg->defult)
        {
          continue;
        }

        ctx.diag.error("missing type argument", ctx.file, declref->loc());
        return;
      }

      if (k != declref->args.size())
      {
        ctx.diag.error("extra type arguments", ctx.file, declref->loc());
        return;
      }

      for(auto &arg : declref->namedargs)
      {
        auto j = find_if(declargs->begin(), declargs->end(), [&](auto &k) { return decl_cast<TypeArgDecl>(k)->name == arg.first; });

        if (j == declargs->end())
        {
          ctx.diag.error("extra type argument", ctx.file, declref->loc());
          return;
        }
      }
    }

    ctx.diag.error("invalid type arguments", ctx.file, declref->loc());
  }

  //|///////////////////// find_decls ////////////////////////////////////////
  void find_decls(TyperContext &ctx, Scope const &scope, Ident *name, long queryflags, vector<Decl*> &results, Sema &sema)
  {
    find_decls(scope, name, queryflags, results);

    for(size_t i = 0; i < results.size(); ++i)
    {
      auto decl = results[i];

      if (decl->kind() == Decl::If)
      {
        auto ifd = decl_cast<IfDecl>(decl);

        if ((ifd->flags & IfDecl::ResolvedTrue) || !(ifd->flags & IfDecl::ResolvedFalse))
          find_decls(decl, name, queryflags, results);

        if (auto elseif = ifd->elseif)
          if ((ifd->flags & IfDecl::ResolvedFalse) || !(ifd->flags & IfDecl::ResolvedTrue))
            results.push_back(elseif);
      }

      if (decl->kind() == Decl::Using)
      {
        auto n = results.size();

        if (decl_cast<UsingDecl>(decl)->flags & UsingDecl::Resolving)
          continue;

        if (!(decl_cast<UsingDecl>(decl)->flags & UsingDecl::Resolved))
          resolve_decl(ctx, parent_scope(decl), decl, sema);

        switch(auto usein = decl_cast<UsingDecl>(decl); usein->decl->kind())
        {
          case Decl::Module:
            find_decls(usein->decl, name, queryflags | QueryFlags::Public, results);
            break;

          case Decl::Struct:
          case Decl::Union:
          case Decl::VTable:
          case Decl::Concept:
          case Decl::Enum:
            if (decl_cast<TagDecl>(usein->decl)->name == name && (queryflags & QueryFlags::Types))
              results.push_back(usein->decl);
            break;

          case Decl::TypeAlias:
            if (decl_cast<TypeAliasDecl>(usein->decl)->name == name && (queryflags & QueryFlags::Types))
              results.push_back(usein->decl);
            break;

          case Decl::DeclRef:
            if (decl_cast<DeclRefDecl>(usein->decl)->name == name && (queryflags & QueryFlags::Functions))
              results.push_back(usein->decl);
            break;

          case Decl::DeclScoped:
            if (decl_cast<DeclRefDecl>(decl_cast<DeclScopedDecl>(usein->decl)->decls.back())->name == name && (queryflags & QueryFlags::Functions))
              results.push_back(usein->decl);
            break;

          case Decl::TypeArg:
          case Decl::EnumConstant:
            break;

          default:
            assert(false);
        }

        results.erase(remove_if(results.begin() + n, results.end(), [&](auto &decl) {
          return count(results.begin(), results.begin() + n, decl) != 0;
        }), results.end());
      }
    }

    for(size_t i = 0; i < results.size(); ++i)
    {
      if (results[i]->kind() == Decl::Import)
      {
        results.erase(remove_if(results.begin() + i + 1, results.end(), [&](auto &decl) {
          return decl->kind() == Decl::Import;
        }), results.end());
      }
    }

    results.erase(remove_if(results.begin(), results.end(), [&](auto &decl) {
      return decl->kind() == Decl::If || decl->kind() == Decl::Using;
    }), results.end());
  }

  //|///////////////////// is_dependant_type ////////////////////////////////
  bool is_dependant_type(TyperContext &ctx, Type const *type)
  {
    switch (type->klass())
    {
      case Type::Builtin:
        return false;

      case Type::Const:
        return is_dependant_type(ctx, type_cast<ConstType>(type)->type);

      case Type::QualArg:
        return is_dependant_type(ctx, type_cast<QualArgType>(type)->type);

      case Type::Pointer:
        return is_dependant_type(ctx, type_cast<PointerType>(type)->type);

      case Type::Reference:
        return is_dependant_type(ctx, type_cast<ReferenceType>(type)->type);

      case Type::Array:
        return is_dependant_type(ctx, type_cast<ArrayType>(type)->type) || is_dependant_type(ctx, type_cast<ArrayType>(type)->size);

      case Type::Tuple:

        for(auto &field : type_cast<TupleType>(type)->fields)
          if (is_dependant_type(ctx, field))
            return true;

        return false;

      case Type::Tag:

        for(auto &[decl, arg] : type_cast<TagType>(type)->args)
          if (is_dependant_type(ctx, arg))
            return true;

        return false;

      case Type::Function:

        if (is_dependant_type(ctx, type_cast<FunctionType>(type)->returntype))
          return true;

        if (is_dependant_type(ctx, type_cast<FunctionType>(type)->paramtuple))
          return true;

        return false;

      case Type::TypeLit:
        return !is_literal_expr(type_cast<TypeLitType>(type)->value);

      case Type::TypeArg:
        return false;

      case Type::TypeRef:
        return true;

      case Type::Pack:
        return is_dependant_type(ctx, type_cast<PackType>(type)->type);

      case Type::Unpack:
        return is_dependant_type(ctx, type_cast<UnpackType>(type)->type);

      default:
        assert(false);
    }

    throw logic_error("invalid type for is_typeref_type");
  }

  //|///////////////////// substitute_type //////////////////////////////////
  Type *substitute_type(TyperContext &ctx, vector<pair<Decl*, Type*>> const &typeargs, Type *type, Sema &sema)
  {
    switch (type->klass())
    {
      case Type::Builtin:
        return type;

      case Type::Const:
        return sema.make_const(substitute_type(ctx, typeargs, type_cast<ConstType>(type)->type, sema));

      case Type::QualArg:
        return sema.make_qualarg(substitute_type(ctx, typeargs, type_cast<QualArgType>(type)->type, sema));

      case Type::Pointer:
        return sema.make_pointer(substitute_type(ctx, typeargs, type_cast<PointerType>(type)->type, sema));

      case Type::Reference:
        return sema.make_reference(substitute_type(ctx, typeargs, type_cast<ReferenceType>(type)->type, sema));

      case Type::Array:
        return sema.make_array(substitute_type(ctx, typeargs, type_cast<ArrayType>(type)->type, sema), substitute_type(ctx, typeargs, type_cast<ArrayType>(type)->size, sema));

      case Type::Tuple: {
        auto fields = type_cast<TupleType>(type)->fields;
        for(auto &field : fields)
          field = substitute_type(ctx, typeargs, field, sema);
        return sema.make_tuple(fields);
      }

      case Type::Tag: {
        auto args = type_cast<TagType>(type)->args;
        for(auto &[decl, type] : args)
          type = substitute_type(ctx, typeargs, type, sema);
        return sema.make_tagtype(type_cast<TagType>(type)->decl, args);
      }

      case Type::Function: {
        auto returntype = substitute_type(ctx, typeargs, type_cast<FunctionType>(type)->returntype, sema);
        auto paramtuple = substitute_type(ctx, typeargs, type_cast<FunctionType>(type)->paramtuple, sema);
        auto throwtype = substitute_type(ctx, typeargs, type_cast<FunctionType>(type)->throwtype, sema);
        return sema.make_fntype(returntype, paramtuple, throwtype);
      }

      case Type::TypeLit:
        return type;

      case Type::TypeArg:
        if (auto j = find_if(typeargs.begin(), typeargs.end(), [&](auto k) { return k.first == type_cast<TypeArgType>(type)->decl; }); j != typeargs.end())
          return j->second;
        return type;

      case Type::TypeRef:
        return type;

      case Type::Pack:
        return sema.make_pack(substitute_type(ctx, typeargs, type_cast<PackType>(type)->type, sema));

      case Type::Unpack:
        return sema.make_unpack(substitute_type(ctx, typeargs, type_cast<UnpackType>(type)->type, sema));

      default:
        assert(false);
    }

    throw logic_error("invalid type for substitute");
  }

  //|///////////////////// substitute_defaulted /////////////////////////////
  Type *substitute_defaulted(TyperContext &ctx, Scope const &scope, Type *type, Sema &sema)
  {
    switch (type->klass())
    {
      case Type::Builtin:
        break;

      case Type::Const:
        if (auto newtype = substitute_defaulted(ctx, scope, type_cast<ConstType>(type)->type, sema); newtype != type_cast<ConstType>(type)->type)
          type = sema.make_const(newtype);
        break;

      case Type::QualArg:
        if (auto newtype = substitute_defaulted(ctx, scope, type_cast<QualArgType>(type)->type, sema); newtype != type_cast<QualArgType>(type)->type)
          type = sema.make_qualarg(newtype);
        break;

      case Type::Pointer:
        if (auto newtype = substitute_defaulted(ctx, scope, type_cast<PointerType>(type)->type, sema); newtype != type_cast<PointerType>(type)->type)
          type = sema.make_pointer(newtype);
        break;

      case Type::Reference:
        if (auto newtype = substitute_defaulted(ctx, scope, type_cast<ReferenceType>(type)->type, sema); newtype != type_cast<ReferenceType>(type)->type)
          type = sema.make_reference(newtype);
        break;

      case Type::Array:
        if (auto newtype = substitute_defaulted(ctx, scope, type_cast<ArrayType>(type)->type, sema); newtype != type_cast<ArrayType>(type)->type)
          type = sema.make_array(newtype, type_cast<ArrayType>(type)->size);
        break;

      case Type::Tuple: {
        auto fields = type_cast<TupleType>(type)->fields;

        for(auto &field : fields)
          field = substitute_defaulted(ctx, scope, field, sema);

        if (fields != type_cast<TupleType>(type)->fields)
          type = sema.make_tuple(fields);
        break;
      }

      case Type::Tag: {
        auto tagtype = type_cast<TagType>(type);

        vector<pair<Decl*, Type*>> newargs;

        for(auto &[arg, type] : tagtype->args)
        {
          if (is_typearg_type(type))
          {
            auto decl = decl_cast<TypeArgDecl>(type_cast<TypeArgType>(type)->decl);

            if (decl == arg && !outer_scope(scope, decl))
            {
              auto typearg = make_typearg(ctx, Ident::kw_var, arg->loc(), sema);

              typearg->defult = decl->defult;

              newargs.emplace_back(arg, sema.make_typearg(typearg));
            }

            continue;
          }

          if (auto newtype = substitute_defaulted(ctx, scope, type, sema); newtype != type)
            newargs.emplace_back(arg, newtype);
        }

        if (newargs.size() != 0)
        {
          Scope tx(tagtype->decl, tagtype->args);

          for(auto &[arg, type] : newargs)
            tx.set_type(arg, type);

          type = sema.make_tagtype(tagtype->decl, std::move(tx.typeargs));
        }

        break;
      }

      case Type::Constant:
        break;

      case Type::Function:
        break;

      case Type::TypeLit:
      case Type::TypeArg:
      case Type::TypeRef:
        break;

      case Type::Pack:
      case Type::Unpack:
        break;

      default:
        assert(false);
    }

    return type;
  }

  //|///////////////////// resolve_alias ////////////////////////////////////
  Type *resolve_alias(TyperContext &ctx, Scope const &scope, Type *type, Sema &sema)
  {
    resolve_type(ctx, scope, type, sema);

    if (scope.typeargs.size() != 0)
    {
      type = substitute_type(ctx, scope.typeargs, type, sema);
    }

    return type;
  }

  //|///////////////////// resolve_typearg //////////////////////////////////
  Type *resolve_typearg(TyperContext &ctx, Decl *decl, Sema &sema)
  {
    auto j = ctx.typetable.find(decl);

    if (j == ctx.typetable.end())
    {
      j = ctx.typetable.emplace(decl, sema.make_typearg(decl)).first;
    }

    return j->second;
  }

  //|///////////////////// resolve_decl /////////////////////////////////////
  void resolve_decl(TyperContext &ctx, Scope const &scope, DeclRefDecl *declref, Sema &sema)
  {
    for(auto &arg : declref->args)
    {
      resolve_type(ctx, scope, arg, sema);
    }

    for(auto &[name, arg] : declref->namedargs)
    {
      resolve_type(ctx, scope, arg, sema);
    }
  }

  //|///////////////////// resolve_decl /////////////////////////////////////
  void resolve_decl(TyperContext &ctx, Scope const &scope, DeclScopedDecl *declref, Sema &sema)
  {
    for(auto &decl : declref->decls)
    {
      resolve_decl(ctx, scope, decl, sema);
    }
  }

  //|///////////////////// resolve_typename /////////////////////////////////
  void resolve_decl(TyperContext &ctx, Scope const &scope, TypeNameDecl *declref, Sema &sema)
  {
    resolve_type(ctx, scope, declref->type, sema);
  }

  //|///////////////////// resolve_declname /////////////////////////////////
  void resolve_decl(TyperContext &ctx, Scope const &scope, DeclNameDecl *declref, Sema &sema)
  {
    for(auto &arg : declref->args)
    {
      resolve_type(ctx, scope, arg, sema);
    }

    for(auto &[name, arg] : declref->namedargs)
    {
      resolve_type(ctx, scope, arg, sema);
    }
  }

  //|///////////////////// resolve_decl /////////////////////////////////////
  void resolve_decl(TyperContext &ctx, Scope const &scope, TypeOfDecl *typedecl, Sema &sema)
  {
    resolve_expr(ctx, scope, typedecl->expr, sema);
  }

  //|///////////////////// resolve_decl /////////////////////////////////////
  void resolve_decl(TyperContext &ctx, Scope const &scope, UsingDecl *usein, Sema &sema)
  {
    usein->flags |= UsingDecl::Resolving;

    long querymask = 0;
    Scope declscope = ctx.stack.front();

    vector<Decl*> decls;

    if (usein->decl->kind() == Decl::DeclRef)
    {
      auto declref = decl_cast<DeclRefDecl>(usein->decl);

      if (declref->args.size() != 0 || declref->namedargs.size() != 0)
      {
        ctx.diag.error("arguments invalid in using", usein, declref->loc());
        return;
      }

      if (auto owner = get_if<Decl*>(&usein->owner); owner && (*owner)->kind() == Decl::Import)
        querymask |= QueryFlags::Public;

      for(auto sx = scope; sx; sx = parent_scope(std::move(sx)))
      {
        find_decls(ctx, sx, declref->name, QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Functions | QueryFlags::Usings | querymask, decls, sema);

        if (decls.empty())
          continue;

        declscope = sx;

        break;
      }

      if (decls.size() == 0)
      {
        ctx.diag.error("no such declaration", usein, usein->loc());
        return;
      }

      if (usein->flags & Decl::Public)
      {
        if (any_of(decls.begin(), decls.end(), [&](auto *decl) { return get_module(decl) == get_module(usein); }))
        {
          ctx.diag.error("recursive public using", usein, usein->loc());
          return;
        }
      }

      if (!all_of(decls.begin(), decls.end(), [](auto *decl) { return decl->kind() == Decl::Function || decl->kind() == Decl::DeclScoped; }))
      {
        decls.erase(remove_if(decls.begin(), decls.end(), [](auto *decl) { return decl->kind() == Decl::Function || decl->kind() == Decl::DeclScoped; }), decls.end());

        if (decls.size() != 1)
        {
          ctx.diag.error("ambiguous using declaration", usein, usein->loc());
          return;
        }
      }
    }

    if (usein->decl->kind() == Decl::DeclScoped)
    {
      auto scoped = decl_cast<DeclScopedDecl>(usein->decl);

      if (scoped->decls[0]->kind() == Decl::TypeOf)
      {
        ctx.diag.error("typeof invalid in using", usein, scoped->loc());
        return;
      }

      if (auto declref = decl_cast<DeclRefDecl>(scoped->decls[0]); declref->name != Ident::op_scope)
      {
        if (declref->args.size() != 0 || declref->namedargs.size() != 0)
        {
          ctx.diag.error("arguments invalid in using", usein, declref->loc());
          return;
        }

        for(auto sx = scope; sx; sx = parent_scope(std::move(sx)))
        {
          find_decls(ctx, sx, declref->name, QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Usings | querymask, decls, sema);

          if (decls.empty())
            continue;

          size_t k = 0;

          declscope = decl_scope(ctx, outer_scope(sx, decls[0]), decls[0], k, declref->args, declref->namedargs, sema);

          break;
        }

        if (decls.size() != 1)
        {
          ctx.diag.error("no such scope", usein, declref->loc());
          return;
        }

        if (usein->flags & Decl::Public)
        {
          if (get_module(decls[0])->name->sv().substr(0, declref->name->sv().size()) == declref->name->sv())
          {
            ctx.diag.error("recursive public using", usein, usein->loc());
            return;
          }
        }

        if (decls[0]->kind() == Decl::Import || decls[0]->kind() == Decl::Module)
          querymask |= QueryFlags::Public;

        decls.clear();
      }

      for(size_t i = 1; i + 1 < scoped->decls.size(); ++i)
      {
        auto declref = decl_cast<DeclRefDecl>(scoped->decls[i]);

        if (declref->args.size() != 0 || declref->namedargs.size() != 0)
        {
          ctx.diag.error("arguments invalid in using", usein, declref->loc());
          return;
        }

        find_decls(ctx, declscope, declref->name, QueryFlags::Modules | QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Usings | querymask, decls, sema);

        if (decls.size() != 1)
        {
          ctx.diag.error("no such scope", usein, declref->loc());
          return;
        }

        size_t k = 0;

        declscope = decl_scope(ctx, outer_scope(declscope, decls[0]), decls[0], k, declref->args, declref->namedargs, sema);

        if (decls[0]->kind() == Decl::Import || decls[0]->kind() == Decl::Module)
          querymask |= QueryFlags::Public;

        decls.clear();
      }

      if (auto declref = decl_cast<DeclRefDecl>(scoped->decls.back()))
      {
        if (declref->args.size() != 0 || declref->namedargs.size() != 0)
        {
          ctx.diag.error("arguments invalid in using", usein, declref->loc());
          return;
        }

        find_decls(ctx, declscope, declref->name, QueryFlags::Modules | QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Functions | QueryFlags::Usings | querymask, decls, sema);

        if (decls.size() == 0)
        {
          ctx.diag.error("no such declaration", usein, usein->loc());
          return;
        }

        if (!all_of(decls.begin(), decls.end(), [](auto *decl) { return decl->kind() == Decl::Function || decl->kind() == Decl::DeclScoped; }))
        {
          decls.erase(remove_if(decls.begin(), decls.end(), [](auto *decl) { return decl->kind() == Decl::Function || decl->kind() == Decl::DeclScoped; }), decls.end());

          if (decls.size() != 1)
          {
            ctx.diag.error("ambiguous using declaration", usein, usein->loc());
            return;
          }
        }
      }
    }

    if (decls.size() != 0)
    {
      switch(auto decl = decls[0]; decl->kind())
      {
        case Decl::Module:
          usein->decl = decl;
          break;

        case Decl::Import:
          usein->decl = decl_cast<ImportDecl>(decl)->decl;
          break;

        case Decl::TypeArg:
        case Decl::TypeAlias:
        case Decl::Struct:
        case Decl::Union:
        case Decl::VTable:
        case Decl::Concept:
        case Decl::Enum:
          usein->decl = decl;
          break;

        case Decl::Function:
        case Decl::DeclScoped:
          usein->decl->owner = declscope.owner;
          break;

        default:
          ctx.diag.error("invalid using declaration", usein, usein->loc());
          ctx.diag << "  type: '" << *decl << "'\n";
          return;
      }
    }

    usein->flags |= UsingDecl::Resolved;
    usein->flags &= ~UsingDecl::Resolving;
  }

  //|///////////////////// resolve_initialiser //////////////////////////////
  void resolve_decl(TyperContext &ctx, Scope const &scope, InitialiserDecl *init, Sema &sema)
  {
    vector<Decl*> decls;

    if (init->name == Ident::kw_this)
      return;

    for(auto sx = scope; sx; sx = parent_scope(std::move(sx)))
    {
      find_decls(ctx, sx, init->name, QueryFlags::Fields, decls, sema);

      if (decls.empty())
      {
        if (is_tag_scope(sx))
          break;

        continue;
      }

      break;
    }

    if (decls.empty())
    {
      ctx.diag.error("no such field", init, init->loc());
      return;
    }
  }

  //|///////////////////// resolve_decl /////////////////////////////////////
  void resolve_decl(TyperContext &ctx, Scope const &scope, Decl *&decl, Sema &sema)
  {
    switch(decl->kind())
    {
      case Decl::DeclRef:
        resolve_decl(ctx, scope, decl_cast<DeclRefDecl>(decl), sema);
        break;

      case Decl::DeclScoped:
        resolve_decl(ctx, scope, decl_cast<DeclScopedDecl>(decl), sema);
        break;

      case Decl::TypeName:
        resolve_decl(ctx, scope, decl_cast<TypeNameDecl>(decl), sema);
        break;

      case Decl::DeclName:
        resolve_decl(ctx, scope, decl_cast<DeclNameDecl>(decl), sema);
        break;

      case Decl::TypeOf:
        resolve_decl(ctx, scope, decl_cast<TypeOfDecl>(decl), sema);
        break;

      case Decl::Using:
        resolve_decl(ctx, scope, decl_cast<UsingDecl>(decl), sema);
        break;

      case Decl::Initialiser:
        resolve_decl(ctx, scope, decl_cast<InitialiserDecl>(decl), sema);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// resolve_typeref //////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, Decl *decl, DeclRefDecl *declref, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    size_t k = 0;

    switch(decl->kind())
    {
      case Decl::TypeArg:
        typeref->decl = decl;
        break;

      case Decl::TypeAlias:
        typeref->decl = decl;
        typeref->args = child_scope(ctx, scope, decl_cast<TypeAliasDecl>(decl), k, declref->args, declref->namedargs, sema).typeargs;
        break;

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Concept:
      case Decl::Enum:
        typeref->decl = decl;
        typeref->args = child_scope(ctx, scope, decl_cast<TagDecl>(decl), k, declref->args, declref->namedargs, sema).typeargs;
        break;

      case Decl::EnumConstant:
        typeref->decl = decl;
        typeref->args = scope.typeargs;
        break;

      default:
        ctx.diag.error("invalid type", scope, declref->loc());
        ctx.diag << "  type: '" << *decl << "'\n";
        return;
    }

    if (k != declref->args.size() + declref->namedargs.size())
    {
      diag_args(ctx, declref, decl, sema);
    }

    resolve_type(ctx, scope, dst, sema);
  }

  //|///////////////////// resolve_typearg //////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, TypeArgDecl *typearg, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    dst = resolve_typearg(ctx, typearg, sema);
  }

  //|///////////////////// resolve_typealias ////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, TypeAliasDecl *alias, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    resolve_type(ctx, alias, alias->type, sema);

    if (!is_dependant_type(ctx, alias->type))
    {
      dst = resolve_alias(ctx, Scope(alias, typeref->args), alias->type, sema);
    }
  }

  //|///////////////////// resolve_tagdecl //////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, TagDecl *tagdecl, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    Scope tx(tagdecl, typeref->args);

    for(auto sx = get<Decl*>(tx.owner); sx; sx = parent_decl(sx))
    {
      vector<Decl*> *declargs = nullptr;

      switch (sx->kind())
      {
        case Decl::Function:
          declargs = &decl_cast<FunctionDecl>(sx)->args;
          break;

        case Decl::Struct:
        case Decl::Union:
        case Decl::VTable:
        case Decl::Concept:
        case Decl::Lambda:
        case Decl::Enum:
          declargs = &decl_cast<TagDecl>(sx)->args;
          break;

        default:
          break;
      }

      if (declargs)
      {
        for(auto &arg : *declargs)
        {
          auto j = lower_bound(tx.typeargs.begin(), tx.typeargs.end(), arg, [](auto &lhs, auto &rhs) { return lhs.first < rhs; });

          if (j == tx.typeargs.end() || j->first != arg)
          {
            tx.typeargs.emplace(j, arg, resolve_typearg(ctx, arg, sema));
          }
        }
      }
    }

    dst = sema.make_tagtype(tagdecl, std::move(tx.typeargs));
  }

  //|///////////////////// resolve_constant /////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, EnumConstantDecl *constant, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    resolve_type(ctx, scope, decl_cast<EnumDecl>(get<Decl*>(scope.owner)), typeref, dst, sema);

    dst = sema.make_constant(constant, dst);
  }

  //|///////////////////// resolve_typeof ///////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, TypeOfDecl *typedecl, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    assert(typeref->args.empty());

    resolve_expr(ctx, scope, typedecl->expr, sema);

    switch(typedecl->expr->kind())
    {
      case Expr::BoolLiteral:
        dst = type(Builtin::Type_Bool);
        break;

      case Expr::CharLiteral:
        dst = type(Builtin::Type_Char);
        break;

      case Expr::IntLiteral:
        dst = type(Builtin::Type_IntLiteral);
        break;

      case Expr::FloatLiteral:
        dst = type(Builtin::Type_FloatLiteral);
        break;

      case Expr::StringLiteral:
        dst = type(Builtin::Type_StringLiteral);
        break;

      case Expr::Typeid:
        dst = type(Builtin::Type_TypeidLiteral);
        break;

      case Expr::Lambda:
        resolve_type(ctx, scope, decl_cast<TagDecl>(expr_cast<LambdaExpr>(typedecl->expr)->decl), typeref, dst, sema);
        break;

      default:
        break;
    }
  }

  //|///////////////////// resolve_concept //////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, ConceptDecl *koncept, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    auto arg = make_typearg(ctx, Ident::kw_var, koncept->loc(), sema);

    dst = sema.make_typearg(arg, koncept, std::move(typeref->args));
  }

  //|///////////////////// resolve_typename /////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, TypeNameDecl *typenam, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    resolve_type(ctx, scope, typenam->type, sema);

    dst = typenam->type;
  }

  //|///////////////////// resolve_typeref //////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, DeclRefDecl *declref, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    vector<Decl*> decls;

    resolve_decl(ctx, scope, declref, sema);

    for(auto sx = scope; sx; sx = parent_scope(std::move(sx)))
    {
      find_decls(ctx, sx, declref->name, QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Enums | QueryFlags::Usings, decls, sema);

      if (decls.empty())
        continue;

      break;
    }

    if (decls.empty())
    {
      for(auto sx = scope; sx; sx = parent_scope(std::move(sx)))
      {
        find_decls(ctx, sx, declref->name, QueryFlags::Functions | QueryFlags::Parameters | QueryFlags::Variables | QueryFlags::Usings, decls, sema);

        if (decls.empty())
          continue;

        break;
      }

      if (decls.size() == 1)
      {
        dst = sema.make_typelit(sema.make_declref_expression(declref, declref->loc()));
        return;
      }

      decls.clear();
    }

    if (any_of(decls.begin(), decls.end(), [](auto k) { return k->kind() == Decl::Run; }))
    {
      decls.erase(remove_if(decls.begin(), decls.end(), [&](auto &decl) { return decl->kind() == Decl::Run; }), decls.end());

      if (decls.empty())
        return;
    }

    if (any_of(decls.begin(), decls.end(), [](auto k) { return k->flags & Decl::Conditional; }))
      return;

    if (decls.size() != 1)
    {
      if (decls.empty())
        ctx.diag.error("no such type", scope, declref->loc());
      else
        ctx.diag.error("ambiguous type reference", scope, declref->loc());

      for(auto &decl : decls)
        ctx.diag << "  type: '" << *decl << "'\n";

      return;
    }

    if ((decls[0]->flags & TypeAliasDecl::Implicit) && !declref->argless)
      decls[0] = get<Decl*>(decls[0]->owner);

    resolve_type(ctx, parent_scope(decls[0]), decls[0], declref, typeref, dst, sema);
  }

  //|///////////////////// resolve_typeref //////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, DeclScopedDecl *scoped, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    long queryflags = 0;
    Scope declscope = ctx.stack.front();

    vector<Decl*> decls;

    resolve_decl(ctx, scope, scoped, sema);

    if (scoped->decls[0]->kind() == Decl::TypeOf)
      return;

    if (scoped->decls[0]->kind() == Decl::TypeName)
      return;

    if (auto declref = decl_cast<DeclRefDecl>(scoped->decls[0]); declref->name != Ident::op_scope)
    {
      for(auto sx = scope; sx; sx = parent_scope(std::move(sx)))
      {
        find_decls(ctx, sx, declref->name, QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Usings | queryflags, decls, sema);

        if (decls.empty())
          continue;

        if (decls[0]->kind() == Decl::Run)
          return;

        if (decls[0]->kind() == Decl::TypeArg)
          return;

        if (decls[0]->kind() == Decl::TypeAlias && is_dependant_type(ctx, decl_cast<TypeAliasDecl>(decls[0])->type))
          return;

        size_t k = 0;

        if ((decls[0]->flags & TypeAliasDecl::Implicit) && !declref->argless)
          decls[0] = get<Decl*>(decls[0]->owner);

        declscope = decl_scope(ctx, outer_scope(sx, decls[0]), decls[0], k, declref->args, declref->namedargs, sema);

        if (k != declref->args.size() + declref->namedargs.size())
        {
          diag_args(ctx, declref, decls[0], sema);
          return;
        }

        break;
      }

      if (decls.size() != 1)
      {
        ctx.diag.error("no such scope", scope, declref->loc());
        return;
      }

      if (decls[0]->kind() == Decl::Import || decls[0]->kind() == Decl::Module)
        queryflags |= QueryFlags::Public;

      decls.clear();
    }

    for(size_t i = 1; i + 1 < scoped->decls.size(); ++i)
    {
      auto declref = decl_cast<DeclRefDecl>(scoped->decls[i]);

      find_decls(ctx, declscope, declref->name, QueryFlags::Modules | QueryFlags::Imports | QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Usings | queryflags, decls, sema);

      if (any_of(decls.begin(), decls.end(), [](auto k) { return k->kind() == Decl::Run; }))
      {
        decls.erase(remove_if(decls.begin(), decls.end(), [&](auto &decl) { return decl->kind() == Decl::Run; }), decls.end());

        if (decls.empty())
          return;
      }

      if (any_of(decls.begin(), decls.end(), [](auto k) { return k->flags & Decl::Conditional; }))
        return;

      if (decls.size() != 1)
      {
        ctx.diag.error("no such scope", scope, declref->loc());
        return;
      }

      size_t k = 0;

      declscope = decl_scope(ctx, outer_scope(declscope, decls[0]), decls[0], k, declref->args, declref->namedargs, sema);

      if (k != declref->args.size() + declref->namedargs.size())
      {
        diag_args(ctx, declref, decls[0], sema);
        return;
      }

      if (decls[0]->kind() == Decl::Import || decls[0]->kind() == Decl::Module)
        queryflags |= QueryFlags::Public;

      decls.clear();
    }

    if (auto declref = decl_cast<DeclRefDecl>(scoped->decls.back()))
    {
      find_decls(ctx, declscope, declref->name, QueryFlags::Types | QueryFlags::Concepts | QueryFlags::Enums | QueryFlags::Usings | queryflags, decls, sema);

      if (decls.empty())
      {
        find_decls(ctx, declscope, declref->name, QueryFlags::Functions | QueryFlags::Usings | queryflags, decls, sema);

        if (decls.size() == 1 && is_fn_decl(decls[0]))
        {
          dst = sema.make_typelit(sema.make_call_expression(scoped, scoped->loc()));
          return;
        }

        decls.clear();
      }

      if (any_of(decls.begin(), decls.end(), [](auto k) { return k->kind() == Decl::Run; }))
      {
        decls.erase(remove_if(decls.begin(), decls.end(), [&](auto &decl) { return decl->kind() == Decl::Run; }), decls.end());

        if (decls.empty())
          return;
      }

      if (any_of(decls.begin(), decls.end(), [](auto k) { return k->flags & Decl::Conditional; }))
        return;

      if (decls.size() != 1)
      {
        if (decls.empty())
          ctx.diag.error("no such type", scope, declref->loc());
        else
          ctx.diag.error("ambiguous type reference", scope, declref->loc());

        for(auto &decl : decls)
          ctx.diag << "  type: '" << *decl << "'\n";

        return;
      }

      resolve_type(ctx, declscope, decls[0], declref, typeref, dst, sema);
    }
  }

  //|///////////////////// resolve_typeref //////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, TypeRefType *typeref, Type *&dst, Sema &sema)
  {
    for(auto &[decl, type] : typeref->args)
    {
      resolve_type(ctx, scope, type, sema);
    }

    switch(typeref->decl->kind())
    {
      case Decl::DeclRef:
        resolve_type(ctx, scope, decl_cast<DeclRefDecl>(typeref->decl), typeref, dst, sema);
        break;

      case Decl::DeclScoped:
        resolve_type(ctx, scope, decl_cast<DeclScopedDecl>(typeref->decl), typeref, dst, sema);
        break;

      case Decl::TypeOf:
        resolve_type(ctx, scope, decl_cast<TypeOfDecl>(typeref->decl), typeref, dst, sema);
        break;

      case Decl::TypeArg:
        resolve_type(ctx, scope, decl_cast<TypeArgDecl>(typeref->decl), typeref, dst, sema);
        break;

      case Decl::TypeAlias:
        resolve_type(ctx, scope, decl_cast<TypeAliasDecl>(typeref->decl), typeref, dst, sema);
        break;

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Lambda:
      case Decl::Enum:
        resolve_type(ctx, scope, decl_cast<TagDecl>(typeref->decl), typeref, dst, sema);
        break;

      case Decl::EnumConstant:
        resolve_type(ctx, scope, decl_cast<EnumConstantDecl>(typeref->decl), typeref, dst, sema);
        break;

      case Decl::Concept:
        resolve_type(ctx, scope, decl_cast<ConceptDecl>(typeref->decl), typeref, dst, sema);
        break;

      case Decl::TypeName:
        resolve_type(ctx, scope, decl_cast<TypeNameDecl>(typeref->decl), typeref, dst, sema);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// resolve_type /////////////////////////////////////
  void resolve_type(TyperContext &ctx, Scope const &scope, Type *&type, Sema &sema)
  {
    auto rr = recursion_counter<__COUNTER__>();

    if (rr.count > 256)
      throw runtime_error("recursion limit reached during type resolution");

    switch (type->klass())
    {
      case Type::Builtin:
        break;

      case Type::Const:
        resolve_type(ctx, scope, type_cast<ConstType>(type)->type, sema);
        break;

      case Type::Pointer:
        resolve_type(ctx, scope, type_cast<PointerType>(type)->type, sema);
        break;

      case Type::Reference:
        resolve_type(ctx, scope, type_cast<ReferenceType>(type)->type, sema);
        break;

      case Type::Array:
        resolve_type(ctx, scope, type_cast<ArrayType>(type)->type, sema);
        resolve_type(ctx, scope, type_cast<ArrayType>(type)->size, sema);
        break;

      case Type::Tuple:
        for(auto &field : type_cast<TupleType>(type)->fields)
          resolve_type(ctx, scope, field, sema);
        break;

      case Type::Function:
        resolve_type(ctx, scope, type_cast<FunctionType>(type)->returntype, sema);
        resolve_type(ctx, scope, type_cast<FunctionType>(type)->paramtuple, sema);
        break;

      case Type::Pack:
        resolve_type(ctx, scope, type_cast<PackType>(type)->type, sema);
        break;

      case Type::Unpack:
        resolve_type(ctx, scope, type_cast<UnpackType>(type)->type, sema);
        break;

      case Type::TypeRef:
        resolve_type(ctx, scope, type_cast<TypeRefType>(type), type, sema);
        break;

      case Type::QualArg:
        resolve_type(ctx, scope, type_cast<QualArgType>(type)->type, sema);
        break;

      case Type::TypeLit:
        resolve_expr(ctx, scope, type_cast<TypeLitType>(type)->value, sema);
        break;

      case Type::TypeArg:
      case Type::Tag:
        break;

      default:
        assert(false);
    }

    if (is_const_type(type) && is_const_type(type_cast<ConstType>(type)->type))
      type = remove_const_type(type);
  }

  //|///////////////////// arrayliteral /////////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, ArrayLiteralExpr *arrayliteral, Sema &sema)
  {
    for(auto &element : arrayliteral->elements)
    {
      resolve_expr(ctx, scope, element, sema);
    }

    resolve_type(ctx, scope, arrayliteral->size, sema);
  }

  //|///////////////////// compoundliteral //////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, CompoundLiteralExpr *compoundliteral, Sema &sema)
  {
    for(auto &field: compoundliteral->fields)
    {
      resolve_expr(ctx, scope, field, sema);
    }
  }

  //|///////////////////// exprref_expression ///////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, ExprRefExpr *exprref, Sema &sema)
  {
    resolve_expr(ctx, scope, exprref->expr, sema);
  }

  //|///////////////////// paren_expression /////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, ParenExpr *paren, Sema &sema)
  {
    resolve_expr(ctx, scope, paren->subexpr, sema);
  }

  //|///////////////////// unary_expression /////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, UnaryOpExpr *unaryop, Sema &sema)
  {
    resolve_expr(ctx, scope, unaryop->subexpr, sema);
  }

  //|///////////////////// binary_expression ////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, BinaryOpExpr *binaryop, Sema &sema)
  {
    resolve_expr(ctx, scope, binaryop->lhs, sema);
    resolve_expr(ctx, scope, binaryop->rhs, sema);
  }

  //|///////////////////// ternary_expression ///////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, TernaryOpExpr *ternaryop, Sema &sema)
  {
    resolve_expr(ctx, scope, ternaryop->cond, sema);
    resolve_expr(ctx, scope, ternaryop->lhs, sema);
    resolve_expr(ctx, scope, ternaryop->rhs, sema);
  }

  //|///////////////////// call_expression //////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, CallExpr *call, Sema &sema)
  {
    for(auto &parm : call->parms)
    {
      resolve_expr(ctx, scope, parm, sema);
    }

    for(auto &[name, parm] : call->namedparms)
    {
      resolve_expr(ctx, scope, parm, sema);
    }

    if (call->base)
    {
      resolve_expr(ctx, scope, call->base, sema);
    }

    resolve_decl(ctx, scope, call->callee, sema);
  }

  //|///////////////////// sizeof_expression ////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, SizeofExpr *call, Sema &sema)
  {
    if (call->type)
    {
      resolve_type(ctx, scope, call->type, sema);
    }

    if (call->expr)
    {
      resolve_expr(ctx, scope, call->expr, sema);
    }
  }

  //|///////////////////// alignof_expression ///////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, AlignofExpr *call, Sema &sema)
  {
    if (call->type)
    {
      resolve_type(ctx, scope, call->type, sema);
    }

    if (call->expr)
    {
      resolve_expr(ctx, scope, call->expr, sema);
    }
  }

  //|///////////////////// offsetof_expression //////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, OffsetofExpr *call, Sema &sema)
  {
    resolve_type(ctx, scope, call->type, sema);
  }

  //|///////////////////// instanceof_expression ////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, InstanceofExpr *call, Sema &sema)
  {
    resolve_type(ctx, scope, call->type, sema);
    resolve_type(ctx, scope, call->instance, sema);
  }

  //|///////////////////// typeid_expression ////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, TypeidExpr *call, Sema &sema)
  {
    resolve_decl(ctx, scope, call->decl, sema);
  }

  //|///////////////////// cast_expression //////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, CastExpr *call, Sema &sema)
  {
    resolve_type(ctx, scope, call->type, sema);

    resolve_expr(ctx, scope, call->expr, sema);
  }

  //|///////////////////// new_expression ///////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, NewExpr *call, Sema &sema)
  {
    resolve_type(ctx, scope, call->type, sema);

    resolve_expr(ctx, scope, call->address, sema);

    for(auto &parm : call->parms)
    {
      resolve_expr(ctx, scope, parm, sema);
    }

    for(auto &[name, parm] : call->namedparms)
    {
      resolve_expr(ctx, scope, parm, sema);
    }
  }

  //|///////////////////// requires_expression //////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, RequiresExpr *requires, Sema &sema)
  {
    typer_decl(ctx, requires->decl, sema);
  }

  //|///////////////////// match_expression /////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, MatchExpr *match, Sema &sema)
  {
    typer_decl(ctx, match->decl, sema);
  }

  //|///////////////////// lambda_expression ////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, LambdaExpr *lambda, Sema &sema)
  {
    typer_decl(ctx, lambda->decl, sema);
  }

  //|///////////////////// declref_expression ///////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, DeclRefExpr *declexpr, Expr *&dst, Sema &sema)
  {
    if (declexpr->base)
    {
      resolve_expr(ctx, scope, declexpr->base, sema);
    }

    if (declexpr->decl->kind() == Decl::DeclRef)
    {
      auto declref = decl_cast<DeclRefDecl>(declexpr->decl);

      if (!declexpr->base && declref->name == Ident::kw_void && declref->argless)
        dst = sema.make_void_literal(declexpr->loc());

      if (!declexpr->base && declref->name == Ident::kw_null && declref->argless)
        dst = sema.make_pointer_literal(declexpr->loc());
    }

    resolve_decl(ctx, scope, declexpr->decl, sema);
  }

  //|///////////////////// fragment_expression //////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, FragmentExpr *fragment, Sema &sema)
  {
    for(auto &arg : fragment->args)
    {
      resolve_expr(ctx, scope, arg, sema);
    }
  }

  //|///////////////////// resolve_expr ///////////////////////////////////////
  void resolve_expr(TyperContext &ctx, Scope const &scope, Expr *&expr, Sema &sema)
  {
    switch (expr->kind())
    {
      case Expr::BoolLiteral:
      case Expr::CharLiteral:
      case Expr::IntLiteral:
      case Expr::FloatLiteral:
      case Expr::StringLiteral:
      case Expr::PointerLiteral:
      case Expr::FunctionPointer:
        break;

      case Expr::ArrayLiteral:
        resolve_expr(ctx, scope, expr_cast<ArrayLiteralExpr>(expr), sema);
        break;

      case Expr::CompoundLiteral:
        resolve_expr(ctx, scope, expr_cast<CompoundLiteralExpr>(expr), sema);
        break;

      case Expr::ExprRef:
        resolve_expr(ctx, scope, expr_cast<ExprRefExpr>(expr), sema);
        break;

      case Expr::Paren:
        resolve_expr(ctx, scope, expr_cast<ParenExpr>(expr), sema);
        break;

      case Expr::UnaryOp:
        resolve_expr(ctx, scope, expr_cast<UnaryOpExpr>(expr), sema);
        break;

      case Expr::BinaryOp:
        resolve_expr(ctx, scope, expr_cast<BinaryOpExpr>(expr), sema);
        break;

      case Expr::TernaryOp:
        resolve_expr(ctx, scope, expr_cast<TernaryOpExpr>(expr), sema);
        break;

      case Expr::Call:
        resolve_expr(ctx, scope, expr_cast<CallExpr>(expr), sema);
        break;

      case Expr::Sizeof:
        resolve_expr(ctx, scope, expr_cast<SizeofExpr>(expr), sema);
        break;

      case Expr::Alignof:
        resolve_expr(ctx, scope, expr_cast<AlignofExpr>(expr), sema);
        break;

      case Expr::Offsetof:
        resolve_expr(ctx, scope, expr_cast<OffsetofExpr>(expr), sema);
        break;

      case Expr::Instanceof:
        resolve_expr(ctx, scope, expr_cast<InstanceofExpr>(expr), sema);
        break;

      case Expr::Typeid:
        resolve_expr(ctx, scope, expr_cast<TypeidExpr>(expr), sema);
        break;

      case Expr::Cast:
        resolve_expr(ctx, scope, expr_cast<CastExpr>(expr), sema);
        break;

      case Expr::New:
        resolve_expr(ctx, scope, expr_cast<NewExpr>(expr), sema);
        break;

      case Expr::Requires:
        resolve_expr(ctx, scope, expr_cast<RequiresExpr>(expr), sema);
        break;

      case Expr::Match:
        resolve_expr(ctx, scope, expr_cast<MatchExpr>(expr), sema);
        break;

      case Expr::Lambda:
        resolve_expr(ctx, scope, expr_cast<LambdaExpr>(expr), sema);
        break;

      case Expr::DeclRef:
        resolve_expr(ctx, scope, expr_cast<DeclRefExpr>(expr), expr, sema);
        break;

      case Expr::Fragment:
        resolve_expr(ctx, scope, expr_cast<FragmentExpr>(expr), sema);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// voidvar //////////////////////////////////////////
  void typer_decl(TyperContext &ctx, VoidVarDecl *var, Sema &sema)
  {
    resolve_type(ctx, ctx.stack.back(), var->type, sema);
  }

  //|///////////////////// stmtvar //////////////////////////////////////////
  void typer_decl(TyperContext &ctx, StmtVarDecl *var, Sema &sema)
  {
    resolve_type(ctx, ctx.stack.back(), var->type, sema);

    resolve_expr(ctx, ctx.stack.back(), var->value, sema);
  }

  //|///////////////////// parmvar //////////////////////////////////////////
  void typer_decl(TyperContext &ctx, ParmVarDecl *var, Sema &sema)
  {
    resolve_type(ctx, ctx.stack.back(), var->type, sema);

#if DEFAULT_SUBSTITUTION
    var->type = substitute_defaulted(ctx, ctx.stack.back(), var->type, sema);
#endif

    if (var->defult)
    {
      resolve_expr(ctx, ctx.stack.back(), var->defult, sema);
    }
  }

  //|///////////////////// thisvar //////////////////////////////////////////
  void typer_decl(TyperContext &ctx, ThisVarDecl *var, Sema &sema)
  {
    resolve_type(ctx, ctx.stack.back(), var->type, sema);
  }

  //|///////////////////// errorvar /////////////////////////////////////////
  void typer_decl(TyperContext &ctx, ErrorVarDecl *var, Sema &sema)
  {
    resolve_type(ctx, ctx.stack.back(), var->type, sema);
  }

  //|///////////////////// typearg //////////////////////////////////////////
  void typer_decl(TyperContext &ctx, TypeArgDecl *typearg, Sema &sema)
  {
    if (typearg->defult)
    {
      resolve_type(ctx, ctx.stack.back(), typearg->defult, sema);
    }
  }

  //|///////////////////// declref //////////////////////////////////////////
  void typer_decl(TyperContext &ctx, DeclRefDecl *declref, Sema &sema)
  {
    resolve_decl(ctx, ctx.stack.back(), declref, sema);
  }

  //|///////////////////// declscoped ///////////////////////////////////////
  void typer_decl(TyperContext &ctx, DeclScopedDecl *scoped, Sema &sema)
  {
    for(auto &decl : scoped->decls)
    {
      resolve_decl(ctx, ctx.stack.back(), decl, sema);
    }
  }

  //|///////////////////// typealias ////////////////////////////////////////
  void typer_decl(TyperContext &ctx, TypeAliasDecl *typealias, Sema &sema)
  {
    ctx.stack.emplace_back(typealias);

    for(auto &arg : typealias->args)
    {
      typer_decl(ctx, arg, sema);
    }

    resolve_type(ctx, ctx.stack.back(), typealias->type, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// tagdecl //////////////////////////////////////////
  void typer_decl(TyperContext &ctx, TagDecl *tagdecl, Sema &sema)
  {
    for(auto &arg : tagdecl->args)
    {
      typer_decl(ctx, arg, sema);
    }

    if (tagdecl->basetype)
    {
      resolve_type(ctx, ctx.stack.back(), tagdecl->basetype, sema);
    }

    for(auto &decl : tagdecl->decls)
    {
      typer_decl(ctx, decl, sema);
    }
  }

  //|///////////////////// struct ///////////////////////////////////////////
  void typer_decl(TyperContext &ctx, StructDecl *strct, Sema &sema)
  {
    ctx.stack.emplace_back(strct);

    typer_decl(ctx, decl_cast<TagDecl>(strct), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// union ////////////////////////////////////////////
  void typer_decl(TyperContext &ctx, UnionDecl *unnion, Sema &sema)
  {
    ctx.stack.emplace_back(unnion);

    typer_decl(ctx, decl_cast<TagDecl>(unnion), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// vtable ///////////////////////////////////////////
  void typer_decl(TyperContext &ctx, VTableDecl *vtable, Sema &sema)
  {
    ctx.stack.emplace_back(vtable);

    typer_decl(ctx, decl_cast<TagDecl>(vtable), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// concept //////////////////////////////////////////
  void typer_decl(TyperContext &ctx, ConceptDecl *koncept, Sema &sema)
  {
    ctx.stack.emplace_back(koncept);

    typer_decl(ctx, decl_cast<TagDecl>(koncept), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// requires /////////////////////////////////////////
  void typer_decl(TyperContext &ctx, RequiresDecl *reqires, Sema &sema)
  {
    ctx.stack.emplace_back(reqires);

    typer_decl(ctx, reqires->fn, sema);

    if (reqires->requirestype)
    {
      resolve_type(ctx, ctx.stack.back(), reqires->requirestype, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// lambda ///////////////////////////////////////////
  void typer_decl(TyperContext &ctx, LambdaDecl *lambda, Sema &sema)
  {
    ctx.stack.emplace_back(lambda);

    typer_decl(ctx, decl_cast<TagDecl>(lambda), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// enum /////////////////////////////////////////////
  void typer_decl(TyperContext &ctx, EnumDecl *enumm, Sema &sema)
  {
    ctx.stack.emplace_back(enumm);

    typer_decl(ctx, decl_cast<TagDecl>(enumm), sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// constant /////////////////////////////////////////
  void typer_decl(TyperContext &ctx, EnumConstantDecl *constant, Sema &sema)
  {
    if (constant->value)
    {
      resolve_expr(ctx, ctx.stack.back(), constant->value, sema);
    }
  }

  //|///////////////////// field ////////////////////////////////////////////
  void typer_decl(TyperContext &ctx, FieldVarDecl *field, Sema &sema)
  {
    resolve_type(ctx, ctx.stack.back(), field->type, sema);

    if (field->defult)
    {
      resolve_expr(ctx, ctx.stack.back(), field->defult, sema);
    }
  }

  //|///////////////////// initialiser //////////////////////////////////////
  void typer_decl(TyperContext &ctx, InitialiserDecl *init, Sema &sema)
  {
    for(auto &parm : init->parms)
    {
      resolve_expr(ctx, ctx.stack.back(), parm, sema);
    }

    for(auto &[name, parm] : init->namedparms)
    {
      resolve_expr(ctx, ctx.stack.back(), parm, sema);
    }

    resolve_decl(ctx, ctx.stack.back(), init, sema);
  }

  //|///////////////////// case /////////////////////////////////////////////
  void typer_decl(TyperContext &ctx, CaseDecl *casse, Sema &sema)
  {
    ctx.stack.emplace_back(casse);

    if (casse->label)
    {
      resolve_expr(ctx, ctx.stack.back(), casse->label, sema);
    }

    if (casse->parm)
    {
      typer_decl(ctx, casse->parm, sema);
    }

    if (casse->body)
    {
      typer_statement(ctx, casse->body, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// casevar //////////////////////////////////////////
  void typer_decl(TyperContext &ctx, CaseVarDecl *var, Sema &sema)
  {
    resolve_type(ctx, ctx.stack.back(), var->type, sema);

    if (var->value)
    {
      resolve_expr(ctx, ctx.stack.back(), var->value, sema);
    }
  }

  //|///////////////////// import ///////////////////////////////////////////
  void typer_decl(TyperContext &ctx, ImportDecl *imprt, Sema &sema)
  {
    for(auto &usein : imprt->usings)
    {
      resolve_decl(ctx, imprt->decl, usein, sema);
    }
  }

  //|///////////////////// using ////////////////////////////////////////////
  void typer_decl(TyperContext &ctx, UsingDecl *usein, Sema &sema)
  {
    resolve_decl(ctx, ctx.stack.back(), usein, sema);
  }

  //|///////////////////// function /////////////////////////////////////////
  void typer_decl(TyperContext &ctx, FunctionDecl *fn, Sema &sema)
  {
    ctx.stack.emplace_back(fn);

    for(auto &arg : fn->args)
    {
      typer_decl(ctx, arg, sema);
    }

    for(auto &parm : fn->parms)
    {
      typer_decl(ctx, parm, sema);
    }

    if (fn->throws)
    {
      resolve_expr(ctx, ctx.stack.back(), fn->throws, sema);
    }

    if (fn->returntype)
    {
      resolve_type(ctx, ctx.stack.back(), fn->returntype, sema);

      if (is_const_type(fn->returntype))
      {
        fn->returntype = remove_const_type(fn->returntype);
      }
    }

    if (fn->match)
    {
      resolve_expr(ctx, ctx.stack.back(), fn->match, sema);
    }

    if (fn->where)
    {
      resolve_expr(ctx, ctx.stack.back(), fn->where, sema);
    }

    for(auto &init : fn->inits)
    {
      typer_decl(ctx, init, sema);
    }

    if (fn->body)
    {
      typer_statement(ctx, fn->body, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// run //////////////////////////////////////////////
  void typer_decl(TyperContext &ctx, RunDecl *run, Sema &sema)
  {
    typer_decl(ctx, run->fn, sema);
  }

  //|///////////////////// if ///////////////////////////////////////////////
  void typer_decl(TyperContext &ctx, IfDecl *ifd, Sema &sema)
  {
    resolve_expr(ctx, ctx.stack.back(), ifd->cond, sema);

    if ((ifd->flags & IfDecl::ResolvedTrue) || !(ifd->flags & IfDecl::ResolvedFalse))
    {
      for(auto &decl: ifd->decls)
      {
        typer_decl(ctx, decl, sema);
      }
    }

    if ((ifd->flags & IfDecl::ResolvedFalse) || !(ifd->flags & IfDecl::ResolvedTrue))
    {
      if (ifd->elseif)
      {
        typer_decl(ctx, ifd->elseif, sema);
      }
    }
  }

  //|///////////////////// typer_decl ///////////////////////////////////////
  void typer_decl(TyperContext &ctx, Decl *decl, Sema &sema)
  {
    switch(decl->kind())
    {
      case Decl::VoidVar:
        typer_decl(ctx, decl_cast<VoidVarDecl>(decl), sema);
        break;

      case Decl::StmtVar:
        typer_decl(ctx, decl_cast<StmtVarDecl>(decl), sema);
        break;

      case Decl::ParmVar:
        typer_decl(ctx, decl_cast<ParmVarDecl>(decl), sema);
        break;

      case Decl::ThisVar:
        typer_decl(ctx, decl_cast<ThisVarDecl>(decl), sema);
        break;

      case Decl::ErrorVar:
        typer_decl(ctx, decl_cast<ErrorVarDecl>(decl), sema);
        break;

      case Decl::TypeArg:
        typer_decl(ctx, decl_cast<TypeArgDecl>(decl), sema);
        break;

      case Decl::DeclRef:
        typer_decl(ctx, decl_cast<DeclRefDecl>(decl), sema);
        break;

      case Decl::DeclScoped:
        typer_decl(ctx, decl_cast<DeclScopedDecl>(decl), sema);
        break;

      case Decl::TypeAlias:
        typer_decl(ctx, decl_cast<TypeAliasDecl>(decl), sema);
        break;

      case Decl::Struct:
        typer_decl(ctx, decl_cast<StructDecl>(decl), sema);
        break;

      case Decl::Union:
        typer_decl(ctx, decl_cast<UnionDecl>(decl), sema);
        break;

      case Decl::VTable:
        typer_decl(ctx, decl_cast<VTableDecl>(decl), sema);
        break;

      case Decl::Concept:
        typer_decl(ctx, decl_cast<ConceptDecl>(decl), sema);
        break;

      case Decl::Requires:
        typer_decl(ctx, decl_cast<RequiresDecl>(decl), sema);
        break;

      case Decl::Lambda:
        typer_decl(ctx, decl_cast<LambdaDecl>(decl), sema);
        break;

      case Decl::Enum:
        typer_decl(ctx, decl_cast<EnumDecl>(decl), sema);
        break;

      case Decl::EnumConstant:
        typer_decl(ctx, decl_cast<EnumConstantDecl>(decl), sema);
        break;

      case Decl::FieldVar:
        typer_decl(ctx, decl_cast<FieldVarDecl>(decl), sema);
        break;

      case Decl::Initialiser:
        typer_decl(ctx, decl_cast<InitialiserDecl>(decl), sema);
        break;

      case Decl::Case:
        typer_decl(ctx, decl_cast<CaseDecl>(decl), sema);
        break;

      case Decl::CaseVar:
        typer_decl(ctx, decl_cast<CaseVarDecl>(decl), sema);
        break;

      case Decl::Import:
        typer_decl(ctx, decl_cast<ImportDecl>(decl), sema);
        break;

      case Decl::Using:
        typer_decl(ctx, decl_cast<UsingDecl>(decl), sema);
        break;

      case Decl::Function:
        typer_decl(ctx, decl_cast<FunctionDecl>(decl), sema);
        break;

      case Decl::Run:
        typer_decl(ctx, decl_cast<RunDecl>(decl), sema);
        break;

      case Decl::If:
        typer_decl(ctx, decl_cast<IfDecl>(decl), sema);
        break;

      case Decl::TranslationUnit:
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// injection_statement //////////////////////////////
  void typer_injection_statement(TyperContext &ctx, InjectionStmt *injection, Sema &sema)
  {
    resolve_expr(ctx, ctx.stack.back(), injection->expr, sema);
  }

  //|///////////////////// typer_declaration_statement //////////////////////
  void typer_declaration_statement(TyperContext &ctx, DeclStmt *declstmt, Sema &sema)
  {
    typer_decl(ctx, declstmt->decl, sema);
  }

  //|///////////////////// typer_expression_statement ///////////////////////
  void typer_expression_statement(TyperContext &ctx, ExprStmt *exprstmt, Sema &sema)
  {
    if (exprstmt->expr)
    {
      resolve_expr(ctx, ctx.stack.back(), exprstmt->expr, sema);
    }
  }

  //|///////////////////// typer_if_statement ///////////////////////////////
  void typer_if_statement(TyperContext &ctx, IfStmt *ifs, Sema &sema)
  {
    ctx.stack.emplace_back(ifs);

    for(auto &init : ifs->inits)
    {
      ctx.stack.back().goalpost = init;

      typer_statement(ctx, init, sema);
    }

    ctx.stack.back().goalpost = nullptr;

    resolve_expr(ctx, ctx.stack.back(), ifs->cond, sema);

    if (ifs->stmts[0])
    {
      typer_statement(ctx, ifs->stmts[0], sema);
    }

    if (ifs->stmts[1])
    {
      typer_statement(ctx, ifs->stmts[1], sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// typer_for_statement //////////////////////////////
  void typer_for_statement(TyperContext &ctx, ForStmt *fors, Sema &sema)
  {
    ctx.stack.emplace_back(fors);

    for(auto &init : fors->inits)
    {
      ctx.stack.back().goalpost = init;

      typer_statement(ctx, init, sema);
    }

    ctx.stack.back().goalpost = nullptr;

    if (fors->cond)
    {
      resolve_expr(ctx, ctx.stack.back(), fors->cond, sema);
    }

    typer_statement(ctx, fors->stmt, sema);

    for(auto &iter : fors->iters)
    {
      typer_statement(ctx, iter, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// typer_rof_statement //////////////////////////////
  void typer_rof_statement(TyperContext &ctx, RofStmt *rofs, Sema &sema)
  {
    ctx.stack.emplace_back(rofs);

    for(auto &init : rofs->inits)
    {
      ctx.stack.back().goalpost = init;

      typer_statement(ctx, init, sema);
    }

    ctx.stack.back().goalpost = nullptr;

    if (rofs->cond)
    {
      resolve_expr(ctx, ctx.stack.back(), rofs->cond, sema);
    }

    typer_statement(ctx, rofs->stmt, sema);

    for(auto &iter : rofs->iters)
    {
      typer_statement(ctx, iter, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// typer_while_statement ////////////////////////////
  void typer_while_statement(TyperContext &ctx, WhileStmt *wile, Sema &sema)
  {
    ctx.stack.emplace_back(wile);

    for(auto &init : wile->inits)
    {
      ctx.stack.back().goalpost = init;

      typer_statement(ctx, init, sema);
    }

    for(auto &iter : wile->iters)
    {
      typer_statement(ctx, iter, sema);
    }

    ctx.stack.back().goalpost = nullptr;

    resolve_expr(ctx, ctx.stack.back(), wile->cond, sema);

    typer_statement(ctx, wile->stmt, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// typer_switch_statement ///////////////////////////
  void typer_switch_statement(TyperContext &ctx, SwitchStmt *swtch, Sema &sema)
  {
    ctx.stack.emplace_back(swtch);

    for(auto &init : swtch->inits)
    {
      ctx.stack.back().goalpost = init;

      typer_statement(ctx, init, sema);
    }

    ctx.stack.back().goalpost = nullptr;

    resolve_expr(ctx, ctx.stack.back(), swtch->cond, sema);

    for(auto &decl : swtch->decls)
    {
      typer_decl(ctx, decl, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// typer_goto_statement //////////////////////////////
  void typer_goto_statement(TyperContext &ctx, GotoStmt *gotoo, Sema &sema)
  {
    if (gotoo->label)
    {
      resolve_expr(ctx, ctx.stack.back(), gotoo->label, sema);
    }
  }

  //|///////////////////// typer_try_statement //////////////////////////////
  void typer_try_statement(TyperContext &ctx, TryStmt *trys, Sema &sema)
  {
    ctx.stack.emplace_back(trys);

    typer_statement(ctx, trys->body, sema);
    typer_statement(ctx, trys->handler, sema);

    ctx.stack.pop_back();
  }

  //|///////////////////// typer_throw_statement ////////////////////////////
  void typer_throw_statement(TyperContext &ctx, ThrowStmt *throwe, Sema &sema)
  {
    resolve_expr(ctx, ctx.stack.back(), throwe->expr, sema);
  }

  //|///////////////////// typer_return_statement ///////////////////////////
  void typer_return_statement(TyperContext &ctx, ReturnStmt *retrn, Sema &sema)
  {
    if (retrn->expr)
    {
      resolve_expr(ctx, ctx.stack.back(), retrn->expr, sema);
    }
  }

  //|///////////////////// typer_compound_statement /////////////////////////
  void typer_compound_statement(TyperContext &ctx, CompoundStmt *compound, Sema &sema)
  {
    ctx.stack.emplace_back(compound);

    for(auto &stmt : compound->stmts)
    {
      ctx.stack.back().goalpost = stmt;

      typer_statement(ctx, stmt, sema);
    }

    ctx.stack.pop_back();
  }

  //|///////////////////// typer_statement //////////////////////////////////
  void typer_statement(TyperContext &ctx, Stmt *stmt, Sema &sema)
  {
    switch(stmt->kind())
    {
      case Stmt::Null:
        break;

      case Stmt::Declaration:
        typer_declaration_statement(ctx, stmt_cast<DeclStmt>(stmt), sema);
        break;

      case Stmt::Expression:
        typer_expression_statement(ctx, stmt_cast<ExprStmt>(stmt), sema);
        break;

      case Stmt::If:
        typer_if_statement(ctx, stmt_cast<IfStmt>(stmt), sema);
        break;

      case Stmt::For:
        typer_for_statement(ctx, stmt_cast<ForStmt>(stmt), sema);
        break;

      case Stmt::Rof:
        typer_rof_statement(ctx, stmt_cast<RofStmt>(stmt), sema);
        break;

      case Stmt::While:
        typer_while_statement(ctx, stmt_cast<WhileStmt>(stmt), sema);
        break;

      case Stmt::Switch:
        typer_switch_statement(ctx, stmt_cast<SwitchStmt>(stmt), sema);
        break;

      case Stmt::Goto:
        typer_goto_statement(ctx, stmt_cast<GotoStmt>(stmt), sema);
        break;

      case Stmt::Try:
        typer_try_statement(ctx, stmt_cast<TryStmt>(stmt), sema);
        break;

      case Stmt::Throw:
        typer_throw_statement(ctx, stmt_cast<ThrowStmt>(stmt), sema);
        break;

      case Stmt::Break:
      case Stmt::Continue:
        break;

      case Stmt::Injection:
        typer_injection_statement(ctx, stmt_cast<InjectionStmt>(stmt), sema);
        break;

      case Stmt::Return:
        typer_return_statement(ctx, stmt_cast<ReturnStmt>(stmt), sema);
        break;

      case Stmt::Compound:
        typer_compound_statement(ctx, stmt_cast<CompoundStmt>(stmt), sema);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// index_decl ///////////////////////////////////////
  void index_decl(TyperContext &ctx, ModuleDecl *module, Decl *decl, Sema &sema)
  {
    switch(decl->kind())
    {
      case Decl::TypeAlias:
        module->index[decl_cast<TypeAliasDecl>(decl)->name].push_back(decl);
        break;

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Concept:
      case Decl::Enum:
        module->index[decl_cast<TagDecl>(decl)->name].push_back(decl);
        break;

      case Decl::Import:
        module->index[decl_cast<ImportDecl>(decl)->alias].push_back(decl);
        for(auto &usein : decl_cast<ImportDecl>(decl)->usings)
          index_decl(ctx, module, usein, sema);
        break;

      case Decl::Using:

        switch(auto usein = decl_cast<UsingDecl>(decl); usein->decl->kind())
        {
          case Decl::Module:
          case Decl::Struct:
          case Decl::Union:
          case Decl::VTable:
          case Decl::Concept:
          case Decl::Enum:
          case Decl::TypeAlias:
            module->index[nullptr].push_back(decl);
            break;

          case Decl::DeclRef:
            module->index[decl_cast<DeclRefDecl>(usein->decl)->name].push_back(decl);
            break;

          case Decl::DeclScoped:
            module->index[decl_cast<DeclRefDecl>(decl_cast<DeclScopedDecl>(usein->decl)->decls.back())->name].push_back(decl);
            break;

          default:
            assert(false);
        }
        break;

      case Decl::Function:
        module->index[decl_cast<FunctionDecl>(decl)->name].push_back(decl);
        break;

      case Decl::If:
        if (auto ifd = decl_cast<IfDecl>(decl))
        {
          if (ifd->flags & IfDecl::ResolvedTrue)
            for(auto &decl : ifd->decls)
              index_decl(ctx, module, decl, sema);

          if (auto elseif = ifd->elseif)
            if (ifd->flags & IfDecl::ResolvedFalse)
              index_decl(ctx, module, elseif, sema);
        }
        break;

      case Decl::Run:
        module->index[nullptr].push_back(decl);
        break;

      default:
        assert(false);
    }
  }

  //|///////////////////// typer_module /////////////////////////////////////
  void typer_module(TyperContext &ctx, ModuleDecl *module, Sema &sema)
  {
    ctx.file = module->file();

    ctx.stack.emplace_back(module);

    for(auto &decl : module->decls)
    {
      typer_decl(ctx, decl, sema);
    }

    for(auto &decl : module->decls)
    {
      index_decl(ctx, module, decl, sema);
    }

    module->flags |= ModuleDecl::Indexed;

    ctx.stack.pop_back();
  }
}

//|--------------------- Typer ----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// typer //////////////////////////////////////////////
void typer(AST *ast, Sema &sema, Diag &diag)
{
  TyperContext ctx(diag);

  auto root = decl_cast<TranslationUnitDecl>(ast->root);

  ctx.stack.emplace_back(root);

  for(auto &decl : root->decls)
  {
    switch (decl->kind())
    {
      case Decl::Module:
        typer_module(ctx, decl_cast<ModuleDecl>(decl), sema);
        break;

      default:
        break;
    }
  }

  ctx.stack.pop_back();
}
