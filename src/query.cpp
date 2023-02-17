//
// query.cpp
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "query.h"
#include "builtins.h"
#include <variant>
#include <algorithm>
#include <iostream>

using namespace std;

//|///////////////////// print //////////////////////////////////////////////
ostream &operator <<(ostream &os, Scope const &scope)
{
  visit([&](auto v) { os << *v; }, scope.owner);

  if (scope.typeargs.size() != 0)
  {
    os << ' ';
    os << '[';

    int i = 0;
    for(auto &[k, v] : scope.typeargs)
      os << (!i++ ? "" : ", ") << *k << ": " << *v;

    os << ']';
  }

  if (scope.goalpost)
  {
    os << ' ' << scope.goalpost;
  }

  return os;
}

//|///////////////////// set_type ///////////////////////////////////////////
void Scope::set_type(Decl *in, Type *out)
{
  auto j = lower_bound(typeargs.begin(), typeargs.end(), in, [](auto &lhs, auto &rhs) { return less<>{}(lhs.first, rhs); });

  if (j == typeargs.end() || j->first != in)
  {
    typeargs.emplace(j, in, out);
  }
  else
  {
    j->second = out;
  }
}

//|///////////////////// is_fn_scope ////////////////////////////////////////
bool is_fn_scope(Scope const &scope)
{
  if (auto owner = get_if<Decl*>(&scope.owner); owner && *owner)
    return is_fn_decl(*owner);

  return false;
}

//|///////////////////// is_tag_scope ///////////////////////////////////////
bool is_tag_scope(Scope const &scope)
{
  if (auto owner = get_if<Decl*>(&scope.owner); owner && *owner)
    return is_tag_decl(*owner);

  return false;
}

//|///////////////////// is_decl_scope //////////////////////////////////////
bool is_decl_scope(Scope const &scope)
{
  if (auto owner = get_if<Decl*>(&scope.owner); owner && *owner)
    return true;

  return false;
}

//|///////////////////// is_stmt_scope //////////////////////////////////////
bool is_stmt_scope(Scope const &scope)
{
  if (auto owner = get_if<Stmt*>(&scope.owner); owner && *owner)
    return true;

  return false;
}

//|///////////////////// is_module_scope ////////////////////////////////////
bool is_module_scope(Scope const &scope)
{
  if (auto owner = get_if<Decl*>(&scope.owner); owner && *owner)
    return is_module_decl(*owner);

  return false;
}

//|///////////////////// parent_scope /////////////////////////////////////
Scope parent_scope(Scope scope)
{
  switch(scope.owner.index())
  {
    case 0:
      scope.typeargs.erase(remove_if(scope.typeargs.begin(), scope.typeargs.end(), [&](auto &arg) {
        return arg.first->owner == scope.owner;
      }), scope.typeargs.end());

      scope.goalpost = get<Decl*>(scope.owner);
      scope.owner = get<Decl*>(scope.owner)->owner;
      break;

    case 1:
      scope.goalpost = get<Stmt*>(scope.owner);
      scope.owner = get<Stmt*>(scope.owner)->owner;
      break;
  }

  return scope;
}

//|///////////////////// super_scope ////////////////////////////////////////
Scope super_scope(Scope scope, variant<Decl*, Stmt*> const &owner)
{
  while (scope && scope.owner != owner)
    scope = parent_scope(std::move(scope));

  return scope;
}

//|///////////////////// outer_scope ////////////////////////////////////////
Scope outer_scope(Scope scope, variant<Decl*, Stmt*> const &owner)
{
  auto target = std::visit([&](auto &v) { return v->owner; }, owner);

  if (auto stmt = get_if<Stmt*>(&target); stmt && (*stmt)->kind() == Stmt::Declaration)
    target = (*stmt)->owner;

  return super_scope(std::move(scope), target);
}

//|///////////////////// child_scope ////////////////////////////////////////
Scope child_scope(Scope scope, variant<Decl*, Stmt*> const &owner, vector<pair<Decl*, Type*>> const &typeargs)
{
  Scope child;

  child.owner = owner;
  child.typeargs = std::move(scope.typeargs);

  for(auto &[decl, type] : typeargs)
    child.set_type(decl, type);

  return child;
}

//|///////////////////// seed_stack /////////////////////////////////////////
void seed_stack(vector<Scope> &stack, Scope scope)
{
  if (scope)
  {
    seed_stack(stack, parent_scope(scope));

    stack.emplace_back(std::move(scope));
  }
}

//|///////////////////// parent_decl ////////////////////////////////////////
Decl *parent_decl(Decl *decl)
{
  auto parent = decl->owner;

  while (parent != std::variant<Decl*, Stmt*>())
  {
    if (auto decl = get_if<Decl*>(&parent); decl && *decl)
      return *decl;

    parent = std::visit([](auto &v) { return v->owner; }, parent);
  }

  return nullptr;

}

//|///////////////////// get_unit ///////////////////////////////////////////
TranslationUnitDecl *get_unit(Scope const &scope)
{
  auto parent = scope.owner;

  while (parent != std::variant<Decl*, Stmt*>())
  {
    if (auto decl = get_if<Decl*>(&parent); decl && *decl && (*decl)->kind() == Decl::TranslationUnit)
      return decl_cast<TranslationUnitDecl>(*decl);

    parent = std::visit([](auto &v) { return v->owner; }, parent);
  }

  return nullptr;
}

//|///////////////////// get_module /////////////////////////////////////////
ModuleDecl *get_module(Scope const &scope)
{
  auto parent = scope.owner;

  while (parent != std::variant<Decl*, Stmt*>())
  {
    if (auto decl = get_if<Decl*>(&parent); decl && *decl && (*decl)->kind() == Decl::Module)
      return decl_cast<ModuleDecl>(*decl);

    parent = std::visit([](auto &v) { return v->owner; }, parent);
  }

  return nullptr;
}

//|///////////////////// find_decl //////////////////////////////////////////
void find_decl(Decl *decl, Ident *name, long flags, vector<Decl*> &results)
{
  using namespace QueryFlags;

  if ((flags & Public) && !(decl->flags & Decl::Public))
    return;

  switch (decl->kind())
  {
    case Decl::Module:
      if (decl_cast<ModuleDecl>(decl)->name == name && (flags & Modules))
        results.push_back(decl);
      break;

    case Decl::Function:
      if (decl_cast<FunctionDecl>(decl)->name == name && ((flags & Functions) == Functions || ((flags & Methods) && !(decl->flags & FunctionDecl::Static))))
        results.push_back(decl);
      break;

    case Decl::ParmVar:
      if (decl_cast<VarDecl>(decl)->name == name && (flags & Parameters))
        results.push_back(decl);
      break;

    case Decl::VoidVar:
    case Decl::StmtVar:
    case Decl::CaseVar:
      if (flags & Variables)
      {
        if (decl_cast<VarDecl>(decl)->name == name)
          results.push_back(decl);

        if (auto pattern = decl_cast<VarDecl>(decl)->pattern; pattern)
        {
          switch (pattern->kind())
          {
            case Decl::IdentPattern:
              if (decl_cast<IdentPatternDecl>(pattern)->name == name)
                results.push_back(decl);
              break;

            case Decl::TuplePattern:
              for(auto &binding : decl_cast<TuplePatternDecl>(pattern)->bindings)
                find_decl(binding, name, flags, results);
              break;

            default:
              assert(false);
          }
        }
      }
      break;

    case Decl::ThisVar:
    case Decl::ErrorVar:
      if (decl_cast<VarDecl>(decl)->name == name && (flags & Variables))
        results.push_back(decl);
      break;

    case Decl::TypeAlias:
      if (decl_cast<TypeAliasDecl>(decl)->name == name && (flags & Types))
        results.push_back(decl);
      break;

    case Decl::Struct:
    case Decl::Union:
    case Decl::VTable:
    case Decl::Enum:
      if (decl_cast<TagDecl>(decl)->name == name && (flags & Types))
        results.push_back(decl);
      break;

    case Decl::TypeArg:
      if (decl_cast<TypeArgDecl>(decl)->name == name && (flags & Types))
        results.push_back(decl);
      break;

    case Decl::EnumConstant:
      if (decl_cast<EnumConstantDecl>(decl)->name == name && (flags & Enums))
        results.push_back(decl);
      break;

    case Decl::FieldVar:
      if (decl_cast<FieldVarDecl>(decl)->name == name && (flags & Fields))
        results.push_back(decl);
      break;

    case Decl::Concept:
      if (decl_cast<ConceptDecl>(decl)->name == name && (flags & Concepts))
        results.push_back(decl);
      break;

    case Decl::Requires:
      break;

    case Decl::Import:
      if (decl_cast<ImportDecl>(decl)->alias == name && (flags & Imports))
        results.push_back(decl);
      for(auto &usein : decl_cast<ImportDecl>(decl)->usings)
        find_decl(usein, name, flags, results);
      break;

    case Decl::Using:
      if (flags & Usings)
        results.push_back(decl);
      break;

    case Decl::Run:
      results.push_back(decl);
      break;

    case Decl::If:
      results.push_back(decl);
      break;

    default:
      assert(false);
  }
}

//|///////////////////// find_decls /////////////////////////////////////////
void find_decls(Scope const &scope, Ident *name, long flags, vector<Decl*> &results)
{
  if (auto owner = get_if<Decl*>(&scope.owner); owner && *owner)
  {
    switch ((*owner)->kind())
    {
      case Decl::TranslationUnit:
        for(auto &decl : decl_cast<TranslationUnitDecl>(*owner)->decls)
          find_decl(decl, name, flags, results);
        break;

      case Decl::Module:
        for(auto &decl : decl_cast<ModuleDecl>(*owner)->decls)
          find_decl(decl, name, flags, results);
        break;

      case Decl::Struct:
      case Decl::Union:
      case Decl::VTable:
      case Decl::Lambda:
      case Decl::Concept:
      case Decl::Enum:
        for(auto &decl : decl_cast<TagDecl>(*owner)->args)
          find_decl(decl, name, flags, results);
        for(auto &decl : decl_cast<TagDecl>(*owner)->decls)
          find_decl(decl, name, flags, results);
        break;

      case Decl::TypeAlias:
        for(auto &decl : decl_cast<TypeAliasDecl>(*owner)->args)
          find_decl(decl, name, flags, results);
        break;

      case Decl::Import:
        find_decls(decl_cast<ImportDecl>(*owner)->decl, name, flags, results);
        break;

      case Decl::Function:
        for(auto &decl : decl_cast<FunctionDecl>(*owner)->args)
          find_decl(decl, name, flags, results);
        for(auto &decl : decl_cast<FunctionDecl>(*owner)->parms)
          find_decl(decl, name, flags, results);
        break;

      case Decl::Case:
        if (decl_cast<CaseDecl>(*owner)->parm)
          find_decl(decl_cast<CaseDecl>(*owner)->parm, name, flags, results);
        break;

      case Decl::If:
        for(auto &decl : decl_cast<IfDecl>(*owner)->decls)
          find_decl(decl, name, flags, results);
        break;

      case Decl::TypeArg:
      case Decl::DeclRef:
      case Decl::DeclScoped:
      case Decl::Requires:
      case Decl::Run:
        break;

      default:
        assert(false);
    }
  }

  if (auto owner = get_if<Stmt*>(&scope.owner); owner && *owner)
  {
    bool pastthepost = false;

    switch ((*owner)->kind())
    {
      case Stmt::If:
        for(auto init : stmt_cast<IfStmt>(*owner)->inits)
        {
          if (init == scope.goalpost)
            break;

          if (init->kind() == Stmt::Declaration)
            find_decl(stmt_cast<DeclStmt>(init)->decl, name, flags, results);
        }
        break;

      case Stmt::For:
        for(auto init : stmt_cast<ForStmt>(*owner)->inits)
        {
          if (init == scope.goalpost)
            break;

          if (init->kind() == Stmt::Declaration)
            find_decl(stmt_cast<DeclStmt>(init)->decl, name, flags, results);
        }
        break;

      case Stmt::Rof:
        for(auto init : stmt_cast<RofStmt>(*owner)->inits)
        {
          if (init == scope.goalpost)
            break;

          if (init->kind() == Stmt::Declaration)
            find_decl(stmt_cast<DeclStmt>(init)->decl, name, flags, results);
        }
        break;

      case Stmt::While:
        for(auto init : stmt_cast<WhileStmt>(*owner)->inits)
        {
          if (init == scope.goalpost)
            break;

          if (init->kind() == Stmt::Declaration)
            find_decl(stmt_cast<DeclStmt>(init)->decl, name, flags, results);
        }
        break;

      case Stmt::Switch:
        for(auto init : stmt_cast<SwitchStmt>(*owner)->inits)
        {
          if (init == scope.goalpost)
            break;

          if (init->kind() == Stmt::Declaration)
            find_decl(stmt_cast<DeclStmt>(init)->decl, name, flags, results);
        }
        break;

      case Stmt::Try:
        break;

      case Stmt::Compound:
        for(auto stmt : stmt_cast<CompoundStmt>(*owner)->stmts)
        {
          if (stmt == scope.goalpost)
            pastthepost = true;

          if (stmt->kind() == Stmt::Declaration)
          {
            switch (auto decl = stmt_cast<DeclStmt>(stmt)->decl; decl->kind())
            {
              case Decl::Struct:
              case Decl::Union:
              case Decl::VTable:
              case Decl::Concept:
              case Decl::Enum:
              case Decl::ThisVar:
                find_decl(decl, name, flags, results);
                break;

              case Decl::VoidVar:
              case Decl::StmtVar:
              case Decl::ErrorVar:
              case Decl::Function:
              case Decl::TypeAlias:
              case Decl::Import:
              case Decl::Using:
                if (!pastthepost)
                  find_decl(decl, name, flags, results);
                break;

              default:
                assert(false);
            }
          }
        }
        break;

      case Stmt::Declaration:
        find_decl(stmt_cast<DeclStmt>(*owner)->decl, name, flags, results);
        break;

      default:
        assert(false);
    }
  }
}
