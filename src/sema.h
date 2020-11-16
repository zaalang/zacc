//
// sema.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"
#include "parser.h"
#include <map>
#include <stack>
#include <vector>
#include <variant>

//-------------------------- Sema -------------------------------------------
//---------------------------------------------------------------------------

class Sema
{
  public:
    Sema();
    Sema(Sema const &) = delete;
    Sema &operator=(Sema const &) = delete;

    TranslationUnitDecl *translation_unit(std::string_view file);

    ModuleDecl *module_declaration(std::string_view name, std::string_view file);

    FunctionDecl *function_declaration(SourceLocation loc);
    CompoundStmt *compound_statement(SourceLocation loc);
    TryStmt *try_statement(SourceLocation loc);
    DeclStmt *declaration_statement(SourceLocation loc);
    IfStmt *if_statement(SourceLocation loc);
    ForStmt *for_statement(SourceLocation loc);
    RofStmt *rof_statement(SourceLocation loc);
    WhileStmt *while_statement(SourceLocation loc);
    ExprStmt *expression_statement(SourceLocation loc);
    NullStmt *null_statement(SourceLocation loc);
    ThrowStmt *throw_statement(SourceLocation loc);
    BreakStmt *break_statement(SourceLocation loc);
    ContinueStmt *continue_statement(SourceLocation loc);
    ReturnStmt *return_statement( SourceLocation loc);
    ImportDecl *import_declaration(SourceLocation loc);
    UsingDecl *using_declaration(SourceLocation loc);
    TypeAliasDecl *alias_declaration(SourceLocation loc);
    TypeArgDecl *typearg_declaration(SourceLocation loc);
    StructDecl *struct_declaration(SourceLocation loc);
    LambdaDecl *lambda_declaration(SourceLocation loc);
    StmtVarDecl *var_declaration(SourceLocation loc);
    ParmVarDecl *parm_declaration(SourceLocation loc);
    FieldVarDecl *field_declaration(SourceLocation loc);
    InitialiserDecl *initialiser_declaration(SourceLocation loc);
    RangeVarDecl *rangevar_declaration(SourceLocation loc);
    VoidVarDecl *voidvar_declaration(SourceLocation loc);
    ErrorVarDecl *errorvar_declaration(SourceLocation loc);
    ThisVarDecl *thisvar_declaration(SourceLocation loc);
    ConceptDecl *concept_declaration(SourceLocation loc);
    RequiresDecl *requires_declaration(SourceLocation loc);
    EnumDecl *enum_declaration(SourceLocation loc);
    EnumConstantDecl *enum_constant_declaration(SourceLocation loc);
    IfDecl *if_declaration(SourceLocation loc);

    DeclRefDecl *make_declref(std::string_view name, SourceLocation loc);
    DeclScopedDecl *make_declref(std::vector<Decl*> const &decls, SourceLocation loc);
    TypeOfDecl *make_decltype(Expr *expr, SourceLocation loc);
    TypeArgDecl *make_typearg(std::string_view name, SourceLocation loc);

    Expr *make_bool_literal(bool value, SourceLocation loc);
    Expr *make_char_literal(std::string_view value, SourceLocation loc);
    Expr *make_numeric_literal(int sign, std::string_view value, SourceLocation loc);
    Expr *make_numeric_literal(int sign, size_t value, SourceLocation loc);
    Expr *make_string_literal(std::string_view value, SourceLocation loc);
    Expr *make_array_literal(std::vector<Expr*> const &elements, Type *size, SourceLocation loc);
    Expr *make_paren_expression(Expr *subexpr, SourceLocation loc);
    Expr *make_unary_expression(UnaryOpExpr::OpCode op, Expr *subexpr, SourceLocation loc);
    Expr *make_binary_expression(BinaryOpExpr::OpCode op, Expr *lhs, Expr *rhs, SourceLocation loc);
    Expr *make_ternary_expression(Expr *cond, Expr *lhs, Expr *rhs, SourceLocation loc);
    Expr *make_declref_expression(Decl *decl, SourceLocation loc);
    Expr *make_declref_expression(Expr *base, Decl *decl, SourceLocation loc);
    Expr *make_call_expression(Decl *decl, SourceLocation loc);
    Expr *make_call_expression(Decl *decl, std::vector<Expr*> const &parms, std::map<std::string, Expr*> const &namedparms, SourceLocation loc);
    Expr *make_call_expression(Expr *base, Decl *decl, std::vector<Expr*> const &parms, std::map<std::string, Expr*> const &namedparms, SourceLocation loc);
    Expr *make_sizeof_expression(Type *type, SourceLocation loc);
    Expr *make_sizeof_expression(Expr *expr, SourceLocation loc);
    Expr *make_alignof_expression(Type *type, SourceLocation loc);
    Expr *make_alignof_expression(Expr *expr, SourceLocation loc);
    Expr *make_cast_expression(Type *type, Expr *expr, SourceLocation loc);
    Expr *make_new_expression(Type *type, Expr *address, SourceLocation loc);
    Expr *make_new_expression(Type *type, Expr *address, std::vector<Expr*> const &parms, std::map<std::string, Expr*> const &namedparms, SourceLocation loc);
    Expr *make_requires_expression(Decl *decl, SourceLocation loc);
    Expr *make_lambda_expression(Decl *decl, SourceLocation loc);

    Type *make_const(Type *type);
    Type *make_pointer(Type *type);
    Type *make_reference(Type *type);
    Type *make_array(Type *type, Type *size);
    Type *make_tuple(std::vector<Type*> const &fields);
    Type *make_typeref(Decl *decl);
    Type *make_typearg(Decl *decl);
    Type *make_typearg(Decl *decl, Decl *koncept, std::vector<std::pair<Decl*, Type*>> const &args);
    Type *make_qualarg(Type *type);
    Type *make_typelit(Expr *expr);
    Type *make_constant(Decl *decl, Type *type);
    Type *make_tagtype(Decl *decl, std::vector<std::pair<Decl*, Type*>> const &args);
    Type *make_fntype(Type *returntype, Type *paramtuple);
    Type *make_pack(Type *type);
    Type *make_unpack(Type *type);

    ModuleDecl *lookup_module(std::string_view name);

    void add_include_path(std::string_view path);

    void end();

    AST *ast = nullptr;

    std::vector<std::string> m_include_paths;
};
