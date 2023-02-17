//
// sema.h
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
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

    ModuleDecl *module_declaration(Ident *name, std::string_view file);

    IdentPatternDecl *ident_pattern(Ident *name, SourceLocation loc);
    TuplePatternDecl *tuple_pattern(std::vector<Decl*> const &decls, SourceLocation loc);

    FunctionDecl *function_declaration(SourceLocation loc);
    CompoundStmt *compound_statement(SourceLocation loc);
    TryStmt *try_statement(SourceLocation loc);
    DeclStmt *declaration_statement(SourceLocation loc);
    IfStmt *if_statement(SourceLocation loc);
    ForStmt *for_statement(SourceLocation loc);
    RofStmt *rof_statement(SourceLocation loc);
    WhileStmt *while_statement(SourceLocation loc);
    SwitchStmt *switch_statement(SourceLocation loc);
    ExprStmt *expression_statement(SourceLocation loc);
    NullStmt *null_statement(SourceLocation loc);
    GotoStmt *goto_statement(SourceLocation loc);
    ThrowStmt *throw_statement(SourceLocation loc);
    BreakStmt *break_statement(SourceLocation loc);
    ContinueStmt *continue_statement(SourceLocation loc);
    InjectionStmt *injection_statement(SourceLocation loc);
    ReturnStmt *return_statement(SourceLocation loc);
    ImportDecl *import_declaration(SourceLocation loc);
    UsingDecl *using_declaration(SourceLocation loc);
    TypeAliasDecl *alias_declaration(SourceLocation loc);
    TypeArgDecl *typearg_declaration(SourceLocation loc);
    StructDecl *struct_declaration(SourceLocation loc);
    UnionDecl *union_declaration(SourceLocation loc);
    LambdaDecl *lambda_declaration(SourceLocation loc);
    VTableDecl *vtable_declaration(SourceLocation loc);
    StmtVarDecl *var_declaration(SourceLocation loc);
    ParmVarDecl *parm_declaration(SourceLocation loc);
    FieldVarDecl *field_declaration(SourceLocation loc);
    InitialiserDecl *initialiser_declaration(SourceLocation loc);
    VoidVarDecl *voidvar_declaration(SourceLocation loc);
    ErrorVarDecl *errorvar_declaration(SourceLocation loc);
    ThisVarDecl *thisvar_declaration(SourceLocation loc);
    LambdaVarDecl *capture_declaration(SourceLocation loc);
    CaseDecl *case_declaration(SourceLocation loc);
    CaseVarDecl *casevar_declaration(SourceLocation loc);
    ConceptDecl *concept_declaration(SourceLocation loc);
    RequiresDecl *requires_declaration(SourceLocation loc);
    EnumDecl *enum_declaration(SourceLocation loc);
    EnumConstantDecl *enum_constant_declaration(SourceLocation loc);
    AttributeDecl *attribute_declaration(SourceLocation loc);
    RunDecl *run_declaration(SourceLocation loc);
    IfDecl *if_declaration(SourceLocation loc);

    DeclRefDecl *make_declref(Ident *name, SourceLocation loc);
    DeclScopedDecl *make_declref(std::vector<Decl*> const &decls, SourceLocation loc);
    TypeNameDecl *make_typename(Type *type, SourceLocation loc);
    DeclNameDecl *make_declname(Ident *name, SourceLocation loc);
    TypeOfDecl *make_decltype(Expr *expr, SourceLocation loc);
    TypeArgDecl *make_typearg(Ident *name, SourceLocation loc);

    Expr *make_bool_literal(bool value, SourceLocation loc);
    Expr *make_char_literal(std::string_view value, SourceLocation loc);
    Expr *make_numeric_literal(int sign, std::string_view value, SourceLocation loc);
    Expr *make_numeric_literal(int sign, size_t value, SourceLocation loc);
    Expr *make_string_literal(std::string_view value, SourceLocation loc);
    Expr *make_array_literal(Type *elementtype, std::vector<Expr*> const &elements, Type *size, SourceLocation loc);
    Expr *make_tuple_literal(std::vector<Expr*> const &fields, SourceLocation loc);
    Expr *make_void_literal(SourceLocation loc);
    Expr *make_pointer_literal(SourceLocation loc);
    Expr *make_ref_expression(Expr *expr, long qualifiers, SourceLocation loc);
    Expr *make_paren_expression(Expr *subexpr, SourceLocation loc);
    Expr *make_unary_expression(UnaryOpExpr::OpCode op, Expr *subexpr, SourceLocation loc);
    Expr *make_binary_expression(BinaryOpExpr::OpCode op, Expr *lhs, Expr *rhs, SourceLocation loc);
    Expr *make_ternary_expression(Expr *cond, Expr *lhs, Expr *rhs, SourceLocation loc);
    Expr *make_declref_expression(Decl *decl, SourceLocation loc);
    Expr *make_declref_expression(Expr *base, Decl *decl, SourceLocation loc);
    Expr *make_call_expression(Decl *decl, SourceLocation loc);
    Expr *make_call_expression(Decl *decl, std::vector<Expr*> const &parms, std::map<Ident*, Expr*> const &namedparms, SourceLocation loc);
    Expr *make_call_expression(Expr *base, Decl *decl, std::vector<Expr*> const &parms, std::map<Ident*, Expr*> const &namedparms, SourceLocation loc);
    Expr *make_sizeof_expression(Type *type, SourceLocation loc);
    Expr *make_sizeof_expression(Expr *expr, SourceLocation loc);
    Expr *make_alignof_expression(Type *type, SourceLocation loc);
    Expr *make_alignof_expression(Decl *decl, SourceLocation loc);
    Expr *make_offsetof_expression(Decl *decl, SourceLocation loc);
    Expr *make_instanceof_expression(Type *type, Type *instance, SourceLocation loc);
    Expr *make_throws_expression(Expr *expr, SourceLocation loc);
    Expr *make_typeid_expression(Decl *decl, SourceLocation loc);
    Expr *make_cast_expression(Type *type, Expr *expr, SourceLocation loc);
    Expr *make_new_expression(Type *type, Expr *address, SourceLocation loc);
    Expr *make_new_expression(Type *type, Expr *address, std::vector<Expr*> const &parms, std::map<Ident*, Expr*> const &namedparms, SourceLocation loc);
    Expr *make_requires_expression(Decl *decl, SourceLocation loc);
    Expr *make_match_expression(Decl *decl, SourceLocation loc);
    Expr *make_lambda_expression(Decl *decl, SourceLocation loc);
    Expr *make_fragment_expression(std::vector<Expr*> const &args, std::vector<Decl*> const &decls, SourceLocation loc);

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
    Type *make_fntype(Type *returntype, Type *paramtuple, Type *throwtype = nullptr);
    Type *make_pack(Type *type);
    Type *make_unpack(Type *type);

    ModuleDecl *lookup_module(Ident *name);

    void add_cfg(std::string_view str);
    void add_include_path(std::string_view path);

    void end();

    AST *ast = nullptr;

    std::vector<std::string> m_cfgs;
    std::vector<std::string> m_include_paths;
};
