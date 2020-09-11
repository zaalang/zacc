//
// parser.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "parser.h"
#include "semantic.h"
#include "diag.h"
#include "sema.h"
#include "util.h"
#include <iostream>
#include <cassert>

using namespace std;

namespace
{
  struct ParseContext
  {
    Diag &diag;

    Token tok;
    LexCursor lexcursor;

    SourceText const &text;

    ParseContext(SourceText const &text, Diag &diag)
      : diag(diag),
        text(text)
    {
      consume_token();
    }

    Token token(int i)
    {
      auto token = tok;
      auto cursor = lexcursor;

      for( ; token != Token::eof && i > 0; --i)
        cursor = lex(text, cursor, token);

      return token;
    }

    void consume_token()
    {
      lexcursor = lex(text, lexcursor, tok);
    }

    void consume_token(Token::Type expected)
    {
      assert(tok == expected);

      consume_token();
    }

    bool try_consume_token(Token::Type expected)
    {
      if (tok == expected)
      {
        consume_token();

        return true;
      }

      return false;
    }

    void consume_til(Token::Type type)
    {
      while (tok != type && tok != Token::eof)
      {
        consume_token();
      }
    }

    void comsume_til_resumable()
    {
      while (true)
      {
        switch(tok.type)
        {
          case Token::l_brace:
            consume_til(Token::r_brace);
            consume_token();
            return;

          case Token::l_square:
            consume_til(Token::r_square);
            consume_token();
            continue;

          case Token::l_paren:
            consume_til(Token::r_paren);
            consume_token();
            continue;

          case Token::semi:
            consume_token();
            return;

          case Token::eof:
            return;

          default:
            consume_token();
        }
      }
    }
  };

  enum class PrecLevel
  {
    Zero            = 0,    // Not binary operator.
    Assignment      = 1,    // =, *=, /=, %=, +=, -=, <<=, >>=, &=, ^=, |=
    Range           = 2,    // .., ..=
    Conditional     = 3,    // ?
    LogicalOr       = 4,    // ||
    LogicalAnd      = 5,    // &&
    Equality        = 6,    // ==, !=
    Relational      = 7,    // >=, <=, >, <
    Spaceship       = 8,    // <=>
    Additive        = 9,    // -, +
    BitwiseOr       = 10,   // |
    BitwiseXOr      = 11,   // ^
    BitwiseAnd      = 12,   // &
    Shift           = 13,   // <<, >>
    Multiplicative  = 14,   // *, /, %
    PointerToMember = 15,   // .*, ->*
  };

  PrecLevel precedence(Token const &tok)
  {
    switch (tok.type)
    {
      case Token::equal:
      case Token::starequal:
      case Token::slashequal:
      case Token::percentequal:
      case Token::plusequal:
      case Token::minusequal:
      case Token::lesslessequal:
      case Token::greatergreaterequal:
      case Token::ampequal:
      case Token::caretequal:
      case Token::pipeequal:
        return PrecLevel::Assignment;

      case Token::dotdot:
      case Token::dotdotequal:
        return PrecLevel::Range;

      case Token::question:
        return PrecLevel::Conditional;

      case Token::pipepipe:
        return PrecLevel::LogicalOr;

      case Token::ampamp:
        return PrecLevel::LogicalAnd;

      case Token::exclaimequal:
      case Token::equalequal:
        return PrecLevel::Equality;

      case Token::lessequal:
      case Token::less:
      case Token::greaterequal:
      case Token::greater:
        return PrecLevel::Relational;

      case Token::spaceship:
        return PrecLevel::Spaceship;

      case Token::plus:
      case Token::minus:
        return PrecLevel::Additive;

      case Token::pipe:
        return PrecLevel::BitwiseOr;

      case Token::caret:
        return PrecLevel::BitwiseXOr;

      case Token::amp:
        return PrecLevel::BitwiseAnd;

      case Token::lessless:
      case Token::greatergreater:
        return PrecLevel::Shift;

      case Token::percent:
      case Token::slash:
      case Token::star:
        return PrecLevel::Multiplicative;

      case Token::periodstar:
      case Token::arrowstar:
        return PrecLevel::PointerToMember;

      default:
        return PrecLevel::Zero;
    }
  }

  UnaryOpExpr::OpCode unaryopcode(Token const &tok)
  {
    switch (tok.type)
    {
      case Token::plus: return UnaryOpExpr::Plus;
      case Token::minus: return UnaryOpExpr::Minus;
      case Token::tilde: return UnaryOpExpr::Not;
      case Token::exclaim: return UnaryOpExpr::LNot;
      case Token::plusplus: return UnaryOpExpr::PreInc;
      case Token::minusminus: return UnaryOpExpr::PreDec;
      case Token::amp: return UnaryOpExpr::Ref;
      case Token::star: return UnaryOpExpr::Fer;
      case Token::ampamp: return UnaryOpExpr::Fwd;
      case Token::hash: return UnaryOpExpr::Literal;

      default:
        throw logic_error("invalid unary op");
    }
  }

  BinaryOpExpr::OpCode binaryopcode(Token const &tok)
  {
    switch (tok.type)
    {
      case Token::plus: return BinaryOpExpr::Add;
      case Token::minus: return BinaryOpExpr::Sub;
      case Token::star: return BinaryOpExpr::Mul;
      case Token::slash: return BinaryOpExpr::Div;
      case Token::percent: return BinaryOpExpr::Rem;
      case Token::lessless: return BinaryOpExpr::Shl;
      case Token::greatergreater: return BinaryOpExpr::Shr;
      case Token::amp: return BinaryOpExpr::And;
      case Token::pipe: return BinaryOpExpr::Or;
      case Token::caret: return BinaryOpExpr::Xor;
      case Token::ampamp: return BinaryOpExpr::LAnd;
      case Token::pipepipe: return BinaryOpExpr::LOr;
      case Token::less: return BinaryOpExpr::LT;
      case Token::greater: return BinaryOpExpr::GT;
      case Token::lessequal: return BinaryOpExpr::LE;
      case Token::greaterequal: return BinaryOpExpr::GE;
      case Token::equalequal: return BinaryOpExpr::EQ;
      case Token::exclaimequal: return BinaryOpExpr::NE;
      case Token::spaceship: return BinaryOpExpr::Cmp;
      case Token::equal: return BinaryOpExpr::Assign;
      case Token::starequal: return BinaryOpExpr::MulAssign;
      case Token::slashequal: return BinaryOpExpr::DivAssign;
      case Token::percentequal: return BinaryOpExpr::RemAssign;
      case Token::plusequal: return BinaryOpExpr::AddAssign;
      case Token::minusequal: return BinaryOpExpr::SubAssign;
      case Token::lesslessequal: return BinaryOpExpr::ShlAssign;
      case Token::greatergreaterequal: return BinaryOpExpr::ShrAssign;
      case Token::ampequal: return BinaryOpExpr::AndAssign;
      case Token::caretequal: return BinaryOpExpr::XorAssign;
      case Token::pipeequal: return BinaryOpExpr::OrAssign;
      case Token::dotdot: return BinaryOpExpr::Range;
      case Token::dotdotequal: return BinaryOpExpr::RangeEq;

      default:
        throw logic_error("invalid binary op");
    }
  }

  Type *parse_type(ParseContext &ctx, Sema &sema);
  Type *parse_type_ex(ParseContext &ctx, Sema &sema);
  Expr *parse_expression(ParseContext &ctx, Sema &sema);
  Expr *parse_expression_til(ParseContext &ctx, LexCursor const &cursor, Sema &sema);
  Expr *parse_expression_left(ParseContext &ctx, Sema &sema);
  Decl *parse_enum_declaration(ParseContext &ctx, Sema &sema);
  Decl *parse_struct_declaration(ParseContext &ctx, Sema &sema);
  Stmt *parse_statement(ParseContext &ctx, Sema &sema);
  Stmt *parse_compound_statement(ParseContext &ctx, Sema &sema);

  //|///////////////////// parse_typearg_list ///////////////////////////////
  vector<Type*> parse_typearg_list(ParseContext &ctx, Sema &sema)
  {
    vector<Type*> args;

    while (ctx.tok != Token::greater && ctx.tok != Token::r_paren && ctx.tok != Token::eof)
    {
      if (ctx.tok == Token::identifier && ctx.token(1) == Token::colon)
        break;

      auto type = parse_type_ex(ctx, sema);

      if (ctx.try_consume_token(Token::ellipsis))
        type = sema.make_unpack(type);

      args.push_back(type);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return args;
  }

  //|///////////////////// parse_named_typearg_list //////////////////////
  map<string, Type*> parse_named_typearg_list(ParseContext &ctx, Sema &sema)
  {
    map<string, Type*> args;

    while (ctx.tok != Token::greater && ctx.tok != Token::eof)
    {
      if (ctx.tok != Token::identifier || ctx.token(1) != Token::colon)
        break;

      auto name = ctx.tok.text;

      ctx.consume_token(Token::identifier);
      ctx.consume_token(Token::colon);

      args.emplace(name, parse_type_ex(ctx, sema));

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return args;
  }

  //|///////////////////// parse_args_list //////////////////////////////////
  vector<Decl*> parse_args_list(ParseContext &ctx, Sema &sema)
  {
    vector<Decl*> args;

    while (ctx.tok != Token::greater && ctx.tok != Token::eof)
    {
      auto arg = sema.typearg_declaration(ctx.tok.loc);

      if (ctx.try_consume_token(Token::ellipsis))
        arg->flags |= TypeArgDecl::Pack;

      arg->name = ctx.tok.text;

      if (!ctx.try_consume_token(Token::identifier))
      {
        ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        break;
      }

      if (ctx.try_consume_token(Token::equal))
      {
        arg->defult = parse_type_ex(ctx, sema);
      }

      args.push_back(arg);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return args;
  }

  //|///////////////////// parse_expression_list ////////////////////////////
  vector<Expr*> parse_expression_list(ParseContext &ctx, Sema &sema)
  {
    vector<Expr*> exprs;

    while (ctx.tok != Token::r_paren && ctx.tok != Token::r_square && ctx.tok != Token::semi && ctx.tok != Token::eof)
    {
      if (ctx.tok == Token::identifier && ctx.token(1) == Token::colon)
        break;

      auto expr = parse_expression(ctx, sema);

      if (!expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        break;
      }

      if (ctx.try_consume_token(Token::ellipsis))
      {
        expr = sema.make_unary_expression(UnaryOpExpr::Unpack, expr, ctx.tok.loc);
      }

      exprs.push_back(expr);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return exprs;
  }

  //|///////////////////// parse_named_expression_list //////////////////////
  map<string, Expr*> parse_named_expression_list(ParseContext &ctx, Sema &sema)
  {
    map<string, Expr*> exprs;

    while (ctx.tok != Token::r_paren && ctx.tok != Token::eof)
    {
      if (ctx.tok != Token::identifier || ctx.token(1) != Token::colon)
        break;

      auto name = ctx.tok.text;

      ctx.consume_token(Token::identifier);
      ctx.consume_token(Token::colon);

      exprs.emplace(name, parse_expression(ctx, sema));

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return exprs;
  }

  //|///////////////////// parse_parms_list /////////////////////////////////
  vector<Decl*> parse_parms_list(ParseContext &ctx, Sema &sema)
  {
    vector<Decl*> parms;

    while (ctx.tok != Token::r_paren && ctx.tok != Token::eof)
    {
      auto parm = sema.parm_declaration(ctx.tok.loc);

      if (ctx.try_consume_token(Token::hash))
        parm->flags |= VarDecl::Literal;

      parm->type = parse_type(ctx, sema);

      if (!parm->type)
      {
        ctx.diag.error("expected type", ctx.text, ctx.tok.loc);
        break;
      }

      if (is_const_type(parm->type))
      {
        parm->flags |= VarDecl::Const;
        parm->type = remove_const_type(parm->type);
      }

      if (ctx.try_consume_token(Token::ellipsis))
        parm->type = sema.make_pack(parm->type);

      if (ctx.tok == Token::identifier || ctx.tok == Token::kw_this)
      {
        parm->name = ctx.tok.text;

        ctx.consume_token();
      }

      if (ctx.try_consume_token(Token::equal))
      {
        parm->defult = parse_expression(ctx, sema);
      }

      parms.push_back(parm);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return parms;
  }

  //|///////////////////// parse_statement_list /////////////////////////////
  vector<Stmt*> parse_statement_list(ParseContext &ctx, Sema &sema)
  {
    vector<Stmt*> stmts;

    while (ctx.tok != Token::r_paren && ctx.tok != Token::semi && ctx.tok != Token::eof)
    {
      if (ctx.tok == Token::kw_let || ctx.tok == Token::kw_var || ctx.tok == Token::kw_const)
      {
        auto stmt = sema.declaration_statement(ctx.tok.loc);

        auto flags = 0;

        switch(ctx.tok.type)
        {
          case Token::kw_var:
            break;

          case Token::kw_let:
            flags |= VarDecl::Const;
            break;

          case Token::kw_const:
            flags |= VarDecl::Literal;
            break;

          default:
            assert(false);
        }

        ctx.consume_token();

        auto type = sema.make_typearg(sema.make_typearg("var", ctx.tok.loc));

        if (ctx.try_consume_token(Token::kw_const))
          flags |= VarDecl::Const;

        if (ctx.try_consume_token(Token::amp))
        {
          if (flags & VarDecl::Const)
            type = sema.make_const(type);

          type = sema.make_reference(type);
        }

        auto name = ctx.tok.text;

        if (!ctx.try_consume_token(Token::identifier))
        {
          ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
          ctx.comsume_til_resumable();
          break;
        }

        if (ctx.tok != Token::colon && ctx.tok != Token::equal)
        {
          ctx.diag.error("expected assignment", ctx.text, ctx.tok.loc);
          ctx.comsume_til_resumable();
          break;
        }

        if (ctx.try_consume_token(Token::colon))
        {
          auto var = sema.rangevar_declaration(stmt->loc());

          var->name = name;
          var->flags = flags;
          var->type = type;
          var->range = parse_expression(ctx, sema);

          if (!var->range)
          {
            ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
            ctx.comsume_til_resumable();
            break;
          }

          stmt->decl = var;
        }

        if (ctx.try_consume_token(Token::equal))
        {
          auto var = sema.var_declaration(stmt->loc());

          var->name = name;
          var->flags = flags;
          var->type = type;
          var->value = parse_expression(ctx, sema);

          if (!var->value)
          {
            ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
            ctx.comsume_til_resumable();
            break;
          }

          stmt->decl = var;
        }

        stmts.push_back(stmt);
      }
      else
      {
        auto stmt = sema.expression_statement(ctx.tok.loc);

        stmt->expr = parse_expression(ctx, sema);

        if (!stmt->expr)
        {
          ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
          ctx.comsume_til_resumable();
          break;
        }

        stmts.push_back(stmt);
      }

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return stmts;
  }

  //|///////////////////// parse_name ///////////////////////////////////////
  string_view parse_name(ParseContext &ctx, Sema &sema)
  {
    auto name = ctx.tok.text;

    if (ctx.tok == Token::l_square || ctx.tok == Token::l_paren || (ctx.tok == Token::tilde && ctx.token(1) == Token::identifier))
    {
      ctx.consume_token();

      if (ctx.tok.text.begin() != name.end())
      {
        ctx.diag.error("extra characters within function name", ctx.text, ctx.tok.loc);
      }

      name = string_view(name.data(), ctx.tok.text.length() + 1);
    }

    ctx.consume_token();

    return name;
  }

  //|///////////////////// parse_qualified_name /////////////////////////////
  Decl *parse_qualified_name(ParseContext &ctx, Sema &sema)
  {
    vector<Decl*> decls;

    auto loc = ctx.tok.loc;

    if (ctx.tok == Token::coloncolon)
    {
      auto loc = ctx.tok.loc;

      decls.push_back(sema.make_declref("::", loc));

      ctx.consume_token(Token::coloncolon);
    }

    if (ctx.try_consume_token(Token::kw_typeof))
    {
      auto loc = ctx.tok.loc;

      if (!ctx.try_consume_token(Token::l_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      auto expr = parse_expression(ctx, sema);

      if (!expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      decls.push_back(sema.make_decltype(expr, loc));

      if (!ctx.try_consume_token(Token::coloncolon))
        return decls.back();
    }

    while (true)
    {
      auto loc = ctx.tok.loc;
      auto name = parse_name(ctx, sema);

      auto ref = sema.make_declref(name, loc);

      if ((ctx.tok == Token::coloncolon && ctx.token(1) == Token::less) || (ctx.tok == Token::less && ctx.tok.text.begin() == name.end()))
      {
        if (ctx.tok == Token::coloncolon)
          ctx.consume_token();

        ctx.consume_token(Token::less);

        ref->args = parse_typearg_list(ctx, sema);
        ref->namedargs = parse_named_typearg_list(ctx, sema);

        if (ctx.tok != Token::greater && ctx.tok != Token::greatergreater)
        {
          ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
          ctx.comsume_til_resumable();
          return nullptr;
        }

        if (ctx.tok == Token::greatergreater)
          ctx.tok.type = Token::greater;
        else
          ctx.consume_token();
      }

      decls.push_back(ref);

      if (!ctx.try_consume_token(Token::coloncolon))
        break;
    }

    return (decls.size() == 1) ? decls.front() : sema.make_declref(decls, loc);
  }

  //|///////////////////// parse_bool_literal ///////////////////////////////
  Expr *parse_bool_literal(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;
    auto type = ctx.tok.type;

    ctx.consume_token();

    return sema.make_bool_literal((type == Token::kw_true), loc);
  }

  //|///////////////////// parse_char_literal ///////////////////////////////
  Expr *parse_char_literal(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;
    auto text = ctx.tok.text;

    ctx.consume_token(Token::char_constant);

    return sema.make_char_literal(text, loc);
  }

  //|///////////////////// parse_numeric_literal ////////////////////////////
  Expr *parse_numeric_literal(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;
    auto text = ctx.tok.text;

    ctx.consume_token(Token::numeric_constant);

    return sema.make_numeric_literal(+1, text, loc);
  }

  //|///////////////////// parse_string_literal /////////////////////////////
  Expr *parse_string_literal(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;
    auto text = ctx.tok.text;

    ctx.consume_token();

    return sema.make_string_literal(unescape(text.substr(1, text.length()-2)), loc);
  }

  //|///////////////////// parse_array_literal //////////////////////////////
  Expr *parse_array_literal(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::l_square);

    auto elements = parse_expression_list(ctx, sema);

    Expr *size;

    if (ctx.try_consume_token(Token::semi))
    {
      if (elements.size() != 1)
      {
        ctx.diag.error("expected single repeat value", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      size = parse_expression(ctx, sema);
    }
    else
    {
      size = sema.make_numeric_literal(+1, elements.size(), loc);
    }

    if (!size)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    if (!ctx.try_consume_token(Token::r_square))
    {
      ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    return sema.make_array_literal(elements, sema.make_typelit(size), loc);
  }

  //|///////////////////// parse_type ///////////////////////////////////////
  Type *parse_type(ParseContext &ctx, Sema &sema)
  {
    Type *type = nullptr;

    auto outer_const = ctx.try_consume_token(Token::kw_const);

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto fields = parse_typearg_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      type = sema.make_tuple(fields);
    }
    else
    {
      auto name = parse_qualified_name(ctx, sema);

      type = sema.make_typeref(name);
    }

    while (ctx.tok == Token::kw_mut || ctx.tok == Token::kw_const || ctx.tok == Token::star || ctx.tok == Token::amp || ctx.tok == Token::ampamp || ctx.tok == Token::l_square || ctx.tok == Token::l_paren)
    {
      auto kw_mut = ctx.try_consume_token(Token::kw_mut);
      auto kw_const = ctx.try_consume_token(Token::kw_const);

      if (kw_mut && kw_const)
      {
        ctx.diag.warn("mut has no effect when const", ctx.text, ctx.tok.loc);
      }

      if (ctx.try_consume_token(Token::star))
      {
        if (!kw_mut || kw_const)
          type = sema.make_const(type);

        type = sema.make_pointer(type);
      }

      else if (ctx.try_consume_token(Token::amp))
      {
        if (!kw_mut || kw_const)
          type = sema.make_const(type);

        type = sema.make_reference(type);
      }

      else if (ctx.try_consume_token(Token::ampamp))
      {
        if (kw_mut || kw_const)
        {
          ctx.diag.warn("invalid qualifiers", ctx.text, ctx.tok.loc);
        }

        type = sema.make_reference(sema.make_qualarg(type));
      }

      else if (ctx.try_consume_token(Token::l_square))
      {
        if (kw_const)
          type = sema.make_const(type);

        auto size = parse_type_ex(ctx, sema);

        if (!size)
        {
          ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
          break;
        }

        if (!ctx.try_consume_token(Token::r_square))
        {
          ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
          break;
        }

        type = sema.make_array(type, size);
      }
      else if (ctx.try_consume_token(Token::l_paren))
      {
        auto fields = parse_typearg_list(ctx, sema);

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          ctx.comsume_til_resumable();
          return nullptr;
        }

        type = sema.make_fntype(type, sema.make_tuple(fields));
      }

      if (kw_const)
        type = sema.make_const(type);
    }

    if (outer_const && !is_const_type(type))
      type = sema.make_const(type);

    return type;
  }

  //|///////////////////// parse_type ///////////////////////////////////////
  Type *parse_type_ex(ParseContext &ctx, Sema &sema)
  {
//    if (ctx.tok == Token::hash)
//    {
//      ctx.consume_token(Token::hash);

//      auto expr = parse_expression(ctx, sema);

//      if (!expr)
//      {
//        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
//        ctx.comsume_til_resumable();
//        return nullptr;
//      }

//      if (!ctx.try_consume_token(Token::semi))
//      {
//        ctx.diag.error("expected semi after type expression", ctx.text, ctx.tok.loc);
//        ctx.comsume_til_resumable();
//        return nullptr;
//      }

//      return sema.make_typelit(expr);
//    }

    auto tok = ctx.tok;
    auto lexcursor = ctx.lexcursor;
    auto maybe = false;
    auto leftid = false;
    auto comma = false;

    auto skip_bracketed = [&]() {
      for(int indent = 0; tok != Token::eof; )
      {
        if (tok == Token::l_paren)
          indent += 1;

        if (tok == Token::r_paren)
          if (--indent <= 0)
            break;

        if (tok == Token::comma)
          comma = true;

        lexcursor = lex(ctx.text, lexcursor, tok);
      }
    };

    while (true)
    {
      switch(tok.type)
      {
        case Token::plus:
        case Token::minus:
        case Token::slash:
        case Token::percent:
        case Token::pipe:
        case Token::caret:
        case Token::exclaim:
        case Token::tilde:
        case Token::pipepipe:
        case Token::period:
        case Token::kw_true:
        case Token::kw_false:
        case Token::char_constant:
        case Token::numeric_constant:
        case Token::string_literal:
          maybe = true;
          leftid = false;
          break;

        case Token::star:
        case Token::amp:
        case Token::ampamp:
          lexcursor = lex(ctx.text, lexcursor, tok);
          if (tok == Token::identifier || tok == Token::numeric_constant || tok == Token::plus || tok == Token::minus)
            maybe = true;
          leftid = false;
          continue;

        case Token::identifier:
        case Token::coloncolon:
          leftid = true;
          break;

        case Token::l_paren:
          comma = false;
          if (lex(ctx.text, lexcursor, tok); tok == Token::r_paren)
            comma = true;

          tok.type = Token::l_paren;

          skip_bracketed();

          if (leftid || !comma)
            maybe = true;
          break;

        case Token::less:
          for(int indent = 0; tok != Token::eof; )
          {
            if (tok == Token::l_paren)
              skip_bracketed();

            if (tok == Token::less)
              indent += 1;

            if (tok == Token::greater)
              indent -= 1;

            if (tok == Token::greatergreater)
              indent -= 2;

            if (indent <= 0)
              break;

            lexcursor = lex(ctx.text, lexcursor, tok);
          }
          break;

        case Token::greater:
        case Token::greatergreater:
        case Token::r_square:
        case Token::r_paren:
        case Token::comma:

          if (maybe)
          {
            if (auto expr = parse_expression_til(ctx, lexcursor, sema))
              return sema.make_typelit(expr);
          }

          [[fallthrough]];

        default:
          return parse_type(ctx, sema);
      }

      lexcursor = lex(ctx.text, lexcursor, tok);
    }

    return nullptr;
  }

  //|///////////////////// parse_paren //////////////////////////////////////
  Expr *parse_paren(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::l_paren);

    auto expr = parse_expression(ctx, sema);

    if (!expr)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    return sema.make_paren_expression(expr, loc);
  }

  //|///////////////////// parse_unary_plus /////////////////////////////////
  Expr *parse_unary_plus(ParseContext &ctx, Sema &sema)
  {
    auto op = ctx.tok;
    auto text = ctx.tok.text;

    ctx.consume_token(Token::plus);

    if (ctx.tok == Token::numeric_constant)
    {
      if (ctx.tok.text.begin() != text.end())
      {
        ctx.diag.warn("extra characters within numeric literal", ctx.text, op.loc);
      }

      auto value = ctx.tok.text;

      ctx.consume_token(Token::numeric_constant);

      return sema.make_numeric_literal(+1, value, op.loc);
    }

    return sema.make_unary_expression(unaryopcode(op), parse_expression_left(ctx, sema), op.loc);
  }

  //|///////////////////// parse_unary_minus ////////////////////////////////
  Expr *parse_unary_minus(ParseContext &ctx, Sema &sema)
  {
    auto op = ctx.tok;

    ctx.consume_token(Token::minus);

    if (ctx.tok == Token::numeric_constant)
    {
      auto value = ctx.tok.text;

      ctx.consume_token(Token::numeric_constant);

      return sema.make_numeric_literal(-1, value, op.loc);
    }

    return sema.make_unary_expression(unaryopcode(op), parse_expression_left(ctx, sema), op.loc);
  }

  //|///////////////////// parse_callee /////////////////////////////////////
  Expr *parse_callee(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;
    auto name = parse_qualified_name(ctx, sema);

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto parms = parse_expression_list(ctx, sema);
      auto namedparms = parse_named_expression_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      return sema.make_call_expression(name, parms, namedparms, loc);
    }

    return sema.make_declref_expression(name, loc);
  }

  //|///////////////////// parse_sizeof /////////////////////////////////////
  Expr *parse_sizeof(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::kw_sizeof);

    if (ctx.try_consume_token(Token::less))
    {
      auto type = parse_type(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      if (ctx.try_consume_token(Token::l_paren))
      {
        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          ctx.comsume_til_resumable();
          return nullptr;
        }
      }

      return sema.make_sizeof_expression(type, loc);
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto expr = parse_expression(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      return sema.make_sizeof_expression(expr, loc);
    }

    return nullptr;
  }

  //|///////////////////// parse_alignof ////////////////////////////////////
  Expr *parse_alignof(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::kw_alignof);

    if (ctx.try_consume_token(Token::less))
    {
      auto type = parse_type(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      if (ctx.try_consume_token(Token::l_paren))
      {
        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          ctx.comsume_til_resumable();
          return nullptr;
        }
      }

      return sema.make_alignof_expression(type, loc);
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto expr = parse_expression(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      return sema.make_alignof_expression(expr, loc);
    }

    return nullptr;
  }

  //|///////////////////// parse_cast ///////////////////////////////////////
  Expr *parse_cast(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::kw_cast);

    Type *type = nullptr;
    Expr *expr = nullptr;

    if (ctx.try_consume_token(Token::less))
    {
      type = parse_type(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      expr = parse_expression(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }
    }

    if (!expr)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    return sema.make_cast_expression(type, expr, loc);
  }

  //|///////////////////// parse_new ////////////////////////////////////////
  Expr *parse_new(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::kw_new);

    if (!ctx.try_consume_token(Token::less))
    {
      ctx.diag.error("expected less", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    auto type = parse_type(ctx, sema);

    if (!ctx.try_consume_token(Token::greater))
    {
      ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    auto address = parse_expression(ctx, sema);

    if (!address)
    {
      ctx.diag.error("expected address parameter", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto parms = parse_expression_list(ctx, sema);
      auto namedparms = parse_named_expression_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      return sema.make_new_expression(type, address, parms, namedparms, loc);
    }

    return sema.make_new_expression(type, address, loc);
  }

  //|///////////////////// parse_member /////////////////////////////////////
  Expr *parse_member(ParseContext &ctx, Expr *base, Sema &sema)
  {
    ctx.consume_token(Token::period);

    auto loc = ctx.tok.loc;
    auto name = parse_qualified_name(ctx, sema);

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto parms = parse_expression_list(ctx, sema);
      auto namedparms = parse_named_expression_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      return sema.make_call_expression(base, name, parms, namedparms, loc);
    }

    return sema.make_declref_expression(base, name, loc);
  }

  //|///////////////////// parse_subscript //////////////////////////////////
  Expr *parse_subscript(ParseContext &ctx, Expr *base, Sema &sema)
  {
    ctx.consume_token(Token::l_square);

    auto loc = ctx.tok.loc;
    auto name = sema.make_declref("[]", loc);
    auto parms = parse_expression_list(ctx, sema);
    auto namedparms = parse_named_expression_list(ctx, sema);

    if (!ctx.try_consume_token(Token::r_square))
    {
      ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    return sema.make_call_expression(base, name, parms, namedparms, loc);
  }

  //|///////////////////// parse_call ///////////////////////////////////////
  Expr *parse_call(ParseContext &ctx, Expr *base, Sema &sema)
  {
    ctx.consume_token(Token::l_paren);

    auto loc = ctx.tok.loc;
    auto name = sema.make_declref("()", loc);
    auto parms = parse_expression_list(ctx, sema);
    auto namedparms = parse_named_expression_list(ctx, sema);

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    return sema.make_call_expression(base, name, parms, namedparms, loc);
  }

  //|///////////////////// parse_lambda /////////////////////////////////////
  Expr *parse_lambda(ParseContext &ctx, Sema &sema)
  {
    auto lambda = sema.lambda_declaration(ctx.tok.loc);

    auto fn = sema.function_declaration(lambda->loc());

    ctx.consume_token(Token::kw_fn);

    fn->flags |= FunctionDecl::Public;
    fn->flags |= FunctionDecl::LambdaDecl;

    fn->name = "()";

    if (ctx.tok == Token::identifier)
    {
      lambda->name = ctx.tok.text;

      ctx.consume_token(Token::identifier);
    }

    if (ctx.try_consume_token(Token::l_square))
    {
      lambda->flags |= LambdaDecl::Captures;

      if (!ctx.try_consume_token(Token::r_square))
      {
        ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }
    }

    if (ctx.try_consume_token(Token::less))
    {
      fn->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      fn->parms = parse_parms_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }
    }

    if (ctx.try_consume_token(Token::arrow))
    {
      fn->returntype = parse_type(ctx, sema);

      if (!fn->returntype)
      {
        ctx.diag.error("expected return type", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }
    }

    if (ctx.tok != Token::l_brace)
    {
      ctx.diag.error("expected function body", ctx.text, ctx.tok.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    fn->body = parse_compound_statement(ctx, sema);

    lambda->fn = fn;
    lambda->decls.push_back(fn);

    return sema.make_lambda_expression(lambda, fn->loc());
  }

  //|///////////////////// parse_expression_head ////////////////////////////
  Expr *parse_expression_head(ParseContext &ctx, Token op, Expr *lhs, Sema &sema)
  {
    if (!lhs)
    {
      ctx.diag.error("expected expression", ctx.text, op.loc);
      ctx.comsume_til_resumable();
      return nullptr;
    }

    return sema.make_unary_expression(unaryopcode(op), lhs, op.loc);
  }

  //|///////////////////// parse_expression_post ////////////////////////////
  Expr *parse_expression_post(ParseContext &ctx, Expr *lhs, Sema &sema)
  {
    auto op = ctx.tok;

    switch(op.type)
    {
      case Token::period:
        return parse_expression_post(ctx, parse_member(ctx, lhs, sema), sema);

      case Token::l_square:
        return parse_expression_post(ctx, parse_subscript(ctx, lhs, sema), sema);

      case Token::l_paren:
        return parse_expression_post(ctx, parse_call(ctx, lhs, sema), sema);

      case Token::plusplus:
        ctx.consume_token();
        return sema.make_unary_expression(UnaryOpExpr::PostInc, lhs, op.loc);

      case Token::minusminus:
        ctx.consume_token();
        return sema.make_unary_expression(UnaryOpExpr::PostDec, lhs, op.loc);

      default:
        return lhs;
    }
  }

  //|///////////////////// parse_expression /////////////////////////////////
  Expr *parse_expression_left(ParseContext &ctx, Sema &sema)
  {
    auto op = ctx.tok;

    if (ctx.token(1) == Token::coloncolon)
    {
      return parse_expression_post(ctx, parse_callee(ctx, sema), sema);
    }

    switch(op.type)
    {
      case Token::l_paren:
        return parse_expression_post(ctx, parse_paren(ctx, sema), sema);

      case Token::plus:
        return parse_unary_plus(ctx, sema);

      case Token::minus:
        return parse_unary_minus(ctx, sema);

      case Token::kw_true:
      case Token::kw_false:
        return parse_bool_literal(ctx, sema);

      case Token::char_constant:
        return parse_char_literal(ctx, sema);

      case Token::numeric_constant:
        return parse_numeric_literal(ctx, sema);

      case Token::string_literal:
        return parse_string_literal(ctx, sema);

      case Token::l_square:
        return parse_expression_post(ctx, parse_array_literal(ctx, sema), sema);

      case Token::kw_void:
      case Token::kw_null:
        return parse_callee(ctx, sema);

      case Token::kw_sizeof:
        return parse_sizeof(ctx, sema);

      case Token::kw_alignof:
        return parse_alignof(ctx, sema);

      case Token::kw_cast:
        return parse_expression_post(ctx, parse_cast(ctx, sema), sema);

      case Token::kw_new:
        return parse_expression_post(ctx, parse_new(ctx, sema), sema);

      case Token::kw_fn:
        return parse_lambda(ctx, sema);

      case Token::kw_this:
      case Token::kw_typeof:
      case Token::coloncolon:
      case Token::identifier:
        return parse_expression_post(ctx, parse_callee(ctx, sema), sema);

      case Token::exclaim:
      case Token::tilde:
      case Token::minusminus:
      case Token::plusplus:
      case Token::amp:
      case Token::star:
      case Token::ampamp:
        ctx.consume_token();
        return parse_expression_head(ctx, op, parse_expression_left(ctx, sema), sema);

      case Token::hash:
        ctx.consume_token();
        return parse_expression_head(ctx, op, parse_expression(ctx, sema), sema);

      default:
        return nullptr;
    }
  }

  //|///////////////////// parse_expression /////////////////////////////////
  Expr *parse_expression_right(ParseContext &ctx, PrecLevel minprec, Expr *lhs, ptrdiff_t end, Sema &sema)
  {
    Expr *middle;

    if (!lhs)
      return lhs;

    while (true)
    {
      auto op = ctx.tok;
      auto prec = precedence(op);

      if (prec < minprec)
        return lhs;

      if (ctx.lexcursor.position == end)
        return lhs;

      ctx.consume_token();

      if (op == Token::question)
      {
        middle = parse_expression(ctx, sema);

        if (!ctx.try_consume_token(Token::colon))
        {
          ctx.diag.error("expected colon", ctx.text, ctx.tok.loc);
          ctx.comsume_til_resumable();
          return nullptr;
        }
      }

      auto rhs = parse_expression_left(ctx, sema);

      auto nextprec = precedence(ctx.tok);
      auto rightassoc = (prec == PrecLevel::Conditional || prec == PrecLevel::Assignment);

      if (prec < nextprec || (prec == nextprec && rightassoc))
      {
        rhs = parse_expression_right(ctx, static_cast<PrecLevel>(static_cast<int>(prec) + !rightassoc), rhs, end, sema);
      }

      if (!rhs)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        return nullptr;
      }

      if (op == Token::question)
      {
        lhs = sema.make_ternary_expression(lhs, middle, rhs, op.loc);
      }
      else
      {
        lhs = sema.make_binary_expression(binaryopcode(op), lhs, rhs, op.loc);
      }
    }
  }

  //|///////////////////// parse_expression /////////////////////////////////
  Expr *parse_expression(ParseContext &ctx, Sema &sema)
  {
    return parse_expression_right(ctx, PrecLevel::Assignment, parse_expression_left(ctx, sema), 0, sema);
  }

  Expr *parse_expression_til(ParseContext &ctx, LexCursor const &cursor, Sema &sema)
  {
    return parse_expression_right(ctx, PrecLevel::Assignment, parse_expression_left(ctx, sema), cursor.position, sema);
  }

  //|///////////////////// parse_if_declaration /////////////////////////////
  IfDecl *parse_if_declaration(ParseContext &ctx, Sema &sema)
  {
    auto ifd = sema.if_declaration(ctx.tok.loc);

    ctx.consume_token(Token::hash);
    ctx.consume_token(Token::kw_if);

    ifd->cond = parse_expression(ctx, sema);

    if (!ifd->cond)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return ifd;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_else_declaration ///////////////////////////
  IfDecl *parse_else_declaration(ParseContext &ctx, IfDecl *ifd, Sema &sema)
  {
    auto elsed = sema.if_declaration(ctx.tok.loc);

    ctx.consume_token(Token::hash);
    ctx.consume_token(Token::kw_else);

    if (ctx.try_consume_token(Token::kw_if))
    {
      if (!ctx.try_consume_token(Token::l_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }

      elsed->cond = parse_expression(ctx, sema);

      if (!elsed->cond)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        goto resume;
      }

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }
    else
    {
      elsed->cond = sema.make_bool_literal(true, elsed->loc());
    }

    ifd->elseif = elsed;

    return elsed;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_endif_declaration //////////////////////////
  IfDecl *parse_endif_declaration(ParseContext &ctx, IfDecl *ifd, Sema &sema)
  {
    ctx.consume_token(Token::hash);
    ctx.consume_token(Token::kw_endif);

    return ifd;
  }

  //|///////////////////// parse_import_declaration /////////////////////////
  Decl *parse_import_declaration(ParseContext &ctx, Sema &sema)
  {
    auto imprt = sema.import_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      imprt->flags |= Decl::Public;

    ctx.consume_token(Token::kw_import);

    auto loc = ctx.tok.loc;
    auto name = ctx.tok.text;

    if (ctx.tok != Token::identifier)
    {
      ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
      goto resume;
    }

    ctx.consume_token(Token::identifier);

    imprt->alias = name;

    while (ctx.try_consume_token(Token::period))
    {
      if (ctx.tok != Token::identifier)
      {
        ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
        goto resume;
      }

      name = string_view(name.data(), ctx.tok.text.end() - name.begin());

      ctx.consume_token(Token::identifier);
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "as")
    {
      ctx.consume_token(Token::identifier);

      if (ctx.tok != Token::identifier)
      {
        ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
        goto resume;
      }

      imprt->alias = ctx.tok.text;

      ctx.consume_token(Token::identifier);
    }

    if (ctx.try_consume_token(Token::colon))
    {
      while (ctx.tok != Token::semi && ctx.tok != Token::eof)
      {
        auto usein = sema.using_declaration(ctx.tok.loc);

        if (imprt->flags & Decl::Public)
          usein->flags |= Decl::Public;

        if (ctx.tok != Token::identifier)
        {
          ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
          ctx.comsume_til_resumable();
          return nullptr;
        }

        auto loc = ctx.tok.loc;
        auto name = parse_name(ctx, sema);

        usein->decl = sema.make_declref(name, loc);

        imprt->usings.push_back(usein);

        if (!ctx.try_consume_token(Token::comma))
          break;
      }
    }

    imprt->decl = sema.make_declref(name, loc);

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return imprt;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_using_declaration //////////////////////////
  Decl *parse_using_declaration(ParseContext &ctx, Sema &sema)
  {
    auto usein = sema.using_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      usein->flags |= Decl::Public;

    ctx.consume_token(Token::kw_using);

    usein->decl = parse_qualified_name(ctx, sema);

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return usein;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_typealias_declaration //////////////////////
  Decl *parse_typealias_declaration(ParseContext &ctx, Sema &sema)
  {
    auto alias = sema.alias_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      alias->flags |= Decl::Public;

    ctx.consume_token(Token::kw_using);

    alias->name = ctx.tok.text;

    ctx.consume_token(Token::identifier);

    if (ctx.try_consume_token(Token::less))
    {
      alias->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (!ctx.try_consume_token(Token::equal))
    {
      ctx.diag.error("expected equals", ctx.text, ctx.tok.loc);
      goto resume;
    }

    alias->type = parse_type(ctx, sema);

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return alias;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_using_or_alias_declaration /////////////////
  Decl *parse_using_or_alias_declaration(ParseContext &ctx, Sema &sema)
  {
    int i = 0;

    if (ctx.tok == Token::kw_pub)
      i += 1;

    if (ctx.token(i + 1) == Token::identifier && (ctx.token(i + 2) == Token::less || ctx.token(i + 2) == Token::equal))
    {
      return parse_typealias_declaration(ctx, sema);
    }
    else
    {
      return parse_using_declaration(ctx, sema);
    }
  }

  //|///////////////////// parse_var_declaration ////////////////////////////
  Decl *parse_var_declaration(ParseContext &ctx, Sema &sema)
  {
    auto var = sema.var_declaration(ctx.tok.loc);

    switch(ctx.tok.type)
    {
      case Token::kw_var:
        break;

      case Token::kw_let:
        var->flags |= VarDecl::Const;
        break;

      case Token::kw_const:
        var->flags |= VarDecl::Literal;
        break;

      default:
        assert(false);
    }

    ctx.consume_token();

    var->type = sema.make_typearg(sema.make_typearg("var", ctx.tok.loc));

    if (ctx.try_consume_token(Token::kw_const))
      var->flags |= VarDecl::Const;

    if (ctx.try_consume_token(Token::amp))
    {
      if (var->flags & VarDecl::Const)
        var->type = sema.make_const(var->type);

      var->type = sema.make_reference(var->type);
    }

    var->name = ctx.tok.text;

    if (!ctx.try_consume_token(Token::identifier))
    {
      ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::equal))
    {
      ctx.diag.error("expected assignment", ctx.text, ctx.tok.loc);
      goto resume;
    }

    var->value = parse_expression(ctx, sema);

    if (!var->value)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return var;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_field_declaration //////////////////////////
  Decl *parse_field_declaration(ParseContext &ctx, Sema &sema)
  {
    auto field = sema.field_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      field->flags |= FieldVarDecl::Public;

    field->type = parse_type(ctx, sema);

    if (!field->type)
    {
      ctx.diag.error("expected type", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (is_const_type(field->type))
    {
      field->flags |= VarDecl::Const;
      field->type = remove_const_type(field->type);
    }

    field->name = ctx.tok.text;

    if (!ctx.try_consume_token(Token::identifier))
    {
      ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return field;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_const_declaration //////////////////////////
  Decl *parse_const_declaration(ParseContext &ctx, Sema &sema)
  {
    auto fn = sema.function_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      fn->flags |= FunctionDecl::Public;

    ctx.consume_token(Token::kw_const);

    fn->flags |= FunctionDecl::Const;
    fn->flags |= FunctionDecl::ConstDecl;

    fn->name = ctx.tok.text;

    ctx.consume_token(Token::identifier);

    if (ctx.try_consume_token(Token::less))
    {
      fn->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (!ctx.try_consume_token(Token::equal))
    {
      ctx.diag.error("expected assignment", ctx.text, ctx.tok.loc);
      goto resume;
    }

    {
      auto retrn = sema.return_statement(ctx.tok.loc);

      retrn->expr = parse_expression(ctx, sema);

      if (!retrn->expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        goto resume;
      }

      fn->body = retrn;

      if (!ctx.try_consume_token(Token::semi))
      {
        ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    return fn;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_lambda_declaration /////////////////////////
  Decl *parse_lambda_declaration(ParseContext &ctx, Sema &sema)
  {
    auto var = sema.var_declaration(ctx.tok.loc);

    var->flags |= VarDecl::Const;
    var->type = sema.make_typearg(sema.make_typearg("lambda", ctx.tok.loc));

    var->value = parse_lambda(ctx, sema);

    if (!var->value)
      return nullptr;

    var->name = decl_cast<LambdaDecl>(expr_cast<LambdaExpr>(var->value)->decl)->name;

    if (var->name.empty())
    {
      ctx.diag.error("expected identifier", ctx.text, var->loc());
      goto resume;
    }

    return var;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_function_declaration ///////////////////////
  Decl *parse_function_declaration(ParseContext &ctx, Sema &sema)
  {
    auto fn = sema.function_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      fn->flags |= FunctionDecl::Public;

    if (ctx.try_consume_token(Token::kw_extern))
    {
      auto abi = FunctionDecl::ExternC;

      if (ctx.tok == Token::string_literal)
      {
        ctx.consume_token(Token::string_literal);
      }

      fn->flags |= abi;
    }

    if (ctx.try_consume_token(Token::kw_const))
      fn->flags |= FunctionDecl::Const;

    ctx.consume_token(Token::kw_fn);

    auto name = parse_name(ctx, sema);

    if (ctx.tok == Token::equal)
    {
      if (ctx.tok.text.begin() != name.end())
      {
        ctx.diag.error("extra characters within function name", ctx.text, ctx.tok.loc);
      }

      name = string_view(name.data(), name.length() + 1);

      ctx.consume_token();
    }

    fn->name = name;

    if (ctx.tok == Token::coloncolon && ctx.token(1) != Token::identifier)
      ctx.consume_token();

    if (ctx.try_consume_token(Token::less))
    {
      fn->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      fn->parms = parse_parms_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.try_consume_token(Token::kw_throws))
    {
      if (ctx.try_consume_token(Token::l_paren))
      {
        fn->throws = parse_expression(ctx, sema);

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          goto resume;
        }
      }
      else
      {
        fn->throws = sema.make_bool_literal(true, ctx.tok.loc);
      }
    }

    if (ctx.try_consume_token(Token::arrow))
    {
      fn->returntype = parse_type(ctx, sema);

      if (!fn->returntype)
      {
        ctx.diag.error("expected return type", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if ((fn->flags & FunctionDecl::ExternMask) && !fn->returntype)
    {
      ctx.diag.error("expected returntype on extern function", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (ctx.try_consume_token(Token::equal))
    {
      if (ctx.tok.text == "default")
        fn->flags |= FunctionDecl::Defaulted;

      if (ctx.tok.text == "delete")
        fn->flags |= FunctionDecl::Deleted;

      ctx.consume_token();

      if (ctx.tok != Token::semi)
      {
        ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "where")
    {
      ctx.consume_token(Token::identifier);

      fn->where = parse_expression(ctx, sema);
    }

    if (ctx.tok != Token::semi && ctx.tok != Token::l_brace)
    {
      ctx.diag.error("expected function body", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      if (fn->flags & FunctionDecl::ExternMask)
      {
        ctx.diag.error("expected semi on extern function", ctx.text, ctx.tok.loc);
        goto resume;
      }

      fn->body = parse_compound_statement(ctx, sema);
    }

    return fn;

  resume:
    ctx.comsume_til_resumable();
    return nullptr;
  }

  //|///////////////////// parse_initialiser_list ///////////////////////////
  vector<Decl*> parse_initialiser_list(ParseContext &ctx, Sema &sema)
  {
    vector<Decl*> inits;

    while (ctx.tok != Token::l_brace && ctx.tok != Token::eof)
    {
      auto init = sema.initialiser_declaration(ctx.tok.loc);

      init->decl = sema.make_declref(ctx.tok.text, ctx.tok.loc);

      if (!ctx.try_consume_token(Token::identifier))
      {
        ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        break;
      }

      if (!ctx.try_consume_token(Token::l_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        break;
      }

      init->parms = parse_expression_list(ctx, sema);
      init->namedparms = parse_named_expression_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        ctx.comsume_til_resumable();
        break;
      }

      inits.push_back(init);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return inits;
  }

  //|///////////////////// parse_constructor_declaration ////////////////////
  Decl *parse_constructor_declaration(ParseContext &ctx, Sema &sema)
  {
    auto fn = sema.function_declaration(ctx.tok.loc);

    fn->flags |= FunctionDecl::Constructor;

    if (ctx.try_consume_token(Token::kw_pub))
      fn->flags |= FunctionDecl::Public;

    if (ctx.try_consume_token(Token::kw_const))
      fn->flags |= FunctionDecl::Const;

    fn->name = ctx.tok.text;

    ctx.consume_token(Token::identifier);

    if (ctx.tok == Token::coloncolon && ctx.token(1) != Token::identifier)
      ctx.consume_token();

    if (ctx.try_consume_token(Token::less))
    {
      fn->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      fn->parms = parse_parms_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.try_consume_token(Token::equal))
    {
      if (ctx.tok.text == "default")
        fn->flags |= FunctionDecl::Defaulted;

      if (ctx.tok.text == "delete")
        fn->flags |= FunctionDecl::Deleted;

      ctx.consume_token();

      if (ctx.tok != Token::semi)
      {
        ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.try_consume_token(Token::colon))
    {
      fn->inits = parse_initialiser_list(ctx, sema);
    }

    if (ctx.tok != Token::semi && ctx.tok != Token::l_brace)
    {
      ctx.diag.error("expected function body", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      fn->body = parse_compound_statement(ctx, sema);
    }

    return fn;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_destructor_declaration /////////////////////
  Decl *parse_destructor_declaration(ParseContext &ctx, Sema &sema)
  {
    auto fn = sema.function_declaration(ctx.tok.loc);

    fn->flags |= FunctionDecl::Destructor;

    fn->name = string_view(ctx.tok.text.data(), ctx.token(1).text.length() + 1);

    ctx.consume_token(Token::tilde);
    ctx.consume_token(Token::identifier);

    if (ctx.tok == Token::coloncolon && ctx.token(1) != Token::identifier)
      ctx.consume_token();

    if (ctx.try_consume_token(Token::l_paren))
    {
      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.try_consume_token(Token::equal))
    {
      if (ctx.tok.text == "default")
        fn->flags |= FunctionDecl::Defaulted;

      if (ctx.tok.text == "delete")
        fn->flags |= FunctionDecl::Deleted;

      ctx.consume_token();

      if (ctx.tok != Token::semi)
      {
        ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.tok != Token::semi && ctx.tok != Token::l_brace)
    {
      ctx.diag.error("expected function body", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      fn->body = parse_compound_statement(ctx, sema);
    }

    return fn;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_struct_declaration /////////////////////////
  Decl *parse_struct_declaration(ParseContext &ctx, Sema &sema)
  {
    auto strct = sema.struct_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      strct->flags |= StructDecl::Public;

    ctx.consume_token(Token::kw_struct);

    if (ctx.tok == Token::identifier)
    {
      strct->name = ctx.tok.text;

      ctx.consume_token(Token::identifier);
    }

    if (ctx.try_consume_token(Token::less))
    {
      strct->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.try_consume_token(Token::colon))
    {
      strct->basetype = parse_type(ctx, sema);
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      if (!ctx.try_consume_token(Token::l_brace))
      {
        ctx.diag.error("expected brace", ctx.text, ctx.tok.loc);
        goto resume;
      }

      Decl *decl = nullptr;

      IfDecl *conditional = nullptr;
      vector<IfDecl*> conditionals_stack;

      while (ctx.tok != Token::r_brace && ctx.tok != Token::eof)
      {
        auto tok = ctx.tok;
        auto nexttok = 1;

        if (tok == Token::kw_pub)
        {
          tok = ctx.token(nexttok++);
        }

        if (tok == Token::kw_const)
        {
          switch (ctx.token(nexttok).type)
          {
            case Token::kw_fn:
              tok = ctx.token(nexttok++);
              break;

            case Token::identifier:
              break;

            default:
              goto unhandled;
          }
        }

        switch(tok.type)
        {
          case Token::semi:
            ctx.diag.warn("extra semi", ctx.text, tok.loc);
            ctx.consume_token(Token::semi);
            break;

          case Token::kw_const:
            decl = parse_const_declaration(ctx, sema);
            break;

          case Token::kw_fn:
            decl = parse_function_declaration(ctx, sema);
            break;

          case Token::kw_struct:
            decl = parse_struct_declaration(ctx, sema);
            break;

          case Token::kw_enum:
            decl = parse_enum_declaration(ctx, sema);
            break;

          case Token::kw_using:
            decl = parse_using_or_alias_declaration(ctx, sema);
            break;

          case Token::l_paren:
          case Token::identifier:
            if (tok.text == strct->name)
            {
              auto tok = ctx.tok;
              auto lexcursor = ctx.lexcursor;

              lexcursor = lex(ctx.text, lexcursor, tok);

              if (tok == Token::less)
              {
                for(int indent = 0; tok != Token::eof; )
                {
                  if (tok == Token::less)
                    indent += 1;

                  if (tok == Token::greater)
                    indent -= 1;

                  if (tok == Token::greatergreater)
                    indent -= 2;

                  lexcursor = lex(ctx.text, lexcursor, tok);

                  if (indent <= 0)
                    break;
                }
              }

              if (tok == Token::l_paren)
              {
                decl = parse_constructor_declaration(ctx, sema);
                break;
              }
            }

            decl = parse_field_declaration(ctx, sema);
            break;

          case Token::tilde:
            decl = parse_destructor_declaration(ctx, sema);
            break;

          case Token::hash:
            switch (ctx.token(nexttok).type)
            {
              case Token::kw_if:
                conditionals_stack.push_back(conditional);
                conditionals_stack.push_back(parse_if_declaration(ctx, sema));
                conditional = conditionals_stack.back();
                continue;

              case Token::kw_else:
                if (conditionals_stack.empty())
                  goto unhandled;

                conditional = parse_else_declaration(ctx, conditional, sema);
                continue;

              case Token::kw_endif:
                if (conditionals_stack.empty())
                  goto unhandled;

                decl = parse_endif_declaration(ctx, conditionals_stack.back(), sema);

                conditionals_stack.pop_back();
                conditional = conditionals_stack.back();
                conditionals_stack.pop_back();
                break;

              default:
                goto unhandled;
            }
            break;

          case Token::eof:
            break;

          default:
          unhandled:
            ctx.diag.error("expected member declaration", ctx.text, tok.loc);
            goto resume;
        }

        if (!decl)
          break;

        decl->flags |= Decl::Public;

        if (conditional)
        {
          decl->flags |= Decl::Conditional;

          conditional->decls.push_back(decl);

          continue;
        }

        strct->decls.push_back(decl);
      }

      if (ctx.tok == Token::eof)
      {
        ctx.diag.error("unexpected end of file", ctx.text, ctx.tok.loc);
        goto resume;
      }

      if (!ctx.try_consume_token(Token::r_brace))
      {
        ctx.diag.error("expected brace", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    return strct;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_constant_declaration ///////////////////////
  Decl *parse_constant_declaration(ParseContext &ctx, Sema &sema)
  {
    auto constant = sema.enum_constant_declaration(ctx.tok.loc);

    constant->flags |= Decl::Public;

    constant->name = ctx.tok.text;

    ctx.consume_token(Token::identifier);

    if (ctx.try_consume_token(Token::equal))
    {
      constant->value = parse_expression(ctx, sema);

      if (!constant->value)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    ctx.try_consume_token(Token::comma);

    return constant;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_enum_declaration ///////////////////////////
  Decl *parse_enum_declaration(ParseContext &ctx, Sema &sema)
  {
    auto enumm = sema.enum_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      enumm->flags |= EnumDecl::Public;

    ctx.consume_token(Token::kw_enum);

    if (ctx.tok == Token::identifier)
    {
      enumm->name = ctx.tok.text;

      ctx.consume_token(Token::identifier);
    }

    if (ctx.try_consume_token(Token::colon))
    {
      enumm->basetype = parse_type(ctx, sema);
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      if (!ctx.try_consume_token(Token::l_brace))
      {
        ctx.diag.error("expected brace", ctx.text, ctx.tok.loc);
        goto resume;
      }

      Decl *decl = nullptr;

      IfDecl *conditional = nullptr;
      vector<IfDecl*> conditionals_stack;

      while (ctx.tok != Token::r_brace && ctx.tok != Token::eof)
      {
        auto tok = ctx.tok;
        auto nexttok = 1;

        if (tok == Token::kw_pub)
        {
          tok = ctx.token(nexttok++);
        }

        if (tok == Token::kw_const)
        {
          switch (ctx.token(nexttok).type)
          {
            case Token::kw_fn:
              tok = ctx.token(nexttok++);
              break;

            case Token::identifier:
              break;

            default:
              goto unhandled;
          }
        }

        switch(tok.type)
        {
          case Token::semi:
            ctx.diag.warn("extra semi", ctx.text, tok.loc);
            ctx.consume_token(Token::semi);
            break;

          case Token::kw_const:
            decl = parse_const_declaration(ctx, sema);
            break;

          case Token::kw_fn:
            decl = parse_function_declaration(ctx, sema);
            break;

          case Token::identifier:
            decl = parse_constant_declaration(ctx, sema);
            break;

          case Token::hash:
            switch (ctx.token(nexttok).type)
            {
              case Token::kw_if:
                conditionals_stack.push_back(conditional);
                conditionals_stack.push_back(parse_if_declaration(ctx, sema));
                conditional = conditionals_stack.back();
                continue;

              case Token::kw_else:
                if (conditionals_stack.empty())
                  goto unhandled;

                conditional = parse_else_declaration(ctx, conditional, sema);
                continue;

              case Token::kw_endif:
                if (conditionals_stack.empty())
                  goto unhandled;

                decl = parse_endif_declaration(ctx, conditionals_stack.back(), sema);

                conditionals_stack.pop_back();
                conditional = conditionals_stack.back();
                conditionals_stack.pop_back();
                break;

              default:
                goto unhandled;
            }
            break;

          case Token::eof:
            break;

          default:
          unhandled:
            ctx.diag.error("expected member declaration", ctx.text, tok.loc);
            goto resume;
        }

        if (!decl)
          break;

        if (conditional)
        {
          decl->flags |= Decl::Conditional;

          conditional->decls.push_back(decl);

          continue;
        }

        enumm->decls.push_back(decl);
      }

      if (ctx.tok == Token::eof)
      {
        ctx.diag.error("unexpected end of file", ctx.text, ctx.tok.loc);
        goto resume;
      }

      if (!ctx.try_consume_token(Token::r_brace))
      {
        ctx.diag.error("expected brace", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    return enumm;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_requires_declaration ///////////////////////
  Decl *parse_requires_declaration(ParseContext &ctx, Sema &sema)
  {
    auto fn = sema.requires_declaration(ctx.tok.loc);

    ctx.consume_token(Token::identifier);

    if (ctx.try_consume_token(Token::less))
    {
      fn->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      fn->parms = parse_parms_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.tok == Token::l_brace)
    {
      fn->flags |= RequiresDecl::Expression;

      fn->body = parse_compound_statement(ctx, sema);

      if (ctx.try_consume_token(Token::arrow))
      {
        fn->returntype = parse_type(ctx, sema);

        if (!fn->returntype)
        {
          ctx.diag.error("expected requires type", ctx.text, ctx.tok.loc);
          goto resume;
        }
      }
    }
    else
    {
      fn->flags |= RequiresDecl::Condition;

      auto retrn = sema.return_statement(ctx.tok.loc);

      retrn->expr = parse_expression(ctx, sema);

      if (!retrn->expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        goto resume;
      }

      fn->body = retrn;

      fn->returntype = Builtin::type(Builtin::Type_Bool);
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return fn;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_concept_declaration ////////////////////////
  Decl *parse_concept_declaration(ParseContext &ctx, Sema &sema)
  {
    auto koncept = sema.concept_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      koncept->flags |= FunctionDecl::Public;

    ctx.consume_token(Token::kw_concept);

    koncept->name = ctx.tok.text;

    ctx.consume_token(Token::identifier);

    if (ctx.try_consume_token(Token::less))
    {
      koncept->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      if (!ctx.try_consume_token(Token::l_brace))
      {
        ctx.diag.error("expected brace", ctx.text, ctx.tok.loc);
        goto resume;
      }

      Decl *decl = nullptr;

      while (ctx.tok != Token::r_brace && ctx.tok != Token::eof)
      {
        switch(ctx.tok.type)
        {
          case Token::identifier:
            if (ctx.tok.text == "requires")
              decl = parse_requires_declaration(ctx, sema);
            break;

          default:
            ctx.diag.error("expected concept declaration", ctx.text, ctx.tok.loc);
            goto resume;
        }

        if (!decl)
          break;

        koncept->decls.push_back(decl);
      }
    }

    if (!ctx.try_consume_token(Token::r_brace))
    {
      ctx.diag.error("expected brace", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return koncept;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_declaration_statement //////////////////////
  Stmt *parse_declaration_statement(ParseContext &ctx, Sema &sema)
  {
    auto stmt = sema.declaration_statement(ctx.tok.loc);

    switch (ctx.tok.type)
    {
      case Token::kw_fn:
        stmt->decl = parse_lambda_declaration(ctx, sema);
        break;

      case Token::kw_struct:
        stmt->decl = parse_struct_declaration(ctx, sema);
        break;

      case Token::kw_enum:
        stmt->decl = parse_enum_declaration(ctx, sema);
        break;

      case Token::kw_import:
        stmt->decl = parse_import_declaration(ctx, sema);
        break;

      case Token::kw_using:
        stmt->decl = parse_using_or_alias_declaration(ctx, sema);
        break;

      case Token::kw_let:
      case Token::kw_var:
      case Token::kw_const:
        stmt->decl = parse_var_declaration(ctx, sema);
        break;

      default:
        ctx.diag.error("expected declaration", ctx.text, ctx.tok.loc);
        goto resume;
    }

    if (!stmt->decl)
      goto resume;

    return stmt;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_expression_statement ///////////////////////
  Stmt *parse_expression_statement(ParseContext &ctx, Sema &sema)
  {
    auto stmt = sema.expression_statement(ctx.tok.loc);

    stmt->expr = parse_expression(ctx, sema);

    if (!stmt->expr)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return stmt;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_if_statement ///////////////////////////////
  Stmt *parse_if_statement(ParseContext &ctx, Sema &sema)
  {
    auto ifs = sema.if_statement(ctx.tok.loc);

    if (ctx.try_consume_token(Token::hash))
      ifs->flags |= IfStmt::Static;

    ctx.consume_token(Token::kw_if);

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    {
      auto inits = parse_statement_list(ctx, sema);

      if (ctx.tok != Token::semi)
      {
        if (inits.size() == 1 && inits.back()->kind() == Stmt::Expression)
        {
          ifs->cond = stmt_cast<ExprStmt>(inits.back())->expr;
        }
      }

      if (ctx.try_consume_token(Token::semi))
      {
        ifs->inits = std::move(inits);
        ifs->cond = parse_expression(ctx, sema);
      }
    }

    if (!ifs->cond)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    ifs->stmts[0] = parse_statement(ctx, sema);

    if (!ifs->stmts[0])
    {
      ctx.diag.error("expected statement", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if ((ifs->flags & IfStmt::Static) && ctx.tok == Token::hash && ctx.token(1) == Token::kw_else)
      ctx.consume_token(Token::hash);

    if (ctx.try_consume_token(Token::kw_else))
    {
      ifs->stmts[1] = parse_statement(ctx, sema);

      if (!ifs->stmts[1])
      {
        ctx.diag.error("expected statement", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    return ifs;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_for_statement //////////////////////////////
  Stmt *parse_for_statement(ParseContext &ctx, Sema &sema)
  {
    auto fors = sema.for_statement(ctx.tok.loc);

    if (ctx.try_consume_token(Token::hash))
      fors->flags |= ForStmt::Static;

    ctx.consume_token(Token::kw_for);

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    fors->inits = parse_statement_list(ctx, sema);

    if (ctx.try_consume_token(Token::semi))
    {
      fors->cond = parse_expression(ctx, sema);

      if (ctx.try_consume_token(Token::semi))
      {
        fors->iters = parse_statement_list(ctx, sema);
      }

      if (!all_of(fors->iters.begin(), fors->iters.end(), [](auto &k) { return k->kind() == Stmt::Expression; }))
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    fors->stmt = parse_statement(ctx, sema);

    if (!fors->stmt)
    {
      ctx.diag.error("expected statement", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return fors;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_rof_statement //////////////////////////////
  Stmt *parse_rof_statement(ParseContext &ctx, Sema &sema)
  {
    auto rofs = sema.rof_statement(ctx.tok.loc);

    if (ctx.try_consume_token(Token::hash))
      rofs->flags |= ForStmt::Static;

    ctx.consume_token(Token::kw_rof);

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    rofs->inits = parse_statement_list(ctx, sema);

    if (ctx.try_consume_token(Token::semi))
    {
      rofs->cond = parse_expression(ctx, sema);

      if (ctx.try_consume_token(Token::semi))
      {
        rofs->iters = parse_statement_list(ctx, sema);
      }

      if (!all_of(rofs->iters.begin(), rofs->iters.end(), [](auto &k) { return k->kind() == Stmt::Expression; }))
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    rofs->stmt = parse_statement(ctx, sema);

    if (!rofs->stmt)
    {
      ctx.diag.error("expected statement", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return rofs;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_while_statement ////////////////////////////
  Stmt *parse_while_statement(ParseContext &ctx, Sema &sema)
  {
    auto wile = sema.while_statement(ctx.tok.loc);

    ctx.consume_token(Token::kw_while);

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    {
      auto inits = parse_statement_list(ctx, sema);

      if (ctx.tok != Token::semi)
      {
        if (inits.size() == 1 && inits.back()->kind() == Stmt::Expression)
        {
          wile->cond = stmt_cast<ExprStmt>(inits.back())->expr;
        }
      }

      if (ctx.try_consume_token(Token::semi))
      {
        wile->inits = std::move(inits);
        wile->cond = parse_expression(ctx, sema);
      }
    }

    if (!wile->cond)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    wile->stmt = parse_statement(ctx, sema);

    if (!wile->stmt)
    {
      ctx.diag.error("expected statement", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return wile;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_try_statement //////////////////////////////
  Stmt *parse_try_statement(ParseContext &ctx, Sema &sema)
  {
    auto trys = sema.try_statement(ctx.tok.loc);

    ctx.consume_token(Token::kw_try);

    trys->body = parse_compound_statement(ctx, sema);

    if (!trys->body)
    {
      ctx.diag.error("expected statement", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::kw_catch))
    {
      ctx.diag.error("expected catch", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    {
      auto var = sema.errorvar_declaration(ctx.tok.loc);

      var->type = parse_type(ctx, sema);

      if (!var->type)
      {
        ctx.diag.error("expected type", ctx.text, ctx.tok.loc);
        goto resume;
      }

      if (is_const_type(var->type))
      {
        var->flags |= VarDecl::Const;
        var->type = remove_const_type(var->type);
      }

      if (is_reference_type(var->type))
      {
        ctx.diag.error("expect value type", ctx.text, ctx.tok.loc);
        goto resume;
      }

      if (ctx.tok == Token::identifier)
      {
        var->name = ctx.tok.text;

        ctx.consume_token();
      }

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }

      trys->errorvar = var;
    }

    trys->handler = parse_compound_statement(ctx, sema);

    if (!trys->handler)
    {
      ctx.diag.error("expected statement", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return trys;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_throw_statement ////////////////////////////
  Stmt *parse_throw_statement(ParseContext &ctx, Sema &sema)
  {
    auto throwe = sema.throw_statement(ctx.tok.loc);

    ctx.consume_token(Token::kw_throw);

    throwe->expr = parse_expression(ctx, sema);

    if (!throwe->expr)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return throwe;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_break_statement ////////////////////////////
  Stmt *parse_break_statement(ParseContext &ctx, Sema &sema)
  {
    auto breck = sema.break_statement(ctx.tok.loc);

    ctx.consume_token(Token::kw_break);

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return breck;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_continue_statement /////////////////////////
  Stmt *parse_continue_statement(ParseContext &ctx, Sema &sema)
  {
    auto continu = sema.continue_statement(ctx.tok.loc);

    ctx.consume_token(Token::kw_continue);

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return continu;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_return_statement ///////////////////////////
  Stmt *parse_return_statement(ParseContext &ctx, Sema &sema)
  {
    auto retrn = sema.return_statement(ctx.tok.loc);

    ctx.consume_token(Token::kw_return);

    retrn->expr = parse_expression(ctx, sema);

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return retrn;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_compound_statement /////////////////////////
  Stmt *parse_compound_statement(ParseContext &ctx, Sema &sema)
  {
    auto compound = sema.compound_statement(ctx.tok.loc);

    ctx.consume_token(Token::l_brace);

    while (ctx.tok != Token::r_brace && ctx.tok != Token::eof)
    {
      Stmt *stmt = nullptr;

      switch(ctx.tok.type)
      {
        case Token::kw_fn:
        case Token::kw_const:
        case Token::kw_import:
        case Token::kw_using:
        case Token::kw_struct:
        case Token::kw_enum:
        case Token::kw_let:
        case Token::kw_var:
          stmt = parse_declaration_statement(ctx, sema);
          break;

        default:
          stmt = parse_statement(ctx, sema);
          break;
      }

      if (stmt)
      {
        compound->stmts.push_back(stmt);
      }
    }

    compound->endloc = ctx.tok.loc;

    if (ctx.tok == Token::eof)
    {
      ctx.diag.error("unexpected end of file", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::r_brace))
    {
      ctx.diag.error("expected brace", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return compound;

    resume:
      ctx.comsume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_statement //////////////////////////////////
  Stmt *parse_statement(ParseContext &ctx, Sema &sema)
  {
    switch(ctx.tok.type)
    {
      case Token::kw_if:
        return parse_if_statement(ctx, sema);

      case Token::kw_for:
        return parse_for_statement(ctx, sema);

      case Token::kw_rof:
        return parse_rof_statement(ctx, sema);

      case Token::kw_try:
        return parse_try_statement(ctx, sema);

      case Token::kw_while:
        return parse_while_statement(ctx, sema);

      case Token::kw_throw:
        return parse_throw_statement(ctx, sema);

      case Token::kw_break:
        return parse_break_statement(ctx, sema);

      case Token::kw_continue:
        return parse_continue_statement(ctx, sema);

      case Token::kw_return:
        return parse_return_statement(ctx, sema);

      case Token::l_brace:
        return parse_compound_statement(ctx, sema);

      case Token::hash:
        switch (auto nextok = ctx.token(1); nextok.type)
        {
          case Token::kw_if:
            return parse_if_statement(ctx, sema);

          case Token::kw_for:
            return parse_for_statement(ctx, sema);

          default:
            return parse_expression_statement(ctx, sema);
        }
        break;

      case Token::semi: {
        auto loc = ctx.tok.loc;
        ctx.consume_token(Token::semi);
        return sema.null_statement(loc);
      }

      default:
        return parse_expression_statement(ctx, sema);
    }
  }

  //|///////////////////// parse_toplevel_declaration ///////////////////////
  Decl *parse_toplevel_declaration(ParseContext &ctx, Sema &sema)
  {
    Decl *decl = nullptr;

    IfDecl *conditional = nullptr;
    vector<IfDecl*> conditionals_stack;

    while (ctx.tok != Token::eof)
    {
      auto tok = ctx.tok;
      auto nexttok = 1;

      if (tok == Token::kw_pub)
      {
        tok = ctx.token(nexttok++);
      }

      if (tok == Token::kw_const)
      {
        switch (ctx.token(nexttok).type)
        {
          case Token::kw_fn:
            tok = ctx.token(nexttok++);
            break;

          case Token::identifier:
            break;

          default:
            goto unhandled;
        }
      }

      switch (tok.type)
      {
        case Token::semi:
          ctx.diag.warn("extra semi", ctx.text, tok.loc);
          ctx.consume_token(Token::semi);
          break;

        case Token::kw_extern:
          decl = parse_function_declaration(ctx, sema);
          break;

        case Token::kw_const:
          decl = parse_const_declaration(ctx, sema);
          break;

        case Token::kw_fn:
          decl = parse_function_declaration(ctx, sema);
          break;

        case Token::kw_struct:
          decl = parse_struct_declaration(ctx, sema);
          break;

        case Token::kw_concept:
          decl = parse_concept_declaration(ctx, sema);
          break;

        case Token::kw_enum:
          decl = parse_enum_declaration(ctx, sema);
          break;

        case Token::kw_using:
          decl = parse_using_or_alias_declaration(ctx, sema);
          break;

        case Token::kw_import:
          decl = parse_import_declaration(ctx, sema);
          break;

        case Token::hash:
          switch (ctx.token(nexttok).type)
          {
            case Token::kw_if:
              conditionals_stack.push_back(conditional);
              conditionals_stack.push_back(parse_if_declaration(ctx, sema));
              conditional = conditionals_stack.back();
              continue;

            case Token::kw_else:
              if (conditionals_stack.empty())
                goto unhandled;

              conditional = parse_else_declaration(ctx, conditional, sema);
              continue;

            case Token::kw_endif:
              if (conditionals_stack.empty())
                goto unhandled;

              decl = parse_endif_declaration(ctx, conditionals_stack.back(), sema);

              conditionals_stack.pop_back();
              conditional = conditionals_stack.back();
              conditionals_stack.pop_back();
              break;

            default:
              goto unhandled;
          }
          break;

        case Token::eof:
          break;

        default:
        unhandled:
          ctx.diag.error("expected toplevel declaration", ctx.text, tok.loc);
          ctx.comsume_til_resumable();
          return nullptr;
      }

      if (!decl || !conditional)
        break;

      conditional->decls.push_back(decl);
    }

    if (conditionals_stack.size() != 0)
    {
      ctx.diag.error("unmatched conditional declarations", ctx.text, conditionals_stack.back()->loc());
    }

    return decl;
  }
}


//|--------------------- Parser ---------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// load ///////////////////////////////////////////////
void load(ModuleDecl *module, Sema &sema, Diag &diag)
{
  SourceText text(module->file());

  if (!text)
  {
    diag.error("opening file '" + module->file() + "'");
    return;
  }

  ParseContext ctx(text, diag);

  while (ctx.tok != Token::eof)
  {
    if (auto decl = parse_toplevel_declaration(ctx, sema))
    {
      module->decls.push_back(decl);
    }
  }
}

//|///////////////////// parse //////////////////////////////////////////////
void parse(string const &path, Sema &sema, Diag &diag)
{
  auto unit = sema.translation_unit(path);

  load(decl_cast<ModuleDecl>(unit->mainmodule), sema, diag);

  semantic(decl_cast<ModuleDecl>(unit->mainmodule), sema, diag);

  sema.end();
}