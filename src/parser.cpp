//
// parser.cpp
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
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

    vector<Decl*> attributes;
    vector<Expr*> substitutions;

    Ident *fname = nullptr;

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

      for ( ; token != Token::eof && i > 0; --i)
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

    void consume_til_resumable()
    {
      while (true)
      {
        switch (tok.type)
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

          case Token::r_brace:
            return;

          case Token::eof:
            return;

          default:
            consume_token();
        }
      }
    }
  };

  enum class IdentUsage
  {
    VarName,
    TagName,
    FunctionName,
    ScopedName,
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
      case Token::questionquestion:
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
      case Token::questionexclaim: return UnaryOpExpr::Unwrap;
      case Token::amp: return UnaryOpExpr::Ref;
      case Token::star: return UnaryOpExpr::Fer;
      case Token::ampamp: return UnaryOpExpr::Fwd;
      case Token::hash: return UnaryOpExpr::Literal;
      case Token::kw_extern: return UnaryOpExpr::Extern;

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
      case Token::questionquestion: return BinaryOpExpr::Coalesce;

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
  Decl *parse_union_declaration(ParseContext &ctx, Sema &sema);
  Decl *parse_vtable_declaration(ParseContext &ctx, Sema &sema);
  Decl *parse_concept_declaration(ParseContext &ctx, Sema &sema);
  Stmt *parse_statement(ParseContext &ctx, Sema &sema);
  Stmt *parse_compound_statement(ParseContext &ctx, Sema &sema);
  Stmt *parse_declaration_statement(ParseContext &ctx, Sema &sema);

  //|///////////////////// consume_attributes ///////////////////////////////
  void consume_attributes(ParseContext &ctx, Sema &sema)
  {
    ctx.try_consume_token(Token::hash);
    ctx.try_consume_token(Token::l_square);

    while (ctx.tok != Token::r_square && ctx.tok != Token::eof)
    {
      auto attribute = sema.attribute_declaration(ctx.tok.loc);

      attribute->name = ctx.tok.text;

      if (!ctx.try_consume_token(Token::identifier))
      {
        ctx.diag.error("expected attribute", ctx.text, ctx.tok.loc);
        break;
      }

      if (ctx.tok == Token::l_paren)
      {
        auto beg = ctx.tok.text.data();

        for (int indent = 0; ctx.tok != Token::eof; )
        {
          if (ctx.tok == Token::l_paren)
            indent += 1;

          if (ctx.tok == Token::r_paren)
            if (--indent <= 0)
              break;

          ctx.consume_token();
        }

        if (ctx.tok != Token::eof)
        {
          attribute->options = string_view(beg, ctx.tok.text.data() - beg + 1);
        }

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
        }
      }

      ctx.attributes.push_back(attribute);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    if (!ctx.try_consume_token(Token::r_square))
    {
      ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
    }
  }

  //|///////////////////// consume_substitution /////////////////////////////
  void consume_substitution(ParseContext &ctx, Sema &sema)
  {
    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
    }

    auto expr = parse_expression(ctx, sema);

    if (!expr)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
    }

    ctx.substitutions.push_back(expr);
  }

  //|///////////////////// parse_ident //////////////////////////////////////
  Ident *parse_ident(ParseContext &ctx, IdentUsage usage, Sema &sema)
  {
    switch (auto tok = ctx.tok; tok.type)
    {
      case Token::identifier:
      case Token::kw_move:
      case Token::kw_vtable:
         ctx.consume_token();

        return Ident::from(tok.text);

      case Token::l_square:
      case Token::l_paren:
      case Token::plus: case Token::plusplus: case Token::plusequal:
      case Token::minus: case Token::minusminus: case Token::minusequal:
      case Token::star: case Token::starequal:
      case Token::slash: case Token::slashequal:
      case Token::percent: case Token::percentequal:
      case Token::arrow: case Token::arrowstar:
      case Token::amp: case Token::ampamp: case Token::ampequal:
      case Token::pipe: case Token::pipepipe: case Token::pipeequal:
      case Token::caret: case Token::caretequal:
      case Token::exclaim: case Token::exclaimequal:
      case Token::tilde:
      case Token::less: case Token::lessless: case Token::lesslessequal: case Token::lessequal:
      case Token::greater: case Token::greatergreater: case Token::greatergreaterequal: case Token::greaterequal:
      case Token::equal: case Token::equalequal:
      case Token::questionquestion:
      case Token::questionexclaim:
      case Token::spaceship:
      case Token::kw_yield:
      case Token::kw_await:
      case Token::kw_void:
      case Token::kw_null:
      case Token::kw_new:
      case Token::kw_nil:
      case Token::kw_var:
        ctx.consume_token();

        if (usage != IdentUsage::FunctionName && usage != IdentUsage::ScopedName)
          break;

        if (tok == Token::l_square || tok == Token::l_paren || (tok == Token::tilde && ctx.tok == Token::identifier))
        {
          if (ctx.tok.text.data() != tok.text.data() + tok.text.length())
            ctx.diag.error("extra characters within identifier", ctx.text, ctx.tok.loc);

          tok.text = string_view(tok.text.data(), tok.text.length() + ctx.tok.text.length());

          ctx.consume_token();
        }

        return Ident::from(tok.text);

      case Token::numeric_constant:
        ctx.consume_token();

        if (usage != IdentUsage::ScopedName)
          break;

        return Ident::make_index_ident(tok.text);

      case Token::hash:
        ctx.consume_token();

        if (usage != IdentUsage::ScopedName)
          break;

        if (ctx.tok == Token::identifier)
        {
          tok.text = ctx.tok.text;

          ctx.consume_token();
        }

        return Ident::make_hash_ident(tok.text);

      case Token::dollar:
        ctx.consume_token();
        consume_substitution(ctx, sema);

        return Ident::make_dollar_ident(ctx.substitutions.size() - 1);

      default:
        break;
    }

    ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);

    return nullptr;
  }

  //|///////////////////// parse_var_defn ///////////////////////////////////
  Type *parse_var_defn(ParseContext &ctx, long &flags, Decl *vararg, Sema &sema)
  {
    switch (ctx.tok.type)
    {
      case Token::kw_var:
        break;

      case Token::kw_let:
        flags |= VarDecl::Const;
        break;

      case Token::kw_const:
        flags |= VarDecl::Literal;
        break;

      case Token::kw_static:
        flags |= VarDecl::Static;
        break;

      default:
        assert(false);
    }

    ctx.consume_token();

    if (flags & VarDecl::Static)
    {
      while (ctx.tok.text == "thread_local" || ctx.tok.text == "cache_aligned" || ctx.tok.text == "page_aligned")
      {
        if (ctx.tok.text == "thread_local")
          flags |= VarDecl::ThreadLocal;

        if (ctx.tok.text == "cache_aligned")
          flags |= VarDecl::CacheAligned;

        if (ctx.tok.text == "page_aligned")
          flags |= VarDecl::PageAligned;

        ctx.consume_token();
      }
    }

    auto type = sema.make_typearg(vararg);

    auto kw_mut = ctx.try_consume_token(Token::kw_mut);
    auto kw_const = ctx.try_consume_token(Token::kw_const) || (flags & VarDecl::Const);

    if (kw_mut && kw_const)
      ctx.diag.warn("mut has no effect when const", ctx.text, ctx.tok.loc);

    if (ctx.try_consume_token(Token::amp))
    {
      if (flags & VarDecl::Literal)
        ctx.diag.error("literal cannot be a reference", ctx.text, ctx.tok.loc);

      if (!kw_mut || kw_const)
        type = sema.make_const(type);

      type = sema.make_reference(type);
    }

    else if (ctx.try_consume_token(Token::ampamp))
    {
      if (kw_mut || kw_const)
        ctx.diag.warn("invalid qualifiers", ctx.text, ctx.tok.loc);

      type = sema.make_reference(sema.make_qualarg(type));
    }

    if (kw_const)
      flags |= VarDecl::Const;

    return type;
  }

  //|///////////////////// parse_var_bindings_list //////////////////////////
  vector<Decl*> parse_var_bindings_list(ParseContext &ctx, long flags, Sema &sema)
  {
    vector<Decl*> bindings;

    while (ctx.tok != Token::r_paren && ctx.tok != Token::semi && ctx.tok != Token::eof)
    {
      auto var = sema.var_declaration(ctx.tok.loc);

      auto loc = ctx.tok.loc;

      var->flags = flags & VarDecl::Literal;

      var->type = sema.make_reference(sema.make_qualarg(sema.make_typearg(sema.make_typearg(Ident::kw_var, ctx.tok.loc))));

      auto name = Ident::make_index_ident(bindings.size());

      switch (ctx.tok.type)
      {
        case Token::period:
          ctx.try_consume_token(Token::period);
          var->name = parse_ident(ctx, IdentUsage::VarName, sema);
          name = var->name;
          break;

        case Token::identifier:
          var->name = parse_ident(ctx, IdentUsage::VarName, sema);
          break;

        default:
          break;
      }

      if (ctx.try_consume_token(Token::l_paren))
      {
        var->pattern = sema.tuple_pattern(parse_var_bindings_list(ctx, flags, sema), loc);

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          break;
        }
      }

      if (ctx.try_consume_token(Token::colon))
      {
        if (!ctx.try_consume_token(Token::period))
          ctx.diag.error("expected period", ctx.text, ctx.tok.loc);

        name = parse_ident(ctx, IdentUsage::ScopedName, sema);
      }

      var->value = sema.make_declref_expression(sema.make_declref(name, loc), loc);

      bindings.push_back(var);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return bindings;
  }

  //|///////////////////// parse_typearg_list ///////////////////////////////
  vector<Type*> parse_typearg_list(ParseContext &ctx, Sema &sema)
  {
    vector<Type*> args;

    while (ctx.tok != Token::greater && ctx.tok != Token::r_paren && ctx.tok != Token::eof)
    {
      if (ctx.tok == Token::identifier && ctx.token(1) == Token::colon)
        break;

      auto type = parse_type_ex(ctx, sema);

      if (!type)
        break;

      if (ctx.try_consume_token(Token::ellipsis))
        type = sema.make_unpack(type);

      args.push_back(type);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return args;
  }

  //|///////////////////// parse_named_typearg_list //////////////////////
  map<Ident*, Type*> parse_named_typearg_list(ParseContext &ctx, Sema &sema)
  {
    map<Ident*, Type*> args;

    while (ctx.tok != Token::greater && ctx.tok != Token::eof)
    {
      if (ctx.tok != Token::identifier || ctx.token(1) != Token::colon)
        break;

      auto name = parse_ident(ctx, IdentUsage::VarName, sema);

      ctx.consume_token(Token::colon);

      auto type = parse_type_ex(ctx, sema);

      if (!type)
        break;

      args.emplace(name, type);

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

      arg->name = parse_ident(ctx, IdentUsage::VarName, sema);

      if (ctx.try_consume_token(Token::equal))
      {
        arg->defult = parse_type_ex(ctx, sema);
      }

      else if (ctx.try_consume_token(Token::l_paren))
      {
        arg->flags |= TypeArgDecl::SplitFn;

        args.push_back(arg);

        arg = sema.typearg_declaration(ctx.tok.loc);

        arg->name = parse_ident(ctx, IdentUsage::VarName, sema);

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          break;
        }
      }

      else if (ctx.try_consume_token(Token::l_square))
      {
        arg->flags |= TypeArgDecl::SplitArray;

        args.push_back(arg);

        arg = sema.typearg_declaration(ctx.tok.loc);

        arg->name = parse_ident(ctx, IdentUsage::VarName, sema);

        if (!ctx.try_consume_token(Token::r_square))
        {
          ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
          break;
        }
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
      if (ctx.tok == Token::identifier && (ctx.token(1) == Token::colon || (ctx.token(1) == Token::question && ctx.token(2) == Token::colon)))
        break;

      auto expr = parse_expression(ctx, sema);

      if (!expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        break;
      }

      if (expr->kind() == Expr::ExprRef)
      {
        auto ref = expr_cast<ExprRefExpr>(expr);

        if (ref->expr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(ref->expr)->op() == UnaryOpExpr::Unpack)
        {
          expr = ref->expr;
          ref->expr = expr_cast<UnaryOpExpr>(ref->expr)->subexpr;
          expr_cast<UnaryOpExpr>(expr)->subexpr = ref;
        }
      }

      if (expr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr)->op() == UnaryOpExpr::Fwd)
      {
        auto fwd = expr_cast<UnaryOpExpr>(expr);

        if (fwd->subexpr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(fwd->subexpr)->op() == UnaryOpExpr::Unpack)
        {
          expr = fwd->subexpr;
          fwd->subexpr = expr_cast<UnaryOpExpr>(fwd->subexpr)->subexpr;
          expr_cast<UnaryOpExpr>(expr)->subexpr = fwd;
        }
      }

      exprs.push_back(expr);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return exprs;
  }

  //|///////////////////// parse_named_expression_list //////////////////////
  map<Ident*, Expr*> parse_named_expression_list(ParseContext &ctx, Sema &sema)
  {
    map<Ident*, Expr*> exprs;

    while (ctx.tok != Token::r_paren && ctx.tok != Token::eof)
    {
      if (ctx.tok != Token::identifier || !(ctx.token(1) == Token::colon || (ctx.token(1) == Token::question && ctx.token(2) == Token::colon)))
        break;

      auto name = parse_ident(ctx, IdentUsage::VarName, sema);

      if (ctx.try_consume_token(Token::question))
        name = Ident::from(name->str() + "?");

      ctx.consume_token(Token::colon);

      auto expr = parse_expression(ctx, sema);

      if (!expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        break;
      }

      exprs.emplace(name, expr);

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

      if (is_pointference_type(parm->type) && is_function_type(remove_const_type(remove_pointference_type(parm->type))))
      {
        parm->name = ctx.fname;

        if (ctx.tok == Token::identifier || ctx.tok == Token::dollar)
          break;
      }

      if (ctx.tok == Token::identifier || ctx.tok == Token::dollar)
      {
        parm->name = parse_ident(ctx, IdentUsage::VarName, sema);
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

        auto var = sema.var_declaration(stmt->loc());

        var->type = parse_var_defn(ctx, var->flags, sema.make_typearg(Ident::kw_var, ctx.tok.loc), sema);

        auto loc = ctx.tok.loc;

        if (ctx.tok != Token::l_paren)
        {
          var->name = parse_ident(ctx, IdentUsage::VarName, sema);
        }

        if (ctx.try_consume_token(Token::l_paren))
        {
          var->pattern = sema.tuple_pattern(parse_var_bindings_list(ctx, var->flags, sema), loc);

          if (!ctx.try_consume_token(Token::r_paren))
          {
            ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
            break;
          }
        }

        if (ctx.tok != Token::colon && ctx.tok != Token::equal)
        {
          ctx.diag.error("expected assignment", ctx.text, ctx.tok.loc);
          break;
        }

        if (ctx.tok == Token::colon)
          var->flags |= VarDecl::Range;

        ctx.consume_token();

        var->value = parse_expression(ctx, sema);

        if (!var->value)
        {
          ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
          break;
        }

        stmt->decl = var;

        stmts.push_back(stmt);
      }
      else
      {
        auto stmt = sema.expression_statement(ctx.tok.loc);

        stmt->expr = parse_expression(ctx, sema);

        if (!stmt->expr)
        {
          ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
          break;
        }

        stmts.push_back(stmt);
      }

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return stmts;
  }

  //|///////////////////// parse_captures_list //////////////////////////////
  vector<Decl*> parse_captures_list(ParseContext &ctx, Sema &sema)
  {
    vector<Decl*> captures;

    while (ctx.tok != Token::r_square && ctx.tok != Token::semi && ctx.tok != Token::eof)
    {
      auto var = sema.capture_declaration(ctx.tok.loc);

      var->arg = sema.make_typearg(Ident::from("_" + to_string(captures.size() + 1)), ctx.tok.loc);

      if (ctx.tok == Token::kw_var)
      {
        var->type = parse_var_defn(ctx, var->flags, var->arg, sema);

        var->name = parse_ident(ctx, IdentUsage::VarName, sema);

        if (!ctx.try_consume_token(Token::equal))
        {
          ctx.diag.error("expected assignment", ctx.text, ctx.tok.loc);
          break;
        }

        var->value = parse_expression(ctx, sema);

        if (!var->value)
        {
          ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
          break;
        }
      }
      else
      {
        auto loc = ctx.tok.loc;

        var->name = parse_ident(ctx, IdentUsage::VarName, sema);

        var->type = sema.make_reference(sema.make_qualarg(sema.make_typearg(var->arg)));

        var->value = sema.make_declref_expression(sema.make_declref(var->name, loc), loc);
      }

      captures.push_back(var);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    return captures;
  }

  //|///////////////////// parse_qualified_name /////////////////////////////
  Decl *parse_qualified_name(ParseContext &ctx, Sema &sema)
  {
    vector<Decl*> decls;

    auto loc = ctx.tok.loc;

    if (ctx.try_consume_token(Token::coloncolon))
    {
      decls.push_back(sema.make_declref(Ident::op_scope, loc));
    }

    if (ctx.try_consume_token(Token::kw_typeof))
    {
      auto loc = ctx.tok.loc;

      if (!ctx.try_consume_token(Token::l_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      auto expr = parse_expression(ctx, sema);

      if (!expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      decls.push_back(sema.make_decltype(expr, loc));

      if (!ctx.try_consume_token(Token::coloncolon))
        return decls.back();
    }

    while (true)
    {
      auto loc = ctx.tok.loc;
      auto name = parse_ident(ctx, IdentUsage::ScopedName, sema);

      auto declref = sema.make_declref(name, loc);

      if ((ctx.tok == Token::coloncolon && ctx.token(1) == Token::less) || (ctx.tok == Token::less && !std::isspace(ctx.tok.text.data()[-1])))
      {
        if (ctx.tok == Token::coloncolon)
          ctx.consume_token();

        ctx.consume_token(Token::less);

        declref->args = parse_typearg_list(ctx, sema);
        declref->namedargs = parse_named_typearg_list(ctx, sema);
        declref->argless = false;

        if (ctx.tok != Token::greater && ctx.tok != Token::greatergreater)
        {
          ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
          return nullptr;
        }

        if (ctx.tok == Token::greatergreater)
          ctx.tok.type = Token::greater;
        else
          ctx.consume_token();
      }

      decls.push_back(declref);

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
    auto text = std::string();

    while (ctx.tok == Token::string_literal)
    {
      text += unescape(ctx.tok.text.substr(1, ctx.tok.text.length()-2));

      ctx.consume_token();
    }

    return sema.make_string_literal(text, loc);
  }

  //|///////////////////// parse_array_literal //////////////////////////////
  Expr *parse_array_literal(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::l_square);

    Type *coercedtype = nullptr;

    if (ctx.try_consume_token(Token::less))
    {
      coercedtype = parse_type(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      if (!ctx.try_consume_token(Token::colon))
      {
        ctx.diag.error("expected colon", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    auto elements = parse_expression_list(ctx, sema);

    if (ctx.tok == Token::identifier && ctx.token(1) == Token::colon)
      elements.push_back(parse_expression(ctx, sema));

    auto size = sema.make_numeric_literal(+1, elements.size(), loc);

    if (ctx.try_consume_token(Token::semi))
    {
      if (elements.size() != 1)
      {
        ctx.diag.error("expected single repeat value", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      size = parse_expression(ctx, sema);

      if (!size)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (!ctx.try_consume_token(Token::r_square))
    {
      ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    return sema.make_array_literal(coercedtype, elements, sema.make_typelit(size), loc);
  }

  //|///////////////////// parse_type ///////////////////////////////////////
  Type *parse_type(ParseContext &ctx, Sema &sema)
  {
    Type *type = nullptr;

    auto outer_const = ctx.try_consume_token(Token::kw_const);

    switch (ctx.tok.type)
    {
      case Token::kw_fn: {
        ctx.consume_token(Token::kw_fn);

        if (!ctx.try_consume_token(Token::l_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          return nullptr;
        }

        bool pointer = ctx.try_consume_token(Token::star);
        bool reference = !pointer && ctx.try_consume_token(Token::amp);

        if (pointer || reference)
        {
          if (ctx.tok == Token::identifier || ctx.tok == Token::dollar)
          {
            ctx.fname = parse_ident(ctx, IdentUsage::VarName, sema);
          }

          if (!ctx.try_consume_token(Token::r_paren))
          {
            ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
            return nullptr;
          }

          if (!ctx.try_consume_token(Token::l_paren))
          {
            ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
            return nullptr;
          }
        }

        auto parms = parse_typearg_list(ctx, sema);

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          return nullptr;
        }

        auto throwtype = Builtin::type(Builtin::Type_Void);

        if (ctx.try_consume_token(Token::kw_throws))
        {
          if (!ctx.try_consume_token(Token::l_paren))
          {
            ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
            return nullptr;
          }

          throwtype = parse_type(ctx, sema);

          if (!ctx.try_consume_token(Token::r_paren))
          {
            ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
            return nullptr;
          }
        }

        auto returntype = Builtin::type(Builtin::Type_Void);

        if (ctx.try_consume_token(Token::arrow))
        {
          returntype = parse_type(ctx, sema);

          if (!returntype)
          {
            ctx.diag.error("expected requires type", ctx.text, ctx.tok.loc);
            return nullptr;
          }
        }

        type = sema.make_fntype(returntype, sema.make_tuple(parms), throwtype);

        if (pointer)
          type = sema.make_pointer(sema.make_const(type));

        if (reference)
          type = sema.make_reference(sema.make_const(type));

        break;
      }

      case Token::l_paren: {
        ctx.consume_token(Token::l_paren);

        type = sema.make_tuple(parse_typearg_list(ctx, sema));

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          return nullptr;
        }

        break;
      }

      default: {

        auto name = parse_qualified_name(ctx, sema);

        if (!name)
          return nullptr;

        type = sema.make_typeref(name);
      }
    }

    while (ctx.tok == Token::kw_mut || ctx.tok == Token::kw_const || ctx.tok == Token::star || ctx.tok == Token::amp || ctx.tok == Token::ampamp || ctx.tok == Token::l_square)
    {
      auto kw_mut = ctx.try_consume_token(Token::kw_mut);
      auto kw_const = ctx.try_consume_token(Token::kw_const);

      if (kw_mut && kw_const)
        ctx.diag.warn("mut has no effect when const", ctx.text, ctx.tok.loc);

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
          ctx.diag.warn("invalid qualifiers", ctx.text, ctx.tok.loc);

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
//        return nullptr;
//      }

//      if (!ctx.try_consume_token(Token::semi))
//      {
//        ctx.diag.error("expected semi after type expression", ctx.text, ctx.tok.loc);
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
      for (int indent = 0; tok != Token::eof; )
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
      switch (tok.type)
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
        case Token::arrow:
        case Token::kw_true:
        case Token::kw_false:
        case Token::kw_cast:
        case Token::kw_sizeof:
        case Token::kw_alignof:
        case Token::kw_throws:
        case Token::char_constant:
        case Token::numeric_constant:
        case Token::string_literal:
        case Token::dollar:
          maybe = true;
          leftid = false;
          break;

        case Token::star:
        case Token::amp:
        case Token::ampamp:
          lexcursor = lex(ctx.text, lexcursor, tok);
          if (tok == Token::identifier || tok == Token::coloncolon)
            maybe = true;
          leftid = false;
          continue;

        case Token::identifier:
        case Token::coloncolon:
          leftid = true;
          break;

        case Token::l_paren:
          comma = false;
          switch (lex(ctx.text, lexcursor, tok); tok.type)
          {
            case Token::r_paren:
              comma = true;
              break;

            case Token::char_constant:
            case Token::numeric_constant:
            case Token::string_literal:
            case Token::kw_true:
            case Token::kw_false:
              maybe = true;
              break;

            default:
              break;
          }

          tok.type = Token::l_paren;

          skip_bracketed();

          if (leftid || !comma)
            maybe = true;
          break;

        case Token::l_square:
          for (int indent = 0; tok != Token::eof; )
          {
            if (tok == Token::l_paren)
              skip_bracketed();

            if (tok == Token::l_square)
              indent += 1;

            if (tok == Token::r_square)
              indent -= 1;

            if (indent <= 0)
              break;

            lexcursor = lex(ctx.text, lexcursor, tok);
          }
          if (!leftid)
            maybe = true;
          break;

        case Token::less: {
          int indent = 0;
          while (tok != Token::eof)
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

          if (indent < 0)
            continue;

          break;
        }

        case Token::kw_requires:
          if (auto expr = parse_expression(ctx, sema))
            return sema.make_typelit(expr);

          [[fallthrough]];

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

    if (!expr || ctx.try_consume_token(Token::comma) || (expr->kind() == Expr::UnaryOp && expr_cast<UnaryOpExpr>(expr)->op() == UnaryOpExpr::Unpack && expr_cast<UnaryOpExpr>(expr)->subexpr->kind() != Expr::Paren))
    {
      vector<Expr*> fields;

      if (expr)
        fields.push_back(expr);

      while (ctx.tok != Token::r_paren && ctx.tok != Token::eof)
      {
        auto expr = parse_expression(ctx, sema);

        if (!expr)
        {
          ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
          break;
        }

        fields.push_back(expr);

        if (!ctx.try_consume_token(Token::comma))
          break;
      }

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      return sema.make_tuple_literal(fields, loc);
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
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
      if (ctx.tok.text.data() != text.data() + text.length())
        ctx.diag.warn("extra characters within numeric literal", ctx.text, op.loc);

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

    if (!name)
      return nullptr;

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto parms = parse_expression_list(ctx, sema);
      auto namedparms = parse_named_expression_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
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
        return nullptr;
      }

      if (ctx.try_consume_token(Token::l_paren))
      {
        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
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
        return nullptr;
      }

      if (ctx.try_consume_token(Token::l_paren))
      {
        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          return nullptr;
        }
      }

      return sema.make_alignof_expression(type, loc);
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto decl = parse_qualified_name(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      return sema.make_alignof_expression(decl, loc);
    }

    return nullptr;
  }

  //|///////////////////// parse_offsetof ///////////////////////////////////
  Expr *parse_offsetof(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::kw_offsetof);

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    auto decl = parse_qualified_name(ctx, sema);

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    return sema.make_offsetof_expression(decl, loc);
  }

  //|///////////////////// parse_instanceof /////////////////////////////////
  Expr *parse_instanceof(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::kw_instanceof);

    if (!ctx.try_consume_token(Token::less))
    {
      ctx.diag.error("expected less", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    auto type = parse_type(ctx, sema);

    if (!ctx.try_consume_token(Token::comma))
    {
      ctx.diag.error("expected comma", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    auto instance = parse_type(ctx, sema);

    if (!ctx.try_consume_token(Token::greater))
    {
      ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    return sema.make_instanceof_expression(type, instance, loc);
  }

  //|///////////////////// parse_throws /////////////////////////////////////
  Expr *parse_throws(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::kw_throws);

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    auto expr = parse_expression(ctx, sema);

    if (!expr)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    return sema.make_throws_expression(expr, loc);
  }

  //|///////////////////// parse_typeid /////////////////////////////////////
  Expr *parse_typeid(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::dollar);

    auto decl = parse_qualified_name(ctx, sema);

    if (!decl)
      return nullptr;

    return sema.make_typeid_expression(decl, loc);
  }

  //|///////////////////// parse_extern /////////////////////////////////////
  Expr *parse_extern(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::kw_extern);

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    Expr *expr = nullptr;

    if (ctx.tok == Token::identifier)
    {
      expr = sema.make_string_literal(ctx.tok.text, ctx.tok.loc);

      ctx.consume_token(Token::identifier);
    }
    else
    {
      expr = parse_expression(ctx, sema);

      if (!expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    return sema.make_unary_expression(UnaryOpExpr::Extern, expr, loc);
  }

  //|///////////////////// parse_cast ///////////////////////////////////////
  Expr *parse_cast(ParseContext &ctx, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::kw_cast);

    Type *type = nullptr;

    if (ctx.try_consume_token(Token::less))
    {
      auto qualcast = ctx.try_consume_token(Token::ampamp);

      type = parse_type(ctx, sema);

      if (qualcast)
        type = sema.make_qualarg(type);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    Expr *expr = nullptr;

    if (ctx.try_consume_token(Token::l_paren))
    {
      expr = parse_expression(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
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
      return nullptr;
    }

    auto type = parse_type(ctx, sema);

    if (!ctx.try_consume_token(Token::greater))
    {
      ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    auto address = parse_expression(ctx, sema);

    if (!address)
    {
      ctx.diag.error("expected address parameter", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto parms = parse_expression_list(ctx, sema);
      auto namedparms = parse_named_expression_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      return sema.make_new_expression(type, address, parms, namedparms, loc);
    }

    return sema.make_new_expression(type, address, loc);
  }

  //|///////////////////// parse_member /////////////////////////////////////
  Expr *parse_member(ParseContext &ctx, Expr *base, Sema &sema)
  {
    ctx.consume_token();

    auto loc = ctx.tok.loc;
    auto name = parse_qualified_name(ctx, sema);

    if (!name)
      return nullptr;

    if (ctx.try_consume_token(Token::l_paren))
    {
      auto parms = parse_expression_list(ctx, sema);
      auto namedparms = parse_named_expression_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      return sema.make_call_expression(base, name, parms, namedparms, loc);
    }

    return sema.make_declref_expression(base, name, loc);
  }

  //|///////////////////// parse_subscript //////////////////////////////////
  Expr *parse_subscript(ParseContext &ctx, Expr *base, Sema &sema)
  {
    auto loc = ctx.tok.loc;

    ctx.consume_token(Token::l_square);

    auto name = sema.make_declref(Ident::op_index, loc);
    auto parms = parse_expression_list(ctx, sema);
    auto namedparms = parse_named_expression_list(ctx, sema);

    if (!ctx.try_consume_token(Token::r_square))
    {
      ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    return sema.make_call_expression(base, name, parms, namedparms, loc);
  }

  //|///////////////////// parse_call ///////////////////////////////////////
  Expr *parse_call(ParseContext &ctx, Expr *base, Sema &sema)
  {
    ctx.consume_token(Token::l_paren);

    auto loc = ctx.tok.loc;
    auto name = sema.make_declref(Ident::op_call, loc);
    auto parms = parse_expression_list(ctx, sema);
    auto namedparms = parse_named_expression_list(ctx, sema);

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    return sema.make_call_expression(base, name, parms, namedparms, loc);
  }

  //|///////////////////// parse_requires ///////////////////////////////////
  Expr *parse_requires(ParseContext &ctx, Sema &sema)
  {
    auto fn = sema.function_declaration(ctx.tok.loc);

    ctx.consume_token(Token::kw_requires);

    fn->flags |= FunctionDecl::RequiresDecl;

    if (ctx.try_consume_token(Token::l_paren))
    {
      fn->parms = parse_parms_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (ctx.try_consume_token(Token::arrow))
    {
      fn->returntype = parse_type(ctx, sema);

      if (!fn->returntype)
      {
        ctx.diag.error("expected requires type", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (ctx.tok != Token::l_brace)
    {
      ctx.diag.error("expected requires body", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    fn->body = parse_compound_statement(ctx, sema);

    return sema.make_requires_expression(fn, fn->loc());
  }

  //|///////////////////// parse_match //////////////////////////////////////
  Expr *parse_match(ParseContext &ctx, Sema &sema)
  {
    auto fn = sema.function_declaration(ctx.tok.loc);

    ctx.consume_token(Token::identifier);

    fn->flags |= FunctionDecl::MatchDecl;

    if (ctx.try_consume_token(Token::l_paren))
    {
      fn->parms = parse_parms_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (ctx.tok != Token::l_brace)
    {
      ctx.diag.error("expected match body", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    fn->body = parse_compound_statement(ctx, sema);

    return sema.make_match_expression(fn, fn->loc());
  }

  //|///////////////////// parse_where //////////////////////////////////////
  Expr *parse_where(ParseContext &ctx, Sema &sema)
  {
    ctx.consume_token(Token::identifier);

    auto where = parse_expression(ctx, sema);

    if (!where)
    {
      ctx.diag.error("expected where condition", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    return where;
  }

  //|///////////////////// parse_lambda /////////////////////////////////////
  Expr *parse_lambda(ParseContext &ctx, Sema &sema)
  {
    auto lambda = sema.lambda_declaration(ctx.tok.loc);

    auto fn = sema.function_declaration(lambda->loc());

    ctx.consume_token(Token::kw_fn);

    fn->flags |= FunctionDecl::Public;
    fn->flags |= FunctionDecl::LambdaDecl;

    fn->name = Ident::op_call;

    if (ctx.tok == Token::identifier || ctx.tok == Token::dollar)
    {
      lambda->name = parse_ident(ctx, IdentUsage::TagName, sema);
    }

    if (ctx.try_consume_token(Token::less))
    {
      fn->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (ctx.try_consume_token(Token::l_square))
    {
      lambda->captures = parse_captures_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_square))
      {
        ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      fn->parms = parse_parms_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (ctx.try_consume_token(Token::kw_throws))
    {
      if (ctx.try_consume_token(Token::l_paren))
      {
        fn->throws = parse_type_ex(ctx, sema);

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          return nullptr;
        }
      }
      else
      {
        fn->throws = sema.make_typelit(sema.make_bool_literal(true, ctx.tok.loc));
      }
    }

    if (ctx.try_consume_token(Token::arrow))
    {
      fn->returntype = parse_type(ctx, sema);

      if (!fn->returntype)
      {
        ctx.diag.error("expected return type", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "match")
    {
      fn->match = parse_match(ctx, sema);
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "where")
    {
      fn->where = parse_where(ctx, sema);
    }

    if (ctx.tok != Token::l_brace)
    {
      ctx.diag.error("expected function body", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    fn->body = parse_compound_statement(ctx, sema);

    lambda->fn = fn;
    lambda->decls.push_back(fn);

    return sema.make_lambda_expression(lambda, lambda->loc());
  }

  //|///////////////////// parse_lambda /////////////////////////////////////
  Expr *parse_quick_lambda(ParseContext &ctx, Sema &sema)
  {
    auto lambda = sema.lambda_declaration(ctx.tok.loc);

    auto fn = sema.function_declaration(lambda->loc());

    if (ctx.tok != Token::pipepipe)
      ctx.consume_token(Token::pipe);

    if (ctx.tok == Token::pipepipe)
      ctx.tok.type = Token::pipe;

    fn->flags |= FunctionDecl::Public;
    fn->flags |= FunctionDecl::LambdaDecl;

    fn->name = Ident::op_call;

    while (ctx.tok != Token::pipe && ctx.tok != Token::eof)
    {
      auto parm = sema.parm_declaration(ctx.tok.loc);

      parm->name = parse_ident(ctx, IdentUsage::VarName, sema);

      parm->type = sema.make_reference(sema.make_qualarg(sema.make_typeref(sema.make_declref(Ident::kw_var, ctx.tok.loc))));

      fn->parms.push_back(parm);

      if (!ctx.try_consume_token(Token::comma))
        break;
    }

    if (!ctx.try_consume_token(Token::pipe))
    {
      ctx.diag.error("expected pipe", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    if (ctx.tok != Token::l_square)
    {
      lambda->flags |= LambdaDecl::Capture;
    }

    if (ctx.try_consume_token(Token::l_square))
    {
      lambda->captures = parse_captures_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_square))
      {
        ctx.diag.error("expected bracket", ctx.text, ctx.tok.loc);
        return nullptr;
      }
    }

    if (ctx.tok == Token::arrow || ctx.tok == Token::l_brace)
    {
      if (ctx.try_consume_token(Token::arrow))
      {
        fn->returntype = parse_type(ctx, sema);

        if (!fn->returntype)
        {
          ctx.diag.error("expected return type", ctx.text, ctx.tok.loc);
          return nullptr;
        }
      }

      if (ctx.tok != Token::l_brace)
      {
        ctx.diag.error("expected function body", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      fn->body = parse_compound_statement(ctx, sema);
    }
    else
    {
      auto compound = sema.compound_statement(ctx.tok.loc);

      auto retrn = sema.return_statement(ctx.tok.loc);

      retrn->expr = parse_expression(ctx, sema);

      if (!retrn->expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        return nullptr;
      }

      compound->stmts.push_back(retrn);

      fn->body = compound;
    }

    lambda->fn = fn;
    lambda->decls.push_back(fn);

    return sema.make_lambda_expression(lambda, lambda->loc());
  }

  //|///////////////////// parse_expression_head ////////////////////////////
  Expr *parse_expression_head(ParseContext &ctx, Token op, Expr *lhs, Sema &sema)
  {
    if (!lhs)
      return nullptr;

    return sema.make_unary_expression(unaryopcode(op), lhs, op.loc);
  }

  //|///////////////////// parse_expression_post ////////////////////////////
  Expr *parse_expression_post(ParseContext &ctx, Expr *lhs, Sema &sema)
  {
    if (!lhs)
      return nullptr;

    auto op = ctx.tok;

    switch (op.type)
    {
      case Token::arrow:
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

      case Token::questionexclaim:
        ctx.consume_token();
        return parse_expression_post(ctx, sema.make_unary_expression(UnaryOpExpr::Unwrap, lhs, op.loc), sema);

      case Token::ellipsis:
        ctx.consume_token();
        return sema.make_unary_expression(UnaryOpExpr::Unpack, lhs, op.loc);

      default:
        return lhs;
    }
  }

  //|///////////////////// parse_expression /////////////////////////////////
  Expr *parse_expression_left(ParseContext &ctx, Sema &sema)
  {
    auto op = ctx.tok;

    if (auto nexttok = ctx.token(1); nexttok == Token::coloncolon)
    {
      return parse_expression_post(ctx, parse_callee(ctx, sema), sema);
    }

    if (op.type == Token::amp)
    {
      switch (auto nexttok = ctx.token(1); nexttok.type)
      {
        case Token::kw_mut:
          ctx.consume_token(Token::amp);
          ctx.consume_token(Token::kw_mut);
          return sema.make_ref_expression(parse_expression_left(ctx, sema), ExprRefExpr::Mut, op.loc);

        case Token::kw_move:
          ctx.consume_token(Token::amp);
          ctx.consume_token(Token::kw_move);
          return sema.make_ref_expression(parse_expression_left(ctx, sema), ExprRefExpr::Mut | ExprRefExpr::Move, op.loc);

        default:
          break;
      }
    }

    switch (op.type)
    {
      case Token::l_paren:
        return parse_expression_post(ctx, parse_paren(ctx, sema), sema);

      case Token::plus:
        return parse_expression_post(ctx, parse_unary_plus(ctx, sema), sema);

      case Token::minus:
        return parse_expression_post(ctx, parse_unary_minus(ctx, sema), sema);

      case Token::kw_true:
      case Token::kw_false:
        return parse_expression_post(ctx, parse_bool_literal(ctx, sema), sema);

      case Token::char_constant:
        return parse_expression_post(ctx, parse_char_literal(ctx, sema), sema);

      case Token::numeric_constant:
        return parse_expression_post(ctx, parse_numeric_literal(ctx, sema), sema);

      case Token::string_literal:
        return parse_expression_post(ctx, parse_string_literal(ctx, sema), sema);

      case Token::l_square:
        return parse_expression_post(ctx, parse_array_literal(ctx, sema), sema);

      case Token::kw_void:
      case Token::kw_null:
      case Token::kw_move:
        return parse_expression_post(ctx, parse_callee(ctx, sema), sema);

      case Token::kw_sizeof:
        return parse_sizeof(ctx, sema);

      case Token::kw_alignof:
        return parse_alignof(ctx, sema);

      case Token::kw_offsetof:
        return parse_offsetof(ctx, sema);

      case Token::kw_instanceof:
        return parse_instanceof(ctx, sema);

      case Token::kw_throws:
        return parse_throws(ctx, sema);

      case Token::kw_cast:
        return parse_expression_post(ctx, parse_cast(ctx, sema), sema);

      case Token::kw_new:
        return parse_expression_post(ctx, parse_new(ctx, sema), sema);

      case Token::kw_requires:
        return parse_requires(ctx, sema);

      case Token::kw_fn:
        return parse_expression_post(ctx, parse_lambda(ctx, sema), sema);

      case Token::pipe:
      case Token::pipepipe:
        return parse_expression_post(ctx, parse_quick_lambda(ctx, sema), sema);

      case Token::kw_extern:
        return parse_extern(ctx, sema);

      case Token::dollar:
        if (ctx.token(1) != Token::l_paren)
          return parse_typeid(ctx, sema);
        [[fallthrough]];

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
      case Token::hash:
        ctx.consume_token();
        return parse_expression_head(ctx, op, parse_expression_left(ctx, sema), sema);

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

        if (!middle)
        {
          ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
          return nullptr;
        }

        if (!ctx.try_consume_token(Token::colon))
        {
          ctx.diag.error("expected colon", ctx.text, ctx.tok.loc);
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

  //|///////////////////// parse_funciton_specifier /////////////////////////
  Decl *parse_funciton_specifier(ParseContext &ctx, Decl *fn, Sema &sema)
  {
    if (ctx.tok.text == "default")
      fn->flags |= FunctionDecl::Defaulted;

    else if (ctx.tok.text == "delete")
      fn->flags |= FunctionDecl::Deleted;

    else
      ctx.diag.error("unknown specifier", ctx.text, ctx.tok.loc);

    ctx.consume_token();

    return fn;
  }

  //|///////////////////// parse_run_declaration ////////////////////////////
  Decl *parse_run_declaration(ParseContext &ctx, Sema &sema)
  {
    auto run = sema.run_declaration(ctx.tok.loc);

    ctx.consume_token(Token::hash);

    auto fn = sema.function_declaration(ctx.tok.loc);

    fn->name = Ident::op_run;
    fn->flags |= FunctionDecl::RunDecl;

    fn->returntype = Builtin::type(Builtin::Type_Void);

    fn->body = parse_compound_statement(ctx, sema);

    run->fn = fn;

    return run;
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

    ifd->root = ifd;

    return ifd;

    resume:
      ctx.consume_til_resumable();
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

    elsed->root = ifd->root;

    return elsed;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_endif_declaration //////////////////////////
  IfDecl *parse_endif_declaration(ParseContext &ctx, IfDecl *ifd, Sema &sema)
  {
    ctx.consume_token(Token::hash);
    ctx.consume_token(Token::identifier);

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

    if (!ctx.try_consume_token(Token::identifier))
    {
      ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
      goto resume;
    }

    imprt->alias = Ident::from(name);

    while (ctx.try_consume_token(Token::period) || ctx.try_consume_token(Token::minus))
    {
      name = string_view(name.data(), name.length() + ctx.tok.text.length() + 1);

      if (!ctx.try_consume_token(Token::identifier))
      {
        ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (auto j = name.find('.'); j != name.npos)
    {
      if (name.substr(j+1) == imprt->alias->sv())
        name = imprt->alias->sv();
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "as")
    {
      ctx.consume_token(Token::identifier);

      imprt->alias = parse_ident(ctx, IdentUsage::TagName, sema);
    }

    if (ctx.try_consume_token(Token::colon))
    {
      while (ctx.tok != Token::semi && ctx.tok != Token::eof)
      {
        auto usein = sema.using_declaration(ctx.tok.loc);

        if (imprt->flags & Decl::Public)
          usein->flags |= Decl::Public;

        auto loc = ctx.tok.loc;
        auto name = parse_ident(ctx, IdentUsage::FunctionName, sema);

        usein->decl = sema.make_declref(name, loc);

        imprt->usings.push_back(usein);

        if (!ctx.try_consume_token(Token::comma))
          break;
      }
    }

    imprt->decl = sema.make_declref(Ident::from(name), loc);

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return imprt;

    resume:
      ctx.consume_til_resumable();
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

    if (!usein->decl)
    {
      ctx.diag.error("expected identifier", ctx.text, ctx.tok.loc);
      return nullptr;
    }

    if (usein->decl->kind() == Decl::TypeName)
      ctx.diag.error("invalid use of typename", ctx.text, ctx.tok.loc);

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return usein;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_typealias_declaration //////////////////////
  Decl *parse_typealias_declaration(ParseContext &ctx, Sema &sema)
  {
    auto alias = sema.alias_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      alias->flags |= Decl::Public;

    ctx.consume_token(Token::kw_using);

    alias->name = parse_ident(ctx, IdentUsage::TagName, sema);

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

    if (!alias->type)
    {
      ctx.diag.error("expected type", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return alias;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_var_declaration ////////////////////////////
  Decl *parse_var_declaration(ParseContext &ctx, Sema &sema)
  {
    auto var = sema.var_declaration(ctx.tok.loc);

    var->type = parse_var_defn(ctx, var->flags, sema.make_typearg(Ident::kw_var, ctx.tok.loc), sema);

    auto loc = ctx.tok.loc;

    if (ctx.tok != Token::l_paren)
    {
      var->name = parse_ident(ctx, IdentUsage::VarName, sema);
    }

    if (ctx.try_consume_token(Token::l_paren))
    {
      var->pattern = sema.tuple_pattern(parse_var_bindings_list(ctx, var->flags, sema), loc);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }
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
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_requires_declaration ///////////////////////
  Decl *parse_requires_declaration(ParseContext &ctx, Sema &sema)
  {
    auto reqires = sema.requires_declaration(ctx.tok.loc);

    auto fn = sema.function_declaration(ctx.tok.loc);

    ctx.consume_token(Token::kw_requires);

    fn->name = Ident::op_requires;
    fn->flags |= FunctionDecl::RequiresDecl;

    if (ctx.try_consume_token(Token::less))
    {
      fn->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.tok == Token::l_paren)
    {
      auto tok = ctx.tok;
      auto lexcursor = ctx.lexcursor;

      for (int indent = 0; tok != Token::eof; )
      {
        if (tok == Token::l_paren)
          indent += 1;

        if (tok == Token::r_paren)
          if (--indent <= 0)
            break;

        lexcursor = lex(ctx.text, lexcursor, tok);
      }

      lexcursor = lex(ctx.text, lexcursor, tok);

      if (tok == Token::arrow || tok == Token::l_brace)
      {
        ctx.consume_token(Token::l_paren);

        fn->parms = parse_parms_list(ctx, sema);

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          goto resume;
        }
      }
    }

    if (ctx.tok == Token::arrow || ctx.tok == Token::l_brace)
    {
      if (ctx.try_consume_token(Token::arrow))
      {
        reqires->requirestype = parse_type(ctx, sema);

        if (!reqires->requirestype)
        {
          ctx.diag.error("expected requires type", ctx.text, ctx.tok.loc);
          goto resume;
        }
      }

      if (ctx.tok != Token::l_brace)
      {
        reqires->flags |= RequiresDecl::Match;
      }

      if (ctx.tok == Token::l_brace)
      {
        reqires->flags |= RequiresDecl::Expression;

        fn->body = parse_compound_statement(ctx, sema);
      }
    }
    else
    {
      reqires->flags |= RequiresDecl::Condition;

      fn->returntype = Builtin::type(Builtin::Type_Bool);

      auto retrn = sema.return_statement(ctx.tok.loc);

      retrn->expr = parse_expression(ctx, sema);

      if (!retrn->expr)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        goto resume;
      }

      fn->body = retrn;
    }

    reqires->fn = fn;

    return reqires;

    resume:
      ctx.consume_til_resumable();
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

    fn->name = parse_ident(ctx, IdentUsage::VarName, sema);

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
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return fn;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_lambda_declaration /////////////////////////
  Decl *parse_lambda_declaration(ParseContext &ctx, Sema &sema)
  {
    auto var = sema.var_declaration(ctx.tok.loc);

    var->type = sema.make_typearg(sema.make_typearg(Ident::kw_var, ctx.tok.loc));

    var->value = parse_lambda(ctx, sema);

    if (!var->value)
      return nullptr;

    var->name = decl_cast<LambdaDecl>(expr_cast<LambdaExpr>(var->value)->decl)->name;

    if (!var->name)
    {
      ctx.diag.error("expected identifier", ctx.text, var->loc());
      goto resume;
    }

    return var;

    resume:
      ctx.consume_til_resumable();
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
        if (ctx.tok.text == "\"naked\"")
          abi = FunctionDecl::ExternNaked;

        if (ctx.tok.text == "\"win64\"")
          abi = FunctionDecl::ExternWin64;

        if (ctx.tok.text == "\"sysv64\"")
          abi = FunctionDecl::ExternSysv64;

        if (ctx.tok.text == "\"interrupt\"")
          abi = FunctionDecl::ExternInterrupt;

        ctx.consume_token(Token::string_literal);
      }

      fn->flags |= abi;
    }

    if (ctx.try_consume_token(Token::kw_const))
      fn->flags |= FunctionDecl::Const;

    if (ctx.try_consume_token(Token::kw_static))
      fn->flags |= FunctionDecl::Static;

    fn->attributes = std::move(ctx.attributes);

    if (!ctx.try_consume_token(Token::kw_fn))
      ctx.diag.error("expected function", ctx.text, ctx.tok.loc);

    auto name = parse_ident(ctx, IdentUsage::FunctionName, sema);

    if (ctx.try_consume_token(Token::equal))
      name = Ident::from(name->str() + "=");

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
        fn->throws = parse_type_ex(ctx, sema);

        if (!ctx.try_consume_token(Token::r_paren))
        {
          ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
          goto resume;
        }
      }
      else
      {
        fn->throws = sema.make_typelit(sema.make_bool_literal(true, ctx.tok.loc));
      }
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "override")
    {
      fn->flags |= FunctionDecl::Override;
      ctx.consume_token();
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
      parse_funciton_specifier(ctx, fn, sema);

      if (ctx.tok != Token::semi)
      {
        ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "match")
    {
      fn->match = parse_match(ctx, sema);
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "where")
    {
      fn->where = parse_where(ctx, sema);
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
    ctx.consume_til_resumable();
    return nullptr;
  }

  //|///////////////////// parse_initialiser_list ///////////////////////////
  vector<Decl*> parse_initialiser_list(ParseContext &ctx, Sema &sema)
  {
    vector<Decl*> inits;

    while (ctx.tok != Token::l_brace && ctx.tok != Token::eof)
    {
      auto init = sema.initialiser_declaration(ctx.tok.loc);

      init->name = parse_ident(ctx, IdentUsage::VarName, sema);

      if (!ctx.try_consume_token(Token::l_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        break;
      }

      init->parms = parse_expression_list(ctx, sema);
      init->namedparms = parse_named_expression_list(ctx, sema);

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        break;
      }

      inits.push_back(init);

      if (!ctx.try_consume_token(Token::comma))
        break;

      if (inits.size() == 1 && decl_cast<InitialiserDecl>(inits[0])->name == Ident::kw_this)
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

    if (ctx.try_consume_token(Token::kw_static))
      fn->flags |= FunctionDecl::Static;

    fn->attributes = std::move(ctx.attributes);

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
      parse_funciton_specifier(ctx, fn, sema);

      if (ctx.tok != Token::semi)
      {
        ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "match")
    {
      fn->match = parse_match(ctx, sema);
    }

    if (ctx.tok == Token::identifier && ctx.tok.text == "where")
    {
      fn->where = parse_where(ctx, sema);
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
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_destructor_declaration /////////////////////
  Decl *parse_destructor_declaration(ParseContext &ctx, Sema &sema)
  {
    auto fn = sema.function_declaration(ctx.tok.loc);

    fn->flags |= FunctionDecl::Destructor;

    if (ctx.try_consume_token(Token::kw_pub))
      fn->flags |= FunctionDecl::Public;

    fn->attributes = std::move(ctx.attributes);

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
      parse_funciton_specifier(ctx, fn, sema);

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
      ctx.consume_til_resumable();
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

    if (is_pointference_type(field->type) && is_function_type(remove_const_type(remove_pointference_type(field->type))))
      field->name = ctx.fname;
    else
      field->name = parse_ident(ctx, IdentUsage::VarName, sema);

    if (ctx.try_consume_token(Token::equal))
    {
      field->defult = parse_expression(ctx, sema);
    }

    if (!(ctx.try_consume_token(Token::semi) || ctx.try_consume_token(Token::comma)))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return field;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_struct_declaration /////////////////////////
  Decl *parse_struct_declaration(ParseContext &ctx, Sema &sema)
  {
    auto strct = sema.struct_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      strct->flags |= StructDecl::Public;

    strct->attributes = std::move(ctx.attributes);

    ctx.consume_token(Token::kw_struct);

    if (ctx.tok == Token::identifier || ctx.tok == Token::dollar)
    {
      strct->name = parse_ident(ctx, IdentUsage::TagName, sema);
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
      if (ctx.try_consume_token(Token::kw_pub))
        strct->flags |= TagDecl::PublicBase;

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
            case Token::dollar:
              break;

            default:
              goto unhandled;
          }
        }

        if (tok == Token::kw_static)
        {
          tok = ctx.token(nexttok++);
        }

        switch (tok.type)
        {
          case Token::kw_using:
            if (ctx.token(nexttok) == Token::identifier && (ctx.token(nexttok + 1) == Token::less || ctx.token(nexttok + 1) == Token::equal))
              tok.type = Token::pseudo_alias;
            break;

          case Token::kw_fn:
            if (ctx.token(nexttok) == Token::l_paren && (ctx.token(nexttok+1) == Token::star || ctx.token(nexttok+1) == Token::amp))
              tok.type = Token::pseudo_fnptr;
            break;

          default:
            break;
        }

        switch (tok.type)
        {
          case Token::semi:
            ctx.diag.warn("extra semi", ctx.text, tok.loc);
            ctx.consume_token(Token::semi);
            continue;

          case Token::kw_const:
            decl = parse_const_declaration(ctx, sema);
            break;

          case Token::kw_fn:
            decl = parse_function_declaration(ctx, sema);
            break;

          case Token::kw_struct:
            decl = parse_struct_declaration(ctx, sema);
            break;

          case Token::kw_union:
            decl = parse_union_declaration(ctx, sema);
            break;

          case Token::kw_vtable:
            decl = parse_vtable_declaration(ctx, sema);
            break;

          case Token::kw_concept:
            decl = parse_concept_declaration(ctx, sema);
            break;

          case Token::kw_enum:
            decl = parse_enum_declaration(ctx, sema);
            break;

          case Token::kw_import:
            decl = parse_import_declaration(ctx, sema);
            break;

          case Token::kw_using:
            decl = parse_using_declaration(ctx, sema);
            break;

          case Token::pseudo_alias:
            decl = parse_typealias_declaration(ctx, sema);
            break;

          case Token::kw_void:
          case Token::kw_null:
          case Token::kw_typeof:
          case Token::l_paren:
          case Token::identifier:
          case Token::coloncolon:
          case Token::pseudo_fnptr:
          case Token::dollar:
            if (strct->name == tok.text || tok.text == "this")
            {
              auto tok = ctx.tok;
              auto lexcursor = ctx.lexcursor;

              for (size_t i = nexttok; tok != Token::eof && i > 0; --i)
                lexcursor = lex(ctx.text, lexcursor, tok);

              if (tok == Token::less)
              {
                for (int indent = 0; tok != Token::eof; )
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
            switch (auto tok = ctx.token(nexttok); tok.type)
            {
              case Token::l_square:
                consume_attributes(ctx, sema);
                continue;

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

              case Token::identifier:
                if (tok.text != "end")
                  goto unhandled;
                if (conditionals_stack.empty())
                  goto unhandled;

                decl = parse_endif_declaration(ctx, conditionals_stack.back(), sema);

                conditionals_stack.pop_back();
                conditional = conditionals_stack.back();
                conditionals_stack.pop_back();
                break;

              case Token::l_brace:
                decl = parse_run_declaration(ctx, sema);
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
            ctx.consume_til_resumable();
        }

        if (!decl)
          continue;

        if (!ctx.attributes.empty())
          ctx.diag.error("unexpected attributes", ctx.text, tok.loc);

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
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_subject_declaration ////////////////////////
  Decl *parse_subject_declaration(ParseContext &ctx, Sema &sema)
  {
    auto field = sema.field_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      field->flags |= Decl::Public;

    field->name = parse_ident(ctx, IdentUsage::VarName, sema);

    if (ctx.try_consume_token(Token::l_paren))
    {
      field->type = parse_type(ctx, sema);

      if (!field->type)
      {
        ctx.diag.error("expected type", ctx.text, ctx.tok.loc);
        goto resume;
      }

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (!(ctx.try_consume_token(Token::semi) || ctx.try_consume_token(Token::comma)))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return field;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_union_declaration //////////////////////////
  Decl *parse_union_declaration(ParseContext &ctx, Sema &sema)
  {
    auto unnion = sema.union_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      unnion->flags |= StructDecl::Public;

    unnion->attributes = std::move(ctx.attributes);

    ctx.consume_token(Token::kw_union);

    if (ctx.tok == Token::identifier || ctx.tok == Token::dollar)
    {
      unnion->name = parse_ident(ctx, IdentUsage::TagName, sema);
    }

    if (ctx.try_consume_token(Token::less))
    {
      unnion->args = parse_args_list(ctx, sema);

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
            case Token::dollar:
              break;

            default:
              goto unhandled;
          }
        }

        if (tok == Token::kw_static)
        {
          tok = ctx.token(nexttok++);
        }

        switch (tok.type)
        {
          case Token::kw_using:
            if (ctx.token(nexttok) == Token::identifier && (ctx.token(nexttok + 1) == Token::less || ctx.token(nexttok + 1) == Token::equal))
              tok.type = Token::pseudo_alias;
            break;

          case Token::kw_fn:
            if (ctx.token(nexttok) == Token::l_paren && (ctx.token(nexttok+1) == Token::star || ctx.token(nexttok+1) == Token::amp))
              tok.type = Token::pseudo_fnptr;
            break;

          default:
            break;
        }

        switch (tok.type)
        {
          case Token::semi:
            ctx.diag.warn("extra semi", ctx.text, tok.loc);
            ctx.consume_token(Token::semi);
            continue;

          case Token::kw_const:
            decl = parse_const_declaration(ctx, sema);
            break;

          case Token::kw_fn:
            decl = parse_function_declaration(ctx, sema);
            break;

          case Token::kw_struct:
            decl = parse_struct_declaration(ctx, sema);
            break;

          case Token::kw_union:
            decl = parse_union_declaration(ctx, sema);
            break;

          case Token::kw_vtable:
            decl = parse_vtable_declaration(ctx, sema);
            break;

          case Token::kw_concept:
            decl = parse_concept_declaration(ctx, sema);
            break;

          case Token::kw_enum:
            decl = parse_enum_declaration(ctx, sema);
            break;

          case Token::kw_import:
            decl = parse_import_declaration(ctx, sema);
            break;

          case Token::kw_using:
            decl = parse_using_declaration(ctx, sema);
            break;

          case Token::pseudo_alias:
            decl = parse_typealias_declaration(ctx, sema);
            break;

          case Token::identifier:
          case Token::coloncolon:
          case Token::kw_move:
          case Token::dollar:
            if (unnion->name == tok.text || tok.text == "this")
            {
              decl = parse_constructor_declaration(ctx, sema);
              break;
            }

            decl = parse_subject_declaration(ctx, sema);
            break;

          case Token::tilde:
            decl = parse_destructor_declaration(ctx, sema);
            break;

          case Token::hash:
            switch (auto tok = ctx.token(nexttok); tok.type)
            {
              case Token::l_square:
                consume_attributes(ctx, sema);
                continue;

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

              case Token::identifier:
                if (tok.text != "end")
                  goto unhandled;
                if (conditionals_stack.empty())
                  goto unhandled;

                decl = parse_endif_declaration(ctx, conditionals_stack.back(), sema);

                conditionals_stack.pop_back();
                conditional = conditionals_stack.back();
                conditionals_stack.pop_back();
                break;

              case Token::l_brace:
                decl = parse_run_declaration(ctx, sema);
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
            ctx.consume_til_resumable();
        }

        if (!decl)
          continue;

        if (!ctx.attributes.empty())
          ctx.diag.error("unexpected attributes", ctx.text, tok.loc);

        if (conditional)
        {
          decl->flags |= Decl::Conditional;

          conditional->decls.push_back(decl);

          continue;
        }

        unnion->decls.push_back(decl);
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

    return unnion;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_vtable_declaration /////////////////////////
  Decl *parse_vtable_declaration(ParseContext &ctx, Sema &sema)
  {
    auto vtable = sema.vtable_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      vtable->flags |= StructDecl::Public;

    vtable->attributes = std::move(ctx.attributes);

    ctx.consume_token(Token::kw_vtable);

    if (ctx.tok == Token::identifier || ctx.tok == Token::dollar)
    {
      vtable->name = parse_ident(ctx, IdentUsage::TagName, sema);
    }

    if (ctx.try_consume_token(Token::less))
    {
      vtable->args = parse_args_list(ctx, sema);

      if (!ctx.try_consume_token(Token::greater))
      {
        ctx.diag.error("expected greater", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (ctx.try_consume_token(Token::colon))
    {
      vtable->flags |= TagDecl::PublicBase;

      if (ctx.try_consume_token(Token::kw_pub))
        vtable->flags |= TagDecl::PublicBase;

      vtable->basetype = parse_type(ctx, sema);
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

            default:
              goto unhandled;
          }
        }

        if (tok == Token::kw_static)
        {
          tok = ctx.token(nexttok++);
        }

        switch (tok.type)
        {
          case Token::kw_using:
            if (ctx.token(nexttok) == Token::identifier && (ctx.token(nexttok + 1) == Token::less || ctx.token(nexttok + 1) == Token::equal))
              tok.type = Token::pseudo_alias;
            break;

          case Token::kw_fn:
            if (ctx.token(nexttok) == Token::l_paren && (ctx.token(nexttok+1) == Token::star || ctx.token(nexttok+1) == Token::amp))
              tok.type = Token::pseudo_fnptr;
            break;

          default:
            break;
        }

        switch (tok.type)
        {
          case Token::semi:
            ctx.diag.warn("extra semi", ctx.text, tok.loc);
            ctx.consume_token(Token::semi);
            continue;

          case Token::kw_const:
            decl = parse_const_declaration(ctx, sema);
            break;

          case Token::kw_fn:
            decl = parse_function_declaration(ctx, sema);
            break;

          case Token::kw_struct:
            decl = parse_struct_declaration(ctx, sema);
            break;

          case Token::kw_union:
            decl = parse_union_declaration(ctx, sema);
            break;

          case Token::kw_concept:
            decl = parse_concept_declaration(ctx, sema);
            break;

          case Token::kw_enum:
            decl = parse_enum_declaration(ctx, sema);
            break;

          case Token::kw_import:
            decl = parse_import_declaration(ctx, sema);
            break;

          case Token::kw_using:
            decl = parse_using_declaration(ctx, sema);
            break;

          case Token::pseudo_alias:
            decl = parse_typealias_declaration(ctx, sema);
            break;

          case Token::hash:
            switch (auto tok = ctx.token(nexttok); tok.type)
            {
              case Token::l_square:
                consume_attributes(ctx, sema);
                continue;

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

              case Token::identifier:
                if (tok.text != "end")
                  goto unhandled;
                if (conditionals_stack.empty())
                  goto unhandled;

                decl = parse_endif_declaration(ctx, conditionals_stack.back(), sema);

                conditionals_stack.pop_back();
                conditional = conditionals_stack.back();
                conditionals_stack.pop_back();
                break;

              case Token::l_brace:
                decl = parse_run_declaration(ctx, sema);
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
            ctx.consume_til_resumable();
        }

        if (!decl)
          continue;

        if (!ctx.attributes.empty())
          ctx.diag.error("unexpected attributes", ctx.text, tok.loc);

        if (decl->kind() == Decl::Function)
        {
          auto fn = decl_cast<FunctionDecl>(decl);

          if (!fn->returntype)
          {
            ctx.diag.error("expected returntype on vtable function", ctx.text, ctx.tok.loc);
            goto resume;
          }

          if (fn->body)
          {
            ctx.diag.error("unexpected body on vtable function", ctx.text, ctx.tok.loc);
            goto resume;
          }
        }

        if (conditional)
        {
          decl->flags |= Decl::Conditional;

          conditional->decls.push_back(decl);

          continue;
        }

        vtable->decls.push_back(decl);
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

    return vtable;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_concept_declaration ////////////////////////
  Decl *parse_concept_declaration(ParseContext &ctx, Sema &sema)
  {
    auto koncept = sema.concept_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      koncept->flags |= FunctionDecl::Public;

    ctx.consume_token(Token::kw_concept);

    koncept->name = parse_ident(ctx, IdentUsage::TagName, sema);

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
        auto tok = ctx.tok;
        auto nexttok = 1;

        if (tok == Token::kw_pub)
        {
          tok = ctx.token(nexttok++);
        }

        if (tok == Token::kw_using && ctx.token(nexttok) == Token::identifier && (ctx.token(nexttok + 1) == Token::less || ctx.token(nexttok + 1) == Token::equal))
        {
          tok.type = Token::pseudo_alias;
        }

        switch (tok.type)
        {
          case Token::semi:
            ctx.diag.warn("extra semi", ctx.text, tok.loc);
            ctx.consume_token(Token::semi);
            continue;

          case Token::kw_const:
            decl = parse_const_declaration(ctx, sema);
            break;

          case Token::kw_using:
            decl = parse_using_declaration(ctx, sema);
            break;

          case Token::pseudo_alias:
            decl = parse_typealias_declaration(ctx, sema);
            break;

          case Token::kw_requires:
            decl = parse_requires_declaration(ctx, sema);
            break;

          default:
            ctx.diag.error("expected concept declaration", ctx.text, tok.loc);
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
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_constant_declaration ///////////////////////
  Decl *parse_constant_declaration(ParseContext &ctx, Sema &sema)
  {
    auto constant = sema.enum_constant_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      constant->flags |= Decl::Public;

    constant->name = parse_ident(ctx, IdentUsage::VarName, sema);

    if (ctx.try_consume_token(Token::equal))
    {
      constant->value = parse_expression(ctx, sema);

      if (!constant->value)
      {
        ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    if (!(ctx.try_consume_token(Token::semi) || ctx.try_consume_token(Token::comma) || ctx.tok == Token::r_brace))
    {
      ctx.diag.error("expected comma", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return constant;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_enum_declaration ///////////////////////////
  Decl *parse_enum_declaration(ParseContext &ctx, Sema &sema)
  {
    auto enumm = sema.enum_declaration(ctx.tok.loc);

    if (ctx.try_consume_token(Token::kw_pub))
      enumm->flags |= EnumDecl::Public;

    enumm->attributes = std::move(ctx.attributes);

    ctx.consume_token(Token::kw_enum);

    if (ctx.tok == Token::identifier || ctx.tok == Token::dollar)
    {
      enumm->name = parse_ident(ctx, IdentUsage::TagName, sema);
    }

    if (ctx.try_consume_token(Token::colon))
    {
      if (ctx.try_consume_token(Token::kw_pub))
        enumm->flags |= TagDecl::PublicBase;

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
            case Token::dollar:
              break;

            default:
              goto unhandled;
          }
        }

        if (tok == Token::kw_static)
        {
          tok = ctx.token(nexttok++);
        }

        switch (tok.type)
        {
          case Token::kw_using:
            if (ctx.token(nexttok) == Token::identifier && (ctx.token(nexttok + 1) == Token::less || ctx.token(nexttok + 1) == Token::equal))
              tok.type = Token::pseudo_alias;
            break;

          case Token::kw_fn:
            if (ctx.token(nexttok) == Token::l_paren && (ctx.token(nexttok+1) == Token::star || ctx.token(nexttok+1) == Token::amp))
              tok.type = Token::pseudo_fnptr;
            break;

          default:
            break;
        }

        switch (tok.type)
        {
          case Token::semi:
            ctx.diag.warn("extra semi", ctx.text, tok.loc);
            ctx.consume_token(Token::semi);
            continue;

          case Token::kw_const:
            decl = parse_const_declaration(ctx, sema);
            break;

          case Token::kw_fn:
            decl = parse_function_declaration(ctx, sema);
            break;

          case Token::kw_enum:
            decl = parse_enum_declaration(ctx, sema);
            break;

          case Token::identifier:
          case Token::kw_move:
          case Token::dollar:
            if (enumm->name == tok.text || tok.text == "this")
            {
              decl = parse_constructor_declaration(ctx, sema);
              break;
            }

            decl = parse_constant_declaration(ctx, sema);
            break;

          case Token::hash:
            switch (auto tok = ctx.token(nexttok); tok.type)
            {
              case Token::l_square:
                consume_attributes(ctx, sema);
                continue;

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

              case Token::identifier:
                if (tok.text != "end")
                  goto unhandled;
                if (conditionals_stack.empty())
                  goto unhandled;

                decl = parse_endif_declaration(ctx, conditionals_stack.back(), sema);

                conditionals_stack.pop_back();
                conditional = conditionals_stack.back();
                conditionals_stack.pop_back();
                break;

              case Token::l_brace:
                decl = parse_run_declaration(ctx, sema);
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
            ctx.consume_til_resumable();
        }

        if (!decl)
          continue;

        if (!ctx.attributes.empty())
          ctx.diag.error("unexpected attributes", ctx.text, tok.loc);

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
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_case_declaration ///////////////////////////
  Decl *parse_case_declaration(ParseContext &ctx, Sema &sema)
  {
    auto casse = sema.case_declaration(ctx.tok.loc);

    if (ctx.tok == Token::kw_case)
    {
      ctx.consume_token(Token::kw_case);

      auto tok = ctx.tok;
      auto lexcursor = ctx.lexcursor;

      while (!casse->label)
      {
        switch (tok.type)
        {
          case Token::hash:
          case Token::dotdot:
          case Token::dotdotequal:
          case Token::colon:
          case Token::eof:
            if (casse->label = parse_expression(ctx, sema); !casse->label)
              return nullptr;
            break;

          case Token::l_square:
            if (casse->label = sema.make_declref_expression(parse_qualified_name(ctx, sema), ctx.tok.loc); !casse->label)
              return nullptr;
            break;

          default:
            break;
        }

        lexcursor = lex(ctx.text, lexcursor, tok);
      }

      if (ctx.try_consume_token(Token::l_square))
      {
        auto var = sema.casevar_declaration(ctx.tok.loc);

        if (ctx.tok == Token::kw_let || ctx.tok == Token::kw_var)
        {
          var->type = parse_var_defn(ctx, var->flags, sema.make_typearg(Ident::kw_var, ctx.tok.loc), sema);

          auto loc = ctx.tok.loc;

          if (ctx.tok != Token::l_paren)
          {
            var->name = parse_ident(ctx, IdentUsage::VarName, sema);
          }

          if (ctx.try_consume_token(Token::l_paren))
          {
            var->pattern = sema.tuple_pattern(parse_var_bindings_list(ctx, var->flags, sema), loc);

            if (!ctx.try_consume_token(Token::r_paren))
            {
              ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
              goto resume;
            }
          }

          if (ctx.try_consume_token(Token::equal))
          {
            var->value = parse_expression(ctx, sema);
          }
        }
        else
        {
          var->name = parse_ident(ctx, IdentUsage::VarName, sema);

          var->type = sema.make_reference(sema.make_qualarg(sema.make_typearg(sema.make_typearg(Ident::kw_var, var->loc()))));
        }

        casse->parm = var;

        if (!ctx.try_consume_token(Token::r_square))
        {
          ctx.diag.error("expected colon", ctx.text, ctx.tok.loc);
          goto resume;
        }
      }
    }

    if (ctx.tok == Token::kw_else)
    {
      ctx.consume_token(Token::kw_else);
    }

    if (!ctx.try_consume_token(Token::colon))
    {
      ctx.diag.error("expected colon", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (ctx.tok != Token::kw_case && ctx.tok != Token::kw_else)
    {
      auto compound = sema.compound_statement(ctx.tok.loc);

      while (ctx.tok != Token::kw_case && ctx.tok != Token::kw_else && ctx.tok != Token::r_brace && ctx.tok != Token::eof)
      {
        Stmt *stmt = nullptr;

        if (ctx.tok == Token::hash && (ctx.token(1) == Token::kw_else || ctx.token(1).text == "end" || ctx.token(1) == Token::l_brace))
          break;

        switch (ctx.tok.type)
        {
          case Token::kw_fn:
          case Token::kw_extern:
          case Token::kw_const:
          case Token::kw_static:
          case Token::kw_import:
          case Token::kw_using:
          case Token::kw_struct:
          case Token::kw_union:
          case Token::kw_vtable:
          case Token::kw_concept:
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

      casse->body = compound;
    }

    if (casse->parm && !casse->body)
    {
      ctx.diag.error("parameterised case requires body", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return casse;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_injection_statement ////////////////////////
  Stmt *parse_injection_statement(ParseContext &ctx, Sema &sema)
  {
    auto injection = sema.injection_statement(ctx.tok.loc);

    ctx.consume_token(Token::arrow);

    vector<Decl*> decls;
    vector<Expr*> substitutions;
    std::swap(ctx.substitutions, substitutions);

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
            case Token::dollar:
              break;

            default:
              goto unhandled;
          }
        }

        if (tok == Token::kw_static)
        {
          tok = ctx.token(nexttok++);
        }

        switch (tok.type)
        {
          case Token::kw_using:
            if (ctx.token(nexttok) == Token::identifier && (ctx.token(nexttok + 1) == Token::less || ctx.token(nexttok + 1) == Token::equal))
              tok.type = Token::pseudo_alias;
            break;

          case Token::kw_fn:
            if (ctx.token(nexttok) == Token::l_paren && (ctx.token(nexttok+1) == Token::star || ctx.token(nexttok+1) == Token::amp))
              tok.type = Token::pseudo_fnptr;
            break;

          default:
            break;
        }

        switch (tok.type)
        {
          case Token::semi:
            ctx.diag.warn("extra semi", ctx.text, tok.loc);
            ctx.consume_token(Token::semi);
            continue;

          case Token::kw_const:
            decl = parse_const_declaration(ctx, sema);
            break;

          case Token::kw_fn:
            decl = parse_function_declaration(ctx, sema);
            break;

          case Token::kw_struct:
            decl = parse_struct_declaration(ctx, sema);
            break;

          case Token::kw_union:
            decl = parse_union_declaration(ctx, sema);
            break;

          case Token::kw_vtable:
            decl = parse_vtable_declaration(ctx, sema);
            break;

          case Token::kw_concept:
            decl = parse_concept_declaration(ctx, sema);
            break;

          case Token::kw_enum:
            decl = parse_enum_declaration(ctx, sema);
            break;

          case Token::kw_import:
            decl = parse_import_declaration(ctx, sema);
            break;

          case Token::kw_using:
            decl = parse_using_declaration(ctx, sema);
            break;

          case Token::pseudo_alias:
            decl = parse_typealias_declaration(ctx, sema);
            break;

          case Token::kw_case:
          case Token::kw_else:
            decl = parse_case_declaration(ctx, sema);
            break;

          case Token::kw_void:
          case Token::kw_null:
          case Token::kw_typeof:
          case Token::l_paren:
          case Token::identifier:
          case Token::coloncolon:
          case Token::pseudo_fnptr:
          case Token::dollar:
            if (tok == Token::dollar)
            {
              for (int indent = 0; tok != Token::eof; )
              {
                if (tok == Token::l_paren)
                  indent += 1;

                if (tok == Token::r_paren)
                  if (--indent <= 0)
                    break;

                tok = ctx.token(nexttok++);
              }
            }

            if (tok.text == "this")
            {
              decl = parse_constructor_declaration(ctx, sema);
              break;
            }

            switch (ctx.token(nexttok).type)
            {
              case Token::comma:
              case Token::equal:
              case Token::r_brace:
              case Token::semi:
                decl = parse_constant_declaration(ctx, sema);
                break;

              case Token::l_paren:
                decl = parse_subject_declaration(ctx, sema);
                break;

              default:
                decl = parse_field_declaration(ctx, sema);
                break;
            }

            break;

          case Token::kw_requires:
            decl = parse_requires_declaration(ctx, sema);
            break;

          case Token::tilde:
            decl = parse_destructor_declaration(ctx, sema);
            break;

          case Token::eof:
            break;

          default:
          unhandled:
            ctx.diag.error("expected declaration", ctx.text, tok.loc);
            ctx.consume_til_resumable();
        }

        if (!decl)
          continue;

        decls.push_back(decl);
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

    std::swap(ctx.substitutions, substitutions);

    if (any_of(substitutions.begin(), substitutions.end(), [](auto &k) { return !k; }))
      return nullptr;

    injection->expr = sema.make_fragment_expression(std::move(substitutions), decls, injection->loc());

    return injection;

    resume:
      ctx.consume_til_resumable();
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

      case Token::kw_extern:
        stmt->decl = parse_function_declaration(ctx, sema);
        break;

      case Token::kw_struct:
        stmt->decl = parse_struct_declaration(ctx, sema);
        break;

      case Token::kw_union:
        stmt->decl = parse_union_declaration(ctx, sema);
        break;

      case Token::kw_vtable:
        stmt->decl = parse_vtable_declaration(ctx, sema);
        break;

      case Token::kw_concept:
        stmt->decl = parse_concept_declaration(ctx, sema);
        break;

      case Token::kw_enum:
        stmt->decl = parse_enum_declaration(ctx, sema);
        break;

      case Token::kw_import:
        stmt->decl = parse_import_declaration(ctx, sema);
        break;

      case Token::kw_using:
        if (ctx.token(1) == Token::identifier && (ctx.token(2) == Token::less || ctx.token(2) == Token::equal))
          stmt->decl = parse_typealias_declaration(ctx, sema);
        else
          stmt->decl = parse_using_declaration(ctx, sema);
        break;

      case Token::kw_let:
      case Token::kw_var:
      case Token::kw_const:
      case Token::kw_static:
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
      ctx.consume_til_resumable();
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
      ctx.consume_til_resumable();
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
        if (inits.size() == 1)
        {
          if (inits.back()->kind() == Stmt::Expression)
            ifs->cond = stmt_cast<ExprStmt>(inits.back())->expr;

          if (inits.back()->kind() == Stmt::Declaration)
          {
            ifs->inits = std::move(inits);
            ifs->cond = sema.make_declref_expression(sema.make_declref(decl_cast<VarDecl>(stmt_cast<DeclStmt>(ifs->inits.back())->decl)->name, ctx.tok.loc), ctx.tok.loc);
          }
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

    if (ctx.tok == Token::kw_else && ctx.token(1) != Token::colon)
    {
      if (!(ifs->flags & IfStmt::Static) || ctx.token(1) != Token::kw_if)
        ctx.consume_token(Token::kw_else);
      else
        ctx.tok.type = Token::hash;

      ifs->stmts[1] = parse_statement(ctx, sema);

      if (!ifs->stmts[1])
      {
        ctx.diag.error("expected statement", ctx.text, ctx.tok.loc);
        goto resume;
      }
    }

    return ifs;

    resume:
      ctx.consume_til_resumable();
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

    if (ctx.tok != Token::semi)
    {
      if (all_of(fors->inits.begin(), fors->inits.end(), [](auto &k) { return k->kind() == Stmt::Expression; }))
        ctx.diag.error("missing condition", ctx.text, ctx.tok.loc);
    }

    if (ctx.try_consume_token(Token::semi))
    {
      fors->cond = parse_expression(ctx, sema);

      if (!ctx.try_consume_token(Token::semi))
      {
        ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
        goto resume;
      }

      fors->iters = parse_statement_list(ctx, sema);

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
      ctx.consume_til_resumable();
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

    if (ctx.tok != Token::semi)
    {
      if (all_of(rofs->inits.begin(), rofs->inits.end(), [](auto &k) { return k->kind() == Stmt::Expression; }))
        ctx.diag.error("missing condition", ctx.text, ctx.tok.loc);
    }

    if (ctx.try_consume_token(Token::semi))
    {
      rofs->cond = parse_expression(ctx, sema);

      if (!ctx.try_consume_token(Token::semi))
      {
        ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
        goto resume;
      }

      rofs->iters = parse_statement_list(ctx, sema);

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
      ctx.consume_til_resumable();
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
        if (inits.size() == 1)
        {
          if (inits.back()->kind() == Stmt::Expression)
            wile->cond = stmt_cast<ExprStmt>(inits.back())->expr;
        }
      }

      if (ctx.try_consume_token(Token::semi))
      {
        wile->inits = std::move(inits);

        wile->iters = parse_statement_list(ctx, sema);

        if (!all_of(wile->iters.begin(), wile->iters.end(), [](auto &k) { return k->kind() == Stmt::Expression; }))
        {
          ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
          goto resume;
        }

        if (!ctx.try_consume_token(Token::semi))
        {
          ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
          goto resume;
        }

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
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_switch_statement ///////////////////////////
  Stmt *parse_switch_statement(ParseContext &ctx, Sema &sema)
  {
    auto swtch = sema.switch_statement(ctx.tok.loc);

    ctx.consume_token(Token::kw_switch);

    if (!ctx.try_consume_token(Token::l_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    {
      auto inits = parse_statement_list(ctx, sema);

      if (ctx.tok != Token::semi)
      {
        if (inits.size() == 1)
        {
          if (inits.back()->kind() == Stmt::Expression)
            swtch->cond = stmt_cast<ExprStmt>(inits.back())->expr;

          if (inits.back()->kind() == Stmt::Declaration)
          {
            swtch->inits = std::move(inits);
            swtch->cond = sema.make_declref_expression(sema.make_declref(decl_cast<VarDecl>(stmt_cast<DeclStmt>(swtch->inits.back())->decl)->name, ctx.tok.loc), ctx.tok.loc);
          }
        }
      }

      if (ctx.try_consume_token(Token::semi))
      {
        swtch->inits = std::move(inits);
        swtch->cond = parse_expression(ctx, sema);
      }
    }

    if (!swtch->cond)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::r_paren))
    {
      ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (ctx.try_consume_token(Token::l_brace))
    {
      Decl *decl = nullptr;

      IfDecl *conditional = nullptr;
      vector<IfDecl*> conditionals_stack;

      while (ctx.tok != Token::r_brace && ctx.tok != Token::eof)
      {
        auto tok = ctx.tok;
        auto nexttok = 1;

        switch (tok.type)
        {
          case Token::kw_case:
          case Token::kw_else:
            decl = parse_case_declaration(ctx, sema);
            break;

          case Token::hash:
            switch (auto tok = ctx.token(nexttok); tok.type)
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

              case Token::identifier:
                if (tok.text != "end")
                  goto unhandled;
                if (conditionals_stack.empty())
                  goto unhandled;

                decl = parse_endif_declaration(ctx, conditionals_stack.back(), sema);

                conditionals_stack.pop_back();
                conditional = conditionals_stack.back();
                conditionals_stack.pop_back();
                break;

              case Token::l_brace:
                decl = parse_run_declaration(ctx, sema);
                break;

              default:
                goto unhandled;
            }
            break;

          case Token::eof:
            break;

          default:
          unhandled:
            ctx.diag.error("expected case declaration", ctx.text, tok.loc);
            ctx.consume_til_resumable();
        }

        if (!decl)
          continue;

        if (conditional)
        {
          decl->flags |= Decl::Conditional;

          conditional->decls.push_back(decl);

          continue;
        }

        swtch->decls.push_back(decl);
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

    return swtch;

    resume:
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_goto_statement /////////////////////////////
  Stmt *parse_goto_statement(ParseContext &ctx, Sema &sema)
  {
    auto retrn = sema.goto_statement(ctx.tok.loc);

    ctx.consume_token(Token::kw_goto);

    if (ctx.try_consume_token(Token::kw_else))
      retrn->label = sema.make_declref_expression(sema.make_declref(Ident::kw_else, ctx.tok.loc), ctx.tok.loc);
    else
      retrn->label = parse_expression(ctx, sema);

    if (!retrn->label)
    {
      ctx.diag.error("expected expression", ctx.text, ctx.tok.loc);
      goto resume;
    }

    if (!ctx.try_consume_token(Token::semi))
    {
      ctx.diag.error("expected semi", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return retrn;

    resume:
      ctx.consume_til_resumable();
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

      if (ctx.tok == Token::identifier || ctx.tok == Token::dollar)
      {
        var->name = parse_ident(ctx, IdentUsage::VarName, sema);
      }

      if (!ctx.try_consume_token(Token::r_paren))
      {
        ctx.diag.error("expected paren", ctx.text, ctx.tok.loc);
        goto resume;
      }

      trys->errorvar = var;
    }

    if (ctx.tok != Token::l_brace)
    {
      ctx.diag.error("expected brace", ctx.text, ctx.tok.loc);
      goto resume;
    }

    trys->handler = parse_compound_statement(ctx, sema);

    if (!trys->handler)
    {
      ctx.diag.error("expected statement", ctx.text, ctx.tok.loc);
      goto resume;
    }

    return trys;

    resume:
      ctx.consume_til_resumable();
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
      ctx.consume_til_resumable();
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
      ctx.consume_til_resumable();
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
      ctx.consume_til_resumable();
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
      ctx.consume_til_resumable();
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

      while (ctx.tok == Token::hash && ctx.token(1) == Token::l_square)
      {
        consume_attributes(ctx, sema);
      }

      switch (ctx.tok.type)
      {
        case Token::kw_fn:
        case Token::kw_extern:
        case Token::kw_const:
        case Token::kw_static:
        case Token::kw_import:
        case Token::kw_using:
        case Token::kw_struct:
        case Token::kw_union:
        case Token::kw_vtable:
        case Token::kw_concept:
        case Token::kw_enum:
        case Token::kw_let:
        case Token::kw_var:
          stmt = parse_declaration_statement(ctx, sema);
          break;

        default:
          stmt = parse_statement(ctx, sema);
          break;
      }

      if (!ctx.attributes.empty())
      {
        ctx.diag.error("unexpected attributes", ctx.text, ctx.tok.loc);
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
      ctx.consume_til_resumable();
      return nullptr;
  }

  //|///////////////////// parse_statement //////////////////////////////////
  Stmt *parse_statement(ParseContext &ctx, Sema &sema)
  {
    switch (ctx.tok.type)
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

      case Token::kw_switch:
        return parse_switch_statement(ctx, sema);

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

      case Token::arrow:
        return parse_injection_statement(ctx, sema);

      case Token::kw_goto:
        return parse_goto_statement(ctx, sema);

      case Token::hash:
        switch (auto tok = ctx.token(1); tok.type)
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

      if (tok == Token::kw_static)
      {
        tok = ctx.token(nexttok++);
      }

      switch (tok.type)
      {
        case Token::kw_using:
          if (ctx.token(nexttok) == Token::identifier && (ctx.token(nexttok + 1) == Token::less || ctx.token(nexttok + 1) == Token::equal))
            tok.type = Token::pseudo_alias;
          break;

        case Token::kw_fn:
          if (ctx.token(nexttok) == Token::l_paren && (ctx.token(nexttok+1) == Token::star || ctx.token(nexttok+1) == Token::amp))
            tok.type = Token::pseudo_fnptr;
          break;

        default:
          break;
      }

      switch (tok.type)
      {
        case Token::semi:
          ctx.diag.warn("extra semi", ctx.text, tok.loc);
          ctx.consume_token(Token::semi);
          continue;

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

        case Token::kw_union:
          decl = parse_union_declaration(ctx, sema);
          break;

        case Token::kw_vtable:
          decl = parse_vtable_declaration(ctx, sema);
          break;

        case Token::kw_concept:
          decl = parse_concept_declaration(ctx, sema);
          break;

        case Token::kw_enum:
          decl = parse_enum_declaration(ctx, sema);
          break;

        case Token::kw_import:
          decl = parse_import_declaration(ctx, sema);
          break;

        case Token::kw_using:
          decl = parse_using_declaration(ctx, sema);
          break;

        case Token::pseudo_alias:
          decl = parse_typealias_declaration(ctx, sema);
          break;

        case Token::hash:
          switch (auto tok = ctx.token(nexttok); tok.type)
          {
            case Token::l_square:
              consume_attributes(ctx, sema);
              continue;

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

            case Token::identifier:
              if (tok.text != "end")
                goto unhandled;
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

        case Token::r_brace:
          ctx.consume_token(Token::r_brace);
          goto unhandled;

        case Token::eof:
          break;

        default:
        unhandled:
          ctx.diag.error("expected toplevel declaration", ctx.text, tok.loc);
          ctx.consume_til_resumable();
      }

      if (!decl || !conditional)
        break;

      if (!ctx.attributes.empty())
        ctx.diag.error("unexpected attributes", ctx.text, tok.loc);

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
bool load(ModuleDecl *module, Sema &sema, Diag &diag)
{
  SourceText text(module->file());

  if (!text)
    return false;

  ParseContext ctx(text, diag);

  while (ctx.tok != Token::eof)
  {
    if (auto decl = parse_toplevel_declaration(ctx, sema))
    {
      module->decls.push_back(decl);
    }
  }

  return true;
}

//|///////////////////// parse //////////////////////////////////////////////
bool parse(string const &path, Sema &sema, Diag &diag)
{
  auto unit = sema.translation_unit(path);

  if (!load(decl_cast<ModuleDecl>(unit->mainmodule), sema, diag))
    return false;

  semantic(decl_cast<ModuleDecl>(unit->mainmodule), sema, diag);

  sema.end();

  return true;
}
