//
// lexer.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include <iostream>
#include <string_view>
#include <cassert>

struct SourceLocation
{
  int lineno;
  int charpos;
};

inline std::ostream &operator <<(std::ostream &os, SourceLocation const &loc)
{
  os << loc.lineno << ':' << loc.charpos;

  return os;
}

//-------------------------- SourceText -------------------------------------
//---------------------------------------------------------------------------

class SourceText
{
  public:
    SourceText(std::string const &path);
    SourceText(std::string_view::const_iterator beg, std::string_view::const_iterator end);

    std::string const &path() const { return m_path; }

    size_t size() const { return m_contents.size(); }

    const char *head() const { return m_contents.data(); }
    const char *tail() const { return m_contents.data() + m_contents.size(); }

    bool operator!() const { return m_contents.empty(); }
    explicit operator bool() const { return m_contents.size() != 0; }

  private:

    std::string m_path;
    std::string m_contents;
};


//-------------------------- Token ------------------------------------------
//---------------------------------------------------------------------------

struct Token
{
  enum Type
  {
    unknown,

    hash,
    question,
    l_square,
    r_square,
    l_paren,
    r_paren,
    l_brace,
    r_brace,
    period,
    periodstar,
    ellipsis,
    dotdot,
    dotdotequal,
    amp,
    ampamp,
    ampequal,
    star,
    starequal,
    plus,
    plusplus,
    plusequal,
    minus,
    minusminus,
    minusequal,
    arrow,
    arrowstar,
    tilde,
    exclaim,
    exclaimequal,
    slash,
    slashequal,
    percent,
    percentequal,
    less,
    lessless,
    lesslessequal,
    lessequal,
    spaceship,
    greater,
    greatergreater,
    greatergreaterequal,
    greaterequal,
    caret,
    caretequal,
    pipe,
    pipepipe,
    pipeequal,
    colon,
    coloncolon,
    equalequal,
    equal,
    comma,
    semi,
    char_constant,
    string_literal,
    numeric_constant,
    identifier,
    comment,
    eof,

    kw_fn,
    kw_pub,
    kw_extern,
    kw_mut,
    kw_const,
    kw_true,
    kw_false,
    kw_void,
    kw_null,
    kw_nil,
    kw_using,
    kw_var,
    kw_let,
    kw_if,
    kw_else,
    kw_return,
    kw_typedef,
    kw_class,
    kw_struct,
    kw_sizeof,
    kw_alignof,
    kw_typeof,
    kw_static,
    kw_cast,
    kw_this,
    kw_new,
    kw_requires,
    kw_try,
    kw_catch,
    kw_throw,
    kw_throws,
    kw_for,
    kw_rof,
    kw_while,
    kw_break,
    kw_continue,
    kw_concept,
    kw_import,
    kw_enum,
    kw_yield,
    kw_await,
  };

  Type type = unknown;
  SourceLocation loc;
  std::string_view text;
};

inline bool operator==(Token const &lhs, Token::Type type)
{
  return (lhs.type == type);
}

inline bool operator!=(Token const &lhs, Token::Type type)
{
  return !(lhs == type);
}


//-------------------------- Lexer ------------------------------------------
//---------------------------------------------------------------------------

struct LexCursor
{
  int lineno = 0;
  ptrdiff_t linestart = 0;
  ptrdiff_t position = 0;
};

auto lex(SourceText const &src, LexCursor cursor, Token &tok) -> LexCursor;

void dump_token(Token const &tok);
void dump_tokens(SourceText const &src);
