//
// lexer.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "lexer.h"
#include <iostream>
#include <fstream>
#include <cassert>

using namespace std;

namespace
{
  bool is_eol(char ch)
  {
    return (ch == '\r') || (ch == '\n');
  }

  bool is_whitespace(char ch)
  {
    return (ch == ' ') || (ch == '\t');
  }

  [[maybe_unused]] bool is_alpha(char ch)
  {
    return (ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z');
  }

  [[maybe_unused]] bool is_digit(char ch)
  {
    return (ch >= '0') && (ch <= '9');
  }

  bool is_char_body(char ch)
  {
    return (ch != '\r') && (ch != '\n') && (ch != '\t') && (ch != 0);
  }

  bool is_string_body(char ch)
  {
    return (ch != '\r') && (ch != '\n') && (ch != '\t') && (ch != 0);
  }

  bool is_integer_body(char ch)
  {
    return (ch >= '0' && ch <= '9') || (ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') || (ch == '_');
  }

  bool is_identifier_body(char ch)
  {
    return (ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9') || (ch == '_');
  }

  Token make_token(Token::Type type)
  {
    Token tok;
    tok.type = type;
    tok.loc = SourceLocation{};

    return tok;
  }

  Token make_token(Token::Type type, const char *beg, const char *end, LexCursor const &loc)
  {
    Token tok;
    tok.type = type;
    tok.text = string_view(beg, end - beg);
    tok.loc = SourceLocation{ loc.lineno + 1, int(loc.position - loc.linestart + 1) };

    return tok;
  }

  //|///////////////////// lex_comment //////////////////////////////////////
  LexCursor lex_comment(SourceText const &src, LexCursor const &cursor, Token &tok)
  {
    auto beg = src.head() + cursor.position;
    auto lineno = cursor.lineno;
    auto linestart = src.head() + cursor.linestart;

    auto ptr = beg;

    assert(ptr >= src.head() && ptr < src.tail() && *ptr == '/');

    if (ptr[0] == '/')
      ++ptr;

    if (ptr[0] == '/')
    {
      // line comment

      while (*ptr && !is_eol(*ptr))
        ++ptr;
    }

    else if (ptr[0] == '*')
    {
      // block comment

      int nesting = 0;

      while (*ptr)
      {
        if (is_eol(*ptr))
        {
          if (ptr[0] == '\r' && ptr[1] == '\n')
            ++ptr;

          lineno += 1;
          linestart = ptr;
        }

        if (ptr[0] == '*' && ptr[-1] == '/')
          ++nesting;

        if (ptr[0] == '/' && ptr[-1] == '*')
          --nesting;

        ptr += 1;

        if (nesting == 0)
          break;
      }
    }

    tok = make_token(Token::comment, beg, ptr, cursor);

    return LexCursor{ lineno, linestart - src.head(), ptr - src.head() };
  }

  //|///////////////////// lex_char_constant ////////////////////////////////
  LexCursor lex_char_constant(SourceText const &src, LexCursor const &cursor, Token &tok)
  {
    auto beg = src.head() + cursor.position;

    auto ptr = beg;

    assert(ptr >= src.head() && ptr < src.tail() && *ptr == '\'');

    if (ptr[0] == '\'')
      ++ptr;

    while (ptr[0] != '\'' && is_char_body(*ptr))
    {
      if (ptr[0] == '\\' && ptr[1] != 0)
        ++ptr;

      ++ptr;
    }

    if (ptr[0] == '\'')
      ++ptr;

    tok = make_token(Token::char_constant, beg, ptr, cursor);

    return LexCursor{ cursor.lineno, cursor.linestart, ptr - src.head() };
  }

  //|///////////////////// lex_string_literal ///////////////////////////////
  LexCursor lex_string_literal(SourceText const &src, LexCursor const &cursor, Token &tok)
  {
    auto beg = src.head() + cursor.position;

    auto ptr = beg;

    assert(ptr >= src.head() && ptr < src.tail() && *ptr == '"');

    if (ptr[0] == '"')
      ++ptr;

    while (ptr[0] != '"' && is_string_body(*ptr))
    {
      if (ptr[0] == '\\' && ptr[1] != 0)
        ++ptr;

      ++ptr;
    }

    if (ptr[0] == '"')
      ++ptr;

    tok = make_token(Token::string_literal, beg, ptr, cursor);

    return LexCursor{ cursor.lineno, cursor.linestart, ptr - src.head() };
  }

  //|///////////////////// lex_numeric_constant /////////////////////////////
  LexCursor lex_numeric_constant(SourceText const &src, LexCursor const &cursor, Token &tok)
  {
    auto beg = src.head() + cursor.position;

    auto ptr = beg;

    assert(ptr >= src.head() && ptr < src.tail() && is_digit(*ptr));

    while (is_integer_body(*ptr))
      ++ptr;

    if ((cursor.position == 0 || beg[-1] != '.') || (cursor.position > 1 && beg[-2] == '.'))
    {
      if (ptr[0] == '.' && ptr[1] != '.')
      {
        ++ptr;

        while (is_integer_body(*ptr))
          ++ptr;
      }

      if ((ptr[0] == '-' || ptr[0] == '+') && (ptr[-1] == 'e' || ptr[-1] == 'E'))
      {
        ++ptr;

        while (is_integer_body(*ptr))
          ++ptr;
      }

      if ((ptr[0] == '-' || ptr[0] == '+') && (ptr[-1] == 'p' || ptr[-1] == 'P'))
      {
        ++ptr;

        while (is_integer_body(*ptr))
          ++ptr;
      }
    }

    tok = make_token(Token::numeric_constant, beg, ptr, cursor);

    return LexCursor{ cursor.lineno, cursor.linestart, ptr - src.head() };
  }

  //|///////////////////// lex_punctuators //////////////////////////////////
  LexCursor lex_punctuators(SourceText const &src, LexCursor const &cursor, Token &tok)
  {
    auto beg = src.head() + cursor.position;

    auto ptr = beg;

    assert(ptr >= src.head() && ptr < src.tail());

    Token::Type type;

    switch(*ptr)
    {
      case '#':
        ptr += 1;
        type = Token::hash;
        break;

      case '?':
        ptr += 1;
        type = Token::question;
        break;

      case '[':
        ptr += 1;
        type = Token::l_square;
        break;

      case ']':
        ptr += 1;
        type = Token::r_square;
        break;

      case '(':
        ptr += 1;
        type = Token::l_paren;
        break;

      case ')':
        ptr += 1;
        type = Token::r_paren;
        break;

      case '{':
        ptr += 1;
        type = Token::l_brace;
        break;

      case '}':
        ptr += 1;
        type = Token::r_brace;
        break;

      case '.':
        if (ptr[1] == '.' && ptr[2] == '.')
        {
          ptr += 3;
          type = Token::ellipsis;
        }
        else if (ptr[1] == '.' && ptr[2] == '=')
        {
          ptr += 3;
          type = Token::dotdotequal;
        }
        else if (ptr[1] == '.')
        {
          ptr += 2;
          type = Token::dotdot;
        }
        else if (ptr[1] == '*')
        {
          ptr += 2;
          type = Token::periodstar;
        }
        else
        {
          ptr += 1;
          type = Token::period;
        }
        break;

      case '&':
        if (ptr[1] == '&')
        {
          ptr += 2;
          type = Token::ampamp;
        }
        else if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::ampequal;
        }
        else
        {
          ptr += 1;
          type = Token::amp;
        }
        break;

      case '*':
        if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::starequal;
        }
        else
        {
          ptr += 1;
          type = Token::star;
        }
        break;

      case '+':
        if (ptr[1] == '+')
        {
          ptr += 2;
          type = Token::plusplus;
        }
        else if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::plusequal;
        }
        else
        {
          ptr += 1;
          type = Token::plus;
        }
        break;

      case '-':
        if (ptr[1] == '-')
        {
          ptr += 2;
          type = Token::minusminus;
        }
        else if (ptr[1] == '>' && ptr[2] == '*')
        {
          ptr += 3;
          type = Token::arrowstar;
        }
        else if (ptr[1] == '>')
        {
          ptr += 2;
          type = Token::arrow;
        }
        else if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::minusequal;
        }
        else
        {
          ptr += 1;
          type = Token::minus;
        }
        break;

      case '~':
        ptr += 1;
        type = Token::tilde;
        break;

      case '!':
        if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::exclaimequal;
        }
        else
        {
          ptr += 1;
          type = Token::exclaim;
        }
        break;

      case '/':
        if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::slashequal;
        }
        else
        {
          ptr += 1;
          type = Token::slash;
        }
        break;

      case '%':
        if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::percentequal;
        }
        else
        {
          ptr += 1;
          type = Token::percent;
        }
        break;

      case '<':
        if (ptr[1] == '<' && ptr[2] == '=')
        {
          ptr += 3;
          type = Token::lesslessequal;
        }
        else if (ptr[1] == '<')
        {
          ptr += 2;
          type = Token::lessless;
        }
        else if (ptr[1] == '=' && ptr[2] == '>')
        {
          ptr += 3;
          type = Token::spaceship;
        }
        else if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::lessequal;
        }
        else
        {
          ptr += 1;
          type = Token::less;
        }
        break;

      case '>':
        if (ptr[1] == '>' && ptr[2] == '=')
        {
          ptr += 3;
          type = Token::greatergreaterequal;
        }
        else if (ptr[1] == '>')
        {
          ptr += 2;
          type = Token::greatergreater;
        }
        else if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::greaterequal;
        }
        else
        {
          ptr += 1;
          type = Token::greater;
        }
        break;

      case '^':
        if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::caretequal;
        }
        else
        {
          ptr += 1;
          type = Token::caret;
        }
        break;

      case '|':
        if (ptr[1] == '|')
        {
          ptr += 2;
          type = Token::pipepipe;
        }
        else if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::pipeequal;
        }
        else
        {
          ptr += 1;
          type = Token::pipe;
        }
        break;

      case ':':
        if (ptr[1] == ':')
        {
          ptr += 2;
          type = Token::coloncolon;
        }
        else
        {
          ptr += 1;
          type = Token::colon;
        }
        break;

      case '=':
        if (ptr[1] == '=')
        {
          ptr += 2;
          type = Token::equalequal;
        }
        else
        {
          ptr += 1;
          type = Token::equal;
        }
        break;

      case ',':
        ptr += 1;
        type = Token::comma;
        break;

      case ';':
        ptr += 1;
        type = Token::semi;
        break;

      default:
        throw logic_error("unexpected punctuator");
    }

    tok = make_token(type, beg, ptr, cursor);

    return LexCursor{ cursor.lineno, cursor.linestart, ptr - src.head() };
  }

  //|///////////////////// lex_identifier ///////////////////////////////////
  LexCursor lex_identifier(SourceText const &src, LexCursor const &cursor, Token &tok)
  {
    auto beg = src.head() + cursor.position;

    auto ptr = beg;

    assert(ptr >= src.head() && ptr < src.tail() && (is_alpha(*ptr) || *ptr == '_' || *ptr == '#'));

    if (*ptr == '#')
      ++ptr;

    while (is_identifier_body(*ptr))
      ++ptr;

    auto type = Token::identifier;
    auto identifier = string_view(beg, ptr - beg);

    switch(identifier[0])
    {
      case 'a':
        if (identifier == "alignof")
          type = Token::kw_alignof;
        else if (identifier == "await")
          type = Token::kw_await;
        break;

      case 'b':
        if (identifier == "break")
          type = Token::kw_break;
        break;

      case 'c':
        if (identifier == "const")
          type = Token::kw_const;
        else if (identifier == "class")
          type = Token::kw_class;
        else if (identifier == "cast")
          type = Token::kw_cast;
        else if (identifier == "case")
          type = Token::kw_case;
        else if (identifier == "catch")
          type = Token::kw_catch;
        else if (identifier == "continue")
          type = Token::kw_continue;
        else if (identifier == "concept")
          type = Token::kw_concept;
        break;

      case 'e':
        if (identifier == "else")
          type = Token::kw_else;
        else if (identifier == "enum")
          type = Token::kw_enum;
        else if (identifier == "extern")
          type = Token::kw_extern;
        break;

      case 'f':
        if (identifier == "false")
          type = Token::kw_false;
        else if (identifier == "fn")
          type = Token::kw_fn;
        else if (identifier == "for")
          type = Token::kw_for;
        break;

      case 'i':
        if (identifier == "if")
          type = Token::kw_if;
        else if (identifier == "import")
          type = Token::kw_import;
        break;

      case 'l':
        if (identifier == "let")
          type = Token::kw_let;
        break;

      case 'm':
        if (identifier == "mut")
          type = Token::kw_mut;
        break;

      case 'n':
        if (identifier == "null")
          type = Token::kw_null;
        else if (identifier == "new")
          type = Token::kw_new;
        else if (identifier == "nil")
          type = Token::kw_nil;
        break;

      case 'p':
        if (identifier == "pub")
          type = Token::kw_pub;
        break;

      case 'r':
        if (identifier == "return")
          type = Token::kw_return;
        else if (identifier == "rof")
          type = Token::kw_rof;
        else if (identifier == "requires")
          type = Token::kw_requires;
        break;

      case 's':
        if (identifier == "struct")
          type = Token::kw_struct;
        else if (identifier == "switch")
          type = Token::kw_switch;
        else if (identifier == "sizeof")
          type = Token::kw_sizeof;
        else if (identifier == "static")
          type = Token::kw_static;
        break;

      case 't':
        if (identifier == "true")
          type = Token::kw_true;
        else if (identifier == "typedef")
          type = Token::kw_typedef;
        else if (identifier == "typeof")
          type = Token::kw_typeof;
        else if (identifier == "this")
          type = Token::kw_this;
        else if (identifier == "try")
          type = Token::kw_try;
        else if (identifier == "throw")
          type = Token::kw_throw;
        else if (identifier == "throws")
          type = Token::kw_throws;
        break;

      case 'u':
        if (identifier == "using")
          type = Token::kw_using;
        else if (identifier == "union")
          type = Token::kw_union;
        break;

      case 'v':
        if (identifier == "var")
          type = Token::kw_var;
        else if (identifier == "void")
          type = Token::kw_void;
        break;

      case 'w':
        if (identifier == "while")
          type = Token::kw_while;
        break;

      case 'y':
        if (identifier == "yield")
          type = Token::kw_yield;
        break;
    }

    tok = make_token(type, beg, ptr, cursor);

    return LexCursor{ cursor.lineno, cursor.linestart, ptr - src.head() };
  }

  //|///////////////////// lex_identifieror_or_hash /////////////////////////
  LexCursor lex_identifieror_or_hash(SourceText const &src, LexCursor const &cursor, Token &tok)
  {
    auto ptr = src.head() + cursor.position;

    if (cursor.position == 0 || (ptr[-1] != '.' && ptr[-1] != ':'))
      return lex_punctuators(src, cursor, tok);
    else
      return lex_identifier(src, cursor, tok);
  }
}


//|--------------------- SourceText -----------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// SourceText::Constructor ////////////////////////////
SourceText::SourceText(string const &path)
  : m_path(path)
{
  if (auto fin = ifstream(path, ios::binary); fin)
  {
    fin.seekg(0, ios::end);
    size_t size = fin.tellg();
    fin.seekg(0, ios::beg);

    m_contents.resize(size + 1);

    fin.read(m_contents.data(), size);

    m_contents.back() = '\0';
  }
}

//|///////////////////// SourceText::Constructor ////////////////////////////
SourceText::SourceText(string_view::const_iterator beg, string_view::const_iterator end)
{
  m_contents.reserve(distance(beg, end) + 1);
  m_contents.append(beg, end);
  m_contents += '\0';
}


//|--------------------- Lexer ----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// lex ////////////////////////////////////////////////
auto lex(SourceText const &src, LexCursor cursor, Token &tok) -> LexCursor
{
  assert(src.size() > 0 && *prev(src.tail()) == 0);

  while (true)
  {
    auto ptr = src.head() + cursor.position;

    while (is_whitespace(*ptr))
      ++ptr;

    cursor.position = ptr - src.head();

    if (*ptr == 0)
    {
      tok = make_token(Token::eof);

      return cursor;
    }

    if (ptr[0] == '/' && (ptr[1] == '/' || ptr[1] == '*'))
    {
      cursor = lex_comment(src, cursor, tok);

      continue;
    }

    switch (ptr[0])
    {
      case '\r':
        if (ptr[1] == '\n')
          ++ptr;
        [[fallthrough]];

      case '\n':
        ++ptr;
        cursor.lineno += 1;
        cursor.linestart = ptr - src.head();
        break;

      case '\'':
        return lex_char_constant(src, cursor, tok);

      case '"':
        return lex_string_literal(src, cursor, tok);

      case '?':
        return lex_punctuators(src, cursor, tok);

      case '[': case ']':
        return lex_punctuators(src, cursor, tok);

      case '(': case ')':
        return lex_punctuators(src, cursor, tok);

      case '{': case '}':
        return lex_punctuators(src, cursor, tok);

      case '.':
        return lex_punctuators(src, cursor, tok);

      case '+': case '-': case '*': case '/': case '%':
        return lex_punctuators(src, cursor, tok);

      case '&': case '|': case '~': case '!': case '^': case '<': case '>': case '=':
        return lex_punctuators(src, cursor, tok);

      case ':': case ',': case ';':
        return lex_punctuators(src, cursor, tok);

      case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9':
        return lex_numeric_constant(src, cursor, tok);

      case 'A': case 'B': case 'C': case 'D': case 'E': case 'F': case 'G':
      case 'H': case 'I': case 'J': case 'K': case 'L': case 'M': case 'N':
      case 'O': case 'P': case 'Q': case 'R': case 'S': case 'T': case 'U':
      case 'V': case 'W': case 'X': case 'Y': case 'Z':
      case 'a': case 'b': case 'c': case 'd': case 'e': case 'f': case 'g':
      case 'h': case 'i': case 'j': case 'k': case 'l': case 'm': case 'n':
      case 'o': case 'p': case 'q': case 'r': case 's': case 't': case 'u':
      case 'v': case 'w': case 'x': case 'y': case 'z':
      case '_':
        return lex_identifier(src, cursor, tok);

      case '#':
        return lex_identifieror_or_hash(src, cursor, tok);

      default:
        ptr += 1;
        cerr << "warning: unknown character in lexer\n";
    }

    cursor.position = ptr - src.head();
  }
}

//|///////////////////// dump_token /////////////////////////////////////////
void dump_token(Token const &tok)
{
  switch(tok.type)
  {
    case Token::unknown:
      cout << "unknown\n";
      break;

    case Token::question:
      cout << "question '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::l_square:
      cout << "l_square '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::r_square:
      cout << "r_square '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::l_paren:
      cout << "l_paren '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::r_paren:
      cout << "r_paren '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::l_brace:
      cout << "l_brace '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::r_brace:
      cout << "r_brace '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::period:
      cout << "period '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::periodstar:
      cout << "periodstar '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::ellipsis:
      cout << "ellipsis '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::dotdot:
      cout << "dotdot '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::dotdotequal:
      cout << "dotdotequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::amp:
      cout << "amp '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::ampamp:
      cout << "ampamp '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::ampequal:
      cout << "ampequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::star:
      cout << "star '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::starequal:
      cout << "starequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::plus:
      cout << "plus '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::plusplus:
      cout << "plusplus '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::plusequal:
      cout << "plusequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::minus:
      cout << "minus '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::minusminus:
      cout << "minusminus '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::minusequal:
      cout << "minusequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::arrow:
      cout << "arrow '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::arrowstar:
      cout << "arrowstar '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::tilde:
      cout << "tilde '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::exclaim:
      cout << "exclaim '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::exclaimequal:
      cout << "exclaimequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::slash:
      cout << "slash '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::slashequal:
      cout << "slashequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::percent:
      cout << "percent '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::percentequal:
      cout << "percentequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::less:
      cout << "less '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::lessless:
      cout << "lessless '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::lesslessequal:
      cout << "lesslessequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::lessequal:
      cout << "lessequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::spaceship:
      cout << "spaceship '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::greater:
      cout << "greater '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::greatergreater:
      cout << "greatergreater '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::greatergreaterequal:
      cout << "greatergreaterequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::greaterequal:
      cout << "greaterequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::caret:
      cout << "caret '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::caretequal:
      cout << "caretequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::pipe:
      cout << "pipe '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::pipepipe:
      cout << "pipepipe '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::pipeequal:
      cout << "pipeequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::colon:
      cout << "colon '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::coloncolon:
      cout << "coloncolon '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::equalequal:
      cout << "equalequal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::equal:
      cout << "equal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::comma:
      cout << "comma '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::semi:
      cout << "semi '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::char_constant:
      cout << "char_constant '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::string_literal:
      cout << "string_literal '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::numeric_constant:
      cout << "numeric_constant '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::identifier:
      cout << "identifier '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;

    case Token::comment:
      cout << "comment\n";
      break;

    case Token::eof:
      cout << "eof\n";
      break;

    default:
      cout << "keyword '" << tok.text << "' Loc=<" << tok.loc << ">\n";
      break;
  }
}

//|///////////////////// dump_tokens ////////////////////////////////////////
void dump_tokens(SourceText const &src)
{
  Token tok;
  LexCursor cursor;

  while (src)
  {
    cursor = lex(src, cursor, tok);

    dump_token(tok);

    if (tok == Token::eof)
      break;
  }
}
