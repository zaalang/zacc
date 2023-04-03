//
// diag.cpp
//
// Copyright (c) 2020-2023 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "diag.h"
#include <fstream>
#include <algorithm>
#include <iostream>

using namespace std;

namespace
{
  string module_file(Scope const &scope)
  {
    return get_module(scope)->file();
  }
}

//|///////////////////// stream /////////////////////////////////////////////

Diag &operator<<(Diag &diag, Diag::red)
{
  if (diag.colored)
  {
    diag.os << "\033[01;31m";
  }

  return diag;
}

Diag &operator<<(Diag &diag, Diag::cyan)
{
  if (diag.colored)
  {
    diag.os << "\033[01;36m";
  }

  return diag;
}

Diag &operator<<(Diag &diag, Diag::green)
{
  if (diag.colored)
  {
    diag.os << "\033[01;32m";
  }

  return diag;
}

Diag &operator<<(Diag &diag, Diag::white)
{
  if (diag.colored)
  {
    diag.os << "\033[01;37m";
  }

  return diag;
}

Diag &operator<<(Diag &diag, Diag::normal)
{
  if (diag.colored)
  {
    diag.os << "\033[0m";
  }

  return diag;
}


//|--------------------- Diag -----------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// Constructor ////////////////////////////////////////
Diag::Diag(string_view leader)
{
  colored = true;
  m_leader = leader;
}

//|///////////////////// Constructor ////////////////////////////////////////
Diag::Diag(Diag const &other)
{
  colored = other.colored;
  m_leader = other.m_leader;
  m_errored = other.m_errored;
  os << other.str();
}

//|///////////////////// info ///////////////////////////////////////////////
void Diag::info(string_view msg)
{
  *this << white() << m_leader << ": " << normal() << msg << '\n';
}

//|///////////////////// warn ///////////////////////////////////////////////
void Diag::warn(string_view msg)
{
  *this << white() << m_leader << ": " << normal() << "warning: " << msg << '\n';
}

//|///////////////////// error //////////////////////////////////////////////
void Diag::error(string_view msg)
{
  *this << white() << m_leader << ": " << red() << "error: " << normal() << msg << '\n';

  m_errored = true;
}

//|///////////////////// warn ///////////////////////////////////////////////
void Diag::warn(string_view msg, SourceText const &file, SourceLocation loc)
{
  *this << white() << file.path() << ':' << loc << ": " << normal() << "warning: " << msg << '\n';

  show_source(file, loc);
}

//|///////////////////// error //////////////////////////////////////////////
void Diag::error(string_view msg, SourceText const &file, SourceLocation loc)
{
  *this << white() << file.path() << ':' << loc << ": " << red() << "error: " << normal() << msg << '\n';

  show_source(file, loc);

  m_errored = true;
}

//|///////////////////// warn ///////////////////////////////////////////////
void Diag::warn(string_view msg, Scope const &scope, SourceLocation loc)
{
  auto file = module_file(scope);

  if (is_fn_scope(scope))
  {
    *this << white() << file << ':' << normal() << "in function '" << white() << *get<Decl*>(scope.owner) << normal() << "'\n";
  }

  *this << white() << file << ':' << loc << ": " << normal() << "warning: " << msg << '\n';

  show_source(file, loc);
}

//|///////////////////// error //////////////////////////////////////////////
void Diag::error(string_view msg, Scope const &scope, SourceLocation loc)
{
  auto file = module_file(scope);

  if (is_fn_scope(scope))
  {
    *this << white() << file << ':' << normal() << "in function '" << white() << *get<Decl*>(scope.owner) << normal() << "'\n";
  }

  *this << white() << file << ':' << loc << ": " << red() << "error: " << normal() << msg << '\n';

  show_source(file, loc);

  m_errored = true;
}

//|///////////////////// note ///////////////////////////////////////////////
void Diag::note(string_view msg)
{
  *this << normal() << "note: " << msg << '\n';
}

//|///////////////////// note ///////////////////////////////////////////////
void Diag::note(string_view msg, Scope const &scope, SourceLocation loc)
{
  auto file = module_file(scope);

  *this << white() << file << ':' << loc << ": " << normal() << "note: " << msg << '\n';

  show_source(file, loc);
}

//|///////////////////// Diag::errored //////////////////////////////////////
void Diag::errored()
{
  m_errored = true;
}

//|///////////////////// Diag::marker ///////////////////////////////////////
Diag::Marker Diag::marker()
{
  return { m_errored, os.tellp() };
}

//|///////////////////// Diag::revert ///////////////////////////////////////
void Diag::revert(Diag::Marker const &marker)
{
  m_errored = marker.errorstate;

  if (os.tellp() != marker.contentsize)
  {
    os.str(os.str().substr(0, marker.contentsize));
    os.seekp(0, ios_base::end);
  }
}

//|///////////////////// show_source ////////////////////////////////////////
void Diag::show_source(SourceText const &src, SourceLocation loc)
{
  auto beg = src.head();

  for(int i = 1; i < loc.lineno; ++i)
    beg = find(beg, src.tail(), '\n') + 1;

  auto end = find(beg, src.tail(), '\n');

  if (end[-1] == '\r')
    end -= 1;

  *this << cyan() << "  " << string_view(beg, end - beg) << '\n';

  for(int i = 1; i < loc.charpos; ++i)
    *this << ' ';

  *this << green() << "  ^" << '\n';

  *this << normal();
}
