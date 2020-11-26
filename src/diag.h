//
// diag.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "ast.h"
#include "query.h"
#include <string>
#include <string_view>
#include <sstream>
#include <cassert>

//-------------------------- Diag -------------------------------------------
//---------------------------------------------------------------------------

class Diag
{
  public:
    Diag(std::string_view leader);

    std::string_view leader() const { return m_leader; }

    void info(std::string_view msg);
    void warn(std::string_view msg);
    void error(std::string_view msg);

    void warn(std::string_view msg, SourceText const &file, SourceLocation loc);
    void error(std::string_view msg, SourceText const &file, SourceLocation loc);

    void warn(std::string_view msg, Scope const &scope, SourceLocation loc);
    void error(std::string_view msg, Scope const &scope, SourceLocation loc);

    bool has_errored() const { return m_errored; } 

    std::string str() const { return os.str(); }

  public:

    bool colored;

    struct red { };
    struct cyan { };
    struct green { };
    struct white { };
    struct normal { };

    friend Diag &operator<<(Diag &diag, Diag::red);
    friend Diag &operator<<(Diag &diag, Diag::cyan);
    friend Diag &operator<<(Diag &diag, Diag::green);
    friend Diag &operator<<(Diag &diag, Diag::white);
    friend Diag &operator<<(Diag &diag, Diag::normal);

    template<typename T>
    friend Diag &operator<<(Diag &diag, T &&out)
    {
      diag.os << out;
      return diag;
    }

    friend Diag &operator<<(Diag &diag, Diag &out)
    {
      if (out.has_errored())
        diag.m_errored = true;

      diag.os << out.str();
      return diag;
    }

  public:

    struct Marker
    {
      bool errorstate;
      std::streampos contentsize;
    };

    Marker marker();
    void revert(Marker const &marker);

  protected:

    void show_source(SourceText const &file, SourceLocation loc);

  protected:

    std::ostringstream os;

    bool m_errored = false;

    std::string m_leader;
};

//|///////////////////// print //////////////////////////////////////////////
inline std::ostream &operator <<(std::ostream &os, Diag const &diag)
{
  os << diag.str();

  return os;
}
