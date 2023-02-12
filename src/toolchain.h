//
// toolchain.h
//
// Copyright (C) 2020-2022 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include "codegen.h"
#include <string>
#include <string_view>
#include <vector>

//|--------------------- ToolChain ------------------------------------------
//|--------------------------------------------------------------------------

class ToolChain
{
  public:

    enum Type
    {
      MinGW,
      GCC,
      MSVC,
      ZaOS,
      Wasm,

      Unknown,
    };

    enum FileType
    {
      Object,
      Assembly,
      Intermediate,
      Executable
    };

  public:
    ToolChain(std::string const &triple);

    Type type() const { return m_type; }
    
    std::string const & os() const { return m_os; }
    std::string const & env() const { return m_env; }

    explicit operator bool() const { return m_type != Unknown; }

  public:

    void add_library_path(std::string_view path);

    int ld(std::string_view input, std::string_view output, std::vector<std::string> libraries = {});

  protected:

    Type m_type;

    std::string m_arch;
    std::string m_vendor;
    std::string m_os;
    std::string m_env;

    std::string m_base;

    std::vector<std::string> m_library_paths;
};

std::string filename(ToolChain const &tc, std::string_view path, ToolChain::FileType type);
std::string filename(ToolChain const &tc, std::string_view path, GenOpts::OutputType type);
