//
// toolchain.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "toolchain.h"
#include <iostream>
#include <unistd.h>

using namespace std;

namespace
{
  //|///////////////////// basename ///////////////////////////////////////////
  string basename(string_view path)
  {
  #ifdef _WIN32
    auto i = path.find_last_of(":\\/");
  #else
    auto i = path.find_last_of('/');
  #endif

    if (i != string_view::npos)
      i += 1;
    else
      i = 0;

    auto j = path.find_last_of('.');

    if (j == string_view::npos)
      j = path.length();

    return string(path.substr(i, j - i));
  }
}

//|--------------------- ToolChain ------------------------------------------
//|--------------------------------------------------------------------------

//|///////////////////// Constructor ////////////////////////////////////////
ToolChain::ToolChain(string const &triple)
  : m_type(Unknown)
{
  if (auto i = triple.find_first_of('-'); i != string::npos)
  {
    m_arch = triple.substr(0, i);

    if (auto j = triple.find_first_of('-', i + 1); j != string::npos)
    {
      m_vendor = triple.substr(i + 1, j - i - 1);

      if (auto k = triple.find_first_of('-', j + 1); k != string::npos)
      {
        m_os = triple.substr(j + 1, k - j - 1);

        m_env = triple.substr(k + 1, string::npos);
      }
    }
  }

  if (m_os == "windows" && m_env == "gnu")
  {
    m_type = MinGW;

    if (string paths = string(getenv("PATH")) + ';'; !paths.empty())
    {
      for(size_t i = 0, j = paths.find_first_of(';'); j != string::npos; i = j + 1, j = paths.find_first_of(';', j + 1))
      {
        auto libdir = paths.substr(i, j-i) + "\\..\\" + m_arch + "-" + m_vendor + "-mingw32" + "\\lib";

        if (access(libdir.c_str(), F_OK) == 0)
        {
          m_base = paths.substr(i, paths.substr(i, j-i).find_last_of('\\'));
        }
      }
    }

    add_library_path(m_base + "\\" + m_arch + "-" + m_vendor + "-mingw32" + "\\lib");
  }

  if (m_os == "linux" && m_env == "gnu")
  {
    m_type = GCC;

    if (string paths = "/usr/lib;"; !paths.empty())
    {
      for(size_t i = 0, j = paths.find_first_of(';'); j != string::npos; i = j + 1, j = paths.find_first_of(';', j + 1))
      {
        auto libdir = paths.substr(i, j-i) + "/gcc/" + triple;

        if (access(libdir.c_str(), F_OK) == 0)
        {
          m_base = paths.substr(i, paths.substr(i, j-i).find_last_of('/'));

          if (access((m_base + '/' + triple).c_str(), F_OK) == 0)
            m_base = m_base + '/' + triple;
        }

        add_library_path(paths.substr(i, j-i));
      }      
    }
  }
}

//|///////////////////// add_library_path ///////////////////////////////////
void ToolChain::add_library_path(string_view path)
{
  m_library_paths.emplace_back(path);
}

//|///////////////////// link command ///////////////////////////////////////
int ToolChain::ld(string_view input, string_view output, vector<string> libraries)
{
  string cmd;

  if (m_type == MinGW)
  {
    cmd = m_base + "\\bin\\ld.exe";

    cmd += " -nostdlib";
	cmd += " --stack 8388608";

    // --subsystem console/windows

    cmd += " " + string(input);
    cmd += " -o " + string(output);

    for(auto &librarypath : m_library_paths)
      cmd += " -L" + librarypath;

    for(auto &library : libraries)
      cmd += " -l" + library;
  }

  if (m_type == GCC)
  {
    cmd = m_base + "/bin/ld";

    cmd += " -nostdlib";

    cmd += " " + string(input);
    cmd += " -o " + string(output);

    for(auto &librarypath : m_library_paths)
      cmd += " -L" + librarypath;

    for(auto &library : libraries)
      cmd += " -l" + library;
  }

  return system(cmd.c_str());
}

//|///////////////////// filename ///////////////////////////////////////////
string filename(ToolChain const &tc, string_view path, ToolChain::FileType type)
{
  auto suffix = string_view();

  switch(type)
  {
    case ToolChain::Object:
      suffix = (tc.type() == ToolChain::MinGW) ? ".obj" : ".o";
      break;

    case ToolChain::Assembly:
      suffix = ".s";
      break;

    case ToolChain::Intermediate:
      suffix = ".ll";
      break;

    case ToolChain::Executable:
      suffix = (tc.type() == ToolChain::MinGW) ? ".exe" : "";
      break;
  }

  return basename(path) + string(suffix);
}

string filename(ToolChain const &tc, string_view path, GenOpts::OutputType type)
{
  switch(type)
  {
    case GenOpts::OutputType::EmitAsm:
      return filename(tc, path, ToolChain::Assembly);

    case GenOpts::OutputType::EmitLL:
      return filename(tc, path, ToolChain::Intermediate);

    case GenOpts::OutputType::EmitObj:
      return filename(tc, path, ToolChain::Object);
  }

  throw logic_error("invalid output type");
}
