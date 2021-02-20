//
// tests.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include <filesystem>
#include <vector>
#include <string>
#include <fstream>
#include <iostream>

#if defined _WIN32
#include <windows.h>
#endif

using namespace std;

#if defined _MSC_VER
#define COMPILE_CMD "zacc.exe -c -I..\\..\\..\\..\\std"
#define COMPILE_TESTS_PATH "..\\..\\..\\tests"
#elif defined __MINGW64__
#define COMPILE_CMD "zacc.exe -c -I..\\..\\..\\std"
#define COMPILE_TESTS_PATH "..\\..\\tests"
#else
#define COMPILE_CMD "./zacc -c -I../../../std"
#define COMPILE_TESTS_PATH "../../tests"
#endif

//|//////////////////// compile_tests ///////////////////////////////////////
void compile_tests()
{
  int passed = 0, failed = 0;

  auto fn = fstream("output", ios_base::in | ios_base::out | ios_base::trunc);

  for(auto &entry : std::filesystem::recursive_directory_iterator(COMPILE_TESTS_PATH))
  {
    if (!entry.is_regular_file() || entry.path().extension() != ".zaa")
      continue;

    cout << "[    ] " << entry.path().filename() << '\r' << std::flush;

    fn << "Running " << entry.path().string() << endl;

#if defined _WIN32
    auto fpos = fn.tellg(); fn.close();
#endif

    string cmd;
    cmd += COMPILE_CMD;
    cmd += " " + entry.path().string();
    cmd += " >>output 2>&1";

    int ret = system(cmd.c_str());

#if defined _WIN32
    fn.open("output", ios_base::in | ios_base::out); fn.seekg(fpos, ios_base::beg);
#endif

    string buffer;
    vector<string> output;
    while (getline(fn, buffer))
    {
      output.push_back(buffer);
    }

    fn.clear();

    fn << "Done, exit : " << ret << "\n" << endl;

    bool success = (ret == 0) && output.empty();

    if (success)
      cout << "[\033[01;32mPASS\033[0m] " << entry.path().filename() << endl;
    else
      cout << "[\033[01;31mFAIL\033[0m] " << entry.path().filename() << endl;

    for(auto &line : output)
    {
      cout << "  " << line << '\n';
    }

    if (success)
      passed += 1;
    else
      failed += 1;
  }

  cout << '\n';
  cout << "Completed " << (passed + failed) << " tests " << failed << " failed...\n";
  cout << endl;
}

//|//////////////////// main ////////////////////////////////////////////////
int main(int argc, char *args[])
{
  cout << "zacc tests\n\n";

#if defined _WIN32
  HANDLE handle = GetStdHandle(STD_OUTPUT_HANDLE);
  DWORD mode = 0;
  GetConsoleMode(handle, &mode);
  SetConsoleMode(handle, mode | 0x0004);
#endif

  try
  {
    compile_tests();
  }
  catch(exception &e)
  {
    cout << "** " << e.what() << endl;
  }

  cout << endl;
}
