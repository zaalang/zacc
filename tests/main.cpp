//
// tests.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include <iostream>

using namespace std;

//|//////////////////// main ////////////////////////////////////////////////
int main(int argc, char *args[])
{
  cout << "zacc tests\n\n";

  try
  {
  }
  catch(exception &e)
  {
    cout << "** " << e.what() << endl;
  }

  cout << endl;
}
