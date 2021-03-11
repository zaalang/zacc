//
// numeric.cpp
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#include "numeric.h"
#include <cstdlib>
#include <cassert>
#include <cstdlib>
#include <charconv>
#include <cmath>

using namespace std;

namespace
{

}

namespace Numeric
{
  //|--------------------- Numeric ------------------------------------------
  //|------------------------------------------------------------------------

  //|///////////////////// parse_bin_int ////////////////////////////////////
  Int parse_bin_int_literal(int sign, string_view str)
  {
    uint64_t value = 0;

    auto digit = [](char ch) { return ch - '0'; };

    for(auto ch : str.substr(2))
    {
      if (ch == '_')
        continue;

      auto last = value;

      value = value*2 + digit(ch);

      if (value < last)
        return { sign, last, true };
    }

    return { sign, value, false };
  }

  //|///////////////////// parse_oct_int ////////////////////////////////////
  Int parse_oct_int_literal(int sign, string_view str)
  {
    uint64_t value = 0;

    auto digit = [](char ch) { return ch - '0'; };

    for(auto ch : str.substr(2))
    {
      if (ch == '_')
        continue;

      auto last = value;

      value = value*8 + digit(ch);

      if (value < last)
        return { sign, last, true };
    }

    return { sign, value, false };
  }

  //|///////////////////// parse_hex_int ////////////////////////////////////
  Int parse_hex_int_literal(int sign, string_view str)
  {
    uint64_t value = 0;

    auto digit = [](char ch) { return ch - ((ch <= '9') ? '0' : (ch <= 'F') ? '7' : 'W'); };

    for(auto ch : str.substr(2))
    {
      if (ch == '_')
        continue;

      auto last = value;

      value = value*16 + digit(ch);

      if (value < last)
        return { sign, last, true };
    }

    return { sign, value, false };
  }

  //|///////////////////// parse_dec_int ////////////////////////////////////
  Int parse_dec_int_literal(int sign, string_view str)
  {
    uint64_t value = 0;

    auto digit = [](char ch) { return ch - '0'; };

    for(auto ch : str)
    {
      if (ch == '_')
        continue;

      auto last = value;

      value = value*10 + digit(ch);

      if (value < last)
        return { sign, last, true };
    }

    return { sign, value, false };
  }

  //|///////////////////// parse_int ////////////////////////////////////////
  Int parse_int_literal(int sign, string_view str)
  {
    if (str.substr(0, 2) == "0b")
    {
      return parse_bin_int_literal(sign, str);
    }
    else if (str.substr(0, 2) == "0o")
    {
      return parse_oct_int_literal(sign, str);
    }
    else if (str.substr(0, 2) == "0x")
    {
      return parse_hex_int_literal(sign, str);
    }
    else
    {
      return parse_dec_int_literal(sign, str);
    }
  }

  //|///////////////////// parse_char_literal ///////////////////////////////
  Int parse_char_literal(string_view str)
  {
    //
    // UTF-8 decode
    // Copyright (c) 2008-2009 Bjoern Hoehrmann <bjoern@hoehrmann.de>
    // See http://bjoern.hoehrmann.de/utf-8/decoder/dfa/ for details.
    //

    static const uint8_t utf8d[] = {
      0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 00..1f
      0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 20..3f
      0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 40..5f
      0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // 60..7f
      1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9, // 80..9f
      7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7, // a0..bf
      8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2, // c0..df
      0xa,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x3,0x4,0x3,0x3, // e0..ef
      0xb,0x6,0x6,0x6,0x5,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8, // f0..ff
      0x0,0x1,0x2,0x3,0x5,0x8,0x7,0x1,0x1,0x1,0x4,0x6,0x1,0x1,0x1,0x1, // s0..s0
      1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,1,1,1,1,1, // s1..s2
      1,2,1,1,1,1,1,2,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1, // s3..s4
      1,2,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,3,1,1,1,1,1,1, // s5..s6
      1,3,1,1,1,1,1,3,1,3,1,1,1,1,1,1,1,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1, // s7..s8
    };

    uint32_t value = 0;
    uint32_t state = 0;

    for(auto ch : str.substr(1, str.length() - 2))
    {
      uint32_t byte = uint8_t(ch);
      uint32_t type = utf8d[byte];

      value = (state != 0) ? (byte & 0x3fu) | (value << 6) : (0xff >> type) & (byte);

      state = utf8d[256 + state*16 + type];
    }

    if (str.length() >= 4 && str.substr(1).front() == '\\')
    {
      switch(str.substr(2).front())
      {
        case 'a':
          value = '\a';
          break;

        case 'f':
          value = '\f';
          break;

        case 'n':
          value = '\n';
          break;

        case 'r':
          value = '\r';
          break;

        case 't':
          value = '\t';
          break;

        case 'v':
          value = '\v';
          break;

        case '\'':
          value = '\'';
          break;

        case '"':
          value = '"';
          break;

        case '\\':
          value = '\\';
          break;

        case '0':
          value = 0;
          break;

        case 'x':
        case 'u':
        case 'U':
          std::from_chars(str.data()+3, str.data() + str.size() - 1, value, 16);
          break;

        default:
          break;
      }
    }

    return { +1, value, false };
  }

  //|///////////////////// parse_hex_float //////////////////////////////////
  Float parse_hex_float_literal(int sign, string_view str)
  {
    char buffer[256];

    size_t i = 0;
    for(auto ch : str)
    {
      if (ch == '_')
        continue;

      buffer[i++] = ch;

      if (i + 1 >= extent_v<decltype(buffer)>)
        break;
    }

    buffer[i] = 0;

    return { sign * strtod(buffer, nullptr), false };
  }

  //|///////////////////// parse_dec_float //////////////////////////////////
  Float parse_dec_float_literal(int sign, string_view str)
  {
    char buffer[256];

    size_t i = 0;
    for(auto ch : str)
    {
      if (ch == '_')
        continue;

      buffer[i++] = ch;

      if (i + 1 >= extent_v<decltype(buffer)>)
        break;
    }

    buffer[i] = 0;

    return { sign * strtod(buffer, nullptr), false };
  }

  //|///////////////////// parse_float //////////////////////////////////////
  Float parse_float_literal(int sign, string_view str)
  {
    if (str.substr(0, 2) == "0x")
    {
      return parse_hex_float_literal(sign, str);
    }
    else
    {
      return parse_dec_float_literal(sign, str);
    }
  }

  //|///////////////////// is_int_literal ///////////////////////////////////
  bool is_int_literal(string_view str)
  {
    assert(!str.empty());

    if (str.substr(0, 2) == "0b")
      return true;

    if (str.substr(0, 2) == "0o")
      return true;

    if (str.substr(0, 2) == "0x")
    {
      for(auto ch : str)
      {
        if (ch == '.' || ch == 'p' || ch == 'P')
          return false;
      }

      return true;
    }

    if (str.front() >= '0' && str.front() <= '9')
    {
      for(auto ch : str)
      {
        if (ch == '.' || ch == 'e' || ch == 'E' || ch == 'p' || ch == 'P')
          return false;
      }

      return true;
    }

    return false;
  }

  //|///////////////////// is_char_literal //////////////////////////////////
  bool is_char_literal(string_view str)
  {
    assert(!str.empty());

    if (str.substr(0, 1) == "'" && str.substr(str.size()-1, 1) == "'")
      return true;

    return false;
  }

  //|///////////////////// is_float_literal /////////////////////////////////
  bool is_float_literal(string_view str)
  {
    assert(!str.empty());

    if (str.front() == '.')
      return true;

    if (str.front() >= '0' && str.front() <= '9')
    {
      return !is_int_literal(str);
    }

    return false;
  }

  //|///////////////////// neg //////////////////////////////////////////////
  Int operator-(Int const &i)
  {
    return { -i.sign, i.value, i.overflowed };
  }

  //|///////////////////// add //////////////////////////////////////////////
  Int operator+(Int const &lhs, Int const &rhs)
  {
    auto sign = (lhs.value < rhs.value) ? rhs.sign : lhs.sign;
    auto value = (lhs.sign == rhs.sign) ? lhs.value + rhs.value : max(lhs.value, rhs.value) - min(lhs.value, rhs.value);
    auto overflowed = false;

    return { sign, value, overflowed };
  }

  //|///////////////////// sub //////////////////////////////////////////////
  Int operator-(Int const &lhs, Int const &rhs)
  {
    auto sign = (lhs.value < rhs.value) ? -rhs.sign : lhs.sign;
    auto value = (lhs.sign != rhs.sign) ? lhs.value + rhs.value : max(lhs.value, rhs.value) - min(lhs.value, rhs.value);
    auto overflowed = false;

    return { sign, value, overflowed };
  }

  //|///////////////////// div //////////////////////////////////////////////
  Int operator/(Int const &lhs, Int const &rhs)
  {
    auto sign = lhs.sign / rhs.sign;
    auto value = lhs.value / rhs.value;
    auto overflowed = false;

    return { sign, value, overflowed };
  }

  //|///////////////////// mul //////////////////////////////////////////////
  Int operator*(Int const &lhs, Int const &rhs)
  {
    auto sign = lhs.sign * rhs.sign;
    auto value = lhs.value * rhs.value;
    auto overflowed = false;

    return { sign, value, overflowed };
  }

  //|///////////////////// rem //////////////////////////////////////////////
  Int operator%(Int const &lhs, Int const &rhs)
  {
    auto sign = lhs.sign;
    auto value = lhs.value % rhs.value;
    auto overflowed = false;

    return { sign, value, overflowed };
  }

  //|///////////////////// shl //////////////////////////////////////////////
  Int operator<<(Int const &lhs, Int const &rhs)
  {
    auto sign = lhs.sign;
    auto value = lhs.value << rhs.value;
    auto overflowed = false;

    return { sign, value, overflowed };
  }

  //|///////////////////// shr //////////////////////////////////////////////
  Int operator>>(Int const &lhs, Int const &rhs)
  {
    auto sign = lhs.sign;
    auto value = lhs.value >> rhs.value;
    auto overflowed = false;

    if (sign < 0)
    {
      value = value + 1;
    }

    return { sign, value, overflowed };
  }

  //|///////////////////// and //////////////////////////////////////////////
  Int operator&(Int const &lhs, Int const &rhs)
  {
    auto sign = 1;
    auto value = (lhs.sign*lhs.value) & (rhs.sign*rhs.value);
    auto overflowed = false;

    if ((lhs.sign < 0) & (rhs.sign < 0))
    {
      sign = -1;
      value = ~value + 1;
    }

    return { sign, value, overflowed };
  }

  //|///////////////////// not //////////////////////////////////////////////
  Int operator~(Int const &i)
  {
    auto sign = 1;
    auto value = ~(i.sign*i.value);
    auto overflowed = false;
    auto maybe_unsigned = false;

    if (i.sign > 0)
    {
      sign = -1;
      value = ~value + 1;
      maybe_unsigned = true;
    }

    return { sign, value, overflowed, maybe_unsigned };
  }

  //|///////////////////// or ///////////////////////////////////////////////
  Int operator|(Int const &lhs, Int const &rhs)
  {
    auto sign = 1;
    auto value = (lhs.sign*lhs.value) | (rhs.sign*rhs.value);
    auto overflowed = false;

    if ((lhs.sign < 0) | (rhs.sign < 0))
    {
      sign = -1;
      value = ~value + 1;
    }

    return { sign, value, overflowed };
  }

  //|///////////////////// xor //////////////////////////////////////////////
  Int operator^(Int const &lhs, Int const &rhs)
  {
    auto sign = 1;
    auto value = (lhs.sign*lhs.value) ^ (rhs.sign*rhs.value);
    auto overflowed = false;

    if ((lhs.sign < 0) ^ (rhs.sign < 0))
    {
      sign = -1;
      value = ~value + 1;
    }

    return { sign, value, overflowed };
  }

  //|///////////////////// abs //////////////////////////////////////////////
  Int abs(Int const &lhs)
  {
    return { +1, lhs.value, lhs.overflowed };
  }

  //|///////////////////// pow //////////////////////////////////////////////
  Int pow(Int const &lhs, Int const &rhs)
  {
    auto sign = (rhs.value & 1) ? lhs.sign : 1;
    auto value = static_cast<uint64_t>(std::pow(lhs.value, rhs.value));
    auto overflowed = false;

    return { sign, value, overflowed };
  }

  //|///////////////////// sqrt /////////////////////////////////////////////
  Int sqrt(Int const &lhs)
  {
    auto sign = 1;
    auto value = static_cast<uint64_t>(std::sqrt(lhs.value));
    auto overflowed = false;

    return { sign, value, overflowed };
  }

  //|///////////////////// add_with_carry ///////////////////////////////////
  void add_with_carry(Int const &lhs, Int const &rhs, size_t width, bool is_signed, Int &lo, Int &hi)
  {
    auto sign = (lhs.value < rhs.value) ? rhs.sign : lhs.sign;

    if (lhs.sign == rhs.sign)
    {
      uint64_t result_hi = 0;
      uint64_t result_lo = lhs.value + rhs.value;

      if (result_lo < rhs.value)
        result_hi += 1;

      lo = int_literal(sign, result_lo & (0xFFFFFFFFFFFFFFFF >> (64 - width)));
      hi = int_literal(sign, result_hi | (((result_lo - lo.value) >> width) + (lo.sign < 0 ? 1 : 0)));

      if ((lo.sign < 0 && lo.value <= (size_t(1) << (width - 1))) || (lo.sign > 0 && lo.value >= (size_t(1) << (width - 1))))
        hi = hi + int_literal(1);
    }
    else
    {
      lo = int_literal(sign, max(lhs.value, rhs.value) - min(lhs.value, rhs.value));
      hi = int_literal(+1, !is_signed && lo.sign < 0 ? 1 : 0);
    }
  }

  //|///////////////////// sub_with_borrow //////////////////////////////////
  void sub_with_borrow(Int const &lhs, Int const &rhs, size_t width, bool is_signed, Int &lo, Int &hi)
  {
    auto sign = (lhs.value < rhs.value) ? -rhs.sign : lhs.sign;

    if (lhs.sign != rhs.sign)
    {
      uint64_t result_hi = 0;
      uint64_t result_lo = lhs.value + rhs.value;

      if (result_lo < rhs.value)
        result_hi += 1;

      lo = int_literal(sign, result_lo & (0xFFFFFFFFFFFFFFFF >> (64 - width)));
      hi = int_literal(sign, result_hi | (((result_lo - lo.value) >> width) + (lo.sign < 0 ? 1 : 0)));

      if ((lo.sign < 0 && lo.value <= (size_t(1) << (width - 1))) || (lo.sign > 0 && lo.value >= (size_t(1) << (width - 1))))
        hi = hi + int_literal(1);

      hi.sign *= -1;
    }
    else
    {
      lo = int_literal(sign, max(lhs.value, rhs.value) - min(lhs.value, rhs.value));
      hi = int_literal(+1, !is_signed && lo.sign < 0 ? 1 : 0);
    }
  }

  //|///////////////////// mul_with_carry ///////////////////////////////////
  void mul_with_carry(Int const &lhs, Int const &rhs, size_t width, bool is_signed, Int &lo, Int &hi)
  {
    uint64_t al = (lhs.value) & 0xFFFFFFFF;
    uint64_t ah = (lhs.value) >> 32;
    uint64_t bl = (rhs.value) & 0xFFFFFFFF;
    uint64_t bh = (rhs.value) >> 32;

    uint64_t s1 = al * bl;
    uint64_t s2 = ah * bl + (s1 >> 32);
    uint64_t s3 = al * bh + (s2 & 0xFFFFFFFF);
    uint64_t result_hi = (ah * bh) + (s2 >> 32) + (s3 >> 32);
    uint64_t result_lo = (s3 << 32) + (s1 & 0xFFFFFFFF);

    lo = int_literal(lhs.sign * rhs.sign, result_lo & (0xFFFFFFFFFFFFFFFF >> (64 - width)));
    hi = int_literal(lhs.sign * rhs.sign, result_hi | (((result_lo - lo.value) >> width) + (lo.sign < 0 ? 1 : 0)));

    if ((lo.sign < 0 && lo.value <= (size_t(1) << (width - 1))) || (lo.sign > 0 && lo.value >= (size_t(1) << (width - 1))))
      hi = hi + int_literal(1);
  }

  //|///////////////////// lt ///////////////////////////////////////////////
  bool operator<(Int const &lhs, Int const &rhs)
  {
    return (lhs.sign == rhs.sign && ((lhs.sign > 0 && lhs.value < rhs.value) || (lhs.sign < 0 && lhs.value > rhs.value))) || (lhs.sign < rhs.sign && lhs.value != 0);
  }

  //|///////////////////// gt ///////////////////////////////////////////////
  bool operator>(Int const &lhs, Int const &rhs)
  {
    return (lhs.sign == rhs.sign && ((lhs.sign > 0 && lhs.value > rhs.value) || (lhs.sign < 0 && lhs.value < rhs.value))) || (lhs.sign > rhs.sign && rhs.value != 0);
  }

  //|///////////////////// le ///////////////////////////////////////////////
  bool operator<=(Int const &lhs, Int const &rhs)
  {
    return (lhs.sign == rhs.sign && ((lhs.sign > 0 && lhs.value <= rhs.value) || (lhs.sign < 0 && lhs.value >= rhs.value))) || lhs.sign < rhs.sign || (lhs.value == 0 && rhs.value == 0);
  }

  //|///////////////////// ge ///////////////////////////////////////////////
  bool operator>=(Int const &lhs, Int const &rhs)
  {
    return (lhs.sign == rhs.sign && ((lhs.sign > 0 && lhs.value >= rhs.value) || (lhs.sign < 0 && lhs.value <= rhs.value))) || lhs.sign > rhs.sign || (lhs.value == 0 && rhs.value == 0);
  }

  //|///////////////////// neg //////////////////////////////////////////////
  Float operator-(Float const &f)
  {
    return { -f.value, f.overflowed };
  }

  //|///////////////////// add //////////////////////////////////////////////
  Float operator+(Float const &lhs, Float const &rhs)
  {
    return { lhs.value + rhs.value, lhs.overflowed || rhs.overflowed };
  }

  //|///////////////////// sub //////////////////////////////////////////////
  Float operator-(Float const &lhs, Float const &rhs)
  {
    return { lhs.value - rhs.value, lhs.overflowed || rhs.overflowed };
  }

  //|///////////////////// div //////////////////////////////////////////////
  Float operator/(Float const &lhs, Float const &rhs)
  {
    return { lhs.value / rhs.value, lhs.overflowed || rhs.overflowed };
  }

  //|///////////////////// mul //////////////////////////////////////////////
  Float operator*(Float const &lhs, Float const &rhs)
  {
    return { lhs.value * rhs.value, lhs.overflowed || rhs.overflowed };
  }

  //|///////////////////// rem //////////////////////////////////////////////
  Float operator%(Float const &lhs, Float const &rhs)
  {
    return { std::fmod(lhs.value, rhs.value), lhs.overflowed || rhs.overflowed };
  }

  //|///////////////////// abs //////////////////////////////////////////////
  Float abs(Float const &lhs)
  {
    return { std::fabs(lhs.value), lhs.overflowed };
  }

  //|///////////////////// trunc ////////////////////////////////////////////
  Float floor(Float const &lhs)
  {
    return { std::floor(lhs.value), lhs.overflowed };
  }

  //|///////////////////// ceil /////////////////////////////////////////////
  Float ceil(Float const &lhs)
  {
    return { std::ceil(lhs.value), lhs.overflowed };
  }

  //|///////////////////// round ////////////////////////////////////////////
  Float round(Float const &lhs)
  {
    return { std::round(lhs.value), lhs.overflowed };
  }

  //|///////////////////// trunc ////////////////////////////////////////////
  Float trunc(Float const &lhs)
  {
    return { std::trunc(lhs.value), lhs.overflowed };
  }

  //|///////////////////// pow //////////////////////////////////////////////
  Float pow(Float const &lhs, Float const &rhs)
  {
    return { std::pow(lhs.value, rhs.value), lhs.overflowed || rhs.overflowed };
  }

  //|///////////////////// sqrt /////////////////////////////////////////////
  Float sqrt(Float const &lhs)
  {
    return { std::sqrt(lhs.value), lhs.overflowed };
  }

  //|///////////////////// lt ///////////////////////////////////////////////
  bool operator<(Float const &lhs, Float const &rhs)
  {
    return lhs.value < rhs.value;
  }

  //|///////////////////// gt ///////////////////////////////////////////////
  bool operator>(Float const &lhs, Float const &rhs)
  {
    return lhs.value > rhs.value;
  }

  //|///////////////////// le ///////////////////////////////////////////////
  bool operator<=(Float const &lhs, Float const &rhs)
  {
    return lhs.value <= rhs.value;
  }

  //|///////////////////// ge ///////////////////////////////////////////////
  bool operator>=(Float const &lhs, Float const &rhs)
  {
    return lhs.value >= rhs.value;
  }

}
