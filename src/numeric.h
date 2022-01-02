//
// numeric.h
//
// Copyright (C) 2020-2022 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include <iostream>
#include <string_view>
#include <cassert>

namespace Numeric
{
  //|--------------------- Numeric ------------------------------------------
  //|------------------------------------------------------------------------

  struct Int
  {
    int sign;
    uint64_t value;
    bool overflowed;
    bool maybe_unsigned;
  };

  Int parse_int_literal(int sign, std::string_view str);
  Int parse_bin_int_literal(int sign, std::string_view str);
  Int parse_oct_int_literal(int sign, std::string_view str);
  Int parse_hex_int_literal(int sign, std::string_view str);
  Int parse_dec_int_literal(int sign, std::string_view str);
  Int parse_char_literal(std::string_view str);

  struct Float
  {
    double value;
    bool overflowed;
  };

  Float parse_float_literal(int sign, std::string_view str);
  Float parse_hex_float_literal(int sign, std::string_view str);
  Float parse_dec_float_literal(int sign, std::string_view str);

  // misc

  bool is_int_literal(std::string_view str);
  bool is_char_literal(std::string_view str);
  bool is_float_literal(std::string_view str);

  inline Int int_literal(int64_t value)
  {
    return Int{ (value < 0) ? -1 : +1, static_cast<uint64_t>(std::abs(value)), false, false };
  }

  inline Int int_literal(int sign, uint64_t value)
  {
    return Int{ sign, value, false, false };
  }

  inline bool operator==(Int const &lhs, Int const &rhs)
  {
    return (lhs.sign == rhs.sign && lhs.value == rhs.value) || (lhs.value == 0 && rhs.value == 0);
  }

  inline bool operator!=(Int const &lhs, Int const &rhs)
  {
    return !(lhs == rhs);
  }

  Int operator-(Int const &i);
  Int operator+(Int const &lhs, Int const &rhs);
  Int operator-(Int const &lhs, Int const &rhs);
  Int operator/(Int const &lhs, Int const &rhs);
  Int operator*(Int const &lhs, Int const &rhs);
  Int operator%(Int const &lhs, Int const &rhs);
  Int operator<<(Int const &lhs, Int const &rhs);
  Int operator>>(Int const &lhs, Int const &rhs);
  Int operator~(Int const &i);
  Int operator&(Int const &lhs, Int const &rhs);
  Int operator|(Int const &lhs, Int const &rhs);
  Int operator^(Int const &lhs, Int const &rhs);

  Int abs(Int const &lhs);
  Int pow(Int const &lhs, Int const &rhs);
  Int sqrt(Int const &lhs);

  void add_with_carry(Int const &lhs, Int const &rhs, size_t width, bool is_signed, Int &lo, Int &hi);
  void sub_with_borrow(Int const &lhs, Int const &rhs, size_t width, bool is_signed, Int &lo, Int &hi);
  void mul_with_carry(Int const &lhs, Int const &rhs, size_t width, bool is_signed, Int &lo, Int &hi);

  bool operator<(Int const &lhs, Int const &rhs);
  bool operator>(Int const &lhs, Int const &rhs);
  bool operator<=(Int const &lhs, Int const &rhs);
  bool operator>=(Int const &lhs, Int const &rhs);

  inline Float float_literal(double value)
  {
    return Float{ value, false };
  }

  inline bool operator==(Float const &lhs, Float const &rhs)
  {
    return lhs.value == rhs.value;
  }

  inline bool operator!=(Float const &lhs, Float const &rhs)
  {
    return lhs.value != rhs.value;
  }

  Float operator-(Float const &f);
  Float operator+(Float const &lhs, Float const &rhs);
  Float operator-(Float const &lhs, Float const &rhs);
  Float operator/(Float const &lhs, Float const &rhs);
  Float operator*(Float const &lhs, Float const &rhs);
  Float operator%(Float const &lhs, Float const &rhs);

  Float abs(Float const &lhs);
  Float floor(Float const &lhs);
  Float ceil(Float const &lhs);
  Float round(Float const &lhs);
  Float trunc(Float const &lhs);
  Float pow(Float const &lhs, Float const &rhs);
  Float sqrt(Float const &lhs);

  bool operator<(Float const &lhs, Float const &rhs);
  bool operator>(Float const &lhs, Float const &rhs);
  bool operator<=(Float const &lhs, Float const &rhs);
  bool operator>=(Float const &lhs, Float const &rhs);

  template<typename As>
  Int int_cast(Int const &i)
  {
    auto value = static_cast<As>(i.sign * i.value);

    if (value < 0)
      return int_literal(-1, static_cast<uint64_t>(-value));
    else
      return int_literal(+1, static_cast<uint64_t>(+value));
  }

  template<typename As>
  Int int_cast(Float const &f)
  {
    auto value = static_cast<As>(f.value);

    if (value < 0)
      return int_literal(-1, static_cast<uint64_t>(-value));
    else
      return int_literal(+1, static_cast<uint64_t>(+value));
  }

  template<typename As>
  Float float_cast(Int const &i)
  {
    return float_literal(i.sign * static_cast<As>(i.value));
  }

  inline std::ostream &operator <<(std::ostream &os, Int const &i)
  {
    if (i.sign < 0)
      os << '-';

    os << i.value;

    return os;
  }

  inline std::ostream &operator <<(std::ostream &os, Float const &f)
  {
    os << f.value;

    return os;
  }
}

