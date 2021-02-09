//
// util.h
//
// Copyright (C) 2020 Peter Niekamp. All rights reserved.
//
// This file is part of zaalang, which is BSD-2-Clause licensed.
// See http://opensource.org/licenses/BSD-2-Clause
//

#pragma once

#include <string>
#include <vector>
#include <tuple>
#include <utility>
#include <iterator>
#include <charconv>

//-------------------------- iterator_pair ----------------------------------
//---------------------------------------------------------------------------

template<typename I1, typename I2>
class iterator_pair : public std::pair<I1, I2>
{
  public:
    using std::pair<I1, I2>::pair;

    iterator_pair(I1 const &beg, I2 const &end)
      : std::pair<I1, I2>(beg, end)
    {
    }

    I1 begin() const { return this->first; }
    I2 end() const { return this->second; }
};


//-------------------------- skip_iterator ----------------------------------
//---------------------------------------------------------------------------

template<typename Iterator, typename EndIterator, typename Predicate>
class skip_iterator
{
  public:
    explicit skip_iterator(Iterator iterator, EndIterator end, Predicate skip)
      : iterator(iterator), end(end), skip(skip)
    {
      if (iterator != end && skip(*iterator))
        ++*this;
    }

    bool operator ==(skip_iterator const &that) const { return iterator == that.iterator; }
    bool operator !=(skip_iterator const &that) const { return iterator != that.iterator; }

    bool operator ==(Iterator const &that) const { return iterator == that; }
    bool operator !=(Iterator const &that) const { return iterator != that; }

    auto &operator *() const { return *iterator; }
    auto *operator ->() const { return &*iterator; }

    skip_iterator &operator++()
    {
      ++iterator;

      while (iterator != end && skip(*iterator))
        ++iterator;

      return *this;
    }

    Iterator iterator;
    EndIterator end;
    Predicate skip;
};

//-------------------------- zip_iterator -----------------------------------
//---------------------------------------------------------------------------

template<typename ...Iterators>
class zip_iterator
{
  public:
    explicit zip_iterator(Iterators ...iterators)
      : iterators(iterators...)
    {
    }

    template<typename ...Uterators>
    bool operator ==(zip_iterator<Uterators...> const &that) const { return iterators == that.iterators;  }

    template<typename ...Uterators>
    bool operator !=(zip_iterator<Uterators...> const &that) const { return !(*this == that); }

    auto operator *() const { return std::apply([](auto& ...i) { return std::tie(*i...); }, iterators); }
    auto operator ->() const { return iterators; }

    zip_iterator &operator++()
    {
      std::apply([](auto& ...i) { (++i, ...); }, iterators);

      return *this;
    }

    std::tuple<Iterators...> iterators;
};

template<typename ...Containters>
auto zip(Containters && ...containers)
{
  return iterator_pair(zip_iterator(containers.begin()...), zip_iterator(containers.end()...));
}


//-------------------------- escape -----------------------------------------
//---------------------------------------------------------------------------

inline std::string escape(std::string_view str)
{
  std::string result;

  result.reserve(str.length());

  for(auto ch = str.begin(), end = str.end(); ch != end; ++ch)
  {
    switch(*ch)
    {
      case '\a':
        result += "\\a";
        continue;

      case '\f':
        result += "\\f";
        continue;

      case '\n':
        result += "\\n";
        continue;

      case '\r':
        result += "\\r";
        continue;

      case '\t':
        result += "\\t";
        continue;

      case '\v':
        result += "\\v";
        continue;

      case '"':
        result += "\\\"";
        continue;

      case '\\':
        result += "\\\\";
        continue;

      case 0:
        result += "\\0";
        continue;

      case 1: case 2: case 3: case 4: case 5: case 6: case 8:
        result += "\\x0";
        result += char(ch[0] + '0');
        continue;

      case 14: case 15:
        result += "\\x0";
        result += char(ch[0] - 10 + 'a');
        continue;

      case 16: case 17: case 18: case 19: case 20: case 21: case 22: case 23: case 24: case 25:
        result += "\\x1";
        result += char(ch[0] - 16 + '0');
        continue;

      case 26: case 27: case 28: case 29: case 30: case 31:
        result += "\\x1";
        result += char(ch[0] - 26 + 'a');
        continue;

      case 127:
        result += "\\x7f";
        continue;

      default:
        break;
    }

    result += *ch;
  }

  return result;
}

//-------------------------- unescape ---------------------------------------
//---------------------------------------------------------------------------

inline std::string unescape(std::string_view str)
{
  std::string result;

  result.reserve(str.length());

  for(auto ch = str.data(), end = str.data() + str.size(); ch != end; ++ch)
  {
    if (*ch == '\\')
    {
      switch(*++ch)
      {
        case 'a':
          result += '\a';
          continue;

        case 'f':
          result += '\f';
          continue;

        case 'n':
          result += '\n';
          continue;

        case 'r':
          result += '\r';
          continue;

        case 't':
          result += '\t';
          continue;

        case 'v':
          result += '\v';
          continue;

        case '\'':
          result += '\'';
          continue;

        case '"':
          result += '"';
          continue;

        case '\\':
          result += '\\';
          continue;

        case '0':
          result += char(0);
          continue;

        case 'x': {
          int cc;
          ch = std::from_chars(ch+1, std::min(ch+3, end), cc, 16).ptr - 1;
          result += char(cc);
          continue;
        }

        default:
          break;
      }
    }

    result += *ch;
  }

  return result;
}

//-------------------------- dirname ----------------------------------------
//---------------------------------------------------------------------------

inline std::string dirname(std::string_view path)
{
#if defined _WIN32
  auto j = path.find_last_of(":\\/");
#else
  auto j = path.find_last_of('/');
#endif

  if (j != std::string_view::npos)
    j += 1;
  else
    j = 0;

  return std::string(path.substr(0, j));
}

//-------------------------- basename ---------------------------------------
//---------------------------------------------------------------------------

inline std::string basename(std::string_view path)
{
#if defined _WIN32
  auto i = path.find_last_of(":\\/");
#else
  auto i = path.find_last_of('/');
#endif

  if (i != std::string_view::npos)
    i += 1;
  else
    i = 0;

  auto j = path.find_last_of('.');

  if (j == std::string_view::npos)
    j = path.length();

  return std::string(path.substr(i, j - i));
}
