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
      case '\n':
        result += "\\n";
        continue;

      case '\r':
        result += "\\r";
        continue;

      case '\t':
        result += "\\t";
        continue;

      case '"':
        result += "\\\"";
        continue;

      case '\\':
        result += "\\\\";
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

  for(auto ch = str.begin(), end = str.end(); ch != end; ++ch)
  {
    if (*ch == '\\')
    {
      switch(*++ch)
      {
        case 'n':
          result += '\n';
          continue;

        case 'r':
          result += '\r';
          continue;

        case 't':
          result += '\t';
          continue;

        case '"':
          result += '"';
          continue;

        case '\\':
          result += '\\';
          continue;

        default:
          break;
      }
    }

    result += *ch;
  }

  return result;
}