/* kitty: C++ truth table library
 * Copyright (C) 2017-2019  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file ashenhurst_decomposition.hpp
  \brief Given a partition of function arguments, finds all of the ashenhurst decompositions.

  \author Mahyar Emami (mahyar.emami@epfl.ch)
*/

#pragma once

#include <cstdint>

#include "constructors.hpp"
#include "operations.hpp"
#include <bitset>

namespace kitty
{

namespace detail
{

/*! Composes a truth table
  Given a function f represented as f(.), and a set of truth tables as arguments,
  computes the composed truth table.
  For example, if f(x1, x2) = 1001 and vars = {x1 = 1001, x2= 1010} the function
  returns 1000 This function could be viewed as a general operator with arity 
  vars.size() where the behavior of the operator is given by f.
  \param f The outer function
  \param vars The ordered set of input variables
  \return The composed truth table with vars.size() variables
*/
template<class TTf, class TTv>
auto compose_truth_table( const TTf& f, const std::vector<TTv>& vars )
{
  assert( vars.size() == f.num_vars() );
  auto composed = vars[0].construct();
  for ( uint64_t i = 0; i < composed.num_bits(); i++ )
  {

    uint64_t index = 0;
    for ( uint64_t j = 0; j < vars.size(); j++ )
    {
      index += get_bit( vars[j], i ) << j;
    }
    auto bit = get_bit( f, index );
    if ( bit == 1 )
    {
      set_bit( composed, i );
    }
    else
    {
      clear_bit( composed, i );
    }
  }
  return composed;
}
/*! A helper function to enumerate missing indices
  \param ys_index A list of already selected indices
  \param max_index The maximum value for an index
  \return Remaining indices
*/
std::vector<uint32_t>
enumerate_zs_index( const std::vector<uint32_t>& ys_index, uint32_t max_index )
{

  std::vector<uint32_t> zs_index;
  for ( uint32_t i = 0; i <= max_index; i++ )
    if ( std::find( ys_index.begin(), ys_index.end(), i ) == ys_index.end() )
      zs_index.push_back( i );

  return zs_index;
}

} // namespace detail

/*! Is a function ashenhurst decomposable
  Given functions f(.), g(.), and h(.) and a partition
  on arguments into z and y. This function determines whether 
  f(x) is decomposable into g(z, h(y)) where x = union(z,y) and 
  intersect(z, y) = null.
  This function does not check for permutation of variables given by
  zs_index and ys_index. The elements in these vectors are treated as ordered
  values.
  \param tt The function to the check the decomposition on (function f)
  \param zs_index The ordered set of indices of vector x (input to f) that
                  are the inputs to outer_func (g).
  \param ys_index The ordered set of indices of vector x (input to f) that are
                  input to the inner_func (h).
  \param outer_func The outer decomposition function (function g).
  \param inner_func The inner decomposition function (function h).
  \return true if the given decomposition is a valid one, false otherwise.
*/
template<class TTf, class TTg, class TTh>
bool ashenhurst_decomposable( const TTf& tt,
                              const std::vector<uint32_t>& zs_index,
                              const std::vector<uint32_t>& ys_index,
                              const TTg& outer_func,
                              const TTh& inner_func )
{
  std::vector<TTf> y_vars;
  std::vector<TTf> z_vars;

  for ( const auto idx : ys_index )
  {
    auto var = tt.construct();
    create_nth_var( var, idx );
    y_vars.push_back( var );
  }
  for ( const auto idx : zs_index )
  {
    auto var = tt.construct();
    create_nth_var( var, idx );
    z_vars.push_back( var );
  }
  auto h = detail::compose_truth_table( inner_func, y_vars );
  z_vars.push_back( h );
  auto f = detail::compose_truth_table( outer_func, z_vars );
  return equal( f, tt );
}

/*! Finds all of the possible decompositions of a function given an input 
  partitioning.

  \param tt The function to find all of its decompositions 
  \param ys_index Indices indicating the partitioning of inputs
  \param decomposition A vector of decomposition pairs. This serves as a return
                       return container.
  \return Returns the number of possible decompositions.
*/
template<class TTf, class TTg, class TTh>
int ashenhurst_decomposition( const TTf& tt, const std::vector<uint32_t>& ys_index, std::vector<std::pair<TTg, TTh>>& decomposition )
{
  std::vector<uint32_t> zs_index = detail::enumerate_zs_index( ys_index, tt.num_vars() - 1 );
  decomposition.clear();
  // g_contradiction and h_contradiction are unsatisfiable functions.
  TTg g, g_contradiction;
  do
  {
    TTh h, h_contradiction;
    do
    {
      if ( ashenhurst_decomposable( tt, zs_index, ys_index, g, h ) )
        decomposition.push_back( std::make_pair( g, h ) );
      next_inplace( h );
    } while ( !equal( h, h_contradiction ) );
    next_inplace( g );
  } while ( !equal( g, g_contradiction ) );
  return decomposition.size();
}
template <class TT>
bool is_bad_pair(const TT& tt, const std::tuple<uint32_t, uint32_t, uint32_t>& partition, uint32_t retry = 50) {
  std::array<std::pair<uint64_t, bool>, 8> delta_array;
  uint64_t i, j, m;
  std::tie(i, j, m) = partition;
  dynamic_truth_table index(3);
  assert(i < tt.num_vars());
  assert(j < tt.num_vars());
  assert(m < tt.num_vars());
  assert(i < j);  
  for (auto& pair : delta_array){
    auto& delta = pair.first;
    delta = 0u;
    // Since delta is a sparse bit vector (3 non zero at most) there is room for optimization.
    if (get_bit(index, 0))
      delta |= uint64_t (1) << i;
    if (get_bit(index, 1))
      delta |= uint64_t (1) << j;
    if (get_bit(index, 2))
      delta |= uint64_t (1) << m;
    next_inplace(index);
  }
  std::random_device dev;
  std::mt19937 rand_gen(dev());
  std::uniform_int_distribution<uint64_t> random_x(0, uint64_t(1) << tt.num_vars());
  std::array<uint8_t, 4> pairs;
  for (int c = 0; c < retry; c ++){
    uint64_t x = random_x(rand_gen);
    for (auto& pair : delta_array)
      pair.second = get_bit(tt, x ^ pair.first) > 0;
    pairs[0] = delta_array[0].second + delta_array[1].second << 1;
    pairs[1] = delta_array[2].second + delta_array[3].second << 1;
    pairs[2] = delta_array[3].second + delta_array[5].second << 1;
    pairs[3] = delta_array[4].second + delta_array[7].second << 1;
    std::vector<uint8_t> values;
    for (const auto& pair : pairs)
      if (std::find(values.begin(), values.end(), pair) == values.end())
        values.push_back(pair);
    
    if (values.size() <= 2) //Need to try more
      continue;
    else 
      return true;
  }
  return false;

}
} // namespace kitty
