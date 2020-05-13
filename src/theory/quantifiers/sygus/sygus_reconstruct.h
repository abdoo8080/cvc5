/*********************                                                        */
/*! \file sygus_reconstruct.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for reconstructing terms to match a grammar
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_RECONSTRUCT_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_RECONSTRUCT_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** SygusReconstruct
 *
 */
class SygusReconstruct
{

 public:
  SygusReconstruct(TermDbSygus* tds);
  ~SygusReconstruct(){}
  /** reconstruct solution
   *
   * Returns (if possible) a node that is equivalent to sol whose syntax
   * matches the grammar corresponding to sygus datatype stn.
   * The value reconstructed is set to 1 if we successfully return a node,
   * otherwise it is set to -1.
   * 
   * @param sol The target term.
   * @param stn The sygus datatype type encoding the syntax restrictions,
   * @param reconstructed The flag to update, indicating the status of the
   * reconstruciton,
   * @param enumLimit A value to limit the effort spent by this class (roughly
   * equal to the number of intermediate terms to try).
   * @return The reconstructed term.
   * 
   * For example, given:
   *   sol = (MULT 2 x) 
   *   stn = A sygus datatype encoding the grammar 
   *           Start -> (PLUS Start Start) | x | 0 | 1
   * This method may return (PLUS x x) and set reconstructed to 1.
   */
  Node reconstructSolution(Node sol,
                           TypeNode stn,
                           int& reconstructed,
                           int enumLimit);
private:
  /** pointer to the sygus term database */
  TermDbSygus* d_tds;
};

}
}
}

#endif
