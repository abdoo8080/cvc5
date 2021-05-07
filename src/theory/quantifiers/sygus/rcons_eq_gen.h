/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * utility class for Sygus Reconstruct module.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__RCONS_EQ_GEN_H
#define CVC5__THEORY__QUANTIFIERS__RCONS_EQ_GEN_H

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

class RConsEqGen
{
 public:
  void static getEquivalentTerms(Kind k, Node n, std::vector<Node>& equiv);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif  // CVC5__THEORY__QUANTIFIERS__RCONS_EQ_GEN_H
