/*********************                                                        */
/*! \file lean_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lean proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF_LEAN_RULES_H
#define CVC4__PROOF_LEAN_RULES_H

#include <iostream>

namespace cvc5 {
namespace proof {
enum class LeanRule : uint32_t
{
  // base
  ASSUME,
  SCOPE,
  CL_ASSUME,
  CL_OR,
  // boolean
  R0,
  R1,
  FACTORING,
  REORDER,
  EQ_RESOLVE,
  MODUS_PONENS,
  NOT_NOT_ELIM,
  CONTRADICTION,
  // cnf
  AND_ELIM,
  AND_INTRO,
  NOT_OR_ELIM,
  IMPLIES_ELIM,
  NOT_IMPLIES1,
  NOT_IMPLIES2,
  EQUIV_ELIM1,
  EQUIV_ELIM2,
  NOT_EQUIV_ELIM1,
  NOT_EQUIV_ELIM2,
  XOR_ELIM1,
  XOR_ELIM2,
  NOT_XOR_ELIM1,
  NOT_XOR_ELIM2,
  ITE_ELIM1,
  ITE_ELIM2,
  NOT_ITE_ELIM1,
  NOT_ITE_ELIM2,
  NOT_AND,
  // tseitin
  CNF_AND_POS,
  CNF_AND_NEG,
  CNF_IMPLIES_POS,
  CNF_IMPLIES_NEG1,
  CNF_IMPLIES_NEG2,
  CNF_EQUIV_POS1,
  CNF_EQUIV_POS2,
  CNF_EQUIV_NEG1,
  CNF_EQUIV_NEG2,
  CNF_XOR_POS1,
  CNF_XOR_POS2,
  CNF_XOR_NEG1,
  CNF_XOR_NEG2,
  CNF_ITE_POS1,
  CNF_ITE_POS2,
  CNF_ITE_POS3,
  CNF_ITE_NEG1,
  CNF_ITE_NEG2,
  CNF_ITE_NEG3,
  // euf
  CONG,
  REFL,
  TRANS,
  SYMM,
  NEG_SYMM,

  // holes
  TRUST,
  TH_TRUST,

  UNKNOWN
};
}
}  // namespace cvc5

#endif /* CVC4__PROOF_LEAN_RULES_H */
