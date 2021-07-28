/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Lean node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__LEAN__LEAN_NODE_CONVERTER_H
#define CVC4__PROOF__LEAN__LEAN_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace proof {

class LeanNodeConverter : public NodeConverter
{
 public:
  LeanNodeConverter();
  ~LeanNodeConverter();
  /** convert to internal */
  Node postConvert(Node n) override;
  /** convert to internal */
  // TypeNode postConvertType(TypeNode tn) override;

  Node mkPrintableOp(Node n);

  /**
   * Make an internal symbol with custom name. This is a BOUND_VARIABLE that
   * has a distinguished status so that it is *not* printed as (bvar ...). The
   * returned variable is always fresh.
   */
  Node mkInternalSymbol(const std::string& name, TypeNode tn);

  /** As above but uses SEXPR type */
  Node mkInternalSymbol(const std::string& name);

 private:
  /** the set of all internally generated symbols */
  std::unordered_set<Node> d_symbols;

  Node d_lbrack;
  Node d_rbrack;
  Node d_choice;
};

}  // namespace proof
}  // namespace cvc5

#endif
