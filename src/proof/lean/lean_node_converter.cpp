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
  LeanNodeConverter();
  ~LeanNodeConverter();
  /** convert to internal */
  Node postConvert(Node n) override;
  /** convert to internal */
  TypeNode postConvertType(TypeNode tn) override;
};

}  // namespace proof
}  // namespace cvc5

#endif
