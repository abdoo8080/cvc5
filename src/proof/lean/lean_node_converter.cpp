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
 * Lean node conversion utility
 */
#include "proof/lean/lean_node_converter.h"

#include "proof/proof_checker.h"

#include <sstream>

namespace cvc5 {
namespace proof {

LeanNodeConverter::LeanNodeConverter() {}
LeanNodeConverter::~LeanNodeConverter() {}

Node LeanNodeConverter::postConvert(Node n)
{
  return Node::null();
}

Node LeanNodeConverter::mkPrintableOp(Node n)
{
  Kind k;
  if (!ProofRuleChecker::getKind(n, k))
  {
    return n;
  }
  switch (k)
  {
    case kind::NOT:
    {
      return mkInternalSymbol("notConst");
    }
    case kind::EQUAL:
    {
      return mkInternalSymbol("eqConst");
    }
    case kind::OR:
    {
      return mkInternalSymbol("orConst");
    }
    case kind::AND:
    {
      return mkInternalSymbol("andConst");
    }
    case kind::XOR:
    {
      return mkInternalSymbol("xorConst");
    }
    case kind::IMPLIES:
    {
      return mkInternalSymbol("impliesConst");
    }
    case kind::ITE:
    {
      return mkInternalSymbol("fteConst");
    }
    case kind::PLUS:
    {
      return mkInternalSymbol("plusConst");
    }
    case kind::MINUS:
    {
      return mkInternalSymbol("minusConst");
    }
    case kind::SELECT:
    {
      return mkInternalSymbol("selectConst");
    }
    case kind::STORE:
    {
      return mkInternalSymbol("storeConst");
    }
    default:
    {
      Trace("test-lean") << "non-handled kind " << k << "\n";
    }
  }
  return n;
}

Node LeanNodeConverter::mkInternalSymbol(const std::string& name)
{
  NodeManager* nm = NodeManager::currentNM();
  Node sym = nm->mkBoundVar(name, nm->sExprType());
  d_symbols.insert(sym);
  return sym;
}

Node LeanNodeConverter::mkInternalSymbol(const std::string& name, TypeNode tn)
{
  Node sym = NodeManager::currentNM()->mkBoundVar(name, tn);
  d_symbols.insert(sym);
  return sym;
}

}  // namespace proof
}  // namespace cvc5
