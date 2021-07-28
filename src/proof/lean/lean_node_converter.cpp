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

#include "expr/skolem_manager.h"
#include "proof/proof_checker.h"

#include <sstream>

namespace cvc5 {
namespace proof {

LeanNodeConverter::LeanNodeConverter() {
  NodeManager* nm = NodeManager::currentNM();
  d_lbrack =
      nm->mkNode(kind::SEXPR,
                 nm->getSkolemManager()->mkDummySkolem(
                     "[", nm->sExprType(), "", NodeManager::SKOLEM_EXACT_NAME));
  d_rbrack =
      nm->mkNode(kind::SEXPR,
                 nm->getSkolemManager()->mkDummySkolem(
                     "]", nm->sExprType(), "", NodeManager::SKOLEM_EXACT_NAME));
  d_choice =
      nm->mkNode(kind::SEXPR,
                 nm->getSkolemManager()->mkDummySkolem(
                     "choice", nm->sExprType(), "", NodeManager::SKOLEM_EXACT_NAME));
}
LeanNodeConverter::~LeanNodeConverter() {}

Node LeanNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  TypeNode tn = n.getType();
  size_t nChildren = n.getNumChildren();
  switch (k)
  {
    case kind::WITNESS:
    {
      Node var = n[0][0];
      out << "choice " << var.getId() << " ";
      printTerm(out, n[1]);
      break;
    }
    case kind::APPLY_UF:
    {
      Node op = n.getOperator();
      Assert(nChildren >= 1);
      if (nChildren > 1)
      {
        out << "appN ";
        printTerm(out, op);
        out << " ";
        printTermList(out, n);
      }
      else
      {
        // out << "mkApp ";
        out << "app ";
        printTerm(out, op);
        out << " ";
        printTerm(out, n[0]);
      }
      break;
    }
    case kind::EQUAL:
    {
      // out << "mkEq ";
      out << "eq ";
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      break;
    }
    case kind::XOR:
    {
      // out << "mkXor ";
      out << "xor ";
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      break;
    }
    case kind::OR:
    {
      Assert(nChildren >= 2);
      if (nChildren > 2)
      {
        out << "orN ";
        printTermList(out, n);
      }
      else
      {
        // out << "mkOr ";
        out << "term.or ";
        printTerm(out, n[0]);
        out << " ";
        printTerm(out, n[1]);
      }
      break;
    }
    case kind::AND:
    {
      Assert(nChildren >= 2);
      if (nChildren > 2)
      {
        out << "andN ";
        printTermList(out, n);
      }
      else
      {
        // out << "mkAnd ";
        out << "term.and ";
        printTerm(out, n[0]);
        out << " ";
        printTerm(out, n[1]);
      }
      break;
    }
    case kind::IMPLIES:
    {
      // out << "mkImplies ";
      out << "implies ";
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      break;
    }
    case kind::NOT:
    {
      // out << "mkNot ";
      out << "term.not ";
      printTerm(out, n[0]);
      break;
    }
    case kind::ITE:
    {
      // out << "mkIte ";
      out << "fIte ";
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      out << " ";
      printTerm(out, n[2]);
      break;
    }
    case kind::DISTINCT:
    {
      out << "distinct ";
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      break;
    }
    case kind::SELECT:
    {
      out << "select ";
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      break;
    }
    case kind::STORE:
    {
      out << "store ";
      printTerm(out, n[0]);
      out << " ";
      printTerm(out, n[1]);
      out << " ";
      printTerm(out, n[2]);
      break;
    }
    case kind::SEXPR:
    {
      out << "[";
      printTerm(out, nc[0]);
      for (size_t i = 1, size = n.getNumChildren(); i < size; ++i)
      {
        out << ", ";
        printTerm(out, n[i]);
      }
      out << "]";
      break;
    }
    case kind::STRING_LENGTH:
    {
      out << "mkLength ";
      printTerm(out, n[0]);
      break;
    }
    default: Unreachable() << " Unhandled kind: " << k << "\n";
  }

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
