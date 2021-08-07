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

#include <sstream>

#include "expr/skolem_manager.h"
#include "proof/proof_checker.h"
#include "util/bitvector.h"
#include "util/string.h"

namespace cvc5 {
namespace proof {

std::unordered_map<Kind, std::string> s_kindToString = {
  {kind::BITVECTOR_CONCAT, "bvConcat"},
  {kind::BITVECTOR_AND, "bvAnd"},
  {kind::BITVECTOR_ADD, "bvAdd"},
  {kind::BITVECTOR_SUB, "bvSub"},
  {kind::BITVECTOR_ULT, "bvUlt"},
  {kind::BITVECTOR_ULE, "bvUle"},
  {kind::ITE, "fIte"},
  {kind::SELECT, "select"},
  {kind::STORE, "store"},
  {kind::NOT, "term.not"},
  {kind::STRING_LENGTH, "mkLength"},
  {kind::EQUAL, "eq"},
  {kind::XOR, "xor"},
  {kind::IMPLIES, "implies"},
  {kind::DISTINCT, "distinct"},
};

// have underlying node converter *not* force type preservation
LeanNodeConverter::LeanNodeConverter() : NodeConverter(true, false)
{
  d_brack[0] = mkInternalSymbol("__LEAN_TMP[");
  d_brack[1] = mkInternalSymbol("__LEAN_TMP]");
  d_comma = mkInternalSymbol("__LEAN_TMP,");
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}
LeanNodeConverter::~LeanNodeConverter() {}

bool LeanNodeConverter::shouldTraverse(Node n)
{
  Kind k = n.getKind();
  // don't convert bound variable list directly
  if (k == kind::BOUND_VAR_LIST)
  {
    return false;
  }
  return true;
}

Node LeanNodeConverter::preConvert(Node n)
{
  Kind k = n.getKind();
  NodeManager* nm = NodeManager::currentNM();
  if (k == kind::SKOLEM || k == kind::BOOLEAN_TERM_VARIABLE)
  {
    Node wi = SkolemManager::getWitnessForm(n);
    // true skolem with witness form, just convert that
    if (!wi.isNull())
    {
      Trace("test-lean") << "LeanNodeConverter::postConvert: skolem " << n
                         << " has witness form " << wi << "\n";
      return convert(wi);
    }
    // purification skolem, thus we need to build the fake choice term
    AlwaysAssert(!SkolemManager::getOriginalForm(n).isNull());
    return nm->mkNode(kind::SEXPR,
                      mkInternalSymbol("choice"),
                      nm->mkConst<Rational>(0),
                      convert(SkolemManager::getOriginalForm(n)));
  }
  size_t nChildren = n.getNumChildren();
  std::vector<Node> resChildren;
  switch (k)
  {
    case kind::BOUND_VARIABLE:
    {
      // don't convert internally generated
      if (d_symbols.find(n) != d_symbols.end())
      {
        return n;
      }
      // variables are (const id type)
      resChildren.push_back(mkInternalSymbol("const"));
      resChildren.push_back(nm->mkConst<Rational>(static_cast<int>(n.getId())));
      resChildren.push_back(typeAsNode(n.getType()));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::CONST_BOOLEAN:
    {
      return n.getConst<bool>() ? mkInternalSymbol("top")
                                : mkInternalSymbol("bot");
    }
    case kind::CONST_RATIONAL:
    {
      TypeNode tn = n.getType();
      AlwaysAssert(tn.isInteger()) << "Only support integer rationals\n";
      resChildren.push_back(mkInternalSymbol("val"));
      resChildren.push_back(
          nm->mkNode(kind::SEXPR, mkInternalSymbol("value.integer"), n));
      resChildren.push_back(typeAsNode(tn));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::CONST_BITVECTOR:
    {
      resChildren.push_back(mkInternalSymbol("val"));
      // create list of booleans with bits, by checking if each bit is set and
      // putting top or bottom into the list
      BitVector bv = n.getConst<BitVector>();

      std::vector<Node> bits;
      for (size_t i = 0, size = bv.getSize(); i < size; ++i)
      {
        bits.push_back(mkInternalSymbol(bv.isBitSet(i) ? "top" : "bot"));
      }
      resChildren.push_back(nm->mkNode(kind::SEXPR,
                                       mkInternalSymbol("value.bitvec"),
                                       convert(nm->mkNode(kind::SEXPR, bits))));
      resChildren.push_back(typeAsNode(n.getType()));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    // case kind::CONST_STRING:
    // {
    //   resChildren.push_back(mkInternalSymbol("mkVarChars"));
    //   resChildren.push_back(d_brack[0]);
    //   cvc5::String str = n.getConst<String>();
    //   for (size_t i = 0, size = str.size(); i < size; ++i)
    //   {
    //     resChildren.push_back(str[i]);
    //     resChildren.push_back(mkInternalSymbol(i < size - 1 ? ", " : "]"));
    //   }
    //   return nm->mkNode(kind::SEXPR, resChildren);
    // }
    case kind::FORALL:
    case kind::LAMBDA:
    {
      Node binderOp = mkInternalSymbol(s_kindToString[k]);
      size_t nVars = n[0].getNumChildren();
      // iterate over variables, from last to second, and build layered binding
      Node curChild = convert(n[1]);
      Node convertedVar;
      for (size_t i = 0; i < nVars; ++i)
      {
        convertedVar = convert(n[0][nVars - i]);
        // add the id, which should be the second child, since converted var
        // should be (SEXPR "const" id _)
        AlwaysAssert(convertedVar.getKind() == kind::SEXPR
                     && convertedVar.getNumChildren() == 3);
        curChild = nm->mkNode(kind::SEXPR, binderOp, convertedVar[1], curChild);
      }
      return curChild;
    }
    case kind::WITNESS:
    {
      resChildren.push_back(mkInternalSymbol("choice"));
      // Since variable lists are not converted, we do it here
      AlwaysAssert(n[0].getKind() == kind::BOUND_VAR_LIST
                   && n[0].getNumChildren() == 1);
      Node convertedVar = convert(n[0][0]);
      // add the id, which should be the second child, since converted var
      // should be (SEXPR "const" id _)
      AlwaysAssert(convertedVar.getKind() == kind::SEXPR
                   && convertedVar.getNumChildren() == 3);
      resChildren.push_back(convertedVar[1]);
      // convert the body
      resChildren.push_back(convert(n[1]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::APPLY_UF:
    {
      Node op = n.getOperator();
      Assert(nChildren >= 1);
      if (nChildren > 1)
      {
        resChildren.push_back(mkInternalSymbol("appN"));
        resChildren.push_back(convert(op));
        resChildren.push_back(d_brack[0]);
        for (size_t i = 0; i < nChildren; ++i)
        {
          resChildren.push_back(convert(n[i]));
          if (i < nChildren - 1)
          {
            resChildren.push_back(d_comma);
          }
        }
        resChildren.push_back(d_brack[1]);
      }
      else
      {
        resChildren.push_back(mkInternalSymbol("app"));
        resChildren.push_back(convert(op));
        resChildren.push_back(convert(n[0]));
      }
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    // binary operators
    case kind::BITVECTOR_CONCAT:
    case kind::BITVECTOR_AND:
    case kind::BITVECTOR_ADD:
    case kind::BITVECTOR_SUB:
    case kind::BITVECTOR_ULT:
    case kind::BITVECTOR_ULE:
    case kind::EQUAL:
    case kind::XOR:
    case kind::IMPLIES:
    case kind::DISTINCT:
    case kind::SELECT:
    {
      resChildren.push_back(mkInternalSymbol(s_kindToString[k]));
      resChildren.push_back(convert(n[0]));
      resChildren.push_back(convert(n[1]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    // unary
    case kind::NOT:
    case kind::STRING_LENGTH:
    {
      resChildren.push_back(mkInternalSymbol("term.not"));
      resChildren.push_back(convert(n[0]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    // ternary
    case kind::ITE:
    case kind::STORE:
    {
      resChildren.push_back(mkInternalSymbol(s_kindToString[k]));
      resChildren.push_back(convert(n[0]));
      resChildren.push_back(convert(n[1]));
      resChildren.push_back(convert(n[2]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    // n-ary ones
    case kind::OR:
    {
      if (nChildren > 2)
      {
        resChildren.push_back(mkInternalSymbol("orN"));
        resChildren.push_back(d_brack[0]);
        for (size_t i = 0; i < nChildren; ++i)
        {
          resChildren.push_back(convert(n[i]));
          if (i < nChildren - 1)
          {
            resChildren.push_back(d_comma);
          }
        }
        resChildren.push_back(d_brack[1]);
      }
      else
      {
        resChildren.push_back(mkInternalSymbol("term.or"));
        resChildren.push_back(convert(n[0]));
        resChildren.push_back(convert(n[1]));
      }
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::AND:
    {
      if (nChildren > 2)
      {
        resChildren.push_back(mkInternalSymbol("andN"));
        resChildren.push_back(d_brack[0]);
        for (size_t i = 0; i < nChildren; ++i)
        {
          resChildren.push_back(convert(n[i]));
          if (i < nChildren - 1)
          {
            resChildren.push_back(d_comma);
          }
        }
        resChildren.push_back(d_brack[1]);
      }
      else
      {
        resChildren.push_back(mkInternalSymbol("term.and"));
        resChildren.push_back(convert(n[0]));
        resChildren.push_back(convert(n[1]));
      }
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    // clauses
    case kind::SEXPR:
    {
      resChildren.push_back(d_brack[0]);
      for (size_t i = 0; i < nChildren; ++i)
      {
        resChildren.push_back(convert(n[i]));
        if (i < nChildren - 1)
        {
          resChildren.push_back(d_comma);
        }
      }
      resChildren.push_back(d_brack[1]);
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    default:
    {
      Unreachable() << "Have to convert everything, but " << n << " escaped\n";
    }
  }
  return n;
}

Node LeanNodeConverter::mkPrintableOp(Node n)
{
  Kind k;
  if (!ProofRuleChecker::getKind(n, k))
  {
    return n;
  }
  return mkPrintableOp(k);
}

Node LeanNodeConverter::mkPrintableOp(Kind k)
{
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
      return mkInternalSymbol("fIteConst");
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
    case kind::BITVECTOR_CONCAT:
    {
      return mkInternalSymbol("bvConcatConst");
    }
    case kind::BITVECTOR_AND:
    {
      return mkInternalSymbol("bvAndConst");
    }
    case kind::BITVECTOR_ADD:
    {
      return mkInternalSymbol("bvAddConst");
    }
    case kind::BITVECTOR_SUB:
    {
      return mkInternalSymbol("bvSubConst");
    }
    case kind::BITVECTOR_ULT:
    {
      return mkInternalSymbol("bvUltConst");
    }
    case kind::BITVECTOR_ULE:
    {
      return mkInternalSymbol("bvUleConst");
    }
    default:
    {
      Trace("test-lean") << "non-handled kind " << k << "\n";
    }
  }
  return Node::null();
}

Node LeanNodeConverter::typeAsNode(TypeNode tn)
{
  std::map<TypeNode, Node>::const_iterator it = d_typeAsNode.find(tn);
  if (it != d_typeAsNode.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  // convert
  Node res;
  std::vector<Node> resChildren;
  // functional sort
  if (tn.isFunction())
  {
    resChildren.push_back(mkInternalSymbol("arrowN"));
    resChildren.push_back(d_brack[0]);
    // convert each argument
    size_t size = tn.getNumChildren();
    for (size_t i = 0; i < size - 1; ++i)
    {
      resChildren.push_back(typeAsNode(tn[i]));
      resChildren.push_back(d_comma);
    }
    // return sort
    resChildren.push_back(typeAsNode(tn[size - 1]));
    resChildren.push_back(d_brack[1]);
    res = nm->mkNode(kind::SEXPR, resChildren);
  }
  else if (tn.isArray())
  {
    resChildren.push_back(mkInternalSymbol("array"));
    resChildren.push_back(typeAsNode(tn.getArrayIndexType()));
    resChildren.push_back(typeAsNode(tn.getArrayConstituentType()));
    res = nm->mkNode(kind::SEXPR, resChildren);
  }
  else if (tn.isBoolean())
  {
    res = mkInternalSymbol("boolSort");
  }
  else if (tn.isInteger())
  {
    res = mkInternalSymbol("intSort");
  }
  else if (tn.isBitVector())
  {
    res = nm->mkNode(
        kind::SEXPR,
        mkInternalSymbol("bv"),
        mkInternalSymbol(nm->mkConst<Rational>(tn.getBitVectorSize())));
  }
  else
  {
    std::stringstream ss;
    tn.toStream(ss, language::output::LANG_SMTLIB_V2_6);
    res = mkInternalSymbol(ss.str());
  }
  d_typeAsNode[tn] = res;
  return res;
}

Node LeanNodeConverter::mkInternalSymbol(const std::string& name)
{
  std::unordered_map<std::string, Node>::iterator it = d_symbolsMap.find(name);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node sym = nm->mkBoundVar(name, nm->sExprType());
  d_symbols.insert(sym);
  d_symbolsMap[name] = sym;
  return sym;
}

Node LeanNodeConverter::mkInternalSymbol(TNode n)
{
  std::stringstream ss;
  if (n.getKind() == kind::CONST_RATIONAL)
  {
    ss << "__LEAN_TMP";
  }
  n.toStream(ss, -1, 0, language::output::LANG_SMTLIB_V2_6);
  return mkInternalSymbol(ss.str());
}


}  // namespace proof
}  // namespace cvc5
