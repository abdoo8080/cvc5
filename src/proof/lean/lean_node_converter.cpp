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
#include "util/string.h"

namespace cvc5 {
namespace proof {

// have underlying node converter *not* force type preservation
LeanNodeConverter::LeanNodeConverter() : NodeConverter(true, false)
{
  d_brack[0] = mkInternalSymbol("__LEAN_TMP[");
  d_brack[1] = mkInternalSymbol("__LEAN_TMP]");
  d_comma = mkInternalSymbol("__LEAN_TMP,");
}
LeanNodeConverter::~LeanNodeConverter() {}

Node LeanNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  if (k == kind::SKOLEM)
  {
    Node wi = SkolemManager::getWitnessForm(n);
    AlwaysAssert(!wi.isNull());
    return convert(wi);
  }
  NodeManager* nm = NodeManager::currentNM();
  size_t nChildren = n.getNumChildren();
  std::vector<Node> resChildren;
  switch (k)
  {
    case kind::BOUND_VARIABLE:
    {
      // ignore internally generated symbols
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
    case kind::WITNESS:
    {
      resChildren.push_back(mkInternalSymbol("choice"));
      // the variable id
      resChildren.push_back(nm->mkConst<Rational>(n[0][0].getId()));
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
    case kind::EQUAL:
    {
      resChildren.push_back(mkInternalSymbol("eq"));
      resChildren.push_back(convert(n[0]));
      resChildren.push_back(convert(n[1]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::XOR:
    {
      resChildren.push_back(mkInternalSymbol("xor"));
      resChildren.push_back(convert(n[0]));
      resChildren.push_back(convert(n[1]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
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
    case kind::IMPLIES:
    {
      resChildren.push_back(mkInternalSymbol("implies"));
      resChildren.push_back(convert(n[0]));
      resChildren.push_back(convert(n[1]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::NOT:
    {
      resChildren.push_back(mkInternalSymbol("term.not"));
      resChildren.push_back(convert(n[0]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::ITE:
    {
      resChildren.push_back(mkInternalSymbol("fIte"));
      resChildren.push_back(convert(n[0]));
      resChildren.push_back(convert(n[1]));
      resChildren.push_back(convert(n[2]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::DISTINCT:
    {
      resChildren.push_back(mkInternalSymbol("distinct"));
      resChildren.push_back(convert(n[0]));
      resChildren.push_back(convert(n[1]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::SELECT:
    {
      resChildren.push_back(mkInternalSymbol("select"));
      resChildren.push_back(convert(n[0]));
      resChildren.push_back(convert(n[1]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::STORE:
    {
      resChildren.push_back(mkInternalSymbol("store"));
      resChildren.push_back(convert(n[0]));
      resChildren.push_back(convert(n[1]));
      resChildren.push_back(convert(n[2]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
    case kind::STRING_LENGTH:
    {
      resChildren.push_back(mkInternalSymbol("mkLength"));
      resChildren.push_back(convert(n[0]));
      return nm->mkNode(kind::SEXPR, resChildren);
    }
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
    }
  }
  // everything else is to be printed as itself
  return n;
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

}  // namespace proof
}  // namespace cvc5
