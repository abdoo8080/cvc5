/*********************                                                        */
/*! \file lean_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lean proof nodes
 **/

#include "proof/lean/lean_printer.h"

#include <iostream>
#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "options/expr_options.h"
#include "proof/lean/lean_rules.h"

namespace cvc5 {

namespace proof {

LetUpdaterPfCallback::LetUpdaterPfCallback(LetBinding& lbind,
                                           std::set<LeanRule>& letRules)
    : d_lbind(lbind), d_letRules(letRules)
{
}

LetUpdaterPfCallback::~LetUpdaterPfCallback() {}

bool LetUpdaterPfCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                        const std::vector<Node>& fa,
                                        bool& continueUpdate)
{
  // only process non-let rules
  return d_letRules.find(getLeanRule(pn->getArguments()[0]))
         == d_letRules.end();
}

bool LetUpdaterPfCallback::update(Node res,
                                  PfRule id,
                                  const std::vector<Node>& children,
                                  const std::vector<Node>& args,
                                  CDProof* cdp,
                                  bool& continueUpdate)
{
  d_lbind.process(res);
  return false;
}

LeanPrinter::LeanPrinter()
    : d_letRules({
        LeanRule::R0_PARTIAL,
        LeanRule::R1_PARTIAL,
        LeanRule::REFL_PARTIAL,
        LeanRule::CONG_PARTIAL,
        LeanRule::TRANS_PARTIAL,
        LeanRule::CL_OR,
        LeanRule::CL_ASSUME,
        LeanRule::TH_ASSUME,
    }),
      d_lbind(options::defaultDagThresh() ? options::defaultDagThresh() + 1
                                          : 0),
      d_cb(new LetUpdaterPfCallback(d_lbind, d_letRules))
{
  d_false = NodeManager::currentNM()->mkConst(false);
}
LeanPrinter::~LeanPrinter() {}

void LeanPrinter::printOffset(std::ostream& out, uint64_t offset) const
{
  for (uint64_t i = 0; i < offset; ++i)
  {
    out << "  ";
  }
}

void LeanPrinter::printSort(std::ostream& out, TypeNode sort)
{
  // functional sort
  if (sort.isFunction())
  {
    out << "(mkArrowN [";
    // print each arg sort
    unsigned size = sort.getNumChildren();
    for (unsigned i = 0, n_arg_types = size - 1; i < n_arg_types; ++i)
    {
      printSort(out, sort[i]);
      out << ", ";
    }
    // print return sort
    printSort(out, sort[size - 1]);
    out << "])";
    return;
  }
  // boolean sort
  if (sort.isBoolean())
  {
    out << "boolSort";
    return;
  }
  if (sort.isInteger())
  {
    out << "intSort";
    return;
  }
  // TODO HB will need to add cases for other theories

  // uninterpreted sort
  AlwaysAssert(sort.isSort());
  out << sort;
}

void LeanPrinter::printConstant(std::ostream& out, TNode n)
{
  Kind k = n.getKind();
  if (k == kind::CONST_BOOLEAN)
  {
    out << (n.getConst<bool>() ? "top" : "bot");
    return;
  }
  out << n;
}

void LeanPrinter::printTermList(std::ostream& out, TNode n)
{
  out << "[";
  for (unsigned i = 0, size = n.getNumChildren(); i < size; ++i)
  {
    printTerm(out, n[i]);
    out << (i < size - 1 ? ", " : "]");
  }
}

void LeanPrinter::printTerm(std::ostream& out, TNode n, bool letTop)
{
  Node nc = d_lbind.convert(n, "let", letTop);
  unsigned nChildren = nc.getNumChildren();
  // printing constant symbol
  if (nChildren == 0)
  {
    printConstant(out, nc);
    return;
  }
  // printing applications / formulas
  out << "(";
  Kind k = nc.getKind();
  TypeNode tn = nc.getType();
  switch (k)
  {
    case kind::APPLY_UF:
    {
      Node op = nc.getOperator();
      Assert(nChildren >= 1);
      if (nChildren > 1)
      {
        out << "mkAppN ";
        printTerm(out, op);
        out << " ";
        printTermList(out, nc);
      }
      else
      {
        out << "mkApp ";
        printTerm(out, op);
        out << " ";
        printTerm(out, nc[0]);
      }
      break;
    }
    case kind::EQUAL:
    {
      out << "mkEq ";
      printTerm(out, nc[0]);
      out << " ";
      printTerm(out, nc[1]);
      break;
    }

    case kind::OR:
    {
      Assert(nChildren >= 2);
      if (nChildren > 2)
      {
        out << "mkOrN ";
        printTermList(out, nc);
      }
      else
      {
        out << "mkOr ";
        printTerm(out, nc[0]);
        out << " ";
        printTerm(out, nc[1]);
      }
      break;
    }
    case kind::AND:
    {
      Assert(nChildren >= 2);
      if (nChildren > 2)
      {
        out << "mkAndN ";
        printTermList(out, nc);
      }
      else
      {
        out << "mkAnd ";
        printTerm(out, nc[0]);
        out << " ";
        printTerm(out, nc[1]);
      }
      break;
    }
    case kind::IMPLIES:
    {
      out << "mkImplies ";
      printTerm(out, nc[0]);
      out << " ";
      printTerm(out, nc[1]);
      break;
    }
    case kind::NOT:
    {
      out << "mkNot ";
      printTerm(out, nc[0]);
      break;
    }
    case kind::ITE:
    {
      out << "mkIte ";
      printTerm(out, nc[0]);
      out << " ";
      printTerm(out, nc[1]);
      out << " ";
      printTerm(out, nc[2]);
      break;
    }
    case kind::SEXPR:
    {
      out << "[";
      printTerm(out, nc[0]);
      for (size_t i = 1, size = nc.getNumChildren(); i < size; ++i)
      {
        out << ", ";
        printTerm(out, nc[i]);
      }
      out << "]";
      break;
    }
    default: Unhandled() << " " << k;
  }
  out << ")" << (letTop ? "" : "\n");
}

void LeanPrinter::printTermList(std::ostream& out,
                                const std::vector<Node>& children)
{
  out << "[";
  for (unsigned i = 0, size = children.size(); i < size; ++i)
  {
    printTerm(out, children[i]);
    out << (i < size - 1 ? ", " : "]");
  }
}

void LeanPrinter::printLetList(std::ostream& out)
{
  std::vector<Node> letList;
  d_lbind.letify(letList);
  std::map<Node, size_t>::const_iterator it;
  for (TNode n : letList)
  {
    size_t id = d_lbind.getId(n);
    Assert(id != 0);
    out << "def let" << id << " := ";
    printTerm(out, n, false);
  }
}

void LeanPrinter::printStepId(std::ostream& out,
                              const ProofNode* pfn,
                              const std::map<const ProofNode*, size_t>& pfMap,
                              const std::map<Node, size_t>& pfAssumpMap)
{
  if (pfn->getRule() == PfRule::ASSUME)
  {
    AlwaysAssert(pfAssumpMap.find(pfn->getResult()) != pfAssumpMap.end());
    out << "a" << pfAssumpMap.find(pfn->getResult())->second;
  }
  else
  {
    AlwaysAssert(pfMap.find(pfn) != pfMap.end());
    out << "s" << pfMap.find(pfn)->second;
  }
}

void LeanPrinter::printProof(std::ostream& out,
                             size_t& id,
                             uint64_t offset,
                             std::shared_ptr<ProofNode> pfn,
                             std::map<const ProofNode*, size_t>& pfMap,
                             std::map<Node, size_t>& pfAssumpMap)
{
  std::map<const ProofNode*, size_t>::const_iterator pfIt =
      pfMap.find(pfn.get());
  if (pfIt != pfMap.end())
  {
    return;
  }
  if (pfn->getRule() == PfRule::ASSUME)
  {
    return;
  }
  // print rule specific lean syntax, traversing children before parents in
  // ProofNode tree
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  Trace("test-lean") << "printProof: offset " << offset << "\n";
  Trace("test-lean") << "printProof: args " << args << "\n";
  LeanRule rule = getLeanRule(args[0]);
  Trace("test-lean") << "printProof: rule " << rule << "\n";
  // we handle scope differently because it starts a subproof
  if (rule == LeanRule::SCOPE)
  {
    printOffset(out, offset);
    out << "have s" << id << " : holds ";
    printTerm(out, args[2]);
    out << " from (\n";
    // push offset
    offset++;
    // each argument to the scope proof node corresponds to one scope to close
    // in the Lean proof
    std::map<Node, size_t> backupMap;
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      auto it = pfAssumpMap.find(args[i]);
      if (it != pfAssumpMap.end())
      {
        backupMap[args[i]] = it->second;
      }
      pfAssumpMap[args[i]] = i - 3;
      printOffset(out, offset);
      out << "fun a" << i - 3 << " : thHolds ";
      printTerm(out, args[i]);
      out << " =>\n";
    }
    size_t newId = 0;
    Trace("test-lean") << pop;
    for (const std::shared_ptr<ProofNode>& child : children)
    {
      printProof(out, newId, offset, child, pfMap, pfAssumpMap);
    }
    Trace("test-lean") << pop;
    // print conclusion of scope, which is the conversion to a clause of a scope
    // chain over the arguments until the last step of the subproof
    printOffset(out, offset);
    out << "show holds ";
    printTerm(out, args[2]);
    out << " from clOr";
    std::stringstream cparens;
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      out << " (scope a" << pfAssumpMap[args[i]];
      cparens << ")";
    }
    out << " s" << newId - 1 << cparens.str() << "\n";
    // recover assumption map
    for (const auto& p : backupMap)
    {
      pfAssumpMap[p.first] = p.second;
    }
    // print list of arguments
    printOffset(out, offset);
    out << ")";
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      out << " a" << pfAssumpMap[args[i]];
    }
    out << "\n";
    // pop offset
    offset--;
    // save proof step in map
    pfMap[pfn.get()] = id++;
    return;
  }
  Trace("test-lean") << push;
  for (const std::shared_ptr<ProofNode>& child : children)
  {
    printProof(out, id, offset, child, pfMap, pfAssumpMap);
  }
  Trace("test-lean") << pop;
  printOffset(out, offset);
  AlwaysAssert(args.size() >= 3);
  // print conclusion: proof node concludes `false`, print as show ... rather
  // than have s.... If the proof has a clausal conclusion (as argument), print
  // holds, otherwise thHolds and the result.
  bool hasClausalResult = args[2] != Node::null();
  TNode res = pfn->getResult();
  if (d_letRules.find(rule) != d_letRules.end())
  {
    out << "let s" << id << " := " << rule;
  }
  else
  {
    if (res == d_false)
    {
      out << "show " << (hasClausalResult ? "holds [] " : "thHolds bot");
    }
    else
    {
      out << "have s" << id << " : ";
      if (hasClausalResult)
      {
        out << "holds ";
        printTerm(out, args[2]);
      }
      else
      {
        out << "thHolds ";
        printTerm(out, res);
      }
    }
    out << " from " << rule;
  }
  switch (rule)
  {
    case LeanRule::CNF_AND_POS:
    case LeanRule::R0:
    case LeanRule::R1:
    case LeanRule::REORDER:
    case LeanRule::EQ_RESOLVE:
    case LeanRule::AND_ELIM:
    case LeanRule::REFL:
    case LeanRule::CONG:
    case LeanRule::TRANS:
    case LeanRule::SYMM:
    case LeanRule::NEG_SYMM:
    case LeanRule::TH_TRUST_VALID:
    case LeanRule::R0_PARTIAL:
    case LeanRule::R1_PARTIAL:
    case LeanRule::REFL_PARTIAL:
    case LeanRule::CONG_PARTIAL:
    case LeanRule::CL_OR:
    case LeanRule::CL_ASSUME:
    case LeanRule::TH_ASSUME:
    {
      for (const std::shared_ptr<ProofNode>& child : children)
      {
        out << " ";
        printStepId(out, child.get(), pfMap, pfAssumpMap);
      }
      for (size_t i = 3, size = args.size(); i < size; ++i)
      {
        out << " ";
        printTerm(out, args[i]);
      }
      break;
    }
    default:
    {
      out << "\nUnhandled: " << rule << " " << args;
      break;
    }
  }
  out << "\n";
  // save proof step in map
  pfMap[pfn.get()] = id++;
}

void LeanPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid Lean output from a ProofNode
  Trace("test-lean") << "Post-processed proof " << *pfn.get() << "\n";
  // TODO preamble should be theory dependent
  out << "import Cdclt.Euf\n\n";
  out << "open proof\nopen proof.sort proof.term\n";
  out << "open rules eufRules\n\n";

  // Print user defined sorts and constants of those sorts
  std::unordered_set<Node, NodeHashFunction> syms;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
  }
  int sortCount = 1000;
  int symCount = 1000;
  // uninterpreted sorts
  std::unordered_set<TypeNode, TypeNodeHashFunction> sts;
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    if (st.isSort() && sts.find(st) == sts.end())
    {
      sts.insert(st);
      out << "def " << st << " := atom " << sortCount++ << "\n";
    }
  }
  // uninterpreted functions
  for (const Node& s : syms)
  {
    out << "def " << s << " := const " << symCount++ << " ";
    printSort(out, s.getType());
    out << "\n";
  }
  AlwaysAssert(pfn->getChildren().size() == 1);
  std::shared_ptr<ProofNode> innerPf = pfn->getChildren()[0];
  // compute the term lets. For this consider the assertions and the conclusions
  // of explicit proof steps
  for (const Node& a : assertions)
  {
    d_lbind.process(a);
  }
  ProofNodeUpdater updater(nullptr, *(d_cb.get()), false, false, false);
  updater.process(innerPf);

  const std::vector<Node>& args = pfn->getArguments();
  for (size_t i = 3, size = args.size(); i < size; ++i)
  {
    d_lbind.process(args[i]);
  }
  printLetList(out);

  // print theorem header, which is to get proofs of all the assumptions and
  // conclude a proof of []. The assumptions are args[2..]
  out << "\ntheorem th0 : ";
  Assert(args.size() > 2);
  for (size_t i = 3, size = args.size(); i < size; ++i)
  {
    out << "thHolds ";
    printTerm(out, args[i]);
    out << " -> ";
  }
  // whether conclusion is "thHolds bot" or "holds []" depends on what the inner
  // proof term is concluding. So we check here:
  AlwaysAssert(innerPf->getArguments().size() >= 3);
  if (!innerPf->getArguments()[2].isNull())
  {
    out << "holds [] :=\n";
  }
  else
  {
    AlwaysAssert(innerPf->getResult() == d_false)
        << "conclusion is actually " << innerPf->getResult();
    out << "thHolds bot :=\n";
  }
  // print initial assumptions
  std::map<Node, size_t> pfAssumpMap;
  for (size_t i = 3, size = args.size(); i < size; ++i)
  {
    pfAssumpMap[args[i]] = i - 3;
    out << "fun a" << i - 3 << " : thHolds ";
    printTerm(out, args[i]);
    out << " =>\n";
  }
  std::stringstream ss;
  ss << out.rdbuf();
  size_t id = 0;
  Trace("test-lean") << "Before getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  std::map<const ProofNode*, size_t> pfMap;
  printProof(out, id, 0, innerPf, pfMap, pfAssumpMap);
  ss.clear();
  ss << out.rdbuf();
  Trace("test-lean") << "After getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  out << "\n";
}

}  // namespace proof
}  // namespace cvc5
