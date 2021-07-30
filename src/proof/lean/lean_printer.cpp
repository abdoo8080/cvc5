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
#include "expr/skolem_manager.h"
#include "options/expr_options.h"
#include "proof/lean/lean_rules.h"
#include "util/string.h"

namespace cvc5 {

namespace proof {

LetUpdaterPfCallback::LetUpdaterPfCallback(LetBinding& lbind,
                                           std::map<Node, Node>& skMap,
                                           std::set<LeanRule>& letRules)
    : d_lbind(lbind), d_skMap(skMap), d_letRules(letRules)
{
}

LetUpdaterPfCallback::~LetUpdaterPfCallback() {}

bool LetUpdaterPfCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                        const std::vector<Node>& fa,
                                        bool& continueUpdate)
{
  // only process non-let, non-assume rules
  return pn->getRule() != PfRule::ASSUME
         && d_letRules.find(getLeanRule(pn->getArguments()[0]))
                == d_letRules.end();
}

bool LetUpdaterPfCallback::update(Node res,
                                  PfRule id,
                                  const std::vector<Node>& children,
                                  const std::vector<Node>& args,
                                  CDProof* cdp,
                                  bool& continueUpdate)
{
  // Letification done on the converted terms
  AlwaysAssert(args.size() > 2) << "res: " << res << "\nid: " << id;
  d_lbind.process(args[2]);
  // Skolem rules
  // if (id == PfRule::ARRAYS_EXT)
  // {
  //   d_skMap[res[0][0][1]] = SkolemManager::getWitnessForm(k);
  // }
  return false;
}

LeanPrinter::LeanPrinter(LeanNodeConverter& lnc)
    : d_letRules({
        LeanRule::R0_PARTIAL,
        LeanRule::R1_PARTIAL,
        LeanRule::REFL_PARTIAL,
        LeanRule::CONG_PARTIAL,
        LeanRule::TRANS_PARTIAL,
        LeanRule::AND_INTRO_PARTIAL,
        LeanRule::CL_OR,
        LeanRule::CL_ASSUME,
        LeanRule::TH_ASSUME,
    }),
      d_lbind(options::defaultDagThresh() ? options::defaultDagThresh() + 1
                                          : 0),
      d_lnc(lnc),
      d_cb(new LetUpdaterPfCallback(d_lbind, d_skMap, d_letRules))
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

void LeanPrinter::printTerm(std::ostream& out, TNode n, bool letTop)
{
  out << d_lbind.convert(n, "let", letTop) << (letTop ? "" : "\n");
}

void LeanPrinter::printLetList(std::ostream& out)
{
  std::vector<Node> letList;
  d_lbind.letify(letList);
  for (TNode n : letList)
  {
    size_t id = d_lbind.getId(n);
    Trace("test-lean") << "printLetList, guy with id " << id << ": " << n << "\n";
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
    // converted assumption
    Node conv = d_lnc.convert(pfn->getResult());
    AlwaysAssert(pfAssumpMap.find(conv) != pfAssumpMap.end())
        << "Original: " << pfn->getResult() << "\nConverted: " << conv;
    out << "lean_a" << pfAssumpMap.find(conv)->second;
  }
  else
  {
    AlwaysAssert(pfMap.find(pfn) != pfMap.end());
    out << "lean_s" << pfMap.find(pfn)->second;
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
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  // The result to be printed is the third argument of the LEAN_RULE
  TNode res = pfn->getArguments()[2];
  LeanRule rule = getLeanRule(args[0]);
  Trace("test-lean") << "printProof: offset " << offset << "\n";
  Trace("test-lean") << "printProof: args " << args << "\n";
  Trace("test-lean") << "printProof: rule " << rule << "\n";
  Trace("test-lean") << "printProof: result " << res << "\n";
  if (rule == LeanRule::UNKNOWN)
  {
    // save proof step in map
    pfMap[pfn.get()] = id++;
    out << "Unhandled: " << rule << " " << args << "\n";
    return;
  }
  // we handle scope differently because it starts a subproof
  if (rule == LeanRule::SCOPE)
  {
    printOffset(out, offset);
    out << "have lean_s" << id << " : thHolds ";
    // print conversion to a clause of the original scope's conclusion
    printTerm(out, res);
    out << " from\n";
    // each argument to the scope proof node corresponds to one scope to close
    // in the Lean proof. To avoid clashes, we shift the assumptions numbers by
    // current pfAssumpMap' size
    size_t assumptionsShift = pfAssumpMap.size();
    std::map<Node, size_t> backupMap;
    for (size_t i = 4, size = args.size(); i < size; ++i)
    {
      auto it = pfAssumpMap.find(args[i]);
      if (it != pfAssumpMap.end())
      {
        backupMap[args[i]] = it->second;
      }
      pfAssumpMap[args[i]] = assumptionsShift + i - 4;
      // push and print offset
      printOffset(out, ++offset);
      out << "(scope (fun lean_a" << assumptionsShift + i - 4 << " : thHolds ";
      printTerm(out, args[i]);
      out << " =>\n";
    }
    // similarly, we shift step ids by the number of current steps
    size_t newId = pfMap.size();
    // use a new proof map for subproof
    // std::map<const ProofNode*, size_t> subpfMap{pfMap};
    Trace("test-lean") << pop;
    AlwaysAssert(children.size() == 1);
    printProof(out, newId, ++offset, children[0], pfMap, pfAssumpMap);
    Trace("test-lean") << pop;
    // print conclusion of scope's child. For now this is a redundant step
    // because the proof can't end with "have" but rather with "show"
    printOffset(out, offset);
    out << "show thHolds ";
    printTerm(out, children[0]->getArguments()[2]);
    out << " from ";
    printStepId(out, children[0].get(), pfMap, pfAssumpMap);
    out << "\n";
    // now close. We have assumptions*2 parens
    std::stringstream cparens;
    for (size_t i =  4, size = args.size(); i < size; ++i)
    {
      offset--;
      cparens << "))";
    }
    printOffset(out, offset);
    out << cparens.str() << "\n";
    // recover assumption map
    for (const auto& p : backupMap)
    {
      pfAssumpMap[p.first] = p.second;
    }
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
  AlwaysAssert(args.size() >= 4);
  // print conclusion: proof node concludes `false`, print as show ... rather
  // than have s.... If the proof has a clausal conclusion, print
  // holds, otherwise thHolds and the result.
  bool hasClausalResult = args[3] != d_false;
  if (d_letRules.find(rule) != d_letRules.end())
  {
    out << "let lean_s" << id << " := " << rule;
  }
  else
  {
    if (res == d_false)
    {
      out << "show " << (hasClausalResult ? "holds [] " : "thHolds bot");
    }
    else
    {
      out << "have lean_s" << id << " : "
          << (hasClausalResult ? "holds " : "thHolds ");
      printTerm(out, res);
    }
    out << " from " << rule;
  }
  for (const std::shared_ptr<ProofNode>& child : children)
  {
    out << " ";
    printStepId(out, child.get(), pfMap, pfAssumpMap);
  }
  for (size_t i = 4, size = args.size(); i < size; ++i)
  {
    out << " ";
    printTerm(out, args[i]);
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
  Trace("test-lean-pf") << "Post-processed proof " << *pfn.get() << "\n";
  // TODO preamble should be theory dependent
  out << "import Cdclt.Euf\nimport Cdclt.Array\n";
  // increase recursion depth and heartbeats
  out << "set_option maxRecDepth 10000\nset_option maxHeartbeats 500000\n\n";
  // do includes
  out << "open proof\nopen proof.sort proof.term\n";
  out << "open rules eufRules arrayRules\n\n";

  // Print user defined sorts and constants of those sorts
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
  }
  int sortCount = 1000;
  int symCount = 1000;
  // uninterpreted sorts
  std::unordered_set<TypeNode> sts;
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    std::unordered_set<TypeNode> ctypes;
    expr::getComponentTypes(st, ctypes);
    for (const TypeNode& stc : ctypes)
    {
      // only collect non-predefined sorts for declaration
      if (stc.isSort() && stc.getKind() != kind::TYPE_CONSTANT)
      {
        Trace("test-lean") << "collecting sort " << stc << " with kind "
                           << stc.getKind() << "\n";
        sts.insert(stc);
      }
    }
  }
  for (const auto& s : sts)
  {
    out << "def " << s << " := atom " << sortCount++ << "\n";
  }
  // uninterpreted functions
  for (const Node& s : syms)
  {
    out << "def " << s << " := const " << symCount++ << " "
        << d_lnc.typeAsNode(s.getType());
    out << "\n";
  }
  // actual proof is under the processed scope and possibly spurious thAssume
  // steps
  AlwaysAssert(pfn->getChildren().size() == 1
               && pfn->getChildren()[0]->getChildren().size() == 1);
  std::shared_ptr<ProofNode> innerPf = pfn->getChildren()[0]->getChildren()[0];
  Trace("test-lean") << "innerPf rule: "
                     << getLeanRule(innerPf->getArguments()[0]) << "\n";
  // compute the term lets. For this consider the converted assertions
  for (const Node& a : assertions)
  {
    d_lbind.process(d_lnc.convert(a));
  }
  // Traverse the proof node to letify the (converted) conclusions of explicit
  // proof steps. This traversal will collect the skolems to de defined.
  ProofNodeUpdater updater(nullptr, *(d_cb.get()), false, false);
  updater.process(innerPf);

  const std::vector<Node>& assumptions = pfn->getChildren()[0]->getArguments();
  std::vector<Node> convertedAssumptions;
  for (size_t i = 4, size = assumptions.size(); i < size; ++i)
  {
    convertedAssumptions.push_back(d_lnc.convert(assumptions[i]));
    d_lbind.process(convertedAssumptions.back());
  }
  printLetList(out);

  // print theorem header, which is to get proofs of all the assumptions and
  // conclude a proof of []. The assumptions are args[2..]
  out << "\ntheorem th0 : ";
  for (const Node& a : convertedAssumptions)
  {
    out << "thHolds ";
    printTerm(out, a);
    out << " -> ";
  }
  // whether conclusion is "thHolds bot" or "holds []" depends on what the inner
  // proof term is concluding. So we check here:
  AlwaysAssert(innerPf->getArguments().size() >= 3);
  if (innerPf->getArguments()[3] != d_false)
  {
    out << "holds [] :=\n";
  }
  else
  {
    AlwaysAssert(innerPf->getResult() == d_false)
        << "conclusion with rule " << getLeanRule(innerPf->getArguments()[0])
        << " is actually " << innerPf->getResult();
    out << "thHolds bot :=\n";
  }
  // print initial assumptions
  std::map<Node, size_t> pfAssumpMap;
  for (size_t i = 0, size = convertedAssumptions.size(); i < size; ++i)
  {
    pfAssumpMap[convertedAssumptions[i]] = i;
    out << "fun lean_a" << i << " : thHolds ";
    printTerm(out, convertedAssumptions[i]);
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
