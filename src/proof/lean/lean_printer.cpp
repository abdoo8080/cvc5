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
#include "options/printer_options.h"
#include "proof/lean/lean_rules.h"
#include "util/string.h"

namespace cvc5::internal {

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

LeanPrinter::LeanPrinter(Env& env, LeanNodeConverter& lnc, bool printToCheck)
    : EnvObj(env),
      d_letRules({
          LeanRule::R0_PARTIAL,
          LeanRule::R1_PARTIAL,
          LeanRule::REFL_PARTIAL,
          LeanRule::CONG_PARTIAL,
          LeanRule::BIND_PARTIAL,
          LeanRule::BIND_LAMBDA_PARTIAL,
          LeanRule::TRANS_PARTIAL,
          LeanRule::AND_INTRO_PARTIAL,
          LeanRule::CL_OR,
          LeanRule::CL_ASSUME,
          LeanRule::TH_ASSUME,
      }),
      d_tacticRules({
          LeanRule::R0,
          LeanRule::R0_PARTIAL,
          LeanRule::R1,
          LeanRule::R1_PARTIAL,
          LeanRule::REORDER,
          LeanRule::LIFT_OR_N_TO_IMP,
          LeanRule::TH_TRUST_VALID,
        }),
      d_lbind(options().printer.dagThresh ? options().printer.dagThresh + 1
                                          : 0),
      d_lnc(lnc),
      d_cb(new LetUpdaterPfCallback(d_lbind, d_skMap, d_letRules)),
      d_printToCheck(printToCheck)
{
  d_false = NodeManager::currentNM()->mkConst(false);
}
LeanPrinter::~LeanPrinter() {}

void LeanPrinter::cleanSymbols(std::string& s)
{
  size_t startPos = 0;
  while ((startPos = s.find("|__LEAN_TMP", startPos)) != std::string::npos)
  {
    // stuff is "|__LEAN_TMP$WHATICARE|", so it's needed to kill one after
    // this prefix as well, which after the first replacement is just one after
    // startPos
    s.replace(startPos, 11, "");
    s.replace(startPos + 1, 1, "");
  }
  // also account for cases of like numbers which do not get wrapped if the
  // prefix was used
  startPos = 0;
  while ((startPos = s.find("__LEAN_TMP", startPos)) != std::string::npos)
  {
    // stuff is "__LEAN_TMP$WHATICARE", so just kill prefix
    s.replace(startPos, 10, "");
  }
  // also kill trailing spaces after "[" and before "," or "]"
  startPos = 0;
  while ((startPos = s.find("[ ", startPos)) != std::string::npos)
  {
    s.replace(startPos + 1, 1, "");
  }
  startPos = 0;
  while ((startPos = s.find(" ]", startPos)) != std::string::npos
         || (startPos = s.find(" ,", startPos)) != std::string::npos)
  {
    s.replace(startPos, 1, "");
  }
  startPos = 0;
  while ((startPos = s.find(" ,", startPos)) != std::string::npos)
  {
    s.replace(startPos, 1, "");
  }
  // If first symbols are "([", remove first and last symbols
  if (s.find("([", 0) == 0)
  {
    s.replace(0, 1, "");
    s.replace(s.size() - 1, 1, "");
  }
}

void LeanPrinter::printOffset(std::ostream& out, uint64_t offset) const
{
  for (uint64_t i = 0; i < offset; ++i)
  {
    out << "  ";
  }
}

void LeanPrinter::printSort(std::ostream& out, TypeNode tn)
{
  // must clean indexed symbols
  std::stringstream ss;
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  d_lnc.typeAsNode(tn).toStream(ss);
  std::string s = ss.str();
  cleanSymbols(s);
  out << s;
}

void LeanPrinter::printTerm(std::ostream& out, TNode n, bool letTop)
{
  // must clean indexed symbols
  std::stringstream ss;
  Node nc = d_lbind.convert(n, "let", letTop);
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  nc.toStream(ss);
  std::string s = ss.str();
  cleanSymbols(s);
  out << s << (letTop ? "" : "\n");
}

void LeanPrinter::printLetList(std::ostream& out)
{
  std::vector<Node> letList;
  d_lbind.letify(letList);
  for (TNode n : letList)
  {
    size_t id = d_lbind.getId(n);
    Trace("test-lean") << "printLetList, guy with id " << id << ": " << n
                       << "\n";
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
  out << (d_printToCheck? "lean_" : "");
  if (pfn->getRule() == PfRule::ASSUME)
  {
    // converted assumption
    Node conv = d_lnc.convert(pfn->getResult());
    AlwaysAssert(pfAssumpMap.find(conv) != pfAssumpMap.end())
        << "Original: " << pfn->getResult() << "\nConverted: " << conv;
    out << "a" << pfAssumpMap.find(conv)->second;
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
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  // The result to be printed is the third argument of the LEAN_RULE
  TNode res = pfn->getArguments()[2];
  LeanRule rule = getLeanRule(args[0]);
  Trace("test-lean") << "printProof: offset " << offset << "\n";
  Trace("test-lean") << "printProof: args " << args << "\n";
  Trace("test-lean") << "printProof: rule " << rule << "\n";
  Trace("test-lean") << "printProof: result " << res << "\n-----------\n";
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
    if (d_printToCheck)
    {
      out << "have lean_s" << id << " : ";
    }
    else
    {
      out << "[s" << id << ";";
    }
    // print conversion to a clause of the original scope's conclusion
    printTerm(out, res);
    out << (d_printToCheck ? " :=" : ";") << "\n";
    // each argument to the scope proof node corresponds to one scope to close
    // in the Lean proof. To avoid clashes, we shift the assumptions numbers by
    // current pfAssumpMap' size
    size_t assumptionsShift = pfAssumpMap.size();
    std::map<Node, size_t> backupMap;
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      auto it = pfAssumpMap.find(args[i]);
      if (it != pfAssumpMap.end())
      {
        backupMap[args[i]] = it->second;
      }
      pfAssumpMap[args[i]] = assumptionsShift + i - 3;
      // push and print offset
      printOffset(out, ++offset);
      if (d_printToCheck)
      {
        out << "(scope (fun lean_a" << assumptionsShift + i - 3 << " : ";
        printTerm(out, args[i]);
        out << " =>\n";
      }
      else
      {
        out << "[[a" << assumptionsShift + i - 3 << ";";
        printTerm(out, args[i]);
        out << ";]\n";
      }
    }
    // similarly, we shift step ids by the number of current steps
    size_t newId = pfMap.size();
    // use a new proof map for subproof
    std::map<const ProofNode*, size_t> subpfMap{pfMap};
    Trace("test-lean") << pop;
    AlwaysAssert(children.size() == 1);
    printProof(out, newId, ++offset, children[0], subpfMap, pfAssumpMap);
    Trace("test-lean") << pop;
    // print conclusion of scope's child if result is not "false". For now this
    // is a redundant step because the proof can't end with "have" but rather
    // with "show", and unless the conclusion of the scope is "false" the
    // keyword used would have been "false".
    if (children[0]->getResult() != d_false)
    {
      printOffset(out, offset);
      if (d_printToCheck)
      {
        out << "show ";
        printTerm(out, children[0]->getArguments()[2]);
        out << " from "
            << (d_tacticRules.find(getLeanRule(children[0]->getArguments()[0]))
                        != d_tacticRules.end()
                    ? "by "
                    : "");
        printStepId(out, children[0].get(), subpfMap, pfAssumpMap);
        out << "\n";
      }
      else
      {
        out << "[;";
        printTerm(out, children[0]->getArguments()[2]);
        out << ";";
        printStepId(out, children[0].get(), subpfMap, pfAssumpMap);
        out << "]\n";
      }
    }
    // now close. We have assumptions*2 parens
    std::stringstream cparens;
    for (size_t i = 3, size = args.size(); i < size; ++i)
    {
      offset--;
      cparens << (d_printToCheck? "))" : "]");
    }
    printOffset(out, offset);
    out << cparens.str() << (d_printToCheck? "" : "]") << "\n";
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
  bool isTactic = d_tacticRules.find(rule) != d_tacticRules.end();
  // print conclusion: proof node concludes `false`, print as show ... rather
  // than have s....
  if (d_letRules.find(rule) != d_letRules.end())
  {
    if (d_printToCheck)
    {
      out << "let lean_s" << id << " := " << (isTactic? "by " : "") << rule;
    }
    else
    {
      out << "[s" << id << ";;" << rule;
    }
  }
  else
  {
    if (pfn->getResult() == d_false)
    {
      out << (d_printToCheck ? "show False from " : "[;False;")
          << (d_printToCheck && isTactic ? "by " : "") << rule;
    }
    else
    {
      if (d_printToCheck)
      {
        out << "have lean_s" << id << " : ";
        printTerm(out, res);
        out << " := " << (isTactic? "by " : "") << rule;
      }
      else
      {
        out << "[s" << id << ";";
        printTerm(out, res);
        out << ";" << rule;
      }
    }
  }
  std::string separator = isTactic? ", " : " ";
  for (size_t i = 0, size = children.size(); i < size; ++i)
  {
    out << (i == 0 ? " " : separator);
    printStepId(out, children[i].get(), pfMap, pfAssumpMap);
  }
  for (size_t i = 3, size = args.size(); i < size; ++i)
  {
    out << separator;
    printTerm(out, args[i]);
  }
  out << (d_printToCheck? "" : "]") << "\n";
  // save proof step in map
  pfMap[pfn.get()] = id++;
}

void LeanPrinter::print(std::ostream& out,
                        std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid Lean output from a ProofNode
  if (TraceIsOn("test-lean-pf"))
  {
    Trace("test-lean-pf") << "Post-processed proof ";
    pfn->printDebug(out, true);
    Trace("test-lean-pf") << "\n";
  }
  // Print preamble
  if (d_printToCheck)
  {
    out << "import Meta.Boolean\nimport Meta.Resolution\nimport "
           "Meta.PermutateOr";
    // increase recursion depth and heartbeats
    // out << "set_option maxRecDepth 10000\nset_option maxHeartbeats
    // 500000\n\n";

    std::vector<Node> assertions = pfn->getArguments();
    // Print user defined sorts and constants of those sorts
    std::unordered_set<Node> syms;
    std::unordered_set<TNode> visited;
    for (const Node& a : assertions)
    {
      expr::getSymbols(a, syms, visited);
    }
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
        if (stc.isUninterpretedSort() && stc.getKind() != kind::TYPE_CONSTANT)
        {
          Trace("test-lean") << "collecting sort " << stc << " with kind "
                             << stc.getKind() << "\n";
          sts.insert(stc);
        }
      }
    }
    if (!sts.empty())
    {
      out << "\nuniverse u\n";
    }
    for (const auto& s : sts)
    {
      out << "variable {" << s << " : Type u}\n";
    }
    // uninterpreted functions
    for (const Node& s : syms)
    {
      out << "variable {" << s << " : ";
      printSort(out, s.getType());
      out << "}\n";
    }
  }
  // The proof we will actually process is the one under the original scope.
  // Since our processing of scope converts it into two rules (scope and
  // lifnOrNToImp) we need to get the child of the child
  std::shared_ptr<ProofNode> innerPf = pfn->getChildren()[0]->getChildren()[0];

  // No lets for now

  // // compute the term lets. For this consider the converted assertions
  // for (const Node& a : assertions)
  // {
  //   d_lbind.process(d_lnc.convert(a));
  // }
  // // Traverse the proof node to letify the (converted) conclusions of explicit
  // // proof steps. This traversal will collect the skolems to de defined.
  // ProofNodeUpdater updater(d_env, *(d_cb.get()), false, false);
  // updater.process(innerPf);

  const std::vector<Node>& assumptions = pfn->getChildren()[0]->getArguments();
  std::vector<Node> convertedAssumptions;
  for (size_t i = 4, size = assumptions.size(); i < size; ++i)
  {
    convertedAssumptions.push_back(d_lnc.convert(assumptions[i]));
    d_lbind.process(convertedAssumptions.back());
  }
  printLetList(out);
  if (d_printToCheck)
  {
    // print theorem statement, which is to get proofs of all the assumptions
    // and conclude a proof of False. The assumptions are args[3..]
    out << "\ntheorem th0 : ";
    for (const Node& a : convertedAssumptions)
    {
      printTerm(out, d_lnc.convert(a));
      out << " → ";
    }
    out << "False :=\n";
  }
  // print initial assumptions
  std::map<Node, size_t> pfAssumpMap;
  for (size_t i = 0, size = convertedAssumptions.size(); i < size; ++i)
  {
    pfAssumpMap[convertedAssumptions[i]] = i;
    if (d_printToCheck)
    {
      out << "fun lean_a" << i << " : ";
      printTerm(out, convertedAssumptions[i]);
      out << " =>\n";
    }
    else
    {
      out << "[a" << i << ";";
      printTerm(out, convertedAssumptions[i]);
      out << ";]\n";
    }
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
}  // namespace cvc5::internal
