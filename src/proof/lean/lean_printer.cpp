/*********************                                                        */
/*! \file lean_printer.cpp
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

#include "proof/lean/lean_printer.h"

#include <iostream>

#include "expr/node_algorithm.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "proof/lean/lean_rules.h"

namespace cvc5 {

namespace proof {

const char* toString(LeanRule id)
{
  switch (id)
  {
    case LeanRule::SCOPE: return "scope";
    case LeanRule::CL_ASSUME: return "clAssume";
    case LeanRule::CL_OR: return "clOr";

    case LeanRule::R0: return "R0";
    case LeanRule::R1: return "R1";

    case LeanRule::FACTORING: return "factoring";
    case LeanRule::REORDER: return "reorder";
    case LeanRule::EQ_RESOLVE: return "eqResolve";
    case LeanRule::MODUS_PONENS: return "modusPonens";
    case LeanRule::NOT_NOT_ELIM: return "notNotElim";
    case LeanRule::CONTRADICTION: return "contradiction";
    case LeanRule::AND_ELIM: return "andElim";
    case LeanRule::AND_INTRO: return "andIntro";
    case LeanRule::NOT_OR_ELIM: return "notOrElim";
    case LeanRule::IMPLIES_ELIM: return "impliesElim";
    case LeanRule::NOT_IMPLIES1: return "notImplies1";
    case LeanRule::NOT_IMPLIES2: return "notImplies2";
    case LeanRule::EQUIV_ELIM1: return "equivElim1";
    case LeanRule::EQUIV_ELIM2: return "equivElim2";
    case LeanRule::NOT_EQUIV_ELIM1: return "notEquivElim1";
    case LeanRule::NOT_EQUIV_ELIM2: return "notEquivElim2";
    case LeanRule::XOR_ELIM1: return "xorElim1";
    case LeanRule::XOR_ELIM2: return "xorElim2";
    case LeanRule::NOT_XOR_ELIM1: return "notXorElim1";
    case LeanRule::NOT_XOR_ELIM2: return "notXorElim2";
    case LeanRule::ITE_ELIM1: return "iteElim1";
    case LeanRule::ITE_ELIM2: return "iteElim2";
    case LeanRule::NOT_ITE_ELIM1: return "notIteElim1";
    case LeanRule::NOT_ITE_ELIM2: return "notIteElim2";
    case LeanRule::NOT_AND: return "notAnd";
    case LeanRule::CNF_AND_POS: return "cnfAndPos";
    case LeanRule::CNF_AND_NEG: return "cnfAndNeg";
    case LeanRule::CNF_IMPLIES_POS: return "cnfImpliesPos";
    case LeanRule::CNF_IMPLIES_NEG1: return "cnfImpliesNeg1";
    case LeanRule::CNF_IMPLIES_NEG2: return "cnfImpliesNeg2";
    case LeanRule::CNF_EQUIV_POS1: return "cnfEquivPos1";
    case LeanRule::CNF_EQUIV_POS2: return "cnfEquivPos2";
    case LeanRule::CNF_EQUIV_NEG1: return "cnfEquivNeg1";
    case LeanRule::CNF_EQUIV_NEG2: return "cnfEquivNeg2";
    case LeanRule::CNF_XOR_POS1: return "cnfXorPos1";
    case LeanRule::CNF_XOR_POS2: return "cnfXorPos2";
    case LeanRule::CNF_XOR_NEG1: return "cnfXorNeg1";
    case LeanRule::CNF_XOR_NEG2: return "cnfXorNeg2";
    case LeanRule::CNF_ITE_POS1: return "cnfItePos1";
    case LeanRule::CNF_ITE_POS2: return "cnfItePos2";
    case LeanRule::CNF_ITE_POS3: return "cnfItePos3";
    case LeanRule::CNF_ITE_NEG1: return "cnfIteNeg1";
    case LeanRule::CNF_ITE_NEG2: return "cnfIteNeg2";
    case LeanRule::CNF_ITE_NEG3: return "cnfIteNeg3";
    case LeanRule::TRUST: return "trust";
    case LeanRule::TH_TRUST: return "thTrust";
    case LeanRule::TH_TRUST_VALID: return "thTrustValid";

    case LeanRule::CONG: return "cong";
    case LeanRule::REFL: return "refl";
    case LeanRule::TRANS: return "trans";
    case LeanRule::SYMM: return "symm";
    case LeanRule::NEG_SYMM: return "negSymm";

    case LeanRule::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, LeanRule id)
{
  out << toString(id);
  return out;
}

LeanPrinter::LeanPrinter() {}
LeanPrinter::~LeanPrinter() {}

LeanRule LeanPrinter::getLeanRule(Node n)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    return static_cast<LeanRule>(id);
  }
  return LeanRule::UNKNOWN;
}

void LeanPrinter::printKind(std::ostream& s, Kind k)
{
  switch (k)
  {
    case kind::EQUAL: s << "mkEq"; break;
    case kind::AND: s << "mkAnd"; break;
    case kind::OR: s << "mkOr"; break;
    case kind::NOT: s << "mkNot"; break;
    default: s << "mkOther";
  }
}

void LeanPrinter::printLeanString(std::ostream& s, Node n)
{
  Kind k = n.getKind();
  if (k == kind::VARIABLE)
  {
    s << n.toString();
  }
  else
  {
    s << "(";
    printKind(s, k);
    s << " ";
    for (size_t i = 0, size = n.getNumChildren(); i < size; ++i)
    {
      printLeanString(s, n[i]);
      if (i != size - 1)
      {
        s << " ";
      };
    }
    s << ")";
  }
}

void LeanPrinter::printLeanType(std::ostream& s, Node n)
{
  // convert from node to Lean Type syntax:
  // products are curried
  // types are wrapped in "holds [_]"
  Kind k = n.getKind();
  switch (k)
  {
    case kind::VARIABLE: s << n.toString(); break;
    case kind::AND:
    {
      printLeanType(s, n[0]);
      s << " -> ";
      printLeanType(s, n[1]);
      break;
    }
    default:
      s << "thHolds ";
      printLeanString(s, n);
      break;
  }
}

void LeanPrinter::printLeanTypeToBottom(std::ostream& s, Node n)
{
  // print Lean type corresponding to proof of unsatisfiability
  Trace("test-lean") << "printLeanTypeToBottom: " << n[0] << "\n";
  printLeanType(s, n[0]);
  s << " -> holds []";
}

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
    out << "val (value.bool " << n.getConst<bool>() << ") boolSort)";
    return;
  }
  // uninterpreted
  out << n;
}

void LeanPrinter::printTermList(std::ostream& out, LetBinding& lbind, TNode n)
{
  out << "[";
  for (unsigned i = 0, size = n.getNumChildren(); i < size; ++i)
  {
    printTerm(out, lbind, n[i]);
    out << (i < size - 1 ? ", " : "]");
  }
}

void LeanPrinter::printTermList(std::ostream& out,
                                LetBinding& lbind,
                                const std::vector<Node>& children)
{
  out << "[";
  for (unsigned i = 0, size = children.size(); i < size; ++i)
  {
    printTerm(out, lbind, children[i]);
    out << (i < size - 1 ? ", " : "]");
  }
}

void LeanPrinter::printTerm(std::ostream& out,
                            LetBinding& lbind,
                            TNode n,
                            bool letTop)
{
  Trace("leanpf::print") << "Printing term " << (letTop ? "[decl] " : "") << n
                         << "\n";
  Node nc = lbind.convert(n, "let", letTop);
  unsigned nArgs = nc.getNumChildren();
  // printing constant symbol
  if (nArgs == 0)
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
      out << "mkAppN ";
      Node op = nc.getOperator();
      printTerm(out, lbind, op);
      out << " ";
      printTermList(out, lbind, nc);
      break;
    }

    case kind::EQUAL:
    {
      out << "mkEq ";
      printTerm(out, lbind, nc[0]);
      out << " ";
      printTerm(out, lbind, nc[1]);
      break;
    }

    case kind::OR:
    {
      out << "mkOrN ";
      printTermList(out, lbind, nc);
      break;
    }
    case kind::AND:
    {
      out << "mkAndN ";
      printTermList(out, lbind, nc);
      break;
    }
    case kind::IMPLIES:
    {
      out << "mkImplies ";
      printTerm(out, lbind, nc[0]);
      out << " ";
      printTerm(out, lbind, nc[1]);
      break;
    }
    case kind::NOT:
    {
      out << "mkNot ";
      printTerm(out, lbind, nc[0]);
      break;
    }
    case kind::ITE:
    {
      out << "mkIte ";
      printTerm(out, lbind, nc[0]);
      out << " ";
      printTerm(out, lbind, nc[1]);
      out << " ";
      printTerm(out, lbind, nc[2]);
      break;
    }

    default: Unhandled() << " " << k;
  }
  out << ")" << (letTop ? "" : "\n");
}

void LeanPrinter::printLetList(std::ostream& out, LetBinding& lbind)
{
  std::vector<Node> letList;
  lbind.letify(letList);
  std::map<Node, size_t>::const_iterator it;
  for (TNode n : letList)
  {
    size_t id = lbind.getId(n);
    Assert(id != 0);
    out << "def let" << id << " := ";
    printTerm(out, lbind, n, false);
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
                             LetBinding& lbind,
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
    printTerm(out, lbind, args[1]);
    out << " from (\n";
    // push offset
    offset++;
    // each argument to the scope proof node corresponds to one scope to close
    // in the Lean proof
    std::map<Node, size_t> backupMap;
    for (size_t i = 2, size = args.size(); i < size; ++i)
    {
      auto it = pfAssumpMap.find(args[i]);
      if (it != pfAssumpMap.end())
      {
        backupMap[args[i]] = it->second;
      }
      pfAssumpMap[args[i]] = i - 2;
      printOffset(out, offset);
      out << "fun a" << i - 2 << " : thHolds ";
      printTerm(out, lbind, args[i]);
      out << " =>\n";
    }
    size_t newId = 0;
    Trace("test-lean") << pop;
    for (const std::shared_ptr<ProofNode>& child : children)
    {
      printProof(out, newId, offset, child, lbind, pfMap, pfAssumpMap);
    }
    Trace("test-lean") << pop;
    // print conclusion of scope, which is the conversion to a clause of a scope
    // chain over the arguments until the last step of the subproof
    printOffset(out, offset);
    out << "show holds ";
    printTerm(out, lbind, args[1]);
    out << " from clOr";
    std::stringstream cparens;
    for (size_t i = 2, size = args.size(); i < size; ++i)
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
    for (size_t i = 2, size = args.size(); i < size; ++i)
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
    printProof(out, id, offset, child, lbind, pfMap, pfAssumpMap);
  }
  Trace("test-lean") << pop;
  printOffset(out, offset);
  switch (rule)
  {
    case LeanRule::SYMM:
    {
       out << "have s" << id << " : thHolds ";
       printTerm(out, lbind, pfn->getResult());
       out << " from " << rule << " ";
       Assert(children.size() == 1);
       printStepId(out, children[0].get(), pfMap, pfAssumpMap);
       break;
    }
    case LeanRule::NEG_SYMM:
    {
      size_t varIndex = pfAssumpMap.size();
      std::stringstream varString;
      varString << "v" << varIndex;
      pfAssumpMap[args[1]] = varIndex;
      out << "let " << pfAssumpMap[args[1]];
      out << " := negSymm " << pfAssumpMap[children[0]->getArguments()[0]];
      out << " in \n";
      // maybe add type to annotate term
      break;
    }
    default:
    {
      out << args;
      out << " ?";
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
  Assert(pfn->getRule() == LeanRule::SCOPE);
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
  // TOOD compute proof letification

  // compute the term lets
  // TODO include terms in the proof
  LetBinding lbind;
  for (const Node& a : assertions)
  {
    lbind.process(a);
  }
  const std::vector<Node>& args = pfn->getArguments();
  for (size_t i = 2, size = args.size(); i < size; ++i)
  {
    lbind.process(args[i]);
  }
  printLetList(out, lbind);

  // print theorem header, which is to get proofs of all the assumptions and
  // conclude a proof of []. The assumptions are args[2..]
  out << "\ntheorem th0 : ";
  Assert(args.size() > 2);
  for (size_t i = 2, size = args.size(); i < size; ++i)
  {
    out << "thHolds ";
    printTerm(out, lbind, args[i]);
    out << " -> ";
  }
  out << " holds [] :=\n";
  // print initial assumptions
  std::map<Node, size_t> pfAssumpMap;
  for (size_t i = 2, size = args.size(); i < size; ++i)
  {
    pfAssumpMap[args[i]] = i - 2;
    out << "fun a" << i - 2 << " : thHolds ";
    printTerm(out, lbind, args[i]);
    out << " =>\n";
  }
  std::stringstream ss;
  ss << out.rdbuf();
  size_t id = 0;
  Trace("test-lean") << "Before getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  std::map<const ProofNode*, size_t> pfMap;
  printProof(out, id, 0, pfn->getChildren()[0], lbind, pfMap, pfAssumpMap);
  ss.clear();
  ss << out.rdbuf();
  Trace("test-lean") << "After getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  out << "\n";
}

}  // namespace proof
}  // namespace cvc5
