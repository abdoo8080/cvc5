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
    case LeanRule::ASSUME: return "assume";
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
  printLeanType(s, n[0]);
  s << " -> holds []";
}

void LeanPrinter::printProof(std::ostream& out,
                             std::shared_ptr<ProofNode> pfn,
                             std::map<Node, std::string>& passumeMap)
{

  // print rule specific lean syntax, traversing children before parents in
  // ProofNode tree
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& children = pfn->getChildren();
  Trace("test-lean") << "printProof: args " << args << "\n";
  LeanRule id = getLeanRule(args[0]);
  Trace("test-lean") << "printProof: id " << id << "\n";
  if (id == LeanRule::SCOPE)
  {
    // each argument to the scope proof node corresponds to one scope
    //  to close in the Lean proof
    for (size_t i = 2, size = args.size(); i < size; ++i)
    {
      size_t varIndex = passumeMap.size();
      std::stringstream varString;
      varString << "v" << varIndex;
      passumeMap[args[i]] = varString.str();

      out << "(assume (" << passumeMap[args[i]] << " : ";
      printLeanType(out, args[i]);
      out << "),\n";
    }
    for (const std::shared_ptr<ProofNode>& ch : children)
    {
      printProof(out, ch, passumeMap);
    }
    for (size_t j = 2, size = args.size(); j < size; ++j)
    {
      out << ")";
    }
  }
  else
  {
    for (const std::shared_ptr<ProofNode>& ch : children)
    {
      printProof(out, ch, passumeMap);
    }
  }
  switch (id)
  {
    case LeanRule::SCOPE: break;
    case LeanRule::TRUST:
    {
      out << "trust\n";
      break;
    }
    case LeanRule::ASSUME:
    {
      // get variable name
      break;
    };
    case LeanRule::R0:
    {
      // print variable names of clauses to be resolved against
      out << "R0 ";
      out << "(clAssume ";
      out << passumeMap[children[0]->getArguments()[1]] << ") ";
      out << "(clAssume ";
      out << passumeMap[children[1]->getArguments()[1]] << ") ";
      printLeanString(out, args[2]);
      break;
    }
    case LeanRule::R1:
    {
      // print variable names of clauses to be resolved against
      out << "R1 ";
      out << passumeMap[children[0]->getArguments()[1]] << " ";
      out << passumeMap[children[1]->getArguments()[1]] << " ";
      printLeanString(out, args[2]);
      break;
    }
    // case LeanRule::SMTREFL:
    // {
    //   size_t varIndex = passumeMap.size();
    //   std::stringstream varString;
    //   varString << "v" << varIndex;
    //   passumeMap[args[1]] = varString.str();
    //   out << "let " << passumeMap[args[1]];
    //   out << " := symm " << passumeMap[children[0]->getArguments()[0]];
    //   out << " in \n";
    //   break;
    // }
    case LeanRule::SYMM:
    {
      size_t varIndex = passumeMap.size();
      std::stringstream varString;
      varString << "v" << varIndex;
      passumeMap[args[1]] = varString.str();
      out << "let " << passumeMap[args[1]];
      out << " := symm " << passumeMap[children[0]->getArguments()[0]];
      out << " in \n";
      break;
    }
    case LeanRule::NEG_SYMM:
    {
      size_t varIndex = passumeMap.size();
      std::stringstream varString;
      varString << "v" << varIndex;
      passumeMap[args[1]] = varString.str();
      out << "let " << passumeMap[args[1]];
      out << " := negSymm " << passumeMap[children[0]->getArguments()[0]];
      out << " in \n";
      // maybe add type to annotate term
      break;
    }
    default:
    {
      out << args;
      out << " ?\n";
      break;
    }
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
  out << (letTop ? "" : "\n");
}

void LeanPrinter::printLetList(std::ostream& out,
                               LetBinding& lbind)
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


void LeanPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        std::shared_ptr<ProofNode> pfn)
{
  // outer method to print valid Lean output from a ProofNode
  Trace("test-lean") << "Post-processed proof " << *pfn.get() << "\n";
  std::map<Node, std::string> passumeMap;
  const std::vector<Node>& args = pfn->getArguments();
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
      out << "def " << st << " := sort.atom " << sortCount++ << "\n";
    }
  }
  // uninterpreted functions
  for (const Node& s : syms)
  {
    out << "def " << s << " := const " << symCount++
        << " ";
    printSort(out, s.getType());
    out << "\n";
  }
  // TOOD compute letification

  // compute the term lets
  LetBinding lbind;
  for (const Node& a : assertions)
  {
    lbind.process(a);
  }
  printLetList(out, lbind);

  out << "theorem th0 : ";
  printLeanTypeToBottom(out, args[1]);
  out << " := \n";
  std::stringstream ss;
  ss << out.rdbuf();
  Trace("test-lean") << "Before getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  printProof(out, pfn, passumeMap);
  ss.clear();
  ss << out.rdbuf();
  Trace("test-lean") << "After getting to proof node:\n"
                     << ss.str() << "==================\n\n";
  out << "\n";
}

}  // namespace proof
}  // namespace cvc5
