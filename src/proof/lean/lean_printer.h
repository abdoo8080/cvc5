/*********************                                                        */
/*! \file lean_printer.h
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

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LEAN_PROOF_PRINTER_H
#define CVC4__PROOF__LEAN_PROOF_PRINTER_H

#include <iostream>
#include <sstream>
#include <string>

#include "expr/node_algorithm.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "printer/let_binding.h"
#include "proof/lean/lean_rules.h"

namespace cvc5 {

namespace proof {

class LeanPrinter
{
 public:
  LeanPrinter();
  ~LeanPrinter();

  /**
   * Print the full proof of assertions => false by pfn.
   */
  void print(std::ostream& out,
             const std::vector<Node>& assertions,
             std::shared_ptr<ProofNode> pfn);

 private:
  void printSort(std::ostream& out, TypeNode tn);

  void printConstant(std::ostream& out, TNode n);

  void printTermList(std::ostream& out, LetBinding& lbind, TNode n);

  void printTermList(std::ostream& out,
                     LetBinding& lbind,
                     const std::vector<Node>& children);

  void printTerm(std::ostream& out,
                 LetBinding& lbind,
                 TNode n,
                 bool letTop = true);

  void printLetList(std::ostream& out, LetBinding& lbind);

  /**
   * For each proof node, the final Lean output's formatting depends on
   *  the particular proof rule. For example, a chain resolution must be
   *  converted into a series of sequential resolutions.
   * This method cases on the Lean proof rules (./lean_rules.h) and prints
   *  to the ostream& out.
   * Prints proof node children before parents, unless we encounter the
   *  SCOPE rule, in which case we print "assume" and bind a new variable.
   */
  void printProof(std::ostream& out,
                  size_t& id,
                  uint64_t offset,
                  std::shared_ptr<ProofNode> pfn,
                  LetBinding& lbind,
                  std::map<const ProofNode*, size_t>& pfMap,
                  std::map<Node, size_t>& pfAssumpMap);

  void printOffset(std::ostream& out, uint64_t offset) const;

  void printStepId(std::ostream& out,
                   const ProofNode* pfn,
                   const std::map<const ProofNode*, size_t>& pfMap,
                   const std::map<Node, size_t>& pfAssumpMap);


  Node d_false;

  std::set<LeanRule> d_letRules;
};

}  // namespace proof
}  // namespace cvc5

#endif
