/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the Sygus API.
 *
 * A simple demonstration of how to use the Sygus API to synthesize max and min
 * functions.
 */

#include <cvc5/cvc5.h>

#include <iostream>

#include "utils.h"

using namespace cvc5;

int main()
{
  Solver slv;

  // required options
  slv.setOption("sygus", "true");
  slv.setOption("incremental", "false");
  // slv.setOption("trace", "sygus-enum-exc");
  // slv.setOption("trace", "sygus-engine");
  // slv.setOption("trace", "datatypes-rewrite");
  // slv.setOption("sygus-rewriter", "none");

  // set the logic
  slv.setLogic("NIA");

  Sort integer = slv.getIntegerSort();

  // declare input variables for the functions-to-synthesize
  Term x = slv.mkVar(integer, "x");

  // declare the grammar non-terminals
  Term start = slv.mkVar(integer, "Start");

  // define the rules
  Term zero = slv.mkInteger(0);
  Term one = slv.mkInteger(1);
  Term two = slv.mkInteger(2);
  Term three = slv.mkInteger(3);
  Term thirtyOne = slv.mkInteger(31);

  Term add = slv.mkTerm(Kind::ADD, {start, start});
  Term mult = slv.mkTerm(Kind::MULT, {start, start});

  Weight w = slv.declareWeight("w");

  // create the grammar object
  Grammar g = slv.mkGrammar({x}, {start});

  // bind each non-terminal to its rules
  g.addRules(start, {zero, one, three, x});
  g.addRule(start, add, {{w, one}});
  g.addRule(start, mult, {{w, thirtyOne}});

  // declare the functions-to-synthesize. Optionally, provide the grammar
  // constraints
  Term f = slv.synthFun("f", {x}, integer, g);

  // declare universal variables.
  Term varX = slv.declareSygusVar("x", integer);

  Term fX = slv.mkTerm(Kind::APPLY_UF, {f, varX});
  Term twoX = slv.mkTerm(Kind::MULT, {two, varX});
  Term threeX = slv.mkTerm(Kind::MULT, {three, varX});

  // add semantic constraints
  // (constraint (= (f x) (* 3 x)))
  slv.addSygusConstraint(slv.mkTerm(Kind::EQUAL, {fX, threeX}));

  // declare weight symbol
  Term wF = slv.mkWeightSymbol(w, f);

  // add semantic constraints
  // (constraint (= (_ w f) 2))
  slv.addSygusConstraint(slv.mkTerm(Kind::EQUAL, {wF, two}));

  // print solutions if available
  if (slv.checkSynth().hasSolution())
  {
    // Output should be equivalent to:
    // (
    //   (define-fun f ((x Int)) Int (+ x (+ x x)))
    // )
    std::vector<Term> terms = {f};
    utils::printSynthSolutions(terms, slv.getSynthSolutions(terms));
  }

  return 0;
}
