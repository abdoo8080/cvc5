/*********************                                                        */
/*! \file lean_post_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the Lean post processor
 **/

#include "proof/lean/lean_post_processor.h"

#include "expr/skolem_manager.h"
#include "proof/lazy_proof.h"
#include "proof/lean/lean_rules.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "util/bitvector.h"
#include "util/rational.h"

namespace cvc5::internal {

namespace proof {

std::unordered_map<PfRule, LeanRule, PfRuleHashFunction> s_pfRuleToLeanRule = {
    {PfRule::EQ_RESOLVE, LeanRule::EQ_RESOLVE},
    {PfRule::AND_ELIM, LeanRule::AND_ELIM},
    {PfRule::NOT_OR_ELIM, LeanRule::NOT_OR_ELIM},
    {PfRule::NOT_AND, LeanRule::NOT_AND},
    {PfRule::REFL, LeanRule::REFL},
    {PfRule::THEORY_REWRITE, LeanRule::TH_TRUST_VALID},
    {PfRule::NOT_IMPLIES_ELIM1, LeanRule::NOT_IMPLIES1},
    {PfRule::NOT_IMPLIES_ELIM2, LeanRule::NOT_IMPLIES2},
    {PfRule::MODUS_PONENS, LeanRule::MODUS_PONENS},
    {PfRule::PREPROCESS, LeanRule::TH_TRUST_VALID},
    {PfRule::TRUE_INTRO, LeanRule::TRUE_INTRO},
    {PfRule::TRUE_ELIM, LeanRule::TRUE_ELIM},
    {PfRule::FALSE_INTRO, LeanRule::FALSE_INTRO},
    {PfRule::FALSE_ELIM, LeanRule::FALSE_ELIM},
    {PfRule::EQUIV_ELIM1, LeanRule::EQUIV_ELIM1},
    {PfRule::EQUIV_ELIM2, LeanRule::EQUIV_ELIM2},
    {PfRule::NOT_EQUIV_ELIM1, LeanRule::NOT_EQUIV_ELIM1},
    {PfRule::NOT_EQUIV_ELIM2, LeanRule::NOT_EQUIV_ELIM2},
    {PfRule::XOR_ELIM1, LeanRule::XOR_ELIM1},
    {PfRule::XOR_ELIM2, LeanRule::XOR_ELIM2},
    {PfRule::NOT_XOR_ELIM1, LeanRule::NOT_XOR_ELIM1},
    {PfRule::NOT_XOR_ELIM2, LeanRule::NOT_XOR_ELIM2},
    {PfRule::ITE_ELIM1, LeanRule::ITE_ELIM1},
    {PfRule::ITE_ELIM2, LeanRule::ITE_ELIM2},
    {PfRule::NOT_ITE_ELIM1, LeanRule::NOT_ITE_ELIM1},
    {PfRule::NOT_ITE_ELIM2, LeanRule::NOT_ITE_ELIM2},
    {PfRule::CNF_IMPLIES_POS, LeanRule::CNF_IMPLIES_POS},
    {PfRule::CNF_IMPLIES_NEG1, LeanRule::CNF_IMPLIES_NEG1},
    {PfRule::CNF_IMPLIES_NEG2, LeanRule::CNF_IMPLIES_NEG2},
    {PfRule::CNF_EQUIV_POS1, LeanRule::CNF_EQUIV_POS1},
    {PfRule::CNF_EQUIV_POS2, LeanRule::CNF_EQUIV_POS2},
    {PfRule::CNF_EQUIV_NEG1, LeanRule::CNF_EQUIV_NEG1},
    {PfRule::CNF_EQUIV_NEG2, LeanRule::CNF_EQUIV_NEG2},
    {PfRule::CNF_XOR_POS1, LeanRule::CNF_XOR_POS1},
    {PfRule::CNF_XOR_POS2, LeanRule::CNF_XOR_POS2},
    {PfRule::CNF_XOR_NEG1, LeanRule::CNF_XOR_NEG1},
    {PfRule::CNF_XOR_NEG2, LeanRule::CNF_XOR_NEG2},
    {PfRule::CNF_ITE_POS1, LeanRule::CNF_ITE_POS1},
    {PfRule::CNF_ITE_POS2, LeanRule::CNF_ITE_POS2},
    {PfRule::CNF_ITE_POS3, LeanRule::CNF_ITE_POS3},
    {PfRule::CNF_ITE_NEG1, LeanRule::CNF_ITE_NEG1},
    {PfRule::CNF_ITE_NEG2, LeanRule::CNF_ITE_NEG2},
    {PfRule::CNF_ITE_NEG3, LeanRule::CNF_ITE_NEG3},
    {PfRule::NOT_NOT_ELIM, LeanRule::NOT_NOT_ELIM},
    {PfRule::ARRAYS_READ_OVER_WRITE, LeanRule::READ_OVER_WRITE},
    {PfRule::ARRAYS_READ_OVER_WRITE_CONTRA, LeanRule::READ_OVER_WRITE_CONTRA},
    {PfRule::ARRAYS_READ_OVER_WRITE_1, LeanRule::READ_OVER_WRITE_ID},
    {PfRule::ARRAYS_EXT, LeanRule::ARRAY_EXT},
    {PfRule::SKOLEM_INTRO, LeanRule::SKOLEM_INTRO},
};

LeanProofPostprocess::LeanProofPostprocess(ProofNodeManager* pnm,
                                           LeanNodeConverter& lnc)
    : d_cb(new LeanProofPostprocessCallback(pnm, lnc)),
      d_cbCl(new LeanProofPostprocessClConnectCallback(pnm, lnc)),
      d_pnm(pnm)
{
}

LeanProofPostprocessCallback::LeanProofPostprocessCallback(
    ProofNodeManager* pnm, LeanNodeConverter& lnc)
    : d_pnm(pnm), d_lnc(lnc)
{
  NodeManager* nm = NodeManager::currentNM();
  d_empty = d_lnc.convert(nm->mkNode(kind::SEXPR));
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void LeanProofPostprocessCallback::addLeanStep(
    Node res,
    LeanRule rule,
    Node convertedResult,
    bool isClause,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> leanArgs = {
      NodeManager::currentNM()->mkConstInt(Rational(static_cast<uint32_t>(rule))),
      res,
      convertedResult,
      isClause ? d_true : d_false};
  leanArgs.insert(leanArgs.end(), args.begin(), args.end());
  bool success CVC5_UNUSED =
      cdp.addStep(res, PfRule::LEAN_RULE, children, leanArgs);
  Assert(success);
}

bool LeanProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                const std::vector<Node>& fa,
                                                bool& continueUpdate)
{
  return pn->getRule() != PfRule::LEAN_RULE && pn->getRule() != PfRule::ASSUME;
};

bool LeanProofPostprocessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  Trace("test-lean") << "Updating rule " << id << ": " << res << "\n.."
                     << children.size() << " children: " << children << "\n.."
                     << args.size() << " args: " << args << "\n";
  NodeManager* nm = NodeManager::currentNM();
  switch (id)
  {
    // create clausal conclusion. Shortcut if before scope
    case PfRule::IMPLIES_ELIM:
    {
      // regular case, just turn conclusion into clause
      addLeanStep(res,
                  LeanRule::IMPLIES_ELIM,
                  d_lnc.convert(res),
                  false,
                  children,
                  {},
                  *cdp);
      break;
    }
    // create clausal conclusion
    case PfRule::SCOPE:
    {
      bool negation = false;
      // new result is an or with all assumptions negated and the original
      // conclusion
      std::vector<Node> newResChildren;
      std::vector<Node> newArgs;
      for (const Node& n : args)
      {
        newResChildren.push_back(n.notNode());
        newArgs.push_back(d_lnc.convert(n));
      }
      if (res.getKind() == kind::NOT)
      {
        negation = true;
        newResChildren.push_back(d_false);
      }
      else
      {
        Assert(res.getKind() == kind::IMPLIES || res.getKind() == kind::OR);
        newResChildren.push_back(res[1]);
      }
      Node newRes = nm->mkNode(kind::OR, newResChildren);
      addLeanStep(newRes,
                  LeanRule::SCOPE,
                  d_lnc.convert(newRes),
                  false,
                  children,
                  newArgs,
                  *cdp);
      // add a lifting step from the OR above to the original conclusion. It
      // takes as arguments the number of assumptions and subproof conclusion
      newArgs.clear();
      newArgs.push_back(nm->mkConstInt(Rational(args.size())));
      if (!negation)
      {
        // only implication version takes tail
        newArgs.push_back(d_lnc.convert(newResChildren.back()));
      }
      addLeanStep(
          res,
          negation ? LeanRule::LIFT_N_OR_TO_NEG : LeanRule::LIFT_N_OR_TO_IMP,
          d_lnc.convert(res),
          false,
          {newRes},
          newArgs,
          *cdp);
      break;
    }
    // only the rule changes and can be described with a pure mapping
    case PfRule::EQ_RESOLVE:
    case PfRule::NOT_IMPLIES_ELIM1:
    case PfRule::NOT_IMPLIES_ELIM2:
    case PfRule::TRUE_INTRO:
    case PfRule::TRUE_ELIM:
    case PfRule::FALSE_INTRO:
    case PfRule::FALSE_ELIM:
    case PfRule::MODUS_PONENS:
    case PfRule::NOT_NOT_ELIM:
    {
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  false,
                  children,
                  {},
                  *cdp);
      break;
    }
    case PfRule::REFL:
    {
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  false,
                  children,
                  {d_lnc.convert(args[0])},
                  *cdp);
      break;
    }
    case PfRule::NOT_OR_ELIM:
    case PfRule::AND_ELIM:
    {
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  false,
                  children,
                  args,
                  *cdp);
      break;
    }
    case PfRule::CONTRA:
    {
      addLeanStep(
          res, LeanRule::CONTRADICTION, d_empty, true, children, {}, *cdp);
      break;
    }
    // minor reasoning to clean args
    case PfRule::PREPROCESS:
    case PfRule::THEORY_REWRITE:
    case PfRule::ARRAYS_READ_OVER_WRITE:
    case PfRule::ARRAYS_READ_OVER_WRITE_CONTRA:
    case PfRule::ARRAYS_READ_OVER_WRITE_1:
    {
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  false,
                  children,
                  {},
                  *cdp);
      break;
    }
    // retrieve witness form
    case PfRule::ARRAYS_EXT:
    {
      // The skolem is res[0][0][1]
      Node k = res[0][0][1];
      Node var = SkolemManager::getWitnessForm(k)[0][0];
      Trace("test-lean") << "skolem " << k << " has witness form "
                         << SkolemManager::getWitnessForm(k) << ", its ID is "
                         << var.getId() << "\n";
      // arguments will be the id of the variable and its sort
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  false,
                  children,
                  {nm->mkConstInt(Rational(var.getId())),
                   nm->mkBoundVar(var.getType().getName(), nm->sExprType())},
                  *cdp);
      break;
    }
    // retrieve witness
    case PfRule::SKOLEM_INTRO:
    {
      // The skolem is res[0], its original form is res[1]. Create a "fake"
      // choice term with spurious variable with id 0
      AlwaysAssert(res[1] == SkolemManager::getOriginalForm(res[0]));
      Trace("test-lean") << "skolem " << res[0] << ", kind " << res[0].getKind()
                         << ", has original form "
                         << SkolemManager::getOriginalForm(res[1]) << "\n";
      Node original = d_lnc.convert(res[1]);
      Node witness = nm->mkNode(kind::SEXPR,
                                d_lnc.mkPrintableOp(kind::WITNESS),
                                nm->mkConstInt(Rational(0)),
                                original);
      // arguments will be the id of the variable and its sort
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  d_lnc.convert(res),
                  false,
                  {},
                  {},
                  *cdp);
      break;
    }
    case PfRule::REMOVE_TERM_FORMULA_AXIOM:
    {
      AlwaysAssert(res.getKind() == kind::ITE)
          << "Only support removal of ITEs\n";
      addLeanStep(
          res, LeanRule::ITE_INTRO, d_lnc.convert(res), false, {}, {}, *cdp);
      break;
    }
    // BV
    case PfRule::BV_BITBLAST_STEP:
    {
      Kind k = res[0].getKind();
      switch (k)
      {
        case kind::CONST_BITVECTOR:
        {
          addLeanStep(res,
                      LeanRule::BITBLAST_VAL,
                      d_lnc.convert(res),
                      false,
                      {},
                      {},
                      *cdp);
          break;
        }
        case kind::VARIABLE:
        case kind::SKOLEM:
        {
          addLeanStep(res,
                      LeanRule::BITBLAST_VAR,
                      d_lnc.convert(res),
                      false,
                      {},
                      // the size of the bv is the number of children of the
                      // bitblasted term
                      {nm->mkConstInt(Rational(res[1].getNumChildren()))},
                      *cdp);
          break;
        }
        case kind::BITVECTOR_ULT:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          // if one of the bitblasted terms is the resulting of bitblasting a
          // constant, the rule is different. This is because cvc5 hardcodes
          // simplifications during the bitblasting (like conjunction with
          // Boolean constants, equalities with Boolean constants being
          // eliminated etc). A bitblasted term is the result of bitblasting a
          // constant if its children are Boolean constants.
          bool hasValue = res[0][0][0].getKind() == kind::CONST_BOOLEAN
                          || res[0][1][0].getKind() == kind::CONST_BOOLEAN;
          addLeanStep(res,
                      hasValue? LeanRule::BITBLAST_ULT_VAL : LeanRule::BITBLAST_ULT,
                      d_lnc.convert(res),
                      false,
                      {},
                      // the size of the bv is the number of children of the
                      // bitblasted term
                      {nm->mkConstInt(Rational(res[0][0].getNumChildren()))},
                      *cdp);
          break;
        }
        case kind::EQUAL:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          bool hasValue = res[0][0][0].getKind() == kind::CONST_BOOLEAN
                          || res[0][1][0].getKind() == kind::CONST_BOOLEAN;
          addLeanStep(res,
                      hasValue? LeanRule::BITBLAST_EQ_VAL : LeanRule::BITBLAST_EQ,
                      d_lnc.convert(res),
                      false,
                      {},
                      {nm->mkConstInt(Rational(res[0][0].getNumChildren()))},
                      *cdp);
          break;
        }
        case kind::BITVECTOR_AND:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          bool hasValue = res[0][0][0].getKind() == kind::CONST_BOOLEAN
                          || res[0][1][0].getKind() == kind::CONST_BOOLEAN;
          addLeanStep(res,
                      hasValue? LeanRule::BITBLAST_AND_VAL : LeanRule::BITBLAST_AND,
                      d_lnc.convert(res),
                      false,
                      {},
                      {nm->mkConstInt(Rational(res[0][0].getNumChildren()))},
                      *cdp);
          break;
        }
        case kind::BITVECTOR_ADD:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          addLeanStep(res,
                      LeanRule::BITBLAST_ADD,
                      d_lnc.convert(res),
                      false,
                      {},
                      {nm->mkConstInt(Rational(res[0][0].getNumChildren()))},
                      *cdp);
          break;
        }
        case kind::BITVECTOR_CONCAT:
        {
          // both arguments must be bitblasted terms
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM
                       && res[0][1].getKind() == kind::BITVECTOR_BB_TERM);
          addLeanStep(res,
                      LeanRule::BITBLAST_CONCAT,
                      d_lnc.convert(res),
                      false,
                      {},
                      {nm->mkConstInt(Rational(res[0][0].getNumChildren())),
                       nm->mkConstInt(Rational(res[0][1].getNumChildren()))},
                      *cdp);
          break;
        }
        case kind::BITVECTOR_EXTRACT:
        {
          // argument must be a bitblasted term
          AlwaysAssert(res[0][0].getKind() == kind::BITVECTOR_BB_TERM);
          std::vector<Node> newArgs{nm->mkConstInt(Rational(res[0][0].getNumChildren()))};
          addLeanStep(res,
                      LeanRule::BITBLAST_EXTRACT,
                      d_lnc.convert(res),
                      false,
                      {},
                      newArgs,
                      *cdp);
          break;
        }
        default:
        {
          Trace("test-lean") << "unhandled bitblasting kind " << k << "\n";
          addLeanStep(res,
                      LeanRule::UNKNOWN,
                      Node::null(),
                      false,
                      children,
                      args,
                      *cdp);
        }
      }
      break;
    }
    // create clausal conclusion and remove arguments
    case PfRule::CNF_IMPLIES_POS:
    case PfRule::CNF_IMPLIES_NEG1:
    case PfRule::CNF_IMPLIES_NEG2:
    case PfRule::CNF_EQUIV_POS1:
    case PfRule::CNF_EQUIV_POS2:
    case PfRule::CNF_EQUIV_NEG1:
    case PfRule::CNF_EQUIV_NEG2:
    case PfRule::CNF_XOR_POS1:
    case PfRule::CNF_XOR_POS2:
    case PfRule::CNF_XOR_NEG1:
    case PfRule::CNF_XOR_NEG2:
    case PfRule::CNF_ITE_POS1:
    case PfRule::CNF_ITE_POS2:
    case PfRule::CNF_ITE_POS3:
    case PfRule::CNF_ITE_NEG1:
    case PfRule::CNF_ITE_NEG2:
    case PfRule::CNF_ITE_NEG3:
    case PfRule::NOT_AND:
    case PfRule::EQUIV_ELIM1:
    case PfRule::EQUIV_ELIM2:
    case PfRule::NOT_EQUIV_ELIM1:
    case PfRule::NOT_EQUIV_ELIM2:
    case PfRule::XOR_ELIM1:
    case PfRule::XOR_ELIM2:
    case PfRule::NOT_XOR_ELIM1:
    case PfRule::NOT_XOR_ELIM2:
    case PfRule::ITE_ELIM1:
    case PfRule::ITE_ELIM2:
    case PfRule::NOT_ITE_ELIM1:
    case PfRule::NOT_ITE_ELIM2:
    {
      std::vector<Node> resLits{res.begin(), res.end()};
      addLeanStep(res,
                  s_pfRuleToLeanRule.at(id),
                  // TODO make a "convert clause" which takes the vector?
                  d_lnc.convert(nm->mkNode(kind::SEXPR, resLits)),
                  true,
                  children,
                  {},
                  *cdp);
      break;
    }
    // minor reasoning to pick the rule
    case PfRule::SYMM:
    {
      addLeanStep(
          res,
          res.getKind() == kind::EQUAL ? LeanRule::SYMM : LeanRule::NEG_SYMM,
          d_lnc.convert(res),
          false,
          children,
          {},
          *cdp);
      break;
    }
    //-------------- bigger conversions
    // break down CONG chain
    case PfRule::HO_CONG:
    case PfRule::CONG:
    {
      Kind k = res[0].getKind();
      if (res[0].isClosure())
      {
        // For now we only support the case where the variables are the same.
        // Renaming will be done afterwards
        AlwaysAssert(children[0][0] == children[0][1])
            << "Lean printing without support for congruence over closures "
               "with renaming\n";
        AlwaysAssert(k == kind::FORALL || k == kind::LAMBDA)
            << "Lean printing only supports FORALL/LAMBDA binders for now. "
               "Found kind "
            << k << "\n";
        // break down n-ary binder into chain of binds. Start with term
        Node opBinder = args.size() == 2 ? args[1] : args[0];
        Node currEq = children[1];
        // iterate over variable list
        for (size_t i = 1, nVars = children[0][0].getNumChildren(); i < nVars;
             ++i)
        {
          size_t j = nVars - i;
          AlwaysAssert(j > 0);
          // build dummy equality of partial apps of var j
          Node varEq = nm->mkNode(
              kind::SEXPR,
              nm->mkNode(kind::SEXPR, opBinder, children[0][0][j], currEq[0]),
              nm->mkNode(kind::SEXPR, opBinder, children[0][0][j], currEq[1]));
          // add step that justify equality of partial apps
          addLeanStep(varEq,
                      k == kind::FORALL ? LeanRule::BIND_PARTIAL
                                        : LeanRule::BIND_LAMBDA_PARTIAL,
                      Node::null(),
                      false,
                      {currEq},
                      {},
                      *cdp);
          currEq = varEq;
        }
        addLeanStep(res,
                    k == kind::FORALL ? LeanRule::BIND : LeanRule::BIND_LAMBDA,
                    d_lnc.convert(res),
                    false,
                    {currEq},
                    {},
                    *cdp);
      }
      size_t nchildren = children.size();
      Node eqNode = ProofRuleChecker::mkKindNode(kind::EQUAL);
      Node op, opEq;
      bool isHO = id == PfRule::HO_CONG;
      // There are two differences for HO_CONG vs the regular one: the operators
      // differ, so instead of a REFL steps for them we have the first premise.
      // Also, that first premise is absent in the regular congruence. To keep
      // things modular below, we just use the first premise as the operator
      // equality and below when adding the premises we start from the second
      // premise
      if (isHO)
      {
        // since this is used to identify internal steps, either one of the
        // operators is fine. We pick the leftmost one
        op = children[0][0];
        opEq = children[0];
      }
      else
      {
        op = args.size() == 2 ? args[1] : args[0];
        // add internal refl step
        opEq = nm->mkNode(kind::SEXPR, eqNode, op, op);
        addLeanStep(opEq,
                    LeanRule::REFL_PARTIAL,
                    Node::null(),
                    false,
                    {},
                    {d_lnc.mkPrintableOp(op)},
                    *cdp);
      }
      // Are we doing congruence of an n-ary operator with more than two
      // arguments? If so, notice that op is a binary operator and we must apply
      // congruence in a special way.
      //
      // special case: some kinds are n-ary but expect operators which are not,
      // so we handle them in a regular manner below
      bool isNary = NodeManager::isNAryKind(k) && k != kind::APPLY_UF
                    && k != kind::APPLY_CONSTRUCTOR && k != kind::APPLY_SELECTOR
                    && k != kind::APPLY_TESTER;
      if (isNary && nchildren > 2)
      {
        AlwaysAssert(!isHO);
        // start with the last argument
        Node currEq = children[nchildren - 1];
        for (size_t i = 1; i < nchildren; ++i)
        {
          size_t j = nchildren - i - 1;
          // build equality of partial apps of argument j. We add the index as
          // part of the node to guarantee that there is no ambiguity with
          // applications that have repeated arguments
          std::vector<Node> argAppEqChildren{
              eqNode,
              nm->mkConstInt(Rational(i)),
              nm->mkNode(kind::SEXPR, op, children[j][0]),
              nm->mkNode(kind::SEXPR, op, children[j][1])};
          Node argAppEq = nm->mkNode(kind::SEXPR, argAppEqChildren);
          // add step that justify equality of partial apps
          addLeanStep(argAppEq,
                      LeanRule::CONG_PARTIAL,
                      Node::null(),
                      false,
                      {opEq, children[j]},
                      {},
                      *cdp);
          // last case, we add a CONG step to the original conclusion
          if (j == 0)
          {
            addLeanStep(res,
                        LeanRule::CONG,
                        d_lnc.convert(res),
                        false,
                        {argAppEq, currEq},
                        {},
                        *cdp);
          }
          else
          {
            // build equality of full app with argument j and previous equality
            // in chain
            Node nextEq =
                nm->mkNode(kind::SEXPR,
                           eqNode,
                           nm->mkNode(kind::SEXPR, argAppEq, currEq[0]),
                           nm->mkNode(kind::SEXPR, argAppEq, currEq[1]));
            addLeanStep(nextEq,
                        LeanRule::CONG_PARTIAL,
                        Node::null(),
                        false,
                        {argAppEq, currEq},
                        {},
                        *cdp);
            currEq = nextEq;
          }
        }
        break;
      }
      // regular congruence over non-nary, non-closures
      //
      // add internal steps
      Node curL = op;
      Node curR = op;
      Node currEq = opEq;
      for (size_t i = !isHO ? 0 : 1; i < nchildren - 1; ++i)
      {
        curL = nm->mkNode(kind::SEXPR, currEq, children[i][0]);
        curR = nm->mkNode(kind::SEXPR, currEq, children[i][0]);
        Node nextEq = nm->mkNode(kind::SEXPR, eqNode, curL, curR);
        addLeanStep(nextEq,
                    LeanRule::CONG_PARTIAL,
                    Node::null(),
                    false,
                    {currEq, children[i]},
                    {},
                    *cdp);
        Trace("test-lean") << "..cong internal: " << nextEq << " from "
                           << currEq << ", " << children[i] << "\n";
        currEq = nextEq;
      }
      addLeanStep(res,
                  LeanRule::CONG,
                  d_lnc.convert(res),
                  false,
                  {currEq, children.back()},
                  {},
                  *cdp);
      break;
    }
    case PfRule::TRANS:
    {
      Node cur = children[0], first = children[0][0];
      for (size_t i = 1, size = children.size(); i < size - 1; ++i)
      {
        Node newCur = nm->mkNode(kind::EQUAL, first, children[i][1]);
        addLeanStep(newCur,
                    LeanRule::TRANS_PARTIAL,
                    Node::null(),
                    false,
                    {cur, children[i]},
                    {},
                    *cdp);
        cur = newCur;
      }
      addLeanStep(res,
                  LeanRule::TRANS,
                  d_lnc.convert(res),
                  false,
                  {cur, children.back()},
                  {},
                  *cdp);
      break;
    }
    case PfRule::AND_INTRO:
    {
      size_t size = children.size();
      Node cur = children[size - 1], first = children[0];
      for (size_t i = 1; i < size - 1; ++i)
      {
        size_t j = size - i - 1;
        Node newCur = nm->mkNode(kind::AND, children[j], cur);
        addLeanStep(newCur,
                    LeanRule::AND_INTRO_PARTIAL,
                    Node::null(),
                    false,
                    {
                        children[j],
                        cur,
                    },
                    {},
                    *cdp);
        cur = newCur;
      }
      addLeanStep(res,
                  LeanRule::AND_INTRO,
                  d_lnc.convert(res),
                  false,
                  {first, cur},
                  {},
                  *cdp);
      break;
    }
    //-------- clausal rules
    case PfRule::RESOLUTION:
    case PfRule::CHAIN_RESOLUTION:
    {
      Trace("test-lean") << push;
      Node cur = children[0];
      std::vector<Node> arePremisesSingletons{d_false, d_false};
      // Whether child 0 is a singleton list. The first child is used as an OR
      // non-singleton clause if it is not equal to its pivot L_1. Since it's
      // the first clause in the resolution it can only be equal to the pivot in
      // the case the polarity is true.
      Trace("test-lean") << "\t\ttesting args[0,1] " << args[0] << ", "
                         << args[1] << ", child 0 " << children[0] << "\n";
      if (children[0].getKind() != kind::OR
          || (args[0] == d_true && children[0] == args[1]))
      {
        arePremisesSingletons[0] = d_true;
      }
      // For all other children C_i the procedure is simliar. There is however a
      // key difference in the choice of the pivot element which is now the
      // L_{i-1}, i.e. the pivot of the child with the result of the i-1
      // resolution steps between the children before it. Therefore, if the
      // policy id_{i-1} is true, the pivot has to appear negated in the child
      // in which case it should not be a [(or F1 ... Fn)] node. The same is
      // true if it isn't the pivot element.
      for (size_t i = 1, size = children.size(); i < size; ++i)
      {
        Trace("test-lean") << "\t\ttesting args[" << 2 * (i - 1) << ","
                           << 2 * (i - 1) + 1 << "] " << args[2 * (i - 1)]
                           << ", " << args[2 * (i - 1) + 1] << ", child " << i
                           << " " << children[i] << "\n";
        if (children[i].getKind() != kind::OR
            || (args[2 * (i - 1)] == d_false
                && args[2 * (i - 1) + 1] == children[i]))
        {
          Trace("test-lean") << "\t\t\t..child is singleton\n";
          // mark that this premise is a singleton
          arePremisesSingletons[1] = d_true;
        }
        if (i < size - 1)
        {  // create a (unique) placeholder for the resulting binary
          // resolution. The placeholder is [res, i, pol, pivot], where pol and
          // pivot are relative to this part of the chain resolution
          Node pol = args[(i - 1) * 2];
          std::vector<Node> curArgs{d_lnc.convert(args[(i - 1) * 2 + 1]),
                                    arePremisesSingletons[0],
                                    arePremisesSingletons[1]};
          std::vector<Node> curChildren{
              res, nm->mkConstInt(Rational(i)), pol, curArgs[0]};
          Node newCur = nm->mkNode(kind::SEXPR, curChildren);
          Trace("test-lean")
              << "..res [internal] " << i << " has singleton premises "
              << arePremisesSingletons << "\n";
          addLeanStep(newCur,
                      pol.getConst<bool>() ? LeanRule::R0_PARTIAL
                                           : LeanRule::R1_PARTIAL,
                      Node::null(),
                      true,
                      {cur, children[i]},
                      curArgs,
                      *cdp);
          cur = newCur;
          // all the other resolutions in the chain are with the placeholder
          // clause as the first argument
          arePremisesSingletons[0] = Node::null();
          // reset next child to be computed whether singleton
          arePremisesSingletons[1] = d_false;
        }
      }
      // now check whether conclusion is a singleton
      //
      // If res is not an or node, then it's necessarily a singleton clause.
      bool isSingletonClause = res.getKind() != kind::OR;
      // Otherwise, we need to determine if res if it's of the form (or t1 ...
      // tn), corresponds to the clause (cl t1 ... tn) or to (cl (OR t1 ...
      // tn)). The only way in which the latter can happen is if res occurs as a
      // child in one of the premises, and is not eliminated afterwards. So we
      // search for res as a subterm of some children, which would mark its last
      // insertion into the resolution result. If res does not occur as the
      // pivot to be eliminated in a subsequent premise, then, and only then, it
      // is a singleton clause.
      if (!isSingletonClause)
      {
        size_t i;
        // Find out which child introduced res. There can be at most one by
        // design of the proof production. After the loop finishes i is the
        // index of the child C_i that introduced res. If i=0 none of the
        // children introduced res as a subterm and therefore it cannot be a
        // singleton clause.
        for (i = children.size(); i > 0; --i)
        {
          // only non-singleton clauses may be introducing
          // res, so we only care about non-singleton or nodes. We check then
          // against the kind and whether the whole or node occurs as a pivot of
          // the respective resolution
          if (children[i - 1].getKind() != kind::OR)
          {
            continue;
          }
          size_t pivotIndex = (i != 1) ? 2 * (i - 1) - 1 : 1;
          if (args[pivotIndex] == children[i - 1]
              || args[pivotIndex].notNode() == children[i - 1])
          {
            continue;
          }
          // if res occurs as a subterm of a non-singleton premise
          if (std::find(children[i - 1].begin(), children[i - 1].end(), res)
              != children[i - 1].end())
          {
            break;
          }
        }

        // If res is a subterm of one of the children we still need to check if
        // that subterm is eliminated
        if (i > 0)
        {
          bool posFirst = (i == 1) ? (args[0] == d_true)
                                   : (args[(2 * (i - 1)) - 2] == d_true);
          Node pivot = (i == 1) ? args[1] : args[(2 * (i - 1)) - 1];

          // Check if it is eliminated by the previous resolution step
          if ((res == pivot && !posFirst)
              || (res.notNode() == pivot && posFirst)
              || (pivot.notNode() == res && posFirst))
          {
            // We decrease i by one such that isSingletonClause is set to false
            --i;
          }
          else
          {
            // Otherwise check if any subsequent premise eliminates it
            for (; i < children.size(); ++i)
            {
              posFirst = args[(2 * i) - 2] == d_true;
              pivot = args[(2 * i) - 1];
              // To eliminate res, the clause must contain it with opposite
              // polarity. There are three successful cases, according to the
              // pivot and its sign
              //
              // - res is the same as the pivot and posFirst is true, which
              // means that the clause contains its negation and eliminates it
              //
              // - res is the negation of the pivot and posFirst is false, so
              // the clause contains the node whose negation is res. Note that
              // this case may either be res.notNode() == pivot or res ==
              // pivot.notNode().
              if ((res == pivot && posFirst)
                  || (res.notNode() == pivot && !posFirst)
                  || (pivot.notNode() == res && !posFirst))
              {
                break;
              }
            }
          }
        }
        // if not eliminated (loop went to the end), then it's a singleton
        // clause
        isSingletonClause = i == children.size();
      }
      Node conclusion;
      size_t i = children.size() - 1;
      Trace("test-lean") << "..res [final] " << i << " has singleton premises "
                         << arePremisesSingletons << "\n";
      std::vector<Node> curArgs{d_lnc.convert(args[(i - 1) * 2 + 1]),
                                arePremisesSingletons[0],
                                arePremisesSingletons[1]};
      if (!isSingletonClause)
      {
        std::vector<Node> resLits{res.begin(), res.end()};
        conclusion = nm->mkNode(kind::SEXPR, resLits);
      }
      // conclusion is empty list
      else if (res == d_false)
      {
        conclusion = d_empty;
      }
      else
      {
        conclusion = nm->mkNode(kind::SEXPR, res);
      }
      Trace("test-lean") << "..final step of res " << res << " with children "
                         << cur << ", " << children.back() << " and args "
                         << conclusion << ", " << curArgs << "\n";
      addLeanStep(
          res,
          args[(i - 1) * 2].getConst<bool>() ? LeanRule::R0 : LeanRule::R1,
          d_lnc.convert(conclusion),
          true,
          {cur, children.back()},
          curArgs,
          *cdp);
      Trace("test-lean") << pop;
      break;
    }
    case PfRule::REORDERING:
    {
      // for each literal in the resulting clause, get its position in the
      // premise
      std::vector<Node> pos;
      size_t size = res.getNumChildren();
      std::vector<Node> resLits;
      for (const Node& resLit : res)
      {
        resLits.push_back(resLit);
        for (size_t i = 0; i < size; ++i)
        {
          if (children[0][i] == resLit)
          {
            // we force the naturals to be internal symbols so that they are not
            // converted when we build the final sexpression
            pos.push_back(d_lnc.mkInternalSymbol(nm->mkConstInt(Rational(i))));
          }
        }
      }
      // turn conclusion into clause
      addLeanStep(res,
                  LeanRule::REORDER,
                  d_lnc.convert(nm->mkNode(kind::SEXPR, resLits)),
                  true,
                  children,
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, pos))},
                  *cdp);
      break;
    }
    case PfRule::FACTORING:
    {
      Node conclusion;
      // conclusion is singleton only if it occurs in premise
      if (res.getKind() == kind::OR
          && std::find(children[0].begin(), children[0].end(), res)
                 == children[0].end())
      {
        std::vector<Node> resLits{res.begin(), res.end()};
        conclusion = nm->mkNode(kind::SEXPR, resLits);
      }
      else
      {
        conclusion = nm->mkNode(kind::SEXPR, res);
      }
      addLeanStep(res,
                  LeanRule::FACTORING,
                  d_lnc.convert(conclusion),
                  true,
                  children,
                  {},
                  *cdp);
      break;
    }
    case PfRule::CNF_AND_POS:
    {
      std::vector<Node> resArgs{args[0].begin(), args[0].end()};
      addLeanStep(res,
                  LeanRule::CNF_AND_POS,
                  d_lnc.convert(nm->mkNode(kind::SEXPR, res[0], res[1])),
                  true,
                  children,
                  // don't convert second argument since naturals should be
                  // printed as is
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, resArgs)), args[1]},
                  *cdp);
      break;
    }
    case PfRule::CNF_AND_NEG:
    {
      std::vector<Node> resArgs{args[0].begin(), args[0].end()};
      std::vector<Node> resLits{res.begin(), res.end()};
      addLeanStep(res,
                  LeanRule::CNF_AND_NEG,
                  d_lnc.convert(nm->mkNode(kind::SEXPR, resLits)),
                  true,
                  children,
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, resArgs))},
                  *cdp);
      break;
    }
    case PfRule::CNF_OR_POS:
    {
      std::vector<Node> resLits{res.begin(), res.end()};
      std::vector<Node> resArgs{args[0].begin(), args[0].end()};
      addLeanStep(res,
                  LeanRule::CNF_OR_POS,
                  d_lnc.convert(nm->mkNode(kind::SEXPR, resLits)),
                  true,
                  children,
                  // don't convert second argument since naturals should be
                  // printed as is
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, resArgs))},
                  *cdp);
      break;
    }
    case PfRule::CNF_OR_NEG:
    {
      std::vector<Node> resArgs{args[0].begin(), args[0].end()};
      addLeanStep(res,
                  LeanRule::CNF_OR_NEG,
                  d_lnc.convert(nm->mkNode(kind::SEXPR, res[0], res[1])),
                  true,
                  children,
                  {d_lnc.convert(nm->mkNode(kind::SEXPR, resArgs)), args[1]},
                  *cdp);
      break;
    }
    default:
    {
      Trace("test-lean") << "Unhandled rule " << id << "\n";
      addLeanStep(
          res, LeanRule::UNKNOWN, Node::null(), false, children, args, *cdp);
    }
  };
  return true;
}

LeanProofPostprocessClConnectCallback::LeanProofPostprocessClConnectCallback(
    ProofNodeManager* pnm, LeanNodeConverter& lnc)
    : LeanProofPostprocessCallback(pnm, lnc)
{
  // init conversion rules
  NodeManager* nm = NodeManager::currentNM();
  d_conversionRules = {
      nm->mkConstInt(Rational(static_cast<uint32_t>(LeanRule::CL_OR))),
      nm->mkConstInt(Rational(static_cast<uint32_t>(LeanRule::CL_ASSUME))),
      nm->mkConstInt(Rational(static_cast<uint32_t>(LeanRule::CL_SINGLETON))),
      nm->mkConstInt(Rational(static_cast<uint32_t>(LeanRule::TH_ASSUME))),
  };
  // Rules that take clauses
  d_clausalPremisesRules = {LeanRule::R0,
                            LeanRule::R0_PARTIAL,
                            LeanRule::R1,
                            LeanRule::R1_PARTIAL,
                            LeanRule::FACTORING,
                            LeanRule::REORDER,
                            LeanRule::TRUST};
  d_resRules = {
      LeanRule::R0, LeanRule::R0_PARTIAL, LeanRule::R1, LeanRule::R1_PARTIAL};
}

LeanProofPostprocessClConnectCallback::~LeanProofPostprocessClConnectCallback()
{
}

bool LeanProofPostprocessClConnectCallback::shouldUpdate(
    std::shared_ptr<ProofNode> pn,
    const std::vector<Node>& fa,
    bool& continueUpdate)
{
  // ignore non-lean rules and the steps which are introduce here: CL_ASSUME,
  // CL_OR, TH_ASSUME
  if (pn->getRule() != PfRule::LEAN_RULE
      || d_conversionRules.find(pn->getArguments()[0])
             != d_conversionRules.end())
  {
    return false;
  }
  if (processed.find(pn.get()) == processed.end())
  {
    processed.insert(pn.get());
    return true;
  }
  return false;
}

bool LeanProofPostprocessClConnectCallback::update(
    Node res,
    PfRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof* cdp,
    bool& continueUpdate)
{
  NodeManager* nm = NodeManager::currentNM();
  LeanRule rule = getLeanRule(args[0]);
  Trace("test-lean") << "ClConnectUpdating rule:\nres: " << res
                     << "\nid: " << rule << "\nchildren: " << children
                     << "\nargs: " << args << "\n";
  bool updated = false;
  // Check if every child of clausal rule is itself clausal. Otherwise add
  // "clausal glue", i.e., the rule the converts terms to clauses. For example
  //
  //  t1   C2  t3
  // ------------ R
  //       C
  //
  // in which R is a clausal rule, C and C2 are clausal, t1 and t2 are terms,
  // one would make it
  //
  //  t1         t3
  //  --- G     --- G
  //  C1    C2  C3
  // --------------- R
  //       C
  //
  // in which C1 and C3 are the clausal forms of t1 and t3.
  //
  // Note that the update of cdp is relatively simple, as it suffices to add
  // steps to derive C1/C3 from t1/t3 with the suitable clausal conversion.,
  // afterwards redefining the derivation of C with R.
  if (d_clausalPremisesRules.find(rule) != d_clausalPremisesRules.end())
  {
    std::vector<Node> newChildren{children.begin(), children.end()};
    // Resolution rules need further processing to determine whether each
    // premise is a singleton. This information was computed in the previous
    // pass and just needs to be checked now. Premises that are not singletons
    // need to be turned into clauses via the conversion rules.
    if (d_resRules.find(rule) != d_resRules.end())
    {
      // rule, original conclusion, converted conclusion, whether clausal,
      // pivot, prem1singleton, prem2singleton
      AlwaysAssert(args.size() == 7);
      // all binary
      AlwaysAssert(children.size() == 2);
      for (size_t i = 0; i < 2; ++i)
      {
        // check if child's conclusion is clausal, in which case nothing to
        // do*. Assumptions are never clausal, but since they're not converted
        // during the previous processing we need to special case.
        //
        // There is actually an extra case: if the child is clausal, must be a
        // singleton but actually is not it's necessary to convert it into a
        // singleton
        std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[i]);
        AlwaysAssert(childPf->getRule() == PfRule::ASSUME
                     || childPf->getArguments().size() > 3)
            << "childPf is " << *childPf.get();
        bool reqSingleton = args[5 + i] == d_true;
        bool isChildClausal = childPf->getArguments()[3] == d_true;
        if (childPf->getRule() != PfRule::ASSUME && isChildClausal
            && (!reqSingleton || children[i].getKind() != kind::OR))
        {
          continue;
        }
        Node newChild;
        LeanRule childRule;
        if (reqSingleton)
        {
          // add clAssume step if child is not clausal, otherwise add a
          // clSingleton step if the child is an OR (this may be an spurious
          // step if the clausal conclusion, which may be unknown, is already a
          // singleton, but it will not be wrong). If neither case, we continue.
          if (!isChildClausal)
          {
            childRule = LeanRule::CL_ASSUME;
          }
          else if (children[i].getKind() == kind::OR)
          {
            childRule = LeanRule::CL_SINGLETON;
          }
          else
          {
            continue;
          }
          newChild = d_lnc.convert(nm->mkNode(kind::SEXPR, children[i]));
        }
        else
        {
          // Add clOr step
          std::vector<Node> lits{children[i].begin(), children[i].end()};
          newChild = d_lnc.convert(nm->mkNode(kind::SEXPR, lits));
          childRule = LeanRule::CL_OR;
        }
        addLeanStep(
            newChild, childRule, newChild, true, {children[i]}, {}, *cdp);
        newChildren[i] = newChild;
      }
      // regardless of possible changes above, delete the excess arguments
      cdp->addStep(res, id, newChildren, {args.begin(), args.begin() + 5});
      return true;
    }
    // other rules either do not have premises or are applied on non-singleton
    // clauses, so always use CL_OR if premise is a term
    for (size_t i = 0, size = children.size(); i < size; ++i)
    {
      std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[i]);
      AlwaysAssert(childPf->getRule() == PfRule::ASSUME
                   || childPf->getArguments().size() > 3)
          << "childPf is " << *childPf.get();
      // child is already clausal
      if (childPf->getRule() != PfRule::ASSUME
          && childPf->getArguments()[3] == d_true)
      {
        continue;
      }
      // Add clOr step
      Assert(children[i].getKind() == kind::OR);
      std::vector<Node> lits{children[i].begin(), children[i].end()};
      newChildren[i] = d_lnc.convert(nm->mkNode(kind::SEXPR, lits));
      addLeanStep(newChildren[i],
                  LeanRule::CL_OR,
                  newChildren[i],
                  true,
                  {children[i]},
                  {},
                  *cdp);
      updated = true;
    }
    if (updated)
    {
      cdp->addStep(res, id, newChildren, args);
    }
    return updated;
  }
  Trace("test-lean") << "..not a clausal rule\n";
  // Check if every child of term rule is itself a term. Otherwise add
  // "term glue", i.e., the rule the converts clauses to terms. For example
  //
  //  t1|C1   t2  t3|C3
  // ------------------- R
  //          t
  //
  // in which R is a term rule, t, t1, t2 and t3 are terms, C1 and C3
  // are the clausal converted forms of t1 and t3, one would make it
  //
  //  C1         C3
  //  --- G     --- G
  //  t1    C2  t3
  // --------------- R
  //       C
  //
  // Note that the update of cdp is not simple, since it requires changing the
  // justifications for t1 and t3 and have the steps to derive C1 and C3 in
  // between the original premises of t1 and t3.
  for (size_t i = 0, size = children.size(); i < size; ++i)
  {
    std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[i]);
    const std::vector<Node>& argsOfChild = childPf->getArguments();
    AlwaysAssert(childPf->getRule() == PfRule::ASSUME || argsOfChild.size() > 3)
        << "childPf is " << *childPf.get();
    // child not clausal. Note this is the exact opposite of the tests we were
    // doing with the clausal rules above
    if (childPf->getRule() == PfRule::ASSUME || argsOfChild[3] == d_false)
    {
      continue;
    }
    Trace("test-lean-pf") << "..child " << i
                          << " is clausal: " << *childPf.get() << "\n";
    // Since the child is clausal, a step retrieving the OR term corresponding
    // to the clause will be added. A step is also needed to conclude the clause
    // from the original premises of the child. To build this step in the cdp we
    // need to add to it the proof nodes for these premises.
    std::vector<Node> childrenOfChild;
    const std::vector<std::shared_ptr<ProofNode>>& childrenPfsOfChild =
        childPf->getChildren();
    for (const std::shared_ptr<ProofNode>& cpoc : childrenPfsOfChild)
    {
      childrenOfChild.push_back(cpoc->getResult());
      // store in the proof
      cdp->addProof(cpoc);
    }
    // The new step has the same rule, concludes the clause, whose converted
    // form is the clause, and is clausal
    std::vector<Node> newArgs{
        argsOfChild[0], argsOfChild[2], argsOfChild[2], d_true};
    // Whatever other arguments the child proof had are incorporated
    newArgs.insert(newArgs.end(), argsOfChild.begin() + 4, argsOfChild.end());
    Trace("test-lean") << "..adding step for " << argsOfChild[2] << " from "
                       << childrenOfChild << " with args " << newArgs << "\n";
    cdp->addStep(argsOfChild[2], PfRule::LEAN_RULE, childrenOfChild, newArgs);
    // Now add the glue step to derive the term in a non-clausal rule
    std::vector<Node> replaceArgs{
        nm->mkConstInt(Rational(static_cast<uint32_t>(LeanRule::TH_ASSUME))),
        children[i],
        d_lnc.convert(children[i]),
        d_false};
    Trace("test-lean") << "..adding step for " << children[i] << " from "
                       << argsOfChild[2] << " with args " << replaceArgs
                       << "\n";
    // Note it's necessary to overwrite because the cdp contains a step for
    // children[i]
    cdp->addStep(children[i],
                 PfRule::LEAN_RULE,
                 {argsOfChild[2]},
                 replaceArgs,
                 true,
                 CDPOverwrite::ALWAYS);
    // Add thAssume step
    updated = true;
  }
  if (updated)
  {
    cdp->addStep(res, id, children, args);
  }
  return updated;
}

void LeanProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_pnm, *(d_cb.get()), false, false);
  updater.process(pf);
  ProofNodeUpdater updaterCl(d_pnm, *(d_cbCl.get()), false, false);
  // we don't need to convert the final scope, which has been lifted
  updaterCl.process(pf->getChildren()[0]->getChildren()[0]);
};

}  // namespace proof
}  // namespace cvc5::internal
