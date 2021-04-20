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

#include "expr/lazy_proof.h"
#include "expr/proof_checker.h"
#include "expr/proof_node_algorithm.h"
#include "expr/proof_node_manager.h"
#include "expr/skolem_manager.h"
#include "proof/lean/lean_rules.h"

namespace cvc5 {

namespace proof {

LeanProofPostprocessCallback::LeanProofPostprocessCallback(
    ProofNodeManager* pnm)
    : d_pnm(pnm), d_pc(pnm->getChecker())
{
  NodeManager* nm = NodeManager::currentNM();
  d_empty =
      nm->mkNode(kind::SEXPR,
                 nm->getSkolemManager()->mkDummySkolem(
                     "", nm->sExprType(), "", NodeManager::SKOLEM_EXACT_NAME));
  Trace("test-lean") << "d_empty is " << d_empty << "\n";
}

LeanProofPostprocess::LeanProofPostprocess(ProofNodeManager* pnm)
    : d_cb(new proof::LeanProofPostprocessCallback(pnm)), d_pnm(pnm)
{
}

bool LeanProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                const std::vector<Node>& fa,
                                                bool& continueUpdate)
{
  return pn->getRule() != PfRule::LEAN_RULE && pn->getRule() != PfRule::ASSUME;
};

bool LeanProofPostprocessCallback::addLeanStep(
    Node res,
    LeanRule rule,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> leanArgs = {
      NodeManager::currentNM()->mkConst<Rational>(static_cast<uint32_t>(rule)),
      res};
  leanArgs.insert(leanArgs.end(), args.begin(), args.end());
  return cdp.addStep(res, PfRule::LEAN_RULE, children, leanArgs);
}

bool LeanProofPostprocessCallback::update(Node res,
                                          PfRule id,
                                          const std::vector<Node>& children,
                                          const std::vector<Node>& args,
                                          CDProof* cdp,
                                          bool& continueUpdate)
{
  Trace("test-lean") << "Updating rule:\nres: " << res << "\nid: " << id
                     << "\nchildren: " << children << "\nargs: " << args
                     << "\n";
  NodeManager* nm = NodeManager::currentNM();
  switch (id)
  {
    case PfRule::IMPLIES_ELIM:
    {
      // if this implies elim is applied right after a scope, we short-circuit
      // it
      std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
      PfRule childRule = childPf->getRule();
      if (childRule == PfRule::SCOPE)
      {
        Assert(childPf->getChildren().size() == 1);
        // need to pass proof of children to cdp
        std::vector<Node> childrenOfChild;
        const std::vector<std::shared_ptr<ProofNode>>& childrenPfsOfChild =
            childPf->getChildren();
        for (const std::shared_ptr<ProofNode>& cpoc : childrenPfsOfChild)
        {
          childrenOfChild.push_back(cpoc->getResult());
          // store in the proof
          cdp->addProof(cpoc);
        }
        // update child proof but with this step's conclusion
        bool updateRes CVC5_UNUSED = update(res,
                                            childRule,
                                            childrenOfChild,
                                            childPf->getArguments(),
                                            cdp,
                                            continueUpdate);
        Assert(updateRes);
      }
      else
      {
        // regular case, just turn conclusion into clause
        addLeanStep(res,
                    LeanRule::IMPLIES_ELIM,
                    children,
                    {nm->mkNode(kind::SEXPR, res[0].notNode(), res[1])},
                    *cdp);
      }
      break;
    }
    case PfRule::SCOPE:
    {
      std::vector<Node> newRes;
      for (const Node& n : args)
      {
        newRes.push_back(n.notNode());
      }
      if (res.getKind() == kind::NOT)
      {
        newRes.push_back(nm->mkConst(false));
      }
      else
      {
        Assert(res.getKind() == kind::IMPLIES || res.getKind() == kind::OR);
        newRes.push_back(res[1]);
      }
      std::vector<Node> newArgs{nm->mkNode(kind::SEXPR, newRes)};
      newArgs.insert(newArgs.end(), args.begin(), args.end());
      return addLeanStep(res, LeanRule::SCOPE, children, newArgs, *cdp);
    }
    case PfRule::EQ_RESOLVE:
    {
      return addLeanStep(res, LeanRule::EQ_RESOLVE, children, args, *cdp);
    }
    case PfRule::CHAIN_RESOLUTION_SAT:
    {
      Node trueNode = nm->mkConst(true);
      Node falseNode = nm->mkConst(false);

      Node cur = children[0];
      // If a child F = (or F1 ... Fn) is the result of a ASSUME or
      // EQ_RESOLUTION we need to convert into a list (since these rules
      // introduce terms). The question then is how to convert it, i.e., whether
      // it's a singleton list or not
      std::shared_ptr<ProofNode> childPf = cdp->getProofFor(children[0]);
      Trace("test-lean") << "..child 0 has rule " << childPf->getRule() << "\n";
      if (childPf->getRule() == PfRule::ASSUME
          || childPf->getRule() == PfRule::EQ_RESOLVE)
      {
        Node conclusion;
        LeanRule childRule;
        // The first child is used as a OR non-singleton clause if it is not
        // equal to its pivot L_1. Since it's the first clause in the resolution
        // it can only be equal to the pivot in the case the polarity is true.
        if (children[0].getKind() == kind::OR
            && (args[0] != trueNode || children[0] != args[1]))
        {
          // Add clOr step
          std::vector<Node> lits{children[0].begin(), children[0].end()};
          conclusion = nm->mkNode(kind::SEXPR, lits);
          childRule = LeanRule::CL_OR;
        }
        else
        {
          // add clAssume step
          conclusion = nm->mkNode(kind::SEXPR, children[0]);
          childRule = LeanRule::CL_ASSUME;
        }
        Trace("test-lean") << "....updating to " << childRule << " : "
                          << conclusion << "\n";
        addLeanStep(conclusion, childRule, {children[0]}, {}, *cdp);
        cur = conclusion;
      }

      // add internal steps
      Node nextChild;

      // For all other children C_i the procedure is simliar. There is however a
      // key difference in the choice of the pivot element which is now the
      // L_{i-1}, i.e. the pivot of the child with the result of the i-1
      // resolution steps between the children before it. Therefore, if the
      // policy id_{i-1} is true, the pivot has to appear negated in the child
      // in which case it should not be a [(or F1 ... Fn)] node. The same is
      // true if it isn't the pivot element.
      for (size_t i = 1, size = children.size(); i < size; ++i)
      {
        // check whether need to listify premises
        nextChild = children[i];
        childPf = cdp->getProofFor(children[i]);
        if (childPf->getRule() == PfRule::ASSUME
            || childPf->getRule() == PfRule::EQ_RESOLVE)
        {
          LeanRule childRule;
          // The first child is used as a OR non-singleton clause if it is not
          // equal to its pivot L_1. Since it's the first clause in the
          // resolution it can only be equal to the pivot in the case the
          // polarity is true.
          if (children[i].getKind() == kind::OR
              && (args[2 * (i - 1)] != falseNode
                  || args[2 * (i - 1) + 1] != children[i]))
          {
            // Add clOr step
            std::vector<Node> lits{children[i].begin(), children[i].end()};
            nextChild = nm->mkNode(kind::SEXPR, lits);
            childRule = LeanRule::CL_OR;
          }
          else
          {
            // add clAssume step
            nextChild = nm->mkNode(kind::SEXPR, children[i]);
            childRule = LeanRule::CL_ASSUME;
          }
          addLeanStep(nextChild, childRule, {children[i]}, {}, *cdp);
        }
        if (i < size -1)
        {  // create a (unique) placeholder for the resulting binary
          // resolution. The placeholder is [res, pol, pivot], where pol and
          // pivot are relative to this part of the chain resolution
          std::vector<Node> curArgs{args[(i - 1) * 2], args[(i - 1) * 2 + 1]};
          Node newCur = nm->mkNode(kind::SEXPR, res, curArgs[0], curArgs[1]);
          addLeanStep(newCur,
                      curArgs[0].getConst<bool>() ? LeanRule::R0_PARTIAL
                                                  : LeanRule::R1_PARTIAL,
                      {cur, nextChild},
                      {curArgs[1]},
                      *cdp);
          cur = newCur;
        }
      }
      // now check whether conclusion is a sigleton
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
          bool posFirst = (i == 1) ? (args[0] == trueNode)
                                   : (args[(2 * (i - 1)) - 2] == trueNode);
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
              posFirst = args[(2 * i) - 2] == trueNode;
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
      std::vector<Node> curArgs{args[(i - 1) * 2], args[(i - 1) * 2 + 1]};
      if (!isSingletonClause)
      {
        std::vector<Node> resLits{res.begin(), res.end()};
        conclusion = nm->mkNode(kind::SEXPR, resLits);
      }
      // conclusion is empty list
      else if (res == falseNode)
      {
        conclusion = d_empty;
      }
      else
      {
        conclusion = nm->mkNode(kind::SEXPR, res);
      }
      Trace("test-lean") << "final step of res with children " << cur << ", "
                         << nextChild << " and args " << conclusion << ", "
                         << curArgs[1] << "\n";
      addLeanStep(res,
                  curArgs[0].getConst<bool>() ? LeanRule::R0 : LeanRule::R1,
                  {cur, nextChild},
                  {conclusion, curArgs[1]},
                  *cdp);
      break;
    }
    case PfRule::REORDERING:
    {
      // for each literal in the resulting clause, get its position in the premise
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
            pos.push_back(nm->mkConst<Rational>(i));
            break;
          }
        }
      }
      // turn conclusion into clause
      addLeanStep(
          res,
          LeanRule::REORDER,
          children,
          {nm->mkNode(kind::SEXPR, resLits), nm->mkNode(kind::SEXPR, pos)},
          *cdp);
      break;
    }
    case PfRule::AND_ELIM:
    {
      return addLeanStep(res, LeanRule::AND_ELIM, children, args, *cdp);
    }
    case PfRule::REFL:
    {
      return addLeanStep(res, LeanRule::REFL, {}, args, *cdp);
    }
    case PfRule::CONG:
    {
      // TODO support closures
      if (res[0].isClosure())
      {
        Unreachable() << "Lean printing without support for congruence over "
                         "closures for now\n";
      }
      Node eqNode = ProofRuleChecker::mkKindNode(kind::EQUAL);

      Node op = args.size() == 2 ? args[1] : args[0];
      // add internal refl step
      Node opEq = nm->mkNode(kind::SEXPR, eqNode, op, op);
      addLeanStep(opEq, LeanRule::REFL_PARTIAL, {}, {op}, *cdp);
      // add internal steps
      Node cur = opEq;
      for (size_t i = 0, size = children.size(); i < size - 1; ++i)
      {
        Node newCur = nm->mkNode(kind::SEXPR,
                                 eqNode,
                                 nm->mkNode(kind::SEXPR, cur, children[i][0]),
                                 nm->mkNode(kind::SEXPR, cur, children[i][1]));
        addLeanStep(
            newCur, LeanRule::CONG_PARTIAL, {cur, children[i]}, {}, *cdp);
      }
      addLeanStep(res, LeanRule::CONG, {cur, children.back()}, {}, *cdp);
      break;
    }
    case PfRule::TRANS:
    {
      // break chain
      Node cur = children[0];
      for (size_t i = 1, size = children.size(); i < size; ++i)
      {
        std::vector<Node> newChildren{cur, children[i]};
        std::vector<Node> newArgs{args[(i - 1) * 2], args[(i - 1) * 2 + 1]};
        cur = d_pc->checkDebug(
            PfRule::RESOLUTION, newChildren, newArgs, Node(), "");
        addLeanStep(cur,
                    newArgs[0].getConst<bool>() ? LeanRule::R1 : LeanRule::R0,
                    newChildren,
                    {newArgs[1]},
                    *cdp);
      }
      break;
    }
    case PfRule::SYMM:
    {
      return addLeanStep(
          res,
          res.getKind() == kind::EQUAL ? LeanRule::SYMM : LeanRule::NEG_SYMM,
          children,
          {},
          *cdp);
    }
    case PfRule::THEORY_REWRITE:
    {
      return addLeanStep(res, LeanRule::TH_TRUST_VALID, {}, {}, *cdp);
    }
    case PfRule::CNF_AND_POS:
    {
      std::vector<Node> resArgs{args[0].begin(), args[0].end()};
      return addLeanStep(res,
                         LeanRule::CNF_AND_POS,
                         {},
                         {nm->mkNode(kind::SEXPR, res[0], res[1]),
                          nm->mkNode(kind::SEXPR, resArgs),
                          args[1]},
                         *cdp);
    }
    default:
    {
      addLeanStep(res, LeanRule::UNKNOWN, children, args, *cdp);
    }
  };
  return true;
}

void LeanProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_pnm, *(d_cb.get()), false, false, false);
  updater.process(pf);
};

}  // namespace proof
}  // namespace cvc5
