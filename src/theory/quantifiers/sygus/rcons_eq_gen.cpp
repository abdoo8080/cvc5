/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Reconstruct Equivalence Generator class implementation.
 */

#include "theory/quantifiers/sygus/rcons_eq_gen.h"

#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

void RConsEqGen::getEquivalentTerms(Kind k, Node n, std::vector<Node>& equiv)
{
  NodeManager* nm = NodeManager::currentNM();

  if (k == NOT && n.getKind() == OR)
  {
    Node l = n[0].notNode();
    Node r = n[1].notNode();
    equiv.push_back(l.andNode(r).notNode());
  }

  if (k == AND && n.getKind() == EQUAL)
  {
    Node l = n[0].orNode(n[1].notNode());
    Node r = n[0].notNode().orNode(n[1]);
    equiv.push_back(l.andNode(r));
  }

  if (k == OR && n.getKind() == EQUAL)
  {
    Node l = n[0].andNode(n[1]);
    Node r = n[0].orNode(n[1]).notNode();
    equiv.push_back(l.orNode(r));
  }

  if (k == AND || k == OR)
  {
    equiv.push_back(nm->mkNode(k, n, n));
    equiv.push_back(nm->mkNode(k, n, nm->mkConst(k == AND)));
  }
  // multiplication for integers
  // TODO for bitvectors
  Kind mk = (k == PLUS || k == MINUS) ? MULT : UNDEFINED_KIND;
  if (mk != UNDEFINED_KIND)
  {
    if (n.getKind() == mk && n[0].isConst() && n[0].getType().isInteger())
    {
      bool success = true;
      for (unsigned i = 0; i < 2; i++)
      {
        Node eq;
        if (k == PLUS || k == MINUS)
        {
          Node oth = nm->mkConst(Rational(i == 0 ? 1000 : -1000));
          eq = i == 0 ? nm->mkNode(LEQ, n[0], oth) : nm->mkNode(GEQ, n[0], oth);
        }
        if (!eq.isNull())
        {
          eq = Rewriter::rewrite(eq);
          if (!eq.isConst() || !eq.getConst<bool>())
          {
            success = false;
            break;
          }
        }
      }
      if (success)
      {
        Node var = n[1];
        Node rem;
        if (k == PLUS || k == MINUS)
        {
          int rem_coeff =
              (int)n[0].getConst<Rational>().getNumerator().getSignedInt();
          if (rem_coeff > 0 && k == PLUS)
          {
            rem_coeff--;
          }
          else if (rem_coeff < 0 && k == MINUS)
          {
            rem_coeff++;
          }
          else
          {
            success = false;
          }
          if (success)
          {
            rem = nm->mkNode(MULT, nm->mkConst(Rational(rem_coeff)), var);
            rem = Rewriter::rewrite(rem);
          }
        }
        if (!rem.isNull())
        {
          equiv.push_back(nm->mkNode(k, rem, var));
        }
      }
    }
  }
  // negative constants
  if (k == MINUS)
  {
    if (n.isConst() && n.getType().isInteger()
        && n.getConst<Rational>().getNumerator().strictlyNegative())
    {
      Node nn = nm->mkNode(UMINUS, n);
      nn = Rewriter::rewrite(nn);
      equiv.push_back(nm->mkNode(MINUS, nm->mkConst(Rational(0)), nn));
    }
  }
  // inequalities
  if (k == GEQ || k == LEQ || k == LT || k == GT || k == NOT)
  {
    Node atom = n.getKind() == NOT ? n[0] : n;
    bool pol = n.getKind() != NOT;
    Kind ak = atom.getKind();
    if ((ak == GEQ || ak == LEQ || ak == LT || ak == GT) && (pol || k != NOT))
    {
      Node t1 = atom[0];
      Node t2 = atom[1];
      if (!pol)
      {
        ak = ak == GEQ ? LT : (ak == LEQ ? GT : (ak == LT ? GEQ : LEQ));
      }
      if (k == NOT)
      {
        equiv.push_back(
            nm->mkNode(
                  ak == GEQ ? LT : (ak == LEQ ? GT : (ak == LT ? GEQ : LEQ)),
                  t1,
                  t2)
                .negate());
      }
      else if (k == ak)
      {
        equiv.push_back(nm->mkNode(k, t1, t2));
      }
      else if ((k == GEQ || k == LEQ) == (ak == GEQ || ak == LEQ))
      {
        equiv.push_back(nm->mkNode(k, t2, t1));
      }
      else if (t1.getType().isInteger() && t2.getType().isInteger())
      {
        if ((k == GEQ || k == GT) != (ak == GEQ || ak == GT))
        {
          Node ts = t1;
          t1 = t2;
          t2 = ts;
          ak = ak == GEQ ? LEQ : (ak == LEQ ? GEQ : (ak == LT ? GT : LT));
        }
        t2 = nm->mkNode(
            PLUS, t2, nm->mkConst(Rational((ak == GT || ak == LEQ) ? 1 : -1)));
        t2 = Rewriter::rewrite(t2);
        equiv.push_back(nm->mkNode(k, t1, t2));
      }
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
