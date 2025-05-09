/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple, commonly-used routines for Boolean simplification.
 */

#include "cvc5_private.h"

#ifndef CVC5__BOOLEAN_SIMPLIFICATION_H
#define CVC5__BOOLEAN_SIMPLIFICATION_H

#include <algorithm>
#include <vector>

#include "base/check.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace preprocessing {

/**
 * A class to contain a number of useful functions for simple
 * simplification of nodes.  One never uses it as an object (and
 * it cannot be constructed).  It is used as a namespace.
 */
class BooleanSimplification
{
  // cannot construct one of these
  BooleanSimplification() = delete;
  BooleanSimplification(const BooleanSimplification&) = delete;

  CVC5_WARN_UNUSED_RESULT static bool push_back_associative_commute_recursive(
      Node n, std::vector<Node>& buffer, Kind k, Kind notK, bool negateNode);

 public:
  /**
   * The threshold for removing duplicates.  (See removeDuplicates().)
   */
  static const uint32_t DUPLICATE_REMOVAL_THRESHOLD = 10;

  /**
   * Remove duplicate nodes from a vector, modifying it in-place.
   * If the vector has size >= DUPLICATE_REMOVAL_THRESHOLD, this
   * function is a no-op.
   */
  static void removeDuplicates(std::vector<Node>& buffer)
  {
    if (buffer.size() < DUPLICATE_REMOVAL_THRESHOLD)
    {
      std::sort(buffer.begin(), buffer.end());
      std::vector<Node>::iterator new_end =
          std::unique(buffer.begin(), buffer.end());
      buffer.erase(new_end, buffer.end());
    }
  }

  /**
   * Takes a node with kind AND, collapses all AND and (NOT OR)-kinded
   * children of it (as far as possible---see
   * push_back_associative_commute()), removes duplicates, and returns
   * the resulting Node.
   */
  static Node simplifyConflict(Node andNode)
  {
    AssertArgument(!andNode.isNull(), andNode);
    AssertArgument(andNode.getKind() == Kind::AND, andNode);

    std::vector<Node> buffer;
    push_back_associative_commute(andNode, buffer, Kind::AND, Kind::OR);

    removeDuplicates(buffer);

    if (buffer.size() == 1)
    {
      return buffer[0];
    }

    NodeBuilder nb(andNode.getNodeManager(), Kind::AND);
    nb.append(buffer);
    return nb;
  }

  /**
   * Takes a node with kind OR, collapses all OR and (NOT AND)-kinded
   * children of it (as far as possible---see
   * push_back_associative_commute()), removes duplicates, and returns
   * the resulting Node.
   */
  static Node simplifyClause(Node orNode)
  {
    AssertArgument(!orNode.isNull(), orNode);
    AssertArgument(orNode.getKind() == Kind::OR, orNode);

    std::vector<Node> buffer;
    push_back_associative_commute(orNode, buffer, Kind::OR, Kind::AND);

    removeDuplicates(buffer);

    Assert(buffer.size() > 0);
    if (buffer.size() == 1)
    {
      return buffer[0];
    }

    NodeBuilder nb(orNode.getNodeManager(), Kind::OR);
    nb.append(buffer);
    return nb;
  }

  /**
   * Takes a node with kind IMPLIES, converts it to an OR, then
   * simplifies the result with simplifyClause().
   *
   * The input doesn't actually have to be Horn, it seems, but that's
   * the common case(?), hence the name.
   */
  static Node simplifyHornClause(Node implication)
  {
    AssertArgument(implication.getKind() == Kind::IMPLIES, implication);

    TNode left = implication[0];
    TNode right = implication[1];

    Node notLeft = negate(left);
    Node clause = NodeBuilder(implication.getNodeManager(), Kind::OR)
                  << notLeft << right;

    return simplifyClause(clause);
  }

  /**
   * Aids in reforming a node.  Takes a node of (N-ary) kind k and
   * copies its children into an output vector, collapsing its k-kinded
   * children into it.  Also collapses negations of notK.  For example:
   *
   *   push_back_associative_commute( [OR [OR a b] [OR b c d] [NOT [AND e f]]],
   *                                  buffer, Kind::OR, Kind::AND )
   *   yields a "buffer" vector of [a b b c d e f]
   *
   * @param n the node to operate upon
   * @param buffer the output vector (must be empty on entry)
   * @param k the kind to collapse (should equal the kind of node n)
   * @param notK the "negation" of kind k (e.g. OR's negation is AND),
   * or Kind::UNDEFINED_KIND if none.
   * @param negateChildren true if the children of the resulting node
   * (that is, the elements in buffer) should all be negated; you want
   * this if e.g. you're simplifying the (OR...) in (NOT (OR...)),
   * intending to make the result an AND.
   */
  static inline void push_back_associative_commute(Node n,
                                                   std::vector<Node>& buffer,
                                                   Kind k,
                                                   Kind notK,
                                                   bool negateChildren = false)
  {
    AssertArgument(buffer.empty(), buffer);
    AssertArgument(!n.isNull(), n);
    AssertArgument(k != Kind::UNDEFINED_KIND && k != Kind::NULL_EXPR, k);
    AssertArgument(notK != Kind::NULL_EXPR, notK);
    AssertArgument(n.getKind() == k,
                   n,
                   "expected node to have kind %s",
                   kindToString(k).c_str());

    bool b CVC5_UNUSED =
        push_back_associative_commute_recursive(n, buffer, k, notK, false);

    if (buffer.size() == 0)
    {
      // all the TRUEs for an AND (resp FALSEs for an OR) were simplified away
      buffer.push_back(
          n.getNodeManager()->mkConst(k == Kind::AND ? true : false));
    }
  } /* push_back_associative_commute() */

  /**
   * Negates a node, doing all the double-negation elimination
   * that's possible.
   *
   * @param n the node to negate (cannot be the null node)
   */
  static Node negate(TNode n)
  {
    AssertArgument(!n.isNull(), n);

    bool polarity = true;
    TNode base = n;
    while (base.getKind() == Kind::NOT)
    {
      base = base[0];
      polarity = !polarity;
    }
    if (n.isConst())
    {
      return n.getNodeManager()->mkConst(!n.getConst<bool>());
    }
    if (polarity)
    {
      return base.notNode();
    }
    else
    {
      return base;
    }
  }

  /**
   * Simplify an OR, AND, or IMPLIES.  This function is the identity
   * for all other kinds.
   */
  inline static Node simplify(TNode n)
  {
    switch (n.getKind())
    {
      case Kind::AND: return simplifyConflict(n);

      case Kind::OR: return simplifyClause(n);

      case Kind::IMPLIES: return simplifyHornClause(n);

      default: return n;
    }
  }

}; /* class BooleanSimplification */

}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__BOOLEAN_SIMPLIFICATION_H */
