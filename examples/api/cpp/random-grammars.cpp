#include <cvc5/cvc5.h>

#include <iostream>
#include <random>

#include "utils.h"

using namespace cvc5::api;

using G = std::unordered_map<Term, std::vector<Term>>;

std::random_device rd;
std::mt19937_64 gen(rd());

/** Substitute first occurrence of term `x` in `t` with `y`. */
Term substFirst(const Solver& slv, Term t, Term x, Term y)
{
  if (t == x)
  {
    return y;
  }
  if (!t.hasOp())
  {
    return t;
  }
  Op op = t.getOp();
  std::vector<Term> children;
  size_t i = 0;
  for (size_t n = t.getNumChildren(); i < n; ++i)
  {
    children.push_back(substFirst(slv, t[i], x, y));
    if (children[i] != t[i])
    {
      ++i;
      break;
    }
  }
  for (size_t n = t.getNumChildren(); i < n; ++i)
  {
    children.push_back(t[i]);
  }
  return slv.mkTerm(op, children);
}

/** Get all bound and free variables in an expression. */
std::vector<Term> getVars(Term t)
{
  if (t.getKind() == VARIABLE)
  {
    return {t};
  }
  std::vector<Term> vars;
  for (Term ct : t)
  {
    std::vector<Term> cVars = getVars(ct);
    vars.insert(vars.cend(), cVars.cbegin(), cVars.cend());
  }
  return vars;
}

/** Get all bound and free variables in an expression excluding ones
 * `sygusVars`. */
std::vector<Term> getNonterminals(Term t, const std::vector<Term>& sygusVars)
{
  std::unordered_set<Term> sygusVarsSet;
  for (Term var : sygusVars)
  {
    sygusVarsSet.emplace(var);
  }
  std::vector<Term> nonterminals;
  for (Term var : getVars(t))
  {
    if (sygusVarsSet.find(var) == sygusVarsSet.cend())
    {
      nonterminals.push_back(var);
    }
  }
  return nonterminals;
}

/** Returns a copy of `t` replacing all variables in `t` with fresh ones.
 * Stores a mapping from the fresh variables to the original ones in `map`. */
Term clone(const Solver& slv,
           const std::vector<Term>& sygusVars,
           Term t,
           std::unordered_map<Term, Term>& map)
{
  std::vector<Term> vars = getNonterminals(t, sygusVars);
  for (Term var : vars)
  {
    Term newVar = slv.mkVar(var.getSort());
    t = substFirst(slv, t, var, newVar);
    map.emplace(newVar, var);
  }
  return t;
}

/** Returns zero or more mutations of the provided `rule`. */
std::vector<Term> mutate(const Solver& slv,
                         const std::vector<Term>& sygusVars,
                         G& g,
                         Term rule)
{
  std::bernoulli_distribution bernoulli;
  std::uniform_int_distribution<> uniform(0, 100);
  std::unordered_map<Term, Term> map;
  std::vector<Term> rules;
  // This loop decides how many mutated versions of `rule` we should return.
  while (bernoulli(gen))
  {
    Term newRule = clone(slv, sygusVars, rule, map);
    // This one decides how many mutations we should make to each version.
    while (bernoulli(gen) && !getNonterminals(newRule, sygusVars).empty())
    {
      std::vector<Term> vars = getNonterminals(newRule, sygusVars);
      Term var = vars[uniform(gen) % vars.size()];
      newRule = newRule.substitute(
          var,
          clone(slv,
                sygusVars,
                g[map[var]][uniform(gen) % g[map[var]].size()],
                map));
    }
    std::vector<Term> vars = getNonterminals(newRule, sygusVars);
    // We're done with mutations. Replace all the newly created variables with
    // the original ones.
    for (Term var : vars)
    {
      newRule = newRule.substitute(var, map[var]);
    }
    rules.push_back(newRule);
  }
  return rules;
}

/** Generate a somewhat random grammar from the provided one. */
G randomize(const Solver& slv, const std::vector<Term>& sygusVars, G& g)
{
  G gp;
  for (const std::pair<const Term, std::vector<Term>>& production : g)
  {
    Term nonterminal = production.first;
    const std::vector<Term>& rules = production.second;
    for (Term rule : rules)
    {
      // If this is a terminal rule, keep it. Otherwise, grammar may be
      // ill-formed.
      if (getNonterminals(rule, sygusVars).empty())
      {
        gp[nonterminal].push_back(rule);
      }
      else
      {
        std::vector<Term> newRules = mutate(slv, sygusVars, g, rule);
        // std::cout << newRules << std::endl;
        gp[nonterminal].insert(
            gp[nonterminal].cend(), newRules.cbegin(), newRules.cend());
      }
    }
  }
  return gp;
}

/** Converts a mapping from production to rules to a Sygus grammar. */
Grammar mapToGrammar(const Solver& slv, std::vector<Term> vars, G& map)
{
  std::vector<Term> nonterminals;
  for (const std::pair<const Term, std::vector<Term>>& production : map)
  {
    nonterminals.push_back(production.first);
  }
  Grammar g = slv.mkSygusGrammar(vars, nonterminals);
  for (Term nonterminal : nonterminals)
  {
    g.addRules(nonterminal, map[nonterminal]);
  }
  return g;
}

int main()
{
  Solver slv;

  Sort boolean = slv.getBooleanSort();
  Sort integer = slv.getIntegerSort();
  Sort string = slv.getStringSort();

  Term x = slv.mkVar(string, "x");
  Term y = slv.mkVar(string, "y");

  Term start = slv.mkVar(string, "Start");
  Term startInt = slv.mkVar(integer, "StartInt");
  Term startBool = slv.mkVar(boolean, "StartBool");
  Term constString = slv.mkVar(string, "ConstString");

  Term strAppend = slv.mkTerm(STRING_CONCAT, start, start);
  Term strAt = slv.mkTerm(STRING_CHARAT, start, startInt);
  Term strSubstr = slv.mkTerm(STRING_SUBSTR, start, startInt, startInt);
  Term strReplace = slv.mkTerm(STRING_REPLACE, start, start, start);
  Term strReplaceAll = slv.mkTerm(STRING_REPLACE_ALL, start, start, start);
  Term strFromCode = slv.mkTerm(STRING_FROM_CODE, startInt);
  Term strFromInt = slv.mkTerm(STRING_FROM_INT, startInt);
  Term ite = slv.mkTerm(ITE, startBool, start, start);

  Term zero = slv.mkInteger(0);
  Term one = slv.mkInteger(1);
  Term strIndexof = slv.mkTerm(STRING_INDEXOF, start, start, startInt);
  Term strToCode = slv.mkTerm(STRING_TO_CODE, start);
  Term strToInt = slv.mkTerm(STRING_TO_INT, start);

  Term Not = slv.mkTerm(NOT, startBool);
  Term And = slv.mkTerm(AND, startBool, startBool);
  Term strLt = slv.mkTerm(STRING_LT, start, start);
  Term strLeq = slv.mkTerm(STRING_LEQ, start, start);
  Term strPrefixof = slv.mkTerm(STRING_PREFIX, start, start);
  Term strSuffixof = slv.mkTerm(STRING_SUFFIX, start, start);
  Term strContains = slv.mkTerm(STRING_CONTAINS, start, start);
  Term strIsDigit = slv.mkTerm(STRING_IS_DIGIT, start);
  Term strEqual = slv.mkTerm(EQUAL, start, start);
  Term intEqual = slv.mkTerm(EQUAL, startInt, startInt);
  Term intLeq = slv.mkTerm(LEQ, startInt, startInt);

  Term empty = slv.mkString("");
  Term zeroStr = slv.mkString("0");
  Term oneStr = slv.mkString("1");
  Term a = slv.mkString("a");
  Term b = slv.mkString("b");

  G g;

  g[start] = {constString,
              x,
              y,
              strAppend,
              strAt,
              strSubstr,
              strReplace,
              strReplaceAll,
              strFromCode,
              strFromInt,
              ite};

  g[startInt] = {zero, one, strIndexof, strToCode, strToInt};

  g[startBool] = {Not,
                  And,
                  strLt,
                  strLeq,
                  strPrefixof,
                  strSuffixof,
                  strContains,
                  strIsDigit,
                  strEqual,
                  intEqual,
                  intLeq};

  g[constString] = {empty, zeroStr, oneStr, a, b};

  G ng = randomize(slv, {x, y}, g);
  std::cout << mapToGrammar(slv, {x, y}, ng) << std::endl;

  return 0;
}
