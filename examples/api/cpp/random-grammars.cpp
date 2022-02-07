#include <cvc5/cvc5.h>
#include <string.h>

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

std::tuple<std::vector<Term>, std::vector<Term>, G> bvGrammar(const Solver& slv)
{
  Sort boolean = slv.getBooleanSort();
  Sort bitVec8 = slv.mkBitVectorSort(8);

  Term x = slv.mkVar(bitVec8, "x");
  Term y = slv.mkVar(bitVec8, "y");

  Term start = slv.mkVar(bitVec8, "Start");
  Term startBool = slv.mkVar(boolean, "StartBool");
  Term constBV = slv.mkVar(bitVec8, "ConstBV");

  G g;

  g[start] = {constBV,
              x,
              y,
              slv.mkTerm(BITVECTOR_NOT, start),
              slv.mkTerm(BITVECTOR_NEG, start),
              slv.mkTerm(BITVECTOR_AND, start, start),
              slv.mkTerm(BITVECTOR_OR, start, start),
              slv.mkTerm(BITVECTOR_ADD, start, start),
              slv.mkTerm(BITVECTOR_MULT, start, start),
              slv.mkTerm(BITVECTOR_UDIV, start, start),
              slv.mkTerm(BITVECTOR_UREM, start, start),
              slv.mkTerm(BITVECTOR_SHL, start, start),
              slv.mkTerm(BITVECTOR_LSHR, start, start)};

  g[startBool] = {slv.mkTerm(NOT, startBool),
                  slv.mkTerm(AND, startBool, startBool),
                  slv.mkTerm(BITVECTOR_ULT, start, start)};

  g[constBV] = {slv.mkBitVector(8, "00", 16),
                slv.mkBitVector(8, "01", 16),
                slv.mkBitVector(8, "a5", 16)};

  return {{x, y}, {start, startBool, constBV}, g};
}

std::tuple<std::vector<Term>, std::vector<Term>, G> niaGrammar(
    const Solver& slv)
{
  Sort boolean = slv.getBooleanSort();
  Sort integer = slv.getIntegerSort();

  Term x = slv.mkVar(integer, "x");
  Term y = slv.mkVar(integer, "y");

  Term start = slv.mkVar(integer, "Start");
  Term startBool = slv.mkVar(boolean, "StartBool");
  Term constInt = slv.mkVar(integer, "ConstInt");

  G g;

  g[start] = {constInt,
              x,
              y,
              slv.mkTerm(UMINUS, start),
              slv.mkTerm(MINUS, start, start),
              slv.mkTerm(PLUS, start, start),
              slv.mkTerm(MULT, start, start),
              slv.mkTerm(INTS_DIVISION, start, start),
              slv.mkTerm(INTS_MODULUS, start, start),
              slv.mkTerm(ABS, start),
              slv.mkTerm(ITE, startBool, start, start)};

  g[startBool] = {slv.mkFalse(),
                  slv.mkTrue(),
                  slv.mkTerm(NOT, startBool),
                  slv.mkTerm(AND, startBool, startBool),
                  slv.mkTerm(LEQ, start, start),
                  slv.mkTerm(EQUAL, start, start),
                  slv.mkTerm(GEQ, start, start),
                  slv.mkTerm(GT, start, start)};

  g[constInt] = {slv.mkInteger(0),
                 slv.mkInteger(1),
                 slv.mkInteger(2),
                 slv.mkInteger(3),
                 slv.mkInteger(4),
                 slv.mkInteger(5)};

  return {{x, y}, {start, startBool, constInt}, g};
}

std::tuple<std::vector<Term>, std::vector<Term>, G> stringGrammar(
    const Solver& slv)
{
  Sort boolean = slv.getBooleanSort();
  Sort integer = slv.getIntegerSort();
  Sort string = slv.getStringSort();

  Term x = slv.mkVar(string, "x");
  Term y = slv.mkVar(string, "y");

  Term start = slv.mkVar(string, "Start");
  Term startInt = slv.mkVar(integer, "StartInt");
  Term startBool = slv.mkVar(boolean, "StartBool");
  Term constString = slv.mkVar(string, "ConstString");

  G g;

  g[start] = {constString,
              x,
              y,
              slv.mkTerm(STRING_CONCAT, start, start),
              slv.mkTerm(STRING_CHARAT, start, startInt),
              slv.mkTerm(STRING_SUBSTR, start, startInt, startInt),
              slv.mkTerm(STRING_REPLACE, start, start, start),
              slv.mkTerm(STRING_REPLACE_ALL, start, start, start),
              slv.mkTerm(STRING_FROM_CODE, startInt),
              slv.mkTerm(STRING_FROM_INT, startInt),
              slv.mkTerm(ITE, startBool, start, start)};

  g[startInt] = {slv.mkInteger(0),
                 slv.mkInteger(1),
                 slv.mkTerm(STRING_INDEXOF, start, start, startInt),
                 slv.mkTerm(STRING_TO_CODE, start),
                 slv.mkTerm(STRING_TO_INT, start)};

  g[startBool] = {slv.mkTerm(NOT, startBool),
                  slv.mkTerm(AND, startBool, startBool),
                  slv.mkTerm(STRING_LT, start, start),
                  slv.mkTerm(STRING_LEQ, start, start),
                  slv.mkTerm(STRING_PREFIX, start, start),
                  slv.mkTerm(STRING_SUFFIX, start, start),
                  slv.mkTerm(STRING_CONTAINS, start, start),
                  slv.mkTerm(STRING_IS_DIGIT, start),
                  slv.mkTerm(EQUAL, start, start),
                  slv.mkTerm(EQUAL, startInt, startInt),
                  slv.mkTerm(LEQ, startInt, startInt)};

  g[constString] = {slv.mkString(""),
                    slv.mkString("0"),
                    slv.mkString("1"),
                    slv.mkString("a"),
                    slv.mkString("b")};

  return {{x, y}, {start, startInt, startBool, constString}, g};
}

int main(int argc, char* argv[])
{
  if (argc != 2)
  {
    std::cerr << "Wrong number of arguments!\nUsage: " << argv[0]
              << " [bv|nia|string]" << std::endl;
    return 1;
  }

  Solver slv;
  std::vector<Term> sygusVars, nonterminals;
  G g;

  std::string x = "s";

  if (strcmp(argv[1], "bv") == 0)
  {
    std::tie(sygusVars, nonterminals, g) = bvGrammar(slv);
  }
  else if (strcmp(argv[1], "nia") == 0)
  {
    std::tie(sygusVars, nonterminals, g) = niaGrammar(slv);
  }
  else if (strcmp(argv[1], "string") == 0)
  {
    std::tie(sygusVars, nonterminals, g) = stringGrammar(slv);
  }
  else
  {
    std::cerr << "Unknown option!\nUsage: " << argv[0] << " [bv|nia|string]"
              << std::endl;
    return 2;
  }

  G ng = randomize(slv, sygusVars, g);
  std::cout << mapToGrammar(slv, sygusVars, ng) << std::endl;

  return 0;
}
