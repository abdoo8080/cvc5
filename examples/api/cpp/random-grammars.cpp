#include <cvc5/cvc5.h>
#include <string.h>

#include <algorithm>
#include <iostream>
#include <random>

using namespace cvc5;

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

/** Mutates given production `rules`. */
std::pair<std::vector<Term>, std::vector<Term>> mutateRules(
    const Solver& slv,
    const std::vector<Term>& sygusVars,
    std::unordered_map<Term, std::vector<Term>>& pools,
    const std::vector<Term>& rules)
{
  std::bernoulli_distribution bernoulli;
  std::uniform_int_distribution<uint64_t> uniform;
  std::vector<Term> mutatedRules;
  std::vector<Term> newNonterminals;
  std::vector<Term> terminals;
  for (const Term& rule : rules)
  {
    // Process terminal rules later.
    if (getNonterminals(rule, sygusVars).empty())
    {
      terminals.push_back(rule);
    }
    else
    {
      // Flip a coin to decide whether or not we want to consider this rule.
      if (bernoulli(gen))
      {
        continue;
      }
      std::unordered_map<Term, Term> map;
      Term mutatedRule = clone(slv, sygusVars, rule, map);
      for (const Term& var : getNonterminals(mutatedRule, sygusVars))
      {
        Term nonterminal = map[var];
        uint64_t r = uniform(gen) % (pools[nonterminal].size() + 1);
        if (r == pools[nonterminal].size())
        {
          Term newNonterminal =
              slv.mkVar(nonterminal.getSort(),
                        nonterminal.getSymbol() + '_'
                            + std::to_string(pools[nonterminal].size()));
          pools[nonterminal].push_back(newNonterminal);
          newNonterminals.push_back(newNonterminal);
        }
        mutatedRule = mutatedRule.substitute(var, pools[nonterminal][r]);
      }
      mutatedRules.push_back(mutatedRule);
    }
  }
  // Add at least 1 terminal rule to ensure that the grammar is not ill-formed.
  uint64_t r = uniform(gen) % terminals.size();
  mutatedRules.insert(mutatedRules.cbegin(), terminals[r]);
  terminals.erase(terminals.cbegin() + r);
  while (bernoulli(gen) && !terminals.empty())
  {
    r = uniform(gen) % terminals.size();
    mutatedRules.insert(mutatedRules.cbegin(), terminals[r]);
    terminals.erase(terminals.cbegin() + r);
  }
  return {mutatedRules, newNonterminals};
}

Term findOriginalNonterminal(std::unordered_map<Term, std::vector<Term>> pools,
                             Term newNonterminal)
{
  for (const std::pair<const Term, std::vector<Term>>& pair : pools)
  {
    for (const Term& nonterminal : pair.second)
    {
      if (nonterminal == newNonterminal)
      {
        return pair.first;
      }
    }
  }
}

/** Generate a somewhat random grammar from the provided one. */
G randomize(const Solver& slv, const std::vector<Term>& sygusVars, G& g)
{
  std::unordered_map<Term, std::vector<Term>> pools;
  std::vector<Term> stack;
  for (const std::pair<const Term, std::vector<Term>>& production : g)
  {
    Term nonterminal = production.first;
    pools[nonterminal].push_back(nonterminal);
    stack.push_back(nonterminal);
  }
  G gp;
  while (!stack.empty())
  {
    Term currNonterminal = stack.back();
    stack.pop_back();
    std::vector<Term> mutatedRules, newNonteriminals;
    std::tie(mutatedRules, newNonteriminals) =
        mutateRules(slv,
                    sygusVars,
                    pools,
                    g[findOriginalNonterminal(pools, currNonterminal)]);
    gp[currNonterminal] = mutatedRules;
    stack.insert(
        stack.cend(), newNonteriminals.cbegin(), newNonteriminals.cend());
  }
  return gp;
}

std::tuple<std::vector<Term>, std::vector<Term>, G> update(
    const Solver& slv,
    std::vector<Term> vars,
    std::vector<Term> nonterminals,
    G& map)
{
  for (const auto& production : map)
  {
    if (std::find(nonterminals.cbegin(), nonterminals.cend(), production.first)
        == nonterminals.cend())
    {
      nonterminals.push_back(production.first);
    }
  }
  return {vars, nonterminals, map};
}

/** Converts a mapping from production to rules to a Sygus grammar. */
Grammar mapToGrammar(const Solver& slv,
                     std::vector<Term> vars,
                     std::vector<Term> nonterminals,
                     G map)
{
  std::tie(vars, nonterminals, map) = update(slv, vars, nonterminals, map);
  Grammar g = slv.mkGrammar(vars, nonterminals);
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

  G g;

  g[start] = {x,
              y,
              slv.mkBitVector(8, "00", 16),
              slv.mkBitVector(8, "01", 16),
              slv.mkBitVector(8, "a5", 16),
              slv.mkTerm(BITVECTOR_NOT, {start}),
              slv.mkTerm(BITVECTOR_NEG, {start}),
              slv.mkTerm(BITVECTOR_AND, {start, start}),
              slv.mkTerm(BITVECTOR_OR, {start, start}),
              slv.mkTerm(BITVECTOR_ADD, {start, start}),
              slv.mkTerm(BITVECTOR_MULT, {start, start}),
              slv.mkTerm(BITVECTOR_UDIV, {start, start}),
              slv.mkTerm(BITVECTOR_UREM, {start, start}),
              slv.mkTerm(BITVECTOR_SHL, {start, start}),
              slv.mkTerm(BITVECTOR_LSHR, {start, start})};

  g[startBool] = {slv.mkFalse(),
                  slv.mkTrue(),
                  slv.mkTerm(NOT, {startBool}),
                  slv.mkTerm(AND, {startBool, startBool}),
                  slv.mkTerm(OR, {startBool, startBool}),
                  slv.mkTerm(BITVECTOR_ULT, {start, start})};

  return {{x, y}, {start, startBool}, g};
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

  G g;

  g[start] = {x,
              y,
              slv.mkInteger(0),
              slv.mkInteger(1),
              slv.mkInteger(2),
              slv.mkInteger(3),
              slv.mkInteger(4),
              slv.mkInteger(5),
              slv.mkTerm(NEG, {start}),
              slv.mkTerm(SUB, {start, start}),
              slv.mkTerm(ADD, {start, start}),
              slv.mkTerm(MULT, {start, start}),
              slv.mkTerm(INTS_DIVISION, {start, start}),
              slv.mkTerm(INTS_MODULUS, {start, start}),
              // slv.mkTerm(ABS, {start}),
              slv.mkTerm(ITE, {startBool, start, start})};

  g[startBool] = {slv.mkFalse(),
                  slv.mkTrue(),
                  slv.mkTerm(NOT, {startBool}),
                  slv.mkTerm(AND, {startBool, startBool}),
                  slv.mkTerm(OR, {startBool, startBool}),
                  slv.mkTerm(LT, {start, start}),
                  slv.mkTerm(LEQ, {start, start}),
                  slv.mkTerm(EQUAL, {start, start}),
                  slv.mkTerm(GEQ, {start, start}),
                  slv.mkTerm(GT, {start, start})};

  return {{x, y}, {start, startBool}, g};
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

  G g;

  g[start] = {x,
              y,
              slv.mkString(""),
              slv.mkString("0"),
              slv.mkString("1"),
              slv.mkString("a"),
              slv.mkString("b"),
              slv.mkTerm(STRING_CONCAT, {start, start}),
              slv.mkTerm(STRING_CHARAT, {start, startInt}),
              slv.mkTerm(STRING_SUBSTR, {start, startInt, startInt}),
              slv.mkTerm(STRING_REPLACE, {start, start, start}),
              // slv.mkTerm(STRING_REPLACE_ALL, {start, start, start}),
              // slv.mkTerm(STRING_FROM_CODE, {startInt}),
              slv.mkTerm(STRING_FROM_INT, {startInt}),
              slv.mkTerm(ITE, {startBool, start, start})};

  g[startInt] = {slv.mkInteger(0),
                 slv.mkInteger(1),
                 slv.mkTerm(STRING_LENGTH, {start}),
                 slv.mkTerm(STRING_INDEXOF, {start, start, startInt}),
                //  slv.mkTerm(STRING_TO_CODE, {start}),
                 slv.mkTerm(STRING_TO_INT, {start})};

  g[startBool] = {slv.mkFalse(),
                  slv.mkTrue(),
                  slv.mkTerm(NOT, {startBool}),
                  slv.mkTerm(AND, {startBool, startBool}),
                  // slv.mkTerm(STRING_LT, {start, start}),
                  // slv.mkTerm(STRING_LEQ, {start, start}),
                  slv.mkTerm(STRING_PREFIX, {start, start}),
                  slv.mkTerm(STRING_SUFFIX, {start, start}),
                  slv.mkTerm(STRING_CONTAINS, {start, start}),
                  // slv.mkTerm(STRING_IS_DIGIT, {start}),
                  slv.mkTerm(EQUAL, {start, start}),
                  slv.mkTerm(EQUAL, {startInt, startInt}),
                  slv.mkTerm(LEQ, {startInt, startInt})};

  return {{x, y}, {start, startInt, startBool}, g};
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
    G ng = randomize(slv, sygusVars, g);
    std::cout << "(set-logic BV)" << std::endl
              << std::endl
              << "(synth-fun f ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)"
              << std::endl
              << mapToGrammar(slv, sygusVars, nonterminals, ng) << ')'
              << std::endl
              << std::endl
              << "(declare-var x (_ BitVec 8))" << std::endl
              << "(declare-var y (_ BitVec 8))" << std::endl
              << std::endl;
  }
  else if (strcmp(argv[1], "nia") == 0)
  {
    std::tie(sygusVars, nonterminals, g) = niaGrammar(slv);
    G ng = randomize(slv, sygusVars, g);
    std::cout << "(set-logic NIA)" << std::endl
              << std::endl
              << "(synth-fun f ((x Int) (y Int)) Int" << std::endl
              << mapToGrammar(slv, sygusVars, nonterminals, ng) << ')'
              << std::endl
              << std::endl
              << "(declare-var x Int)" << std::endl
              << "(declare-var y Int)" << std::endl
              << std::endl;
  }
  else if (strcmp(argv[1], "string") == 0)
  {
    std::tie(sygusVars, nonterminals, g) = stringGrammar(slv);
    G ng = randomize(slv, sygusVars, g);
    std::cout << "(set-logic SLIA)" << std::endl
              << std::endl
              << "(synth-fun f ((x String) (y String)) String" << std::endl
              << mapToGrammar(slv, sygusVars, nonterminals, ng) << ')'
              << std::endl
              << std::endl
              << "(declare-var x String)" << std::endl
              << "(declare-var y String)" << std::endl
              << std::endl;
  }
  else
  {
    std::cerr << "Unknown option!\nUsage: " << argv[0] << " [bv|nia|string]"
              << std::endl;
    return 2;
  }

  return 0;
}
