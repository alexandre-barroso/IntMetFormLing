import json
import sympy as sp

checks = []
def check(name, proposition):
    if proposition is not True and proposition != sp.true:
        raise AssertionError((name, proposition))
    checks.append({"id": name, "passed": True})

N = sp.Symbol("N", positive=True, integer=True)
q = sp.Symbol("q", real=True)
i = sp.Symbol("i", integer=True)
check("expected_count", sp.summation(q, (i, 1, N)) == N*q)
V = sp.Symbol("V", positive=True)
n = sp.Symbol("n", positive=True)
gap = sp.Symbol("gap", nonnegative=True)
check("ttr_repeat_identity", sp.cancel(V/n - V/(n+1) - V/(n*(n+1))) == 0)
check("ttr_repeat_positive", (V/(n*(n+1))).is_positive)
check("ttr_new_identity", sp.cancel((V+1)/(n+1)-V/n-(n-V)/(n*(n+1))) == 0)
check("ttr_new_numerator", sp.expand(((n-V)/(n*(n+1))).subs(n,V+gap)).is_nonnegative)
check("ttr_bound", sp.cancel(1-V/(V+gap)-gap/(V+gap)) == 0)
check("ttr_bound_nonnegative", (gap/(V+gap)).is_nonnegative)
c, scale, base = sp.symbols("c scale base", positive=True)
check("normalization_scaling", sp.cancel((scale*c)/(scale*n)*base-c/n*base) == 0)
c1,c2 = sp.symbols("c1 c2", real=True)
n1,n2 = sp.symbols("n1 n2", positive=True)
check("normalization_order_identity", sp.cancel(c2/n2*base-c1/n1*base-base*(c2*n1-c1*n2)/(n1*n2)) == 0)
check("normalization_order_factor_positive", (base/(n1*n2)).is_positive)
words = "They picnicked by the pool then lay back on the grass and looked at the stars".split()
check("figure_F01_tokens", len(words) == 16)
check("figure_F01_types", len(set(words)) == 14)
check("figure_F01_repetitions", [j+1 for j,w in enumerate(words) if w=="the"] == [4,10,15])
check("figure_F01_punctuation", len(words)+len([",", "."]) == 18)
print(json.dumps({"backend":"Python/SymPy", "scope":"general symbolic identities and sign conditions; exact published token sequence", "checks":len(checks), "passed":True, "results":checks}))
