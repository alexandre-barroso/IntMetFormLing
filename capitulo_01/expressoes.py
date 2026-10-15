import json
import sympy as sp

results = []

def check(identifier, condition):
    results.append({"id": identifier, "passed": bool(condition)})

Q = sp.Rational
N = Q(4112943)
q = 195/N
E = 660*q
R = 29/E
check("association_bindings", (N, q, E, R) == (4112943, Q(195,4112943), Q(128700,4112943), Q(119275347,128700)))
check("association_bounds", Q(3,100) < E < Q(4,100) and 926 < R < 927)
check("segmentation_bindings", (len(["I'm"]), len(["I", "am"]), len(["I", "am"])-len(["I'm"])) == (1,2,1))
second, millisecond = Q(1), Q(1,1000)
check("units_and_percent", Q(8,100)*second == 80*millisecond and Q(24,100)*second == 240*millisecond and Q(14-3,100)*second == 110*millisecond and Q(16,100)*second == 160*millisecond and Q(14,16) == Q(875,10)/100)
concordance = [23,27,5,10]
check("concordance_sum", sum(concordance) == 65 and sum(Q(x,65) for x in concordance) == 1)
x = sp.symbols("x1:5", real=True)
check("four_term_sum", sum(x) == x[0]+x[1]+x[2]+x[3])
t = sp.symbols("t", real=True)
check("interval_membership", sp.Interval(Q(3,100),Q(14,100)).contains(t) == sp.And(Q(3,100) <= t,t <= Q(14,100)))
c, total = sp.symbols("c total", positive=True)
check("rate_numerator", sp.cancel(c/total*120000-c*120000/total) == 0)
check("rate_bindings", [Q(c,n)*120000 for c,n in [(14,168799),(242,4623107),(180,1012985),(236,1009304)]] == [Q(1680000,168799),Q(29040000,4623107),Q(21600000,1012985),Q(28320000,1009304)])
check("reversed_relative_difference", (Q(584,10)-Q(706,10))/Q(706,10) == -Q(61,353) != -Q(61,292))
n = sp.symbols("n", positive=True, integer=True)
i = sp.symbols("i", integer=True)
duration = sp.Function("duration")
check("arbitrary_mean", sp.simplify(sp.Sum(duration(i)/n,(i,1,n)).doit() - sp.Sum(duration(i),(i,1,n)).doit()/n) == 0)
check("arbitrary_weights", sp.Sum(1/n,(i,1,n)).doit() == 1)

def ratio(numerator, denominator):
    return None if denominator == 0 else numerator/denominator

check("zero_denominator_undefined", ratio(Q(0),Q(0)) is None)
check("positive_denominator_defined", ratio(c,total) == c/total)
check("zero_equation_not_unique", sp.solveset(0*sp.Symbol("u"),sp.Symbol("u"),domain=sp.S.Reals) == sp.S.Reals)
report = {"backend":"Python/SymPy","checks":len(results),"passed":all(r["passed"] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
