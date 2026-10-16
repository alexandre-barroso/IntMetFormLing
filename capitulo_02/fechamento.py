import json
import sympy as sp

results = []

def check(name, proposition):
    if proposition is not True and proposition != sp.true:
        raise AssertionError((name, proposition))
    results.append({"id": name, "passed": True})

u, k, x, c = sp.symbols("u k x c", real=True)
d, s, A, lam = sp.symbols("d s A lam", positive=True)
e = sp.Symbol("e", nonnegative=True)
check("addition_order_gap", sp.expand((u+d+k)-(u+k)) == d)
check("addition_order_positive", d.is_positive)
check("positive_scale_order_gap", sp.expand(s*(u+d)-s*u) == s*d)
check("positive_scale_order_positive", (s*d).is_positive)
check("negative_scale_reversed_gap", sp.expand((-s)*u-(-s)*(u+d)) == s*d)
check("negative_scale_reversed_positive", (s*d).is_positive)
check("weak_order_gaps", sp.expand((u+e+k)-(u+k)) == e and sp.expand(s*(u+e)-s*u) == s*e and sp.expand((-s)*u-(-s)*(u+e)) == s*e and e.is_nonnegative and (s*e).is_nonnegative)
f = A*sp.exp(-lam*x)
check("decreasing_exponential_difference", sp.simplify(f-f.subs(x,x+d)-f*(1-sp.exp(-lam*d))) == 0)
check("decreasing_exponential_derivative", sp.simplify(sp.diff(f,x)+A*lam*sp.exp(-lam*x)) == 0)
check("decreasing_exponential_derivative_negative", sp.diff(f,x).is_negative)
g = sp.exp(s*x)
check("growing_exponential_derivative", sp.simplify(sp.diff(g,x)-s*g) == 0)
check("growing_exponential_derivative_positive", sp.diff(g,x).is_positive)
F = sp.Function("F")
G = sp.Function("G")
z = sp.Symbol("z", real=True)
check("derivative_constant", sp.diff(c,x) == 0)
check("derivative_sum", sp.diff(F(x)+G(x),x) == sp.diff(F(x),x)+sp.diff(G(x),x))
check("derivative_constant_factor", sp.diff(c*F(x),x) == c*sp.diff(F(x),x))
check("derivative_composition", sp.simplify(sp.diff(G(F(x)),x)-sp.Subs(sp.diff(G(z),z),z,F(x)).doit()*sp.diff(F(x),x)) == 0)
p, q, r = sp.symbols("p q r", nonnegative=True)
check("finite_probability_partition_identity", sp.expand((p+q+r)-(p+q)) == r)
check("finite_probability_partition_bound", r.is_nonnegative and (p+q).is_nonnegative)
fa, fb, fc, fd = sp.symbols("fa fb fc fd", real=True)
check("adjacent_integral_endpoint_cancellation", sp.expand((fb-fa)+(fc-fb)) == fc-fa)
print(json.dumps({"backend":"Python/SymPy","scope":"exact symbolic order gaps for arbitrary real inputs and positive/negative scales; exponential derivative signs; formal differentiation identities whose analytic hypotheses are proved in Lean", "checks":len(results),"passed":True,"results":results}))
