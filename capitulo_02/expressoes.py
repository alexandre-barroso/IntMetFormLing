import json
import sympy as sp

results = []

def check(identifier, condition):
    results.append({"id": identifier, "passed": bool(condition)})

Q = sp.Rational
c = sp.Symbol("c", integer=True, nonnegative=True)
keep = sp.Piecewise((0,c <= 5),(1,True))
check("keep_cases", keep.as_expr_set_pairs() == [(0,sp.Interval(-sp.oo,5)),(1,sp.Interval.open(5,sp.oo))])
m,L,L1,L2,h = sp.symbols("m L L1 L2 h", real=True)
check("affine_difference", sp.expand(m*L2-m*L1-m*(L2-L1)) == 0)
check("finite_rate", sp.cancel((m*L2-m*L1)/(L2-L1)-m) == 0)
check("linear_increment_steps", all(sp.cancel(v-m) == 0 for v in [(m*(L+h)-m*L)/h,(m*L+m*h-m*L)/h,m*h/h]))
x,y = sp.symbols("x y", positive=True)
u,v = sp.symbols("u v", real=True)
check("power_product", sp.powsimp(2**u*2**v) == 2**(u+v))
check("logarithm_base_conversion", sp.log(x,2) == sp.log(x)/sp.log(2))
check("logarithm_inverse", sp.simplify(2**sp.log(x,2)-x) == 0)
check("logarithm_product", sp.simplify(sp.expand_log(sp.log(x*y,2))-sp.log(x,2)-sp.log(y,2)) == 0)
check("logarithm_quotient", sp.simplify(sp.expand_log(sp.log(x/y,2))-sp.log(x,2)+sp.log(y,2)) == 0)
check("logarithm_power", sp.simplify(sp.expand_log(sp.log(x**v,2))-v*sp.log(x,2)) == 0)
R = Q(119275347,128700)
check("association_logarithm_bounds", 2**197 < R**20 < 2**199 and Q(197,20) < sp.log(R,2) < Q(199,20))
check("association_logarithm_order", 9 < sp.log(R,2) < 10)
a,n = sp.symbols("a n", positive=True)
b,c = sp.symbols("b c", real=True)
mal = a*n**b*sp.exp(-c*n)
check("mal_logarithm", sp.simplify(sp.expand_log(sp.log(mal))-sp.log(a)-b*sp.log(n)+c*n) == 0)
check("mal_derivative_original", sp.simplify(sp.diff(mal,n)-mal*(b/n-c)) == 0)
check("mal_logarithmic_rate", sp.simplify(sp.diff(mal,n)/mal-b/n+c) == 0)
negative_c = sp.symbols("negative_c", negative=True)
delta = sp.symbols("delta", positive=True)
before = sp.simplify((b/n-c).subs({b:negative_c*(n+delta),c:negative_c}))
after = sp.simplify((b/n-c).subs({b:negative_c*(n-delta),c:negative_c}))
check("derivative_sign_before", before == negative_c*delta/n and before.is_negative is True)
check("derivative_sign_after", after == -negative_c*delta/n and after.is_positive is True)
d = sp.symbols("d", real=True)
check("inverse_rate_sign", sp.reduce_inequalities(-d/y**2 > 0,d) == (d < 0) and sp.reduce_inequalities(-d/y**2 < 0,d) == (0 < d))
steps = [(1/(x+h)-1/x)/h,(x-(x+h))/(x*(x+h)*h),-h/(x*(x+h)*h),-1/(x*(x+h))]
check("reciprocal_steps", all(sp.cancel(left-right) == 0 for left,right in zip(steps,steps[1:])))
N = sp.symbols("N", positive=True, integer=True)
j = sp.symbols("j", integer=True)
check("equal_partition_sum", sp.simplify(sp.Sum(m*L/N,(j,1,N)).doit()-m*L) == 0)
positive_b,p = sp.symbols("positive_b p", positive=True)
check("decreasing_reading_time", (-positive_b/(p*sp.log(2))).is_negative is True)

A,C,r,alpha,lam=sp.symbols("A C r alpha lam",positive=True)
ell=sp.Symbol("ell",real=True)
check('zipf_logarithm', sp.simplify(sp.expand_log(sp.log(C*r**(-alpha)),force=True)-(sp.log(C)-alpha*sp.log(r)))==0)
check('frequency_duration_logarithm', sp.simplify(sp.expand_log(sp.log(A*sp.exp(-lam*ell)),force=True)-(sp.log(A)-lam*ell))==0)
check('frequency_duration_composition', sp.simplify(sp.solve(sp.log(A)-lam*ell-sp.log(C)+alpha*sp.log(r),ell)[0]-alpha*sp.log(r)/lam-(sp.log(A)-sp.log(C))/lam)==0)


report = {"backend":"Python/SymPy","checks":len(results),"passed":all(r["passed"] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
