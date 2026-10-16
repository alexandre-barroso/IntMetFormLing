import json
import sys
import mpmath as mp
import sympy as sp

results = []

def check(identifier, result):
    results.append({"id": identifier, "passed": bool(result)})

a, b, t, epsilon = sp.symbols("a b t epsilon", real=True)
n = sp.symbols("n", positive=True, integer=True)
j = sp.symbols("j", integer=True)
delta = (b - a) / n
check("c02_p05_partition_width", sp.simplify(n * delta - (b - a)) == 0)
check("c02_p05_partition_endpoint", sp.simplify(a + n * delta - b) == 0)
check("c02_p05_partition_increment", sp.simplify((a + j * delta) - (a + (j - 1) * delta) - delta) == 0)
check("c02_p05_constant_integral", sp.simplify(sp.summation(delta, (j, 1, n)) - sp.integrate(1, (t, a, b))) == 0)
check("c02_p05_uniform_error_bound", sp.simplify(n * epsilon * delta - epsilon * (b - a)) == 0)
check("c02_p05_error_limit", sp.limit(epsilon * (b - a), epsilon, 0, dir="+") == 0)
mp.mp.dps = 50
mu = -mp.mpf(268) / 100
sigma = mp.mpf(59) / 100
lower = mp.mpf(3) / 100
upper = mp.mpf(14) / 100

def density(value):
    return mp.exp(-((mp.log(value) - mu) ** 2) / (2 * sigma ** 2)) / (value * sigma * mp.sqrt(2 * mp.pi))

integral = mp.quad(density, [lower, upper])
cdf = lambda value: (1 + mp.erf((mp.log(value) - mu) / (sigma * mp.sqrt(2)))) / 2
check("c02_p05_density_integral", abs(integral - (cdf(upper) - cdf(lower))) < mp.mpf("1e-45"))
errors = []
for count in (16, 64, 256, 1024):
    width = (upper - lower) / count
    approximation = mp.fsum(density(lower + k * width) * width for k in range(1, count + 1))
    errors.append(abs(approximation - integral))
check("c02_p05_riemann_refinement", all(right < left for left, right in zip(errors, errors[1:])))
check("c02_p05_riemann_precision", errors[-1] < mp.mpf("0.001"))
w = sp.Function("w")(t)
f = sp.Function("f")(t)
alpha, beta = sp.symbols("alpha beta", real=True)
check("c02_n01_weighted_sum_linearity", sp.expand(w * (alpha * f + beta) - (alpha * w * f + beta * w)) == 0)
report = {"backend": "Python/SymPy/mpmath", "checks": len(results), "passed": all(item["passed"] for item in results), "results": results}
print(json.dumps(report))
sys.exit(0 if report["passed"] else 1)
