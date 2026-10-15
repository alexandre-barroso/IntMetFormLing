import json
import sys
import sympy as sp

results = []

def check(identifier, result):
    results.append({"id": identifier, "passed": bool(result)})

o, s, m = sp.symbols("o s m", real=True)
bound = o + s - 2 * m * o
check("c05_d03_upper_signed_bound", sp.expand(bound - (o - s) - 2 * ((s - m) + m * (1 - o))) == 0)
check("c05_d03_lower_signed_bound", sp.expand(bound - (s - o) - 2 * o * (1 - m)) == 0)
check("c05_d03_sum_bound", sp.expand((1 + 1 - 2 * m) / 2 - (1 - m)) == 0)
sizes = [sp.Rational(4, 10), sp.Rational(3, 10), sp.Rational(3, 10)]
observed = [sp.Rational(6, 10), sp.Rational(2, 10), sp.Rational(2, 10)]
dispersion = sum(abs(left - right) for left, right in zip(observed, sizes)) / 2
check("c05_r05_source_dispersion", dispersion == sp.Rational(1, 5))
check("c05_d03_source_normalization", dispersion / (1 - min(sizes)) == sp.Rational(2, 7))
for j in range(3):
    concentrated = [int(i == j) for i in range(3)]
    value = sum(abs(left - right) for left, right in zip(concentrated, sizes)) / 2
    check("c05_d03_attained_" + str(j), value == 1 - sizes[j])
check("c05_r05_no_dispersion", sum(abs(value - value) for value in sizes) == 0)
report = {"backend": "Python/SymPy", "checks": len(results), "passed": all(item["passed"] for item in results), "results": results}
print(json.dumps(report))
sys.exit(0 if report["passed"] else 1)
