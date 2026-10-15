import itertools
import json
import sys

results = []
for left, right in itertools.product((False, True), repeat=2):
    results.append({"id": "c03_r01_membership_" + str(int(left)) + str(int(right)), "passed": int(left or right) + int(left and right) == int(left) + int(right)})
report = {"backend": "Python", "checks": len(results), "passed": all(item["passed"] for item in results), "results": results}
print(json.dumps(report))
sys.exit(0 if report["passed"] else 1)
