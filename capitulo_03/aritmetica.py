from fractions import Fraction as F
import math
import json
results = []
def check(identity, value):
    results.append({"id": identity, "passed": bool(value)})
check('c03.e0057', ((F(4,1)/F(4,1)) == F(1,1)))
check('c03.e0066', ((F(158,1)/F(200,1)) == F(79,100)))
check('c03.e0067', ((F(72,1)/F(200,1)) == F(9,25)))
check('c03.e0068', ((F(5,1)*F(5,1)) == F(25,1)))
check('c03.e0097', (((((F(1,1)+F(2,1))+F(1,1))+F(3,1))+F(1,1)) == F(8,1)))
check('c03.e0324', ((F(69,1)-F(59,1)) == F(10,1)))
check('c03.e0325', ((F(8651,100)-F(85,1)) == F(151,100)))
check('c03.e0326', ((F(96,1)-F(72,1)) == F(24,1)))
report = {"checks":len(results),"passed":all(item["passed"] for item in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
