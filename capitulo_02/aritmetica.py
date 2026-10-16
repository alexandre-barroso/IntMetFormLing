from fractions import Fraction as F
import math
import json
results = []
def check(identity, value):
    results.append({"id": identity, "passed": bool(value)})
check('c02.e0031', ((F(2,25)*F(3,1)) == F(6,25)))
check('c02.e0095', ((F(10,1)**5) == ((((F(10,1)*F(10,1))*F(10,1))*F(10,1))*F(10,1))) and (((((F(10,1)*F(10,1))*F(10,1))*F(10,1))*F(10,1)) == F(100000,1)))
check('c02.e0096', ((F(8,1)*(F(10,1)**5)) == F(800000,1)))
check('c02.e0097', ((F(3,1)*(F(10,1)**5)) == F(300000,1)))
check('c02.e0098', ((F(5,1)*(F(10,1)**4)) == F(50000,1)))
check('c02.e0134', ((F(2,1)**9) == F(512,1)))
check('c02.e0135', ((F(2,1)**10) == F(1024,1)))
check('c02.e0197', ((F(63,100)/F(20,1)) == F(63,2000)))
check('c02.e0198', ((F(141,100)/F(20,1)) == F(141,2000)))
report = {"checks":len(results),"passed":all(item["passed"] for item in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
