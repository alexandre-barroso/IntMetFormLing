from fractions import Fraction as F
import math
import json
results = []
def check(identity, value):
    results.append({"id": identity, "passed": bool(value)})
check('c06.e0014', ((((((F(1,1)+F(2,1))+F(1,1))+F(3,1))+F(1,1))/F(8,1)) == (F(8,1)/F(8,1))) and ((F(8,1)/F(8,1)) == F(1,1)))
check('c06.e0033', (((F(2,1)/F(8,1))*(F(1,1)/F(8,1))) == (F(1,1)/F(32,1))))
check('c06.e0057', (((F(1,1)/F(2,1))/((F(1,1)/F(2,1))+(F(1,1)/F(2,1)))) == (F(1,1)/F(2,1))))
check('c06.e0061', (((F(1,1)/F(2,1))/((F(1,1)/F(2,1))+F(1,1))) == (F(1,1)/F(3,1))))
check('c06.e0087', (F(math.factorial(0)) == F(1,1)))
check('c06.e0096', (F(math.factorial(100)) == (F(100,1)*F(math.factorial(99)))))
check('c06.e0097', (F(math.factorial(1)) == F(1,1)))
check('c06.e0119', (((F(30,1)/F(100,1))*(F(40,1)/F(100,1))) == F(3,25)))
check('c06.e0120', (((F(70,1)/F(100,1))*(F(60,1)/F(100,1))) == F(21,50)))
check('c06.e0136', ((1/(F(2,1)**1)) == (F(1,1)/F(2,1))))
check('c06.e0143', (((F(2,1)/F(8,1))*(F(1,1)/F(2,1))) == (F(1,1)/F(8,1))))
check('c06.e0181', ((F(30,1)/F(6,1)) == F(5,1)))
check('c06.e0207', (((F(1,1)/F(2,1))+F(1,1)) == (F(3,1)/F(2,1))))
check('c06.e0231', ((((F(9,1)+F(4,1))+F(9,1))/F(8,1)) == (F(22,1)/F(8,1))) and ((F(22,1)/F(8,1)) == (F(11,1)/F(4,1))))
check('c06.e0257', (((F(2,1)/F(3,1))+(F(1,1)/F(3,1))) == F(1,1)))
check('c06.e0332', ((F(2,1)*(F(59,100)**2)) == (F(2,1)*F(3481,10000))) and ((F(2,1)*F(3481,10000)) == F(3481,5000)))
report = {"checks":len(results),"passed":all(item["passed"] for item in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
