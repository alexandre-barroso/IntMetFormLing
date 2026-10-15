from fractions import Fraction as F
import math
import json
results = []
def check(identity, value):
    results.append({"id": identity, "passed": bool(value)})
check('c04.e0028', (((((F(1,1)+F(0,1))+F(1,1))+F(0,1))+F(1,1)) == F(3,1)))
check('c04.e0049', (((F(1,1)*F(1,1))+(F(1,1)*F(1,1))) == F(2,1)))
check('c04.e0098', ((((F(1,1)*(-F(4,1)))+(F(41,10)*F(0,1)))+(F(1,1)*(-F(4,1)))) == (((-F(4,1))+F(0,1))-F(4,1))) and ((((-F(4,1))+F(0,1))-F(4,1)) == (-F(8,1))))
check('c04.e0099', ((((F(1,1)*F(0,1))+(F(41,10)*(-F(2,1))))+(F(1,1)*F(0,1))) == ((F(0,1)-F(41,5))+F(0,1))) and (((F(0,1)-F(41,5))+F(0,1)) == (-F(41,5))))
check('c04.e0100', ((-F(8,1)) > (-F(41,5))))
check('c04.e0112', ((F(903,1000)*F(100,1)) == F(903,10)))
check('c04.e0113', ((F(1,20)*F(100,1)) == F(5,1)))
report = {"checks":len(results),"passed":all(item["passed"] for item in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
