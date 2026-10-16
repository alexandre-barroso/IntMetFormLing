import json
import sympy as sp
results=[]
def check(identity,value):
    results.append({"id":identity,"passed":bool(value)})

check('c03.e0018.1', sp.sympify('Add(Mul(Integer(-1), Integer(2)), Add(Integer(3), Integer(3)))') == sp.sympify('Integer(4)'))
check('c03.e0057.1', sp.sympify('Mul(Integer(4), Pow(Integer(4), Integer(-1)))') == sp.sympify('Integer(1)'))
check('c03.e0061.1', sp.sympify('Mul(Integer(3), Pow(Integer(4), Integer(-1)))') == sp.sympify('Rational(3, 4)'))
check('c03.e0065.1', sp.sympify('Mul(Integer(2), Pow(Integer(4), Integer(-1)))') == sp.sympify('Rational(1, 2)'))
check('c03.e0066.1', sp.sympify('Mul(Integer(158), Pow(Integer(200), Integer(-1)))') == sp.sympify('Rational(79, 100)'))
check('c03.e0067.1', sp.sympify('Mul(Integer(72), Pow(Integer(200), Integer(-1)))') == sp.sympify('Rational(9, 25)'))
check('c03.e0068.1', sp.sympify('Mul(Integer(5), Integer(5))') == sp.sympify('Integer(25)'))
check('c03.e0097.1', sp.sympify('Add(Integer(1), Add(Integer(3), Add(Integer(1), Add(Integer(1), Integer(2)))))') == sp.sympify('Integer(8)'))
check('c03.e0188.1', sp.sympify('Add(Integer(2), Integer(4))') == sp.sympify('Integer(6)'))
check('c03.e0324.1', sp.sympify('Add(Integer(69), Mul(Integer(-1), Integer(59)))') == sp.sympify('Integer(10)'))
check('c03.e0325.1', sp.sympify('Add(Rational(8651, 100), Mul(Integer(-1), Integer(85)))') == sp.sympify('Rational(151, 100)'))
check('c03.e0326.1', sp.sympify('Add(Integer(96), Mul(Integer(-1), Integer(72)))') == sp.sympify('Integer(24)'))
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r["passed"] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
