import json
import sympy as sp
results=[]
def check(identity,value):
    results.append({"id":identity,"passed":bool(value)})

check('c04.e0008.1', sp.sympify('Abs(Integer(1))') == sp.sympify('Integer(1)'))
check('c04.e0008.2', sp.sympify('Abs(Mul(Integer(-1), Integer(1)))') == sp.sympify('Integer(1)'))
check('c04.e0008.3', sp.sympify('Abs(Mul(Integer(-1), Integer(3)))') == sp.sympify('Integer(3)'))
check('c04.e0010.1', sp.sympify('Add(Integer(1), Add(Add(Integer(1), Integer(1)), Integer(3)))') == sp.sympify('Integer(6)'))
check('c04.e0013.1', sp.sympify('Abs(Add(Integer(1), Mul(Integer(-1), Integer(5))))') == sp.sympify('Integer(4)'))
check('c04.e0014.1', sp.sympify('Add(Abs(Add(Integer(4), Mul(Integer(-1), Integer(3)))), Add(Abs(Add(Integer(2), Mul(Integer(-1), Integer(4)))), Add(Abs(Add(Integer(2), Mul(Integer(-1), Integer(1)))), Abs(Add(Integer(2), Mul(Integer(-1), Integer(5)))))))') == sp.sympify('Add(Integer(1), Add(Integer(2), Add(Integer(1), Integer(3))))'))
check('c04.e0014.2', sp.sympify('Add(Integer(1), Add(Integer(2), Add(Integer(1), Integer(3))))') == sp.sympify('Integer(7)'))
check('c04.e0015.1', sp.sympify('Add(Add(Integer(2), Mul(Integer(-1), Integer(3))), Add(Integer(3), Mul(Integer(-1), Integer(1))))') == sp.sympify('Add(Integer(2), Mul(Integer(-1), Integer(1)))'))
check('c04.e0015.2', sp.sympify('Add(Integer(2), Mul(Integer(-1), Integer(1)))') == sp.sympify('Integer(1)'))
check('c04.e0028.1', sp.sympify('Add(Integer(1), Add(Integer(0), Add(Add(Integer(0), Integer(1)), Integer(1))))') == sp.sympify('Integer(3)'))
check('c04.e0049.1', sp.sympify('Add(Mul(Integer(1), Integer(1)), Mul(Integer(1), Integer(1)))') == sp.sympify('Integer(2)'))
check('c04.e0062.1', sp.sympify('Add(Integer(1), Add(Integer(2), Add(Integer(1), Add(Integer(1), Add(Integer(1), Add(Integer(2), Add(Add(Integer(1), Integer(1)), Integer(4))))))))') == sp.sympify('Integer(14)'))
check('c04.e0075.1', sp.sympify('Mul(Pow(Integer(2), Integer(-1)), Mul(Integer(4), Add(Integer(4), Mul(Integer(-1), Integer(1)))))') == sp.sympify('Mul(Pow(Integer(2), Integer(-1)), Mul(Integer(3), Integer(4)))'))
check('c04.e0075.2', sp.sympify('Mul(Pow(Integer(2), Integer(-1)), Mul(Integer(3), Integer(4)))') == sp.sympify('Integer(6)'))
check('c04.e0098.1', sp.sympify('Add(Add(Mul(Integer(1), Mul(Integer(-1), Integer(4))), Mul(Integer(0), Rational(41, 10))), Mul(Integer(1), Mul(Integer(-1), Integer(4))))') == sp.sympify('Add(Add(Mul(Integer(-1), Integer(4)), Integer(0)), Mul(Integer(-1), Integer(4)))'))
check('c04.e0098.2', sp.sympify('Add(Add(Mul(Integer(-1), Integer(4)), Integer(0)), Mul(Integer(-1), Integer(4)))') == sp.sympify('Mul(Integer(-1), Integer(8))'))
check('c04.e0099.1', sp.sympify('Add(Add(Mul(Rational(41, 10), Mul(Integer(-1), Integer(2))), Mul(Integer(0), Integer(1))), Mul(Integer(0), Integer(1)))') == sp.sympify('Add(Add(Mul(Integer(-1), Rational(41, 5)), Integer(0)), Integer(0))'))
check('c04.e0099.2', sp.sympify('Add(Add(Mul(Integer(-1), Rational(41, 5)), Integer(0)), Integer(0))') == sp.sympify('Mul(Integer(-1), Rational(41, 5))'))
check('c04.e0100.1', sp.sympify('Mul(Integer(-1), Integer(8))') > sp.sympify('Mul(Integer(-1), Rational(41, 5))'))
check('c04.e0107.1', sp.sympify('Add(Integer(5552750), Add(Integer(25), Integer(6701706)))') == sp.sympify('Integer(12254481)'))
check('c04.e0112.1', sp.sympify('Mul(Rational(903, 1000), Integer(100))') == sp.sympify('Rational(903, 10)'))
check('c04.e0113.1', sp.sympify('Mul(Rational(1, 20), Integer(100))') == sp.sympify('Integer(5)'))
check('c04.e0273.1', sp.sympify('Add(Rational(4191, 250000), Rational(1837, 12500))') == sp.sympify('Rational(40931, 250000)'))
check('c04.e0277.1', sp.sympify('Add(Rational(112057, 250000), Mul(Integer(-1), Rational(23749, 500000)))') == sp.sympify('Rational(40073, 100000)'))
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r["passed"] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
