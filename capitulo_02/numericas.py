import json
import sympy as sp
results=[]
def check(identity,value):
    results.append({"id":identity,"passed":bool(value)})

check('c02.e0031.1', sp.sympify('Mul(Rational(2, 25), Integer(3))') == sp.sympify('Rational(6, 25)'))
check('c02.e0095.1', sp.sympify('Pow(Integer(10), Integer(5))') == sp.sympify('Mul(Integer(10), Mul(Integer(10), Mul(Integer(10), Mul(Integer(10), Integer(10)))))'))
check('c02.e0095.2', sp.sympify('Mul(Integer(10), Mul(Integer(10), Mul(Integer(10), Mul(Integer(10), Integer(10)))))') == sp.sympify('Integer(100000)'))
check('c02.e0096.1', sp.sympify('Mul(Integer(8), Pow(Integer(10), Integer(5)))') == sp.sympify('Integer(800000)'))
check('c02.e0097.1', sp.sympify('Mul(Integer(3), Pow(Integer(10), Integer(5)))') == sp.sympify('Integer(300000)'))
check('c02.e0098.1', sp.sympify('Mul(Integer(5), Pow(Integer(10), Integer(4)))') == sp.sympify('Integer(50000)'))
check('c02.e0134.1', sp.sympify('Pow(Integer(2), Integer(9))') == sp.sympify('Integer(512)'))
check('c02.e0135.1', sp.sympify('Pow(Integer(2), Integer(10))') == sp.sympify('Integer(1024)'))
check('c02.e0197.1', sp.sympify('Mul(Rational(63, 100), Pow(Integer(20), Integer(-1)))') == sp.sympify('Rational(63, 2000)'))
check('c02.e0198.1', sp.sympify('Mul(Rational(141, 100), Pow(Integer(20), Integer(-1)))') == sp.sympify('Rational(141, 2000)'))
check('c02.e0270.1', sp.sympify('Mul(Mul(Integer(-1), Rational(227, 1000)), Pow(Mul(Integer(-1), Rational(67, 10000)), Integer(-1)))') == sp.sympify('Mul(Rational(227, 1000), Pow(Rational(67, 10000), Integer(-1)))'))
check('c02.e0270.2', sp.sympify('Mul(Rational(227, 1000), Pow(Rational(67, 10000), Integer(-1)))') == sp.sympify('Mul(Integer(2270), Pow(Integer(67), Integer(-1)))'))
check('c02.e0270.3', abs(sp.sympify('Mul(Integer(2270), Pow(Integer(67), Integer(-1)))')-sp.sympify('Rational(847, 25)'))<=sp.Rational(1,200))
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r["passed"] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
