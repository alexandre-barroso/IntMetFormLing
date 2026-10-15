import json
import sympy as sp
results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
check('c09_e0029_0', sp.simplify(sp.sympify('100*292/395',rational=True)-sp.sympify('29200/395',rational=True)) == 0)
check('c09_e0029_1', sp.simplify(sp.sympify('100*292/783',rational=True)-sp.sympify('29200/783',rational=True)) == 0)
check('c09_e0029_2', sp.sympify('Abs((29200/395)-(739/10))',rational=True)<=sp.sympify('1/20',rational=True))
check('c09_e0029_3', sp.sympify('Abs((29200/783)-(373/10))',rational=True)<=sp.sympify('1/20',rational=True))
check('c09_e0032_0', sp.simplify(sp.sympify('100*122/257',rational=True)-sp.sympify('12200/257',rational=True)) == 0)
check('c09_e0032_1', sp.simplify(sp.sympify('100*96/257',rational=True)-sp.sympify('9600/257',rational=True)) == 0)
check('c09_e0032_2', sp.sympify('Abs((12200/257)-(475/10))',rational=True)<=sp.sympify('1/20',rational=True))
check('c09_e0032_3', sp.sympify('Abs((9600/257)-(374/10))',rational=True)<=sp.sympify('1/20',rational=True))
print(json.dumps({"checks":len(results),"passed":all(r["passed"] for r in results),"results":results}))
raise SystemExit(0 if all(r["passed"] for r in results) else 1)
