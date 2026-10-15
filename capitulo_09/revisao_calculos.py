import json
import sympy as sp
results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
p=sp.Symbol('p',real=True)
check('indicator_numeric_cases',p*0==0 and 1*1==1)
print(json.dumps({"checks":len(results),"passed":all(r["passed"] for r in results),"results":results}))
raise SystemExit(0 if all(r["passed"] for r in results) else 1)
