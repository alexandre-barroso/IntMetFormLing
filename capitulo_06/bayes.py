import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({'id':identifier,'passed':bool(condition)})
n=sp.symbols('n',integer=True,positive=True)
i=sp.symbols('i',integer=True)
prior=sp.IndexedBase('prior',nonnegative=True)
likelihood=sp.IndexedBase('likelihood',nonnegative=True)
evidence=sp.symbols('evidence',positive=True)
weight=prior[i]*likelihood[i]
weight_sum=sp.Sum(weight,(i,1,n))
posterior_sum=sp.Sum(weight/evidence,(i,1,n))
check('bayes_finite_normalization',sp.simplify(posterior_sum-weight_sum/evidence)==0 and (weight_sum/evidence).subs(weight_sum,evidence)==1)
check('bayes_nonnegative',weight.is_nonnegative is True and (weight/evidence).is_nonnegative is True)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
