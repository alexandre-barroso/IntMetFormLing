import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({'id':identifier,'passed':bool(condition)})
def joint_information_term(p,q,w):
    if sp.simplify(p*q)==0:
        return sp.Integer(0)
    return sp.Piecewise((0,sp.Eq(p*q,0)),(p*q*sp.log((p*q)/(p*w),2),True))
def conditional_information_term(p,q,w):
    if sp.simplify(p*q)==0:
        return sp.Integer(0)
    return sp.Piecewise((0,sp.Eq(p*q,0)),(p*q*sp.log(q/w,2),True))
p,q=sp.symbols('p q',nonnegative=True)
w=sp.symbols('w',positive=True)
check('weighted_information_term',sp.simplify(joint_information_term(p,q,w)-conditional_information_term(p,q,w))==0)
check('weighted_information_zero_terms',joint_information_term(0,q,w)==conditional_information_term(0,q,w)==0 and joint_information_term(p,0,w)==conditional_information_term(p,0,w)==0)
check('weighted_information_zero_column',joint_information_term(p,0,0)==conditional_information_term(p,0,0)==0 and joint_information_term(0,q,0)==conditional_information_term(0,q,0)==0)
i,j=sp.symbols('i j',integer=True)
m,n=sp.symbols('m n',integer=True,nonnegative=True)
probabilities=sp.IndexedBase('probabilities',nonnegative=True)
conditionals=sp.IndexedBase('conditionals',nonnegative=True)
marginals=sp.IndexedBase('marginals',positive=True)
summand=joint_information_term(probabilities[i],conditionals[i,j],marginals[j])-conditional_information_term(probabilities[i],conditionals[i,j],marginals[j])
check('weighted_information_sum',sp.Sum(summand,(i,1,m),(j,1,n)).doit()==0)
successes,failures=sp.symbols('successes failures',integer=True,nonnegative=True)
pp,qq=sp.symbols('pp qq',positive=True)
check('pattern_grouped_products',sp.product(pp,(i,1,successes))*sp.product(qq,(i,1,failures))==pp**successes*qq**failures and sp.simplify(successes+failures-successes)==failures)
check('pattern_reordering_laws',sp.expand(pp*qq-qq*pp)==0 and sp.expand((pp*qq)*w-pp*(qq*w))==0)
check('pattern_empty_products',sp.product(pp,(i,1,0))==1 and sp.product(qq,(i,1,0))==1)
positive_count=sp.symbols('positive_count',integer=True,positive=True)
check('pattern_boundary_products',sp.product(0,(i,1,positive_count))==0 and sp.product(1,(i,1,positive_count))==1 and sp.product(0,(i,1,0))==1)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
