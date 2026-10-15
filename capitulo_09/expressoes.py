import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
Q=sp.Rational
s,p,q=sp.symbols('s p q')
check("correct_subsets",sp.simplify_logic(sp.Implies(s&p&q,s&p))==True and sp.simplify_logic(sp.Implies(s&p&q,s&q))==True)
def precision(S,P,Q):
    selected=S&P
    return None if not selected else sp.Rational(len(selected&Q),len(selected))
def coverage(S,P,Q):
    relevant=S&Q
    return None if not relevant else sp.Rational(len(relevant&P),len(relevant))
check("precision_empty",precision(set(),set(),set()) is None)
check("coverage_empty",coverage(set(),set(),set()) is None)
before=sp.Matrix([[85,15],[4,105]]);after=sp.Matrix([[100,0],[4,105]])
check("revision_rows",[sum(before.row(i)) for i in range(2)]==[sum(after.row(i)) for i in range(2)]==[100,109])
check("revision_columns",[sum(before.col(i)) for i in range(2)]==[89,120] and [sum(after.col(i)) for i in range(2)]==[104,105])
check("revision_conservation",sum(before)==sum(after)==209 and after-before==sp.Matrix([[15,-15],[0,0]]))
check("revision_proportion",sum(after.col(0))/sum(after)-sum(before.col(0))/sum(before)==Q(15,209))
transfer=[Q(x,1000) for x in [997,986,918,951,966,936,813,906,985]]
check("transfer_mean",sum(transfer)==Q(8458,1000) and sum(transfer)/len(transfer)==Q(4229,4500))
a,b=sp.symbols('a b')
check("nested_indicators",sp.simplify_logic(sp.Implies(sp.Implies(b,a),sp.Equivalent(a&b,b)))==True)
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r['passed'] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
