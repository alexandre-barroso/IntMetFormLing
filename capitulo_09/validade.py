import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
    if not condition:
        raise AssertionError(identifier)

def measures(S,P,Q):
    if not all(isinstance(a,(set,frozenset)) for a in (S,P,Q)):
        raise ValueError('finite sets required')
    selected=S&P;relevant=S&Q;correct=selected&Q
    return (None if not selected else sp.Rational(len(correct),len(selected)),None if not relevant else sp.Rational(len(correct),len(relevant)))

s,p,q=sp.symbols('s p q')
check('correct_subset_selected',sp.simplify_logic(sp.Implies(s&p&q,s&p))==sp.true)
check('correct_subset_relevant',sp.simplify_logic(sp.Implies(s&p&q,s&q))==sp.true)
check('selected_partition',sp.simplify_logic(sp.Equivalent(s&p,(s&p&q)|(s&p&~q)))==sp.true)
check('relevant_partition',sp.simplify_logic(sp.Equivalent(s&q,(s&p&q)|(s&~p&q)))==sp.true)
check('partition_disjointness',sp.simplify_logic((s&p&q)&(s&p&~q))==sp.false and sp.simplify_logic((s&p&q)&(s&~p&q))==sp.false)
t=sp.symbols('correct',positive=True)
u=sp.symbols('remainder',nonnegative=True)
u_positive=sp.symbols('remainder_positive',positive=True)
r=sp.symbols('ratio',real=True)
check('ratio_nonnegative', (t/(t+u)).is_nonnegative)
check('ratio_zero_numerator',0/u_positive==0 and u_positive/u_positive==1)
check('ratio_complement',sp.cancel(1-t/(t+u)-u/(t+u))==0)
check('ratio_upper_bound', (u/(t+u)).is_nonnegative)
check('empty_denominators',measures(set(),set(),set())==(None,None))
check('nested_sets',sp.simplify_logic(sp.Implies(sp.Implies(q,p),sp.Equivalent(p&q,q)))==sp.true)
opportunities=[5509,395,209];preposed=[601,292,89]
precision=[sp.Rational(a,b) for a,b in zip(preposed,opportunities)]
coverage=[sp.Rational(a,783) for a in preposed]
pplot=list(map(sp.Rational,['10.9','73.9','42.6']))
cplot=list(map(sp.Rational,['76.8','37.3','11.4']))
check('source_domains',all(0<=a<=b and b>0 and a<=783 for a,b in zip(preposed,opportunities)))
check('source_precision_range',all(0<=a<=1 for a in precision))
check('source_coverage_range',all(0<=a<=1 for a in coverage))
check('source_precision_plot_rounding',all(abs(100*a-b)<sp.Rational(1,20) for a,b in zip(precision,pplot)))
check('source_coverage_plot_rounding',all(abs(100*a-b)<sp.Rational(1,20) for a,b in zip(coverage,cplot)))
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r['passed'] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
