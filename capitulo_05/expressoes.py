import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
Q=sp.Rational
x=list(map(Q,[2,2,2,2,3,1,2,2,2,2,1,2,1,3,2,1,2,2,2,2]))
mean=lambda xs:sum(xs)/len(xs)
variance=lambda xs:sum((v-mean(xs))**2 for v in xs)/(len(xs)-1)
check("mean_from_observations", sum(x)==38 and mean(x)==Q(19,10))
check("variance_from_observations", sum(v-mean(x) for v in x)==0 and sum((v-mean(x))**2 for v in x)==Q(29,5) and variance(x)==Q(29,95))
sizes=list(map(Q,['.4','.3','.3']));observations=list(map(Q,['.6','.2','.2']))
dispersion=lambda o,s:sum(abs(a-b) for a,b in zip(o,s))/2
check("dispersion_from_distributions", dispersion(observations,sizes)==Q(1,5) and sum(sizes)==sum(observations)==1)
check("normalized_dispersion", min(sizes)==sizes[1] and dispersion(observations,sizes)/(1-min(sizes))==Q(2,7))
check("weighted_empirical_mean", sum(a*b for a,b in zip([Q(4,20),Q(14,20),Q(2,20)],[1,2,3]))==mean(x))
m=sp.symbols('m',real=True);s=sp.symbols('s',nonzero=True)
check("standardization_origin_unit", sp.cancel((m-m)/s)==0 and sp.cancel((m+s-m)/s)==1)
O1=sp.Matrix([[180,3],[20,153]]);O2=sp.Matrix([[29,13],[123,31612]])
row=lambda o:[sum(o.row(i)) for i in range(o.rows)]
col=lambda o:[sum(o.col(j)) for j in range(o.cols)]
expected=lambda o:sp.Matrix(o.rows,o.cols,lambda i,j:row(o)[i]*col(o)[j]/sum(o))
check("margins_one", row(O1)==[183,173] and col(O1)==[200,156] and sum(O1)==356)
check("margins_two", row(O2)==[42,31735] and col(O2)==[152,31625] and sum(O2)==31777)
check("expected_one", expected(O1)==sp.Matrix([[36600,28548],[34600,26988]])/356)
check("expected_two", expected(O2)==sp.Matrix([[6384,1328250],[4823720,1003619375]])/31777)
r,total,column,next_column=sp.symbols('r total column next_column',nonzero=True)
check("expected_row_general_base", r*0/total==0)
check("expected_row_general_step", sp.cancel(r*column/total+r*next_column/total-r*(column+next_column)/total)==0)
check("expected_row_general_total", sp.cancel(r*total/total-r)==0)
e=expected(O2)
terms=[O2[i,j]*sp.log(O2[i,j]/e[i,j]) for i in range(2) for j in range(2)]
targets=[29*sp.log(Q(921533,6384)),13*sp.log(Q(413101,1328250)),123*sp.log(Q(3908571,4823720)),31612*sp.log(Q(1004534524,1003619375))]
check("contributions_from_table", terms==targets)
check("g_from_table", sp.expand(2*sum(terms)-2*sum(targets))==0)
def valid_sample_variance(xs):
    if len(xs)<2:
        raise ValueError('sample_variance_requires_at_least_two_observations')
    return variance(xs)
def valid_standardize(value,center,scale):
    if scale<=0:
        return None
    return (value-center)/scale
def valid_expected(o):
    if any(value<0 for value in o) or sum(o)<=0:
        return None
    return expected(o)
check("sample_variance_domain",len(x)>=2 and valid_sample_variance(x)>=0)
invalid_sample_rejected=False
try:
    valid_sample_variance([Q(1)])
except ValueError:
    invalid_sample_rejected=True
check("sample_variance_rejects_singleton",invalid_sample_rejected)
check("standardization_zero_scale",valid_standardize(Q(1),Q(2),Q(0)) is None)
positive_difference,positive_scale=sp.symbols('positive_difference positive_scale',positive=True)
check("standardization_sign",(positive_difference/positive_scale).is_positive and (-positive_difference/positive_scale).is_negative)
check("expected_distribution_domain",all(valid_expected(o) is not None and all(v>=0 for v in valid_expected(o)) and row(valid_expected(o))==row(o) and col(valid_expected(o))==col(o) and sum(valid_expected(o))==sum(o) for o in [O1,O2]))
check("expected_rejects_zero_total",valid_expected(sp.zeros(2,2)) is None)
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r["passed"] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
