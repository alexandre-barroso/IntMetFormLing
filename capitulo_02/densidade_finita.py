from pathlib import Path
import json
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
import densidade_interfaces as interfaces
import medida_finita as finite
from medida_finita import *

DENSITY_FUNCTION = FT(OMEGA, 'R')
DENSITY_INTEGRABLE = C('lebesgue_integrable_density', FT(DENSITY_FUNCTION, 'Prop'))
LEBESGUE_MEASURABLE = C('lebesgue_measurable_subset_real', SIGMA)
DENSITY_INTEGRAL = C('lebesgue_integral_over_event', FT(DENSITY_FUNCTION, MEASURE_FUNCTION))


def nonnegative_density(f):
    x = V('density_real_point', OMEGA)
    return All(x, Le(RZERO, A(f,x)))


def translated_interfaces():
    f = V('density_integrand', DENSITY_FUNCTION)
    a, b = V('density_event_a', EVENT), V('density_event_b', EVENT)
    sigma = LEBESGUE_MEASURABLE
    mu = A(DENSITY_INTEGRAL,f)
    integrable = A(DENSITY_INTEGRABLE,f)
    positive = nonnegative_density(f)
    return {
        'density_event_nonnegative': alls((f,a), imps((integrable,positive,A(sigma,a)),Le(RZERO,A(mu,a)))),
        'density_disjoint_union': alls((f,a,b), imps((integrable,A(sigma,a),A(sigma,b),event_disjoint(a,b)),Eq(A(mu,event_union(a,b)),Add(A(mu,a),A(mu,b))))),
        'density_empty_event': All(f,Eq(A(mu,empty_event()),RZERO)),
        'density_sigma_empty': A(sigma,empty_event()),
        'density_sigma_universe': A(sigma,universe_event()),
        'density_sigma_union': alls((a,b),imps((A(sigma,a),A(sigma,b)),A(sigma,event_union(a,b)))),
        'density_sigma_difference': alls((a,b),imps((A(sigma,a),A(sigma,b)),A(sigma,event_difference(a,b)))),
    }


def verified_bridge():
    checked={r['id']:r for r in interfaces.checks()}
    result=translated_interfaces()
    if not set(result)<=set(checked) or not all(checked[n]['passed'] for n in result):
        raise ValueError('unverified_measure_interface')
    return {'metamath_'+name:formula for name,formula in result.items()}


def derive_density_union(kernel):
    f=V('finite_density',DENSITY_FUNCTION)
    xs,family=V('density_event_list',LIST),V('density_event_family',FAMILY)
    a,b=V('density_local_event_a',EVENT),V('density_local_event_b',EVENT)
    sigma=LEBESGUE_MEASURABLE
    mu=A(DENSITY_INTEGRAL,f)
    integrable=A(DENSITY_INTEGRABLE,f)
    positive=nonnegative_density(f)
    normalized=Eq(A(mu,universe_event()),RONE)
    ha,hb=A(sigma,a),A(sigma,b)
    hd=event_disjoint(a,b)
    positive_event=apply(ax('metamath_density_event_nonnegative',f,a),('assume',integrable),('assume',positive),('assume',ha))
    positive_events=close(positive_event,(a,),(ha,))
    additive=apply(ax('metamath_density_disjoint_union',f,a,b),('assume',integrable),('assume',ha),('assume',hb),('assume',hd))
    additive_events=close(additive,(a,b),(ha,hb,hd))
    premises=(
        ('axiom','metamath_density_sigma_empty'),
        ('axiom','metamath_density_sigma_universe'),
        ('axiom','metamath_density_sigma_union'),
        ('axiom','metamath_density_sigma_difference'),
        positive_events,
        ax('metamath_density_empty_event',f),
        ('assume',normalized),
        additive_events
    )
    hm,disj=measurable(xs,family,sigma),disjoint(xs,family)
    result=apply(instantiate(('ref','finite_probability_union_and_sum_bounds'),sigma,mu,xs,family),*premises,('assume',hm),('assume',disj))
    conditions=(integrable,positive,normalized,hm,disj)
    statement=alls((f,xs,family),imps(conditions,kernel.infer(result).conclusion))
    kernel.theorem('density_finite_disjoint_union_and_bounds',statement,close(result,(f,xs,family),conditions))


def certificates():
    kernel=finite.certificates()
    kernel.axioms.update(verified_bridge())
    derive_density_union(kernel)
    return kernel


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel=certificates()
    check('density_finite_disjoint_union_and_bounds', 'density_finite_disjoint_union_and_bounds' in kernel.verified and not kernel.verified['density_finite_disjoint_union_and_bounds'].assumptions)
    return {'backend':'Python 3 Metamath and typed proof kernels','passed':True,'results':[{'id':name,'passed':True} for name in kernel.verified],'scope':'Every finite measurable disjoint family for any nonnegative Lebesgue-integrable density of total integral one on the real line. Integral interfaces are verified by the Metamath kernel before translation into the finite induction kernel.'}


if __name__=='__main__':
    print(json.dumps(verify()))
