import json
from fractions import Fraction
import sympy as sp


def main():
    results=[]
    def check(name,condition):
        if not bool(condition):
            raise AssertionError(name)
        results.append(name)
    intersection,selected,target=292,395,783
    check('F12_input_domain',all(isinstance(value,int) for value in (intersection,selected,target)) and 0<=intersection<=min(selected,target) and selected>0 and target>0)
    check('F12_three_regions',selected-intersection==103 and target-intersection==491 and intersection+103+491==886)
    check('F12_precision_rounding',abs(100*Fraction(intersection,selected)-Fraction(739,10))<Fraction(1,20))
    check('F12_coverage_rounding',abs(100*Fraction(intersection,target)-Fraction(373,10))<Fraction(1,20))
    s,h=sp.symbols('s h',nonnegative=True)
    delta=sp.factor((292+s+h)/(886+s+h)-(292+s)/(886+s))
    check('F12_accuracy_exterior_dependence',sp.simplify(delta-594*h/((886+s+h)*(886+s)))==0)
    ss,pp,qq=sp.symbols('scope interrogative anteposed')
    check('F12_exterior_membership',sp.simplify(sp.Equivalent(sp.And(ss,sp.Not(sp.Or(pp,qq))),sp.And(ss,sp.Not(pp),sp.Not(qq))))==sp.true)
    print(json.dumps({'passed':True,'checks':len(results),'results':results,'scope':'Internally specified nonnegative set counts and exact rounding; symbolic dependence of global accuracy on the unspecified exterior for arbitrary nonnegative counts.'}))


if __name__=='__main__':
    main()
