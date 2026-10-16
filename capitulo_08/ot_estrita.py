import json
import sympy as sp
from sympy.logic.inference import satisfiable


def certify_order_cases():
    p,q,r=sp.symbols('p q r',real=True)
    formulas={
        'irreflexive':sp.Lt(p,p,evaluate=False),
        'asymmetric_same_first_difference':sp.And(p<q,q<p),
        'asymmetric_earlier_first_difference':sp.And(p<q,sp.Eq(p,q)),
        'transitive_equal_first_difference':sp.And(p<q,q<r,p>=r),
        'transitive_left_first_difference':sp.And(p<q,sp.Eq(q,r),p>=r),
        'transitive_right_first_difference':sp.And(sp.Eq(p,q),q<r,p>=r),
        'equal_profiles_cannot_win':sp.And(sp.Eq(p,q),p<q)
    }
    for name,formula in formulas.items():
        if satisfiable(formula,use_lra_theory=True) is not False:
            raise AssertionError(name)
    return tuple(formulas)


def prefers(p,q):
    if len(p)!=len(q) or any(not isinstance(v,int) or v<0 for v in p+q):
        raise ValueError('Finite equally sized nonnegative violation profiles required')
    for left,right in zip(p,q):
        if left!=right:
            return left<right
    return False


def main():
    checked=[]
    def check(name,condition):
        if not bool(condition):
            raise AssertionError(name)
        checked.append(name)
    check('strict_order_all_first_difference_cases',len(certify_order_cases())==7)
    assert prefers((2,0),(1,1)) is False
    assert prefers((1,1),(2,0)) is True
    assert prefers((1,0),(0,1)) is False
    assert prefers((0,1),(1,0)) is True
    assert not prefers((1,0),(1,0))
    print(json.dumps({'passed':True,'checks':len(checked)+5,'results':checked,
                      'scope':'Exact linear-arithmetic certificates for every possible ordering of the two first-difference indices. General finite-profile transitivity, comparability and ties are proved in OtEstrita.lean; the additional examples only check the source tableau profiles under the stated priority order.'}))


if __name__=='__main__':
    main()
