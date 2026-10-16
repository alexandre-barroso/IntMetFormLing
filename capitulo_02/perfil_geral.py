from pathlib import Path
import json
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import perfil_interfaces as interfaces
import capitulo_01.razoes as ratios
from capitulo_01.somas_finitas import *
from capitulo_07.probabilidade_geral import OMEGA, EVENT, Or, BOTTOM, Lt

PFUNCTION=FT(OMEGA,'R')
INTEGRABLE=C('profile_integrable_on',FT(EVENT,FT(PFUNCTION,'Prop')))
RAW=C('profile_lebesgue_integral',FT(EVENT,FT(PFUNCTION,'R')))
TOTAL=C('profile_totalized_integral',FT(EVENT,FT(PFUNCTION,'R')))


def neg(p):
    return Imp(p,BOTTOM)


def scale(c,f):
    x=V('profile_scale_point',OMEGA)
    return Lam(x,Mul(c,A(f,x)))


def square(f):
    x=V('profile_square_point',OMEGA)
    return Lam(x,Mul(A(f,x),A(f,x)))


def product(f,g):
    x=V('profile_product_point',OMEGA)
    return Lam(x,Mul(A(f,x),A(g,x)))


def zero():
    return Lam(V('profile_zero_point',OMEGA),RZERO)


def definitions():
    a=V('profile_domain',EVENT)
    f,g=V('profile_function',PFUNCTION),V('profile_other',PFUNCTION)
    x=V('profile_extensional_point',OMEGA)
    h=A(INTEGRABLE,a,f)
    return {
        'profile_function_extensionality':alls((f,g),Imp(All(x,Eq(A(f,x),A(g,x))),Eq(f,g))),
        'profile_total_integrable':alls((a,f),Imp(h,Eq(A(TOTAL,a,f),A(RAW,a,f)))),
        'profile_total_nonintegrable':alls((a,f),Imp(neg(h),Eq(A(TOTAL,a,f),RZERO)))
    }


def translated_interfaces():
    a=V('profile_domain',EVENT)
    f=V('profile_function',PFUNCTION)
    c=V('profile_scalar','R')
    h=A(INTEGRABLE,a,f)
    return {
        'profile_integrable_scaling':alls((a,f,c),Imp(h,A(INTEGRABLE,a,scale(c,f)))),
        'profile_integral_scaling':alls((a,f,c),Imp(h,Eq(Mul(c,A(RAW,a,f)),A(RAW,a,scale(c,f))))),
        'profile_zero_integral':All(a,Eq(A(RAW,a,zero()),RZERO))
    }


def verified_bridge():
    checked={r['id']:r for r in interfaces.checks()}
    result=translated_interfaces()
    if not set(result)<=set(checked) or not all(checked[n]['passed'] for n in result):
        raise ValueError('unverified_profile_interface')
    return {'metamath_'+n:p for n,p in result.items()}


def function_equality(kernel,left,right,equalities=()):
    x=V('profile_equality_point',OMEGA)
    proof=polynomial(kernel,Eq(A(left,x),A(right,x)),equalities)
    return apply(ax('profile_function_extensionality',left,right),close(proof,(x,)))


def cases(proposition,left,right):
    return ('or_e',('tautology',Or(proposition,neg(proposition))),left,right)


def derive_totalized_scale(kernel):
    a=V('total_domain',EVENT)
    f=V('total_function',PFUNCTION)
    c=V('total_scalar','R')
    h=A(INTEGRABLE,a,f)
    scaled=scale(c,f)
    hs=A(INTEGRABLE,a,scaled)
    hz=A(INTEGRABLE,a,zero())
    zi=apply(ax('profile_total_integrable',a,zero()),('assume',hz))
    zi=polynomial(kernel,Eq(A(TOTAL,a,zero()),RZERO),[zi,ax('metamath_profile_zero_integral',a)])
    zn=apply(ax('profile_total_nonintegrable',a,zero()),('assume',neg(hz)))
    zproof=cases(hz,zi,zn)
    kernel.theorem('totalized_zero_integral',All(a,Eq(A(TOTAL,a,zero()),RZERO)),close(zproof,(a,)))
    scalar_zero=Eq(c,RZERO)
    scalar_nonzero=neg(scalar_zero)
    inverse=Div(RONE,c)
    inverse_product=apply(ax('division_reconstruction_nonzero',RONE,c),('assume',scalar_nonzero))
    recovered=function_equality(kernel,scale(inverse,scaled),f,[ring(Mul(inverse,Mul(c,A(f,V('profile_equality_point',OMEGA)))),Mul(Mul(inverse,c),A(f,V('profile_equality_point',OMEGA)))),inverse_product])
    inverse_integrable=apply(ax('metamath_profile_integrable_scaling',a,scaled,inverse),('assume',hs))
    original_integrable=rewrite(kernel,inverse_integrable,recovered)
    contradiction=apply(('assume',neg(h)),original_integrable)
    scaled_not_integrable=close(contradiction,assumptions=(hs,))
    target=Eq(A(TOTAL,a,scaled),Mul(c,A(TOTAL,a,f)))
    nonintegrable_nonzero=polynomial(kernel,target,[apply(ax('profile_total_nonintegrable',a,scaled),scaled_not_integrable),apply(ax('profile_total_nonintegrable',a,f),('assume',neg(h)))])
    scaled_zero=function_equality(kernel,scaled,zero(),[('assume',scalar_zero)])
    nonintegrable_zero=polynomial(kernel,target,[scaled_zero,instantiate(('ref','totalized_zero_integral'),a),('assume',scalar_zero)])
    nonintegrable_case=cases(scalar_zero,nonintegrable_zero,nonintegrable_nonzero)
    scaled_integrable=apply(ax('metamath_profile_integrable_scaling',a,f,c),('assume',h))
    integrable_case=polynomial(kernel,target,[apply(ax('profile_total_integrable',a,scaled),scaled_integrable),apply(ax('profile_total_integrable',a,f),('assume',h)),symmetric(Mul(c,A(RAW,a,f)),A(RAW,a,scaled),apply(ax('metamath_profile_integral_scaling',a,f,c),('assume',h)))])
    proof=cases(h,integrable_case,nonintegrable_case)
    kernel.theorem('totalized_integral_scalar_linearity',alls((a,f,c),target),close(proof,(a,f,c)))
    nonzero=neg(Eq(A(TOTAL,a,f),RZERO))
    bad=apply(('assume',nonzero),apply(ax('profile_total_nonintegrable',a,f),('assume',neg(h))))
    integrability=cases(h,('assume',h),('false_e',h,bad))
    kernel.theorem('nonzero_totalized_integral_is_integrable',alls((a,f),Imp(nonzero,h)),close(integrability,(a,f),(nonzero,)))


def derive_profile(kernel):
    a=V('normalized_domain',EVENT)
    w,f=V('normalized_weight',PFUNCTION),V('normalized_signal',PFUNCTION)
    c=V('normalized_scalar','R')
    score=A(TOTAL,a,product(w,f))
    scaled_product=product(scale(c,w),f)
    product_identity=function_equality(kernel,scaled_product,scale(c,product(w,f)))
    scalar=instantiate(('ref','totalized_integral_scalar_linearity'),a,product(w,f),c)
    target=Eq(A(TOTAL,a,scaled_product),Mul(c,score))
    score_proof=polynomial(kernel,target,[product_identity,scalar])
    kernel.theorem('profile_score_scaling',alls((a,w,f,c),target),close(score_proof,(a,w,f,c)))
    scaled_square=square(scale(c,w))
    square_identity=function_equality(kernel,scaled_square,scale(Mul(c,c),square(w)))
    scalar=instantiate(('ref','totalized_integral_scalar_linearity'),a,square(w),Mul(c,c))
    target=Eq(A(TOTAL,a,scaled_square),Mul(Mul(c,c),A(TOTAL,a,square(w))))
    square_proof=polynomial(kernel,target,[square_identity,scalar])
    kernel.theorem('profile_square_scaling',alls((a,w,c),target),close(square_proof,(a,w,c)))
    normalization=Eq(A(TOTAL,a,square(w)),RONE)
    normalized_target=Eq(A(TOTAL,a,scaled_square),Mul(c,c))
    norm_proof=polynomial(kernel,normalized_target,[square_proof,('assume',normalization)])
    kernel.theorem('normalized_profile_square_scaling',alls((a,w,c),Imp(normalization,normalized_target)),close(norm_proof,(a,w,c),(normalization,)))
    nz=neg(Eq(A(TOTAL,a,square(w)),RZERO))
    zero_hyp=Eq(A(TOTAL,a,square(w)),RZERO)
    one_zero=polynomial(kernel,Eq(RONE,RZERO),[symmetric(A(TOTAL,a,square(w)),RONE,('assume',normalization)),('assume',zero_hyp)])
    bad=apply(apply(instantiate(('ref','positive_is_nonzero'),RONE),('axiom','one_positive')),one_zero)
    nonzero=close(bad,assumptions=(zero_hyp,))
    integral=apply(instantiate(('ref','nonzero_totalized_integral_is_integrable'),a,square(w)),nonzero)
    kernel.theorem('normalized_profile_square_is_integrable',alls((a,w),Imp(normalization,A(INTEGRABLE,a,square(w)))),close(integral,(a,w),(normalization,)))
    root=Eq(Mul(c,c),RONE)
    factors=Mul(Sub(c,RONE),Add(c,RONE))
    product_zero=polynomial(kernel,Eq(factors,RZERO),[ring(factors,Sub(Mul(c,c),RONE)),('assume',root)])
    choices=apply(ax('ratio_zero_product',Sub(c,RONE),Add(c,RONE)),product_zero)
    minus_one=Sub(RZERO,RONE)
    alternatives=Or(Eq(c,RONE),Eq(c,minus_one))
    left_zero=Eq(Sub(c,RONE),RZERO)
    left=polynomial(kernel,Eq(c,RONE),[ring(c,Add(Sub(c,RONE),RONE)),('assume',left_zero)])
    right_zero=Eq(Add(c,RONE),RZERO)
    right=polynomial(kernel,Eq(c,minus_one),[ring(c,Sub(Add(c,RONE),RONE)),('assume',right_zero)])
    roots=('or_e',choices,('or_l',Eq(c,minus_one),left),('or_r',Eq(c,RONE),right))
    forward=close(roots,assumptions=(root,))
    back_left=polynomial(kernel,root,[('assume',Eq(c,RONE))])
    back_right=polynomial(kernel,root,[('assume',Eq(c,minus_one))])
    backward=close(('or_e',('assume',alternatives),back_left,back_right),assumptions=(alternatives,))
    iff=both((forward,backward))
    kernel.theorem('real_square_one_iff_unit_sign',All(c,Iff(root,alternatives)),close(iff,(c,)))
    retained=Eq(A(TOTAL,a,scaled_square),RONE)
    to_square=polynomial(kernel,root,[symmetric(A(TOTAL,a,scaled_square),Mul(c,c),norm_proof),('assume',retained)])
    to_roots=apply(('and_l',iff),to_square)
    from_roots=apply(('and_r',iff),('assume',alternatives))
    back=polynomial(kernel,retained,[norm_proof,from_roots])
    proof=both((close(to_roots,assumptions=(retained,)),close(back,assumptions=(alternatives,))))
    kernel.theorem('profile_normalization_preserved_iff_unit_sign',alls((a,w,c),Imp(normalization,Iff(retained,alternatives))),close(proof,(a,w,c),(normalization,)))



def derive_oriented_profile(kernel):
    a,b=V('oriented_forward_domain',EVENT),V('oriented_backward_domain',EVENT)
    w,f=V('oriented_weight',PFUNCTION),V('oriented_signal',PFUNCTION)
    c=V('oriented_scalar','R')
    integral=lambda g:Sub(A(TOTAL,a,g),A(TOTAL,b,g))
    scalar=Eq(integral(scale(c,f)),Mul(c,integral(f)))
    proof=polynomial(kernel,scalar,[instantiate(('ref','totalized_integral_scalar_linearity'),domain,f,c) for domain in (a,b)])
    kernel.theorem('oriented_integral_scalar_linearity',alls((a,b,f,c),scalar),close(proof,(a,b,f,c)))
    score_target=Eq(integral(product(scale(c,w),f)),Mul(c,integral(product(w,f))))
    score_identity=function_equality(kernel,product(scale(c,w),f),scale(c,product(w,f)))
    score_proof=polynomial(kernel,score_target,[score_identity,instantiate(('ref','oriented_integral_scalar_linearity'),a,b,product(w,f),c)])
    kernel.theorem('oriented_profile_score_scaling',alls((a,b,w,f,c),score_target),close(score_proof,(a,b,w,f,c)))
    target=Eq(integral(square(scale(c,w))),Mul(Mul(c,c),integral(square(w))))
    square_identity=function_equality(kernel,square(scale(c,w)),scale(Mul(c,c),square(w)))
    square_proof=polynomial(kernel,target,[square_identity,instantiate(('ref','oriented_integral_scalar_linearity'),a,b,square(w),Mul(c,c))])
    kernel.theorem('oriented_profile_square_scaling',alls((a,b,w,c),target),close(square_proof,(a,b,w,c)))
    normalized=Eq(integral(square(w)),RONE)
    scaled_normalized=Eq(integral(square(scale(c,w))),RONE)
    alternatives=Or(Eq(c,RONE),Eq(c,Sub(RZERO,RONE)))
    square_one=Eq(Mul(c,c),RONE)
    normalized_scaling=polynomial(kernel,Eq(integral(square(scale(c,w))),Mul(c,c)),[square_proof,('assume',normalized)])
    square_value=polynomial(kernel,square_one,[symmetric(integral(square(scale(c,w))),Mul(c,c),normalized_scaling),('assume',scaled_normalized)])
    scalar_iff=instantiate(('ref','real_square_one_iff_unit_sign'),c)
    forward=apply(('and_l',scalar_iff),square_value)
    backward=polynomial(kernel,scaled_normalized,[normalized_scaling,apply(('and_r',scalar_iff),('assume',alternatives))])
    result=both((close(forward,assumptions=(scaled_normalized,)),close(backward,assumptions=(alternatives,))))
    statement=alls((a,b,w,c),Imp(normalized,Iff(scaled_normalized,alternatives)))
    kernel.theorem('oriented_profile_normalization_preserved_iff_unit_sign',statement,close(result,(a,b,w,c),(normalized,)))


def certificates():
    kernel=ratios.certificates()
    kernel.axioms.update(definitions())
    kernel.axioms.update(verified_bridge())
    derive_totalized_scale(kernel)
    derive_profile(kernel)
    derive_oriented_profile(kernel)
    return kernel


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel=certificates()
    check('nonzero_totalized_integral_is_integrable', 'nonzero_totalized_integral_is_integrable' in kernel.verified and not kernel.verified['nonzero_totalized_integral_is_integrable'].assumptions)
    check('normalized_profile_square_is_integrable', 'normalized_profile_square_is_integrable' in kernel.verified and not kernel.verified['normalized_profile_square_is_integrable'].assumptions)
    check('normalized_profile_square_scaling', 'normalized_profile_square_scaling' in kernel.verified and not kernel.verified['normalized_profile_square_scaling'].assumptions)
    check('oriented_integral_scalar_linearity', 'oriented_integral_scalar_linearity' in kernel.verified and not kernel.verified['oriented_integral_scalar_linearity'].assumptions)
    check('oriented_profile_normalization_preserved_iff_unit_sign', 'oriented_profile_normalization_preserved_iff_unit_sign' in kernel.verified and not kernel.verified['oriented_profile_normalization_preserved_iff_unit_sign'].assumptions)
    check('oriented_profile_score_scaling', 'oriented_profile_score_scaling' in kernel.verified and not kernel.verified['oriented_profile_score_scaling'].assumptions)
    check('oriented_profile_square_scaling', 'oriented_profile_square_scaling' in kernel.verified and not kernel.verified['oriented_profile_square_scaling'].assumptions)
    check('profile_normalization_preserved_iff_unit_sign', 'profile_normalization_preserved_iff_unit_sign' in kernel.verified and not kernel.verified['profile_normalization_preserved_iff_unit_sign'].assumptions)
    check('profile_score_scaling', 'profile_score_scaling' in kernel.verified and not kernel.verified['profile_score_scaling'].assumptions)
    check('profile_square_scaling', 'profile_square_scaling' in kernel.verified and not kernel.verified['profile_square_scaling'].assumptions)
    check('real_square_one_iff_unit_sign', 'real_square_one_iff_unit_sign' in kernel.verified and not kernel.verified['real_square_one_iff_unit_sign'].assumptions)
    check('totalized_integral_scalar_linearity', 'totalized_integral_scalar_linearity' in kernel.verified and not kernel.verified['totalized_integral_scalar_linearity'].assumptions)
    check('totalized_zero_integral', 'totalized_zero_integral' in kernel.verified and not kernel.verified['totalized_zero_integral'].assumptions)
    return {'backend':'Python 3 Metamath and typed proof kernels','passed':True,'results':[{'id':n,'passed':True} for n in kernel.verified],'scope':'Totalized real integral, zero outside L1; unrestricted real scalar, including zero. Nonzero integrals force integrability by the totalization definition. Score and squared-profile scaling are derived pointwise and via independently checked integral homogeneity.'}


if __name__=='__main__':
    print(json.dumps(verify()))
