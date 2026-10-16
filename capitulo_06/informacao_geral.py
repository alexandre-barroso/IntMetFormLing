from pathlib import Path
import sys
import json
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from capitulo_07.probabilidade_geral import V,C,FT,A,Lam,All,Ex,Imp,And,Or,Eq,Iff,BOTTOM,Kernel,Sequent,RZERO,RONE,Le,Lt,Mul,Add,Sub,Div,alls,imps,field_axioms,add_axioms,instantiate,apply,close,ax,ref,hyp,ring,rewrite,rewrite_right,symmetric,normalize,same,substitute,free_variables,sort_of,eq_trans,logical,rejects

base_ax=ax
ANALYTIC_NAMES=('log_positive_quotient','log_positive_product','log_two_positive','log_one_zero','log_mean_value')
def ax(name,*terms):
 return ref(name,*terms) if name in ANALYTIC_NAMES or name=='log_upper_bound' else base_ax(name,*terms)

LOG=C('natural_log',FT('R','R'))
def Log(x):return A(LOG,x)
def list_sort(t):return ('List',t)
def nil(t):return C('list_nil',list_sort(t))
def cons(h,t):return A(C('list_cons',FT(sort_of(h),FT(sort_of(t),sort_of(t)))),h,t)
def sumv(xs,f):return A(C('finite_sum',FT(sort_of(xs),FT(sort_of(f),'R'))),xs,f)
def mem(h,xs):return A(C('list_member',FT(sort_of(h),FT(sort_of(xs),'Prop'))),h,xs)
def sy(k,p):
 a,b=k.infer(p).conclusion[1:]
 return symmetric(a,b,p)
def rr(k,p,e,reverse=False):return rewrite_right(k,p,e,reverse)
def cn(k,p,target):
 if not same(k.infer(p).conclusion,target):raise ValueError(('conversion',k.infer(p).conclusion,target))
 return ('conversion',target,p)
def cong(k,p,fun):
 a,b=k.infer(p).conclusion[1:]
 z=V('congruence_variable',sort_of(a))
 if z in free_variables(fun):raise ValueError('fresh congruence')
 return ('eq_e',p,z,Eq(A(fun,a),A(fun,z)),('eq_i',A(fun,a)))
def theorem(k,name,variables,conditions,conclusion,p):
 return k.theorem(name,alls(variables,imps(conditions,conclusion)),close(cn(k,p,conclusion),variables,conditions))
def algebra_foundations():
 x,y,z=(V(n,'R') for n in ('field_x','field_y','field_z'))
 return {
 'nonnegative_product':alls((x,y),imps((Le(RZERO,x),Le(RZERO,y)),Le(RZERO,Mul(x,y)))),
 'positive_product':alls((x,y),imps((Lt(RZERO,x),Lt(RZERO,y)),Lt(RZERO,Mul(x,y)))),
 'positive_quotient':alls((x,y),imps((Lt(RZERO,x),Lt(RZERO,y)),Lt(RZERO,Div(x,y)))),
 'nonnegative_quotient':alls((x,y),imps((Le(RZERO,x),Lt(RZERO,y)),Le(RZERO,Div(x,y)))),
 'positive_product_factors':alls((x,y),imps((Le(RZERO,x),Le(RZERO,y),Lt(RZERO,Mul(x,y))),And(Lt(RZERO,x),Lt(RZERO,y)))),
 'positive_le_transitive':alls((x,y),imps((Lt(RZERO,x),Le(x,y)),Lt(RZERO,y))),
 'positive_division_self':All(x,Imp(Lt(RZERO,x),Eq(Div(x,x),RONE))),
 'quotient_times_positive':alls((x,y),Imp(Lt(RZERO,y),Eq(Mul(y,Div(x,y)),x))),
 'quotient_product_cancel_positive':alls((x,y,z),Imp(Lt(RZERO,x),Eq(Div(Mul(x,y),Mul(x,z)),Div(y,z)))),
 'quotient_quotient_total':alls((x,y,z),Eq(Div(Div(x,y),z),Div(x,Mul(y,z)))),
 'quotient_as_product':alls((x,y),Eq(Div(x,y),Mul(x,Div(RONE,y)))),
 'division_zero_total':All(x,Eq(Div(RZERO,x),RZERO)),
 'division_positive_preserves_nonnegative':alls((x,y),imps((Le(RZERO,x),Lt(RZERO,y)),Le(RZERO,Div(x,y)))),
 'subtraction_order_reverse':alls((x,y,z),Iff(Lt(Sub(z,x),Sub(z,y)),Lt(y,x))),
 'subtraction_weak_order_reverse':alls((x,y,z),Iff(Le(Sub(z,x),Sub(z,y)),Le(y,x))),
 'nonnegative_difference_order':alls((x,y),Iff(Le(RZERO,Sub(x,y)),Le(y,x))),
 'log_positive_quotient':alls((x,y),imps((Lt(RZERO,x),Lt(RZERO,y)),Eq(Log(Div(x,y)),Sub(Log(x),Log(y))))),
 'log_positive_product':alls((x,y),imps((Lt(RZERO,x),Lt(RZERO,y)),Eq(Log(Mul(x,y)),Add(Log(x),Log(y))))),
 'log_one_zero':Eq(Log(RONE),RZERO),
 'log_mean_value':alls((x,y),imps((Lt(RZERO,x),Lt(x,y)),Ex(z,And(Lt(x,z),And(Lt(z,y),Eq(Div(RONE,z),Div(Sub(Log(y),Log(x)),Sub(y,x)))))))),
 'one_positive':Lt(RZERO,RONE),
 'strict_to_weak':alls((x,y),Imp(Lt(x,y),Le(x,y))),
 'strict_transitive':alls((x,y,z),imps((Lt(x,y),Lt(y,z)),Lt(x,z))),
 'positive_difference':alls((x,y),Imp(Lt(x,y),Lt(RZERO,Sub(y,x)))),
 'order_trichotomy':alls((x,y),Or(Lt(x,y),Or(Eq(x,y),Lt(y,x)))),
 'positive_quotient_comparison':alls((x,y,z),Imp(Lt(RZERO,z),Iff(Le(Div(x,z),y),Le(x,Mul(y,z))))),
 'positive_quotient_comparison_reverse':alls((x,y,z),Imp(Lt(RZERO,z),Iff(Le(y,Div(x,z)),Le(Mul(y,z),x)))),
 'log_two_positive':Lt(RZERO,Log(Add(RONE,RONE)))
 }
class InformationKernel(Kernel):
 def infer(self,proof,environment=None):
  if isinstance(proof,tuple) and proof and proof[0]=='analytic':
   if len(proof)!=2 or proof[1] not in ANALYTIC_NAMES:raise ValueError('unknown analytic bridge')
   from capitulo_06.fundamentos_informacao import logarithm_basic_certificates
   if not hasattr(self,'analytic_verified'):
    self.analytic_verified=logarithm_basic_certificates()
   if proof[1] not in self.analytic_verified:raise ValueError('analytic proof missing')
   return Sequent(frozenset(),algebra_foundations()[proof[1]])
  return super().infer(proof,environment)

def sum_foundations(t):
 xs=V('sum_list',list_sort(t));h=V('sum_head',t);f=V('sum_function',FT(t,'R'));x=V('sum_element',t)
 return {
 'sum_nil_'+t:All(f,Eq(sumv(nil(t),f),RZERO)),
 'sum_cons_'+t:alls((h,xs,f),Eq(sumv(cons(h,xs),f),Add(A(f,h),sumv(xs,f)))),
 'member_nil_'+t:All(x,Imp(mem(x,nil(t)),BOTTOM)),
 'member_cons_'+t:alls((x,h,xs),Iff(mem(x,cons(h,xs)),Or(Eq(x,h),mem(x,xs))))
 }
def derive_sums(k,t):
 add_axioms(k,sum_foundations(t))
 xs=V('xs_'+t,list_sort(t));tail=V('tail_'+t,list_sort(t));head=V('head_'+t,t);x=V('x_'+t,t)
 f=V('f_'+t,FT(t,'R'));g=V('g_'+t,FT(t,'R'));c=V('c_'+t,'R')
 def establish(name,vars,conditions,body,base,step):
  tailbody=substitute(body,xs,tail)
  step=close(cn(k,step,substitute(body,xs,cons(head,tail))),(head,tail),(tailbody,))
  proof=('list_induction',xs,head,tail,body,cn(k,base,substitute(body,xs,nil(t))),step)
  return theorem(k,name,vars,conditions,All(xs,body),proof)
 for name,op in [('add',Add),('sub',Sub)]:
  fg=Lam(x,op(A(f,x),A(g,x)))
  body=Eq(sumv(xs,fg),op(sumv(xs,f),sumv(xs,g)))
  base=ax('sum_nil_'+t,fg)
  rhs=('eq_i',op(sumv(nil(t),f),sumv(nil(t),g)));rhs=rr(k,rhs,ax('sum_nil_'+t,f));rhs=rr(k,rhs,ax('sum_nil_'+t,g));rhs=rr(k,rhs,ring(op(RZERO,RZERO),RZERO));base=eq_trans(sumv(nil(t),fg),RZERO,op(sumv(nil(t),f),sumv(nil(t),g)),base,sy(k,rhs))
  step=ax('sum_cons_'+t,head,tail,fg)
  step=rr(k,step,hyp(substitute(body,xs,tail)))
  right=op(Add(A(f,head),sumv(tail,f)),Add(A(g,head),sumv(tail,g)))
  step=eq_trans(sumv(cons(head,tail),fg),k.infer(step).conclusion[2],right,step,ring(k.infer(step).conclusion[2],right))
  step=rr(k,step,ax('sum_cons_'+t,head,tail,f),True);step=rr(k,step,ax('sum_cons_'+t,head,tail,g),True)
  establish('sum_'+name+'_'+t,(f,g),(),body,base,step)
 fg=Lam(x,Mul(c,A(f,x)));body=Eq(sumv(xs,fg),Mul(c,sumv(xs,f)))
 base=ax('sum_nil_'+t,fg);rhs=('eq_i',Mul(c,sumv(nil(t),f)));rhs=rr(k,rhs,ax('sum_nil_'+t,f));rhs=rr(k,rhs,ring(Mul(c,RZERO),RZERO));base=eq_trans(sumv(nil(t),fg),RZERO,Mul(c,sumv(nil(t),f)),base,sy(k,rhs))
 step=ax('sum_cons_'+t,head,tail,fg);step=rr(k,step,hyp(substitute(body,xs,tail)))
 right=Mul(c,Add(A(f,head),sumv(tail,f)));step=eq_trans(sumv(cons(head,tail),fg),k.infer(step).conclusion[2],right,step,ring(k.infer(step).conclusion[2],right));step=rr(k,step,ax('sum_cons_'+t,head,tail,f),True)
 establish('sum_scale_'+t,(f,c),(),body,base,step)
 samepoint=All(x,Eq(A(f,x),A(g,x)));body=Eq(sumv(xs,f),sumv(xs,g))
 base=ax('sum_nil_'+t,f);base=rr(k,base,ax('sum_nil_'+t,g),True)
 step=ax('sum_cons_'+t,head,tail,f);step=rr(k,step,instantiate(hyp(samepoint),head));step=rr(k,step,hyp(substitute(body,xs,tail)));step=rr(k,step,ax('sum_cons_'+t,head,tail,g),True)
 establish('sum_congr_'+t,(f,g),(samepoint,),body,base,step)
 nonneg=All(x,Le(RZERO,A(f,x)));body=Le(RZERO,sumv(xs,f))
 z=V('nonneg_base_'+t,'R');base=('eq_e',sy(k,ax('sum_nil_'+t,f)),z,Le(RZERO,z),ax('real_order_reflexive',RZERO))
 step=apply(ax('addition_monotone',RZERO,A(f,head),RZERO,sumv(tail,f)),instantiate(hyp(nonneg),head),hyp(substitute(body,xs,tail)))
 step=rewrite(k,step,ring(Add(RZERO,RZERO),RZERO));step=rewrite(k,step,ax('sum_cons_'+t,head,tail,f),True)
 establish('sum_nonnegative_'+t,(f,),(nonneg,),body,base,step)
 pointle=All(x,Le(A(f,x),A(g,x)));body=Le(sumv(xs,f),sumv(xs,g))
 z=V('base_sum_'+t,'R');base=('eq_e',sy(k,ax('sum_nil_'+t,f)),z,Le(z,RZERO),ax('real_order_reflexive',RZERO));base=('eq_e',sy(k,ax('sum_nil_'+t,g)),z,Le(sumv(nil(t),f),z),base)
 step=apply(ax('addition_monotone',A(f,head),A(g,head),sumv(tail,f),sumv(tail,g)),instantiate(hyp(pointle),head),hyp(substitute(body,xs,tail)))
 step=rewrite(k,step,ax('sum_cons_'+t,head,tail,f),True);step=rewrite(k,step,ax('sum_cons_'+t,head,tail,g),True)
 establish('sum_monotone_'+t,(f,g),(pointle,),body,base,step)
 zero=Lam(x,RZERO);body=Eq(sumv(xs,zero),RZERO)
 base=ax('sum_nil_'+t,zero);step=ax('sum_cons_'+t,head,tail,zero);step=rr(k,step,hyp(substitute(body,xs,tail)));step=rr(k,step,ring(Add(RZERO,RZERO),RZERO))
 establish('sum_zero_'+t,(),(),body,base,step)
 body=Imp(mem(x,xs),Le(A(f,x),sumv(xs,f)))
 base=('false_e',Le(A(f,x),sumv(nil(t),f)),apply(ax('member_nil_'+t,x),hyp(mem(x,nil(t)))));base=close(base,(),(mem(x,nil(t)),))
 choices=apply(('and_l',ax('member_cons_'+t,x,head,tail)),hyp(mem(x,cons(head,tail))))
 tailnonneg=instantiate(apply(ref('sum_nonnegative_'+t,f),hyp(nonneg)),tail)
 hle=apply(ax('addition_monotone',A(f,head),A(f,head),RZERO,sumv(tail,f)),ax('real_order_reflexive',A(f,head)),tailnonneg);hle=rewrite(k,hle,ring(Add(A(f,head),RZERO),A(f,head)))
 hle=rewrite(k,hle,hyp(Eq(x,head)),True)
 z=V('head_restore_'+t,t);hle=('eq_e',hyp(Eq(x,head)),z,Le(A(f,x),Add(A(f,z),sumv(tail,f))),hle)
 tle=apply(hyp(substitute(body,xs,tail)),hyp(mem(x,tail)))
 addle=apply(ax('addition_monotone',RZERO,A(f,head),sumv(tail,f),sumv(tail,f)),instantiate(hyp(nonneg),head),ax('real_order_reflexive',sumv(tail,f)));addle=rewrite(k,addle,ring(Add(RZERO,sumv(tail,f)),sumv(tail,f)))
 tle=apply(ax('real_order_transitive',A(f,x),sumv(tail,f),Add(A(f,head),sumv(tail,f))),tle,addle)
 step=('or_e',choices,hle,tle);step=rewrite(k,step,ax('sum_cons_'+t,head,tail,f),True);step=close(step,(),(mem(x,cons(head,tail)),))
 establish('sum_member_bound_'+t,(f,x),(nonneg,),body,base,step)
 return k

def sum_equality(k,x,xs,p):
 a,b=k.infer(p).conclusion[1:]
 f,g=Lam(x,a),Lam(x,b)
 return instantiate(apply(ref('sum_congr_'+sort_of(x),f,g),close(p,(x,))),xs)
def sum_rule(k,rule,x,xs,expression,*args):
 return instantiate(ref('sum_'+rule+'_'+sort_of(x),Lam(x,expression),*args),xs)
def sum_monotonicity(k,x,xs,p):
 formula=k.infer(p).conclusion
 left,right=formula[1][2],formula[2]
 return instantiate(apply(ref('sum_monotone_'+sort_of(x),Lam(x,left),Lam(x,right)),close(p,(x,))),xs)
def trans(k,p,q):
 a,b=k.infer(p).conclusion[1:];c,d=k.infer(q).conclusion[1:]
 if not same(b,c):raise ValueError('equality transitivity middle mismatch')
 return eq_trans(a,b,d,p,cn(k,q,Eq(b,d)))
def derive_fubini(k,t,u):
 xs=V('fubini_xs_'+t+u,list_sort(t));ys=V('fubini_ys_'+t+u,list_sort(u))
 h=V('fubini_head_'+t+u,t);tail=V('fubini_tail_'+t+u,list_sort(t));x=V('fubini_x_'+t+u,t);y=V('fubini_y_'+t+u,u)
 f=V('fubini_f_'+t+u,FT(t,FT(u,'R')))
 row=Lam(x,sumv(ys,Lam(y,A(f,x,y))))
 col=lambda z:Lam(y,sumv(z,Lam(x,A(f,x,y))))
 body=Eq(sumv(xs,row),sumv(ys,col(xs)))
 lhs=ax('sum_nil_'+t,row)
 rhs=sum_equality(k,y,ys,ax('sum_nil_'+t,Lam(x,A(f,x,y))))
 rhs=trans(k,rhs,instantiate(ref('sum_zero_'+u),ys))
 base=trans(k,lhs,sy(k,rhs))
 step=ax('sum_cons_'+t,h,tail,row);step=rr(k,step,hyp(substitute(body,xs,tail)))
 add=instantiate(ref('sum_add_'+u,Lam(y,A(f,h,y)),col(tail)),ys)
 step=trans(k,step,sy(k,add))
 inner=ax('sum_cons_'+t,h,tail,Lam(x,A(f,x,y)))
 step=trans(k,step,sy(k,sum_equality(k,y,ys,inner)))
 induction=('list_induction',xs,h,tail,body,cn(k,base,substitute(body,xs,nil(t))),close(cn(k,step,substitute(body,xs,cons(h,tail))),(h,tail),(substitute(body,xs,tail),)))
 theorem(k,'sum_fubini_'+t+u,(f,ys),(),All(xs,body),induction)

def derive_log_upper(k):
 x=V('log_argument','R');c=V('mean_value_point','R')
 positive=Lt(RZERO,x);less=Lt(x,RONE);equal=Eq(x,RONE);greater=Lt(RONE,x)
 target=Le(Log(x),Sub(x,RONE))
 zero=ax('log_one_zero')
 onecase=ax('real_order_reflexive',RZERO)
 z=V('one_bound_placeholder','R')
 onecase=('eq_e',sy(k,zero),z,Le(z,RZERO),onecase)
 onecase=('eq_e',sy(k,ring(Sub(RONE,RONE),RZERO)),z,Le(Log(RONE),z),onecase)
 onecase=('eq_e',sy(k,hyp(equal)),z,Le(Log(z),Sub(z,RONE)),onecase)
 upper_exists=apply(ax('log_mean_value',RONE,x),ax('one_positive'),hyp(greater))
 upperbody=And(Lt(RONE,c),And(Lt(c,x),Eq(Div(RONE,c),Div(Sub(Log(x),Log(RONE)),Sub(x,RONE)))))
 cup=('and_l',hyp(upperbody));eq=('and_r',('and_r',hyp(upperbody)))
 cpositive=apply(ax('strict_transitive',RZERO,RONE,c),ax('one_positive'),cup)
 cle=apply(ax('strict_to_weak',RONE,c),cup)
 cle=rewrite(k,cle,ring(Mul(RONE,c),c),True)
 recip=apply(('and_r',apply(ax('positive_quotient_comparison',RONE,RONE,c),cpositive)),cle)
 width=Sub(x,RONE);widthpositive=apply(ax('positive_difference',RONE,x),hyp(greater));widthnonneg=apply(ax('positive_implies_nonnegative',width),widthpositive)
 bound=apply(ax('nonnegative_multiplication_monotone',width,Div(RONE,c),RONE),widthnonneg,recip)
 bound=rewrite(k,bound,eq)
 bound=rewrite(k,bound,apply(ax('quotient_times_positive',Sub(Log(x),Log(RONE)),width),widthpositive))
 bound=rewrite(k,bound,ax('log_one_zero'));bound=rewrite(k,bound,ring(Sub(Log(x),RZERO),Log(x)));bound=rewrite(k,bound,ring(Mul(width,RONE),width))
 upper=('ex_e',upper_exists,c,cn(k,bound,target))
 lower_exists=apply(ax('log_mean_value',x,RONE),hyp(positive),hyp(less))
 lowerbody=And(Lt(x,c),And(Lt(c,RONE),Eq(Div(RONE,c),Div(Sub(Log(RONE),Log(x)),Sub(RONE,x)))))
 clow=('and_l',hyp(lowerbody));cu=('and_l',('and_r',hyp(lowerbody)));eq=('and_r',('and_r',hyp(lowerbody)))
 cpositive=apply(ax('strict_transitive',RZERO,x,c),hyp(positive),clow)
 cle=apply(ax('strict_to_weak',c,RONE),cu);cle=rewrite(k,cle,ring(Mul(RONE,c),c),True)
 recip=apply(('and_r',apply(ax('positive_quotient_comparison_reverse',RONE,RONE,c),cpositive)),cle)
 width=Sub(RONE,x);widthpositive=apply(ax('positive_difference',x,RONE),hyp(less));widthnonneg=apply(ax('positive_implies_nonnegative',width),widthpositive)
 bound=apply(ax('nonnegative_multiplication_monotone',width,RONE,Div(RONE,c)),widthnonneg,recip)
 bound=rewrite(k,bound,eq);bound=rewrite(k,bound,apply(ax('quotient_times_positive',Sub(Log(RONE),Log(x)),width),widthpositive));bound=rewrite(k,bound,ax('log_one_zero'));bound=rewrite(k,bound,ring(Mul(width,RONE),width))
 increment=Sub(Log(x),width)
 bound=apply(ax('addition_monotone',width,Sub(RZERO,Log(x)),increment,increment),bound,ax('real_order_reflexive',increment))
 bound=rewrite(k,bound,ring(Add(width,increment),Log(x)));bound=rewrite(k,bound,ring(Add(Sub(RZERO,Log(x)),increment),Sub(x,RONE)))
 lower=('ex_e',lower_exists,c,cn(k,bound,target))
 nested=('or_e',hyp(Or(equal,greater)),cn(k,onecase,target),upper)
 cases=('or_e',ax('order_trichotomy',x,RONE),lower,nested)
 theorem(k,'log_upper_bound',(x,),(positive,),target,cases)

def derive_log_lower(k):
 p,q=V('mass_p','R'),V('reference_q','R')
 conditions=(Le(RZERO,p),Le(RZERO,q),Imp(Lt(RZERO,p),Lt(RZERO,q)))
 target=Le(Sub(p,q),Mul(p,Log(Div(p,q))))
 zero=Eq(p,RZERO);positive=Lt(RZERO,p)
 z=V('zero_placeholder','R')
 negq=Sub(RZERO,q)
 nonpositive=apply(ax('addition_monotone',RZERO,q,negq,negq),hyp(conditions[1]),ax('real_order_reflexive',negq))
 nonpositive=rewrite(k,nonpositive,ring(Add(RZERO,negq),negq));nonpositive=rewrite(k,nonpositive,ring(Add(q,negq),RZERO))
 rhs0=ring(Mul(RZERO,Log(Div(RZERO,q))),RZERO)
 nonpositive=('eq_e',sy(k,rhs0),z,Le(negq,z),nonpositive)
 nonpositive=('eq_e',sy(k,hyp(zero)),z,Le(Sub(z,q),Mul(z,Log(Div(z,q)))),nonpositive)
 qp=apply(hyp(conditions[2]),hyp(positive))
 ratio_pos=apply(ax('positive_quotient',q,p),qp,hyp(positive))
 log_bound=apply(ax('log_upper_bound',Div(q,p)),ratio_pos)
 scaled=apply(ax('nonnegative_multiplication_monotone',p,Log(Div(q,p)),Sub(Div(q,p),RONE)),hyp(conditions[0]),log_bound)
 decomp=ring(Mul(p,Sub(Div(q,p),RONE)),Sub(Mul(p,Div(q,p)),p));decomp=rr(k,decomp,apply(ax('quotient_times_positive',q,p),hyp(positive)))
 scaled=rewrite(k,scaled,decomp)
 reverse=('eq_i',Mul(p,Log(Div(q,p))))
 reverse=rr(k,reverse,apply(ax('log_positive_quotient',q,p),qp,hyp(positive)))
 reverse=trans(k,reverse,ring(k.infer(reverse).conclusion[2],Sub(RZERO,Mul(p,Sub(Log(p),Log(q))))))
 reverse=rr(k,reverse,apply(ax('log_positive_quotient',p,q),hyp(positive),qp),True)
 scaled=rewrite(k,scaled,reverse)
 x=Mul(p,Log(Div(p,q)))
 scaled=apply(ax('addition_right_backward',Sub(RZERO,x),p,q),scaled)
 scaled=apply(ax('addition_monotone',Add(Sub(RZERO,x),p),q,x,x),scaled,ax('real_order_reflexive',x))
 scaled=rewrite(k,scaled,ring(Add(Add(Sub(RZERO,x),p),x),p))
 scaled=apply(ax('addition_monotone',p,Add(q,x),negq,negq),scaled,ax('real_order_reflexive',negq))
 scaled=rewrite(k,scaled,ring(Add(p,negq),Sub(p,q)))
 target_positive=rewrite(k,scaled,ring(Add(Add(q,x),negq),x))
 cases=apply(ax('nonnegative_zero_or_positive',p),hyp(conditions[0]))
 proof=('or_e',cases,cn(k,nonpositive,target),cn(k,target_positive,target))
 theorem(k,'weighted_log_ratio_lower',(p,q),conditions,target,proof)

def derive_mutual_information(k):
 xs=V('joint_rows',list_sort('M'));ys=V('joint_columns',list_sort('U'))
 i=V('joint_i','M');j=V('joint_j','U');u=V('joint_u','U');m=V('joint_m','M')
 p=V('joint_distribution',FT('M',FT('U','R')))
 row=lambda x:sumv(ys,Lam(u,A(p,x,u)))
 col=lambda y:sumv(xs,Lam(m,A(p,m,y)))
 pi=A(p,i,j);qi=Mul(row(i),col(j));term=Mul(pi,Log(Div(pi,qi)))
 total=sumv(xs,Lam(i,row(i)))
 conditions=(alls((i,j),Le(RZERO,pi)),Eq(total,RONE),All(i,mem(i,xs)),All(j,mem(j,ys)))
 nonneg=conditions[0]
 rownonneg=instantiate(apply(ref('sum_nonnegative_U',Lam(u,A(p,i,u))),close(instantiate(hyp(nonneg),i,u),(u,))),ys)
 colnonneg=instantiate(apply(ref('sum_nonnegative_M',Lam(m,A(p,m,j))),close(instantiate(hyp(nonneg),m,j),(m,))),xs)
 qnonneg=apply(ax('nonnegative_product',row(i),col(j)),rownonneg,colnonneg)
 rowbound=apply(instantiate(apply(ref('sum_member_bound_U',Lam(u,A(p,i,u)),j),close(instantiate(hyp(nonneg),i,u),(u,))),ys),instantiate(hyp(conditions[3]),j))
 colbound=apply(instantiate(apply(ref('sum_member_bound_M',Lam(m,A(p,m,j)),i),close(instantiate(hyp(nonneg),m,j),(m,))),xs),instantiate(hyp(conditions[2]),i))
 positive=Lt(RZERO,pi)
 rowpositive=apply(ax('positive_le_transitive',pi,row(i)),hyp(positive),rowbound)
 colpositive=apply(ax('positive_le_transitive',pi,col(j)),hyp(positive),colbound)
 support=close(apply(ax('positive_product',row(i),col(j)),rowpositive,colpositive),(),(positive,))
 lower=apply(ref('weighted_log_ratio_lower',pi,qi),instantiate(hyp(nonneg),i,j),qnonneg,support)
 lower=sum_monotonicity(k,j,ys,lower);lower=sum_monotonicity(k,i,xs,lower)
 coltotal=instantiate(ref('sum_fubini_MU',p,ys),xs)
 coltotal=trans(k,sy(k,coltotal),hyp(conditions[1]))
 qsum=instantiate(ref('sum_scale_U',Lam(j,col(j)),row(i)),ys)
 qsum=rr(k,qsum,coltotal);qsum=rr(k,qsum,ring(Mul(row(i),RONE),row(i)))
 qtotal=trans(k,sum_equality(k,i,xs,qsum),hyp(conditions[1]))
 left=instantiate(ref('sum_sub_U',Lam(j,pi),Lam(j,qi)),ys)
 left=sum_equality(k,i,xs,left)
 left=trans(k,left,instantiate(ref('sum_sub_M',Lam(i,row(i)),Lam(i,sumv(ys,Lam(j,qi)))),xs))
 left=rr(k,left,hyp(conditions[1]));left=rr(k,left,qtotal);left=rr(k,left,ring(Sub(RONE,RONE),RZERO))
 lower=rewrite(k,lower,left)
 natural=sumv(xs,Lam(i,sumv(ys,Lam(j,term))))
 information=Div(natural,Log(Add(RONE,RONE)))
 positive=apply(ax('division_positive_preserves_nonnegative',natural,Log(Add(RONE,RONE))),cn(k,lower,Le(RZERO,natural)),ax('log_two_positive'))
 theorem(k,'finite_joint_mutual_information_nonnegative',(p,xs,ys),conditions,Le(RZERO,information),positive)
 theorem(k,'finite_independent_reference_normalized',(p,xs,ys),conditions,Eq(sumv(xs,Lam(i,sumv(ys,Lam(j,qi)))),RONE),qtotal)
 conditional_term=Mul(pi,Log(Div(pi,row(i))))
 marginal_term=Mul(pi,Log(col(j)))
 target=Eq(term,Sub(conditional_term,marginal_term))
 zero_case=Eq(pi,RZERO)
 zero_left=('eq_i',term);zero_left=rr(k,zero_left,hyp(zero_case));zero_left=rr(k,zero_left,ring(k.infer(zero_left).conclusion[2],RZERO))
 zero_right=('eq_i',Sub(conditional_term,marginal_term));zero_right=rr(k,zero_right,hyp(zero_case));zero_right=rr(k,zero_right,ring(k.infer(zero_right).conclusion[2],RZERO))
 zproof=trans(k,zero_left,sy(k,zero_right))
 ppositive=Lt(RZERO,pi)
 qpositive=apply(ax('positive_product',row(i),col(j)),rowpositive,colpositive)
 term_positive=('eq_i',term)
 term_positive=rr(k,term_positive,apply(ax('log_positive_quotient',pi,qi),hyp(ppositive),qpositive))
 term_positive=rr(k,term_positive,apply(ax('log_positive_product',row(i),col(j)),rowpositive,colpositive))
 term_positive=trans(k,term_positive,ring(k.infer(term_positive).conclusion[2],Sub(Mul(pi,Sub(Log(pi),Log(row(i)))),marginal_term)))
 term_positive=rr(k,term_positive,apply(ax('log_positive_quotient',pi,row(i)),hyp(ppositive),rowpositive),True)
 eq=('or_e',apply(ax('nonnegative_zero_or_positive',pi),instantiate(hyp(nonneg),i,j)),cn(k,zproof,target),cn(k,term_positive,target))
 eq=sum_equality(k,j,ys,eq);eq=trans(k,eq,instantiate(ref('sum_sub_U',Lam(j,conditional_term),Lam(j,marginal_term)),ys))
 eq=sum_equality(k,i,xs,eq);eq=trans(k,eq,instantiate(ref('sum_sub_M',Lam(i,sumv(ys,Lam(j,conditional_term))),Lam(i,sumv(ys,Lam(j,marginal_term)))),xs))
 agg=instantiate(ref('sum_fubini_MU',Lam(i,Lam(j,marginal_term)),ys),xs)
 inner=sum_right_scale(k,i,xs,pi,Log(col(j)))
 agg=trans(k,agg,sum_equality(k,j,ys,inner));eq=rr(k,eq,agg)
 csum=sumv(xs,Lam(i,sumv(ys,Lam(j,conditional_term))))
 hsum=sumv(ys,Lam(j,Mul(col(j),Log(col(j)))))
 eq=cn(k,eq,Eq(natural,Sub(csum,hsum)))
 ln2=Log(Add(RONE,RONE));conditional=Div(Sub(RZERO,csum),ln2);entropy=Div(Sub(RZERO,hsum),ln2)
 eq=cong(k,eq,Lam(V('entropy_base','R'),Div(V('entropy_base','R'),ln2)))
 eq=rr(k,eq,ring(Sub(csum,hsum),Sub(Sub(RZERO,hsum),Sub(RZERO,csum))))
 eq=trans(k,eq,division_difference(k,Sub(RZERO,hsum),Sub(RZERO,csum),ln2))
 theorem(k,'finite_MI_entropy_identity',(p,xs,ys),conditions,Eq(information,Sub(entropy,conditional)),eq)
 bound=rewrite(k,positive,eq)
 bound=apply(('and_l',ax('nonnegative_difference_order',entropy,conditional)),bound)
 theorem(k,'finite_conditioning_reduces_average_entropy',(p,xs,ys),conditions,Le(conditional,entropy),bound)

 return k

def derive_log_split(k):
 t,r,d,u=(V(n,'R') for n in ('weight','meaning_mass','decoder_mass','universe_mass'))
 support=Imp(Lt(RZERO,t),And(Lt(RZERO,r),And(Lt(RZERO,d),Lt(RZERO,u))))
 conditions=(Le(RZERO,t),support)
 left=Mul(t,Log(Div(r,d)));right=Sub(Mul(t,Log(Div(r,u))),Mul(t,Log(Div(d,u))))
 z=Eq(t,RZERO);pos=Lt(RZERO,t)
 zero=ring(substitute(left,t,RZERO),substitute(right,t,RZERO));zero=rewrite(k,zero,hyp(z),True)
 supported=apply(hyp(support),hyp(pos));rp=('and_l',supported);dp=('and_l',('and_r',supported));up=('and_r',('and_r',supported))
 positive=('eq_i',left)
 positive=rr(k,positive,apply(ax('log_positive_quotient',r,d),rp,dp))
 positive=trans(k,positive,ring(k.infer(positive).conclusion[2],Sub(Mul(t,Sub(Log(r),Log(u))),Mul(t,Sub(Log(d),Log(u))))))
 positive=rr(k,positive,apply(ax('log_positive_quotient',r,u),rp,up),True)
 positive=rr(k,positive,apply(ax('log_positive_quotient',d,u),dp,up),True)
 proof=('or_e',apply(ax('nonnegative_zero_or_positive',t),hyp(conditions[0])),zero,positive)
 theorem(k,'zero_safe_weighted_log_split',(t,r,d,u),conditions,Eq(left,right),proof)

def sum_right_scale(k,x,xs,expression,scalar):
 first=sum_equality(k,x,xs,ring(Mul(expression,scalar),Mul(scalar,expression)))
 second=instantiate(ref('sum_scale_'+sort_of(x),Lam(x,expression),scalar),xs)
 answer=trans(k,first,second)
 return trans(k,answer,ring(Mul(scalar,sumv(xs,Lam(x,expression))),Mul(sumv(xs,Lam(x,expression)),scalar)))

def division_difference(k,a,b,c):
 p=ax('quotient_as_product',Sub(a,b),c)
 p=trans(k,p,ring(k.infer(p).conclusion[2],Sub(Mul(a,Div(RONE,c)),Mul(b,Div(RONE,c)))))
 p=rr(k,p,ax('quotient_as_product',a,c),True);p=rr(k,p,ax('quotient_as_product',b,c),True)
 return p
def sum_division(k,x,xs,expression,denominator):
 p=sum_equality(k,x,xs,ax('quotient_as_product',expression,denominator))
 p=trans(k,p,sum_right_scale(k,x,xs,expression,Div(RONE,denominator)))
 return trans(k,p,sy(k,ax('quotient_as_product',sumv(xs,Lam(x,expression)),denominator)))
def weighted_division(k,a,b,c):
 p=('eq_i',Mul(a,Div(b,c)));p=rr(k,p,ax('quotient_as_product',b,c))
 p=trans(k,p,ring(k.infer(p).conclusion[2],Mul(Mul(a,b),Div(RONE,c))))
 return trans(k,p,sy(k,ax('quotient_as_product',Mul(a,b),c)))

def derive_color(k):
 ms=V('meanings',list_sort('M'));ws=V('words',list_sort('W'));us=V('universe',list_sort('U'))
 m=V('meaning','M');w=V('word','W');u=V('item','U');mi=V('meaning_index','M');wi=V('word_index','W');ui=V('item_index','U')
 p=V('prior',FT('M','R'));q=V('encoder',FT('M',FT('W','R')));r=V('meaning_distribution',FT('M',FT('U','R')))
 triple=lambda mm,ww,uu:Mul(Mul(A(p,mm),A(q,mm,ww)),A(r,mm,uu))
 pw=lambda ww:sumv(ms,Lam(mi,Mul(A(p,mi),A(q,mi,ww))))
 pu=lambda uu:sumv(ms,Lam(mi,Mul(A(p,mi),A(r,mi,uu))))
 joint=lambda ww,uu:sumv(ms,Lam(mi,triple(mi,ww,uu)))
 decoder=lambda ww,uu:Div(joint(ww,uu),pw(ww))
 variables=(p,q,r,ms,ws,us)
 conditions=(All(m,Le(RZERO,A(p,m))),alls((m,w),Le(RZERO,A(q,m,w))),alls((m,u),Le(RZERO,A(r,m,u))),Eq(sumv(ms,p),RONE),All(m,Eq(sumv(ws,Lam(w,A(q,m,w))),RONE)),All(m,Eq(sumv(us,Lam(u,A(r,m,u))),RONE)),All(m,mem(m,ms)),All(w,mem(w,ws)),All(u,mem(u,us)))
 def prove(name,extra,extra_conditions,conclusion,proof):return theorem(k,name,variables+extra,conditions+extra_conditions,conclusion,proof)
 def use(name,*extra):return apply(ref(name,*(variables+extra)),*(hyp(c) for c in conditions))
 pp=instantiate(hyp(conditions[0]),m);qq=instantiate(hyp(conditions[1]),m,w);rrp=instantiate(hyp(conditions[2]),m,u)
 pq=apply(ax('nonnegative_product',A(p,m),A(q,m,w)),pp,qq)
 tnonneg=apply(ax('nonnegative_product',Mul(A(p,m),A(q,m,w)),A(r,m,u)),pq,rrp)
 prove('color_triple_nonnegative',(m,w,u),(),Le(RZERO,triple(m,w,u)),tnonneg)
 eq=ring(triple(m,w,u),Mul(Mul(A(p,m),A(r,m,u)),A(q,m,w)))
 eq=sum_equality(k,w,ws,eq)
 eq=trans(k,eq,instantiate(ref('sum_scale_W',Lam(w,A(q,m,w)),Mul(A(p,m),A(r,m,u))),ws))
 eq=rr(k,eq,instantiate(hyp(conditions[4]),m));eq=rr(k,eq,ring(Mul(Mul(A(p,m),A(r,m,u)),RONE),Mul(A(p,m),A(r,m,u))))
 prove('color_sum_encoder',(m,u),(),Eq(sumv(ws,Lam(w,triple(m,w,u))),Mul(A(p,m),A(r,m,u))),eq)
 eq=instantiate(ref('sum_scale_U',Lam(u,A(r,m,u)),Mul(A(p,m),A(q,m,w))),us)
 eq=rr(k,eq,instantiate(hyp(conditions[5]),m));eq=rr(k,eq,ring(Mul(Mul(A(p,m),A(q,m,w)),RONE),Mul(A(p,m),A(q,m,w))))
 prove('color_sum_meaning',(m,w),(),Eq(sumv(us,Lam(u,triple(m,w,u))),Mul(A(p,m),A(q,m,w))),eq)
 eq=sy(k,instantiate(ref('sum_fubini_MU',Lam(mi,Lam(ui,triple(mi,w,ui))),us),ms))
 eq=trans(k,eq,sum_equality(k,mi,ms,use('color_sum_meaning',mi,w)))
 prove('color_joint_word_marginal',(w,),(),Eq(sumv(us,Lam(u,joint(w,u))),pw(w)),eq)
 eq=sy(k,instantiate(ref('sum_fubini_MW',Lam(mi,Lam(wi,triple(mi,wi,u))),ws),ms))
 eq=trans(k,eq,sum_equality(k,mi,ms,use('color_sum_encoder',mi,u)))
 prove('color_joint_universe_marginal',(u,),(),Eq(sumv(ws,Lam(w,joint(w,u))),pu(u)),eq)
 eq=instantiate(ref('sum_scale_U',Lam(u,A(r,m,u)),A(p,m)),us);eq=rr(k,eq,instantiate(hyp(conditions[5]),m));eq=rr(k,eq,ring(Mul(A(p,m),RONE),A(p,m)))
 prove('color_source_marginal',(m,),(),Eq(sumv(us,Lam(u,Mul(A(p,m),A(r,m,u)))),A(p,m)),eq)
 qeq=instantiate(ref('sum_scale_W',Lam(w,A(q,m,w)),A(p,m)),ws);qeq=rr(k,qeq,instantiate(hyp(conditions[4]),m));qeq=rr(k,qeq,ring(Mul(A(p,m),RONE),A(p,m)))
 eq=sy(k,instantiate(ref('sum_fubini_MW',Lam(mi,Lam(wi,Mul(A(p,mi),A(q,mi,wi)))),ws),ms));eq=trans(k,eq,sum_equality(k,m,ms,qeq));eq=trans(k,eq,instantiate(apply(ref('sum_congr_M',Lam(m,A(p,m)),p),close(('eq_i',A(p,m)),(m,))),ms));eq=rr(k,eq,hyp(conditions[3]))
 prove('color_word_normalized',(),(),Eq(sumv(ws,Lam(w,pw(w))),RONE),eq)
 eq=sum_equality(k,w,ws,use('color_joint_word_marginal',w));eq=trans(k,eq,use('color_word_normalized'))
 prove('color_joint_normalized',(),(),Eq(sumv(ws,Lam(w,sumv(us,Lam(u,joint(w,u))))),RONE),eq)
 eq=sum_equality(k,m,ms,use('color_source_marginal',m));eq=trans(k,eq,instantiate(apply(ref('sum_congr_M',Lam(m,A(p,m)),p),close(('eq_i',A(p,m)),(m,))),ms));eq=rr(k,eq,hyp(conditions[3]))
 prove('color_source_normalized',(),(),Eq(sumv(ms,Lam(m,sumv(us,Lam(u,Mul(A(p,m),A(r,m,u)))))),RONE),eq)
 jnonneg=instantiate(apply(ref('sum_nonnegative_M',Lam(mi,triple(mi,w,u))),close(use('color_triple_nonnegative',mi,w,u),(mi,))),ms)
 prove('color_joint_nonnegative',(w,u),(),Le(RZERO,joint(w,u)),jnonneg)
 ppq=Mul(A(p,m),A(q,m,w));positive=Lt(RZERO,triple(m,w,u))
 factors=apply(ax('positive_product_factors',ppq,A(r,m,u)),pq,rrp,hyp(positive))
 ppos=('and_l',apply(ax('positive_product_factors',A(p,m),A(q,m,w)),pp,qq,('and_l',factors)))
 rpos=('and_r',factors)
 def member_bound(expr,nonnegative):
  return apply(instantiate(apply(ref('sum_member_bound_M',Lam(mi,expr),m),close(nonnegative,(mi,))),ms),instantiate(hyp(conditions[6]),m))
 jb=member_bound(triple(mi,w,u),use('color_triple_nonnegative',mi,w,u))
 jp=apply(ax('positive_le_transitive',triple(m,w,u),joint(w,u)),hyp(positive),jb)
 wb=member_bound(Mul(A(p,mi),A(q,mi,w)),apply(ax('nonnegative_product',A(p,mi),A(q,mi,w)),instantiate(hyp(conditions[0]),mi),instantiate(hyp(conditions[1]),mi,w)))
 wp=apply(ax('positive_le_transitive',ppq,pw(w)),('and_l',factors),wb)
 ub=member_bound(Mul(A(p,mi),A(r,mi,u)),apply(ax('nonnegative_product',A(p,mi),A(r,mi,u)),instantiate(hyp(conditions[0]),mi),instantiate(hyp(conditions[2]),mi,u)))
 up=apply(ax('positive_le_transitive',Mul(A(p,m),A(r,m,u)),pu(u)),apply(ax('positive_product',A(p,m),A(r,m,u)),ppos,rpos),ub)
 dp=apply(ax('positive_quotient',joint(w,u),pw(w)),jp,wp)
 support=('and_i',rpos,('and_i',dp,up))
 prove('color_positive_triple_support',(m,w,u),(positive,),And(Lt(RZERO,A(r,m,u)),And(Lt(RZERO,decoder(w,u)),Lt(RZERO,pu(u)))),support)
 split=apply(ref('zero_safe_weighted_log_split',triple(m,w,u),A(r,m,u),decoder(w,u),pu(u)),tnonneg,close(support,(),(positive,)))
 prove('color_weighted_log_split',(m,w,u),(),k.infer(split).conclusion,split)
 f=V('meaning_payoff',FT('M',FT('U','R')))
 inner=Mul(triple(m,w,u),A(f,m,u))
 eq=instantiate(ref('sum_fubini_WU',Lam(w,Lam(u,inner)),us),ws)
 agg=sum_right_scale(k,w,ws,triple(m,w,u),A(f,m,u));agg=rr(k,agg,use('color_sum_encoder',m,u))
 eq=trans(k,eq,sum_equality(k,u,us,agg));eq=sum_equality(k,m,ms,eq)
 prove('color_aggregate_meaning',(f,),(),k.infer(eq).conclusion,eq)
 g=V('word_payoff',FT('W',FT('U','R')));inner=Mul(triple(m,w,u),A(g,w,u))
 eq=instantiate(ref('sum_fubini_MW',Lam(m,Lam(w,sumv(us,Lam(u,inner)))),ws),ms)
 innereq=instantiate(ref('sum_fubini_MU',Lam(m,Lam(u,inner)),us),ms)
 agg=sum_right_scale(k,m,ms,triple(m,w,u),A(g,w,u))
 innereq=trans(k,innereq,sum_equality(k,u,us,agg));eq=trans(k,eq,sum_equality(k,w,ws,innereq))
 prove('color_aggregate_word',(g,),(),k.infer(eq).conclusion,eq)
 split=use('color_weighted_log_split',m,w,u)
 eq=sum_equality(k,u,us,split)
 fterm=Mul(triple(m,w,u),Log(Div(A(r,m,u),pu(u))));gterm=Mul(triple(m,w,u),Log(Div(decoder(w,u),pu(u))))
 eq=trans(k,eq,instantiate(ref('sum_sub_U',Lam(u,fterm),Lam(u,gterm)),us))
 eq=sum_equality(k,w,ws,eq);eq=trans(k,eq,instantiate(ref('sum_sub_W',Lam(w,sumv(us,Lam(u,fterm))),Lam(w,sumv(us,Lam(u,gterm)))),ws))
 eq=sum_equality(k,m,ms,eq);eq=trans(k,eq,instantiate(ref('sum_sub_M',Lam(m,sumv(ws,Lam(w,sumv(us,Lam(u,fterm))))),Lam(m,sumv(ws,Lam(w,sumv(us,Lam(u,gterm)))))),ms))
 eq=rr(k,eq,use('color_aggregate_meaning',Lam(m,Lam(u,Log(Div(A(r,m,u),pu(u)))))))
 eq=rr(k,eq,use('color_aggregate_word',Lam(w,Lam(u,Log(Div(decoder(w,u),pu(u)))))))
 prove('color_distortion_information_identity_natural',(),(),k.infer(eq).conclusion,eq)
 natural_equation=eq
 logtwo=Log(Add(RONE,RONE))
 natural_distortion,natural_difference=k.infer(eq).conclusion[1:]
 natural_source,natural_word=natural_difference[1][2],natural_difference[2]
 bit_equation=cong(k,eq,Lam(V('base_change','R'),Div(V('base_change','R'),logtwo)))
 bit_equation=trans(k,bit_equation,division_difference(k,natural_source,natural_word,logtwo))
 bit_equation=cn(k,bit_equation,Eq(Div(natural_distortion,logtwo),Sub(Div(natural_source,logtwo),Div(natural_word,logtwo))))
 prove('color_distortion_information_identity_bits',(),(),k.infer(bit_equation).conclusion,bit_equation)
 d_nonneg=apply(ax('nonnegative_quotient',joint(w,u),pw(w)),use('color_joint_nonnegative',w,u),hyp(Lt(RZERO,pw(w))))
 dsum=sum_division(k,u,us,joint(w,u),pw(w));dsum=rr(k,dsum,use('color_joint_word_marginal',w));dsum=trans(k,dsum,apply(ax('positive_division_self',pw(w)),hyp(Lt(RZERO,pw(w)))))
 prove('color_decoder_normalized',(w,),(Lt(RZERO,pw(w)),),And(All(u,Le(RZERO,decoder(w,u))),Eq(sumv(us,Lam(u,decoder(w,u))),RONE)),('and_i',close(d_nonneg,(u,)),dsum))
 bayes=sum_division(k,mi,ms,triple(mi,w,u),pw(w))
 term=weighted_division(k,A(r,mi,u),Mul(A(p,mi),A(q,mi,w)),pw(w))
 term=rr(k,term,ring(Mul(A(r,mi,u),Mul(A(p,mi),A(q,mi,w))),triple(mi,w,u)))
 termleft=Mul(Div(Mul(A(p,mi),A(q,mi,w)),pw(w)),A(r,mi,u))
 term=trans(k,ring(termleft,k.infer(term).conclusion[1]),term)
 bayes=trans(k,sum_equality(k,mi,ms,term),bayes)
 prove('color_bayesian_decoder',(w,u),(),Eq(decoder(w,u),sumv(ms,Lam(mi,termleft))),sy(k,bayes))
 zguard=C('zero_guard',FT('R',FT('R','R')))
 za,zb=V('guard_mass','R'),V('guard_value','R')
 if 'zero_guard_at_zero' not in k.axioms:
  add_axioms(k,{'zero_guard_at_zero':All(zb,Eq(A(zguard,RZERO,zb),RZERO)),'zero_guard_positive':alls((za,zb),Imp(Lt(RZERO,za),Eq(A(zguard,za,zb),zb)))})
 logterm=Log(Div(A(r,m,u),decoder(w,u)))
 unguarded=Mul(ppq,sumv(us,Lam(u,Mul(A(r,m,u),logterm))))
 guarded=A(zguard,ppq,unguarded)
 distexpand=sy(k,instantiate(ref('sum_scale_U',Lam(u,Mul(A(r,m,u),logterm)),ppq),us))
 innerring=sum_equality(k,u,us,ring(Mul(ppq,Mul(A(r,m,u),logterm)),Mul(triple(m,w,u),logterm)))
 distexpand=trans(k,distexpand,innerring)
 pzero=Eq(ppq,RZERO);ppositive=Lt(RZERO,ppq)
 zero_rhs=rewrite(k,('eq_i',unguarded),hyp(pzero));zero_rhs=rr(k,zero_rhs,ring(k.infer(zero_rhs).conclusion[2],RZERO))
 zero_left=ax('zero_guard_at_zero',substitute(unguarded,m,m))
 z=V('guard_replace','R')
 zero_left=('eq_e',sy(k,hyp(pzero)),z,Eq(A(zguard,z,unguarded),RZERO),zero_left)
 z_right=('eq_i',unguarded);z_right=rr(k,z_right,hyp(pzero));z_right=rr(k,z_right,ring(k.infer(z_right).conclusion[2],RZERO))
 zero_guard=trans(k,zero_left,sy(k,z_right))
 positive_guard=apply(ax('zero_guard_positive',ppq,unguarded),hyp(ppositive))
 guard_eq=('or_e',apply(ax('nonnegative_zero_or_positive',ppq),pq),zero_guard,positive_guard)
 expected=trans(k,guard_eq,distexpand);expected=sum_equality(k,w,ws,expected);expected=sum_equality(k,m,ms,expected)
 prove('color_expected_KL_equals_distortion_natural',(),(),k.infer(expected).conclusion,expected)
 expected=trans(k,expected,natural_equation)
 expected=cong(k,expected,Lam(V('expected_base','R'),Div(V('expected_base','R'),logtwo)))
 expected=trans(k,expected,division_difference(k,natural_source,natural_word,logtwo))
 prove('color_expected_KL_equals_information_loss_bits',(),(),k.infer(expected).conclusion,expected)
 wordratio=ax('quotient_quotient_total',joint(w,u),pw(w),pu(u))
 wordratio=cong(k,wordratio,Lam(V('log_argument','R'),Mul(joint(w,u),Log(V('log_argument','R')))))
 wordratio_point=wordratio
 wordratio=sum_equality(k,u,us,wordratio);wordratio=sum_equality(k,w,ws,wordratio)
 prove('color_word_information_is_MI_natural',(),(),k.infer(wordratio).conclusion,wordratio)
 wfull=wordratio_point
 wfull=rr(k,wfull,use('color_joint_word_marginal',w),True);wfull=rr(k,wfull,use('color_joint_universe_marginal',u),True)
 wfull=sum_equality(k,u,us,wfull);wfull=sum_equality(k,w,ws,wfull)
 prove('color_word_information_full_marginals_natural',(),(),k.infer(wfull).conclusion,wfull)
 sourceleft=Mul(Mul(A(p,m),A(r,m,u)),Log(Div(A(r,m,u),pu(u))))
 sourceright=Mul(Mul(A(p,m),A(r,m,u)),Log(Div(Mul(A(p,m),A(r,m,u)),Mul(A(p,m),pu(u)))))
 ppzero=Eq(A(p,m),RZERO);ppos=Lt(RZERO,A(p,m))
 zeroleft=('eq_i',sourceleft);zeroleft=rr(k,zeroleft,hyp(ppzero));zeroleft=rr(k,zeroleft,ring(k.infer(zeroleft).conclusion[2],RZERO))
 zeroright=('eq_i',sourceright);zeroright=rr(k,zeroright,hyp(ppzero));zeroright=rr(k,zeroright,ring(k.infer(zeroright).conclusion[2],RZERO))
 zeroproof=trans(k,zeroleft,sy(k,zeroright))
 cancel=apply(ax('quotient_product_cancel_positive',A(p,m),A(r,m,u),pu(u)),hyp(ppos))
 posproof=cong(k,sy(k,cancel),Lam(V('source_ratio','R'),Mul(Mul(A(p,m),A(r,m,u)),Log(V('source_ratio','R')))))
 sourceeq=('or_e',apply(ax('nonnegative_zero_or_positive',A(p,m)),pp),zeroproof,posproof)
 sourceeq_point=sourceeq
 sourceeq=sum_equality(k,u,us,sourceeq);sourceeq=sum_equality(k,m,ms,sourceeq)
 prove('color_source_information_is_MI_natural',(),(),k.infer(sourceeq).conclusion,sourceeq)
 sourceeq=rr(k,sourceeq_point,use('color_source_marginal',m),True)
 sourceeq=sum_equality(k,u,us,sourceeq);sourceeq=sum_equality(k,m,ms,sourceeq)
 prove('color_source_information_full_marginals_natural',(),(),k.infer(sourceeq).conclusion,sourceeq)

 return k

def derive_comparison(k):
 source,wa,wb,da,db=(V(n,'R') for n in ('fixed_source_information','word_information_a','word_information_b','distortion_a','distortion_b'))
 cond=(Eq(da,Sub(source,wa)),Eq(db,Sub(source,wb)))
 for name,order,axiomname in [('strict',Lt,'subtraction_order_reverse'),('weak',Le,'subtraction_weak_order_reverse')]:
  proof=ax(axiomname,wa,wb,source)
  proof=rewrite(k,proof,hyp(cond[0]),True);proof=rewrite(k,proof,hyp(cond[1]),True)
  theorem(k,'fixed_source_'+name+'_distortion_information_order',(source,wa,wb,da,db),cond,Iff(order(da,db),order(wb,wa)),proof)

def certificates():
 k=InformationKernel(field_axioms());add_axioms(k,{n:f for n,f in algebra_foundations().items() if n not in ANALYTIC_NAMES})
 for name in ANALYTIC_NAMES:k.theorem(name,algebra_foundations()[name],('analytic',name))
 derive_log_upper(k)
 for t in ('M','W','U'):derive_sums(k,t)
 for t,u in [('M','U'),('M','W'),('W','U')]:derive_fubini(k,t,u)
 derive_log_lower(k)
 derive_mutual_information(k)
 derive_log_split(k)
 derive_color(k)
 derive_comparison(k)
 return k


def interfaces():
 ms=V('meanings',list_sort('M'));ws=V('words',list_sort('W'));us=V('universe',list_sort('U'))
 m=V('meaning','M');w=V('word','W');u=V('item','U');mi=V('meaning_index','M');wi=V('word_index','W');ui=V('item_index','U')
 p=V('prior',FT('M','R'));q=V('encoder',FT('M',FT('W','R')));r=V('meaning_distribution',FT('M',FT('U','R')))
 variables=(p,q,r,ms,ws,us)
 conditions=(All(m,Le(RZERO,A(p,m))),alls((m,w),Le(RZERO,A(q,m,w))),alls((m,u),Le(RZERO,A(r,m,u))),Eq(sumv(ms,p),RONE),All(m,Eq(sumv(ws,Lam(w,A(q,m,w))),RONE)),All(m,Eq(sumv(us,Lam(u,A(r,m,u))),RONE)),All(m,mem(m,ms)),All(w,mem(w,ws)),All(u,mem(u,us)))
 triple=lambda mm,ww,uu:Mul(Mul(A(p,mm),A(q,mm,ww)),A(r,mm,uu))
 pw=lambda ww:sumv(ms,Lam(mi,Mul(A(p,mi),A(q,mi,ww))))
 pu=lambda uu:sumv(ms,Lam(mi,Mul(A(p,mi),A(r,mi,uu))))
 joint=lambda ww,uu:sumv(ms,Lam(mi,triple(mi,ww,uu)))
 decoder=lambda ww,uu:Div(joint(ww,uu),pw(ww))
 ln2=Log(Add(RONE,RONE))
 pair=Mul(A(p,m),A(q,m,w))
 inner=sumv(us,Lam(u,Mul(A(r,m,u),Log(Div(A(r,m,u),decoder(w,u))))))
 guard=A(C('zero_guard',FT('R',FT('R','R'))),pair,Mul(pair,inner))
 expected=Div(sumv(ms,Lam(m,sumv(ws,Lam(w,guard)))),ln2)
 source=Div(sumv(ms,Lam(m,sumv(us,Lam(u,Mul(Mul(A(p,m),A(r,m,u)),Log(Div(A(r,m,u),pu(u)))))))),ln2)
 word=Div(sumv(ws,Lam(w,sumv(us,Lam(u,Mul(joint(w,u),Log(Div(decoder(w,u),pu(u)))))))),ln2)
 expected_identity=alls(variables,imps(conditions,Eq(expected,Sub(source,word))))
 decoder_identity=alls(variables+(w,u),imps(conditions,Eq(decoder(w,u),sumv(ms,Lam(mi,Mul(Div(Mul(A(p,mi),A(q,mi,w)),pw(w)),A(r,mi,u)))))))
 xs=V('joint_rows',list_sort('M'));ys=V('joint_columns',list_sort('U'));i=V('joint_i','M');j=V('joint_j','U');iu=V('joint_u','U');im=V('joint_m','M');jointp=V('joint_distribution',FT('M',FT('U','R')))
 row=lambda x:sumv(ys,Lam(iu,A(jointp,x,iu)))
 col=lambda y:sumv(xs,Lam(im,A(jointp,im,y)))
 jc=(alls((i,j),Le(RZERO,A(jointp,i,j))),Eq(sumv(xs,Lam(i,row(i))),RONE),All(i,mem(i,xs)),All(j,mem(j,ys)))
 mutual=Div(sumv(xs,Lam(i,sumv(ys,Lam(j,Mul(A(jointp,i,j),Log(Div(A(jointp,i,j),Mul(row(i),col(j))))))))),ln2)
 conditional=Div(Sub(RZERO,sumv(xs,Lam(i,sumv(ys,Lam(j,Mul(A(jointp,i,j),Log(Div(A(jointp,i,j),row(i))))))))),ln2)
 marginal=Div(Sub(RZERO,sumv(ys,Lam(j,Mul(col(j),Log(col(j)))))),ln2)
 return {'color_expected_KL_equals_information_loss_bits':expected_identity,'color_bayesian_decoder':decoder_identity,'finite_joint_mutual_information_nonnegative':alls((jointp,xs,ys),imps(jc,Le(RZERO,mutual))),'finite_MI_entropy_identity':alls((jointp,xs,ys),imps(jc,Eq(mutual,Sub(marginal,conditional)))),'finite_conditioning_reduces_average_entropy':alls((jointp,xs,ys),imps(jc,Le(conditional,marginal)))}

def self_test(k):
 checks={}
 def check(name,condition):
  if not condition:raise ValueError(("closed certificate",name))
  checks[name]=True
 check('color_decoder_normalized', 'color_decoder_normalized' in k.verified and not k.verified['color_decoder_normalized'].assumptions)
 check('color_bayesian_decoder', 'color_bayesian_decoder' in k.verified and not k.verified['color_bayesian_decoder'].assumptions)
 check('color_positive_triple_support', 'color_positive_triple_support' in k.verified and not k.verified['color_positive_triple_support'].assumptions)
 check('color_expected_KL_equals_information_loss_bits', 'color_expected_KL_equals_information_loss_bits' in k.verified and not k.verified['color_expected_KL_equals_information_loss_bits'].assumptions)
 check('color_word_information_full_marginals_natural', 'color_word_information_full_marginals_natural' in k.verified and not k.verified['color_word_information_full_marginals_natural'].assumptions)
 check('color_source_information_full_marginals_natural', 'color_source_information_full_marginals_natural' in k.verified and not k.verified['color_source_information_full_marginals_natural'].assumptions)
 check('fixed_source_strict_distortion_information_order', 'fixed_source_strict_distortion_information_order' in k.verified and not k.verified['fixed_source_strict_distortion_information_order'].assumptions)
 check('fixed_source_weak_distortion_information_order', 'fixed_source_weak_distortion_information_order' in k.verified and not k.verified['fixed_source_weak_distortion_information_order'].assumptions)
 check('log_upper_bound', 'log_upper_bound' in k.verified and not k.verified['log_upper_bound'].assumptions)
 check('weighted_log_ratio_lower', 'weighted_log_ratio_lower' in k.verified and not k.verified['weighted_log_ratio_lower'].assumptions)
 check('finite_joint_mutual_information_nonnegative', 'finite_joint_mutual_information_nonnegative' in k.verified and not k.verified['finite_joint_mutual_information_nonnegative'].assumptions)
 check('finite_MI_entropy_identity', 'finite_MI_entropy_identity' in k.verified and not k.verified['finite_MI_entropy_identity'].assumptions)
 check('finite_conditioning_reduces_average_entropy', 'finite_conditioning_reduces_average_entropy' in k.verified and not k.verified['finite_conditioning_reduces_average_entropy'].assumptions)

 for name,formula in interfaces().items():
  checks[name]=same(k.verified[name].conclusion,formula)
  if not checks[name]:raise ValueError(('independent interface',name))
 for name in ('finite_joint_mutual_information_nonnegative','color_expected_KL_equals_information_loss_bits'):
  record=next(r for r in k.records if r[0]==name)
  formula=record[1]
  def replace_first_conclusion(t):
   if t[0] in ('all','imp'):return (t[0],t[1],replace_first_conclusion(t[2]))
   if t[0]=='eq':return Eq(t[1],RZERO)
   return Eq(RONE,RZERO)
  changed=replace_first_conclusion(formula)
  checks[name+'_false_target_rejected']=rejects(lambda:k.theorem(name+'_mutated',changed,record[2]))
 altered=dict(k.axioms)
 old=altered['sum_cons_M']
 def twice_head(t):
  if t[0]=='eq':
   left,right=t[1:]
   value=right[1][2]
   return Eq(left,Add(Add(value,value),right[2]))
  return (t[0],t[1],twice_head(t[2]))
 altered['sum_cons_M']=twice_head(old)
 replay=InformationKernel(altered)
 rejected=False
 for name,formula,proof in k.records:
  if rejects(lambda:replay.theorem(name,formula,proof)):
   rejected=True
   break
 checks['sum_recurrence_mutation_rejected']=rejected
 if not all(checks.values()):raise ValueError(checks)
 return checks

if __name__=='__main__':
 k=certificates()
 print(json.dumps({'backend':'Python/typed-natural-deduction','proved':list(k.verified),'checks':self_test(k),'analytic_foundations_verified':True,'passed':True,'foundational_axioms':list(k.axioms)}))
 raise SystemExit(0)
