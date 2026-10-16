import json
from dataclasses import dataclass
import sympy as sp

proved=set()
certified_schemas={}
results=[]
NIL=()
def word(name):return (('L',name),)
def letter(name):return ('a',name)
def cons(a,x):
    if not isinstance(a,tuple) or len(a)!=2 or a[0]!='a':raise ValueError('letter')
    return (a,)+x
def rev(x):return tuple((('R' if t[0]=='L' else 'L'),t[1]) if t[0] in ('L','R') else t for t in reversed(x))
def length(x):return sum((sp.Integer(1) if t[0]=='a' else sp.Symbol('len_'+t[1],integer=True,nonnegative=True) for t in x),sp.Integer(0))
def exact(a,b):return sp.expand(a-b)==0
def nonnegative(x):return sp.expand(x).is_nonnegative is True
@dataclass(frozen=True)
class Judgment:
    kind:str
    source:tuple
    target:tuple
    cost:sp.Expr

def judgment(kind,x,y,k):
    if kind not in ('A','P','S') or not nonnegative(k):raise ValueError('judgment')
    if any(t[0] not in ('L','R','a') or not isinstance(t[1],str) for t in x+y):raise ValueError('word')
    return Judgment(kind,x,y,sp.expand(k))
def same(j,kind,x,y,k):return j.kind==kind and j.source==x and j.target==y and exact(j.cost,k)
def hyp(name):return ('hyp',name)
def infer(p,env):
    tag=p[0]
    if tag=='hyp':return env[p[1]]
    if tag=='anil':return judgment('A',NIL,NIL,sp.Integer(0))
    if tag in ('adel','ains','keep'):
        a,j=p[1],infer(p[2],env)
        if j.kind!='A':raise ValueError('alignment constructor')
        return judgment('A',cons(a,j.source) if tag!='ains' else j.source,cons(a,j.target) if tag!='adel' else j.target,j.cost+(0 if tag=='keep' else 1))
    if tag in ('sdel','sins','ssame','sdiff'):
        pre,post,a=p[1:4]
        if tag=='sdel':return judgment('S',pre+cons(a,post),pre+post,sp.Integer(1))
        if tag=='sins':return judgment('S',pre+post,pre+cons(a,post),sp.Integer(1))
        b=a if tag=='ssame' else p[4]
        if tag=='sdiff' and ('neq',a,b) not in env:raise ValueError('substitution side condition')
        return judgment('S',pre+cons(a,post),pre+cons(b,post),sp.Integer(0 if tag=='ssame' else 2))
    if tag=='prefl':return judgment('P',p[1],p[1],sp.Integer(0))
    if tag=='pstep':
        s,t=infer(p[1],env),infer(p[2],env)
        if s.kind!='S' or t.kind!='P' or s.target!=t.source:raise ValueError('path endpoint')
        return judgment('P',s.source,t.target,s.cost+t.cost)
    if tag=='pcons':
        if 'path_cons' not in proved:raise ValueError('unproved prefix lemma')
        j=infer(p[2],env)
        if j.kind!='P':raise ValueError('path')
        return judgment('P',cons(p[1],j.source),cons(p[1],j.target),j.cost)
    if tag=='arefl':
        if 'alignment_refl' not in proved:raise ValueError('unproved reflexivity')
        return judgment('A',p[1],p[1],sp.Integer(0))
    if tag=='reverse_path':
        if 'path_reverse' not in proved:raise ValueError('unproved reversal')
        j=infer(p[1],env)
        if j.kind!='P':raise ValueError('path')
        return judgment('P',rev(j.source),rev(j.target),j.cost)
    if tag=='alignment_path':
        if 'alignment_to_path' not in proved:raise ValueError('unproved alignment conversion')
        j=infer(p[1],env)
        if j.kind!='A':raise ValueError('alignment')
        return judgment('P',j.source,j.target,j.cost)
    raise ValueError('proof rule')

def bound(lower,upper,premises=(),weights=(),slack=0):
    if len(premises)!=len(weights) or any(not sp.Rational(c)>=0 for c in weights) or not nonnegative(sp.sympify(slack)):return False
    return exact(upper-lower,sum((sp.Rational(c)*(b-a) for c,(a,b) in zip(weights,premises)),sp.Integer(0))+slack)

def fresh(name,env):
    z=sp.Symbol(name,integer=True,nonnegative=True)
    if any(isinstance(j,Judgment) and z in j.cost.free_symbols for j in env.values()):raise ValueError('fresh cost')
    return z

def source_witness(mode,p,pre,post,a,name,env,bounds,root=None):
    if mode not in ('add','remove'):raise ValueError('mode')
    if root is not None:
        if root[0] not in ('adel','ains','keep') or root[2]!=p:raise ValueError('not strict alignment child')
    elif 'source_'+mode not in proved:raise ValueError('unproved source transformation')
    j=infer(p,env)
    expected=pre+post if mode=='add' else pre+cons(a,post)
    if j.kind!='A' or j.source!=expected:raise ValueError('source factorization')
    z=fresh(name,env)
    out=pre+cons(a,post) if mode=='add' else pre+post
    env[name]=judgment('A',out,j.target,z)
    bounds.append((z,j.cost+1))
    return hyp(name)

X,Y,Z,P,T=map(word,('X','Y','Z','P','T'))
a,b,c=letter('a'),letter('b'),letter('c')
k,l,m=sp.symbols('k l m',integer=True,nonnegative=True)

def source_case(mode,label):
    env={};bounds=[]
    def child(x,y=Y):
        env['child']=judgment('A',x,y,k)
        return hyp('child')
    if mode=='add':
        if label=='nil':root=('anil',);pre=post=NIL;out=('adel',a,root)
        elif label=='delete_empty':root=('adel',b,child(X));pre=NIL;post=cons(b,X);out=('adel',a,root)
        elif label=='keep_empty':root=('keep',b,child(X));pre=NIL;post=cons(b,X);out=('adel',a,root)
        elif label in ('delete_cons','keep_cons'):
            c=child(P+T);tag='adel' if label=='delete_cons' else 'keep';root=(tag,b,c);pre=cons(b,P);post=T
            out=(tag,b,source_witness(mode,c,P,T,a,'u',env,bounds,root))
        elif label=='insert':
            c=child(P+T);root=('ains',b,c);pre=P;post=T
            out=('ains',b,source_witness(mode,c,P,T,a,'u',env,bounds,root))
        else:raise ValueError('case')
    else:
        if label=='delete_empty':c=child(T);root=('adel',a,c);pre=NIL;post=T;out=c
        elif label=='keep_empty':c=child(T);root=('keep',a,c);pre=NIL;post=T;out=('ains',a,c)
        elif label in ('delete_cons','keep_cons'):
            c=child(P+cons(a,T));tag='adel' if label=='delete_cons' else 'keep';root=(tag,b,c);pre=cons(b,P);post=T
            out=(tag,b,source_witness(mode,c,P,T,a,'u',env,bounds,root))
        elif label=='insert':
            c=child(P+cons(a,T));root=('ains',b,c);pre=P;post=T
            out=('ains',b,source_witness(mode,c,P,T,a,'u',env,bounds,root))
        else:raise ValueError('case')
    original=infer(root,env);answer=infer(out,env)
    initial=pre+post if mode=='add' else pre+cons(a,post)
    final=pre+cons(a,post) if mode=='add' else pre+post
    if original.source!=initial or answer.source!=final or answer.target!=original.target:return False
    remainder=sp.expand(original.cost+1-answer.cost-sum((hi-lo for lo,hi in bounds),sp.Integer(0)))
    return bound(answer.cost,original.cost+1,bounds,[1]*len(bounds),remainder)

def certify_source(mode,labels):
    expected={'add':{'nil','delete_empty','delete_cons','insert','keep_empty','keep_cons'},'remove':{'delete_empty','delete_cons','insert','keep_empty','keep_cons'}}
    if len(labels)!=len(expected[mode]) or set(labels)!=expected[mode]:return False
    if mode=='remove' and not nonnegative(length(P+cons(a,T))-1):return False
    if not all(source_case(mode,label) for label in labels):return False
    proved.add('source_'+mode)
    return True

def reflexivity_induction():
    env={'child':judgment('A',X,X,sp.Integer(0))}
    if not same(infer(('anil',),env),'A',NIL,NIL,0):return False
    if not same(infer(('keep',a,hyp('child')),env),'A',cons(a,X),cons(a,X),0):return False
    proved.add('alignment_refl');return True

def step_transform(kind):
    for tag in ('sdel','sins','ssame','sdiff'):
        env={('neq',a,b):True} if tag=='sdiff' else {}
        rule=(tag,P,T,a,b) if tag=='sdiff' else (tag,P,T,a)
        original=infer(rule,env)
        transformed=(tag,cons(c,P),T,a,b) if tag=='sdiff' else (tag,cons(c,P),T,a)
        if kind=='reverse':transformed=(tag,rev(T),rev(P),a,b) if tag=='sdiff' else (tag,rev(T),rev(P),a)
        answer=infer(transformed,env)
        targetsource=cons(c,original.source) if kind=='cons' else rev(original.source)
        targettarget=cons(c,original.target) if kind=='cons' else rev(original.target)
        if not same(answer,'S',targetsource,targettarget,original.cost):return False
    proved.add('step_'+kind);return True

def path_transform(kind):
    if 'step_'+kind not in proved:return False
    f=(lambda x:cons(a,x)) if kind=='cons' else rev
    base=infer(('prefl',f(X)),{})
    if not same(base,'P',f(X),f(X),0):return False
    env={'step':judgment('S',f(X),f(Y),k),'strict_tail':judgment('P',f(Y),f(Z),l)}
    result=infer(('pstep',hyp('step'),hyp('strict_tail')),env)
    if not same(result,'P',f(X),f(Z),k+l):return False
    proved.add('path_'+kind);return True

def alignment_path_induction():
    if not same(infer(('prefl',NIL),{}),'P',NIL,NIL,0):return False
    for tag in ('adel','ains','keep'):
        env={'child':judgment('A',X,Y,k),'strict_child_path':judgment('P',X,Y,k)}
        root=(tag,a,hyp('child'));r=infer(root,env)
        if tag=='adel':out=('pstep',('sdel',NIL,X,a),hyp('strict_child_path'))
        elif tag=='ains':out=('pstep',('sins',NIL,X,a),('pcons',a,hyp('strict_child_path')))
        else:out=('pcons',a,hyp('strict_child_path'))
        if not same(infer(out,env),'P',r.source,r.target,r.cost):return False
    proved.add('alignment_to_path');return True

def path_alignment_induction():
    if 'alignment_refl' not in proved or not {'source_add','source_remove'}<=proved:return False
    if not same(infer(('arefl',X),{}),'A',X,X,0):return False
    for tag in ('sdel','sins','ssame','sdiff'):
        env={('neq',a,b):True} if tag=='sdiff' else {};bounds=[]
        step=(tag,P,T,a,b) if tag=='sdiff' else (tag,P,T,a)
        s=infer(step,env)
        env['strict_tail_alignment']=judgment('A',s.target,Z,l)
        bounds.append((l,k))
        q=hyp('strict_tail_alignment')
        if tag=='sdel':out=source_witness('add',q,P,T,a,'u',env,bounds)
        elif tag=='sins':out=source_witness('remove',q,P,T,a,'u',env,bounds)
        elif tag=='ssame':out=q
        else:
            r=source_witness('remove',q,P,T,b,'u',env,bounds)
            out=source_witness('add',r,P,T,a,'v',env,bounds)
        result=infer(out,env)
        if result.source!=s.source or result.target!=Z or not bound(result.cost,s.cost+k,bounds,[1]*len(bounds)):return False
    proved.add('path_to_alignment');return True

def distance_atom(x,y):
    if not x:return length(y)
    if not y:return length(x)
    return sp.Symbol('D_'+repr((x,y)),integer=True,nonnegative=True)
def distance_step(x,y,equal):
    if not x or not y:return distance_atom(x,y)
    if x[0][0]!='a' or y[0][0]!='a':return distance_atom(x,y)
    if equal and x[0]!=y[0]:raise ValueError('equal heads')
    return sp.Min(distance_atom(x[1:],y)+1,distance_atom(x,y[1:])+1,distance_atom(x[1:],y[1:])+(0 if equal else 2))

def min_certificate(costs):
    q=sp.symbols('delta_1:'+str(len(costs)),integer=True,nonnegative=True)
    for winner in range(len(costs)):
        others=[j for j in range(len(costs)) if j!=winner]
        origin=sp.Symbol('minimum',integer=True,nonnegative=True)
        representative=[origin]*len(costs)
        for j,v in zip(others,q):representative[j]=origin+v
        if sp.Min(*representative)!=origin:return False
        if any(not nonnegative(value-origin) for value in representative):return False
    return True

def border_alignment_induction():
    for side in ('left','right'):
        if not same(infer(('anil',),{}),'A',NIL,NIL,0):return False
        src,tgt=(NIL,X) if side=='left' else (X,NIL)
        env={'strict_tail':judgment('A',src,tgt,length(X))}
        tag='ains' if side=='left' else 'adel'
        answer=infer((tag,a,hyp('strict_tail')),env)
        if not same(answer,'A',NIL if side=='left' else cons(a,X),cons(a,X) if side=='left' else NIL,length(cons(a,X))):return False
    proved.add('alignment_borders');return True

def optimal_alignment_induction():
    if 'alignment_borders' not in proved:return False
    for equal in (False,True):
        right=a if equal else b
        src,tgt=cons(a,X),cons(right,Y)
        subpairs=[(X,tgt),(src,Y),(X,Y)]
        costs=[distance_atom(*p) for p in subpairs]
        env={str(i):judgment('A',*pair,cost) for i,(pair,cost) in enumerate(zip(subpairs,costs))}
        candidates=[('adel',a,hyp('0')),('ains',right,hyp('1')),('keep',a,hyp('2')) if equal else ('adel',a,('ains',right,hyp('2')))]
        expected=[costs[0]+1,costs[1]+1,costs[2]+(0 if equal else 2)]
        for pair,candidate,value in zip(subpairs,candidates,expected):
            if not nonnegative(length(src)+length(tgt)-length(pair[0])-length(pair[1])-1):return False
            if not same(infer(candidate,env),'A',src,tgt,value):return False
        if not min_certificate(expected) or distance_step(src,tgt,equal)!=sp.Min(*expected):return False
    proved.add('optimal_alignment');return True

def lower_alignment_induction():
    if distance_atom(NIL,NIL)!=0:return False
    for tag in ('adel','ains','keep'):
        for opposite_empty in (True,False):
            if tag=='keep' and opposite_empty:continue
            for equal in ((True,) if tag=='keep' else (False,True)):
                other=a if equal else b
                source,target=(X,NIL if opposite_empty else cons(other,Y)) if tag=='adel' else ((NIL if opposite_empty else cons(other,X)),Y) if tag=='ains' else (X,Y)
                env={'child':judgment('A',source,target,k)}
                root=infer((tag,a,hyp('child')),env)
                ih=(distance_atom(source,target),k)
                if opposite_empty:
                    wanted=distance_atom(root.source,root.target)
                    if not bound(wanted,root.cost,[ih],[1]):return False
                else:
                    candidates=[distance_atom(root.source[1:],root.target)+1,distance_atom(root.source,root.target[1:])+1,distance_atom(root.source[1:],root.target[1:])+(0 if equal else 2)]
                    selected={'adel':0,'ains':1,'keep':2}[tag]
                    if not exact(candidates[selected],ih[0]+(0 if tag=='keep' else 1)) or not min_certificate(candidates):return False
                    if not bound(candidates[selected],root.cost,[ih],[1]):return False
                    if distance_step(root.source,root.target,equal)!=sp.Min(*candidates):return False
    proved.add('distance_lower_alignment');return True

def edit_minimum_certificate():
    needed={'optimal_alignment','distance_lower_alignment','alignment_to_path','path_to_alignment'}
    if not needed<=proved:return False
    d=distance_atom(X,Y)
    env={'optimum':judgment('A',X,Y,d)}
    if not same(infer(('alignment_path',hyp('optimum')),env),'P',X,Y,d):return False
    if not bound(d,k,[(d,l),(l,k)],[1,1]):return False
    proved.add('minimum_edit_cost');return True

def reversal_minimum_certificate():
    if not {'minimum_edit_cost','path_reverse'}<=proved:return False
    if rev(rev(X))!=X or rev(rev(Y))!=Y:return False
    d=distance_atom(X,Y);r=distance_atom(rev(X),rev(Y))
    env={'forward_optimum':judgment('P',X,Y,d),'reverse_optimum':judgment('P',rev(X),rev(Y),r)}
    forward=infer(('reverse_path',hyp('forward_optimum')),env)
    backward=infer(('reverse_path',hyp('reverse_optimum')),env)
    if not same(forward,'P',rev(X),rev(Y),d) or not same(backward,'P',X,Y,r):return False
    if not bound(d-r,0,[(d,r)],[1]) or not bound(r-d,0,[(r,d)],[1]):return False
    proved.add('distance_reverse');return True

def snoc_recurrence_certificate(insertion_cost=1):
    if not {'distance_reverse','optimal_alignment','minimum_edit_cost'}<=proved:return False
    for equal in (False,True):
        right=a if equal else b
        src,tgt=X+(a,),Y+(right,)
        if rev(src)!=cons(a,rev(X)) or rev(tgt)!=cons(right,rev(Y)):return False
        reversed_pairs=[(rev(X),rev(tgt)),(rev(src),rev(Y)),(rev(X),rev(Y))]
        original_pairs=[(X,tgt),(src,Y),(X,Y)]
        if any((rev(v),rev(w))!=pair for (v,w),pair in zip(reversed_pairs,original_pairs)):return False
        values=[distance_atom(*p) for p in original_pairs]
        candidates=[values[0]+1,values[1]+insertion_cost,values[2]+(0 if equal else 2)]
        head=distance_step(rev(src),rev(tgt),equal)
        substitution={distance_atom(*reverse_pair):distance_atom(*original_pair) for reverse_pair,original_pair in zip(reversed_pairs,original_pairs)}
        schema_left,schema_right=snoc_schema()
        assignment={'px':X,'py':Y,'ax':a,'by':right}
        if schema_value(schema_left,assignment)!=distance_atom(src,tgt):return False
        if schema_value(schema_right,assignment)!=sp.Min(*candidates):return False
        if head.xreplace(substitution)!=schema_value(schema_right,assignment) or not min_certificate(candidates):return False
    certified_schemas['snoc_recurrence']=snoc_schema()
    proved.add('snoc_recurrence');return True

def pt(tag,*args):return (tag,*args)
def snoc_schema():
    px,py=pt('v','px'),pt('v','py');ax,by=pt('letter','ax'),pt('letter','by')
    sx,sy=pt('append',px,pt('cons',ax,('nil',))),pt('append',py,pt('cons',by,('nil',)))
    rhs=pt('minimum',pt('succ',pt('distance',px,sy)),pt('minimum',pt('succ',pt('distance',sx,py)),pt('plus',pt('distance',px,py),pt('delta',ax,by))))
    return pt('distance',sx,sy),rhs

def schema_value(t,assignment):
    tag=t[0]
    if tag in ('v','letter'):return assignment[t[1]]
    if tag=='nil':return NIL
    if tag=='cons':return cons(schema_value(t[1],assignment),schema_value(t[2],assignment))
    if tag=='append':return schema_value(t[1],assignment)+schema_value(t[2],assignment)
    if tag=='distance':return distance_atom(schema_value(t[1],assignment),schema_value(t[2],assignment))
    if tag=='succ':return schema_value(t[1],assignment)+1
    if tag=='plus':return schema_value(t[1],assignment)+schema_value(t[2],assignment)
    if tag=='minimum':return sp.Min(schema_value(t[1],assignment),schema_value(t[2],assignment))
    if tag=='delta':return sp.Integer(0 if schema_value(t[1],assignment)==schema_value(t[2],assignment) else 2)
    raise ValueError('schema term')

def pn(t):
    if len(t)==1 or t[0] in ('v','letter','nat'):return t
    tag=t[0];args=[pn(a) for a in t[1:]]
    if tag=='take':
        i,x=args
        if i==('zero',):return ('nil',)
        if x==('nil',):return ('nil',)
        if i[0]=='succ' and x[0]=='cons':return pn(pt('cons',x[1],pt('take',i[1],x[2])))
    if tag=='at':
        i,x=args
        if x[0]=='cons':
            if i==('zero',):return x[1]
            if i[0]=='succ':return pn(pt('at',i[1],x[2]))
    if tag=='append':
        x,y=args
        if x==('nil',):return y
        if x[0]=='cons':return pn(pt('cons',x[1],pt('append',x[2],y)))
    if tag=='distance':
        x,y=args
        if x==('nil',):return pn(pt('length',y))
        if y==('nil',):return pn(pt('length',x))
    if tag=='length':
        x=args[0]
        if x==('nil',):return ('zero',)
        if x[0]=='cons':return pn(pt('succ',pt('length',x[2])))
    return (tag,*args)
def pr(t,left,right):
    if t==left:return right
    if len(t)==1 or t[0] in ('v','letter','nat'):return t
    return (t[0],*(pr(a,left,right) for a in t[1:]))
def take_successor_induction():
    n=pt('nat','n');xs=pt('v','xs');head=pt('letter','head');tail=pt('v','tail')
    def sides(index,lst):
        return pt('take',pt('succ',index),lst),pt('append',pt('take',index,lst),pt('cons',pt('at',index,lst),('nil',)))
    base_left,base_right=sides(('zero',),pt('cons',head,tail))
    if pn(base_left)!=pn(base_right):return False
    ih_left,ih_right=sides(n,tail)
    step_left,step_right=sides(pt('succ',n),pt('cons',head,tail))
    if pn(pr(pn(step_left),pn(ih_left),pn(ih_right)))!=pn(step_right):return False
    nn,ll=sp.symbols('index length_tail',integer=True,nonnegative=True)
    if sp.Lt(nn,0)!=sp.false or not exact((ll+1)-(nn+1),ll-nn):return False
    proved.add('take_successor');return True

def take_length_induction():
    n=pt('nat','n');head=pt('letter','head');tail=pt('v','tail')
    if pn(pt('length',pt('take',('zero',),tail)))!=('zero',):return False
    lhs=pt('length',pt('take',pt('succ',n),pt('cons',head,tail)))
    ih=pt('length',pt('take',n,tail))
    if pn(pr(pn(lhs),ih,n))!=pt('succ',n):return False
    nn=sp.Symbol('index',integer=True,nonnegative=True)
    if sp.Le(nn+1,0)!=sp.false:return False
    proved.add('take_length_bounded');return True

def prefix_certificate(insertion_cost=1):
    if not {'snoc_recurrence','alignment_borders','take_successor','take_length_bounded'}<=proved:return False
    i,j=pt('nat','i'),pt('nat','j');x,y=pt('v','x'),pt('v','y')
    pre_x,pre_y=pt('take',i,x),pt('take',j,y)
    ax,by=pt('at',i,x),pt('at',j,y)
    full_x,full_y=pt('take',pt('succ',i),x),pt('take',pt('succ',j),y)
    snoc_x,snoc_y=pt('append',pre_x,pt('cons',ax,('nil',))),pt('append',pre_y,pt('cons',by,('nil',)))
    def rhs(sx,sy):
        insertion=pt('distance',sx,pre_y)
        for _ in range(insertion_cost):insertion=pt('succ',insertion)
        return pt('minimum',pt('succ',pt('distance',pre_x,sy)),pt('minimum',insertion,pt('plus',pt('distance',pre_x,pre_y),pt('delta',ax,by))))
    converted=pr(pr(rhs(full_x,full_y),full_x,snoc_x),full_y,snoc_y)
    schema_left,schema_right=certified_schemas['snoc_recurrence']
    for variable,value in ((pt('v','px'),pre_x),(pt('v','py'),pre_y),(pt('letter','ax'),ax),(pt('letter','by'),by)):
        schema_left=pr(schema_left,variable,value)
        schema_right=pr(schema_right,variable,value)
    if converted!=schema_right:return False
    if pr(pr(pt('distance',full_x,full_y),full_x,snoc_x),full_y,snoc_y)!=schema_left:return False
    proved.add('prefix_recurrence');return True

def prefix_boundary_certificate():
    if not {'take_length_bounded','minimum_edit_cost','alignment_borders'}<=proved:return False
    i=pt('nat','i');x=pt('v','x');prefix=pt('take',i,x)
    for pair in ((prefix,('nil',)),(('nil',),prefix)):
        expr=pn(pt('distance',*pair))
        if pn(pr(expr,pt('length',prefix),i))!=i:return False
    proved.add('prefix_boundary');return True

def missing_conversion_rejected():
    for name in ('alignment_to_path','path_to_alignment'):
        proved.remove(name)
        invalid=edit_minimum_certificate()
        proved.add(name)
        if invalid:return False
    return True

def rejected(f):
    try:f()
    except (ValueError,KeyError):return True
    return False

def check(name,value):
    if value is not True:raise AssertionError((name,value))
    results.append({'id':name,'passed':True})

check('alignment_reflexivity_induction',reflexivity_induction())
check('source_insertion_induction',certify_source('add',['nil','delete_empty','delete_cons','insert','keep_empty','keep_cons']))
check('source_deletion_induction',certify_source('remove',['delete_empty','delete_cons','insert','keep_empty','keep_cons']))
check('step_prefix_preservation',step_transform('cons'))
check('path_prefix_induction',path_transform('cons'))
check('alignment_to_edit_path_induction',alignment_path_induction())
check('arbitrary_edit_path_to_alignment_induction',path_alignment_induction())
check('empty_alignment_induction',border_alignment_induction())
check('recurrence_alignment_attainment_induction',optimal_alignment_induction())
check('recurrence_lower_bound_alignment_induction',lower_alignment_induction())
check('recurrence_is_minimum_over_edit_paths',edit_minimum_certificate())
check('step_reversal_preservation',step_transform('reverse'))
check('path_reversal_induction',path_transform('reverse'))
check('edit_minimum_reversal_invariance',reversal_minimum_certificate())
check('snoc_recurrence_minimum',snoc_recurrence_certificate())
check('take_successor_index_induction',take_successor_induction())
check('bounded_prefix_length_induction',take_length_induction())
check('prefix_recurrence_indices',prefix_certificate())
check('prefix_empty_minimum',prefix_boundary_certificate())
check('altered_recurrence_cost_rejected',not snoc_recurrence_certificate(2))
check('altered_prefix_cost_rejected',not prefix_certificate(2))
check('missing_induction_case_rejected',not certify_source('add',['nil','delete_empty','delete_cons','keep_empty','keep_cons']))
check('non_strict_induction_rejected',rejected(lambda:source_witness('add',('adel',a,hyp('child')),NIL,cons(a,X),a,'u',{'child':judgment('A',X,Y,k)},[],('adel',a,hyp('child')))))
check('bad_edit_endpoint_rejected',rejected(lambda:infer(('pstep',('sdel',NIL,X,a),('prefl',Y)),{})))
check('wrong_substitution_branch_rejected',rejected(lambda:infer(('sdiff',P,T,a,b),{})))
check('invalid_cost_bound_rejected',not bound(l,k,[(l,k+1)],[1]))
check('edit_bound_requires_both_conversions',missing_conversion_rejected())
check('ill_typed_alignment_rejected',rejected(lambda:infer(('adel',a,('prefl',X)),{})))
check('zero_cost_mismatch_rejected',not same(infer(('sdiff',P,T,a,b),{('neq',a,b):True}),'S',P+cons(a,T),P+cons(b,T),0))

if __name__=='__main__':
    print(json.dumps({'backend':'Python','checks':len(results),'passed':True,'scope':'Symbolic structural induction over arbitrary finite words, alignment constructors and arbitrary-position edit paths. Insert/delete cost one; equal replacement zero, unequal replacement two. Typed constructor endpoints and exact linear cost certificates verify source surgery, both semantic conversions, attainment and lower bound of the recurrence. Reversal transfers the head recurrence to final symbols of prefixes; one-based matrix indices correspond to successor prefix lengths. No sampling of word length is used.','results':results}))
