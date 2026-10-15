import json
from dataclasses import dataclass
from itertools import product
import sympy as sp
import dinamica as D

proved=set()
certified_values={}
results=[]
@dataclass(frozen=True)
class UnitJudgment:
    kind:str
    source:tuple
    target:tuple
    cost:sp.Expr
    gaps:sp.Expr

def unit_judgment(kind,x,y,k,g):
    if kind not in ('S','P') or not D.nonnegative(k) or not D.nonnegative(g):raise ValueError('unit judgment')
    D.judgment(kind,x,y,k)
    return UnitJudgment(kind,x,y,sp.expand(k),sp.expand(g))
def unit_same(j,kind,x,y,k,g):return j.kind==kind and j.source==x and j.target==y and D.exact(j.cost,k) and D.exact(j.gaps,g)
def unit_infer(p,env):
    tag=p[0]
    if tag=='hyp':return env[p[1]]
    if tag in ('sdel','sins','ssame','sdiff'):
        doubled=D.infer(p,env)
        cost=0 if tag=='ssame' else 1
        gaps=1 if tag in ('sdel','sins') else 0
        return unit_judgment('S',doubled.source,doubled.target,sp.Integer(cost),sp.Integer(gaps))
    if tag=='prefl':return unit_judgment('P',p[1],p[1],sp.Integer(0),sp.Integer(0))
    if tag=='pstep':
        first,tail=unit_infer(p[1],env),unit_infer(p[2],env)
        if first.kind!='S' or tail.kind!='P' or first.target!=tail.source:raise ValueError('unit path endpoint')
        return unit_judgment('P',first.source,tail.target,first.cost+tail.cost,first.gaps+tail.gaps)
    raise ValueError('unit proof rule')

A,B,C,E=map(D.letter,('a','b','c','e'))
P,T,X,Y,Z=map(D.word,('P','T','X','Y','Z'))
c,k,g,e,r,s=sp.symbols('c k g e r s',integer=True,nonnegative=True)

def lift_step_certificate(factor=2,include_gaps=True):
    for tag in ('sdel','sins','ssame','sdiff'):
        env={('neq',A,B):True} if tag=='sdiff' else {}
        proof=(tag,P,T,A,B) if tag=='sdiff' else (tag,P,T,A)
        original=unit_infer(proof,env)
        lifted=D.infer(proof,env)
        if original.source!=lifted.source or original.target!=lifted.target:return False
        if not D.exact(lifted.cost+(original.gaps if include_gaps else 0),factor*original.cost):return False
    proved.add('lift_step');return True

def lift_path_induction():
    if 'lift_step' not in proved:return False
    base=unit_infer(('prefl',X),{})
    lifted=D.infer(('prefl',X),{})
    if not D.exact(lifted.cost+base.gaps,2*base.cost):return False
    original_env={'step':unit_judgment('S',X,Y,c,g),'strict_tail':unit_judgment('P',Y,Z,k,e)}
    original=unit_infer(('pstep',D.hyp('step'),D.hyp('strict_tail')),original_env)
    lifted_env={'step':D.judgment('S',X,Y,r),'strict_tail':D.judgment('P',Y,Z,s)}
    lifted=D.infer(('pstep',D.hyp('step'),D.hyp('strict_tail')),lifted_env)
    if original.source!=lifted.source or original.target!=lifted.target:return False
    premise_step=r+g-2*c
    premise_tail=s+e-2*k
    if not D.exact(lifted.cost+original.gaps-2*original.cost,premise_step+premise_tail):return False
    proved.add('lift_path');return True

def mismatch(a,b):
    if a==b:return sp.Integer(0)
    return sp.Symbol('mismatch_'+repr((a,b)),integer=True,nonnegative=True)
def hamming_atom(x,y):
    if not x or not y:return sp.Integer(0)
    return sp.Symbol('hamming_'+repr((x,y)),integer=True,nonnegative=True)
def hamming_step(x,y):
    if not x or not y:return sp.Integer(0)
    if x[0][0]=='a' and y[0][0]=='a':return mismatch(x[0],y[0])+hamming_atom(x[1:],y[1:])
    return hamming_atom(x,y)
def equality_partitions():return [(0,0,0),(0,0,1),(0,1,0),(0,1,1),(0,1,2)]
def mismatch_triangle_certificate(partitions=None):
    if partitions is None:partitions=equality_partitions()
    consistent={(ab,bc,ac) for ab,bc,ac in product((False,True),repeat=3) if (not (ab and bc) or ac) and (not (ab and ac) or bc) and (not (ac and bc) or ab)}
    represented={(a==b,b==c,a==c) for a,b,c in partitions}
    if represented!=consistent:return False
    for a,b,c0 in partitions:
        if int(a!=c0)>int(a!=b)+int(b!=c0):return False
    proved.add('mismatch_triangle');return True

def hamming_reflexivity_induction():
    if hamming_atom(D.NIL,D.NIL)!=0:return False
    original=hamming_step(D.cons(A,X),D.cons(A,X))
    if original.xreplace({hamming_atom(X,X):sp.Integer(0)})!=0:return False
    proved.add('hamming_refl');return True

def hamming_substitution_induction():
    if 'mismatch_triangle' not in proved:return False
    m=mismatch(A,B)
    if not D.bound(0,m,[],[],m):return False
    for av,bv,cv in equality_partitions():
        letters=[D.letter('class_'+str(v)) for v in (av,bv,cv)]
        a,b,c0=letters
        source=D.cons(a,T);other=D.cons(b,T);target=D.cons(c0,Z)
        expressions=[hamming_step(source,target),mismatch(a,b)+hamming_step(other,target)]
        substitution={mismatch(x,y):sp.Integer(int(x!=y)) for x in letters for y in letters if x!=y}
        lower,upper=[expr.xreplace(substitution) for expr in expressions]
        if not D.nonnegative(upper-lower):return False
    left=hamming_step(D.cons(C,P+D.cons(A,T)),D.cons(E,Z))
    right=m+hamming_step(D.cons(C,P+D.cons(B,T)),D.cons(E,Z))
    ih=(hamming_atom(P+D.cons(A,T),Z),m+hamming_atom(P+D.cons(B,T),Z))
    if not D.bound(left,right,[ih],[1]):return False
    proved.add('hamming_substitution');return True

def contradiction(premises,weights):
    if len(premises)!=len(weights) or any(sp.Rational(w)<0 for w in weights):return False
    total=sp.expand(sum((sp.Rational(w)*(b-a) for w,(a,b) in zip(weights,premises)),sp.Integer(0)))
    return total.is_negative is True

def zero_gap_induction():
    if not {'hamming_refl','hamming_substitution'}<=proved:return False
    base_hamming=hamming_atom(X,X)
    if base_hamming.xreplace({hamming_atom(X,X):sp.Integer(0)})!=0:return False
    for tag in ('sdel','sins','ssame','sdiff'):
        env={('neq',A,B):True} if tag=='sdiff' else {}
        proof=(tag,P,T,A,B) if tag=='sdiff' else (tag,P,T,A)
        step=unit_infer(proof,env)
        if step.gaps==1:
            if not contradiction([(1+e,0),(0,e)],[1,1]):return False
        else:
            source_h=hamming_atom(step.source,Z);tail_h=hamming_atom(step.target,Z)
            replacement=A if tag=='ssame' else B
            theorem_upper=mismatch(A,replacement)+tail_h
            if tag=='sdiff':theorem_upper=theorem_upper.xreplace({mismatch(A,B):sp.Integer(1)})
            if not D.exact(theorem_upper,step.cost+tail_h):return False
            if not D.bound(source_h,step.cost+k,[(source_h,theorem_upper),(tail_h,k)],[1,1]):return False
            if not D.exact((step.gaps+e)-0,e):return False
    proved.add('zero_gap_hamming');return True

source='intention'
target='execution'
printed_table=[[0,1,2,3,4,5,6,7,8,9],[1,2,3,4,5,6,7,6,7,8],[2,3,4,5,6,7,8,7,8,7],[3,4,5,6,7,8,7,8,9,8],[4,3,4,5,6,7,8,9,10,9],[5,4,5,6,7,8,9,10,11,10],[6,5,6,7,8,9,8,9,10,11],[7,6,7,8,9,10,9,8,9,10],[8,7,8,9,10,11,10,9,8,9],[9,8,9,10,11,12,11,10,9,8]]

def table_minimum_certificate(table):
    if not {'minimum_edit_cost','prefix_recurrence','prefix_boundary'}<=D.proved:return False
    if len(table)!=len(source)+1 or any(len(row)!=len(target)+1 for row in table):return False
    derived={}
    for total in range(len(source)+len(target)+1):
        for i in range(len(source)+1):
            j=total-i
            if not 0<=j<=len(target):continue
            if i==0:value=j
            elif j==0:value=i
            else:
                if not all((u,v) in derived and u+v<total for u,v in ((i-1,j),(i,j-1),(i-1,j-1))):return False
                value=min(derived[i-1,j]+1,derived[i,j-1]+1,derived[i-1,j-1]+(0 if source[i-1]==target[j-1] else 2))
            if table[i][j]!=value:return False
            derived[i,j]=value
    if len(derived)!=100 or derived[len(source),len(target)]!=8:return False
    certified_values['doubled_minimum']=derived[len(source),len(target)]
    proved.add('doubled_distance_eight');return True

def concrete_hamming_certificate():
    if len(source)!=len(target):return False
    positions=[int(a!=b) for a,b in zip(source,target)]
    if positions!=[1,1,1,1,1,0,0,0,0] or sum(positions)!=5:return False
    certified_values['hamming']=sum(positions)
    proved.add('hamming_five');return True

def unit_lower_certificate(doubled_minimum=8,hamming_minimum=5,domain='Nat'):
    if domain!='Nat' or not {'lift_path','zero_gap_hamming','doubled_distance_eight','hamming_five'}<=proved:return False
    if doubled_minimum!=certified_values['doubled_minimum'] or hamming_minimum!=certified_values['hamming']:return False
    gap_case=[(r+g,2*k),(2*k,8),(doubled_minimum,r),(1,g)]
    zero_case=[(hamming_minimum,k),(k,4)]
    if not contradiction(gap_case,[1,1,1,1]) or not contradiction(zero_case,[1,1]):return False
    proved.add('unit_lower_five');return True

def literal(text):return tuple(D.letter(char) for char in text)
def published_path_certificate():
    descriptions=[('sdel','','ntention','i'),('sdiff','','tention','n','e'),('sdiff','e','ention','t','x'),('sins','exen','tion','u'),('sdiff','exe','ution','n','c')]
    intermediate=['intention','ntention','etention','exention','exenution','execution']
    env={}
    steps=[]
    for i,description in enumerate(descriptions):
        tag,pre,post,a,*rest=description
        proof=(tag,literal(pre),literal(post),D.letter(a),D.letter(rest[0])) if rest else (tag,literal(pre),literal(post),D.letter(a))
        if rest:
            if a==rest[0]:return False
            env[('neq',D.letter(a),D.letter(rest[0]))]=True
        step=unit_infer(proof,env)
        if not unit_same(step,'S',literal(intermediate[i]),literal(intermediate[i+1]),1,1 if tag in ('sdel','sins') else 0):return False
        steps.append(proof)
    path=('prefl',literal(target))
    for step in reversed(steps):path=('pstep',step,path)
    if not unit_same(unit_infer(path,env),'P',literal(source),literal(target),5,2):return False
    proved.add('published_unit_path');return True

def unit_minimum_certificate():
    return {'unit_lower_five','published_unit_path'}<=proved

def check(name,value):
    if value is not True:raise AssertionError((name,value))
    results.append({'id':name,'passed':True})

check('unit_step_cost_lift',lift_step_certificate())
check('unit_path_cost_lift_induction',lift_path_induction())
check('mismatch_triangle_equality_cases',mismatch_triangle_certificate())
check('hamming_reflexivity_induction',hamming_reflexivity_induction())
check('hamming_single_substitution_induction',hamming_substitution_induction())
check('zero_gap_path_hamming_bound',zero_gap_induction())
check('doubled_table_is_minimum_eight',table_minimum_certificate(printed_table))
check('published_hamming_distance_five',concrete_hamming_certificate())
check('all_unit_paths_cost_at_least_five',unit_lower_certificate())
check('published_unit_path_cost_five',published_path_certificate())
check('published_unit_minimum_five',unit_minimum_certificate())
check('wrong_lift_factor_rejected',not lift_step_certificate(1))
check('omitted_gap_count_rejected',not lift_step_certificate(2,False))
check('weaker_doubled_bound_rejected',not unit_lower_certificate(7,5))
check('weaker_hamming_bound_rejected',not unit_lower_certificate(8,4))
check('noninteger_cost_domain_rejected',not unit_lower_certificate(domain='Real'))
check('incomplete_equality_cases_rejected',not mismatch_triangle_certificate(equality_partitions()[:-1]))
check('unsupported_stronger_bound_rejected',not unit_lower_certificate(9,5))
wrong_table=[row[:] for row in printed_table]
wrong_table[4][5]+=1
check('altered_table_cell_rejected',not table_minimum_certificate(wrong_table))

if __name__=='__main__':
    print(json.dumps({'backend':'Python','checks':len(results),'passed':True,'scope':'Only intention to execution with unit insertion/deletion and unequal substitution cost one, equal replacement zero. Universal induction lifts every finite unit edit path to the proved doubled-substitution model with r+d=2k, counting d gaps. A separate induction bounds truncated positional Hamming distance on every zero-gap path. The full published 10x10 table is connected to the already proved prefix minimum. Natural integrality gives cost at least five; the published five-operation path attains five. This is not a general proof of unit-cost dynamic programming.','results':results}))
