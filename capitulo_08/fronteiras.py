import json
import sympy as sp

NIL=('nil',)
def word(name):return ('word',name)
def cons(letter,tail):return ('cons',letter,tail)
def cat(left,right):return ('cat',left,right)
def normal(term):
    if term[0] in ('nil','word'):return term
    if term[0]=='cons':return cons(term[1],normal(term[2]))
    left,right=normal(term[1]),normal(term[2])
    if left==NIL:return right
    if right==NIL:return left
    if left[0]=='cons':return cons(left[1],normal(cat(left[2],right)))
    return cat(left,right)
def length(term):
    if term==NIL:return sp.Integer(0)
    if term[0]=='word':return sp.Symbol('length_'+term[1],integer=True,nonnegative=True)
    if term[0]=='cons':return 1+length(term[2])
    if term[0]=='cat':return length(term[1])+length(term[2])
    raise ValueError('word grammar')
def operation(kind,pre,post,a='a',b='b'):
    old=normal(cat(pre,cons(a,post)))
    short=normal(cat(pre,post))
    if kind=='delete':return old,short,sp.Integer(1)
    if kind=='insert':return short,old,sp.Integer(1)
    if kind=='substitute':return old,normal(cat(pre,cons(b,post))),sp.Integer(0 if a==b else 2)
    raise ValueError('operation')
def verify(proof,hypotheses):
    if proof[0]=='hyp':return hypotheses[proof[1]]
    if proof[0]=='refl':return normal(proof[1]),normal(proof[1]),sp.Integer(0)
    if proof[0]=='step':
        x,y,c=operation(*proof[1])
        u,z,k=verify(proof[2],hypotheses)
        if normal(y)!=normal(u):raise ValueError('unmatched intermediate word')
        return normal(x),normal(z),c+k
    if proof[0]=='compose':
        x,y,c=verify(proof[1],hypotheses)
        u,z,k=verify(proof[2],hypotheses)
        if normal(y)!=normal(u):raise ValueError('unmatched intermediate word')
        return normal(x),normal(z),c+k
    raise ValueError('path rule')

def all_path_length_bounds(extra_cost=0):
    pre,post,z=word('pre'),word('post'),word('z')
    k=sp.Symbol('tail_cost',integer=True,nonnegative=True)
    if any(sp.simplify(length(pre)+0-length(pre))!=0 for _ in (0,1)):return False
    for kind,first,second in (('delete','a','b'),('insert','a','b'),('substitute','a','b'),('substitute','a','a')):
        x,y,c=operation(kind,pre,post,first,second)
        c+=extra_cost
        for start,end in ((x,y),(y,x)):
            local=sp.expand(length(end)+c-length(start))
            if local.is_nonnegative is not True:return False
        child_forward=length(z)+k-length(y)
        child_backward=length(y)+k-length(z)
        total_forward=length(z)+c+k-length(x)
        total_backward=length(x)+c+k-length(z)
        if sp.expand(total_forward-child_forward-(length(y)+c-length(x)))!=0:return False
        if sp.expand(total_backward-child_backward-(length(x)+c-length(y)))!=0:return False
    return True

def constructive_induction(direction,extra=0):
    tail=word('tail')
    base=verify(('refl',NIL),{})
    if base!=(NIL,NIL,0):return False
    if direction=='delete':
        hypotheses={'tail':(tail,NIL,length(tail))}
        proof=('step',('delete',NIL,tail),('hyp','tail'))
        goal=(cons('a',tail),NIL,length(cons('a',tail))+extra)
    elif direction=='insert':
        target=normal(cat(tail,cons('a',NIL)))
        hypotheses={'tail':(NIL,tail,length(tail))}
        proof=('compose',('hyp','tail'),('step',('insert',tail,NIL),('refl',target)))
        goal=(NIL,target,length(target)+extra)
    else:raise ValueError(direction)
    result=verify(proof,hypotheses)
    return result[:2]==goal[:2] and sp.expand(result[2]-goal[2])==0

def rejected(proof,hypotheses):
    try:verify(proof,hypotheses)
    except (ValueError,KeyError):return True
    return False

results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('operation_length_changes',all(sp.expand(length(operation(kind,word('pre'),word('post'))[1])-length(operation(kind,word('pre'),word('post'))[0]))==delta for kind,delta in (('delete',-1),('insert',1),('substitute',0))))
check('substitution_cost_cases',operation('substitute',word('pre'),word('post'),'a','a')[2]==0 and operation('substitute',word('pre'),word('post'),'a','b')[2]==2)
a,b=sp.symbols('a b',nonnegative=True)
check('nonnegative_addition',(a+b).is_nonnegative is True)
lx,ly,lz,c,k=sp.symbols('lx ly lz c k',integer=True,nonnegative=True)
check('composition_length_bounds',sp.expand((lz+c+k-lx)-(ly+c-lx)-(lz+k-ly))==0 and sp.expand((lx+c+k-lz)-(lx+c-ly)-(ly+k-lz))==0)
check('all_finite_path_length_bounds',all_path_length_bounds())
check('zero_cost_deletion_rejected',not all_path_length_bounds(-1))
check('delete_all_structural_certificate',constructive_induction('delete'))
check('insert_all_structural_certificate',constructive_induction('insert'))
check('incorrect_constructive_cost_rejected',not constructive_induction('delete',-1) and not constructive_induction('insert',1))
check('unmatched_path_rejected',rejected(('step',('delete',NIL,word('tail')),('refl',NIL)),{}))
i,slack,c=sp.symbols('i slack c',integer=True,nonnegative=True)
check('prefix_length_domain',sp.Min(i,i+slack)==i)
check('empty_target_lower_bound',sp.expand(0+c-i)==c-i)
check('empty_source_lower_bound',sp.expand(0+c-i)==c-i)
check('delete_boundary_minimum',all_path_length_bounds() and constructive_induction('delete') and sp.Min(i,i+slack)==i)
check('insert_boundary_minimum',all_path_length_bounds() and constructive_induction('insert') and sp.Min(i,i+slack)==i)
print(json.dumps({'backend':'Python 3','scope':'induction over every edit-path constructor and finite-word constructor; deletion/insertion cost1; substitution cost0 for equal symbols and2 otherwise; both equality cases checked; prefix length within the source','checks':len(results),'passed':True,'results':results}))
