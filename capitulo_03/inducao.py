import json

NIL=('nil',)
ZERO=('zero',)
def var(name,sort):return ('var',name,sort)
def cons(a,b):return ('cons',a,b)
def append(a,b):return ('append',a,b)
def length(a):return ('len',a)
def succ(a):return ('succ',a)
def add(a,b):return ('add',a,b)
def free(term):
    if term[0]=='var':return {term[1]}
    if len(term)==1:return set()
    return set().union(*(free(t) for t in term[1:]))
def substitute(term,name,value):
    if term[0]=='var':return value if term[1]==name else term
    return (term[0],*(substitute(t,name,value) for t in term[1:]))
def type_of(term):
    tag=term[0]
    if tag=='var':
        if term[2] not in ('list','element','nat'):raise ValueError('sort')
        return term[2]
    if tag=='nil':return 'list'
    if tag=='zero':return 'nat'
    args=[type_of(t) for t in term[1:]]
    signature={'cons':(['element','list'],'list'),'append':(['list','list'],'list'),'len':(['list'],'nat'),'succ':(['nat'],'nat'),'add':(['nat','nat'],'nat')}
    if tag not in signature or args!=signature[tag][0]:raise ValueError('type')
    return signature[tag][1]
def normalize(term):
    if term[0]=='var' or len(term)==1:return term
    tag=term[0];args=[normalize(t) for t in term[1:]]
    if tag=='append':
        if args[0]==NIL:return args[1]
        if args[0][0]=='cons':return cons(args[0][1],normalize(append(args[0][2],args[1])))
    if tag=='len':
        if args[0]==NIL:return ZERO
        if args[0][0]=='cons':return succ(normalize(length(args[0][2])))
    if tag=='add':
        if args[0]==ZERO:return args[1]
        if args[0][0]=='succ':return succ(normalize(add(args[0][1],args[1])))
    return (tag,*args)
def rewrite_exact(term,left,right):
    if term==left:return right
    if term[0]=='var' or len(term)==1:return term
    return (term[0],*(rewrite_exact(t,left,right) for t in term[1:]))
def structural_induction(left,right,variable):
    if type_of(left)!=type_of(right) or type_of(variable)!='list':raise ValueError('type')
    names=free(left)|free(right)
    if names&{'fresh_head','fresh_tail'}:raise ValueError('freshness')
    base_left=normalize(substitute(left,variable[1],NIL))
    base_right=normalize(substitute(right,variable[1],NIL))
    if base_left!=base_right:return False
    head=var('fresh_head','element');tail=var('fresh_tail','list')
    hypothesis_left=normalize(substitute(left,variable[1],tail))
    hypothesis_right=normalize(substitute(right,variable[1],tail))
    step_left=normalize(substitute(left,variable[1],cons(head,tail)))
    step_right=normalize(substitute(right,variable[1],cons(head,tail)))
    return normalize(rewrite_exact(step_left,hypothesis_left,hypothesis_right))==step_right

def word(text):
    result=NIL
    for c in reversed(text):result=cons(var(c,'element'),result)
    return result

def number(n):
    result=ZERO
    for _ in range(n):result=succ(result)
    return result

xs,ys,zs=[var(a,'list') for a in ('xs','ys','zs')]
certificates={'associativity':(append(append(xs,ys),zs),append(xs,append(ys,zs)),xs),'right_identity':(append(xs,NIL),xs,xs),'length_append':(length(append(xs,ys)),add(length(xs),length(ys)),xs)}
results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('associativity_induction',structural_induction(*certificates['associativity']))
check('right_identity_induction',structural_induction(*certificates['right_identity']))
check('length_append_induction',structural_induction(*certificates['length_append']))
check('left_identity_definition',normalize(append(NIL,xs))==xs)
check('empty_length_definition',normalize(length(NIL))==ZERO)
check('published_worked',normalize(append(word('work'),word('ed')))==word('worked') and normalize(length(word('work')))==number(4) and normalize(length(word('ed')))==number(2) and normalize(length(word('worked')))==number(6) and normalize(add(number(4),number(2)))==number(6))
check('published_carefully',normalize(append(append(word('care'),word('ful')),word('ly')))==normalize(append(word('care'),append(word('ful'),word('ly'))))==word('carefully') and normalize(length(word('carefully')))==number(9))
check('commutativity_rejected',not structural_induction(append(xs,ys),append(ys,xs),xs))
check('wrong_length_rejected',not structural_induction(length(append(xs,ys)),succ(add(length(xs),length(ys))),xs))
print(json.dumps({'backend':'Python 3','scope':'structural induction from finite-list append, length and natural-addition recursions','checks':len(results),'passed':True,'results':results}))
