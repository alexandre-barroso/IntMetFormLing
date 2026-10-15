import json
from itertools import product

SNIL=('snil',)
FNIL=('fnil',)
ZERO=('zero',)
BIT0=('bit0',)
BIT1=('bit1',)
TRUE=('truth',)
FALSE=('falsehood',)
proved=set()
def var(name,sort):return ('var',name,sort)
def term(tag,*args):return (tag,*args)
def eq(a,b):return term('eq',a,b)
def conjunction(*args):return term('and',*args)
def free(t):
    if t[0]=='var':return {t[1]}
    return set().union(*(free(a) for a in t[1:])) if len(t)>1 else set()
def substitute(t,name,value):
    if t[0]=='var':return value if t[1]==name else t
    return (t[0],*(substitute(a,name,value) for a in t[1:]))
def type_of(t):
    tag=t[0]
    if tag=='var':
        if t[2] not in ('bit','string','family','nat'):raise ValueError('sort')
        return t[2]
    constants={'snil':'string','fnil':'family','zero':'nat','bit0':'bit','bit1':'bit','truth':'prop','falsehood':'prop'}
    if tag in constants:
        if len(t)!=1:raise ValueError('arity')
        return constants[tag]
    args=[type_of(a) for a in t[1:]]
    if tag in ('and','or'):
        if any(a!='prop' for a in args):raise ValueError('type')
        return 'prop'
    if tag=='eq':
        if len(args)!=2 or args[0]!=args[1]:raise ValueError('type')
        return 'prop'
    signature={'scons':(['bit','string'],'string'),'fcons':(['string','family'],'family'),'head':(['string'],'bit'),'tail':(['string'],'string'),'succ':(['nat'],'nat'),'add':(['nat','nat'],'nat'),'slen':(['string'],'nat'),'flen':(['family'],'nat'),'map':(['bit','family'],'family'),'append':(['family','family'],'family'),'enum':(['nat'],'family'),'pow2':(['nat'],'nat'),'mem':(['string','family'],'prop'),'not':(['prop'],'prop'),'unique':(['family'],'prop'),'disjoint':(['family','family'],'prop')}
    if tag not in signature or args!=signature[tag][0]:raise ValueError('type')
    return signature[tag][1]
def normalize(t):
    if t[0]=='var' or len(t)==1:return t
    tag=t[0];args=[normalize(a) for a in t[1:]]
    if tag in ('and','or'):
        unit,absorber=(TRUE,FALSE) if tag=='and' else (FALSE,TRUE)
        flat=[]
        for a in args:
            if a==absorber:return absorber
            if a==unit:continue
            flat.extend(a[1:] if a[0]==tag else [a])
        flat=sorted(set(flat),key=repr)
        if not flat:return unit
        if len(flat)==1:return flat[0]
        return (tag,*flat)
    if tag=='not':
        a=args[0]
        if a==TRUE:return FALSE
        if a==FALSE:return TRUE
        if a[0]=='not':return a[1]
        if a[0] in ('or','and'):return normalize(term('and' if a[0]=='or' else 'or',*(term('not',b) for b in a[1:])))
    if tag=='eq':
        a,b=args
        if a==b:return TRUE
        if {a,b}=={BIT0,BIT1}:return FALSE
        if a==SNIL and b[0]=='scons' or b==SNIL and a[0]=='scons':return FALSE
        if a[0]=='scons' and b[0]=='scons':return normalize(conjunction(eq(a[1],b[1]),eq(a[2],b[2])))
        if a==ZERO and b[0]=='succ' or b==ZERO and a[0]=='succ':return FALSE
        if a[0]=='succ' and b[0]=='succ':return normalize(eq(a[1],b[1]))
    if tag=='slen':
        if args[0]==SNIL:return ZERO
        if args[0][0]=='scons':return normalize(term('succ',term('slen',args[0][2])))
    if tag in ('head','tail') and args[0][0]=='scons':return args[0][1 if tag=='head' else 2]
    if tag=='map':
        bit,family=args
        if family==FNIL:return FNIL
        if family[0]=='fcons':return normalize(term('fcons',term('scons',bit,family[1]),term('map',bit,family[2])))
    if tag=='append':
        first,second=args
        if first==FNIL:return second
        if first[0]=='fcons':return normalize(term('fcons',first[1],term('append',first[2],second)))
    if tag=='flen':
        family=args[0]
        if family==FNIL:return ZERO
        if family[0]=='fcons':return normalize(term('succ',term('flen',family[2])))
        if family[0]=='append' and 'append_length' in proved:return normalize(term('add',term('flen',family[1]),term('flen',family[2])))
        if family[0]=='map' and 'map_length' in proved:return normalize(term('flen',family[2]))
    if tag=='add':
        if args[0]==ZERO:return args[1]
        if args[0][0]=='succ':return normalize(term('succ',term('add',args[0][1],args[1])))
    if tag=='enum':
        if args[0]==ZERO:return term('fcons',SNIL,FNIL)
        if args[0][0]=='succ':return normalize(term('append',term('map',BIT0,term('enum',args[0][1])),term('map',BIT1,term('enum',args[0][1]))))
    if tag=='pow2':
        if args[0]==ZERO:return term('succ',ZERO)
        if args[0][0]=='succ':return normalize(term('add',term('pow2',args[0][1]),term('pow2',args[0][1])))
    if tag=='mem':
        sequence,family=args
        if family==FNIL:return FALSE
        if family[0]=='fcons':return normalize(term('or',eq(sequence,family[1]),term('mem',sequence,family[2])))
        if family[0]=='append' and 'member_append' in proved:return normalize(term('or',term('mem',sequence,family[1]),term('mem',sequence,family[2])))
        if family[0]=='map':
            if sequence==SNIL and 'member_map_empty' in proved:return FALSE
            if sequence[0]=='scons' and 'member_map_cons' in proved:return normalize(conjunction(eq(sequence[1],family[1]),term('mem',sequence[2],family[2])))
    if tag=='unique':
        family=args[0]
        if family==FNIL:return TRUE
        if family[0]=='fcons':return normalize(conjunction(term('not',term('mem',family[1],family[2])),term('unique',family[2])))
        if family[0]=='map' and 'map_unique' in proved:return normalize(term('unique',family[2]))
        if family[0]=='append' and 'append_unique' in proved:return normalize(conjunction(term('unique',family[1]),term('unique',family[2]),term('disjoint',family[1],family[2])))
    if tag=='disjoint':
        first,second=args
        if first==FNIL:return TRUE
        if first[0]=='fcons':return normalize(conjunction(term('not',term('mem',first[1],second)),term('disjoint',first[2],second)))
        if first[0]=='map' and second[0]=='map' and first[1]==BIT0 and second[1]==BIT1 and 'disjoint_images' in proved:return TRUE
    return (tag,*args)
def rewrite(t,left,right):
    if t==left:return right
    if t[0]=='var' or len(t)==1:return t
    return (t[0],*(rewrite(a,left,right) for a in t[1:]))
def equivalent(left,right):
    if left==right:return True
    if type_of(left)!='prop' or type_of(right)!='prop':return False
    def atoms(t):
        if t in (TRUE,FALSE):return set()
        if t[0] in ('and','or','not'):return set().union(*(atoms(a) for a in t[1:]))
        return {t}
    def evaluate(t,assignment):
        if t==TRUE:return True
        if t==FALSE:return False
        if t[0]=='and':return all(evaluate(a,assignment) for a in t[1:])
        if t[0]=='or':return any(evaluate(a,assignment) for a in t[1:])
        if t[0]=='not':return not evaluate(t[1],assignment)
        return assignment[t]
    labels=sorted(atoms(left)|atoms(right),key=repr)
    return all(evaluate(left,dict(zip(labels,values)))==evaluate(right,dict(zip(labels,values))) for values in product((False,True),repeat=len(labels)))

def family_induction(left,right,variable):
    if type_of(left)!=type_of(right) or type_of(variable)!='family':raise ValueError('type')
    if (free(left)|free(right))&{'fresh_head','fresh_tail'}:raise ValueError('freshness')
    if normalize(substitute(left,variable[1],FNIL))!=normalize(substitute(right,variable[1],FNIL)):return False
    head=var('fresh_head','string');tail=var('fresh_tail','family')
    ihl=normalize(substitute(left,variable[1],tail));ihr=normalize(substitute(right,variable[1],tail))
    stepl=normalize(substitute(left,variable[1],term('fcons',head,tail)));stepr=normalize(substitute(right,variable[1],term('fcons',head,tail)))
    return equivalent(normalize(rewrite(stepl,ihl,ihr)),stepr)

def natural_induction(left,right,variable):
    if type_of(left)!=type_of(right) or type_of(variable)!='nat':raise ValueError('type')
    if normalize(substitute(left,variable[1],ZERO))!=normalize(substitute(right,variable[1],ZERO)):return False
    stepl=normalize(substitute(left,variable[1],term('succ',variable)));stepr=normalize(substitute(right,variable[1],term('succ',variable)))
    return normalize(rewrite(stepl,normalize(left),normalize(right)))==stepr

def coverage_induction():
    n=var('n','nat');tail=var('xs','string')
    for sequence in (SNIL,term('scons',BIT0,tail),term('scons',BIT1,tail)):
        if normalize(term('mem',sequence,term('enum',ZERO)))!=normalize(eq(term('slen',sequence),ZERO)):return False
        left=normalize(term('mem',sequence,term('enum',term('succ',n))))
        right=normalize(eq(term('slen',sequence),term('succ',n)))
        left=normalize(rewrite(left,term('mem',tail,term('enum',n)),eq(term('slen',tail),n)))
        if left!=right:return False
    return True

xs,ys=var('xs','family'),var('ys','family')
s,t=var('s','string'),var('t','string')
bit=var('bit','bit');other_bit=var('other_bit','bit');n=var('n','nat')
results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})
rule_targets={'map_length': (term('flen', term('map', bit, xs)), term('flen', xs), xs),
'append_length': (term('flen', term('append', xs, ys)), term('add', term('flen', xs), term('flen', ys)), xs),
'member_map_empty': (term('mem', SNIL, term('map', bit, xs)), FALSE, xs),
'member_map_cons': (term('mem', term('scons', bit, s), term('map', other_bit, xs)), conjunction(eq(bit, other_bit), term('mem', s, xs)), xs),
'map_unique': (term('unique', term('map', bit, xs)), term('unique', xs), xs),
'member_append': (term('mem', s, term('append', xs, ys)), term('or', term('mem', s, xs), term('mem', s, ys)), xs),
'append_unique': (term('unique', term('append', xs, ys)), conjunction(term('unique', xs), term('unique', ys), term('disjoint', xs, ys)), xs),
'disjoint_images': (term('disjoint', term('map', BIT0, xs), term('map', BIT1, ys)), TRUE, xs)}
def certify(name,left,right,variable):
    if name in proved or name not in rule_targets or (left,right,variable)!=rule_targets[name]:return False
    valid=family_induction(left,right,variable)
    if valid:proved.add(name)
    return valid

check('prepend_left_inverse',normalize(term('tail',term('scons',bit,s)))==s and normalize(term('head',term('scons',bit,s)))==bit)
check('prepend_injective',normalize(eq(term('scons',bit,s),term('scons',bit,t)))==eq(s,t))
check('binary_images_disjoint',normalize(eq(term('scons',BIT0,s),term('scons',BIT1,t)))==FALSE)
check('map_length_induction',certify('map_length',term('flen',term('map',bit,xs)),term('flen',xs),xs))
check('append_length_induction',certify('append_length',term('flen',term('append',xs,ys)),term('add',term('flen',xs),term('flen',ys)),xs))
check('map_membership_empty_induction',certify('member_map_empty',term('mem',SNIL,term('map',bit,xs)),FALSE,xs))
check('map_membership_constructor_induction',certify('member_map_cons',term('mem',term('scons',bit,s),term('map',other_bit,xs)),conjunction(eq(bit,other_bit),term('mem',s,xs)),xs))
check('map_unique_induction',certify('map_unique',term('unique',term('map',bit,xs)),term('unique',xs),xs))
check('append_membership_induction',certify('member_append',term('mem',s,term('append',xs,ys)),term('or',term('mem',s,xs),term('mem',s,ys)),xs))
check('append_unique_induction',certify('append_unique',term('unique',term('append',xs,ys)),conjunction(term('unique',xs),term('unique',ys),term('disjoint',xs,ys)),xs))
check('disjoint_images_induction',certify('disjoint_images',term('disjoint',term('map',BIT0,xs),term('map',BIT1,ys)),TRUE,xs))
check('enumeration_unique_induction',natural_induction(term('unique',term('enum',n)),TRUE,n))
check('enumeration_complete_induction',coverage_induction())
check('enumeration_cardinality_induction',natural_induction(term('flen',term('enum',n)),term('pow2',n),n))
check('unrelated_rule_rejected',not certify('map_length',TRUE,TRUE,xs))
check('wrong_count_rejected',not natural_induction(term('flen',term('enum',n)),term('add',term('pow2',n),term('succ',ZERO)),n))
check('duplicated_prefix_not_disjoint',normalize(eq(term('scons',BIT0,s),term('scons',BIT0,s)))==TRUE)
check('empty_assignment_unique',normalize(term('enum',ZERO))==term('fcons',SNIL,FNIL) and normalize(term('flen',term('enum',ZERO)))==term('succ',ZERO))
print(json.dumps({'backend':'Python 3','scope':'Finite binary sequences encode one orientation per indexed pair. The enumerator starts with the singleton empty sequence and appends the false-prefixed and true-prefixed images at each successor. Typed free-constructor inversion proves injectivity and disjointness. Structural inductions certify map/append lengths and uniqueness; induction on n proves every and only sequence of length n occurs and no occurrence is duplicated. The actual enumeration length is then proved equal to natural 2^n by induction. n=0 is included; numerical performance values and ties are not identified with assignments.','checks':len(results),'passed':True,'results':results}))
