import json
import analise_geral as a


def iff(proof, premise, side=0):
    result=('iff_mp',proof,premise,side)
    a.infer(result)
    return result


def part(proof,index):
    result=('and_elim',proof,index)
    a.infer(result)
    return result


def h(formula):
    return a.assumption('|- '+formula)


def real(term):
    return h(term+' e. RR')


def positive(term):
    return h(term+' e. RR+')


def positive_parts(term,proof):
    return iff(a.mm('elrp',{'A':term}),proof)


def as_real(term,proof):
    return part(positive_parts(term,proof),0)


def as_positive(term,hr,hp):
    return iff(a.mm('elrp',{'A':term}),a.both(hr,hp),1)


def as_complex(term,proof):
    return a.unlift(a.mm('recnd',{'ph':'T.','A':term},(a.lift(proof),)))


def larger_positive(x,y,hx,hy,hxy):
    xp=positive_parts(x,hx)
    zero=a.mm('0re')
    result=a.mp(a.mp(a.mm('lttr',{'A':'0','B':x,'C':y}),a.both(zero,part(xp,0),hy)),a.both(part(xp,1),hxy))
    return as_positive(y,hy,result)


def neg_product(x,y,hx,hy):
    return a.mp(a.mm('mulneg1',{'A':x,'B':y}),a.both(as_complex(x,hx),as_complex(y,hy)))


def scalar_order(label,u,v,c,hu,hv,hc,order):
    equivalent=a.mp(a.mm(label,{'A':u,'B':v,'C':c}),a.both(hu,hv,hc))
    return iff(equivalent,order)


def add_order(weak=False):
    return scalar_order('leadd1' if weak else 'ltadd1','A','B','C',real('A'),real('B'),real('C'),h('A <_ B' if weak else 'A < B'))


def positive_order(weak=False):
    return scalar_order('lemul2' if weak else 'ltmul2','A','B','C',real('A'),real('B'),positive_parts('C',positive('C')),h('A <_ B' if weak else 'A < B'))


def negative_order(weak=False):
    ha,hb,hc=real('A'),real('B'),real('C')
    hcnegative=h('C < 0')
    negc='-u C'
    hneg=a.mp(a.mm('renegcl',{'A':'C'}),hc)
    hp=iff(a.mp(a.mm('lt0neg1',{'A':'C'}),hc),hcnegative)
    ordered=scalar_order('lemul2' if weak else 'ltmul2','A','B',negc,ha,hb,a.both(hneg,hp),h('A <_ B' if weak else 'A < B'))
    left=f'( {negc} x. A )';right=f'( {negc} x. B )'
    lreal=a.mp(a.mm('remulcl',{'A':negc,'B':'A'}),a.both(hneg,ha))
    rreal=a.mp(a.mm('remulcl',{'A':negc,'B':'B'}),a.both(hneg,hb))
    negated=iff(a.mp(a.mm('leneg' if weak else 'ltneg',{'A':left,'B':right}),a.both(lreal,rreal)),ordered)
    result=negated
    for value,hr in [('A',ha),('B',hb)]:
        result=a.rewrite(neg_product('C',value,hc,hr),result)
        prod=f'( C x. {value} )'
        pr=a.mp(a.mm('remulcl',{'A':'C','B':value}),a.both(hc,hr))
        double=a.mp(a.mm('negneg',{'A':prod}),as_complex(prod,pr))
        result=a.rewrite(double,result)
    return result


def exponential_decreasing():
    hx,hy=real('A'),real('B')
    hlam,hscale=positive('C'),positive('D')
    lc='-u C'
    hr=as_real('C',hlam)
    nr=a.mp(a.mm('renegcl',{'A':'C'}),hr)
    p=a.mp(a.mm('rpgt0',{'A':'C'}),hlam)
    argument=scalar_order('ltmul2','A','B','C',hx,hy,a.both(hr,p),h('A < B'))
    ax='( C x. A )';by='( C x. B )'
    ar=a.mp(a.mm('remulcl',{'A':'C','B':'A'}),a.both(hr,hx))
    br=a.mp(a.mm('remulcl',{'A':'C','B':'B'}),a.both(hr,hy))
    neg_order=iff(a.mp(a.mm('ltneg',{'A':ax,'B':by}),a.both(ar,br)),argument)
    nx='-u '+ax;ny='-u '+by
    nxr=a.mp(a.mm('renegcl',{'A':ax}),ar);nyr=a.mp(a.mm('renegcl',{'A':by}),br)
    exp_order=iff(a.mp(a.mm('eflt',{'A':ny,'B':nx}),a.both(nyr,nxr)),neg_order)
    ea=f'( exp ` {ny} )';eb=f'( exp ` {nx} )'
    ear=a.mp(a.mm('reefcl',{'A':ny}),nyr);ebr=a.mp(a.mm('reefcl',{'A':nx}),nxr)
    return scalar_order('ltmul2',ea,eb,'D',ear,ebr,positive_parts('D',hscale),exp_order)


def exponential_increasing():
    hx,hy,hc=real('A'),real('B'),real('C')
    nc='-u C';ncr=a.mp(a.mm('renegcl',{'A':'C'}),hc)
    ncp=iff(a.mp(a.mm('lt0neg1',{'A':'C'}),hc),h('C < 0'))
    order=scalar_order('ltmul2','A','B',nc,hx,hy,a.both(ncr,ncp),h('A < B'))
    x=f'( {nc} x. A )';y=f'( {nc} x. B )'
    xr=a.mp(a.mm('remulcl',{'A':nc,'B':'A'}),a.both(ncr,hx))
    yr=a.mp(a.mm('remulcl',{'A':nc,'B':'B'}),a.both(ncr,hy))
    return iff(a.mp(a.mm('eflt',{'A':x,'B':y}),a.both(xr,yr)),order)


def negative_argument():
    hc,hn=real('C'),positive('N')
    ncr=a.mp(a.mm('renegcl',{'A':'C'}),hc)
    ncp=iff(a.mp(a.mm('lt0neg1',{'A':'C'}),hc),h('C < 0'))
    return a.mp(a.mm('mulgt0',{'A':'-u C','B':'N'}),a.both(a.both(ncr,ncp),positive_parts('N',hn)))


def surprise_order():
    hp=positive('A')
    hq=larger_positive('A','B',hp,real('B'),h('A < B'))
    la='( log ` A )';lb='( log ` B )';l2='( log ` 2 )'
    lr=a.mp(a.mm('relogcl',{'A':'A'}),hp);qr=a.mp(a.mm('relogcl',{'A':'B'}),hq)
    order=iff(a.mp(a.mm('logltb'),a.both(hp,hq)),h('A < B'))
    negated=iff(a.mp(a.mm('ltneg',{'A':la,'B':lb}),a.both(lr,qr)),order)
    negla='-u '+la;neglb='-u '+lb
    nlr=a.mp(a.mm('renegcl',{'A':la}),lr);nqr=a.mp(a.mm('renegcl',{'A':lb}),qr)
    lr2=a.mp(a.mm('relogcl',{'A':'2'}),a.mm('2rp'))
    pos2=iff(a.mp(a.mm('loggt0b',{'A':'2'}),a.mm('2rp')),a.mm('1lt2'),1)
    return scalar_order('ltdiv1',neglb,negla,l2,nqr,nlr,a.both(lr2,pos2),negated)


def heaps_increasing():
    ha,hb=real('A'),real('B')
    hage0=h('0 <_ A')
    hbge0=a.mp(a.mp(a.mm('lelttr',{'A':'0','B':'A','C':'B'}),a.both(a.mm('0re'),ha,hb)),a.both(hage0,h('A < B')))
    hbge0=a.mp(a.mp(a.mm('ltle',{'A':'0','B':'B'}),a.both(a.mm('0re'),hb)),hbge0)
    hc,hd=positive('C'),positive('D')
    p=iff(a.mp(a.mm('cxplt2'),a.both(a.both(ha,hage0),a.both(hb,hbge0),hc)),h('A < B'))
    cr=as_real('C',hc)
    ar=a.mp(a.mm('recxpcl',{'A':'A','B':'C'}),a.both(ha,hage0,cr))
    br=a.mp(a.mm('recxpcl',{'A':'B','B':'C'}),a.both(hb,hbge0,cr))
    return scalar_order('ltmul2','( A ^c C )','( B ^c C )','D',ar,br,positive_parts('D',hd),p)


def zipf_decreasing():
    hx,hc,hd=positive('A'),positive('C'),positive('D')
    hy=larger_positive('A','B',hx,real('B'),h('A < B'))
    xr,yr,cr=as_real('A',hx),as_real('B',hy),as_real('C',hc)
    gea=a.mp(a.mm('rpge0',{'A':'A'}),hx)
    geb=a.mp(a.mm('rpge0',{'A':'B'}),hy)
    growth=iff(a.mp(a.mm('cxplt2'),a.both(a.both(xr,gea),a.both(yr,geb),hc)),h('A < B'))
    xp='( A ^c C )';yp='( B ^c C )'
    xpp=a.mp(a.mm('rpcxpcl',{'A':'A','B':'C'}),a.both(hx,cr))
    ypp=a.mp(a.mm('rpcxpcl',{'A':'B','B':'C'}),a.both(hy,cr))
    inv=iff(a.mp(a.mm('ltrec',{'A':xp,'B':yp}),a.both(positive_parts(xp,xpp),positive_parts(yp,ypp))),growth)
    ncr=a.mp(a.mm('renegcl',{'A':'C'}),cr)
    nx='( A ^c -u C )';ny='( B ^c -u C )'
    nxp=a.mp(a.mm('rpcxpcl',{'A':'A','B':'-u C'}),a.both(hx,ncr))
    nyp=a.mp(a.mm('rpcxpcl',{'A':'B','B':'-u C'}),a.both(hy,ncr))
    for value,hp,hr in [('A',hx,xr),('B',hy,yr)]:
        eq=a.mp(a.mm('cxpneg',{'A':value,'B':'C'}),a.both(as_complex(value,hr),a.mp(a.mm('rpne0',{'A':value}),hp),as_complex('C',cr)))
        inv=a.rewrite(a.eqsym(eq),inv)
    return scalar_order('ltmul2',ny,nx,'D',as_real(ny,nyp),as_real(nx,nxp),positive_parts('D',hd),inv)


def derivative_sum_or_chain(chain=False):
    hf=h('F : RR --> RR');hg=h('G : RR --> RR')
    rrcc=a.mm('axresscn');rrself=a.mm('ssid',{'A':'RR'})
    fc=a.mp(a.mm('fss',{'F':'F','A':'RR','B':'RR','C':'CC'}),a.both(hf,rrcc))
    gc=a.mp(a.mm('fss',{'F':'G','A':'RR','B':'RR','C':'CC'}),a.both(hg,rrcc))
    df=h('( G ` C ) ( RR _D F ) K') if chain else h('C ( RR _D F ) K')
    dg=h('C ( RR _D G ) L')
    sub={'ph':'T.','S':'RR','X':'RR','Y':'RR','J':'( TopOpen ` CCfld )'}
    if chain:
        sub['T']='RR'
        premises=(fc,rrself,hg,rrself,rrcc,rrcc,df,dg)
    else:
        premises=(fc,rrself,gc,rrself,rrcc,df,dg)
    return a.unlift(a.mm('dvcobr' if chain else 'dvaddbr',sub,tuple(a.lift(x) for x in premises)+(a.eqref('( TopOpen ` CCfld )'),)))


def derivative_constant():
    hr=real('C');dc=as_complex('D',real('D'))
    deriv=a.mp(a.mm('dvsconst',{'S':'RR','A':'D'}),a.both(a.mm('reelprrecn'),dc))
    zero_singleton=a.mp(a.mm('snidg',{'A':'0','V':'CC'}),a.mm('0cn'))
    point=iff(a.mm('brxp',{'A':'C','B':'0','C':'RR','D':'{ 0 }'}),a.both(hr,zero_singleton),1)
    return a.rewrite(a.eqsym(deriv),point)


def derivative_identity():
    identity='( x e. RR |-> x )'
    deriv=a.unlift(a.mm('dvmptid',{'ph':'T.','S':'RR','x':'x'},(a.lift(a.mm('reelprrecn')),)))
    constant=a.mm('fconstmpt',{'x':'x','A':'RR','B':'1'})
    one_singleton=a.mp(a.mm('snidg',{'A':'1','V':'CC'}),a.mm('ax1cn'))
    point=iff(a.mm('brxp',{'A':'C','B':'1','C':'RR','D':'{ 1 }'}),a.both(real('C'),one_singleton),1)
    point=a.rewrite(constant,point)
    return a.rewrite(a.eqsym(deriv),point)


def derivative_scalar_factor():
    hr,dr,kr=real('C'),real('D'),real('K')
    dc,kc=as_complex('D',dr),as_complex('K',kr)
    f='( RR X. { D } )'
    fc=a.mp(a.mm('fconstg',{'A':'RR','B':'D','V':'CC'}),dc)
    single=a.mp(a.mm('snssi',{'A':'D','B':'CC'}),dc)
    fc=a.mp(a.mm('fss',{'F':f,'A':'RR','B':'{ D }','C':'CC'}),a.both(fc,single))
    gr=h('G : RR --> RR')
    gc=a.mp(a.mm('fss',{'F':'G','A':'RR','B':'RR','C':'CC'}),a.both(gr,a.mm('axresscn')))
    dg=h('C ( RR _D G ) K')
    premises=(fc,a.mm('ssid',{'A':'RR'}),gc,a.mm('ssid',{'A':'RR'}),a.mm('axresscn'),derivative_constant(),dg)
    proof=a.unlift(a.mm('dvmulbr',{'ph':'T.','F':f,'S':'RR','X':'RR','Y':'RR','K':'0','L':'K','J':'( TopOpen ` CCfld )'},tuple(a.lift(p) for p in premises)+(a.eqref('( TopOpen ` CCfld )'),)))
    gvalue=a.mp(a.mm('ffvelcdm',{'F':'G','A':'RR','B':'CC','C':'C'}),a.both(gc,hr))
    zero=a.mp(a.mm('mul02',{'A':'( G ` C )'}),gvalue)
    proof=a.rewrite(zero,proof)
    fv=a.mp(a.mm('fvconst2',{'A':'RR','B':'D','C':'C'},(a.mp(a.mm('elex',{'A':'D','B':'CC'}),dc),)),hr)
    proof=a.rewrite(fv,proof)
    product=a.mp(a.mm('mulcl',{'A':'K','B':'D'}),a.both(kc,dc))
    proof=a.rewrite(a.mp(a.mm('addlid',{'A':'( K x. D )'}),product),proof)
    return a.rewrite(a.mp(a.mm('mulcom',{'A':'K','B':'D'}),a.both(kc,dc)),proof)


def heaps_sublinear():
    ap,dp=h('A e. RR+'),h('D e. RR+')
    br,cr=real('B'),real('C')
    bp=larger_positive('1','B',a.mm('1rp'),br,h('1 < B'))
    ratio=iff(a.mp(a.mm('cxplt',{'A':'B','B':'C','C':'1'}),a.both(a.both(br,h('1 < B')),a.both(cr,a.mm('1re')))),h('C < 1'))
    ratio=a.rewrite(a.mp(a.mm('cxp1',{'A':'B'}),as_complex('B',br)),ratio)
    ac='( A ^c C )';bc='( B ^c C )';factor=f'( D x. {ac} )'
    acp=a.mp(a.mm('rpcxpcl',{'A':'A','B':'C'}),a.both(ap,cr))
    bcp=a.mp(a.mm('rpcxpcl',{'A':'B','B':'C'}),a.both(bp,cr))
    fp=a.mp(a.mm('rpmulcl',{'A':'D','B':ac}),a.both(dp,acp))
    proof=scalar_order('ltmul2',bc,'B',factor,as_real(bc,bcp),br,positive_parts(factor,fp),ratio)
    dc=as_complex('D',as_real('D',dp));acc=as_complex(ac,as_real(ac,acp));bcc=as_complex(bc,as_real(bc,bcp))
    proof=a.rewrite(a.mp(a.mm('mul32',{'A':'D','B':ac,'C':bc}),a.both(dc,acc,bcc)),proof)
    proof=a.rewrite(a.mp(a.mm('mulass',{'A':'D','B':bc,'C':ac}),a.both(dc,bcc,acc)),proof)
    product=a.mp(a.mm('mulcxp',{'A':'B','B':'A','C':'C'}),a.both(a.both(br,a.mp(a.mm('rpge0',{'A':'B'}),bp)),a.both(as_real('A',ap),a.mp(a.mm('rpge0',{'A':'A'}),ap)),as_complex('C',cr)))
    proof=a.rewrite(a.eqsym(product),proof)
    return a.rewrite(a.mp(a.mm('mulcom',{'A':factor,'B':'B'}),a.both(as_complex(factor,as_real(factor,fp)),as_complex('B',br))),proof)


def fractional_power():
    ap,zp=positive('A'),positive('Z')
    mn,nn=h('M e. NN'),h('N e. NN')
    mp=a.mp(a.mm('nnrp',{'A':'M'}),mn);np=a.mp(a.mm('nnrp',{'A':'N'}),nn)
    mr,nr=as_real('M',mp),as_real('N',np)
    mc,nc=as_complex('M',mr),as_complex('N',nr)
    nne=a.mp(a.mm('rpne0',{'A':'N'}),np)
    m0=a.mp(a.mm('nnnn0',{'A':'M'}),mn);n0=a.mp(a.mm('nnnn0',{'A':'N'}),nn)
    ratio='( M / N )'
    rp=a.mp(a.mm('rpdivcl',{'A':'M','B':'N'}),a.both(mp,np))
    rr=as_real(ratio,rp);rc=as_complex(ratio,rr)
    ar=as_real('A',ap);ac=as_complex('A',ar)
    target=f'( A ^c {ratio} )'
    tp=a.mp(a.mm('rpcxpcl',{'A':'A','B':ratio}),a.both(ap,rr));tr=as_real(target,tp);tc=as_complex(target,tr)
    power=a.mp(a.mm('cxpmul2',{'A':'A','B':ratio,'C':'N'}),a.both(ac,rc,n0))
    cancel=a.mp(a.mm('divcan1',{'A':'M','B':'N'}),a.both(mc,nc,nne))
    power=a.rewrite(cancel,power)
    integer=a.mp(a.mm('cxpexp',{'A':'A','B':'M'}),a.both(ac,m0))
    power=a.rewrite(integer,power)
    power=a.eqsym(power)
    given=h('( Z ^ N ) = ( A ^ M )')
    equal=a.rewrite(a.eqsym(power),given)
    zr=as_real('Z',zp);zc=as_complex('Z',zr)
    for base,bcomplex in [('Z',zc),(target,tc)]:
        eq=a.mp(a.mm('cxpexp',{'A':base,'B':'N'}),a.both(bcomplex,n0))
        equal=a.rewrite(a.eqsym(eq),equal)
    premises=(zr,a.mp(a.mm('rpge0',{'A':'Z'}),zp),tr,a.mp(a.mm('rpge0',{'A':target}),tp),np)
    injective=a.unlift(a.mm('recxpf1lem',{'ph':'T.','A':'Z','B':target,'C':'N'},tuple(a.lift(p) for p in premises)))
    unique=iff(injective,equal,1)
    return power,unique


def raw_certificates():
    return {
        'addition_preserves_strict_order':add_order(),
        'addition_preserves_weak_order':add_order(True),
        'positive_scaling_preserves_strict_order':positive_order(),
        'positive_scaling_preserves_weak_order':positive_order(True),
        'negative_scaling_reverses_strict_order':negative_order(),
        'negative_scaling_reverses_weak_order':negative_order(True),
        'decreasing_exponential':exponential_decreasing(),
        'growing_exponential_factor':exponential_increasing(),
        'negative_parameter_argument':negative_argument(),
        'surprise_decreasing':surprise_order(),
        'heaps_increasing':heaps_increasing(),
        'zipf_decreasing':zipf_decreasing(),
        'derivative_sum':derivative_sum_or_chain(),
        'derivative_composition':derivative_sum_or_chain(True),
        'derivative_constant':derivative_constant(),
        'derivative_identity':derivative_identity(),
        'derivative_scalar_factor':derivative_scalar_factor(),
        'heaps_sublinear_scale':heaps_sublinear(),
        'fractional_power_equation_general':fractional_power()[0],
        'fractional_power_unique_general':fractional_power()[1],
    }


EXPECTED_INTERFACES = {'addition_preserves_strict_order': ('|- ( A + C ) < ( B + C )',
                                     ('|- A < B', '|- A e. RR', '|- B e. RR', '|- C e. RR')),
 'addition_preserves_weak_order': ('|- ( A + C ) <_ ( B + C )',
                                   ('|- A <_ B', '|- A e. RR', '|- B e. RR', '|- C e. RR')),
 'positive_scaling_preserves_strict_order': ('|- ( C x. A ) < ( C x. B )',
                                             ('|- A < B', '|- A e. RR', '|- B e. RR', '|- C e. RR+')),
 'positive_scaling_preserves_weak_order': ('|- ( C x. A ) <_ ( C x. B )',
                                           ('|- A <_ B', '|- A e. RR', '|- B e. RR', '|- C e. RR+')),
 'negative_scaling_reverses_strict_order': ('|- ( C x. B ) < ( C x. A )',
                                            ('|- A < B', '|- A e. RR', '|- B e. RR', '|- C < 0', '|- C e. RR')),
 'negative_scaling_reverses_weak_order': ('|- ( C x. B ) <_ ( C x. A )',
                                          ('|- A <_ B', '|- A e. RR', '|- B e. RR', '|- C < 0', '|- C e. RR')),
 'decreasing_exponential': ('|- ( D x. ( exp ` -u ( C x. B ) ) ) < ( D x. ( exp ` -u ( C x. A ) ) )',
                            ('|- A < B', '|- A e. RR', '|- B e. RR', '|- C e. RR+', '|- D e. RR+')),
 'growing_exponential_factor': ('|- ( exp ` ( -u C x. A ) ) < ( exp ` ( -u C x. B ) )',
                                ('|- A < B', '|- A e. RR', '|- B e. RR', '|- C < 0', '|- C e. RR')),
 'negative_parameter_argument': ('|- 0 < ( -u C x. N )', ('|- C < 0', '|- C e. RR', '|- N e. RR+')),
 'surprise_decreasing': ('|- ( -u ( log ` B ) / ( log ` 2 ) ) < ( -u ( log ` A ) / ( log ` 2 ) )',
                         ('|- A < B', '|- A e. RR+', '|- B e. RR')),
 'heaps_increasing': ('|- ( D x. ( A ^c C ) ) < ( D x. ( B ^c C ) )',
                      ('|- 0 <_ A', '|- A < B', '|- A e. RR', '|- B e. RR', '|- C e. RR+', '|- D e. RR+')),
 'zipf_decreasing': ('|- ( D x. ( B ^c -u C ) ) < ( D x. ( A ^c -u C ) )',
                     ('|- A < B', '|- A e. RR+', '|- B e. RR', '|- C e. RR+', '|- D e. RR+')),
 'derivative_sum': ('|- C ( RR _D ( F oF + G ) ) ( K + L )',
                    ('|- C ( RR _D F ) K', '|- C ( RR _D G ) L', '|- F : RR --> RR', '|- G : RR --> RR')),
 'derivative_composition': ('|- C ( RR _D ( F o. G ) ) ( K x. L )',
                            ('|- ( G ` C ) ( RR _D F ) K',
                             '|- C ( RR _D G ) L',
                             '|- F : RR --> RR',
                             '|- G : RR --> RR')),
 'derivative_constant': ('|- C ( RR _D ( RR X. { D } ) ) 0', ('|- C e. RR', '|- D e. RR')),
 'derivative_identity': ('|- C ( RR _D ( x e. RR |-> x ) ) 1', ('|- C e. RR',)),
 'derivative_scalar_factor': ('|- C ( RR _D ( ( RR X. { D } ) oF x. G ) ) ( D x. K )',
                              ('|- C ( RR _D G ) K', '|- C e. RR', '|- D e. RR', '|- G : RR --> RR', '|- K e. RR')),
 'heaps_sublinear_scale': ('|- ( D x. ( ( B x. A ) ^c C ) ) < ( B x. ( D x. ( A ^c C ) ) )',
                           ('|- 1 < B', '|- A e. RR+', '|- B e. RR', '|- C < 1', '|- C e. RR', '|- D e. RR+')),
 'fractional_power_equation_general': ('|- ( ( A ^c ( M / N ) ) ^ N ) = ( A ^ M )',
                                       ('|- A e. RR+', '|- M e. NN', '|- N e. NN')),
 'fractional_power_unique_general': ('|- Z = ( A ^c ( M / N ) )',
                                     ('|- ( Z ^ N ) = ( A ^ M )',
                                      '|- A e. RR+',
                                      '|- M e. NN',
                                      '|- N e. NN',
                                      '|- Z e. RR+'))}


def checks():
    results=[]
    certificates=raw_certificates()
    def check(name):
        formula,hypotheses=a.infer(certificates[name])
        expected,required=EXPECTED_INTERFACES[name]
        if formula!=expected or hypotheses!=frozenset(required):
            raise a.ProofError(('certificate_scope',name))
        results.append({'id':name,'passed':True,'formula':formula,'hypotheses':sorted(hypotheses)})
    check('addition_preserves_strict_order')
    check('addition_preserves_weak_order')
    check('positive_scaling_preserves_strict_order')
    check('positive_scaling_preserves_weak_order')
    check('negative_scaling_reverses_strict_order')
    check('negative_scaling_reverses_weak_order')
    check('decreasing_exponential')
    check('growing_exponential_factor')
    check('negative_parameter_argument')
    check('surprise_decreasing')
    check('heaps_increasing')
    check('zipf_decreasing')
    check('derivative_sum')
    check('derivative_composition')
    check('derivative_constant')
    check('derivative_identity')
    check('derivative_scalar_factor')
    check('heaps_sublinear_scale')
    check('fractional_power_equation_general')
    check('fractional_power_unique_general')
    return results


if __name__=='__main__':
    results=checks()
    print(json.dumps({'backend':'Python/Metamath','checks':len(results),'passed':True,'results':results}))
