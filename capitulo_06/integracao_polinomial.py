from pathlib import Path
import sys
import json

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_02 import analise_geral as a


def h(formula):
    return a.assumption('|- ' + formula)


def imp(formula, proof):
    result = ('imp_intro', '|- ' + formula, proof)
    a.infer(result)
    return result


def discharge(proof, replacements):
    if isinstance(proof, tuple):
        if proof and proof[0] == 'assume' and proof[1] in replacements:
            return replacements[proof[1]]
        return tuple(discharge(item, replacements) for item in proof)
    return proof


def monomial_integral(exponent='N', coefficient='C'):
    X = '( A [,] B )'
    ar, br, order = h('A e. RR'), h('B e. RR'), h('A <_ B')
    nn, cc = h(exponent + ' e. NN0'), h(coefficient + ' e. CC')
    term = f'( x ^ {exponent} )'
    complex_function = f'( x e. CC |-> {term} )'
    function = f'( x e. {X} |-> {term} )'
    subset = a.mm('sstri', {'A': X, 'B': 'RR', 'C': 'CC'}, (a.mp(a.mm('iccssre'), a.both(ar, br)), a.mm('axresscn')))
    continuous = a.mp(a.mm('expcncf', {'N': exponent}), nn)
    continuous = a.mp(a.mp(a.mm('rescncf', {'A': 'CC', 'B': 'CC', 'C': X, 'F': complex_function}), subset), continuous)
    restriction = a.mp(a.mm('resmpt', {'x': 'x', 'A': 'CC', 'B': X, 'C': term}), subset)
    continuous = a.rewrite(restriction, continuous)
    integrable = a.mp(a.mm('cniccibl', {'F': function}), a.both(ar, br, continuous))
    term_exists = a.mm('ovex', {'A': 'x', 'B': exponent, 'F': '^'})
    condition = f'( T. /\\ x e. {X} )'
    scalar_hypotheses = (a.lift(cc), imp(condition, term_exists), a.lift(integrable))
    scalar = a.unlift(a.mm('itgmulc2', {'ph': 'T.', 'x': 'x', 'A': X, 'B': term, 'C': coefficient, 'V': '_V'}, scalar_hypotheses))
    scalar_integrable = a.unlift(a.mm('iblmulc2', {'ph': 'T.', 'x': 'x', 'A': X, 'B': term, 'C': coefficient, 'V': '_V'}, scalar_hypotheses))
    power = a.unlift(a.mm('itgpowd', {'ph': 'T.', 'N': exponent}, tuple(a.lift(p) for p in (ar, br, order, nn))))
    result = a.rewrite(power, a.eqsym(scalar))
    return {'integral': result, 'integrable': scalar_integrable}


def finite_polynomial_integral():
    X = '( A [,] B )'
    ar, br, order = h('A e. RR'), h('B e. RR'), h('A <_ B')
    finite, subset, coefficients = h('I e. Fin'), h('I C_ NN0'), h('F : I --> CC')
    condition = '( T. /\\ k e. I )'
    membership = ('and_elim', h(condition), 1)
    kn = a.mm('sselii', {'A': 'I', 'B': 'NN0', 'C': 'k'}, (subset, membership))
    value = '( F ` k )'
    vc = a.mp(a.mm('ffvelcdm', {'F': 'F', 'A': 'I', 'B': 'CC', 'C': 'k'}), a.both(coefficients, membership))
    monomial = monomial_integral('k', value)
    bindings = {'|- k e. NN0': kn, '|- ( F ` k ) e. CC': vc}
    integrable = discharge(monomial['integrable'], bindings)
    integral = discharge(monomial['integral'], bindings)
    term = f'( {value} x. ( x ^ k ) )'
    both_condition = f'( T. /\\ ( x e. {X} /\\ k e. I ) )'
    measurable = a.mp(a.mm('iccmbl'), a.both(ar, br))
    exists = a.mm('ovex', {'A': value, 'B': '( x ^ k )', 'F': 'x.'})
    total = a.unlift(a.mm('itgfsum', {'ph': 'T.', 'x': 'x', 'A': X, 'B': 'I', 'C': term, 'V': '_V'}, (
        a.lift(measurable), a.lift(finite), imp(both_condition, exists), imp(condition, integrable)
    )))
    evaluated = f'( {value} x. ( ( ( B ^ ( k + 1 ) ) - ( A ^ ( k + 1 ) ) ) / ( k + 1 ) ) )'
    sum_equality = a.unlift(a.mm('sumeq2dv', {'ph': 'T.', 'k': 'k', 'A': 'I', 'B': f'S. {X} {term} _d x', 'C': evaluated}, (imp(condition, integral),)))
    total_integral = ('and_elim', total, 1)
    result = a.rewrite(sum_equality, total_integral)
    expected = f'|- S. {X} sum_ k e. I {term} _d x = sum_ k e. I {evaluated}'
    hypotheses = frozenset({'|- A e. RR', '|- B e. RR', '|- A <_ B', '|- I e. Fin', '|- I C_ NN0', '|- F : I --> CC'})
    if a.infer(result) != (expected, hypotheses):
        raise a.ProofError(('finite_polynomial_integral_scope', a.infer(result)))
    return {'finite_polynomial_integrable': ('and_elim', total, 0), 'finite_polynomial_integral': result}


def integral_approximation_sandwich(fvalue='( F ` x )', gvalue='( G ` x )'):
    X = '( A [,] B )'
    ar, br, order, er = h('A e. RR'), h('B e. RR'), h('A <_ B'), h('E e. RR')
    fi = h(f'( x e. {X} |-> {fvalue} ) e. L^1')
    gi = h(f'( x e. {X} |-> {gvalue} ) e. L^1')
    bounds = f'( ( {fvalue} e. RR /\\ {gvalue} e. RR ) /\\ ( ( {fvalue} - E ) <_ {gvalue} /\\ {gvalue} <_ ( {fvalue} + E ) ) )'
    pointwise = h(f'A. x e. {X} {bounds}')
    condition = f'( T. /\\ x e. {X} )'
    membership = ('and_elim', h(condition), 1)
    values = ('rall_elim', pointwise, membership)
    fr = ('and_elim', ('and_elim', values, 0), 0)
    gr = ('and_elim', ('and_elim', values, 0), 1)
    left = ('and_elim', ('and_elim', values, 1), 0)
    right = ('and_elim', ('and_elim', values, 1), 1)
    ec = a.unlift(a.mm('recnd', {'ph': 'T.', 'A': 'E'}, (a.lift(er),)))
    subset = a.mm('sstri', {'A': X, 'B': 'RR', 'C': 'CC'}, (a.mp(a.mm('iccssre'), a.both(ar, br)), a.mm('axresscn')))
    constant_cn = a.mp(a.mm('cncfmptc', {'x': 'x', 'A': 'E', 'S': X, 'T': 'CC'}), a.both(ec, subset, a.mm('ssid', {'A': 'CC'})))
    ei = a.mp(a.mm('cniccibl', {'F': f'( x e. {X} |-> E )'}), a.both(ar, br, constant_cn))
    fex = a.mp(a.mm('elex', {'A': fvalue, 'B': 'RR'}), fr)
    eex = a.mp(a.mm('elex', {'A': 'E', 'B': 'RR'}), er)
    additive = (imp(condition, fex), a.lift(fi), imp(condition, eex), a.lift(ei))
    lower_fn, upper_fn = f'( {fvalue} - E )', f'( {fvalue} + E )'
    lower_i = a.unlift(a.mm('iblsub', {'ph': 'T.', 'x': 'x', 'A': X, 'B': fvalue, 'C': 'E', 'V': '_V'}, additive))
    upper_i = a.unlift(a.mm('ibladd', {'ph': 'T.', 'x': 'x', 'A': X, 'B': fvalue, 'C': 'E', 'V': '_V'}, additive))
    lower_r = a.mp(a.mm('resubcl', {'A': fvalue, 'B': 'E'}), a.both(fr, er))
    upper_r = a.mp(a.mm('readdcl', {'A': fvalue, 'B': 'E'}), a.both(fr, er))
    lower = a.unlift(a.mm('itgle', {'ph': 'T.', 'x': 'x', 'A': X, 'B': lower_fn, 'C': gvalue}, (a.lift(lower_i), a.lift(gi), imp(condition, lower_r), imp(condition, gr), imp(condition, left))))
    upper = a.unlift(a.mm('itgle', {'ph': 'T.', 'x': 'x', 'A': X, 'B': gvalue, 'C': upper_fn}, (a.lift(gi), a.lift(upper_i), imp(condition, gr), imp(condition, upper_r), imp(condition, right))))
    left_linear = a.unlift(a.mm('itgsub', {'ph': 'T.', 'x': 'x', 'A': X, 'B': fvalue, 'C': 'E', 'V': '_V'}, additive))
    right_linear = a.unlift(a.mm('itgadd', {'ph': 'T.', 'x': 'x', 'A': X, 'B': fvalue, 'C': 'E', 'V': '_V'}, additive))
    measurable = a.mp(a.mm('iccmbl'), a.both(ar, br))
    volume = a.mp(a.mm('volicc'), a.both(ar, br, order))
    width_real = a.mp(a.mm('resubcl', {'A': 'B', 'B': 'A'}), a.both(br, ar))
    volume_real = a.rewrite(a.eqsym(volume), width_real)
    constant_integral = a.mp(a.mm('itgconst', {'x': 'x', 'A': X, 'B': 'E'}), a.both(measurable, volume_real, ec))
    constant_integral = a.rewrite(volume, constant_integral)
    lower = a.rewrite(constant_integral, a.rewrite(left_linear, lower))
    upper = a.rewrite(constant_integral, a.rewrite(right_linear, upper))
    result = a.both(lower, upper)
    expected = f'|- ( ( S. {X} {fvalue} _d x - ( E x. ( B - A ) ) ) <_ S. {X} {gvalue} _d x /\\ S. {X} {gvalue} _d x <_ ( S. {X} {fvalue} _d x + ( E x. ( B - A ) ) ) )'
    hypotheses = frozenset(a.infer(p)[0] for p in (ar, br, order, er, fi, gi, pointwise))
    if a.infer(result) != (expected, hypotheses):
        raise a.ProofError(('integral_approximation_scope', a.infer(result)))
    return result


def gaussian_integrable():
    X = '( A [,] B )'
    ar, br = h('A e. RR'), h('B e. RR')
    subset = a.mm('sstri', {'A': X, 'B': 'RR', 'C': 'CC'}, (a.mp(a.mm('iccssre'), a.both(ar, br)), a.mm('axresscn')))
    def constant(value, proof, nonzero=False):
        target = '( CC \\ { 0 } )' if nonzero else 'CC'
        inclusion = a.mm('difss', {'A': 'CC', 'B': '{ 0 }'}) if nonzero else a.mm('ssid', {'A': 'CC'})
        return a.mp(a.mm('cncfmptc', {'x': 'x', 'A': value, 'S': X, 'T': target}), a.both(proof, subset, inclusion))
    def binary(label, left, right, lp, rp):
        return a.unlift(a.mm(label, {'ph': 'T.', 'x': 'x', 'X': X, 'A': left, 'B': right}, (a.lift(lp), a.lift(rp))))
    identity = a.mp(a.mm('cncfmptid', {'x': 'x', 'S': X, 'T': 'CC'}), a.both(subset, a.mm('ssid', {'A': 'CC'})))
    square = binary('mulcncf', 'x', 'x', identity, identity)
    negative = binary('subcncf', '0', '( x x. x )', constant('0', a.mm('0cn')), square)
    two_real = a.mp(a.mm('rpre', {'A': '2'}), a.mm('2rp'))
    two_complex = a.unlift(a.mm('recnd', {'ph': 'T.', 'A': '2'}, (a.lift(two_real),)))
    two_nonzero = a.mp(a.mm('rpne0', {'A': '2'}), a.mm('2rp'))
    two_member = ('iff_mp', a.mm('eldifsn', {'A': '2', 'B': 'CC', 'C': '0'}), a.both(two_complex, two_nonzero), 1)
    exponent = '( ( 0 - ( x x. x ) ) / 2 )'
    exp_cn = binary('divcncf', '( 0 - ( x x. x ) )', '2', negative, constant('2', two_member, True))
    gaussian = f'( exp ` {exponent} )'
    cn = a.unlift(a.mm('cncfmpt1f', {'ph': 'T.', 'x': 'x', 'X': X, 'F': 'exp', 'A': exponent}, (a.lift(a.mm('efcn')), a.lift(exp_cn))))
    integrable = a.mp(a.mm('cniccibl', {'F': f'( x e. {X} |-> {gaussian} )'}), a.both(ar, br, cn))
    expected = f'|- ( x e. {X} |-> {gaussian} ) e. L^1'
    if a.infer(integrable) != (expected, frozenset({'|- A e. RR', '|- B e. RR'})):
        raise a.ProofError(('gaussian_integrable_scope', a.infer(integrable)))
    return {'gaussian_continuous': cn, 'gaussian_integrable': integrable}


def gaussian_normalizer_outside_integral():
    from capitulo_06.fundamentos_pi import gaussian_normalizer
    normalizer = gaussian_normalizer()
    X = '( A [,] B )'
    ar, br = h('A e. RR'), h('B e. RR')
    root = '( sqrt ` ( 2 x. _pi ) )'
    coefficient = f'( 1 / {root} )'
    expression = '( exp ` ( ( 0 - ( x x. x ) ) / 2 ) )'
    function = f'( x e. {X} |-> {expression} )'
    facts = gaussian_integrable()
    condition = f'( T. /\\ x e. {X} )'
    membership = ('and_elim', h(condition), 1)
    root_complex = a.unlift(a.mm('recnd', {'ph': 'T.', 'A': root}, (a.lift(normalizer['gaussian_normalizer_real']),)))
    root_positive = ('iff_mp', a.mm('elrp', {'A': root}), a.both(normalizer['gaussian_normalizer_real'], normalizer['gaussian_normalizer_positive']), 1)
    root_nonzero = a.mp(a.mm('rpne0', {'A': root}), root_positive)
    coefficient_complex = a.mp(a.mm('reccl', {'A': root}), a.both(root_complex, root_nonzero))
    exists = a.mm('fvex', {'F': 'exp', 'A': '( ( 0 - ( x x. x ) ) / 2 )'})
    scalar = a.unlift(a.mm('itgmulc2', {'ph': 'T.', 'x': 'x', 'A': X, 'B': expression, 'C': coefficient, 'V': '_V'}, (a.lift(coefficient_complex), imp(condition, exists), a.lift(facts['gaussian_integrable']))))
    func = a.mp(a.mm('cncff', {'A': X, 'B': 'CC', 'F': function}), facts['gaussian_continuous'])
    value_complex = a.mp(a.mm('ffvelcdm', {'F': function, 'A': X, 'B': 'CC', 'C': 'x'}), a.both(func, membership))
    value = a.mp(a.mm('fvmpt2', {'x': 'x', 'A': X, 'B': expression, 'C': '_V', 'F': function}, (a.eqref(function),)), a.both(membership, exists))
    value_complex = a.mm('eqeltrri', {'A': f'( {function} ` x )', 'B': expression, 'C': 'CC'}, (value, value_complex))
    divide = a.mp(a.mm('divrec', {'A': expression, 'B': root}), a.both(value_complex, root_complex, root_nonzero))
    commute = a.mp(a.mm('mulcom', {'A': expression, 'B': coefficient}), a.both(value_complex, coefficient_complex))
    divide = a.rewrite(commute, divide)
    equality = a.unlift(a.mm('itgeq2dv', {'ph': 'T.', 'x': 'x', 'A': X, 'B': f'( {expression} / {root} )', 'C': f'( {coefficient} x. {expression} )'}, (imp(condition, divide),)))
    result = a.rewrite(a.eqsym(scalar), equality)
    expected = f'|- S. {X} ( {expression} / {root} ) _d x = ( {coefficient} x. S. {X} {expression} _d x )'
    if a.infer(result) != (expected, frozenset({'|- A e. RR', '|- B e. RR'})):
        raise a.ProofError(('gaussian_normalizer_scope', a.infer(result)))
    return result


def gaussian_standard_form_integral():
    X = '( A [,] B )'
    ar, br = h('A e. RR'), h('B e. RR')
    condition = f'( T. /\\ x e. {X} )'
    membership = ('and_elim', h(condition), 1)
    subset = a.mp(a.mm('iccssre'), a.both(ar, br))
    xr = a.mm('sselii', {'A': X, 'B': 'RR', 'C': 'x'}, (subset, membership))
    xc = a.unlift(a.mm('recnd', {'ph': 'T.', 'A': 'x'}, (a.lift(xr),)))
    equality = a.mp(a.mm('sqval', {'A': 'x'}), xc)
    left, right = '( x ^ 2 )', '( x x. x )'
    for operator, other, left_slot in [('-', '0', False), ('/', '2', True)]:
        if left_slot:
            equality = a.mp(a.mm('oveq1', {'A': left, 'B': right, 'C': other, 'F': operator}), equality)
            left, right = f'( {left} {operator} {other} )', f'( {right} {operator} {other} )'
        else:
            equality = a.mp(a.mm('oveq2', {'A': left, 'B': right, 'C': other, 'F': operator}), equality)
            left, right = f'( {other} {operator} {left} )', f'( {other} {operator} {right} )'
    equality = a.mp(a.mm('fveq2', {'A': left, 'B': right, 'F': 'exp'}), equality)
    left, right = f'( exp ` {left} )', f'( exp ` {right} )'
    root = '( sqrt ` ( 2 x. _pi ) )'
    equality = a.mp(a.mm('oveq1', {'A': left, 'B': right, 'C': root, 'F': '/'}), equality)
    left, right = f'( {left} / {root} )', f'( {right} / {root} )'
    integral = a.unlift(a.mm('itgeq2dv', {'ph': 'T.', 'x': 'x', 'A': X, 'B': left, 'C': right}, (imp(condition, equality),)))
    result = a.rewrite(gaussian_normalizer_outside_integral(), integral)
    expected = f'|- S. {X} {left} _d x = ( ( 1 / {root} ) x. S. {X} ( exp ` ( ( 0 - ( x x. x ) ) / 2 ) ) _d x )'
    if a.infer(result) != (expected, frozenset({'|- A e. RR', '|- B e. RR'})):
        raise a.ProofError(('gaussian_standard_form_scope', a.infer(result)))
    return result


if __name__ == '__main__':
    results = []
    proofs = finite_polynomial_integral()
    proofs['integral_approximation_sandwich'] = integral_approximation_sandwich()
    proofs.update(gaussian_integrable())
    proofs['gaussian_normalizer_outside_integral'] = gaussian_normalizer_outside_integral()
    proofs['gaussian_standard_form_integral'] = gaussian_standard_form_integral()
    for name, proof in proofs.items():
        formula, hypotheses = a.infer(proof)
        results.append({'id': name, 'formula': formula, 'hypotheses': sorted(hypotheses), 'passed': True})
    print(json.dumps({'backend': 'Python/independent-Metamath-kernel', 'passed': True, 'results': results}))
