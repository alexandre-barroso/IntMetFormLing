import json
import sys
from pathlib import Path

SCRIPTS_ROOT = Path(__file__).resolve().parents[1]
if str(SCRIPTS_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_ROOT))
from capitulo_07 import probabilidade_geral as p
from capitulo_07 import momentos_gerais as m


def translated(f, constant):
    return p.add_function(p.constant_function(constant), f)


def derive_translation(kernel):
    f, g = p.V('affine_left', p.FUNCTION), p.V('affine_right', p.FUNCTION)
    a, b = p.V('affine_left_constant', 'R'), p.V('affine_right_constant', 'R')
    point = p.V('affine_point', p.OMEGA)
    condition = p.integrable(f)
    shift = translated(f, a)
    value = p.Add(a, p.expectation(f))
    integral = p.apply(m.use(kernel, 'signed_integral_add', p.constant_function(a), f, a, p.expectation(f)), m.use(kernel, 'constant_signed_integral', a), p.hyp(condition))
    expected = m.expectation_from(kernel, shift, value, integral)
    kernel.theorem('expectation_after_constant_translation', p.alls((f, a), p.Imp(condition, p.Eq(p.expectation(shift), value))), p.close(expected, (f, a), (condition,)))
    shifted_center = m.centered(shift)
    original_center = m.centered(f)
    lhs = p.A(shifted_center, point)
    rhs = p.A(original_center, point)
    reduced = p.replace_subterm(p.normalize(lhs), p.expectation(shift), value)
    pointwise = p.ring(reduced, rhs)
    placeholder = p.V('shifted_mean_placeholder', 'R')
    template = p.replace_subterm(p.normalize(lhs), p.expectation(shift), placeholder)
    pointwise = ('eq_e', p.symmetric(p.expectation(shift), value, expected), placeholder, p.Eq(template, rhs), pointwise)
    equality = p.apply(m.literal(kernel, 'moment_function_extensionality', shifted_center, original_center), p.close(pointwise, (point,)))
    kernel.theorem('centered_function_unchanged_by_constant_translation', p.alls((f, a), p.Imp(condition, p.Eq(shifted_center, original_center))), p.close(equality, (f, a), (condition,)))
    conditions = (p.integrable(f), p.integrable(g))
    first = p.apply(p.ref('centered_function_unchanged_by_constant_translation', f, a), p.hyp(conditions[0]))
    second = p.apply(p.ref('centered_function_unchanged_by_constant_translation', g, b), p.hyp(conditions[1]))
    shifted_covariance = m.covariance(translated(f, a), translated(g, b))
    function_placeholder = p.V('centered_function_placeholder', p.FUNCTION)
    identity = ('eq_i', shifted_covariance)
    identity = ('eq_e', first, function_placeholder, p.Eq(shifted_covariance, p.expectation(p.product_function(function_placeholder, m.centered(translated(g, b))))), identity)
    identity = ('eq_e', second, function_placeholder, p.Eq(shifted_covariance, p.expectation(p.product_function(m.centered(f), function_placeholder))), identity)
    target = p.Eq(shifted_covariance, m.covariance(f, g))
    kernel.theorem('covariance_unchanged_by_constant_translation', p.alls((f, g, a, b), p.imps(conditions, target)), p.close(identity, (f, g, a, b), conditions))
    return kernel


def shared_statement():
    names = ('u', 'v', 'e', 'w', 'f')
    variables = {name: p.V('full_response_component_' + name, p.FUNCTION) for name in names}
    pairs = (('u', 'w'), ('u', 'f'), ('v', 'u'), ('v', 'w'), ('v', 'f'), ('e', 'u'), ('e', 'w'), ('e', 'f'))
    a, b = p.V('first_fixed_part', 'R'), p.V('second_fixed_part', 'R')
    conditions = tuple(p.square_integrable(variables[name]) for name in names) + tuple(p.independent_functions(variables[left], variables[right]) for left, right in pairs)
    u, v, e, w, f = (variables[name] for name in names)
    first, second = p.add_function(p.add_function(u, v), e), p.add_function(p.add_function(u, w), f)
    conclusion = p.Eq(m.covariance(translated(first, a), translated(second, b)), m.variance(u))
    return names, variables, pairs, a, b, conditions, first, second, conclusion


def derive_complete_responses(kernel):
    names, variables, pairs, a, b, conditions, first, second, target = shared_statement()
    hypotheses = tuple(p.hyp(condition) for condition in conditions)
    l2 = dict(zip(names, hypotheses[:5]))
    integrals = {name: m.l2_integral(kernel, variables[name], l2[name]) for name in names}
    def sum_integrable(selected, function):
        terms = [(p.RONE, variables[name], p.expectation(variables[name]), integrals[name]) for name in selected]
        raw, value, proof = m.linear_integral(kernel, terms)
        proof = m.signed(kernel, raw, value, proof, function)
        return m.integral_self_value(kernel, function, value, proof)
    first_integrable = sum_integrable(('u', 'v', 'e'), first)
    second_integrable = sum_integrable(('u', 'w', 'f'), second)
    translation = p.apply(p.ref('covariance_unchanged_by_constant_translation', first, second, a, b), first_integrable, second_integrable)
    shared = p.apply(p.ref('shared_participant_covariance_from_independence', *(variables[name] for name in names)), *hypotheses)
    proof = p.eq_trans(m.covariance(translated(first, a), translated(second, b)), m.covariance(first, second), m.variance(variables['u']), translation, shared)
    quantified = tuple(variables.values()) + (a, b)
    kernel.theorem('full_response_covariance_equals_shared_variance', p.alls(quantified, p.imps(conditions, target)), p.close(proof, quantified, conditions))
    return kernel


def derive_affine_moments(kernel):
    if 'shared_participant_covariance_from_independence' not in kernel.verified:
        raise ValueError('shared covariance must be derived before translation')
    derive_translation(kernel)
    derive_complete_responses(kernel)
    return kernel


def check(name, condition):
    if condition is not True:
        raise AssertionError(name)
    return {'id': name, 'passed': True}


def verify():
    kernel = m.verify_general_probability()['kernel']
    derive_affine_moments(kernel)
    records = {name: (name, formula, proof) for name, formula, proof in kernel.records}
    full = records['full_response_covariance_equals_shared_variance']
    names, variables, pairs, a, b, conditions, first, second, conclusion = shared_statement()
    expected = p.alls(tuple(variables.values()) + (a, b), p.imps(conditions, conclusion))
    results = [
        check('centered_functions_equal_after_fixed_translation', not kernel.verified['centered_function_unchanged_by_constant_translation'].assumptions),
        check('covariance_invariant_under_fixed_translation', not kernel.verified['covariance_unchanged_by_constant_translation'].assumptions),
        check('full_response_covariance_exact_hypotheses', p.same(full[1], expected) and not kernel.verified[full[0]].assumptions),
        check('no_translation_or_shared_result_assumed', not {'centered_function_unchanged_by_constant_translation', 'covariance_unchanged_by_constant_translation', 'shared_participant_covariance_from_independence', 'full_response_covariance_equals_shared_variance'} & set(kernel.axioms)),
        check('reject_each_removed_cross_independence', all(p.rejects(lambda i=i: kernel.theorem('invalid_removed_independence_' + str(i), m.remove_premise(full[1], i), full[2])) for i in range(5, 13))),
        check('reject_each_removed_square_integrability', all(p.rejects(lambda i=i: kernel.theorem('invalid_removed_l2_' + str(i), m.remove_premise(full[1], i), full[2])) for i in range(5))),
        check('reject_random_shift_as_fixed_constant', p.rejects(lambda: kernel.infer(p.ref('covariance_unchanged_by_constant_translation', first, second, variables['v'], b))))
    ]
    wrong = p.replace_subterm(full[1], m.variance(variables['u']), p.RZERO)
    results.append(check('reject_erasing_shared_variance', p.rejects(lambda: kernel.theorem('invalid_zero_shared_covariance', wrong, full[2]))))
    first_new = next(i for i, record in enumerate(kernel.records) if record[0] == 'expectation_after_constant_translation')
    return {'kernel': kernel, 'records': kernel.records[first_new:], 'results': results, 'target': expected}


if __name__ == '__main__':
    verification = verify()
    print(json.dumps({'backend': 'Python 3', 'results': verification['results'], 'derived': [record[0] for record in verification['records']], 'passed': all(result['passed'] for result in verification['results'])}, ensure_ascii=False))
