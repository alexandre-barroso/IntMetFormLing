from dataclasses import dataclass
from fractions import Fraction
import itertools
import json
import sys
from pathlib import Path
import sympy as sp


def V(name, sort):
    return ('v', name, sort)


def C(name, sort):
    return ('c', name, sort)


def FT(domain, codomain):
    return ('fun', domain, codomain)


def A(function, *arguments):
    result = function
    for argument in arguments:
        result = ('app', result, argument)
    return result


def Lam(variable, body):
    return ('lam', variable, body)


def All(variable, body):
    return ('all', variable, body)


def Ex(variable, body):
    return ('ex', variable, body)


def Imp(left, right):
    return ('imp', left, right)


def And(left, right):
    return ('and', left, right)


def Or(left, right):
    return ('or', left, right)


def Eq(left, right):
    return ('eq', left, right)


def Iff(left, right):
    return And(Imp(left, right), Imp(right, left))


BOTTOM = ('false',)


def sort_of(term):
    if not isinstance(term, tuple) or not term:
        raise ValueError('malformed term')
    tag = term[0]
    if tag in ('v', 'c'):
        if len(term) != 3 or not isinstance(term[1], str):
            raise ValueError('malformed symbol')
        return term[2]
    if tag == 'app':
        if len(term) != 3:
            raise ValueError('malformed application')
        function_sort = sort_of(term[1])
        if not isinstance(function_sort, tuple) or len(function_sort) != 3 or function_sort[0] != 'fun' or function_sort[1] != sort_of(term[2]):
            raise ValueError('application type mismatch')
        return function_sort[2]
    if tag in ('lam', 'all', 'ex'):
        if len(term) != 3 or term[1][0] != 'v':
            raise ValueError('malformed binder')
        body_sort = sort_of(term[2])
        if tag == 'lam':
            return FT(sort_of(term[1]), body_sort)
        if body_sort != 'Prop':
            raise ValueError('quantified body is not a formula')
        return 'Prop'
    if tag in ('imp', 'and', 'or'):
        if len(term) != 3 or sort_of(term[1]) != 'Prop' or sort_of(term[2]) != 'Prop':
            raise ValueError('logical connective type mismatch')
        return 'Prop'
    if tag == 'eq':
        if len(term) != 3 or sort_of(term[1]) != sort_of(term[2]):
            raise ValueError('equality type mismatch')
        return 'Prop'
    if term == BOTTOM:
        return 'Prop'
    raise ValueError(('unknown term constructor', tag))


def free_variables(term):
    if term[0] == 'v':
        return frozenset([term])
    if term[0] in ('c', 'false'):
        return frozenset()
    if term[0] in ('lam', 'all', 'ex'):
        return free_variables(term[2]) - {term[1]}
    return frozenset().union(*(free_variables(child) for child in term[1:]))


def substitute(term, variable, replacement):
    if variable[0] != 'v' or sort_of(variable) != sort_of(replacement):
        raise ValueError('substitution type mismatch')
    if term == variable:
        return replacement
    if term[0] in ('v', 'c', 'false'):
        return term
    if term[0] in ('lam', 'all', 'ex'):
        binder, body = term[1:]
        if binder == variable:
            return term
        if binder in free_variables(replacement) and variable in free_variables(body):
            raise ValueError('capturing substitution')
        return (term[0], binder, substitute(body, variable, replacement))
    return (term[0], *(substitute(child, variable, replacement) for child in term[1:]))


def normalize(term):
    if term[0] in ('v', 'c', 'false'):
        return term
    if term[0] in ('lam', 'all', 'ex'):
        return (term[0], term[1], normalize(term[2]))
    reduced = (term[0], *(normalize(child) for child in term[1:]))
    if reduced[0] == 'app' and reduced[1][0] == 'lam':
        return normalize(substitute(reduced[1][2], reduced[1][1], reduced[2]))
    return reduced


def alpha_key(term, bound=()):
    if term[0] == 'v':
        return ('bound', bound[::-1].index(term), term[2]) if term in bound else term
    if term[0] in ('c', 'false'):
        return term
    if term[0] in ('lam', 'all', 'ex'):
        return (term[0], term[1][2], alpha_key(term[2], bound + (term[1],)))
    return (term[0], *(alpha_key(child, bound) for child in term[1:]))


def same(left, right):
    return alpha_key(normalize(left)) == alpha_key(normalize(right))


def atoms(formula):
    if formula[0] in ('imp', 'and', 'or'):
        return atoms(formula[1]) | atoms(formula[2])
    if formula == BOTTOM:
        return set()
    return {formula}


def boolean_value(formula, values):
    if formula == BOTTOM:
        return False
    if formula[0] == 'and':
        return boolean_value(formula[1], values) and boolean_value(formula[2], values)
    if formula[0] == 'or':
        return boolean_value(formula[1], values) or boolean_value(formula[2], values)
    if formula[0] == 'imp':
        return not boolean_value(formula[1], values) or boolean_value(formula[2], values)
    return values[formula]


def tautology(formula):
    components = sorted(atoms(formula), key=repr)
    if len(components) > 16:
        raise ValueError('propositional certificate too large')
    return all(boolean_value(formula, dict(zip(components, values))) for values in itertools.product((False, True), repeat=len(components)))


@dataclass(frozen=True)
class Sequent:
    assumptions: frozenset
    conclusion: tuple


class Kernel:
    def __init__(self, axioms):
        self.axioms = dict(axioms)
        self.verified = {}
        self.records = []
        for name, formula in self.axioms.items():
            if sort_of(formula) != 'Prop' or free_variables(formula):
                raise ValueError(('axiom must be a closed formula', name))

    def infer(self, proof, environment=None):
        environment = {} if environment is None else environment
        if not isinstance(proof, tuple) or not proof:
            raise ValueError('malformed proof')
        rule, *data = proof
        if rule == 'assume':
            formula, = data
            if sort_of(formula) != 'Prop':
                raise ValueError('assumption is not a formula')
            return Sequent(frozenset([formula]), formula)
        if rule == 'axiom':
            name, = data
            return Sequent(frozenset(), self.axioms[name])
        if rule == 'ref':
            name, = data
            return self.verified[name]
        if rule == 'local':
            name, = data
            return environment[name]
        if rule == 'let':
            name, value_proof, body_proof = data
            if name in environment:
                raise ValueError('duplicate local proof name')
            extended = dict(environment)
            extended[name] = self.infer(value_proof, environment)
            return self.infer(body_proof, extended)
        if rule == 'imp_i':
            assumption, body = data
            if sort_of(assumption) != 'Prop':
                raise ValueError('invalid discharged assumption')
            result = self.infer(body, environment)
            return Sequent(result.assumptions - {assumption}, Imp(assumption, result.conclusion))
        if rule == 'mp':
            implication, antecedent = (self.infer(item, environment) for item in data)
            if implication.conclusion[0] != 'imp' or not same(implication.conclusion[1], antecedent.conclusion):
                raise ValueError('modus ponens antecedent mismatch')
            return Sequent(implication.assumptions | antecedent.assumptions, implication.conclusion[2])
        if rule == 'and_i':
            left, right = (self.infer(item, environment) for item in data)
            return Sequent(left.assumptions | right.assumptions, And(left.conclusion, right.conclusion))
        if rule in ('and_l', 'and_r'):
            result = self.infer(data[0], environment)
            if result.conclusion[0] != 'and':
                raise ValueError('conjunction elimination on a non-conjunction')
            return Sequent(result.assumptions, result.conclusion[1 if rule == 'and_l' else 2])
        if rule in ('or_l', 'or_r'):
            other, body = data
            if sort_of(other) != 'Prop':
                raise ValueError('invalid disjunction')
            result = self.infer(body, environment)
            conclusion = Or(result.conclusion, other) if rule == 'or_l' else Or(other, result.conclusion)
            return Sequent(result.assumptions, conclusion)
        if rule == 'or_e':
            choice, left, right = (self.infer(item, environment) for item in data)
            if choice.conclusion[0] != 'or' or not same(left.conclusion, right.conclusion):
                raise ValueError('disjunction cases mismatch')
            remaining = (left.assumptions - {choice.conclusion[1]}) | (right.assumptions - {choice.conclusion[2]})
            return Sequent(choice.assumptions | remaining, left.conclusion)
        if rule == 'all_i':
            variable, body = data
            if variable[0] != 'v':
                raise ValueError('universal binder is not a variable')
            result = self.infer(body, environment)
            if any(variable in free_variables(hypothesis) for hypothesis in result.assumptions):
                raise ValueError('universal eigenvariable is not fresh')
            return Sequent(result.assumptions, All(variable, result.conclusion))
        if rule == 'all_e':
            body, replacement = data
            result = self.infer(body, environment)
            if result.conclusion[0] != 'all':
                raise ValueError('universal elimination on a non-universal')
            return Sequent(result.assumptions, substitute(result.conclusion[2], result.conclusion[1], replacement))
        if rule == 'ex_i':
            existential, witness, body = data
            if sort_of(existential) != 'Prop' or existential[0] != 'ex':
                raise ValueError('existential introduction target mismatch')
            result = self.infer(body, environment)
            instance = substitute(existential[2], existential[1], witness)
            if not same(instance, result.conclusion):
                raise ValueError('existential witness proves another formula')
            return Sequent(result.assumptions, existential)
        if rule == 'ex_e':
            existential_proof, eigenvariable, body_proof = data
            existential = self.infer(existential_proof, environment)
            body = self.infer(body_proof, environment)
            if existential.conclusion[0] != 'ex' or eigenvariable[0] != 'v':
                raise ValueError('invalid existential elimination')
            instance = substitute(existential.conclusion[2], existential.conclusion[1], eigenvariable)
            remaining = body.assumptions - {instance}
            protected = existential.assumptions | remaining | {body.conclusion, existential.conclusion}
            if any(eigenvariable in free_variables(item) for item in protected):
                raise ValueError('existential eigenvariable escapes')
            return Sequent(existential.assumptions | remaining, body.conclusion)
        if rule == 'eq_i':
            term, = data
            sort_of(term)
            return Sequent(frozenset(), Eq(term, term))
        if rule == 'eq_e':
            equality_proof, variable, pattern, instance_proof = data
            equality = self.infer(equality_proof, environment)
            instance = self.infer(instance_proof, environment)
            if equality.conclusion[0] != 'eq' or sort_of(pattern) != 'Prop':
                raise ValueError('invalid equality elimination')
            left, right = equality.conclusion[1:]
            if not same(substitute(pattern, variable, left), instance.conclusion):
                raise ValueError('equality replacement premise mismatch')
            return Sequent(equality.assumptions | instance.assumptions, substitute(pattern, variable, right))
        if rule == 'conversion':
            target, body = data
            if sort_of(target) != 'Prop':
                raise ValueError('conversion target is not a formula')
            result = self.infer(body, environment)
            if not same(target, result.conclusion):
                raise ValueError('non-definitional conversion')
            return Sequent(result.assumptions, target)
        if rule == 'false_e':
            target, body = data
            result = self.infer(body, environment)
            if result.conclusion != BOTTOM or sort_of(target) != 'Prop':
                raise ValueError('false elimination lacks contradiction')
            return Sequent(result.assumptions, target)
        if rule == 'ring':
            formula, = data
            if sort_of(formula) != 'Prop' or formula[0] != 'eq' or sort_of(formula[1]) != 'R' or not ring_identity(formula[1], formula[2]):
                raise ValueError('invalid real polynomial identity')
            return Sequent(frozenset(), formula)
        if rule == 'tautology':
            formula, = data
            if sort_of(formula) != 'Prop' or not tautology(formula):
                raise ValueError('invalid propositional tautology')
            return Sequent(frozenset(), formula)
        if rule == 'nat_induction':
            variable, body, base_proof, step_proof = data
            if variable[0] != 'v' or sort_of(variable) != 'N' or sort_of(body) != 'Prop':
                raise ValueError('invalid induction predicate')
            base, step = self.infer(base_proof, environment), self.infer(step_proof, environment)
            zero = C('zero_nat', 'N')
            successor = A(C('successor', FT('N', 'N')), variable)
            expected_step = All(variable, Imp(body, substitute(body, variable, successor)))
            if not same(base.conclusion, substitute(body, variable, zero)) or not same(step.conclusion, expected_step):
                raise ValueError('induction base or step mismatch')
            assumptions = base.assumptions | step.assumptions
            if any(variable in free_variables(item) for item in assumptions):
                raise ValueError('induction variable occurs in open assumptions')
            return Sequent(assumptions, All(variable, body))
        if rule == 'list_induction':
            variable, head, tail, body, base_proof, step_proof = data
            list_sort = sort_of(variable)
            if variable[0] != 'v' or not isinstance(list_sort, tuple) or len(list_sort) != 2 or list_sort[0] != 'List' or sort_of(head) != list_sort[1] or sort_of(tail) != list_sort or head[0] != 'v' or tail[0] != 'v' or len({variable, head, tail}) != 3 or sort_of(body) != 'Prop':
                raise ValueError('invalid list induction variables')
            if head in free_variables(body) or tail in free_variables(body):
                raise ValueError('list induction variables are not fresh')
            base, step = self.infer(base_proof, environment), self.infer(step_proof, environment)
            nil = C('list_nil', list_sort)
            cons = A(C('list_cons', FT(list_sort[1], FT(list_sort, list_sort))), head, tail)
            expected_step = All(head, All(tail, Imp(substitute(body, variable, tail), substitute(body, variable, cons))))
            if not same(base.conclusion, substitute(body, variable, nil)) or not same(step.conclusion, expected_step):
                raise ValueError('list induction base or step mismatch')
            assumptions = base.assumptions | step.assumptions
            if any({variable, head, tail} & free_variables(item) for item in assumptions):
                raise ValueError('list induction variable occurs in open assumptions')
            return Sequent(assumptions, All(variable, body))
        raise ValueError(('unrecognized proof rule', rule))

    def theorem(self, name, formula, proof):
        if name in self.verified or name in self.axioms:
            raise ValueError('duplicate theorem name')
        if sort_of(formula) != 'Prop' or free_variables(formula):
            raise ValueError('theorem must be closed')
        result = self.infer(proof)
        if result.assumptions or not same(result.conclusion, formula):
            raise ValueError(('theorem has open hypotheses or another conclusion', name, result))
        self.verified[name] = Sequent(frozenset(), formula)
        self.records.append((name, formula, proof))
        return ('ref', name)


def instantiate(proof, *terms):
    for term in terms:
        proof = ('all_e', proof, term)
    return proof


def apply(proof, *premises):
    for premise in premises:
        proof = ('mp', proof, premise)
    return proof


def close(proof, variables=(), assumptions=()):
    for assumption in reversed(assumptions):
        proof = ('imp_i', assumption, proof)
    for variable in reversed(variables):
        proof = ('all_i', variable, proof)
    return proof


def rejects(call):
    try:
        call()
    except (ValueError, KeyError, TypeError, IndexError):
        return True
    return False


def alls(variables, formula):
    for variable in reversed(variables):
        formula = All(variable, formula)
    return formula


def imps(assumptions, formula):
    for assumption in reversed(assumptions):
        formula = Imp(assumption, formula)
    return formula


RZERO = C('zero_real', 'R')
RONE = C('one_real', 'R')
NZERO = C('zero_nat', 'N')
RLE = C('real_le', FT('R', FT('R', 'Prop')))
RLT = C('real_lt', FT('R', FT('R', 'Prop')))
RMUL = C('real_mul', FT('R', FT('R', 'R')))
RADD = C('real_add', FT('R', FT('R', 'R')))
RSUB = C('real_sub', FT('R', FT('R', 'R')))
RDIV = C('real_div', FT('R', FT('R', 'R')))
NLE = C('nat_le', FT('N', FT('N', 'Prop')))
NMAX = C('nat_max', FT('N', FT('N', 'N')))


def Le(left, right):
    return A(RLE, left, right)


def Lt(left, right):
    return A(RLT, left, right)


def Mul(left, right):
    return A(RMUL, left, right)


def Add(left, right):
    return A(RADD, left, right)


def Sub(left, right):
    return A(RSUB, left, right)


def Div(left, right):
    return A(RDIV, left, right)


def lub(sequence, value):
    index = V('lub_index', 'N')
    bound = V('lub_bound', 'R')
    return And(All(index, Le(A(sequence, index), value)), All(bound, Imp(All(index, Le(A(sequence, index), bound)), Le(value, bound))))


def increasing(sequence):
    left, right = V('increasing_left', 'N'), V('increasing_right', 'N')
    return alls((left, right), Imp(A(NLE, left, right), Le(A(sequence, left), A(sequence, right))))


def nonnegative_sequence(sequence):
    index = V('nonnegative_index', 'N')
    return All(index, Le(RZERO, A(sequence, index)))


def field_axioms():
    x, y, z, t = (V(name, 'R') for name in ('x', 'y', 'z', 't'))
    i, j = V('i', 'N'), V('j', 'N')
    return {
        'real_order_reflexive': alls((x,), Le(x, x)),
        'real_order_transitive': alls((x, y, z), imps((Le(x, y), Le(y, z)), Le(x, z))),
        'real_order_antisymmetric': alls((x, y), imps((Le(x, y), Le(y, x)), Eq(x, y))),
        'positive_implies_nonnegative': alls((x,), Imp(Lt(RZERO, x), Le(RZERO, x))),
        'nonnegative_zero_or_positive': alls((x,), Imp(Le(RZERO, x), Or(Eq(x, RZERO), Lt(RZERO, x)))),
        'nonnegative_multiplication_monotone': alls((x, y, z), imps((Le(RZERO, x), Le(y, z)), Le(Mul(x, y), Mul(x, z)))),
        'positive_division_forward': alls((x, y, z), imps((Lt(RZERO, x), Le(Mul(x, y), z)), Le(y, Div(z, x)))),
        'positive_division_backward': alls((x, y, z), imps((Lt(RZERO, x), Le(y, Div(z, x))), Le(Mul(x, y), z))),
        'multiplication_zero': alls((x,), Eq(Mul(RZERO, x), RZERO)),
        'multiplication_commutative': alls((x, y), Eq(Mul(x, y), Mul(y, x))),
        'addition_monotone': alls((x, y, z, t), imps((Le(x, y), Le(z, t)), Le(Add(x, z), Add(y, t)))),
        'addition_right_forward': alls((x, y, z), Imp(Le(Add(x, y), z), Le(x, Sub(z, y)))),
        'addition_right_backward': alls((x, y, z), Imp(Le(x, Sub(z, y)), Le(Add(x, y), z))),
        'addition_left_forward': alls((x, y, z), Imp(Le(Add(x, y), z), Le(y, Sub(z, x)))),
        'addition_left_backward': alls((x, y, z), Imp(Le(y, Sub(z, x)), Le(Add(x, y), z))),
        'real_order_not_reverse_strict': alls((x, y), Imp(Imp(Lt(y, x), BOTTOM), Le(x, y))),
        'real_strict_nonstrict_inconsistent': alls((x, y), imps((Lt(x, y), Le(y, x)), BOTTOM)),
        'ordered_field_gap_witness': alls((x, y), Imp(Lt(y, x), Ex(t, And(And(Lt(RZERO, t), Lt(t, RONE)), Lt(y, Mul(t, x)))))),
        'natural_maximum_left': alls((i, j), A(NLE, i, A(NMAX, i, j))),
        'natural_maximum_right': alls((i, j), A(NLE, j, A(NMAX, i, j)))
    }


def ax(name, *terms):
    return instantiate(('axiom', name), *terms)


def ref(name, *terms):
    return instantiate(('ref', name), *terms)


def hyp(formula):
    return ('assume', formula)


def upper_bound(proof, index):
    return instantiate(('and_l', proof), index)


def least_bound(proof, bound, bound_proof):
    return apply(instantiate(('and_r', proof), bound), bound_proof)


def symmetric(left, right, proof):
    occupied = free_variables(left) | free_variables(right)
    index = 0
    variable = V('equality_placeholder_' + str(index), sort_of(left))
    while variable in occupied:
        index += 1
        variable = V('equality_placeholder_' + str(index), sort_of(left))
    return ('eq_e', proof, variable, Eq(variable, left), ('eq_i', left))


def derived_order_certificates():
    kernel = Kernel(field_axioms())
    sequence = V('sequence', FT('N', 'R'))
    value, multiplier, bound = (V(name, 'R') for name in ('value', 'multiplier', 'bound'))
    index = V('index', 'N')
    scaled = Lam(index, Mul(multiplier, A(sequence, index)))
    has_lub, positive = lub(sequence, value), Lt(RZERO, multiplier)
    nonnegative = apply(ax('positive_implies_nonnegative', multiplier), hyp(positive))
    up = apply(ax('nonnegative_multiplication_monotone', multiplier, A(sequence, index), value), nonnegative, upper_bound(hyp(has_lub), index))
    up = ('conversion', Le(A(scaled, index), Mul(multiplier, value)), up)
    up = close(up, (index,))
    bound_hypothesis = All(index, Le(A(scaled, index), bound))
    point = ('conversion', Le(Mul(multiplier, A(sequence, index)), bound), instantiate(hyp(bound_hypothesis), index))
    divided = apply(ax('positive_division_forward', multiplier, A(sequence, index), bound), hyp(positive), point)
    lower = least_bound(hyp(has_lub), Div(bound, multiplier), close(divided, (index,)))
    lower = apply(ax('positive_division_backward', multiplier, value, bound), hyp(positive), lower)
    lower = close(lower, (bound,), (bound_hypothesis,))
    statement = alls((sequence, value, multiplier), imps((positive, has_lub), lub(scaled, Mul(multiplier, value))))
    proof = close(('and_i', up, lower), (sequence, value, multiplier), (positive, has_lub))
    kernel.theorem('positive_scalar_preserves_lub', statement, proof)
    nonnegative_hypothesis = Le(RZERO, multiplier)
    zero_case = Eq(multiplier, RZERO)
    zero_scaled = substitute(scaled, multiplier, RZERO)
    zero_up = ax('multiplication_zero', A(sequence, index))
    placeholder = V('placeholder', 'R')
    zero_up = ('eq_e', zero_up, placeholder, Le(A(zero_scaled, index), placeholder), ax('real_order_reflexive', Mul(RZERO, A(sequence, index))))
    zero_up = close(zero_up, (index,))
    zero_bound = All(index, Le(A(zero_scaled, index), bound))
    zero_lower = instantiate(hyp(zero_bound), NZERO)
    zero_lower = ('eq_e', ax('multiplication_zero', A(sequence, NZERO)), placeholder, Le(placeholder, bound), zero_lower)
    zero_lower = close(zero_lower, (bound,), (zero_bound,))
    zero_lub = ('and_i', zero_up, zero_lower)
    reversed_product_zero = symmetric(Mul(RZERO, value), RZERO, ax('multiplication_zero', value))
    zero_lub = ('eq_e', reversed_product_zero, placeholder, lub(zero_scaled, placeholder), zero_lub)
    inverse_zero = symmetric(multiplier, RZERO, hyp(zero_case))
    zero_conclusion = ('eq_e', inverse_zero, placeholder, lub(Lam(index, Mul(placeholder, A(sequence, index))), Mul(placeholder, value)), zero_lub)
    positive_conclusion = apply(ref('positive_scalar_preserves_lub', sequence, value, multiplier), hyp(positive), hyp(has_lub))
    cases = apply(ax('nonnegative_zero_or_positive', multiplier), hyp(nonnegative_hypothesis))
    proof = ('or_e', cases, zero_conclusion, positive_conclusion)
    statement = alls((sequence, value, multiplier), imps((nonnegative_hypothesis, has_lub), lub(scaled, Mul(multiplier, value))))
    kernel.theorem('nonnegative_scalar_preserves_lub', statement, close(proof, (sequence, value, multiplier), (nonnegative_hypothesis, has_lub)))
    x, y, z, t = (V(name, 'R') for name in ('left_factor', 'right_factor', 'left_upper', 'right_upper'))
    conditions = (Le(RZERO, x), Le(RZERO, t), Le(x, z), Le(y, t))
    first = apply(ax('nonnegative_multiplication_monotone', x, y, t), hyp(conditions[0]), hyp(conditions[3]))
    second = apply(ax('nonnegative_multiplication_monotone', t, x, z), hyp(conditions[1]), hyp(conditions[2]))
    second = ('eq_e', ax('multiplication_commutative', t, x), placeholder, Le(placeholder, Mul(t, z)), second)
    second = ('eq_e', ax('multiplication_commutative', t, z), placeholder, Le(Mul(x, t), placeholder), second)
    result = apply(ax('real_order_transitive', Mul(x, y), Mul(x, t), Mul(z, t)), first, second)
    statement = alls((x, y, z, t), imps(conditions, Le(Mul(x, y), Mul(z, t))))
    kernel.theorem('nonnegative_product_monotone', statement, close(result, (x, y, z, t), conditions))
    a, b = V('a_sequence', FT('N', 'R')), V('b_sequence', FT('N', 'R'))
    av, bv = V('a_supremum', 'R'), V('b_supremum', 'R')
    i, j = V('first_index', 'N'), V('second_index', 'N')
    conditions = (lub(a, av), lub(b, bv), increasing(a), increasing(b), nonnegative_sequence(a), nonnegative_sequence(b))
    has_a, has_b, inc_a, inc_b, nonneg_a, nonneg_b = map(hyp, conditions)
    bv_nonnegative = apply(ax('real_order_transitive', RZERO, A(b, NZERO), bv), instantiate(nonneg_b, NZERO), upper_bound(has_b, NZERO))
    product = Lam(index, Mul(A(a, index), A(b, index)))
    up = apply(ref('nonnegative_product_monotone', A(a, index), A(b, index), av, bv), instantiate(nonneg_a, index), bv_nonnegative, upper_bound(has_a, index), upper_bound(has_b, index))
    up = close(('conversion', Le(A(product, index), Mul(av, bv)), up), (index,))
    bound_hypothesis = All(index, Le(A(product, index), bound))
    common = A(NMAX, i, j)
    a_le = apply(instantiate(inc_a, i, common), ax('natural_maximum_left', i, j))
    b_le = apply(instantiate(inc_b, j, common), ax('natural_maximum_right', i, j))
    cross_le = apply(ref('nonnegative_product_monotone', A(a, i), A(b, j), A(a, common), A(b, common)), instantiate(nonneg_a, i), instantiate(nonneg_b, common), a_le, b_le)
    point_bound = ('conversion', Le(Mul(A(a, common), A(b, common)), bound), instantiate(hyp(bound_hypothesis), common))
    cross_bound = apply(ax('real_order_transitive', Mul(A(a, i), A(b, j)), Mul(A(a, common), A(b, common)), bound), cross_le, point_bound)
    scalar_b = apply(ref('nonnegative_scalar_preserves_lub', b, bv, A(a, i)), instantiate(nonneg_a, i), has_b)
    lower_b = least_bound(scalar_b, bound, close(cross_bound, (j,)))
    lower_b = ('eq_e', ax('multiplication_commutative', A(a, i), bv), placeholder, Le(placeholder, bound), lower_b)
    scalar_a = apply(ref('nonnegative_scalar_preserves_lub', a, av, bv), bv_nonnegative, has_a)
    lower_a = least_bound(scalar_a, bound, close(lower_b, (i,)))
    lower_a = ('eq_e', ax('multiplication_commutative', bv, av), placeholder, Le(placeholder, bound), lower_a)
    lower = close(lower_a, (bound,), (bound_hypothesis,))
    statement = alls((a, b, av, bv), imps(conditions, lub(product, Mul(av, bv))))
    kernel.theorem('increasing_nonnegative_product_lub', statement, close(('and_i', up, lower), (a, b, av, bv), conditions))
    sum_conditions = conditions[:4]
    sum_sequence = Lam(index, Add(A(a, index), A(b, index)))
    up = apply(ax('addition_monotone', A(a, index), av, A(b, index), bv), upper_bound(has_a, index), upper_bound(has_b, index))
    up = close(('conversion', Le(A(sum_sequence, index), Add(av, bv)), up), (index,))
    sum_bound_hypothesis = All(index, Le(A(sum_sequence, index), bound))
    cross_le = apply(ax('addition_monotone', A(a, i), A(a, common), A(b, j), A(b, common)), a_le, b_le)
    point_bound = ('conversion', Le(Add(A(a, common), A(b, common)), bound), instantiate(hyp(sum_bound_hypothesis), common))
    cross_bound = apply(ax('real_order_transitive', Add(A(a, i), A(b, j)), Add(A(a, common), A(b, common)), bound), cross_le, point_bound)
    lower_b = apply(ax('addition_left_forward', A(a, i), A(b, j), bound), cross_bound)
    lower_b = least_bound(has_b, Sub(bound, A(a, i)), close(lower_b, (j,)))
    lower_b = apply(ax('addition_left_backward', A(a, i), bv, bound), lower_b)
    lower_a = apply(ax('addition_right_forward', A(a, i), bv, bound), lower_b)
    lower_a = least_bound(has_a, Sub(bound, bv), close(lower_a, (i,)))
    lower_a = apply(ax('addition_right_backward', av, bv, bound), lower_a)
    lower = close(lower_a, (bound,), (sum_bound_hypothesis,))
    statement = alls((a, b, av, bv), imps(sum_conditions, lub(sum_sequence, Add(av, bv))))
    kernel.theorem('increasing_sum_lub', statement, close(('and_i', up, lower), (a, b, av, bv), sum_conditions))
    t = V('fraction', 'R')
    fraction = And(Lt(RZERO, t), Lt(t, RONE))
    all_scaled_bounds = All(t, Imp(fraction, Le(Mul(t, value), bound)))
    opposite = Lt(bound, value)
    witness_exists = apply(ax('ordered_field_gap_witness', value, bound), hyp(opposite))
    witness_body = And(fraction, Lt(bound, Mul(t, value)))
    witness_bound = apply(instantiate(hyp(all_scaled_bounds), t), ('and_l', hyp(witness_body)))
    contradiction = apply(ax('real_strict_nonstrict_inconsistent', bound, Mul(t, value)), ('and_r', hyp(witness_body)), witness_bound)
    contradiction = ('ex_e', witness_exists, t, contradiction)
    result = apply(ax('real_order_not_reverse_strict', value, bound), close(contradiction, assumptions=(opposite,)))
    statement = alls((value, bound), Imp(all_scaled_bounds, Le(value, bound)))
    kernel.theorem('unit_fraction_bounds_determine_order', statement, close(result, (value, bound), (all_scaled_bounds,)))
    return kernel


OMEGA = 'Omega'
FUNCTION = FT(OMEGA, 'R')
SIMPLE_HEAD = ('Pair', 'R', FT(OMEGA, 'Prop'))
SIMPLE = ('List', SIMPLE_HEAD)
SIMPLE_SEQUENCE = FT('N', SIMPLE)
SIMPLE_VALUE = C('simple_value', FT(SIMPLE, FUNCTION))
SIMPLE_INTEGRAL = C('simple_integral', FT(SIMPLE, 'R'))
SIMPLE_SCALE = C('simple_scale', FT('R', FT(SIMPLE, SIMPLE)))
CUT = C('threshold_cut', FT(SIMPLE_SEQUENCE, FT(SIMPLE, FT('R', FT('N', SIMPLE)))))


def si(simple):
    return A(SIMPLE_INTEGRAL, simple)


def simple_value(simple):
    return A(SIMPLE_VALUE, simple)


def simple_below(simple, function):
    point = V('simple_order_point', OMEGA)
    return All(point, Le(A(simple_value(simple), point), A(function, point)))


def simple_nonnegative(simple):
    point = V('simple_nonnegative_point', OMEGA)
    return All(point, Le(RZERO, A(simple_value(simple), point)))


def integral_bound(function, bound):
    simple = V('integral_test_simple', SIMPLE)
    return All(simple, Imp(And(simple_nonnegative(simple), simple_below(simple, function)), Le(si(simple), bound)))


def has_integral(function, value):
    bound = V('integral_test_bound', 'R')
    return And(integral_bound(function, value), All(bound, Imp(integral_bound(function, bound), Le(value, bound))))


def simple_monotonicity():
    left, right = V('simple_left', SIMPLE), V('simple_right', SIMPLE)
    return alls((left, right), Imp(simple_below(left, simple_value(right)), Le(si(left), si(right))))


def simple_scaling():
    scalar, simple = V('simple_scalar', 'R'), V('scaled_simple', SIMPLE)
    return alls((scalar, simple), Eq(si(A(SIMPLE_SCALE, scalar, simple)), Mul(scalar, si(simple))))


def cut_cofinality(sequence, function):
    simple, scalar, index = V('cut_simple', SIMPLE), V('cut_fraction', 'R'), V('cut_index', 'N')
    fraction = And(Lt(RZERO, scalar), Lt(scalar, RONE))
    cuts = Lam(index, si(A(CUT, sequence, simple, scalar, index)))
    scaled_cut_below = All(index, simple_below(A(SIMPLE_SCALE, scalar, A(CUT, sequence, simple, scalar, index)), simple_value(A(sequence, index))))
    return All(simple, Imp(And(simple_nonnegative(simple), simple_below(simple, function)), All(scalar, Imp(fraction, And(lub(cuts, si(simple)), scaled_cut_below)))))


def derive_simple_limit_bound(kernel):
    sequence, function = V('simple_approximation', SIMPLE_SEQUENCE), V('limit_function', FUNCTION)
    bound = V('common_integral_bound', 'R')
    simple, scalar, index = V('test_simple', SIMPLE), V('test_fraction', 'R'), V('stage', 'N')
    monotone_integral, scaling, cofinal = simple_monotonicity(), simple_scaling(), cut_cofinality(sequence, function)
    bounds = All(index, Le(si(A(sequence, index)), bound))
    below = And(simple_nonnegative(simple), simple_below(simple, function))
    fraction = And(Lt(RZERO, scalar), Lt(scalar, RONE))
    cut_info = apply(instantiate(apply(instantiate(hyp(cofinal), simple), hyp(below)), scalar), hyp(fraction))
    cut = A(CUT, sequence, simple, scalar, index)
    cuts = Lam(index, si(cut))
    scaled_below = instantiate(('and_r', cut_info), index)
    scaled_bound = apply(instantiate(hyp(monotone_integral), A(SIMPLE_SCALE, scalar, cut), A(sequence, index)), scaled_below)
    scaled_bound = apply(ax('real_order_transitive', si(A(SIMPLE_SCALE, scalar, cut)), si(A(sequence, index)), bound), scaled_bound, instantiate(hyp(bounds), index))
    placeholder = V('scaled_integral_placeholder', 'R')
    scaled_bound = ('eq_e', instantiate(hyp(scaling), scalar, cut), placeholder, Le(placeholder, bound), scaled_bound)
    scaled_lub = apply(ref('positive_scalar_preserves_lub', cuts, si(simple), scalar), ('and_l', hyp(fraction)), ('and_l', cut_info))
    least = least_bound(scaled_lub, bound, close(scaled_bound, (index,)))
    all_fractions = close(least, (scalar,), (fraction,))
    unscaled_bound = apply(ref('unit_fraction_bounds_determine_order', si(simple), bound), all_fractions)
    conclusion = close(unscaled_bound, (simple,), (below,))
    conditions = (monotone_integral, scaling, cofinal, bounds)
    statement = alls((sequence, function, bound), imps(conditions, integral_bound(function, bound)))
    kernel.theorem('simple_limit_bound_from_threshold_cuts', statement, close(conclusion, (sequence, function, bound), conditions))
    return kernel


EVENT = FT(OMEGA, 'Prop')
EVENT_SEQUENCE = FT('N', EVENT)
MEASURABLE = C('measurable_event', FT(EVENT, 'Prop'))
MEASURE = C('probability_measure', FT(EVENT, 'R'))
PREFIX = C('finite_union_prefix', FT(EVENT_SEQUENCE, FT('N', EVENT)))
SUCCESSOR = C('successor', FT('N', 'N'))


def empty_event():
    point = V('empty_event_point', OMEGA)
    return Lam(point, BOTTOM)


def event_union(left, right):
    point = V('union_event_point', OMEGA)
    return Lam(point, Or(A(left, point), A(right, point)))


def event_difference(left, right):
    point = V('difference_event_point', OMEGA)
    return Lam(point, And(A(left, point), Imp(A(right, point), BOTTOM)))


def event_subset(left, right):
    point = V('subset_event_point', OMEGA)
    return All(point, Imp(A(left, point), A(right, point)))


def event_disjoint(left, right):
    point = V('disjoint_event_point', OMEGA)
    return All(point, Imp(And(A(left, point), A(right, point)), BOTTOM))


def prefix_sequence(sequence):
    index = V('prefix_index', 'N')
    return Lam(index, A(PREFIX, sequence, index))


def supremum_event(sequence):
    index, point = V('union_index', 'N'), V('union_point', OMEGA)
    return Lam(point, Ex(index, A(A(sequence, index), point)))


def countable_union(sequence):
    return supremum_event(prefix_sequence(sequence))


def disjointification(sequence):
    index = V('difference_index', 'N')
    return Lam(index, event_difference(A(sequence, index), A(PREFIX, sequence, index)))


def measurable_sequence(sequence):
    index = V('measurable_sequence_index', 'N')
    return All(index, A(MEASURABLE, A(sequence, index)))


def disjoint_sequence(sequence):
    index = V('disjoint_sequence_index', 'N')
    return All(index, event_disjoint(A(sequence, index), A(PREFIX, sequence, index)))


def event_increasing(sequence):
    first, last = V('event_first_index', 'N'), V('event_last_index', 'N')
    return alls((first, last), Imp(A(NLE, first, last), event_subset(A(sequence, first), A(sequence, last))))


def measured_prefix_sequence(sequence):
    index = V('measured_prefix_index', 'N')
    return Lam(index, A(MEASURE, A(PREFIX, sequence, index)))


def measured_sequence(sequence):
    index = V('measured_sequence_index', 'N')
    return Lam(index, A(MEASURE, A(sequence, index)))


def measure_axioms():
    left, right = V('event_left', EVENT), V('event_right', EVENT)
    sequence, index = V('event_sequence', EVENT_SEQUENCE), V('event_index', 'N')
    point = V('event_point', OMEGA)
    family_left, family_right = V('family_left', EVENT_SEQUENCE), V('family_right', EVENT_SEQUENCE)
    empty = empty_event()
    return {
        'event_extensionality': alls((left, right), Imp(All(point, Iff(A(left, point), A(right, point))), Eq(left, right))),
        'event_sequence_extensionality': alls((family_left, family_right), Imp(All(index, Eq(A(family_left, index), A(family_right, index))), Eq(family_left, family_right))),
        'finite_union_prefix_zero': All(sequence, Eq(A(PREFIX, sequence, NZERO), empty)),
        'finite_union_prefix_successor': alls((sequence, index), Eq(A(PREFIX, sequence, A(SUCCESSOR, index)), event_union(A(PREFIX, sequence, index), A(sequence, index)))),
        'sigma_algebra_empty': A(MEASURABLE, empty),
        'sigma_algebra_finite_union': alls((left, right), imps((A(MEASURABLE, left), A(MEASURABLE, right)), A(MEASURABLE, event_union(left, right)))),
        'sigma_algebra_difference': alls((left, right), imps((A(MEASURABLE, left), A(MEASURABLE, right)), A(MEASURABLE, event_difference(left, right)))),
        'sigma_algebra_countable_union': All(sequence, Imp(measurable_sequence(sequence), A(MEASURABLE, countable_union(sequence)))),
        'measure_nonnegative': All(left, Imp(A(MEASURABLE, left), Le(RZERO, A(MEASURE, left)))),
        'measure_empty': Eq(A(MEASURE, empty), RZERO),
        'measure_finite_additivity': alls((left, right), imps((A(MEASURABLE, left), A(MEASURABLE, right), event_disjoint(left, right)), Eq(A(MEASURE, event_union(left, right)), Add(A(MEASURE, left), A(MEASURE, right))))),
        'measure_countable_additivity_partial_unions': All(sequence, imps((measurable_sequence(sequence), disjoint_sequence(sequence)), lub(measured_prefix_sequence(sequence), A(MEASURE, countable_union(sequence))))),
        'addition_zero': All(V('zero_sum_real', 'R'), Eq(Add(V('zero_sum_real', 'R'), RZERO), V('zero_sum_real', 'R'))),
        'natural_successor_upper': All(index, A(NLE, index, A(SUCCESSOR, index)))
    }


def eq_trans(left, middle, right, first, second):
    variable = V('equality_transitive_placeholder', sort_of(left))
    return ('eq_e', second, variable, Eq(left, variable), first)


def logical(proposition):
    return ('conversion', proposition, ('tautology', normalize(proposition)))


def extensional_event(left, right, pointwise):
    return apply(ax('event_extensionality', left, right), pointwise)


def derive_measure_continuity(kernel):
    axioms = measure_axioms()
    for name, formula in axioms.items():
        if name in kernel.axioms or sort_of(formula) != 'Prop' or free_variables(formula):
            raise ValueError(('invalid measure foundation', name))
    kernel.axioms.update(axioms)
    sequence, index, point = V('family', EVENT_SEQUENCE), V('stage', 'N'), V('omega', OMEGA)
    measurable = measurable_sequence(sequence)
    prefix = A(PREFIX, sequence, index)
    base = ('eq_e', symmetric(A(PREFIX, sequence, NZERO), empty_event(), ax('finite_union_prefix_zero', sequence)), V('event_placeholder', EVENT), A(MEASURABLE, V('event_placeholder', EVENT)), ('axiom', 'sigma_algebra_empty'))
    step_hypothesis = A(MEASURABLE, prefix)
    step = apply(ax('sigma_algebra_finite_union', prefix, A(sequence, index)), hyp(step_hypothesis), instantiate(hyp(measurable), index))
    step = ('eq_e', symmetric(A(PREFIX, sequence, A(SUCCESSOR, index)), event_union(prefix, A(sequence, index)), ax('finite_union_prefix_successor', sequence, index)), V('event_placeholder', EVENT), A(MEASURABLE, V('event_placeholder', EVENT)), step)
    induction = ('nat_induction', index, step_hypothesis, base, close(step, (index,), (step_hypothesis,)))
    statement = All(sequence, Imp(measurable, All(index, A(MEASURABLE, prefix))))
    kernel.theorem('finite_union_prefix_measurable', statement, close(induction, (sequence,), (measurable,)))
    differences = disjointification(sequence)
    prefix_difference = A(PREFIX, differences, index)
    base_left = ax('finite_union_prefix_zero', differences)
    base_right = symmetric(A(PREFIX, sequence, NZERO), empty_event(), ax('finite_union_prefix_zero', sequence))
    base = eq_trans(A(PREFIX, differences, NZERO), empty_event(), A(PREFIX, sequence, NZERO), base_left, base_right)
    hypothesis = Eq(prefix_difference, prefix)
    left = A(PREFIX, differences, A(SUCCESSOR, index))
    middle = event_union(prefix, A(differences, index))
    step = ('eq_e', hyp(hypothesis), V('prefix_placeholder', EVENT), Eq(left, event_union(V('prefix_placeholder', EVENT), A(differences, index))), ax('finite_union_prefix_successor', differences, index))
    right = event_union(prefix, A(sequence, index))
    pointwise = close(logical(Iff(A(middle, point), A(right, point))), (point,))
    step = eq_trans(left, middle, right, step, extensional_event(middle, right, pointwise))
    target = A(PREFIX, sequence, A(SUCCESSOR, index))
    step = eq_trans(left, right, target, step, symmetric(target, right, ax('finite_union_prefix_successor', sequence, index)))
    induction = ('nat_induction', index, hypothesis, base, close(step, (index,), (hypothesis,)))
    kernel.theorem('disjointification_preserves_finite_unions', All(sequence, All(index, hypothesis)), close(induction, (sequence,)))
    pointwise_disjoint = close(logical(Imp(And(A(A(differences, index), point), A(prefix, point)), BOTTOM)), (point,))
    prefix_equality = ref('disjointification_preserves_finite_unions', sequence, index)
    disjoint = ('eq_e', symmetric(prefix_difference, prefix, prefix_equality), V('event_placeholder', EVENT), event_disjoint(A(differences, index), V('event_placeholder', EVENT)), pointwise_disjoint)
    kernel.theorem('disjointification_is_disjoint', All(sequence, disjoint_sequence(differences)), close(disjoint, (sequence, index)))
    prefix_measurable = instantiate(apply(ref('finite_union_prefix_measurable', sequence), hyp(measurable)), index)
    differences_measurable = apply(ax('sigma_algebra_difference', A(sequence, index), prefix), instantiate(hyp(measurable), index), prefix_measurable)
    differences_measurable = close(differences_measurable, (index,))
    differences_measurable = ('conversion', measurable_sequence(differences), differences_measurable)
    family_lub = apply(ax('measure_countable_additivity_partial_unions', differences), differences_measurable, ref('disjointification_is_disjoint', sequence))
    prefix_equalities = ref('disjointification_preserves_finite_unions', sequence)
    sequence_equalities = apply(ax('event_sequence_extensionality', prefix_sequence(differences), prefix_sequence(sequence)), prefix_equalities)
    family_placeholder = V('event_family_placeholder', EVENT_SEQUENCE)
    measure_sequence_placeholder = Lam(index, A(MEASURE, A(family_placeholder, index)))
    lub_placeholder = lub(measure_sequence_placeholder, A(MEASURE, supremum_event(family_placeholder)))
    desired = ('eq_e', sequence_equalities, family_placeholder, lub_placeholder, family_lub)
    statement = All(sequence, Imp(measurable, lub(measured_prefix_sequence(sequence), A(MEASURE, countable_union(sequence)))))
    kernel.theorem('measure_union_lub_of_finite_unions', statement, close(desired, (sequence,), (measurable,)))
    left, right = V('smaller_event', EVENT), V('larger_event', EVENT)
    subset = event_subset(left, right)
    conditions = (A(MEASURABLE, left), A(MEASURABLE, right), subset)
    difference = event_difference(right, left)
    difference_measurable = apply(ax('sigma_algebra_difference', right, left), hyp(conditions[1]), hyp(conditions[0]))
    disjoint = close(logical(Imp(And(A(left, point), A(difference, point)), BOTTOM)), (point,))
    finite_add = apply(ax('measure_finite_additivity', left, difference), hyp(conditions[0]), difference_measurable, disjoint)
    point_inclusion = instantiate(hyp(subset), point)
    point_identity = apply(logical(Imp(Imp(A(left, point), A(right, point)), Iff(A(event_union(left, difference), point), A(right, point)))), point_inclusion)
    event_identity = extensional_event(event_union(left, difference), right, close(point_identity, (point,)))
    event_placeholder = V('event_placeholder', EVENT)
    finite_add = ('eq_e', event_identity, event_placeholder, Eq(A(MEASURE, event_placeholder), Add(A(MEASURE, left), A(MEASURE, difference))), finite_add)
    nonnegative_difference = apply(ax('measure_nonnegative', difference), difference_measurable)
    additive_bound = apply(ax('addition_monotone', A(MEASURE, left), A(MEASURE, left), RZERO, A(MEASURE, difference)), ax('real_order_reflexive', A(MEASURE, left)), nonnegative_difference)
    real_placeholder = V('real_placeholder', 'R')
    additive_bound = ('eq_e', ax('addition_zero', A(MEASURE, left)), real_placeholder, Le(real_placeholder, Add(A(MEASURE, left), A(MEASURE, difference))), additive_bound)
    monotone = ('eq_e', symmetric(A(MEASURE, right), Add(A(MEASURE, left), A(MEASURE, difference)), finite_add), real_placeholder, Le(A(MEASURE, left), real_placeholder), additive_bound)
    statement = alls((left, right), imps(conditions, Le(A(MEASURE, left), A(MEASURE, right))))
    kernel.theorem('measure_monotone_from_additivity', statement, close(monotone, (left, right), conditions))
    ascending = event_increasing(sequence)
    property_at_index = event_subset(prefix, A(sequence, index))
    base = close(logical(Imp(A(empty_event(), point), A(A(sequence, NZERO), point))), (point,))
    base = ('eq_e', symmetric(A(PREFIX, sequence, NZERO), empty_event(), ax('finite_union_prefix_zero', sequence)), event_placeholder, event_subset(event_placeholder, A(sequence, NZERO)), base)
    successor = A(SUCCESSOR, index)
    increasing_step = apply(instantiate(hyp(ascending), index, successor), ax('natural_successor_upper', index))
    prefix_member, member, next_member = A(prefix, point), A(A(sequence, index), point), A(A(sequence, successor), point)
    inclusion_step = apply(logical(imps((Imp(prefix_member, member), Imp(member, next_member)), Imp(Or(prefix_member, member), next_member))), instantiate(hyp(property_at_index), point), instantiate(increasing_step, point))
    inclusion_step = close(inclusion_step, (point,))
    inclusion_step = ('eq_e', symmetric(A(PREFIX, sequence, successor), event_union(prefix, A(sequence, index)), ax('finite_union_prefix_successor', sequence, index)), event_placeholder, event_subset(event_placeholder, A(sequence, successor)), inclusion_step)
    induction = ('nat_induction', index, property_at_index, base, close(inclusion_step, (index,), (property_at_index,)))
    statement = All(sequence, Imp(ascending, All(index, property_at_index)))
    kernel.theorem('increasing_family_contains_each_finite_prefix', statement, close(induction, (sequence,), (ascending,)))
    included = close(logical(Imp(A(A(sequence, index), point), A(event_union(prefix, A(sequence, index)), point))), (point,))
    included = ('eq_e', symmetric(A(PREFIX, sequence, successor), event_union(prefix, A(sequence, index)), ax('finite_union_prefix_successor', sequence, index)), event_placeholder, event_subset(A(sequence, index), event_placeholder), included)
    statement = All(sequence, All(index, event_subset(A(sequence, index), A(PREFIX, sequence, successor))))
    kernel.theorem('each_event_is_in_next_finite_prefix', statement, close(included, (sequence, index)))
    union_lub = apply(ref('measure_union_lub_of_finite_unions', sequence), hyp(measurable))
    successor_measurable = instantiate(apply(ref('finite_union_prefix_measurable', sequence), hyp(measurable)), successor)
    local_measure_bound = apply(ref('measure_monotone_from_additivity', A(sequence, index), A(PREFIX, sequence, successor)), instantiate(hyp(measurable), index), successor_measurable, ref('each_event_is_in_next_finite_prefix', sequence, index))
    union_bound = upper_bound(union_lub, successor)
    upper = apply(ax('real_order_transitive', A(MEASURE, A(sequence, index)), A(MEASURE, A(PREFIX, sequence, successor)), A(MEASURE, countable_union(sequence))), local_measure_bound, union_bound)
    upper = close(upper, (index,))
    bound = V('event_measure_bound', 'R')
    bounds = All(index, Le(A(MEASURE, A(sequence, index)), bound))
    prefix_inclusion = instantiate(apply(ref('increasing_family_contains_each_finite_prefix', sequence), hyp(ascending)), index)
    prefix_measurable = instantiate(apply(ref('finite_union_prefix_measurable', sequence), hyp(measurable)), index)
    prefix_bound = apply(ref('measure_monotone_from_additivity', prefix, A(sequence, index)), prefix_measurable, instantiate(hyp(measurable), index), prefix_inclusion)
    prefix_bound = apply(ax('real_order_transitive', A(MEASURE, prefix), A(MEASURE, A(sequence, index)), bound), prefix_bound, instantiate(hyp(bounds), index))
    least = least_bound(union_lub, bound, close(prefix_bound, (index,)))
    least = close(least, (bound,), (bounds,))
    statement = All(sequence, imps((measurable, ascending), lub(measured_sequence(sequence), A(MEASURE, countable_union(sequence)))))
    kernel.theorem('measure_continuity_from_below', statement, close(('and_i', upper, least), (sequence,), (measurable, ascending)))
    return kernel



def ring_identity(left, right):
    symbols = {}
    def encode(term):
        term = normalize(term)
        if term == RZERO:
            return sp.Integer(0)
        if term == RONE:
            return sp.Integer(1)
        if term[0] == 'app' and term[1][0] == 'app':
            operator, a, b = term[1][1], term[1][2], term[2]
            if operator == RADD:
                return encode(a) + encode(b)
            if operator == RSUB:
                return encode(a) - encode(b)
            if operator == RMUL:
                return encode(a) * encode(b)
        key = alpha_key(term)
        if key not in symbols:
            symbols[key] = sp.Symbol('r' + str(len(symbols)))
        return symbols[key]
    return sp.expand(encode(left) - encode(right)) == 0


def ring(left, right):
    return ('ring', Eq(left, right))


def replace_subterm(term, old, new):
    if term == old or (sort_of(term) == sort_of(old) and same(term, old)):
        return new
    if term[0] in ('v', 'c', 'false'):
        return term
    if term[0] in ('lam', 'all', 'ex'):
        return (term[0], term[1], replace_subterm(term[2], old, new))
    return (term[0], *(replace_subterm(child, old, new) for child in term[1:]))


def rewrite(kernel, proof, equality, reverse=False):
    left, right = kernel.infer(equality).conclusion[1:]
    if reverse:
        equality = symmetric(left, right, equality)
        left, right = right, left
    conclusion = kernel.infer(proof).conclusion
    occupied = free_variables(conclusion) | free_variables(left) | free_variables(right)
    index = 0
    variable = V('rewrite_placeholder_' + str(index), sort_of(left))
    while variable in occupied:
        index += 1
        variable = V('rewrite_placeholder_' + str(index), sort_of(left))
    pattern = replace_subterm(conclusion, left, variable)
    if pattern == conclusion:
        normalized = normalize(conclusion)
        pattern = replace_subterm(normalized, normalize(left), variable)
        if pattern == normalized:
            raise ValueError(('rewrite target absent', left, conclusion))
    return ('eq_e', equality, variable, pattern, proof)


def add_axioms(kernel, axioms):
    for name, formula in axioms.items():
        if name in kernel.axioms or name in kernel.verified or sort_of(formula) != 'Prop' or free_variables(formula):
            raise ValueError(('invalid additional foundation', name))
    kernel.axioms.update(axioms)


def event_intersection(left, right):
    point = V('intersection_point', OMEGA)
    return Lam(point, And(A(left, point), A(right, point)))


def intersection_sequence(event, sequence):
    index = V('intersection_index', 'N')
    return Lam(index, event_intersection(event, A(sequence, index)))


def derive_intersection_continuity(kernel):
    sequence, index, point = V('family', EVENT_SEQUENCE), V('stage', 'N'), V('omega', OMEGA)
    witness = V('union_witness', 'N')
    direct = supremum_event(sequence)
    prefix = A(PREFIX, sequence, index)
    proposition = event_subset(prefix, direct)
    base = close(logical(Imp(A(empty_event(), point), A(direct, point))), (point,))
    base = rewrite(kernel, base, ax('finite_union_prefix_zero', sequence), True)
    left_member, right_member = A(prefix, point), A(A(sequence, index), point)
    left_case = apply(instantiate(hyp(proposition), point), hyp(left_member))
    right_case = ('ex_i', normalize(A(direct, point)), index, hyp(right_member))
    step = ('or_e', hyp(Or(left_member, right_member)), left_case, right_case)
    step = close(step, (point,), (Or(left_member, right_member),))
    step = ('conversion', event_subset(event_union(prefix, A(sequence, index)), direct), step)
    step = rewrite(kernel, step, ax('finite_union_prefix_successor', sequence, index), True)
    induction = ('nat_induction', index, proposition, base, close(step, (index,), (proposition,)))
    kernel.theorem('finite_prefix_subset_direct_union', All(sequence, All(index, proposition)), close(induction, (sequence,)))
    prefix_witness = A(A(PREFIX, sequence, witness), point)
    forward = apply(instantiate(ref('finite_prefix_subset_direct_union', sequence, witness), point), hyp(prefix_witness))
    forward = ('ex_e', ('conversion', normalize(A(countable_union(sequence), point)), hyp(A(countable_union(sequence), point))), witness, forward)
    forward = close(forward, assumptions=(A(countable_union(sequence), point),))
    event_witness = A(A(sequence, witness), point)
    in_next = apply(instantiate(ref('each_event_is_in_next_finite_prefix', sequence, witness), point), hyp(event_witness))
    backward = ('ex_i', normalize(A(countable_union(sequence), point)), A(SUCCESSOR, witness), in_next)
    backward = ('ex_e', ('conversion', normalize(A(direct, point)), hyp(A(direct, point))), witness, backward)
    backward = close(backward, assumptions=(A(direct, point),))
    pointwise = close(('and_i', forward, backward), (point,))
    equality = extensional_event(countable_union(sequence), direct, pointwise)
    kernel.theorem('countable_union_equals_existential_union', All(sequence, Eq(countable_union(sequence), direct)), close(equality, (sequence,)))
    left, right = V('left_event', EVENT), V('right_event', EVENT)
    difference = event_difference(left, event_difference(left, right))
    intersection = event_intersection(left, right)
    identity = extensional_event(difference, intersection, close(logical(Iff(A(difference, point), A(intersection, point))), (point,)))
    conditions = (A(MEASURABLE, left), A(MEASURABLE, right))
    inner = apply(ax('sigma_algebra_difference', left, right), hyp(conditions[0]), hyp(conditions[1]))
    result = apply(ax('sigma_algebra_difference', left, event_difference(left, right)), hyp(conditions[0]), inner)
    result = rewrite(kernel, result, identity)
    kernel.theorem('measurable_intersection', alls((left, right), imps(conditions, A(MEASURABLE, intersection))), close(result, (left, right), conditions))
    event = V('fixed_event', EVENT)
    intersections = intersection_sequence(event, sequence)
    left = event_intersection(event, supremum_event(sequence))
    right = supremum_event(intersections)
    left_hypothesis = A(left, point)
    forward_witness = ('and_i', ('and_l', ('conversion', normalize(left_hypothesis), hyp(left_hypothesis))), hyp(A(A(sequence, witness), point)))
    forward_witness = ('conversion', A(A(intersections, witness), point), forward_witness)
    forward_witness = ('ex_i', normalize(A(right, point)), witness, forward_witness)
    forward = ('ex_e', ('and_r', ('conversion', normalize(left_hypothesis), hyp(left_hypothesis))), witness, forward_witness)
    forward = close(forward, assumptions=(left_hypothesis,))
    right_hypothesis = A(right, point)
    witness_hypothesis = normalize(A(A(intersections, witness), point))
    backward_event = ('and_l', hyp(witness_hypothesis))
    backward_union = ('ex_i', normalize(A(supremum_event(sequence), point)), witness, ('and_r', hyp(witness_hypothesis)))
    backward = ('and_i', backward_event, backward_union)
    backward = ('ex_e', ('conversion', normalize(right_hypothesis), hyp(right_hypothesis)), witness, backward)
    backward = close(backward, assumptions=(right_hypothesis,))
    equality = extensional_event(left, right, close(('and_i', forward, backward), (point,)))
    equality = rewrite(kernel, equality, ref('countable_union_equals_existential_union', sequence), True)
    equality = rewrite(kernel, equality, ref('countable_union_equals_existential_union', intersections), True)
    statement = alls((event, sequence), Eq(event_intersection(event, countable_union(sequence)), countable_union(intersections)))
    kernel.theorem('intersection_distributes_over_countable_union', statement, close(equality, (event, sequence)))
    measurable, ascending = measurable_sequence(sequence), event_increasing(sequence)
    conditions = (A(MEASURABLE, event), measurable, ascending)
    intersections_measurable = close(apply(ref('measurable_intersection', event, A(sequence, index)), hyp(conditions[0]), instantiate(hyp(measurable), index)), (index,))
    i, j = V('first', 'N'), V('last', 'N')
    ordered = A(NLE, i, j)
    inclusion = apply(instantiate(hyp(ascending), i, j), hyp(ordered))
    left_atom, right_atom, fixed_atom = A(A(sequence, i), point), A(A(sequence, j), point), A(event, point)
    inc = apply(logical(Imp(Imp(left_atom, right_atom), Imp(And(fixed_atom, left_atom), And(fixed_atom, right_atom)))), instantiate(inclusion, point))
    inc = close(close(inc, (point,)), (i, j), (ordered,))
    continuity = apply(ref('measure_continuity_from_below', intersections), intersections_measurable, inc)
    continuity = rewrite(kernel, continuity, ref('intersection_distributes_over_countable_union', event, sequence), True)
    result = lub(measured_sequence(intersections), A(MEASURE, event_intersection(event, countable_union(sequence))))
    kernel.theorem('measure_continuity_on_fixed_intersection', alls((event, sequence), imps(conditions, result)), close(continuity, (event, sequence), conditions))
    return kernel


SIMPLE_COEFFICIENT = C('simple_head_coefficient', FT(SIMPLE_HEAD, 'R'))
SIMPLE_EVENT = C('simple_head_event', FT(SIMPLE_HEAD, EVENT))
SIMPLE_VALID_NONNEGATIVE = C('valid_nonnegative_simple', FT(SIMPLE, 'Prop'))
RESTRICTED_INTEGRAL = C('restricted_simple_integral', FT(SIMPLE, FT(EVENT, 'R')))
SIMPLE_NIL = C('list_nil', SIMPLE)
SIMPLE_CONS = C('list_cons', FT(SIMPLE_HEAD, FT(SIMPLE, SIMPLE)))


def restricted_integral(simple, event):
    return A(RESTRICTED_INTEGRAL, simple, event)


def weighted_sequence(simple, events):
    index = V('weighted_index', 'N')
    return Lam(index, restricted_integral(simple, A(events, index)))


def simple_recursion_axioms():
    head, tail, event = V('simple_head', SIMPLE_HEAD), V('simple_tail', SIMPLE), V('restricted_event', EVENT)
    cons = A(SIMPLE_CONS, head, tail)
    a, b = V('real_sequence_left', FT('N', 'R')), V('real_sequence_right', FT('N', 'R'))
    index = V('real_sequence_index', 'N')
    return {
        'simple_integral_nil': Eq(si(SIMPLE_NIL), RZERO),
        'simple_integral_cons': alls((head, tail), Eq(si(cons), Add(Mul(A(SIMPLE_COEFFICIENT, head), A(MEASURE, A(SIMPLE_EVENT, head))), si(tail)))),
        'restricted_integral_nil': All(event, Eq(restricted_integral(SIMPLE_NIL, event), RZERO)),
        'restricted_integral_cons': alls((head, tail, event), Eq(restricted_integral(cons, event), Add(Mul(A(SIMPLE_COEFFICIENT, head), A(MEASURE, event_intersection(A(SIMPLE_EVENT, head), event))), restricted_integral(tail, event)))),
        'valid_nonnegative_simple_nil': A(SIMPLE_VALID_NONNEGATIVE, SIMPLE_NIL),
        'valid_nonnegative_simple_cons': alls((head, tail), Iff(A(SIMPLE_VALID_NONNEGATIVE, cons), And(And(A(MEASURABLE, A(SIMPLE_EVENT, head)), Le(RZERO, A(SIMPLE_COEFFICIENT, head))), A(SIMPLE_VALID_NONNEGATIVE, tail)))),
        'real_sequence_extensionality': alls((a, b), Imp(All(index, Eq(A(a, index), A(b, index))), Eq(a, b)))
    }


def derive_finite_simple_continuity(kernel):
    add_axioms(kernel, simple_recursion_axioms())
    index, i, j = V('stage', 'N'), V('first', 'N'), V('last', 'N')
    value, bound, scalar = V('constant_value', 'R'), V('constant_bound', 'R'), V('multiplier', 'R')
    constant = Lam(index, value)
    bounds = All(index, Le(A(constant, index), bound))
    upper = close(ax('real_order_reflexive', value), (index,))
    lower = close(instantiate(hyp(bounds), NZERO), (bound,), (bounds,))
    kernel.theorem('constant_sequence_lub', All(value, lub(constant, value)), close(('and_i', upper, lower), (value,)))
    constant_increasing = close(ax('real_order_reflexive', value), (i, j), (A(NLE, i, j),))
    kernel.theorem('constant_sequence_increasing', All(value, increasing(constant)), close(constant_increasing, (value,)))
    sequence = V('numeric_sequence', FT('N', 'R'))
    conditions = (Le(RZERO, scalar), increasing(sequence))
    point = apply(instantiate(hyp(conditions[1]), i, j), hyp(A(NLE, i, j)))
    scaled = apply(ax('nonnegative_multiplication_monotone', scalar, A(sequence, i), A(sequence, j)), hyp(conditions[0]), point)
    scaled_sequence = Lam(index, Mul(scalar, A(sequence, index)))
    kernel.theorem('nonnegative_scalar_preserves_increasing', alls((sequence, scalar), imps(conditions, increasing(scaled_sequence))), close(close(scaled, (i, j), (A(NLE, i, j),)), (sequence, scalar), conditions))
    other = V('other_numeric_sequence', FT('N', 'R'))
    conditions = (increasing(sequence), increasing(other))
    first = apply(instantiate(hyp(conditions[0]), i, j), hyp(A(NLE, i, j)))
    last = apply(instantiate(hyp(conditions[1]), i, j), hyp(A(NLE, i, j)))
    point = apply(ax('addition_monotone', A(sequence, i), A(sequence, j), A(other, i), A(other, j)), first, last)
    sum_sequence = Lam(index, Add(A(sequence, index), A(other, index)))
    kernel.theorem('sum_preserves_increasing', alls((sequence, other), imps(conditions, increasing(sum_sequence))), close(close(point, (i, j), (A(NLE, i, j),)), (sequence, other), conditions))
    events, event = V('event_family', EVENT_SEQUENCE), V('fixed_event', EVENT)
    conditions = (A(MEASURABLE, event), measurable_sequence(events), event_increasing(events))
    left, right = event_intersection(event, A(events, i)), event_intersection(event, A(events, j))
    left_measurable = apply(ref('measurable_intersection', event, A(events, i)), hyp(conditions[0]), instantiate(hyp(conditions[1]), i))
    right_measurable = apply(ref('measurable_intersection', event, A(events, j)), hyp(conditions[0]), instantiate(hyp(conditions[1]), j))
    inclusion = apply(instantiate(hyp(conditions[2]), i, j), hyp(A(NLE, i, j)))
    point = V('omega', OMEGA)
    implication = apply(logical(Imp(Imp(A(A(events, i), point), A(A(events, j), point)), Imp(A(left, point), A(right, point)))), instantiate(inclusion, point))
    subset = close(implication, (point,))
    point_bound = apply(ref('measure_monotone_from_additivity', left, right), left_measurable, right_measurable, subset)
    measured = measured_sequence(intersection_sequence(event, events))
    inc = close(point_bound, (i, j), (A(NLE, i, j),))
    kernel.theorem('intersection_measures_increasing', alls((event, events), imps(conditions, increasing(measured))), close(inc, (event, events), conditions))
    simple, head, tail = V('finite_simple', SIMPLE), V('fresh_head', SIMPLE_HEAD), V('fresh_tail', SIMPLE)
    valid = A(SIMPLE_VALID_NONNEGATIVE, simple)
    target = And(lub(weighted_sequence(simple, events), restricted_integral(simple, countable_union(events))), increasing(weighted_sequence(simple, events)))
    predicate = Imp(valid, target)
    constant_zero = Lam(index, RZERO)
    zero_sequence_equality = apply(ax('real_sequence_extensionality', weighted_sequence(SIMPLE_NIL, events), constant_zero), close(ax('restricted_integral_nil', A(events, index)), (index,)))
    base_lub = rewrite(kernel, ref('constant_sequence_lub', RZERO), zero_sequence_equality, True)
    base_lub = ('eq_e', symmetric(restricted_integral(SIMPLE_NIL, countable_union(events)), RZERO, ax('restricted_integral_nil', countable_union(events))), V('base_integral_placeholder', 'R'), lub(weighted_sequence(SIMPLE_NIL, events), V('base_integral_placeholder', 'R')), base_lub)
    base_inc = rewrite(kernel, ref('constant_sequence_increasing', RZERO), zero_sequence_equality, True)
    base = close(('and_i', base_lub, base_inc), assumptions=(A(SIMPLE_VALID_NONNEGATIVE, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    cons = A(SIMPLE_CONS, head, tail)
    cons_valid = A(SIMPLE_VALID_NONNEGATIVE, cons)
    validity = apply(('and_l', ax('valid_nonnegative_simple_cons', head, tail)), hyp(cons_valid))
    measurable_head = ('and_l', ('and_l', validity))
    nonnegative_coefficient = ('and_r', ('and_l', validity))
    tail_result = apply(hyp(tail_hypothesis), ('and_r', validity))
    head_event, coefficient = A(SIMPLE_EVENT, head), A(SIMPLE_COEFFICIENT, head)
    head_sequence = measured_sequence(intersection_sequence(head_event, events))
    head_value = A(MEASURE, event_intersection(head_event, countable_union(events)))
    event_conditions = (hyp(measurable_sequence(events)), hyp(event_increasing(events)))
    head_lub = apply(ref('measure_continuity_on_fixed_intersection', head_event, events), measurable_head, *event_conditions)
    head_inc = apply(ref('intersection_measures_increasing', head_event, events), measurable_head, *event_conditions)
    scaled_sequence = Lam(index, Mul(coefficient, A(head_sequence, index)))
    scaled_value = Mul(coefficient, head_value)
    scaled_lub = apply(ref('nonnegative_scalar_preserves_lub', head_sequence, head_value, coefficient), nonnegative_coefficient, head_lub)
    scaled_inc = apply(ref('nonnegative_scalar_preserves_increasing', head_sequence, coefficient), nonnegative_coefficient, head_inc)
    tail_sequence = weighted_sequence(tail, events)
    tail_value = restricted_integral(tail, countable_union(events))
    sum_sequence = Lam(index, Add(A(scaled_sequence, index), A(tail_sequence, index)))
    sum_lub = apply(ref('increasing_sum_lub', scaled_sequence, tail_sequence, scaled_value, tail_value), scaled_lub, ('and_l', tail_result), scaled_inc, ('and_r', tail_result))
    sum_inc = apply(ref('sum_preserves_increasing', scaled_sequence, tail_sequence), scaled_inc, ('and_r', tail_result))
    sequence_equality = apply(ax('real_sequence_extensionality', weighted_sequence(cons, events), sum_sequence), close(ax('restricted_integral_cons', head, tail, A(events, index)), (index,)))
    cons_lub = rewrite(kernel, sum_lub, sequence_equality, True)
    cons_lub = rewrite(kernel, cons_lub, ax('restricted_integral_cons', head, tail, countable_union(events)), True)
    cons_inc = rewrite(kernel, sum_inc, sequence_equality, True)
    step = close(close(('and_i', cons_lub, cons_inc), assumptions=(cons_valid,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    result = instantiate(induction, simple)
    conditions = (measurable_sequence(events), event_increasing(events))
    statement = alls((events, simple), imps(conditions, predicate))
    kernel.theorem('finite_weighted_measure_continuity', statement, close(result, (events, simple), conditions))
    return kernel


SIMPLE_VALID = C('valid_simple', FT(SIMPLE, 'Prop'))
INDICATOR = C('event_indicator', FT(EVENT, FUNCTION))


def universe_event():
    point = V('universe_point', OMEGA)
    return Lam(point, Imp(BOTTOM, BOTTOM))


def val(simple, point):
    return A(simple_value(simple), point)


def simple_function_axioms():
    head, tail = V('simple_head', SIMPLE_HEAD), V('simple_tail', SIMPLE)
    event, point = V('indicator_event', EVENT), V('evaluation_point', OMEGA)
    cons = A(SIMPLE_CONS, head, tail)
    return {
        'valid_simple_nil': A(SIMPLE_VALID, SIMPLE_NIL),
        'valid_simple_cons': alls((head, tail), Iff(A(SIMPLE_VALID, cons), And(A(MEASURABLE, A(SIMPLE_EVENT, head)), A(SIMPLE_VALID, tail)))),
        'simple_value_nil': All(point, Eq(val(SIMPLE_NIL, point), RZERO)),
        'simple_value_cons': alls((head, tail, point), Eq(val(cons, point), Add(Mul(A(SIMPLE_COEFFICIENT, head), A(INDICATOR, A(SIMPLE_EVENT, head), point)), val(tail, point)))),
        'indicator_inside': alls((event, point), Imp(A(event, point), Eq(A(INDICATOR, event, point), RONE))),
        'indicator_outside': alls((event, point), Imp(Imp(A(event, point), BOTTOM), Eq(A(INDICATOR, event, point), RZERO))),
        'sigma_algebra_universe': A(MEASURABLE, universe_event()),
        'probability_of_universe': Eq(A(MEASURE, universe_event()), RONE)
    }


def derive_simple_finite_algebra(kernel):
    add_axioms(kernel, simple_function_axioms())
    simple, head, tail = V('finite_simple', SIMPLE), V('fresh_head', SIMPLE_HEAD), V('fresh_tail', SIMPLE)
    left, right, point = V('left_event', EVENT), V('right_event', EVENT), V('omega', OMEGA)
    valid = A(SIMPLE_VALID, simple)
    conditions = (A(MEASURABLE, left), A(MEASURABLE, right), event_disjoint(left, right))
    identity = Eq(restricted_integral(simple, event_union(left, right)), Add(restricted_integral(simple, left), restricted_integral(simple, right)))
    predicate = Imp(valid, identity)
    base = ring(RZERO, Add(RZERO, RZERO))
    placeholder = V('real_placeholder', 'R')
    base = ('eq_e', symmetric(restricted_integral(SIMPLE_NIL, event_union(left, right)), RZERO, ax('restricted_integral_nil', event_union(left, right))), placeholder, Eq(placeholder, Add(RZERO, RZERO)), base)
    base = ('eq_e', symmetric(restricted_integral(SIMPLE_NIL, left), RZERO, ax('restricted_integral_nil', left)), placeholder, Eq(restricted_integral(SIMPLE_NIL, event_union(left, right)), Add(placeholder, RZERO)), base)
    base = ('eq_e', symmetric(restricted_integral(SIMPLE_NIL, right), RZERO, ax('restricted_integral_nil', right)), placeholder, Eq(restricted_integral(SIMPLE_NIL, event_union(left, right)), Add(restricted_integral(SIMPLE_NIL, left), placeholder)), base)
    base = close(base, assumptions=(A(SIMPLE_VALID, SIMPLE_NIL),))
    cons = A(SIMPLE_CONS, head, tail)
    cons_valid = A(SIMPLE_VALID, cons)
    head_event, coefficient = A(SIMPLE_EVENT, head), A(SIMPLE_COEFFICIENT, head)
    validity = apply(('and_l', ax('valid_simple_cons', head, tail)), hyp(cons_valid))
    tail_hypothesis = substitute(predicate, simple, tail)
    tail_identity = apply(hyp(tail_hypothesis), ('and_r', validity))
    i_left, i_right = event_intersection(head_event, left), event_intersection(head_event, right)
    m_left = apply(ref('measurable_intersection', head_event, left), ('and_l', validity), hyp(conditions[0]))
    m_right = apply(ref('measurable_intersection', head_event, right), ('and_l', validity), hyp(conditions[1]))
    disjoint = apply(logical(Imp(Imp(And(A(left, point), A(right, point)), BOTTOM), Imp(And(A(i_left, point), A(i_right, point)), BOTTOM))), instantiate(hyp(conditions[2]), point))
    disjoint = close(disjoint, (point,))
    additivity = apply(ax('measure_finite_additivity', i_left, i_right), m_left, m_right, disjoint)
    union_intersection = event_intersection(head_event, event_union(left, right))
    distributed = event_union(i_left, i_right)
    set_equality = extensional_event(union_intersection, distributed, close(logical(Iff(A(union_intersection, point), A(distributed, point))), (point,)))
    additivity = rewrite(kernel, additivity, set_equality, True)
    step = ax('restricted_integral_cons', head, tail, event_union(left, right))
    step = rewrite(kernel, step, additivity)
    step = rewrite(kernel, step, tail_identity)
    a, b = A(MEASURE, i_left), A(MEASURE, i_right)
    x, y = restricted_integral(tail, left), restricted_integral(tail, right)
    algebra = ring(Add(Mul(coefficient, Add(a, b)), Add(x, y)), Add(Add(Mul(coefficient, a), x), Add(Mul(coefficient, b), y)))
    step = eq_trans(restricted_integral(cons, event_union(left, right)), kernel.infer(step).conclusion[2], kernel.infer(algebra).conclusion[2], step, algebra)
    step = rewrite(kernel, step, ax('restricted_integral_cons', head, tail, left), True)
    step = rewrite(kernel, step, ax('restricted_integral_cons', head, tail, right), True)
    step = close(close(step, assumptions=(cons_valid,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    statement = alls((left, right, simple), imps(conditions, predicate))
    kernel.theorem('simple_integral_disjoint_additivity', statement, close(instantiate(induction, simple), (left, right, simple), conditions))
    event, cut = V('event', EVENT), V('cut_event', EVENT)
    inside, outside = event_intersection(event, cut), event_difference(event, cut)
    split_union = event_union(inside, outside)
    split_identity = extensional_event(split_union, event, close(logical(Iff(A(split_union, point), A(event, point))), (point,)))
    split_disjoint = close(logical(Imp(And(A(inside, point), A(outside, point)), BOTTOM)), (point,))
    conditions = (A(MEASURABLE, event), A(MEASURABLE, cut))
    inside_measurable = apply(ref('measurable_intersection', event, cut), hyp(conditions[0]), hyp(conditions[1]))
    outside_measurable = apply(ax('sigma_algebra_difference', event, cut), hyp(conditions[0]), hyp(conditions[1]))
    measure_split = apply(ax('measure_finite_additivity', inside, outside), inside_measurable, outside_measurable, split_disjoint)
    measure_split = rewrite(kernel, measure_split, split_identity)
    statement = alls((event, cut), imps(conditions, Eq(A(MEASURE, event), Add(A(MEASURE, inside), A(MEASURE, outside)))))
    kernel.theorem('measure_event_partition', statement, close(measure_split, (event, cut), conditions))
    simple_split = apply(ref('simple_integral_disjoint_additivity', inside, outside, simple), inside_measurable, outside_measurable, split_disjoint, hyp(valid))
    simple_split = rewrite(kernel, simple_split, split_identity)
    statement = alls((event, cut, simple), imps(conditions + (valid,), Eq(restricted_integral(simple, event), Add(restricted_integral(simple, inside), restricted_integral(simple, outside)))))
    kernel.theorem('simple_integral_event_partition', statement, close(simple_split, (event, cut, simple), conditions + (valid,)))
    empty = empty_event()
    predicate = Eq(restricted_integral(simple, empty), RZERO)
    base = ax('restricted_integral_nil', empty)
    hypothesis = substitute(predicate, simple, tail)
    intersection = event_intersection(head_event, empty)
    intersection_empty = extensional_event(intersection, empty, close(logical(Iff(A(intersection, point), A(empty, point))), (point,)))
    step = ax('restricted_integral_cons', head, tail, empty)
    step = rewrite(kernel, step, intersection_empty)
    step = rewrite(kernel, step, ('axiom', 'measure_empty'))
    step = rewrite(kernel, step, hyp(hypothesis))
    step = rewrite(kernel, step, ring(Add(Mul(coefficient, RZERO), RZERO), RZERO))
    step = close(step, (head, tail), (hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    kernel.theorem('simple_integral_empty_event', All(simple, predicate), induction)
    universe = universe_event()
    predicate = Eq(restricted_integral(simple, universe), si(simple))
    base = eq_trans(restricted_integral(SIMPLE_NIL, universe), RZERO, si(SIMPLE_NIL), ax('restricted_integral_nil', universe), symmetric(si(SIMPLE_NIL), RZERO, ('axiom', 'simple_integral_nil')))
    hypothesis = substitute(predicate, simple, tail)
    intersection = event_intersection(head_event, universe)
    intersection_identity = extensional_event(intersection, head_event, close(logical(Iff(A(intersection, point), A(head_event, point))), (point,)))
    step = ax('restricted_integral_cons', head, tail, universe)
    step = rewrite(kernel, step, intersection_identity)
    step = rewrite(kernel, step, hyp(hypothesis))
    step = rewrite(kernel, step, ax('simple_integral_cons', head, tail), True)
    step = close(step, (head, tail), (hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    kernel.theorem('simple_integral_is_unrestricted_weighted_sum', All(simple, predicate), induction)
    return kernel


def nonnegative_on_event(function, event):
    point = V('nonnegative_event_point', OMEGA)
    return All(point, Imp(A(event, point), Le(RZERO, A(function, point))))


def shifted_simple_function(offset, simple):
    point = V('shifted_simple_point', OMEGA)
    return Lam(point, Add(offset, val(simple, point)))


def derive_simple_positivity(kernel):
    x, y = V('nonnegative_left', 'R'), V('nonnegative_right', 'R')
    conditions = (Le(RZERO, x), Le(RZERO, y))
    proof = apply(ax('addition_monotone', RZERO, x, RZERO, y), hyp(conditions[0]), hyp(conditions[1]))
    proof = rewrite(kernel, proof, ring(Add(RZERO, RZERO), RZERO))
    kernel.theorem('sum_nonnegative', alls((x, y), imps(conditions, Le(RZERO, Add(x, y)))), close(proof, (x, y), conditions))
    proof = apply(ax('nonnegative_multiplication_monotone', x, RZERO, y), hyp(conditions[0]), hyp(conditions[1]))
    proof = rewrite(kernel, proof, ring(Mul(x, RZERO), RZERO))
    kernel.theorem('product_nonnegative', alls((x, y), imps(conditions, Le(RZERO, Mul(x, y)))), close(proof, (x, y), conditions))
    event, offset, point = V('constant_event', EVENT), V('constant_offset', 'R'), V('omega', OMEGA)
    bounded = All(point, Imp(A(event, point), Le(RZERO, offset)))
    measurable = A(MEASURABLE, event)
    exists = Ex(point, A(event, point))
    witness = V('fresh_event_witness', OMEGA)
    witness_hypothesis = A(event, witness)
    offset_nonnegative = apply(instantiate(hyp(bounded), witness), hyp(witness_hypothesis))
    measure_nonnegative = apply(ax('measure_nonnegative', event), hyp(measurable))
    positive_case = apply(ref('product_nonnegative', offset, A(MEASURE, event)), offset_nonnegative, measure_nonnegative)
    positive_case = ('ex_e', hyp(exists), witness, positive_case)
    absent = Imp(exists, BOTTOM)
    impossible = ('ex_i', exists, point, hyp(A(event, point)))
    impossible = apply(hyp(absent), impossible)
    point_false = close(impossible, assumptions=(A(event, point),))
    point_equivalence = ('and_i', point_false, logical(Imp(BOTTOM, A(event, point))))
    empty_identity = extensional_event(event, empty_event(), close(point_equivalence, (point,)))
    measure_zero = rewrite(kernel, ('axiom', 'measure_empty'), empty_identity, True)
    zero_case = ax('real_order_reflexive', RZERO)
    zero_case = ('eq_e', symmetric(Mul(offset, RZERO), RZERO, ring(Mul(offset, RZERO), RZERO)), V('zero_product_placeholder', 'R'), Le(RZERO, V('zero_product_placeholder', 'R')), zero_case)
    zero_case = ('eq_e', symmetric(A(MEASURE, event), RZERO, measure_zero), V('empty_measure_placeholder', 'R'), Le(RZERO, Mul(offset, V('empty_measure_placeholder', 'R'))), zero_case)
    cases = ('or_e', logical(Or(exists, absent)), positive_case, zero_case)
    statement = alls((event, offset), imps((measurable, bounded), Le(RZERO, Mul(offset, A(MEASURE, event)))))
    kernel.theorem('constant_nonnegative_on_event_integrates_nonnegative', statement, close(cases, (event, offset), (measurable, bounded)))
    simple, head, tail = V('finite_simple', SIMPLE), V('fresh_head', SIMPLE_HEAD), V('fresh_tail', SIMPLE)
    event, offset = V('integration_event', EVENT), V('constant_offset', 'R')
    conditions = (A(SIMPLE_VALID, simple), A(MEASURABLE, event), nonnegative_on_event(shifted_simple_function(offset, simple), event))
    target = Le(RZERO, Add(Mul(offset, A(MEASURE, event)), restricted_integral(simple, event)))
    predicate = alls((offset, event), imps(conditions, target))
    base_conditions = tuple(substitute(c, simple, SIMPLE_NIL) for c in conditions)
    base_point = apply(instantiate(hyp(base_conditions[2]), point), hyp(A(event, point)))
    base_point = rewrite(kernel, base_point, ax('simple_value_nil', point))
    base_point = rewrite(kernel, base_point, ring(Add(offset, RZERO), offset))
    base_bound = close(base_point, (point,), (A(event, point),))
    base = apply(ref('constant_nonnegative_on_event_integrates_nonnegative', event, offset), hyp(base_conditions[1]), base_bound)
    placeholder = V('base_placeholder', 'R')
    base = ('eq_e', symmetric(Add(Mul(offset, A(MEASURE, event)), RZERO), Mul(offset, A(MEASURE, event)), ring(Add(Mul(offset, A(MEASURE, event)), RZERO), Mul(offset, A(MEASURE, event)))), placeholder, Le(RZERO, placeholder), base)
    base = ('eq_e', symmetric(restricted_integral(SIMPLE_NIL, event), RZERO, ax('restricted_integral_nil', event)), placeholder, Le(RZERO, Add(Mul(offset, A(MEASURE, event)), placeholder)), base)
    base = close(base, (offset, event), base_conditions)
    tail_hypothesis = substitute(predicate, simple, tail)
    cons = A(SIMPLE_CONS, head, tail)
    head_event, coefficient = A(SIMPLE_EVENT, head), A(SIMPLE_COEFFICIENT, head)
    cons_conditions = tuple(substitute(c, simple, cons) for c in conditions)
    validity = apply(('and_l', ax('valid_simple_cons', head, tail)), hyp(cons_conditions[0]))
    tail_valid, head_measurable = ('and_r', validity), ('and_l', validity)
    inside, outside = event_intersection(event, head_event), event_difference(event, head_event)
    inside_measurable = apply(ref('measurable_intersection', event, head_event), hyp(cons_conditions[1]), head_measurable)
    outside_measurable = apply(ax('sigma_algebra_difference', event, head_event), hyp(cons_conditions[1]), head_measurable)
    in_hypothesis = A(inside, point)
    in_conjunction = ('conversion', normalize(in_hypothesis), hyp(in_hypothesis))
    inside_bound = apply(instantiate(hyp(cons_conditions[2]), point), ('and_l', in_conjunction))
    inside_bound = rewrite(kernel, inside_bound, ax('simple_value_cons', head, tail, point))
    inside_bound = rewrite(kernel, inside_bound, apply(ax('indicator_inside', head_event, point), ('and_r', in_conjunction)))
    inside_bound = rewrite(kernel, inside_bound, ring(Add(offset, Add(Mul(coefficient, RONE), val(tail, point))), Add(Add(offset, coefficient), val(tail, point))))
    inside_bound = close(inside_bound, (point,), (in_hypothesis,))
    inside_integral = apply(instantiate(hyp(tail_hypothesis), Add(offset, coefficient), inside), tail_valid, inside_measurable, inside_bound)
    out_hypothesis = A(outside, point)
    out_conjunction = ('conversion', normalize(out_hypothesis), hyp(out_hypothesis))
    outside_bound = apply(instantiate(hyp(cons_conditions[2]), point), ('and_l', out_conjunction))
    outside_bound = rewrite(kernel, outside_bound, ax('simple_value_cons', head, tail, point))
    outside_bound = rewrite(kernel, outside_bound, apply(ax('indicator_outside', head_event, point), ('and_r', out_conjunction)))
    outside_bound = rewrite(kernel, outside_bound, ring(Add(offset, Add(Mul(coefficient, RZERO), val(tail, point))), Add(offset, val(tail, point))))
    outside_bound = close(outside_bound, (point,), (out_hypothesis,))
    outside_integral = apply(instantiate(hyp(tail_hypothesis), offset, outside), tail_valid, outside_measurable, outside_bound)
    term_inside = Add(Mul(Add(offset, coefficient), A(MEASURE, inside)), restricted_integral(tail, inside))
    term_outside = Add(Mul(offset, A(MEASURE, outside)), restricted_integral(tail, outside))
    sum_bound = apply(ref('sum_nonnegative', term_inside, term_outside), inside_integral, outside_integral)
    original_term = Add(Mul(offset, A(MEASURE, event)), restricted_integral(cons, event))
    expression = ('eq_i', original_term)
    expression = ('eq_e', ax('restricted_integral_cons', head, tail, event), placeholder, Eq(original_term, Add(Mul(offset, A(MEASURE, event)), placeholder)), expression)
    intersection = event_intersection(head_event, event)
    intersection_identity = extensional_event(intersection, inside, close(logical(Iff(A(intersection, point), A(inside, point))), (point,)))
    right_term = kernel.infer(expression).conclusion[2]
    expression = ('eq_e', intersection_identity, V('inside_event_placeholder', EVENT), Eq(original_term, replace_subterm(right_term, intersection, V('inside_event_placeholder', EVENT))), expression)
    measure_partition = apply(ref('measure_event_partition', event, head_event), hyp(cons_conditions[1]), head_measurable)
    right_term = kernel.infer(expression).conclusion[2]
    expression = ('eq_e', measure_partition, placeholder, Eq(original_term, replace_subterm(right_term, A(MEASURE, event), placeholder)), expression)
    integral_partition = apply(ref('simple_integral_event_partition', event, head_event, tail), hyp(cons_conditions[1]), head_measurable, tail_valid)
    right_term = kernel.infer(expression).conclusion[2]
    expression = ('eq_e', integral_partition, placeholder, Eq(original_term, replace_subterm(right_term, restricted_integral(tail, event), placeholder)), expression)
    right_term = kernel.infer(expression).conclusion[2]
    expression = eq_trans(original_term, right_term, Add(term_inside, term_outside), expression, ring(right_term, Add(term_inside, term_outside)))
    step = rewrite(kernel, sum_bound, expression, True)
    step = close(close(step, (offset, event), cons_conditions), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    kernel.theorem('simple_integral_positive_by_event_refinement', All(simple, predicate), induction)
    nonnegative = nonnegative_on_event(simple_value(simple), event)
    shifted = apply(instantiate(hyp(nonnegative), point), hyp(A(event, point)))
    shifted = ('eq_e', symmetric(Add(RZERO, val(simple, point)), val(simple, point), ring(Add(RZERO, val(simple, point)), val(simple, point))), placeholder, Le(RZERO, placeholder), shifted)
    shifted = close(shifted, (point,), (A(event, point),))
    result = apply(ref('simple_integral_positive_by_event_refinement', simple, RZERO, event), hyp(conditions[0]), hyp(conditions[1]), shifted)
    result = rewrite(kernel, result, ring(Add(Mul(RZERO, A(MEASURE, event)), restricted_integral(simple, event)), restricted_integral(simple, event)))
    conditions = (A(SIMPLE_VALID, simple), A(MEASURABLE, event), nonnegative)
    statement = alls((simple, event), imps(conditions, Le(RZERO, restricted_integral(simple, event))))
    kernel.theorem('simple_integral_nonnegative', statement, close(result, (simple, event), conditions))
    return kernel


SIMPLE_PAIR = C('simple_head_pair', FT('R', FT(EVENT, SIMPLE_HEAD)))
SIMPLE_APPEND = C('simple_append', FT(SIMPLE, FT(SIMPLE, SIMPLE)))
SIMPLE_RESTRICT = C('simple_restrict', FT(SIMPLE, FT(EVENT, SIMPLE)))


def pair(coefficient, event):
    return A(SIMPLE_PAIR, coefficient, event)


def simple_operation_axioms():
    coefficient, scalar = V('pair_coefficient', 'R'), V('scale_scalar', 'R')
    event = V('pair_event', EVENT)
    head, tail, other = V('operation_head', SIMPLE_HEAD), V('operation_tail', SIMPLE), V('other_simple', SIMPLE)
    cons = A(SIMPLE_CONS, head, tail)
    return {
        'simple_pair_coefficient': alls((coefficient, event), Eq(A(SIMPLE_COEFFICIENT, pair(coefficient, event)), coefficient)),
        'simple_pair_event': alls((coefficient, event), Eq(A(SIMPLE_EVENT, pair(coefficient, event)), event)),
        'simple_scale_nil': All(scalar, Eq(A(SIMPLE_SCALE, scalar, SIMPLE_NIL), SIMPLE_NIL)),
        'simple_scale_cons': alls((scalar, head, tail), Eq(A(SIMPLE_SCALE, scalar, cons), A(SIMPLE_CONS, pair(Mul(scalar, A(SIMPLE_COEFFICIENT, head)), A(SIMPLE_EVENT, head)), A(SIMPLE_SCALE, scalar, tail)))),
        'simple_append_nil': All(other, Eq(A(SIMPLE_APPEND, SIMPLE_NIL, other), other)),
        'simple_append_cons': alls((head, tail, other), Eq(A(SIMPLE_APPEND, cons, other), A(SIMPLE_CONS, head, A(SIMPLE_APPEND, tail, other)))),
        'simple_restrict_nil': All(event, Eq(A(SIMPLE_RESTRICT, SIMPLE_NIL, event), SIMPLE_NIL)),
        'simple_restrict_cons': alls((head, tail, event), Eq(A(SIMPLE_RESTRICT, cons, event), A(SIMPLE_CONS, pair(A(SIMPLE_COEFFICIENT, head), event_intersection(A(SIMPLE_EVENT, head), event)), A(SIMPLE_RESTRICT, tail, event))))
    }


def derive_simple_operations(kernel):
    add_axioms(kernel, simple_operation_axioms())
    simple, head, tail = V('finite_simple', SIMPLE), V('fresh_head', SIMPLE_HEAD), V('fresh_tail', SIMPLE)
    scalar, point = V('scale_factor', 'R'), V('omega', OMEGA)
    cons = A(SIMPLE_CONS, head, tail)
    head_coefficient, head_event = A(SIMPLE_COEFFICIENT, head), A(SIMPLE_EVENT, head)
    scaled_head = pair(Mul(scalar, head_coefficient), head_event)
    scaled_tail = A(SIMPLE_SCALE, scalar, tail)
    predicates = (
        ('simple_scaling_integral', Eq(si(A(SIMPLE_SCALE, scalar, simple)), Mul(scalar, si(simple)))),
        ('simple_scaling_value', All(point, Eq(val(A(SIMPLE_SCALE, scalar, simple), point), Mul(scalar, val(simple, point)))))
    )
    for name, predicate in predicates:
        if name == 'simple_scaling_integral':
            base = rewrite(kernel, ('axiom', 'simple_integral_nil'), ax('simple_scale_nil', scalar), True)
            base = ('eq_e', symmetric(Mul(scalar, RZERO), RZERO, ring(Mul(scalar, RZERO), RZERO)), V('scaling_base_placeholder', 'R'), Eq(si(A(SIMPLE_SCALE, scalar, SIMPLE_NIL)), V('scaling_base_placeholder', 'R')), base)
            base = ('eq_e', symmetric(si(SIMPLE_NIL), RZERO, ('axiom', 'simple_integral_nil')), V('scaling_base_placeholder', 'R'), Eq(si(A(SIMPLE_SCALE, scalar, SIMPLE_NIL)), Mul(scalar, V('scaling_base_placeholder', 'R'))), base)
            step = ax('simple_integral_cons', scaled_head, scaled_tail)
            tail_hypothesis = substitute(predicate, simple, tail)
            step = rewrite(kernel, step, hyp(tail_hypothesis))
        else:
            base = rewrite(kernel, ax('simple_value_nil', point), ax('simple_scale_nil', scalar), True)
            base = ('eq_e', symmetric(Mul(scalar, RZERO), RZERO, ring(Mul(scalar, RZERO), RZERO)), V('scaling_base_placeholder', 'R'), Eq(val(A(SIMPLE_SCALE, scalar, SIMPLE_NIL), point), V('scaling_base_placeholder', 'R')), base)
            base = ('eq_e', symmetric(val(SIMPLE_NIL, point), RZERO, ax('simple_value_nil', point)), V('scaling_base_placeholder', 'R'), Eq(val(A(SIMPLE_SCALE, scalar, SIMPLE_NIL), point), Mul(scalar, V('scaling_base_placeholder', 'R'))), base)
            base = close(base, (point,))
            tail_hypothesis = substitute(predicate, simple, tail)
            step = ax('simple_value_cons', scaled_head, scaled_tail, point)
            step = rewrite(kernel, step, instantiate(hyp(tail_hypothesis), point))
        step = rewrite(kernel, step, ax('simple_pair_coefficient', Mul(scalar, head_coefficient), head_event))
        step = rewrite(kernel, step, ax('simple_pair_event', Mul(scalar, head_coefficient), head_event))
        step = rewrite(kernel, step, ax('simple_scale_cons', scalar, head, tail), True)
        left, right = kernel.infer(step).conclusion[1:]
        if name == 'simple_scaling_integral':
            intermediate = Mul(scalar, Add(Mul(head_coefficient, A(MEASURE, head_event)), si(tail)))
            original = ax('simple_integral_cons', head, tail)
        else:
            intermediate = Mul(scalar, Add(Mul(head_coefficient, A(INDICATOR, head_event, point)), val(tail, point)))
            original = ax('simple_value_cons', head, tail, point)
        step = eq_trans(left, right, intermediate, step, ring(right, intermediate))
        step = rewrite(kernel, step, original, True)
        if name == 'simple_scaling_value':
            step = close(step, (point,))
        induction = ('list_induction', simple, head, tail, predicate, base, close(step, (head, tail), (tail_hypothesis,)))
        kernel.theorem(name, alls((scalar, simple), predicate), close(induction, (scalar,)))
    predicate = Imp(A(SIMPLE_VALID, simple), A(SIMPLE_VALID, A(SIMPLE_SCALE, scalar, simple)))
    base = rewrite(kernel, ('axiom', 'valid_simple_nil'), ax('simple_scale_nil', scalar), True)
    base = close(base, assumptions=(A(SIMPLE_VALID, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    cons_valid = A(SIMPLE_VALID, cons)
    validity = apply(('and_l', ax('valid_simple_cons', head, tail)), hyp(cons_valid))
    scaled_head_measurable = rewrite(kernel, ('and_l', validity), ax('simple_pair_event', Mul(scalar, head_coefficient), head_event), True)
    scaled_tail_valid = apply(hyp(tail_hypothesis), ('and_r', validity))
    step = apply(('and_r', ax('valid_simple_cons', scaled_head, scaled_tail)), ('and_i', scaled_head_measurable, scaled_tail_valid))
    step = rewrite(kernel, step, ax('simple_scale_cons', scalar, head, tail), True)
    step = close(close(step, assumptions=(cons_valid,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    kernel.theorem('simple_scaling_valid', alls((scalar, simple), predicate), close(induction, (scalar,)))
    other = V('other_simple', SIMPLE)
    predicates = (
        ('simple_append_integral', Eq(si(A(SIMPLE_APPEND, simple, other)), Add(si(simple), si(other)))),
        ('simple_append_value', All(point, Eq(val(A(SIMPLE_APPEND, simple, other), point), Add(val(simple, point), val(other, point)))))
    )
    for name, predicate in predicates:
        tail_hypothesis = substitute(predicate, simple, tail)
        if name == 'simple_append_integral':
            base = ring(si(other), Add(RZERO, si(other)))
            base = ('eq_e', symmetric(si(SIMPLE_NIL), RZERO, ('axiom', 'simple_integral_nil')), V('append_placeholder', 'R'), Eq(si(other), Add(V('append_placeholder', 'R'), si(other))), base)
            base = ('eq_e', symmetric(A(SIMPLE_APPEND, SIMPLE_NIL, other), other, ax('simple_append_nil', other)), V('append_simple_placeholder', SIMPLE), Eq(si(V('append_simple_placeholder', SIMPLE)), Add(si(SIMPLE_NIL), si(other))), base)
            step = ax('simple_integral_cons', head, A(SIMPLE_APPEND, tail, other))
            step = rewrite(kernel, step, hyp(tail_hypothesis))
            target = Add(Add(Mul(head_coefficient, A(MEASURE, head_event)), si(tail)), si(other))
            original = ax('simple_integral_cons', head, tail)
        else:
            base = ring(val(other, point), Add(RZERO, val(other, point)))
            base = ('eq_e', symmetric(val(SIMPLE_NIL, point), RZERO, ax('simple_value_nil', point)), V('append_placeholder', 'R'), Eq(val(other, point), Add(V('append_placeholder', 'R'), val(other, point))), base)
            base = ('eq_e', symmetric(A(SIMPLE_APPEND, SIMPLE_NIL, other), other, ax('simple_append_nil', other)), V('append_simple_placeholder', SIMPLE), Eq(val(V('append_simple_placeholder', SIMPLE), point), Add(val(SIMPLE_NIL, point), val(other, point))), base)
            base = close(base, (point,))
            step = ax('simple_value_cons', head, A(SIMPLE_APPEND, tail, other), point)
            step = rewrite(kernel, step, instantiate(hyp(tail_hypothesis), point))
            target = Add(Add(Mul(head_coefficient, A(INDICATOR, head_event, point)), val(tail, point)), val(other, point))
            original = ax('simple_value_cons', head, tail, point)
        step = rewrite(kernel, step, ax('simple_append_cons', head, tail, other), True)
        left, right = kernel.infer(step).conclusion[1:]
        step = eq_trans(left, right, target, step, ring(right, target))
        step = rewrite(kernel, step, original, True)
        if name == 'simple_append_value':
            step = close(step, (point,))
        induction = ('list_induction', simple, head, tail, predicate, base, close(step, (head, tail), (tail_hypothesis,)))
        kernel.theorem(name, alls((other, simple), predicate), close(induction, (other,)))
    predicate = Imp(A(SIMPLE_VALID, simple), A(SIMPLE_VALID, A(SIMPLE_APPEND, simple, other)))
    other_valid = A(SIMPLE_VALID, other)
    base = rewrite(kernel, hyp(other_valid), ax('simple_append_nil', other), True)
    base = close(base, assumptions=(A(SIMPLE_VALID, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    validity = apply(('and_l', ax('valid_simple_cons', head, tail)), hyp(cons_valid))
    append_tail_valid = apply(hyp(tail_hypothesis), ('and_r', validity))
    step = apply(('and_r', ax('valid_simple_cons', head, A(SIMPLE_APPEND, tail, other))), ('and_i', ('and_l', validity), append_tail_valid))
    step = rewrite(kernel, step, ax('simple_append_cons', head, tail, other), True)
    step = close(close(step, assumptions=(cons_valid,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    statement = All(other, Imp(other_valid, All(simple, predicate)))
    kernel.theorem('simple_append_valid', statement, close(induction, (other,), (other_valid,)))
    left, right = V('smaller_real', 'R'), V('larger_real', 'R')
    bound = hyp(Le(left, right))
    bound = ('eq_e', symmetric(Add(RZERO, left), left, ring(Add(RZERO, left), left)), V('order_placeholder', 'R'), Le(V('order_placeholder', 'R'), right), bound)
    bound = apply(ax('addition_right_forward', RZERO, left, right), bound)
    kernel.theorem('difference_nonnegative_from_order', alls((left, right), Imp(Le(left, right), Le(RZERO, Sub(right, left)))), close(bound, (left, right), (Le(left, right),)))
    bound = apply(ax('addition_right_backward', RZERO, left, right), hyp(Le(RZERO, Sub(right, left))))
    bound = rewrite(kernel, bound, ring(Add(RZERO, left), left))
    kernel.theorem('order_from_difference_nonnegative', alls((left, right), Imp(Le(RZERO, Sub(right, left)), Le(left, right))), close(bound, (left, right), (Le(RZERO, Sub(right, left)),)))
    left, right = V('smaller_simple', SIMPLE), V('larger_simple', SIMPLE)
    negative_one = Sub(RZERO, RONE)
    difference = A(SIMPLE_APPEND, right, A(SIMPLE_SCALE, negative_one, left))
    conditions = (A(SIMPLE_VALID, left), A(SIMPLE_VALID, right), simple_below(left, simple_value(right)))
    scaled_valid = apply(ref('simple_scaling_valid', negative_one, left), hyp(conditions[0]))
    difference_valid = apply(instantiate(apply(ref('simple_append_valid', A(SIMPLE_SCALE, negative_one, left)), scaled_valid), right), hyp(conditions[1]))
    difference_value = ref('simple_append_value', A(SIMPLE_SCALE, negative_one, left), right, point)
    difference_value = rewrite(kernel, difference_value, ref('simple_scaling_value', negative_one, left, point))
    difference_value = rewrite(kernel, difference_value, ring(Add(val(right, point), Mul(negative_one, val(left, point))), Sub(val(right, point), val(left, point))))
    point_bound = apply(ref('difference_nonnegative_from_order', val(left, point), val(right, point)), instantiate(hyp(conditions[2]), point))
    point_bound = rewrite(kernel, point_bound, difference_value, True)
    point_bound = close(point_bound, (point,), (A(universe_event(), point),))
    positivity = apply(ref('simple_integral_nonnegative', difference, universe_event()), difference_valid, ('axiom', 'sigma_algebra_universe'), point_bound)
    positivity = rewrite(kernel, positivity, ref('simple_integral_is_unrestricted_weighted_sum', difference))
    difference_integral = ref('simple_append_integral', A(SIMPLE_SCALE, negative_one, left), right)
    difference_integral = rewrite(kernel, difference_integral, ref('simple_scaling_integral', negative_one, left))
    difference_integral = rewrite(kernel, difference_integral, ring(Add(si(right), Mul(negative_one, si(left))), Sub(si(right), si(left))))
    positivity = rewrite(kernel, positivity, difference_integral)
    conclusion = apply(ref('order_from_difference_nonnegative', si(left), si(right)), positivity)
    statement = alls((left, right), imps(conditions, Le(si(left), si(right))))
    kernel.theorem('simple_integral_monotone_from_measure', statement, close(conclusion, (left, right), conditions))
    return kernel


def by_cases(proposition, positive, negative):
    return ('or_e', logical(Or(proposition, Imp(proposition, BOTTOM))), positive, negative)


def derive_simple_restriction(kernel):
    left, right, point = V('left_event', EVENT), V('right_event', EVENT), V('omega', OMEGA)
    p, q = A(left, point), A(right, point)
    intersection = event_intersection(left, right)
    branches = {}
    for pvalue in (False, True):
        for qvalue in (False, True):
            ph = p if pvalue else Imp(p, BOTTOM)
            qh = q if qvalue else Imp(q, BOTTOM)
            value = RONE if pvalue and qvalue else RZERO
            condition = A(intersection, point) if pvalue and qvalue else Imp(A(intersection, point), BOTTOM)
            condition_proof = apply(logical(imps((ph, qh), condition)), hyp(ph), hyp(qh))
            identity = apply(ax('indicator_inside' if pvalue and qvalue else 'indicator_outside', intersection, point), condition_proof)
            target = Mul(RONE if pvalue else RZERO, RONE if qvalue else RZERO)
            identity = eq_trans(A(INDICATOR, intersection, point), value, target, identity, ring(value, target))
            placeholder = V('indicator_placeholder', 'R')
            pidentity = apply(ax('indicator_inside' if pvalue else 'indicator_outside', left, point), hyp(ph))
            qidentity = apply(ax('indicator_inside' if qvalue else 'indicator_outside', right, point), hyp(qh))
            identity = ('eq_e', symmetric(A(INDICATOR, left, point), RONE if pvalue else RZERO, pidentity), placeholder, Eq(A(INDICATOR, intersection, point), Mul(placeholder, RONE if qvalue else RZERO)), identity)
            identity = ('eq_e', symmetric(A(INDICATOR, right, point), RONE if qvalue else RZERO, qidentity), placeholder, Eq(A(INDICATOR, intersection, point), Mul(A(INDICATOR, left, point), placeholder)), identity)
            branches[pvalue, qvalue] = identity
    proof = by_cases(p, by_cases(q, branches[True, True], branches[True, False]), by_cases(q, branches[False, True], branches[False, False]))
    statement = alls((left, right, point), Eq(A(INDICATOR, intersection, point), Mul(A(INDICATOR, left, point), A(INDICATOR, right, point))))
    kernel.theorem('indicator_intersection_product', statement, close(proof, (left, right, point)))
    simple, head, tail = V('finite_simple', SIMPLE), V('fresh_head', SIMPLE_HEAD), V('fresh_tail', SIMPLE)
    event = V('restriction_event', EVENT)
    head_coefficient, head_event = A(SIMPLE_COEFFICIENT, head), A(SIMPLE_EVENT, head)
    restricted_head = pair(head_coefficient, event_intersection(head_event, event))
    restricted_tail = A(SIMPLE_RESTRICT, tail, event)
    predicates = (
        ('simple_restriction_integral', Eq(si(A(SIMPLE_RESTRICT, simple, event)), restricted_integral(simple, event))),
        ('simple_restriction_value', All(point, Eq(val(A(SIMPLE_RESTRICT, simple, event), point), Mul(A(INDICATOR, event, point), val(simple, point)))))
    )
    for name, predicate in predicates:
        tail_hypothesis = substitute(predicate, simple, tail)
        if name == 'simple_restriction_integral':
            base = rewrite(kernel, ('axiom', 'simple_integral_nil'), ax('simple_restrict_nil', event), True)
            base = ('eq_e', symmetric(restricted_integral(SIMPLE_NIL, event), RZERO, ax('restricted_integral_nil', event)), V('restriction_placeholder', 'R'), Eq(si(A(SIMPLE_RESTRICT, SIMPLE_NIL, event)), V('restriction_placeholder', 'R')), base)
            step = ax('simple_integral_cons', restricted_head, restricted_tail)
            step = rewrite(kernel, step, hyp(tail_hypothesis))
        else:
            base = rewrite(kernel, ax('simple_value_nil', point), ax('simple_restrict_nil', event), True)
            base = ('eq_e', symmetric(Mul(A(INDICATOR, event, point), RZERO), RZERO, ring(Mul(A(INDICATOR, event, point), RZERO), RZERO)), V('restriction_placeholder', 'R'), Eq(val(A(SIMPLE_RESTRICT, SIMPLE_NIL, event), point), V('restriction_placeholder', 'R')), base)
            base = ('eq_e', symmetric(val(SIMPLE_NIL, point), RZERO, ax('simple_value_nil', point)), V('restriction_placeholder', 'R'), Eq(val(A(SIMPLE_RESTRICT, SIMPLE_NIL, event), point), Mul(A(INDICATOR, event, point), V('restriction_placeholder', 'R'))), base)
            base = close(base, (point,))
            step = ax('simple_value_cons', restricted_head, restricted_tail, point)
            step = rewrite(kernel, step, instantiate(hyp(tail_hypothesis), point))
        step = rewrite(kernel, step, ax('simple_pair_coefficient', head_coefficient, event_intersection(head_event, event)))
        step = rewrite(kernel, step, ax('simple_pair_event', head_coefficient, event_intersection(head_event, event)))
        step = rewrite(kernel, step, ax('simple_restrict_cons', head, tail, event), True)
        if name == 'simple_restriction_integral':
            step = rewrite(kernel, step, ax('restricted_integral_cons', head, tail, event), True)
        else:
            step = rewrite(kernel, step, ref('indicator_intersection_product', head_event, event, point))
            left_term, right_term = kernel.infer(step).conclusion[1:]
            target = Mul(A(INDICATOR, event, point), Add(Mul(head_coefficient, A(INDICATOR, head_event, point)), val(tail, point)))
            step = eq_trans(left_term, right_term, target, step, ring(right_term, target))
            step = rewrite(kernel, step, ax('simple_value_cons', head, tail, point), True)
            step = close(step, (point,))
        induction = ('list_induction', simple, head, tail, predicate, base, close(step, (head, tail), (tail_hypothesis,)))
        kernel.theorem(name, alls((event, simple), predicate), close(induction, (event,)))
    predicate = Imp(A(SIMPLE_VALID, simple), A(SIMPLE_VALID, A(SIMPLE_RESTRICT, simple, event)))
    measurable = A(MEASURABLE, event)
    base = rewrite(kernel, ('axiom', 'valid_simple_nil'), ax('simple_restrict_nil', event), True)
    base = close(base, assumptions=(A(SIMPLE_VALID, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    cons = A(SIMPLE_CONS, head, tail)
    cons_valid = A(SIMPLE_VALID, cons)
    validity = apply(('and_l', ax('valid_simple_cons', head, tail)), hyp(cons_valid))
    head_measurable = apply(ref('measurable_intersection', head_event, event), ('and_l', validity), hyp(measurable))
    head_measurable = rewrite(kernel, head_measurable, ax('simple_pair_event', head_coefficient, event_intersection(head_event, event)), True)
    tail_valid = apply(hyp(tail_hypothesis), ('and_r', validity))
    step = apply(('and_r', ax('valid_simple_cons', restricted_head, restricted_tail)), ('and_i', head_measurable, tail_valid))
    step = rewrite(kernel, step, ax('simple_restrict_cons', head, tail, event), True)
    step = close(close(step, assumptions=(cons_valid,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    statement = All(event, Imp(measurable, All(simple, predicate)))
    kernel.theorem('simple_restriction_valid', statement, close(induction, (event,), (measurable,)))
    return kernel


def simple_threshold(offset, simple):
    point = V('threshold_point', OMEGA)
    return Lam(point, Le(RZERO, Add(offset, val(simple, point))))


def comparison_event(left, right):
    point = V('comparison_point', OMEGA)
    return Lam(point, Le(val(left, point), val(right, point)))


def derive_simple_threshold_measurable(kernel):
    simple, head, tail = V('finite_simple', SIMPLE), V('fresh_head', SIMPLE_HEAD), V('fresh_tail', SIMPLE)
    offset, point = V('threshold_offset', 'R'), V('omega', OMEGA)
    predicate = All(offset, Imp(A(SIMPLE_VALID, simple), A(MEASURABLE, simple_threshold(offset, simple))))
    bound = Le(RZERO, offset)
    empty, universe = empty_event(), universe_event()
    base_event = simple_threshold(offset, SIMPLE_NIL)
    expression = ax('simple_value_nil', point)
    placeholder = V('threshold_placeholder', 'R')
    expression = ('eq_e', expression, placeholder, Eq(Add(offset, val(SIMPLE_NIL, point)), Add(offset, placeholder)), ('eq_i', Add(offset, val(SIMPLE_NIL, point))))
    expression = eq_trans(Add(offset, val(SIMPLE_NIL, point)), Add(offset, RZERO), offset, expression, ring(Add(offset, RZERO), offset))
    equivalence = ('eq_e', expression, placeholder, Iff(A(base_event, point), Le(RZERO, placeholder)), logical(Iff(A(base_event, point), A(base_event, point))))
    positive_equivalence = apply(logical(imps((Iff(A(base_event, point), bound), bound), Iff(A(base_event, point), A(universe, point)))), equivalence, hyp(bound))
    negative_equivalence = apply(logical(imps((Iff(A(base_event, point), bound), Imp(bound, BOTTOM)), Iff(A(base_event, point), A(empty, point)))), equivalence, hyp(Imp(bound, BOTTOM)))
    positive_identity = extensional_event(base_event, universe, close(positive_equivalence, (point,)))
    negative_identity = extensional_event(base_event, empty, close(negative_equivalence, (point,)))
    positive = rewrite(kernel, ('axiom', 'sigma_algebra_universe'), positive_identity, True)
    negative = rewrite(kernel, ('axiom', 'sigma_algebra_empty'), negative_identity, True)
    base = close(by_cases(bound, positive, negative), (offset,), (A(SIMPLE_VALID, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    cons = A(SIMPLE_CONS, head, tail)
    cons_valid = A(SIMPLE_VALID, cons)
    validity = apply(('and_l', ax('valid_simple_cons', head, tail)), hyp(cons_valid))
    head_event, coefficient = A(SIMPLE_EVENT, head), A(SIMPLE_COEFFICIENT, head)
    shifted_tail = simple_threshold(Add(offset, coefficient), tail)
    unshifted_tail = simple_threshold(offset, tail)
    inside, outside = event_intersection(head_event, shifted_tail), event_difference(unshifted_tail, head_event)
    decomposition = event_union(inside, outside)
    shifted_measurable = apply(instantiate(hyp(tail_hypothesis), Add(offset, coefficient)), ('and_r', validity))
    unshifted_measurable = apply(instantiate(hyp(tail_hypothesis), offset), ('and_r', validity))
    inside_measurable = apply(ref('measurable_intersection', head_event, shifted_tail), ('and_l', validity), shifted_measurable)
    outside_measurable = apply(ax('sigma_algebra_difference', unshifted_tail, head_event), unshifted_measurable, ('and_l', validity))
    decomposition_measurable = apply(ax('sigma_algebra_finite_union', inside, outside), inside_measurable, outside_measurable)
    original = simple_threshold(offset, cons)
    membership = A(head_event, point)
    branches = {}
    for present in (True, False):
        assumption = membership if present else Imp(membership, BOTTOM)
        expression = ax('simple_value_cons', head, tail, point)
        expression = rewrite(kernel, expression, apply(ax('indicator_inside' if present else 'indicator_outside', head_event, point), hyp(assumption)))
        expression = ('eq_e', expression, placeholder, Eq(Add(offset, val(cons, point)), Add(offset, placeholder)), ('eq_i', Add(offset, val(cons, point))))
        current = kernel.infer(expression).conclusion[2]
        target = Add(Add(offset, coefficient), val(tail, point)) if present else Add(offset, val(tail, point))
        expression = eq_trans(Add(offset, val(cons, point)), current, target, expression, ring(current, target))
        equivalence = ('eq_e', expression, placeholder, Iff(A(original, point), Le(RZERO, placeholder)), logical(Iff(A(original, point), A(original, point))))
        tail_event = shifted_tail if present else unshifted_tail
        branch = apply(logical(imps((Iff(A(original, point), A(tail_event, point)), assumption), Iff(A(original, point), A(decomposition, point)))), equivalence, hyp(assumption))
        branches[present] = branch
    pointwise = close(by_cases(membership, branches[True], branches[False]), (point,))
    event_identity = extensional_event(original, decomposition, pointwise)
    step = rewrite(kernel, decomposition_measurable, event_identity, True)
    step = close(close(step, (offset,), (cons_valid,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    kernel.theorem('simple_threshold_measurable_by_refinement', All(simple, predicate), induction)
    left, right = V('smaller_simple', SIMPLE), V('larger_simple', SIMPLE)
    negative_one = Sub(RZERO, RONE)
    difference = A(SIMPLE_APPEND, right, A(SIMPLE_SCALE, negative_one, left))
    conditions = (A(SIMPLE_VALID, left), A(SIMPLE_VALID, right))
    scaled_valid = apply(ref('simple_scaling_valid', negative_one, left), hyp(conditions[0]))
    difference_valid = apply(instantiate(apply(ref('simple_append_valid', A(SIMPLE_SCALE, negative_one, left)), scaled_valid), right), hyp(conditions[1]))
    difference_value = ref('simple_append_value', A(SIMPLE_SCALE, negative_one, left), right, point)
    difference_value = rewrite(kernel, difference_value, ref('simple_scaling_value', negative_one, left, point))
    difference_value = rewrite(kernel, difference_value, ring(Add(val(right, point), Mul(negative_one, val(left, point))), Sub(val(right, point), val(left, point))))
    threshold = simple_threshold(RZERO, difference)
    compare = comparison_event(left, right)
    forward = apply(ref('difference_nonnegative_from_order', val(left, point), val(right, point)), hyp(A(compare, point)))
    forward = rewrite(kernel, forward, difference_value, True)
    forward = ('eq_e', symmetric(Add(RZERO, val(difference, point)), val(difference, point), ring(Add(RZERO, val(difference, point)), val(difference, point))), placeholder, Le(RZERO, placeholder), forward)
    forward = close(forward, assumptions=(A(compare, point),))
    backward = rewrite(kernel, hyp(A(threshold, point)), ring(Add(RZERO, val(difference, point)), val(difference, point)))
    backward = rewrite(kernel, backward, difference_value)
    backward = apply(ref('order_from_difference_nonnegative', val(left, point), val(right, point)), backward)
    backward = close(backward, assumptions=(A(threshold, point),))
    event_identity = extensional_event(compare, threshold, close(('and_i', forward, backward), (point,)))
    measurable = apply(ref('simple_threshold_measurable_by_refinement', difference, RZERO), difference_valid)
    measurable = rewrite(kernel, measurable, event_identity, True)
    statement = alls((left, right), imps(conditions, A(MEASURABLE, compare)))
    kernel.theorem('simple_comparison_measurable', statement, close(measurable, (left, right), conditions))
    return kernel


def derive_nonnegative_simple(kernel):
    x, y, c = V('ordered_left', 'R'), V('ordered_right', 'R'), V('positive_scalar', 'R')
    add_axioms(kernel, {
        'real_one_positive': Lt(RZERO, RONE),
        'real_total_order': alls((x, y), Or(Le(x, y), Le(y, x))),
        'positive_multiplication_strict': alls((c, x, y), imps((Lt(RZERO, c), Lt(x, y)), Lt(Mul(c, x), Mul(c, y))))
    })
    event, point = V('event', EVENT), V('omega', OMEGA)
    inside, outside = A(event, point), Imp(A(event, point), BOTTOM)
    positive = apply(ax('positive_implies_nonnegative', RONE), ('axiom', 'real_one_positive'))
    positive = ('eq_e', symmetric(A(INDICATOR, event, point), RONE, apply(ax('indicator_inside', event, point), hyp(inside))), V('indicator_order_placeholder', 'R'), Le(RZERO, V('indicator_order_placeholder', 'R')), positive)
    zero = ('eq_e', symmetric(A(INDICATOR, event, point), RZERO, apply(ax('indicator_outside', event, point), hyp(outside))), V('indicator_order_placeholder', 'R'), Le(RZERO, V('indicator_order_placeholder', 'R')), ax('real_order_reflexive', RZERO))
    kernel.theorem('indicator_nonnegative', alls((event, point), Le(RZERO, A(INDICATOR, event, point))), close(by_cases(inside, positive, zero), (event, point)))
    simple, head, tail = V('finite_simple', SIMPLE), V('fresh_head', SIMPLE_HEAD), V('fresh_tail', SIMPLE)
    cons = A(SIMPLE_CONS, head, tail)
    predicate = Imp(A(SIMPLE_VALID_NONNEGATIVE, simple), And(A(SIMPLE_VALID, simple), simple_nonnegative(simple)))
    base_nonnegative = ('eq_e', symmetric(val(SIMPLE_NIL, point), RZERO, ax('simple_value_nil', point)), V('simple_order_placeholder', 'R'), Le(RZERO, V('simple_order_placeholder', 'R')), ax('real_order_reflexive', RZERO))
    base = close(('and_i', ('axiom', 'valid_simple_nil'), close(base_nonnegative, (point,))), assumptions=(A(SIMPLE_VALID_NONNEGATIVE, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    cons_nonnegative = A(SIMPLE_VALID_NONNEGATIVE, cons)
    validity = apply(('and_l', ax('valid_nonnegative_simple_cons', head, tail)), hyp(cons_nonnegative))
    tail_result = apply(hyp(tail_hypothesis), ('and_r', validity))
    valid = apply(('and_r', ax('valid_simple_cons', head, tail)), ('and_i', ('and_l', ('and_l', validity)), ('and_l', tail_result)))
    coefficient, head_event = A(SIMPLE_COEFFICIENT, head), A(SIMPLE_EVENT, head)
    head_nonnegative = apply(ref('product_nonnegative', coefficient, A(INDICATOR, head_event, point)), ('and_r', ('and_l', validity)), ref('indicator_nonnegative', head_event, point))
    nonnegative = apply(ref('sum_nonnegative', Mul(coefficient, A(INDICATOR, head_event, point)), val(tail, point)), head_nonnegative, instantiate(('and_r', tail_result), point))
    nonnegative = rewrite(kernel, nonnegative, ax('simple_value_cons', head, tail, point), True)
    step = close(close(('and_i', valid, close(nonnegative, (point,))), assumptions=(cons_nonnegative,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    kernel.theorem('nonnegative_simple_is_valid_and_pointwise_nonnegative', All(simple, predicate), induction)
    sequence, supremum, lower = V('real_sequence', FT('N', 'R')), V('supremum', 'R'), V('strict_lower', 'R')
    index = V('stage', 'N')
    conditions = (lub(sequence, supremum), Lt(lower, supremum))
    exists = Ex(index, Le(lower, A(sequence, index)))
    absent = Imp(exists, BOTTOM)
    opposite = Le(lower, A(sequence, index))
    contradiction = apply(hyp(absent), ('ex_i', exists, index, hyp(opposite)))
    point_bound = ('or_e', ax('real_total_order', A(sequence, index), lower), hyp(Le(A(sequence, index), lower)), ('false_e', Le(A(sequence, index), lower), contradiction))
    sup_bound = least_bound(hyp(conditions[0]), lower, close(point_bound, (index,)))
    contradiction = apply(ax('real_strict_nonstrict_inconsistent', lower, supremum), hyp(conditions[1]), sup_bound)
    contradiction = close(contradiction, assumptions=(absent,))
    result = apply(logical(Imp(Imp(absent, BOTTOM), exists)), contradiction)
    statement = alls((sequence, supremum, lower), imps(conditions, exists))
    kernel.theorem('strict_lower_than_lub_is_below_a_term', statement, close(result, (sequence, supremum, lower), conditions))
    scalar, value = V('fraction', 'R'), V('positive_value', 'R')
    conditions = (Lt(RZERO, value), Lt(scalar, RONE))
    result = apply(ax('positive_multiplication_strict', value, scalar, RONE), hyp(conditions[0]), hyp(conditions[1]))
    result = rewrite(kernel, result, ring(Mul(value, scalar), Mul(scalar, value)))
    result = rewrite(kernel, result, ring(Mul(value, RONE), value))
    kernel.theorem('strict_fraction_reduces_positive_value', alls((scalar, value), imps(conditions, Lt(Mul(scalar, value), value))), close(result, (scalar, value), conditions))
    conditions = (Lt(x, y), Le(y, c))
    opposite = Le(c, x)
    upper = apply(ax('real_order_transitive', y, c, x), hyp(conditions[1]), hyp(opposite))
    contradiction = apply(ax('real_strict_nonstrict_inconsistent', x, y), hyp(conditions[0]), upper)
    negative = close(contradiction, assumptions=(opposite,))
    add_axioms(kernel, {'real_not_reverse_nonstrict': alls((x, c), Imp(Imp(Le(c, x), BOTTOM), Lt(x, c)))})
    result = apply(ax('real_not_reverse_nonstrict', x, c), negative)
    kernel.theorem('strict_nonstrict_transitive', alls((x, y, c), imps(conditions, Lt(x, c))), close(result, (x, y, c), conditions))
    return kernel


def simple_sequence_positive(sequence):
    index = V('positive_sequence_index', 'N')
    return All(index, A(SIMPLE_VALID_NONNEGATIVE, A(sequence, index)))


def simple_sequence_increasing(sequence):
    point, index = V('increasing_point', OMEGA), V('pointwise_index', 'N')
    return All(point, increasing(Lam(index, val(A(sequence, index), point))))


def simple_pointwise_lub(sequence, function):
    point, index = V('convergence_point', OMEGA), V('pointwise_index', 'N')
    return All(point, lub(Lam(index, val(A(sequence, index), point)), A(function, point)))


def threshold_sequence(sequence, simple, fraction):
    index = V('threshold_index', 'N')
    return Lam(index, comparison_event(A(SIMPLE_SCALE, fraction, simple), A(sequence, index)))


def positive_integral_bound(function, bound):
    simple = V('integral_test_simple', SIMPLE)
    return All(simple, Imp(And(A(SIMPLE_VALID_NONNEGATIVE, simple), simple_below(simple, function)), Le(si(simple), bound)))


def has_positive_integral(function, value):
    bound = V('integral_test_bound', 'R')
    return And(positive_integral_bound(function, value), All(bound, Imp(positive_integral_bound(function, bound), Le(value, bound))))


def integral_sequence(sequence):
    index = V('simple_integral_index', 'N')
    return Lam(index, si(A(sequence, index)))


def derive_monotone_convergence(kernel):
    sequence, function = V('approximating_simples', SIMPLE_SEQUENCE), V('limit_function', FUNCTION)
    simple, scalar = V('test_simple', SIMPLE), V('fraction', 'R')
    point, index, i, j = V('omega', OMEGA), V('stage', 'N'), V('first', 'N'), V('last', 'N')
    conditions = (simple_sequence_positive(sequence), simple_sequence_increasing(sequence), simple_pointwise_lub(sequence, function), A(SIMPLE_VALID_NONNEGATIVE, simple), simple_below(simple, function), Lt(RZERO, scalar), Lt(scalar, RONE))
    events = threshold_sequence(sequence, simple, scalar)
    test_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', simple), hyp(conditions[3])))
    test_nonnegative = ('and_r', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', simple), hyp(conditions[3])))
    stage_validity = apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(sequence, index)), instantiate(hyp(conditions[0]), index))
    scaled_valid = apply(ref('simple_scaling_valid', scalar, simple), test_valid)
    stage_measurable = apply(ref('simple_comparison_measurable', A(SIMPLE_SCALE, scalar, simple), A(sequence, index)), scaled_valid, ('and_l', stage_validity))
    measurable = close(stage_measurable, (index,))
    inclusion_hypothesis = A(A(events, i), point)
    ordered = A(NLE, i, j)
    point_increasing = instantiate(hyp(conditions[1]), point)
    increasing_step = apply(instantiate(point_increasing, i, j), hyp(ordered))
    step_bound = apply(ax('real_order_transitive', val(A(SIMPLE_SCALE, scalar, simple), point), val(A(sequence, i), point), val(A(sequence, j), point)), hyp(inclusion_hypothesis), increasing_step)
    ascending = close(close(step_bound, (point,), (inclusion_hypothesis,)), (i, j), (ordered,))
    positive_value, zero_value = Lt(RZERO, val(simple, point)), Eq(val(simple, point), RZERO)
    scalar_product = Mul(scalar, val(simple, point))
    point_sequence = Lam(index, val(A(sequence, index), point))
    point_lub = instantiate(hyp(conditions[2]), point)
    test_upper = instantiate(hyp(conditions[4]), point)
    strict_lower = apply(ref('strict_fraction_reduces_positive_value', scalar, val(simple, point)), hyp(positive_value), hyp(conditions[6]))
    strict_lower = apply(ref('strict_nonstrict_transitive', scalar_product, val(simple, point), A(function, point)), strict_lower, test_upper)
    exists_lower = apply(ref('strict_lower_than_lub_is_below_a_term', point_sequence, A(function, point), scalar_product), point_lub, strict_lower)
    witness = V('threshold_witness', 'N')
    existential_formula = kernel.infer(exists_lower).conclusion
    witness_hypothesis = substitute(existential_formula[2], existential_formula[1], witness)
    witness_bound = rewrite(kernel, hyp(witness_hypothesis), ref('simple_scaling_value', scalar, simple, point), True)
    existence = Ex(index, A(A(events, index), point))
    positive_existence = ('ex_i', existence, witness, witness_bound)
    positive_existence = ('ex_e', exists_lower, witness, positive_existence)
    stage_zero_validity = apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(sequence, NZERO)), instantiate(hyp(conditions[0]), NZERO))
    zero_bound = instantiate(('and_r', stage_zero_validity), point)
    placeholder = V('threshold_order_placeholder', 'R')
    zero_bound = ('eq_e', symmetric(Mul(scalar, RZERO), RZERO, ring(Mul(scalar, RZERO), RZERO)), placeholder, Le(placeholder, val(A(sequence, NZERO), point)), zero_bound)
    zero_bound = ('eq_e', symmetric(val(simple, point), RZERO, hyp(zero_value)), placeholder, Le(Mul(scalar, placeholder), val(A(sequence, NZERO), point)), zero_bound)
    zero_bound = rewrite(kernel, zero_bound, ref('simple_scaling_value', scalar, simple, point), True)
    zero_existence = ('ex_i', existence, NZERO, zero_bound)
    alternatives = apply(ax('nonnegative_zero_or_positive', val(simple, point)), instantiate(test_nonnegative, point))
    point_existence = ('or_e', alternatives, zero_existence, positive_existence)
    direct_union = supremum_event(events)
    point_existence = ('conversion', A(direct_union, point), point_existence)
    backward = close(point_existence, assumptions=(A(universe_event(), point),))
    forward = logical(Imp(A(direct_union, point), A(universe_event(), point)))
    union_identity = extensional_event(direct_union, universe_event(), close(('and_i', forward, backward), (point,)))
    union_identity = eq_trans(countable_union(events), direct_union, universe_event(), ref('countable_union_equals_existential_union', events), union_identity)
    result = ('and_i', ('and_i', measurable, ascending), union_identity)
    statement = alls((sequence, function, simple, scalar), imps(conditions, And(And(measurable_sequence(events), event_increasing(events)), Eq(countable_union(events), universe_event()))))
    kernel.theorem('threshold_events_increase_to_universe', statement, close(result, (sequence, function, simple, scalar), conditions))
    event = A(events, index)
    restricted = A(SIMPLE_RESTRICT, simple, event)
    scaled_restricted = A(SIMPLE_SCALE, scalar, restricted)
    value_equality = ref('simple_scaling_value', scalar, restricted, point)
    value_equality = rewrite(kernel, value_equality, ref('simple_restriction_value', event, simple, point))
    inside_hypothesis = A(event, point)
    outside_hypothesis = Imp(inside_hypothesis, BOTTOM)
    inside_value = rewrite(kernel, value_equality, apply(ax('indicator_inside', event, point), hyp(inside_hypothesis)))
    inside_value = rewrite(kernel, inside_value, ring(Mul(scalar, Mul(RONE, val(simple, point))), scalar_product))
    inside_bound = rewrite(kernel, hyp(inside_hypothesis), ref('simple_scaling_value', scalar, simple, point))
    inside_bound = rewrite(kernel, inside_bound, inside_value, True)
    outside_value = rewrite(kernel, value_equality, apply(ax('indicator_outside', event, point), hyp(outside_hypothesis)))
    outside_value = rewrite(kernel, outside_value, ring(Mul(scalar, Mul(RZERO, val(simple, point))), RZERO))
    outside_bound = instantiate(('and_r', stage_validity), point)
    outside_bound = ('eq_e', symmetric(val(scaled_restricted, point), RZERO, outside_value), placeholder, Le(placeholder, val(A(sequence, index), point)), outside_bound)
    point_bound = by_cases(inside_hypothesis, inside_bound, outside_bound)
    bound = close(point_bound, (point,))
    statement = alls((sequence, simple, scalar, index), Imp(simple_sequence_positive(sequence), simple_below(scaled_restricted, simple_value(A(sequence, index)))))
    kernel.theorem('threshold_restriction_is_below_approximant', statement, close(bound, (sequence, simple, scalar, index), (conditions[0],)))
    common_bound = V('common_integral_bound', 'R')
    bounds = All(index, Le(si(A(sequence, index)), common_bound))
    primary_conditions = conditions[:3] + (bounds,)
    test_condition = And(A(SIMPLE_VALID_NONNEGATIVE, simple), simple_below(simple, function))
    test_positive, test_below = ('and_l', hyp(test_condition)), ('and_r', hyp(test_condition))
    fraction = And(Lt(RZERO, scalar), Lt(scalar, RONE))
    threshold_info = apply(ref('threshold_events_increase_to_universe', sequence, function, simple, scalar), *(hyp(item) for item in conditions[:3]), test_positive, test_below, ('and_l', hyp(fraction)), ('and_r', hyp(fraction)))
    events_measurable, events_increasing = ('and_l', ('and_l', threshold_info)), ('and_r', ('and_l', threshold_info))
    finite_lub = apply(ref('finite_weighted_measure_continuity', events, simple), events_measurable, events_increasing, test_positive)
    finite_lub = ('and_l', finite_lub)
    finite_lub = rewrite(kernel, finite_lub, ('and_r', threshold_info))
    finite_lub = rewrite(kernel, finite_lub, ref('simple_integral_is_unrestricted_weighted_sum', simple))
    test_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', simple), test_positive))
    restricted_valid = apply(instantiate(apply(ref('simple_restriction_valid', event), instantiate(events_measurable, index)), simple), test_valid)
    scaled_valid = apply(ref('simple_scaling_valid', scalar, restricted), restricted_valid)
    stage_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(sequence, index)), instantiate(hyp(conditions[0]), index)))
    restriction_below = apply(ref('threshold_restriction_is_below_approximant', sequence, simple, scalar, index), hyp(conditions[0]))
    local_bound = apply(ref('simple_integral_monotone_from_measure', scaled_restricted, A(sequence, index)), scaled_valid, stage_valid, restriction_below)
    local_bound = apply(ax('real_order_transitive', si(scaled_restricted), si(A(sequence, index)), common_bound), local_bound, instantiate(hyp(bounds), index))
    local_bound = rewrite(kernel, local_bound, ref('simple_scaling_integral', scalar, restricted))
    local_bound = rewrite(kernel, local_bound, ref('simple_restriction_integral', event, simple))
    scaled_lub = apply(ref('positive_scalar_preserves_lub', weighted_sequence(simple, events), si(simple), scalar), ('and_l', hyp(fraction)), finite_lub)
    fraction_bound = least_bound(scaled_lub, common_bound, close(local_bound, (index,)))
    all_fraction_bounds = close(fraction_bound, (scalar,), (fraction,))
    test_bound = apply(ref('unit_fraction_bounds_determine_order', si(simple), common_bound), all_fraction_bounds)
    result = close(test_bound, (simple,), (test_condition,))
    statement = alls((sequence, function, common_bound), imps(primary_conditions, positive_integral_bound(function, common_bound)))
    kernel.theorem('monotone_simple_approximation_integral_bound', statement, close(result, (sequence, function, common_bound), primary_conditions))
    integral = V('finite_integral', 'R')
    approximation_conditions = conditions[:3]
    integral_lub = lub(integral_sequence(sequence), integral)
    bound = V('candidate_bound', 'R')
    integral_bounds = positive_integral_bound(function, bound)
    stage_below = close(upper_bound(instantiate(hyp(conditions[2]), point), index), (point,))
    stage_bound = apply(instantiate(hyp(integral_bounds), A(sequence, index)), ('and_i', instantiate(hyp(conditions[0]), index), stage_below))
    all_stage_bounds = close(stage_bound, (index,))
    least = least_bound(hyp(integral_lub), bound, all_stage_bounds)
    least = close(least, (bound,), (integral_bounds,))
    actual_bound = apply(ref('monotone_simple_approximation_integral_bound', sequence, function, integral), *(hyp(item) for item in approximation_conditions), ('and_l', hyp(integral_lub)))
    result = ('and_i', actual_bound, least)
    statement = alls((sequence, function, integral), imps(approximation_conditions + (integral_lub,), has_positive_integral(function, integral)))
    kernel.theorem('integral_of_monotone_simple_limit', statement, close(result, (sequence, function, integral), approximation_conditions + (integral_lub,)))
    has_integral = has_positive_integral(function, integral)
    stage_bound = apply(instantiate(('and_l', hyp(has_integral)), A(sequence, index)), ('and_i', instantiate(hyp(conditions[0]), index), stage_below))
    upper = close(stage_bound, (index,))
    sequence_bounds = All(index, Le(si(A(sequence, index)), bound))
    function_bound = apply(ref('monotone_simple_approximation_integral_bound', sequence, function, bound), *(hyp(item) for item in approximation_conditions), hyp(sequence_bounds))
    least = apply(instantiate(('and_r', hyp(has_integral)), bound), function_bound)
    least = close(least, (bound,), (sequence_bounds,))
    statement = alls((sequence, function, integral), imps(approximation_conditions + (has_integral,), integral_lub))
    kernel.theorem('monotone_simple_integrals_converge', statement, close(('and_i', upper, least), (sequence, function, integral), approximation_conditions + (has_integral,)))
    return kernel


EVENT_FAMILY = FT(EVENT, 'Prop')
SIMPLE_ADAPTED = C('simple_adapted', FT(EVENT_FAMILY, FT(SIMPLE, 'Prop')))
SIMPLE_PRODUCT = C('simple_product', FT(SIMPLE, FT(SIMPLE, SIMPLE)))


def independent_event_families(left, right):
    a, b = V('independent_left_event', EVENT), V('independent_right_event', EVENT)
    return alls((a, b), imps((A(left, a), A(right, b)), Eq(A(MEASURE, event_intersection(a, b)), Mul(A(MEASURE, a), A(MEASURE, b)))))


def simple_product_axioms():
    head, tail, other = V('product_head', SIMPLE_HEAD), V('product_tail', SIMPLE), V('product_other', SIMPLE)
    family = V('event_family', EVENT_FAMILY)
    cons = A(SIMPLE_CONS, head, tail)
    restricted = A(SIMPLE_RESTRICT, other, A(SIMPLE_EVENT, head))
    return {
        'simple_adapted_nil': All(family, A(SIMPLE_ADAPTED, family, SIMPLE_NIL)),
        'simple_adapted_cons': alls((family, head, tail), Iff(A(SIMPLE_ADAPTED, family, cons), And(A(family, A(SIMPLE_EVENT, head)), A(SIMPLE_ADAPTED, family, tail)))),
        'simple_product_nil': All(other, Eq(A(SIMPLE_PRODUCT, SIMPLE_NIL, other), SIMPLE_NIL)),
        'simple_product_cons': alls((head, tail, other), Eq(A(SIMPLE_PRODUCT, cons, other), A(SIMPLE_APPEND, A(SIMPLE_SCALE, A(SIMPLE_COEFFICIENT, head), restricted), A(SIMPLE_PRODUCT, tail, other))))
    }


def derive_simple_product_factorization(kernel):
    add_axioms(kernel, simple_product_axioms())
    simple, head, tail = V('finite_simple', SIMPLE), V('fresh_head', SIMPLE_HEAD), V('fresh_tail', SIMPLE)
    other, point = V('other_simple', SIMPLE), V('omega', OMEGA)
    cons = A(SIMPLE_CONS, head, tail)
    coefficient, head_event = A(SIMPLE_COEFFICIENT, head), A(SIMPLE_EVENT, head)
    predicate = All(point, Eq(val(A(SIMPLE_PRODUCT, simple, other), point), Mul(val(simple, point), val(other, point))))
    base = rewrite(kernel, ax('simple_value_nil', point), ax('simple_product_nil', other), True)
    placeholder = V('product_placeholder', 'R')
    base = ('eq_e', symmetric(Mul(RZERO, val(other, point)), RZERO, ring(Mul(RZERO, val(other, point)), RZERO)), placeholder, Eq(val(A(SIMPLE_PRODUCT, SIMPLE_NIL, other), point), placeholder), base)
    base = ('eq_e', symmetric(val(SIMPLE_NIL, point), RZERO, ax('simple_value_nil', point)), placeholder, Eq(val(A(SIMPLE_PRODUCT, SIMPLE_NIL, other), point), Mul(placeholder, val(other, point))), base)
    base = close(base, (point,))
    tail_hypothesis = substitute(predicate, simple, tail)
    restricted = A(SIMPLE_RESTRICT, other, head_event)
    scaled = A(SIMPLE_SCALE, coefficient, restricted)
    tail_product = A(SIMPLE_PRODUCT, tail, other)
    step = ref('simple_append_value', tail_product, scaled, point)
    step = rewrite(kernel, step, ref('simple_scaling_value', coefficient, restricted, point))
    step = rewrite(kernel, step, ref('simple_restriction_value', head_event, other, point))
    step = rewrite(kernel, step, instantiate(hyp(tail_hypothesis), point))
    step = rewrite(kernel, step, ax('simple_product_cons', head, tail, other), True)
    left, right = kernel.infer(step).conclusion[1:]
    target = Mul(Add(Mul(coefficient, A(INDICATOR, head_event, point)), val(tail, point)), val(other, point))
    step = eq_trans(left, right, target, step, ring(right, target))
    step = rewrite(kernel, step, ax('simple_value_cons', head, tail, point), True)
    induction = ('list_induction', simple, head, tail, predicate, base, close(close(step, (point,)), (head, tail), (tail_hypothesis,)))
    kernel.theorem('simple_product_value', alls((other, simple), predicate), close(induction, (other,)))
    left_family, right_family = V('left_family', EVENT_FAMILY), V('right_family', EVENT_FAMILY)
    event = V('independent_event', EVENT)
    independence = independent_event_families(left_family, right_family)
    event_adapted = A(left_family, event)
    predicate = Imp(A(SIMPLE_ADAPTED, right_family, simple), Eq(restricted_integral(simple, event), Mul(A(MEASURE, event), si(simple))))
    base = ax('restricted_integral_nil', event)
    base = ('eq_e', symmetric(Mul(A(MEASURE, event), RZERO), RZERO, ring(Mul(A(MEASURE, event), RZERO), RZERO)), placeholder, Eq(restricted_integral(SIMPLE_NIL, event), placeholder), base)
    base = ('eq_e', symmetric(si(SIMPLE_NIL), RZERO, ('axiom', 'simple_integral_nil')), placeholder, Eq(restricted_integral(SIMPLE_NIL, event), Mul(A(MEASURE, event), placeholder)), base)
    base = close(base, assumptions=(A(SIMPLE_ADAPTED, right_family, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    adapted = A(SIMPLE_ADAPTED, right_family, cons)
    adaptation = apply(('and_l', ax('simple_adapted_cons', right_family, head, tail)), hyp(adapted))
    cell_factor = apply(instantiate(hyp(independence), event, head_event), hyp(event_adapted), ('and_l', adaptation))
    commutation = extensional_event(event_intersection(head_event, event), event_intersection(event, head_event), close(logical(Iff(A(event_intersection(head_event, event), point), A(event_intersection(event, head_event), point))), (point,)))
    step = ax('restricted_integral_cons', head, tail, event)
    step = rewrite(kernel, step, commutation)
    step = rewrite(kernel, step, cell_factor)
    step = rewrite(kernel, step, apply(hyp(tail_hypothesis), ('and_r', adaptation)))
    left, right = kernel.infer(step).conclusion[1:]
    target = Mul(A(MEASURE, event), Add(Mul(coefficient, A(MEASURE, head_event)), si(tail)))
    step = eq_trans(left, right, target, step, ring(right, target))
    step = rewrite(kernel, step, ax('simple_integral_cons', head, tail), True)
    step = close(close(step, assumptions=(adapted,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    statement = alls((left_family, right_family, event), imps((independence, event_adapted), All(simple, predicate)))
    kernel.theorem('simple_integral_on_independent_event', statement, close(induction, (left_family, right_family, event), (independence, event_adapted)))
    adapted_other = A(SIMPLE_ADAPTED, right_family, other)
    predicate = Imp(A(SIMPLE_ADAPTED, left_family, simple), Eq(si(A(SIMPLE_PRODUCT, simple, other)), Mul(si(simple), si(other))))
    base = rewrite(kernel, ('axiom', 'simple_integral_nil'), ax('simple_product_nil', other), True)
    base = ('eq_e', symmetric(Mul(RZERO, si(other)), RZERO, ring(Mul(RZERO, si(other)), RZERO)), placeholder, Eq(si(A(SIMPLE_PRODUCT, SIMPLE_NIL, other)), placeholder), base)
    base = ('eq_e', symmetric(si(SIMPLE_NIL), RZERO, ('axiom', 'simple_integral_nil')), placeholder, Eq(si(A(SIMPLE_PRODUCT, SIMPLE_NIL, other)), Mul(placeholder, si(other))), base)
    base = close(base, assumptions=(A(SIMPLE_ADAPTED, left_family, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    adapted = A(SIMPLE_ADAPTED, left_family, cons)
    adaptation = apply(('and_l', ax('simple_adapted_cons', left_family, head, tail)), hyp(adapted))
    restricted_factor = apply(instantiate(apply(ref('simple_integral_on_independent_event', left_family, right_family, head_event), hyp(independence), ('and_l', adaptation)), other), hyp(adapted_other))
    restricted = A(SIMPLE_RESTRICT, other, head_event)
    scaled = A(SIMPLE_SCALE, coefficient, restricted)
    tail_product = A(SIMPLE_PRODUCT, tail, other)
    step = ref('simple_append_integral', tail_product, scaled)
    step = rewrite(kernel, step, ref('simple_scaling_integral', coefficient, restricted))
    step = rewrite(kernel, step, ref('simple_restriction_integral', head_event, other))
    step = rewrite(kernel, step, restricted_factor)
    step = rewrite(kernel, step, apply(hyp(tail_hypothesis), ('and_r', adaptation)))
    step = rewrite(kernel, step, ax('simple_product_cons', head, tail, other), True)
    left, right = kernel.infer(step).conclusion[1:]
    target = Mul(Add(Mul(coefficient, A(MEASURE, head_event)), si(tail)), si(other))
    step = eq_trans(left, right, target, step, ring(right, target))
    step = rewrite(kernel, step, ax('simple_integral_cons', head, tail), True)
    step = close(close(step, assumptions=(adapted,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    statement = alls((left_family, right_family, other), imps((independence, adapted_other), All(simple, predicate)))
    kernel.theorem('independent_simple_products_factor', statement, close(induction, (left_family, right_family, other), (independence, adapted_other)))
    return kernel


def simple_sequence_adapted(sequence, family):
    index = V('adapted_sequence_index', 'N')
    return All(index, A(SIMPLE_ADAPTED, family, A(sequence, index)))


def product_function(left, right):
    point = V('product_function_point', OMEGA)
    return Lam(point, Mul(A(left, point), A(right, point)))


def product_simple_sequence(left, right):
    index = V('product_sequence_index', 'N')
    return Lam(index, A(SIMPLE_PRODUCT, A(left, index), A(right, index)))


def derive_nonnegative_operations(kernel):
    simple, head, tail = V('finite_simple', SIMPLE), V('fresh_head', SIMPLE_HEAD), V('fresh_tail', SIMPLE)
    scalar, event = V('scalar', 'R'), V('event', EVENT)
    cons = A(SIMPLE_CONS, head, tail)
    coefficient, head_event = A(SIMPLE_COEFFICIENT, head), A(SIMPLE_EVENT, head)
    nn = SIMPLE_VALID_NONNEGATIVE
    for kind in ('scale', 'restrict'):
        if kind == 'scale':
            operation = lambda s: A(SIMPLE_SCALE, scalar, s)
            transformed_head = pair(Mul(scalar, coefficient), head_event)
            conditions = (Le(RZERO, scalar),)
            nil_identity = ax('simple_scale_nil', scalar)
            cons_identity = ax('simple_scale_cons', scalar, head, tail)
            variable = scalar
        else:
            operation = lambda s: A(SIMPLE_RESTRICT, s, event)
            transformed_head = pair(coefficient, event_intersection(head_event, event))
            conditions = (A(MEASURABLE, event),)
            nil_identity = ax('simple_restrict_nil', event)
            cons_identity = ax('simple_restrict_cons', head, tail, event)
            variable = event
        predicate = Imp(A(nn, simple), A(nn, operation(simple)))
        base = rewrite(kernel, ('axiom', 'valid_nonnegative_simple_nil'), nil_identity, True)
        base = close(base, assumptions=(A(nn, SIMPLE_NIL),))
        tail_hypothesis = substitute(predicate, simple, tail)
        cons_valid = A(nn, cons)
        validity = apply(('and_l', ax('valid_nonnegative_simple_cons', head, tail)), hyp(cons_valid))
        head_measurable, head_nonnegative = ('and_l', ('and_l', validity)), ('and_r', ('and_l', validity))
        if kind == 'scale':
            transformed_nonnegative = apply(ref('product_nonnegative', scalar, coefficient), hyp(conditions[0]), head_nonnegative)
            transformed_nonnegative = rewrite(kernel, transformed_nonnegative, ax('simple_pair_coefficient', Mul(scalar, coefficient), head_event), True)
            transformed_measurable = rewrite(kernel, head_measurable, ax('simple_pair_event', Mul(scalar, coefficient), head_event), True)
        else:
            transformed_measurable = apply(ref('measurable_intersection', head_event, event), head_measurable, hyp(conditions[0]))
            transformed_measurable = rewrite(kernel, transformed_measurable, ax('simple_pair_event', coefficient, event_intersection(head_event, event)), True)
            transformed_nonnegative = rewrite(kernel, head_nonnegative, ax('simple_pair_coefficient', coefficient, event_intersection(head_event, event)), True)
        tail_validity = apply(hyp(tail_hypothesis), ('and_r', validity))
        step = apply(('and_r', ax('valid_nonnegative_simple_cons', transformed_head, operation(tail))), ('and_i', ('and_i', transformed_measurable, transformed_nonnegative), tail_validity))
        step = rewrite(kernel, step, cons_identity, True)
        step = close(close(step, assumptions=(cons_valid,)), (head, tail), (tail_hypothesis,))
        induction = ('list_induction', simple, head, tail, predicate, base, step)
        statement = All(variable, imps(conditions, All(simple, predicate)))
        kernel.theorem('nonnegative_simple_' + kind, statement, close(induction, (variable,), conditions))
    other = V('other_simple', SIMPLE)
    other_positive = A(nn, other)
    predicate = Imp(A(nn, simple), A(nn, A(SIMPLE_APPEND, simple, other)))
    base = rewrite(kernel, hyp(other_positive), ax('simple_append_nil', other), True)
    base = close(base, assumptions=(A(nn, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    cons_positive = A(nn, cons)
    validity = apply(('and_l', ax('valid_nonnegative_simple_cons', head, tail)), hyp(cons_positive))
    tail_validity = apply(hyp(tail_hypothesis), ('and_r', validity))
    step = apply(('and_r', ax('valid_nonnegative_simple_cons', head, A(SIMPLE_APPEND, tail, other))), ('and_i', ('and_l', validity), tail_validity))
    step = rewrite(kernel, step, ax('simple_append_cons', head, tail, other), True)
    step = close(close(step, assumptions=(cons_positive,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    kernel.theorem('nonnegative_simple_append', All(other, Imp(other_positive, All(simple, predicate))), close(induction, (other,), (other_positive,)))
    predicate = Imp(A(nn, simple), A(nn, A(SIMPLE_PRODUCT, simple, other)))
    base = rewrite(kernel, ('axiom', 'valid_nonnegative_simple_nil'), ax('simple_product_nil', other), True)
    base = close(base, assumptions=(A(nn, SIMPLE_NIL),))
    tail_hypothesis = substitute(predicate, simple, tail)
    validity = apply(('and_l', ax('valid_nonnegative_simple_cons', head, tail)), hyp(cons_positive))
    restricted = A(SIMPLE_RESTRICT, other, head_event)
    restricted_positive = apply(instantiate(apply(ref('nonnegative_simple_restrict', head_event), ('and_l', ('and_l', validity))), other), hyp(other_positive))
    scaled = A(SIMPLE_SCALE, coefficient, restricted)
    scaled_positive = apply(instantiate(apply(ref('nonnegative_simple_scale', coefficient), ('and_r', ('and_l', validity))), restricted), restricted_positive)
    tail_product = A(SIMPLE_PRODUCT, tail, other)
    tail_positive = apply(hyp(tail_hypothesis), ('and_r', validity))
    step = apply(instantiate(apply(ref('nonnegative_simple_append', tail_product), tail_positive), scaled), scaled_positive)
    step = rewrite(kernel, step, ax('simple_product_cons', head, tail, other), True)
    step = close(close(step, assumptions=(cons_positive,)), (head, tail), (tail_hypothesis,))
    induction = ('list_induction', simple, head, tail, predicate, base, step)
    kernel.theorem('nonnegative_simple_product', All(other, Imp(other_positive, All(simple, predicate))), close(induction, (other,), (other_positive,)))
    point = V('omega', OMEGA)
    positive = A(nn, simple)
    validity = apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', simple), hyp(positive))
    bound = close(instantiate(('and_r', validity), point), (point,), (A(universe_event(), point),))
    integral_positive = apply(ref('simple_integral_nonnegative', simple, universe_event()), ('and_l', validity), ('axiom', 'sigma_algebra_universe'), bound)
    integral_positive = rewrite(kernel, integral_positive, ref('simple_integral_is_unrestricted_weighted_sum', simple))
    kernel.theorem('nonnegative_simple_integral_nonnegative', All(simple, Imp(positive, Le(RZERO, si(simple)))), close(integral_positive, (simple,), (positive,)))
    return kernel


def derive_nonnegative_factorization_limit(kernel):
    left, right = V('left_approximants', SIMPLE_SEQUENCE), V('right_approximants', SIMPLE_SEQUENCE)
    f, g = V('left_function', FUNCTION), V('right_function', FUNCTION)
    a, b = V('left_integral', 'R'), V('right_integral', 'R')
    gf, gg = V('left_event_family', EVENT_FAMILY), V('right_event_family', EVENT_FAMILY)
    conditions = (simple_sequence_positive(left), simple_sequence_increasing(left), simple_pointwise_lub(left, f), has_positive_integral(f, a), simple_sequence_adapted(left, gf), simple_sequence_positive(right), simple_sequence_increasing(right), simple_pointwise_lub(right, g), has_positive_integral(g, b), simple_sequence_adapted(right, gg), independent_event_families(gf, gg))
    index, point, i, j = V('stage', 'N'), V('omega', OMEGA), V('first', 'N'), V('last', 'N')
    products = product_simple_sequence(left, right)
    fg = product_function(f, g)
    nn_left, nn_right = instantiate(hyp(conditions[0]), index), instantiate(hyp(conditions[5]), index)
    product_nn = apply(instantiate(apply(ref('nonnegative_simple_product', A(right, index)), nn_right), A(left, index)), nn_left)
    product_nn = close(product_nn, (index,))
    left_values = Lam(index, val(A(left, index), point))
    right_values = Lam(index, val(A(right, index), point))
    left_nonnegative = close(instantiate(('and_r', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(left, index)), nn_left)), point), (index,))
    right_nonnegative = close(instantiate(('and_r', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(right, index)), nn_right)), point), (index,))
    left_inc, right_inc = instantiate(hyp(conditions[1]), point), instantiate(hyp(conditions[6]), point)
    left_lub, right_lub = instantiate(hyp(conditions[2]), point), instantiate(hyp(conditions[7]), point)
    product_lub = apply(ref('increasing_nonnegative_product_lub', left_values, right_values, A(f, point), A(g, point)), left_lub, right_lub, left_inc, right_inc, left_nonnegative, right_nonnegative)
    numeric_product = Lam(index, Mul(val(A(left, index), point), val(A(right, index), point)))
    actual_product = Lam(index, val(A(products, index), point))
    values_identity = apply(ax('real_sequence_extensionality', actual_product, numeric_product), close(ref('simple_product_value', A(right, index), A(left, index), point), (index,)))
    product_lub = rewrite(kernel, product_lub, values_identity, True)
    product_lub = close(product_lub, (point,))
    ordered = A(NLE, i, j)
    left_bound = apply(instantiate(left_inc, i, j), hyp(ordered))
    right_bound = apply(instantiate(right_inc, i, j), hyp(ordered))
    product_bound = apply(ref('nonnegative_product_monotone', val(A(left, i), point), val(A(right, i), point), val(A(left, j), point), val(A(right, j), point)), instantiate(left_nonnegative, i), instantiate(right_nonnegative, j), left_bound, right_bound)
    product_bound = rewrite(kernel, product_bound, ref('simple_product_value', A(right, i), A(left, i), point), True)
    product_bound = rewrite(kernel, product_bound, ref('simple_product_value', A(right, j), A(left, j), point), True)
    product_inc = close(close(product_bound, (i, j), (ordered,)), (point,))
    left_integral_lub = apply(ref('monotone_simple_integrals_converge', left, f, a), *(hyp(item) for item in conditions[:4]))
    right_integral_lub = apply(ref('monotone_simple_integrals_converge', right, g, b), *(hyp(item) for item in conditions[5:9]))
    integral_nonnegative_left = close(apply(ref('nonnegative_simple_integral_nonnegative', A(left, index)), nn_left), (index,))
    integral_nonnegative_right = close(apply(ref('nonnegative_simple_integral_nonnegative', A(right, index)), nn_right), (index,))
    integral_increasing = []
    for sequence, positivity, monotonicity in ((left, conditions[0], conditions[1]), (right, conditions[5], conditions[6])):
        first_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(sequence, i)), instantiate(hyp(positivity), i)))
        last_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(sequence, j)), instantiate(hyp(positivity), j)))
        value_bound = apply(instantiate(instantiate(hyp(monotonicity), point), i, j), hyp(ordered))
        below = close(value_bound, (point,))
        integral_bound = apply(ref('simple_integral_monotone_from_measure', A(sequence, i), A(sequence, j)), first_valid, last_valid, below)
        integral_increasing.append(close(integral_bound, (i, j), (ordered,)))
    product_integral_lub = apply(ref('increasing_nonnegative_product_lub', integral_sequence(left), integral_sequence(right), a, b), left_integral_lub, right_integral_lub, *integral_increasing, integral_nonnegative_left, integral_nonnegative_right)
    independence = hyp(conditions[10])
    right_adapted = instantiate(hyp(conditions[9]), index)
    left_adapted = instantiate(hyp(conditions[4]), index)
    factor = apply(instantiate(apply(ref('independent_simple_products_factor', gf, gg, A(right, index)), independence, right_adapted), A(left, index)), left_adapted)
    factored_sequence = Lam(index, Mul(si(A(left, index)), si(A(right, index))))
    integral_identity = apply(ax('real_sequence_extensionality', integral_sequence(products), factored_sequence), close(factor, (index,)))
    product_integral_lub = rewrite(kernel, product_integral_lub, integral_identity, True)
    result = apply(ref('integral_of_monotone_simple_limit', products, fg, Mul(a, b)), product_nn, product_inc, product_lub, product_integral_lub)
    statement = alls((left, right, f, g, a, b, gf, gg), imps(conditions, has_positive_integral(fg, Mul(a, b))))
    kernel.theorem('independent_nonnegative_limits_factor', statement, close(result, (left, right, f, g, a, b, gf, gg), conditions))
    return kernel


EXPECTATION = C('expectation', FT(FUNCTION, 'R'))
RMAX = C('real_max', FT('R', FT('R', 'R')))


def function_nonnegative(function):
    point = V('nonnegative_function_point', OMEGA)
    return All(point, Le(RZERO, A(function, point)))


def function_below(left, right):
    point = V('function_order_point', OMEGA)
    return All(point, Le(A(left, point), A(right, point)))


def upper_level(function, level):
    point = V('upper_level_point', OMEGA)
    return Lam(point, Le(level, A(function, point)))


def lower_level(function, level):
    point = V('lower_level_point', OMEGA)
    return Lam(point, Le(A(function, point), level))


def measurable_in(function, family):
    level = V('measurability_level', 'R')
    return All(level, And(A(family, upper_level(function, level)), A(family, lower_level(function, level))))


def measurable_real(function):
    return measurable_in(function, MEASURABLE)


def add_function(left, right):
    point = V('sum_function_point', OMEGA)
    return Lam(point, Add(A(left, point), A(right, point)))


def subtract_function(left, right):
    point = V('difference_function_point', OMEGA)
    return Lam(point, Sub(A(left, point), A(right, point)))


def scale_function(scalar, function):
    point = V('scalar_function_point', OMEGA)
    return Lam(point, Mul(scalar, A(function, point)))


def constant_function(value):
    point = V('constant_function_point', OMEGA)
    return Lam(point, value)


def square_function(function):
    return product_function(function, function)


def positive_part(function):
    point = V('positive_part_point', OMEGA)
    return Lam(point, A(RMAX, RZERO, A(function, point)))


def negative_part(function):
    point = V('negative_part_point', OMEGA)
    return Lam(point, A(RMAX, RZERO, Sub(RZERO, A(function, point))))


def positive_approximation(sequence, function):
    return And(And(simple_sequence_positive(sequence), simple_sequence_increasing(sequence)), simple_pointwise_lub(sequence, function))


def positive_approximable(function):
    sequence = V('positive_simple_approximation', SIMPLE_SEQUENCE)
    return Ex(sequence, positive_approximation(sequence, function))


def positive_integrable(function, value):
    return And(positive_approximable(function), has_positive_integral(function, value))


def has_signed_integral(function, value):
    positive, negative = V('signed_positive_function', FUNCTION), V('signed_negative_function', FUNCTION)
    positive_value, negative_value = V('signed_positive_value', 'R'), V('signed_negative_value', 'R')
    point = V('signed_decomposition_point', OMEGA)
    decomposition = All(point, Eq(A(function, point), Sub(A(positive, point), A(negative, point))))
    body = And(And(positive_integrable(positive, positive_value), positive_integrable(negative, negative_value)), And(decomposition, Eq(value, Sub(positive_value, negative_value))))
    return Ex(positive, Ex(negative, Ex(positive_value, Ex(negative_value, body))))


def expectation(function):
    return A(EXPECTATION, function)


def integrable(function):
    return has_signed_integral(function, expectation(function))


def square_integrable(function):
    value = V('square_integral_value', 'R')
    return And(measurable_real(function), Ex(value, has_positive_integral(square_function(function), value)))


def measurable_event_family(family):
    event = V('family_member', EVENT)
    return All(event, Imp(A(family, event), A(MEASURABLE, event)))


def independent_functions(left, right):
    left_family, right_family = V('independent_left_family', EVENT_FAMILY), V('independent_right_family', EVENT_FAMILY)
    body = And(And(measurable_event_family(left_family), measurable_event_family(right_family)), And(And(A(left_family, universe_event()), A(right_family, universe_event())), And(And(measurable_in(left, left_family), measurable_in(right, right_family)), independent_event_families(left_family, right_family))))
    return Ex(left_family, Ex(right_family, body))


def real_set_lub(real_set, value):
    x, bound = V('real_set_member', 'R'), V('real_set_bound', 'R')
    return And(All(x, Imp(A(real_set, x), Le(x, value))), All(bound, Imp(All(x, Imp(A(real_set, x), Le(x, bound))), Le(value, bound))))


def simple_constant(value):
    return A(SIMPLE_CONS, pair(value, universe_event()), SIMPLE_NIL)


def derive_positive_integral_basics(kernel):
    f, g = V('function', FUNCTION), V('other_function', FUNCTION)
    value, other_value, bound = V('integral_value', 'R'), V('other_integral_value', 'R'), V('bound', 'R')
    conditions = (has_positive_integral(f, value), has_positive_integral(f, other_value))
    first = apply(instantiate(('and_r', hyp(conditions[0])), other_value), ('and_l', hyp(conditions[1])))
    second = apply(instantiate(('and_r', hyp(conditions[1])), value), ('and_l', hyp(conditions[0])))
    unique = apply(ax('real_order_antisymmetric', value, other_value), first, second)
    kernel.theorem('positive_integral_unique', alls((f, value, other_value), imps(conditions, Eq(value, other_value))), close(unique, (f, value, other_value), conditions))
    point, simple = V('omega', OMEGA), V('test_simple', SIMPLE)
    below = And(A(SIMPLE_VALID_NONNEGATIVE, simple), simple_below(simple, f))
    conditions = (has_positive_integral(f, value), has_positive_integral(g, other_value), function_below(f, g))
    comparison = apply(ax('real_order_transitive', val(simple, point), A(f, point), A(g, point)), instantiate(('and_r', hyp(below)), point), instantiate(hyp(conditions[2]), point))
    simple_below_g = close(comparison, (point,))
    bound_for_g = apply(instantiate(('and_l', hyp(conditions[1])), simple), ('and_i', ('and_l', hyp(below)), simple_below_g))
    bound_for_f = close(bound_for_g, (simple,), (below,))
    result = apply(instantiate(('and_r', hyp(conditions[0])), other_value), bound_for_f)
    statement = alls((f, g, value, other_value), imps(conditions, Le(value, other_value)))
    kernel.theorem('positive_integral_monotone', statement, close(result, (f, g, value, other_value), conditions))
    set_sort = FT('R', 'Prop')
    real_set, member, supremum = V('real_set', set_sort), V('real_member', 'R'), V('real_supremum', 'R')
    nonempty = Ex(member, A(real_set, member))
    bounded = All(member, Imp(A(real_set, member), Le(member, bound)))
    add_axioms(kernel, {'real_dedekind_completeness': alls((real_set, bound), imps((nonempty, bounded), Ex(supremum, real_set_lub(real_set, supremum))))})
    test_simple = V('set_test_simple', SIMPLE)
    membership = And(And(A(SIMPLE_VALID_NONNEGATIVE, test_simple), simple_below(test_simple, f)), Eq(member, si(test_simple)))
    integral_set = Lam(member, Ex(test_simple, membership))
    function_positive, integral_bound = function_nonnegative(f), positive_integral_bound(f, bound)
    nil_below = instantiate(hyp(function_positive), point)
    nil_below = ('eq_e', symmetric(val(SIMPLE_NIL, point), RZERO, ax('simple_value_nil', point)), V('nil_value_placeholder', 'R'), Le(V('nil_value_placeholder', 'R'), A(f, point)), nil_below)
    nil_below = close(nil_below, (point,))
    zero_membership = ('and_i', ('and_i', ('axiom', 'valid_nonnegative_simple_nil'), nil_below), symmetric(si(SIMPLE_NIL), RZERO, ('axiom', 'simple_integral_nil')))
    zero_membership = ('ex_i', normalize(A(integral_set, RZERO)), SIMPLE_NIL, zero_membership)
    set_nonempty = ('ex_i', Ex(member, A(integral_set, member)), RZERO, zero_membership)
    witness_simple = V('fresh_set_simple', SIMPLE)
    member_formula = normalize(A(integral_set, member))
    witness_hypothesis = substitute(member_formula[2], member_formula[1], witness_simple)
    simple_bound = apply(instantiate(hyp(integral_bound), witness_simple), ('and_l', hyp(witness_hypothesis)))
    member_bound = rewrite(kernel, simple_bound, ('and_r', hyp(witness_hypothesis)), True)
    member_bound = ('ex_e', ('conversion', member_formula, hyp(A(integral_set, member))), witness_simple, member_bound)
    set_bound = close(member_bound, (member,), (A(integral_set, member),))
    supremum_exists = apply(ax('real_dedekind_completeness', integral_set, bound), set_nonempty, set_bound)
    supremum_formula = kernel.infer(supremum_exists).conclusion
    supremum_hypothesis = substitute(supremum_formula[2], supremum_formula[1], value)
    simple_hypothesis = And(A(SIMPLE_VALID_NONNEGATIVE, simple), simple_below(simple, f))
    own_membership = ('and_i', hyp(simple_hypothesis), ('eq_i', si(simple)))
    own_membership = ('ex_i', normalize(A(integral_set, si(simple))), simple, own_membership)
    simple_upper = apply(instantiate(('and_l', hyp(supremum_hypothesis)), si(simple)), own_membership)
    upper = close(simple_upper, (simple,), (simple_hypothesis,))
    other_bound = positive_integral_bound(f, other_value)
    member_bound = apply(instantiate(hyp(other_bound), witness_simple), ('and_l', hyp(witness_hypothesis)))
    member_bound = rewrite(kernel, member_bound, ('and_r', hyp(witness_hypothesis)), True)
    member_bound = ('ex_e', ('conversion', member_formula, hyp(A(integral_set, member))), witness_simple, member_bound)
    member_bound = close(member_bound, (member,), (A(integral_set, member),))
    least = apply(instantiate(('and_r', hyp(supremum_hypothesis)), other_value), member_bound)
    least = close(least, (other_value,), (other_bound,))
    has_integral = ('and_i', upper, least)
    integral_exists = Ex(value, has_positive_integral(f, value))
    result = ('ex_i', integral_exists, value, has_integral)
    result = ('ex_e', supremum_exists, value, result)
    statement = alls((f, bound), imps((function_positive, integral_bound), integral_exists))
    kernel.theorem('bounded_nonnegative_integral_exists', statement, close(result, (f, bound), (function_positive, integral_bound)))
    positive = A(SIMPLE_VALID_NONNEGATIVE, simple)
    candidate = V('candidate_simple', SIMPLE)
    candidate_condition = And(A(SIMPLE_VALID_NONNEGATIVE, candidate), simple_below(candidate, simple_value(simple)))
    simple_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', simple), hyp(positive)))
    candidate_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', candidate), ('and_l', hyp(candidate_condition))))
    upper = apply(ref('simple_integral_monotone_from_measure', candidate, simple), candidate_valid, simple_valid, ('and_r', hyp(candidate_condition)))
    upper = close(upper, (candidate,), (candidate_condition,))
    all_bounds = positive_integral_bound(simple_value(simple), bound)
    itself_below = close(ax('real_order_reflexive', val(simple, point)), (point,))
    lower = apply(instantiate(hyp(all_bounds), simple), ('and_i', hyp(positive), itself_below))
    least = close(lower, (bound,), (all_bounds,))
    statement = All(simple, Imp(positive, has_positive_integral(simple_value(simple), si(simple))))
    kernel.theorem('positive_integral_of_simple', statement, close(('and_i', upper, least), (simple,), (positive,)))
    index = V('stage', 'N')
    sequence = Lam(index, simple)
    sequence_positive = close(hyp(positive), (index,))
    sequence_increasing = close(ref('constant_sequence_increasing', val(simple, point)), (point,))
    sequence_lub = close(ref('constant_sequence_lub', val(simple, point)), (point,))
    approximation = ('and_i', ('and_i', sequence_positive, sequence_increasing), sequence_lub)
    approximation = ('ex_i', positive_approximable(simple_value(simple)), sequence, approximation)
    integral = apply(ref('positive_integral_of_simple', simple), hyp(positive))
    statement = All(simple, Imp(positive, positive_integrable(simple_value(simple), si(simple))))
    kernel.theorem('simple_is_positive_integrable', statement, close(('and_i', approximation, integral), (simple,), (positive,)))
    constant = simple_constant(value)
    head = pair(value, universe_event())
    head_measurable = rewrite(kernel, ('axiom', 'sigma_algebra_universe'), ax('simple_pair_event', value, universe_event()), True)
    coefficient_positive = rewrite(kernel, hyp(Le(RZERO, value)), ax('simple_pair_coefficient', value, universe_event()), True)
    constant_positive = apply(('and_r', ax('valid_nonnegative_simple_cons', head, SIMPLE_NIL)), ('and_i', ('and_i', head_measurable, coefficient_positive), ('axiom', 'valid_nonnegative_simple_nil')))
    value_identity = ax('simple_value_cons', head, SIMPLE_NIL, point)
    value_identity = rewrite(kernel, value_identity, ax('simple_pair_coefficient', value, universe_event()))
    value_identity = rewrite(kernel, value_identity, ax('simple_pair_event', value, universe_event()))
    value_identity = rewrite(kernel, value_identity, apply(ax('indicator_inside', universe_event(), point), logical(A(universe_event(), point))))
    value_identity = rewrite(kernel, value_identity, ax('simple_value_nil', point))
    value_identity = rewrite(kernel, value_identity, ring(Add(Mul(value, RONE), RZERO), value))
    integral_identity = ax('simple_integral_cons', head, SIMPLE_NIL)
    integral_identity = rewrite(kernel, integral_identity, ax('simple_pair_coefficient', value, universe_event()))
    integral_identity = rewrite(kernel, integral_identity, ax('simple_pair_event', value, universe_event()))
    integral_identity = rewrite(kernel, integral_identity, ('axiom', 'probability_of_universe'))
    integral_identity = rewrite(kernel, integral_identity, ('axiom', 'simple_integral_nil'))
    integral_identity = rewrite(kernel, integral_identity, ring(Add(Mul(value, RONE), RZERO), value))
    statement = All(value, Imp(Le(RZERO, value), And(A(SIMPLE_VALID_NONNEGATIVE, constant), And(All(point, Eq(val(constant, point), value)), Eq(si(constant), value)))))
    kernel.theorem('constant_simple_value_and_integral', statement, close(('and_i', constant_positive, ('and_i', close(value_identity, (point,)), integral_identity)), (value,), (Le(RZERO, value),)))
    return kernel


def planned_probability_interfaces():
    f, g = V('function', FUNCTION), V('other_function', FUNCTION)
    a, b, c = V('integral_value', 'R'), V('other_integral_value', 'R'), V('scalar', 'R')
    return {
        'signed_integral_add': alls((f, g, a, b), imps((has_signed_integral(f, a), has_signed_integral(g, b)), has_signed_integral(add_function(f, g), Add(a, b)))),
        'signed_integral_scale': alls((f, a, c), Imp(has_signed_integral(f, a), has_signed_integral(scale_function(c, f), Mul(c, a)))),
        'signed_integral_unique': alls((f, a, b), imps((has_signed_integral(f, a), has_signed_integral(f, b)), Eq(a, b))),
        'expectation_of_signed_integral': alls((f, a), Imp(has_signed_integral(f, a), Eq(expectation(f), a))),
        'l2_implies_integrable': All(f, Imp(square_integrable(f), integrable(f))),
        'l2_square_signed_integral': All(f, Imp(square_integrable(f), integrable(square_function(f)))),
        'independent_l2_product_integral': alls((f, g), imps((square_integrable(f), square_integrable(g), independent_functions(f, g)), has_signed_integral(product_function(f, g), Mul(expectation(f), expectation(g))))),
        'constant_signed_integral': All(c, has_signed_integral(constant_function(c), c))
    }


def sum_simple_sequence(left, right):
    index = V('sum_sequence_index', 'N')
    return Lam(index, A(SIMPLE_APPEND, A(left, index), A(right, index)))


def scaled_simple_sequence(scalar, sequence):
    index = V('scaled_sequence_index', 'N')
    return Lam(index, A(SIMPLE_SCALE, scalar, A(sequence, index)))


def approximation_parts(proof):
    return ('and_l', ('and_l', proof)), ('and_r', ('and_l', proof)), ('and_r', proof)


def derive_positive_linear(kernel):
    f, g = V('function', FUNCTION), V('other_function', FUNCTION)
    point = V('omega', OMEGA)
    add_axioms(kernel, {'real_function_extensionality': alls((f, g), Imp(All(point, Eq(A(f, point), A(g, point))), Eq(f, g)))})
    left, right = V('left_approximants', SIMPLE_SEQUENCE), V('right_approximants', SIMPLE_SEQUENCE)
    scalar = V('scalar', 'R')
    index, i, j = V('stage', 'N'), V('first', 'N'), V('last', 'N')
    left_condition, right_condition = positive_approximation(left, f), positive_approximation(right, g)
    left_positive, left_increasing, left_lub = approximation_parts(hyp(left_condition))
    right_positive, right_increasing, right_lub = approximation_parts(hyp(right_condition))
    left_values, right_values = Lam(index, val(A(left, index), point)), Lam(index, val(A(right, index), point))
    left_point_positive = close(instantiate(('and_r', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(left, index)), instantiate(left_positive, index))), point), (index,))
    right_point_positive = close(instantiate(('and_r', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(right, index)), instantiate(right_positive, index))), point), (index,))
    for kind in ('sum', 'product'):
        if kind == 'sum':
            sequence = sum_simple_sequence(left, right)
            function = add_function(f, g)
            positive = apply(instantiate(apply(ref('nonnegative_simple_append', A(right, index)), instantiate(right_positive, index)), A(left, index)), instantiate(left_positive, index))
            numerical = Lam(index, Add(val(A(left, index), point), val(A(right, index), point)))
            point_identity = ref('simple_append_value', A(right, index), A(left, index), point)
            limit = apply(ref('increasing_sum_lub', left_values, right_values, A(f, point), A(g, point)), instantiate(left_lub, point), instantiate(right_lub, point), instantiate(left_increasing, point), instantiate(right_increasing, point))
            monotonicity = apply(ref('sum_preserves_increasing', left_values, right_values), instantiate(left_increasing, point), instantiate(right_increasing, point))
        else:
            sequence = product_simple_sequence(left, right)
            function = product_function(f, g)
            positive = apply(instantiate(apply(ref('nonnegative_simple_product', A(right, index)), instantiate(right_positive, index)), A(left, index)), instantiate(left_positive, index))
            numerical = Lam(index, Mul(val(A(left, index), point), val(A(right, index), point)))
            point_identity = ref('simple_product_value', A(right, index), A(left, index), point)
            limit = apply(ref('increasing_nonnegative_product_lub', left_values, right_values, A(f, point), A(g, point)), instantiate(left_lub, point), instantiate(right_lub, point), instantiate(left_increasing, point), instantiate(right_increasing, point), left_point_positive, right_point_positive)
            ordered = A(NLE, i, j)
            first_bound = apply(instantiate(instantiate(left_increasing, point), i, j), hyp(ordered))
            last_bound = apply(instantiate(instantiate(right_increasing, point), i, j), hyp(ordered))
            monotonicity = apply(ref('nonnegative_product_monotone', val(A(left, i), point), val(A(right, i), point), val(A(left, j), point), val(A(right, j), point)), instantiate(left_point_positive, i), instantiate(right_point_positive, j), first_bound, last_bound)
            monotonicity = close(monotonicity, (i, j), (ordered,))
        sequence_identity = apply(ax('real_sequence_extensionality', Lam(index, val(A(sequence, index), point)), numerical), close(point_identity, (index,)))
        limit = rewrite(kernel, limit, sequence_identity, True)
        monotonicity = ('conversion', increasing(numerical), monotonicity)
        monotonicity = rewrite(kernel, monotonicity, sequence_identity, True)
        result = ('and_i', ('and_i', close(positive, (index,)), close(monotonicity, (point,))), close(limit, (point,)))
        statement = alls((left, right, f, g), imps((left_condition, right_condition), positive_approximation(sequence, function)))
        kernel.theorem('positive_approximations_' + kind, statement, close(result, (left, right, f, g), (left_condition, right_condition)))
    sequence = scaled_simple_sequence(scalar, left)
    nonnegative = Le(RZERO, scalar)
    positive = apply(instantiate(apply(ref('nonnegative_simple_scale', scalar), hyp(nonnegative)), A(left, index)), instantiate(left_positive, index))
    numerical = Lam(index, Mul(scalar, val(A(left, index), point)))
    sequence_identity = apply(ax('real_sequence_extensionality', Lam(index, val(A(sequence, index), point)), numerical), close(ref('simple_scaling_value', scalar, A(left, index), point), (index,)))
    limit = apply(ref('nonnegative_scalar_preserves_lub', left_values, A(f, point), scalar), hyp(nonnegative), instantiate(left_lub, point))
    monotonicity = apply(ref('nonnegative_scalar_preserves_increasing', left_values, scalar), hyp(nonnegative), instantiate(left_increasing, point))
    limit = rewrite(kernel, limit, sequence_identity, True)
    monotonicity = rewrite(kernel, monotonicity, sequence_identity, True)
    result = ('and_i', ('and_i', close(positive, (index,)), close(monotonicity, (point,))), close(limit, (point,)))
    statement = alls((left, f, scalar), imps((left_condition, nonnegative), positive_approximation(sequence, scale_function(scalar, f))))
    kernel.theorem('positive_approximations_scale', statement, close(result, (left, f, scalar), (left_condition, nonnegative)))
    value = V('integral_value', 'R')
    conditions = (left_condition, has_positive_integral(f, value))
    integral_lub = apply(ref('monotone_simple_integrals_converge', left, f, value), left_positive, left_increasing, left_lub, hyp(conditions[1]))
    ordered = A(NLE, i, j)
    first_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(left, i)), instantiate(left_positive, i)))
    last_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', A(left, j)), instantiate(left_positive, j)))
    point_bound = apply(instantiate(instantiate(left_increasing, point), i, j), hyp(ordered))
    monotone = apply(ref('simple_integral_monotone_from_measure', A(left, i), A(left, j)), first_valid, last_valid, close(point_bound, (point,)))
    monotone = close(monotone, (i, j), (ordered,))
    integral_positive = close(apply(ref('nonnegative_simple_integral_nonnegative', A(left, index)), instantiate(left_positive, index)), (index,))
    result = ('and_i', ('and_i', integral_lub, monotone), integral_positive)
    statement = alls((left, f, value), imps(conditions, And(And(lub(integral_sequence(left), value), increasing(integral_sequence(left))), nonnegative_sequence(integral_sequence(left)))))
    kernel.theorem('positive_approximation_integral_sequence', statement, close(result, (left, f, value), conditions))
    zero_positive = instantiate(left_point_positive, NZERO)
    value_positive = apply(ax('real_order_transitive', RZERO, val(A(left, NZERO), point), A(f, point)), zero_positive, upper_bound(instantiate(left_lub, point), NZERO))
    statement = alls((left, f), Imp(left_condition, function_nonnegative(f)))
    kernel.theorem('positive_approximation_limit_nonnegative', statement, close(close(value_positive, (point,)), (left, f), (left_condition,)))
    a, b = V('left_integral', 'R'), V('right_integral', 'R')
    left_integrable, right_integrable = positive_integrable(f, a), positive_integrable(g, b)
    left_ex = ('and_l', hyp(left_integrable))
    right_ex = ('and_l', hyp(right_integrable))
    left_instance = substitute(kernel.infer(left_ex).conclusion[2], kernel.infer(left_ex).conclusion[1], left)
    right_instance = substitute(kernel.infer(right_ex).conclusion[2], kernel.infer(right_ex).conclusion[1], right)
    left_info = apply(ref('positive_approximation_integral_sequence', left, f, a), hyp(left_instance), ('and_r', hyp(left_integrable)))
    right_info = apply(ref('positive_approximation_integral_sequence', right, g, b), hyp(right_instance), ('and_r', hyp(right_integrable)))
    sum_approx = apply(ref('positive_approximations_sum', left, right, f, g), hyp(left_instance), hyp(right_instance))
    sum_sequence = sum_simple_sequence(left, right)
    sum_positive, sum_increasing, sum_point_lub = approximation_parts(sum_approx)
    sum_lub = apply(ref('increasing_sum_lub', integral_sequence(left), integral_sequence(right), a, b), ('and_l', ('and_l', left_info)), ('and_l', ('and_l', right_info)), ('and_r', ('and_l', left_info)), ('and_r', ('and_l', right_info)))
    sum_identity = apply(ax('real_sequence_extensionality', integral_sequence(sum_sequence), Lam(index, Add(si(A(left, index)), si(A(right, index))))), close(ref('simple_append_integral', A(right, index), A(left, index)), (index,)))
    sum_lub = rewrite(kernel, sum_lub, sum_identity, True)
    sum_integral = apply(ref('integral_of_monotone_simple_limit', sum_sequence, add_function(f, g), Add(a, b)), sum_positive, sum_increasing, sum_point_lub, sum_lub)
    sum_exists = ('ex_i', positive_approximable(add_function(f, g)), sum_sequence, sum_approx)
    result = ('and_i', sum_exists, sum_integral)
    result = ('ex_e', right_ex, right, result)
    result = ('ex_e', left_ex, left, result)
    statement = alls((f, g, a, b), imps((left_integrable, right_integrable), positive_integrable(add_function(f, g), Add(a, b))))
    kernel.theorem('positive_integrable_add', statement, close(result, (f, g, a, b), (left_integrable, right_integrable)))
    scale_approx = apply(ref('positive_approximations_scale', left, f, scalar), hyp(left_instance), hyp(nonnegative))
    scaled_sequence = scaled_simple_sequence(scalar, left)
    scaled_positive, scaled_increasing, scaled_point_lub = approximation_parts(scale_approx)
    scaled_lub = apply(ref('nonnegative_scalar_preserves_lub', integral_sequence(left), a, scalar), hyp(nonnegative), ('and_l', ('and_l', left_info)))
    scaled_identity = apply(ax('real_sequence_extensionality', integral_sequence(scaled_sequence), Lam(index, Mul(scalar, si(A(left, index))))), close(ref('simple_scaling_integral', scalar, A(left, index)), (index,)))
    scaled_lub = rewrite(kernel, scaled_lub, scaled_identity, True)
    scaled_integral = apply(ref('integral_of_monotone_simple_limit', scaled_sequence, scale_function(scalar, f), Mul(scalar, a)), scaled_positive, scaled_increasing, scaled_point_lub, scaled_lub)
    scaled_exists = ('ex_i', positive_approximable(scale_function(scalar, f)), scaled_sequence, scale_approx)
    result = ('and_i', scaled_exists, scaled_integral)
    result = ('ex_e', left_ex, left, result)
    statement = alls((f, a, scalar), imps((left_integrable, nonnegative), positive_integrable(scale_function(scalar, f), Mul(scalar, a))))
    kernel.theorem('positive_integrable_scale', statement, close(result, (f, a, scalar), (left_integrable, nonnegative)))
    constant_info = apply(ref('constant_simple_value_and_integral', value), hyp(Le(RZERO, value)))
    simple = simple_constant(value)
    constant_integrable = apply(ref('simple_is_positive_integrable', simple), ('and_l', constant_info))
    constant_identity = apply(ax('real_function_extensionality', simple_value(simple), constant_function(value)), ('and_l', ('and_r', constant_info)))
    constant_integrable = rewrite(kernel, constant_integrable, constant_identity)
    constant_integrable = rewrite(kernel, constant_integrable, ('and_r', ('and_r', constant_info)))
    statement = All(value, Imp(Le(RZERO, value), positive_integrable(constant_function(value), value)))
    kernel.theorem('nonnegative_constant_positive_integrable', statement, close(constant_integrable, (value,), (Le(RZERO, value),)))
    return kernel


def open_existentials(kernel, proof, witnesses):
    frames = []
    for witness in witnesses:
        formula = kernel.infer(proof).conclusion
        if formula[0] != 'ex':
            raise ValueError('existential opening reached a non-existential')
        instance = substitute(formula[2], formula[1], witness)
        frames.append((proof, witness))
        proof = hyp(instance)
    return proof, frames


def discharge_existentials(result, frames):
    for proof, witness in reversed(frames):
        result = ('ex_e', proof, witness, result)
    return result


def introduce_existentials(formula, witnesses, proof):
    frames = []
    for witness in witnesses:
        if formula[0] != 'ex':
            raise ValueError('existential construction reached a non-existential')
        frames.append((formula, witness))
        formula = substitute(formula[2], formula[1], witness)
    for target, witness in reversed(frames):
        proof = ('ex_i', target, witness, proof)
    return proof


def equality_congruence(kernel, proof, operation):
    left, right = kernel.infer(proof).conclusion[1:]
    placeholder = V('congruence_placeholder', sort_of(left))
    occupied = free_variables(left) | free_variables(right) | free_variables(operation(left))
    while placeholder in occupied:
        placeholder = V(placeholder[1] + '_fresh', sort_of(left))
    return ('eq_e', proof, placeholder, Eq(operation(left), operation(placeholder)), ('eq_i', operation(left)))



def rewrite_right(kernel, proof, equality, reverse=False):
    original, current = kernel.infer(proof).conclusion[1:]
    left, right = kernel.infer(equality).conclusion[1:]
    if reverse:
        equality = symmetric(left, right, equality)
        left, right = right, left
    placeholder = V('right_rewrite_placeholder', sort_of(left))
    while placeholder in free_variables(original) | free_variables(current) | free_variables(left) | free_variables(right):
        placeholder = V(placeholder[1] + '_fresh', sort_of(left))
    pattern = Eq(original, replace_subterm(current, left, placeholder))
    return ('eq_e', equality, placeholder, pattern, proof)


def signed_integral_witness(function, value, positive, negative, pv, nv, p_integral, n_integral, decomposition, value_equation):
    body = ('and_i', ('and_i', p_integral, n_integral), ('and_i', decomposition, value_equation))
    return introduce_existentials(has_signed_integral(function, value), (positive, negative, pv, nv), body)


def derive_signed_linear(kernel):
    f, g = V('function', FUNCTION), V('other_function', FUNCTION)
    a, b, scalar = V('integral_value', 'R'), V('other_integral_value', 'R'), V('scalar', 'R')
    p, n, q, r = (V(name, FUNCTION) for name in ('first_positive', 'first_negative', 'second_positive', 'second_negative'))
    pv, nv, qv, rv = (V(name, 'R') for name in ('first_positive_integral', 'first_negative_integral', 'second_positive_integral', 'second_negative_integral'))
    point = V('omega', OMEGA)
    signed_f, signed_g = has_signed_integral(f, a), has_signed_integral(g, b)
    left, frames_left = open_existentials(kernel, hyp(signed_f), (p, n, pv, nv))
    right, frames_right = open_existentials(kernel, hyp(signed_g), (q, r, qv, rv))
    pi, ni = ('and_l', ('and_l', left)), ('and_r', ('and_l', left))
    qi, ri = ('and_l', ('and_l', right)), ('and_r', ('and_l', right))
    fd, gd = ('and_l', ('and_r', left)), ('and_l', ('and_r', right))
    av, bv = ('and_r', ('and_r', left)), ('and_r', ('and_r', right))
    positive, negative = add_function(p, q), add_function(n, r)
    positive_value, negative_value = Add(pv, qv), Add(nv, rv)
    positive_integral = apply(ref('positive_integrable_add', p, q, pv, qv), pi, qi)
    negative_integral = apply(ref('positive_integrable_add', n, r, nv, rv), ni, ri)
    point_identity = equality_congruence(kernel, instantiate(fd, point), lambda x: Add(x, A(g, point)))
    point_identity = rewrite_right(kernel, point_identity, instantiate(gd, point))
    original, current = kernel.infer(point_identity).conclusion[1:]
    target = Sub(Add(A(p, point), A(q, point)), Add(A(n, point), A(r, point)))
    point_identity = eq_trans(original, current, target, point_identity, ring(current, target))
    point_identity = close(point_identity, (point,))
    value_identity = equality_congruence(kernel, av, lambda x: Add(x, b))
    value_identity = rewrite_right(kernel, value_identity, bv)
    original, current = kernel.infer(value_identity).conclusion[1:]
    value_identity = eq_trans(original, current, Sub(positive_value, negative_value), value_identity, ring(current, Sub(positive_value, negative_value)))
    result = signed_integral_witness(add_function(f, g), Add(a, b), positive, negative, positive_value, negative_value, positive_integral, negative_integral, point_identity, value_identity)
    result = discharge_existentials(discharge_existentials(result, frames_right), frames_left)
    kernel.theorem('signed_integral_add', planned_probability_interfaces()['signed_integral_add'], close(result, (f, g, a, b), (signed_f, signed_g)))
    signed_same = has_signed_integral(f, b)
    right, frames_right = open_existentials(kernel, hyp(signed_same), (q, r, qv, rv))
    qi, ri = ('and_l', ('and_l', right)), ('and_r', ('and_l', right))
    gd, bv = ('and_l', ('and_r', right)), ('and_r', ('and_r', right))
    first_equation, second_equation = instantiate(fd, point), instantiate(gd, point)
    difference_equality = eq_trans(Sub(A(p, point), A(n, point)), A(f, point), Sub(A(q, point), A(r, point)), symmetric(A(f, point), Sub(A(p, point), A(n, point)), first_equation), second_equation)
    point_equality = equality_congruence(kernel, difference_equality, lambda x: Add(x, Add(A(n, point), A(r, point))))
    point_equality = rewrite(kernel, point_equality, ring(Add(Sub(A(p, point), A(n, point)), Add(A(n, point), A(r, point))), Add(A(p, point), A(r, point))))
    point_equality = rewrite(kernel, point_equality, ring(Add(Sub(A(q, point), A(r, point)), Add(A(n, point), A(r, point))), Add(A(q, point), A(n, point))))
    function_identity = apply(ax('real_function_extensionality', add_function(p, r), add_function(q, n)), close(point_equality, (point,)))
    first_sum = apply(ref('positive_integrable_add', p, r, pv, rv), pi, ri)
    second_sum = apply(ref('positive_integrable_add', q, n, qv, nv), qi, ni)
    first_sum = rewrite(kernel, first_sum, function_identity)
    value_identity = apply(ref('positive_integral_unique', add_function(q, n), Add(pv, rv), Add(qv, nv)), ('and_r', first_sum), ('and_r', second_sum))
    value_identity = equality_congruence(kernel, value_identity, lambda x: Sub(x, Add(nv, rv)))
    value_identity = rewrite(kernel, value_identity, ring(Sub(Add(pv, rv), Add(nv, rv)), Sub(pv, nv)))
    value_identity = rewrite(kernel, value_identity, ring(Sub(Add(qv, nv), Add(nv, rv)), Sub(qv, rv)))
    value_identity = rewrite(kernel, value_identity, av, True)
    value_identity = rewrite(kernel, value_identity, bv, True)
    result = discharge_existentials(discharge_existentials(value_identity, frames_right), frames_left)
    kernel.theorem('signed_integral_unique', planned_probability_interfaces()['signed_integral_unique'], close(result, (f, a, b), (signed_f, signed_same)))
    positive_scalar, negative_scalar = Le(RZERO, scalar), Le(scalar, RZERO)
    branches = {}
    for nonnegative_case in (True, False):
        if nonnegative_case:
            coefficient = scalar
            coefficient_nonnegative = hyp(positive_scalar)
            positive, negative = scale_function(coefficient, p), scale_function(coefficient, n)
            positive_value, negative_value = Mul(coefficient, pv), Mul(coefficient, nv)
            positive_integral = apply(ref('positive_integrable_scale', p, pv, coefficient), pi, coefficient_nonnegative)
            negative_integral = apply(ref('positive_integrable_scale', n, nv, coefficient), ni, coefficient_nonnegative)
        else:
            coefficient = Sub(RZERO, scalar)
            coefficient_nonnegative = apply(ref('difference_nonnegative_from_order', scalar, RZERO), hyp(negative_scalar))
            positive, negative = scale_function(coefficient, n), scale_function(coefficient, p)
            positive_value, negative_value = Mul(coefficient, nv), Mul(coefficient, pv)
            positive_integral = apply(ref('positive_integrable_scale', n, nv, coefficient), ni, coefficient_nonnegative)
            negative_integral = apply(ref('positive_integrable_scale', p, pv, coefficient), pi, coefficient_nonnegative)
        point_identity = equality_congruence(kernel, instantiate(fd, point), lambda x: Mul(scalar, x))
        original, current = kernel.infer(point_identity).conclusion[1:]
        target = Sub(A(positive, point), A(negative, point))
        point_identity = eq_trans(original, current, target, point_identity, ring(current, target))
        value_identity = equality_congruence(kernel, av, lambda x: Mul(scalar, x))
        original, current = kernel.infer(value_identity).conclusion[1:]
        value_identity = eq_trans(original, current, Sub(positive_value, negative_value), value_identity, ring(current, Sub(positive_value, negative_value)))
        branches[nonnegative_case] = signed_integral_witness(scale_function(scalar, f), Mul(scalar, a), positive, negative, positive_value, negative_value, positive_integral, negative_integral, close(point_identity, (point,)), value_identity)
    result = ('or_e', ax('real_total_order', RZERO, scalar), branches[True], branches[False])
    result = discharge_existentials(result, frames_left)
    kernel.theorem('signed_integral_scale', planned_probability_interfaces()['signed_integral_scale'], close(result, (f, a, scalar), (signed_f,)))
    zero_integrable = apply(ref('nonnegative_constant_positive_integrable', RZERO), ax('real_order_reflexive', RZERO))
    constant_branches = {}
    for nonnegative_case in (True, False):
        if nonnegative_case:
            positive, negative = constant_function(scalar), constant_function(RZERO)
            pv_value, nv_value = scalar, RZERO
            positive_integral = apply(ref('nonnegative_constant_positive_integrable', scalar), hyp(positive_scalar))
            negative_integral = zero_integrable
        else:
            positive, negative = constant_function(RZERO), constant_function(Sub(RZERO, scalar))
            pv_value, nv_value = RZERO, Sub(RZERO, scalar)
            positive_integral = zero_integrable
            coefficient_nonnegative = apply(ref('difference_nonnegative_from_order', scalar, RZERO), hyp(negative_scalar))
            negative_integral = apply(ref('nonnegative_constant_positive_integrable', Sub(RZERO, scalar)), coefficient_nonnegative)
        point_identity = close(ring(scalar, Sub(pv_value, nv_value)), (point,))
        constant_branches[nonnegative_case] = signed_integral_witness(constant_function(scalar), scalar, positive, negative, pv_value, nv_value, positive_integral, negative_integral, point_identity, ring(scalar, Sub(pv_value, nv_value)))
    result = ('or_e', ax('real_total_order', RZERO, scalar), constant_branches[True], constant_branches[False])
    kernel.theorem('constant_signed_integral', planned_probability_interfaces()['constant_signed_integral'], close(result, (scalar,)))
    real_set_sort = FT('R', 'Prop')
    real_choice = C('real_choice', FT(real_set_sort, 'R'))
    real_set = V('choice_real_set', real_set_sort)
    value = V('choice_real_value', 'R')
    chosen_set = Lam(value, has_signed_integral(f, value))
    add_axioms(kernel, {
        'real_hilbert_choice': All(real_set, Imp(Ex(value, A(real_set, value)), A(real_set, A(real_choice, real_set)))),
        'expectation_definition': All(f, Eq(expectation(f), A(real_choice, chosen_set)))
    })
    exists = ('ex_i', Ex(value, A(chosen_set, value)), a, hyp(signed_f))
    selected = apply(ax('real_hilbert_choice', chosen_set), exists)
    selected = rewrite(kernel, selected, ax('expectation_definition', f), True)
    statement = alls((f, a), Imp(signed_f, integrable(f)))
    kernel.theorem('signed_integral_implies_integrable', statement, close(selected, (f, a), (signed_f,)))
    identity = apply(ref('signed_integral_unique', f, expectation(f), a), selected, hyp(signed_f))
    kernel.theorem('expectation_of_signed_integral', planned_probability_interfaces()['expectation_of_signed_integral'], close(identity, (f, a), (signed_f,)))
    return kernel


def derive_jordan_scalar(kernel):
    x, y = V('real_value', 'R'), V('real_upper', 'R')
    add_axioms(kernel, {
        'real_max_right_definition': alls((x, y), Imp(Le(x, y), Eq(A(RMAX, x, y), y))),
        'real_max_left_definition': alls((x, y), Imp(Le(y, x), Eq(A(RMAX, x, y), x)))
    })
    conditions = (Le(x, y),)
    difference = apply(ref('difference_nonnegative_from_order', x, y), hyp(conditions[0]))
    target_difference = Sub(Sub(RZERO, x), Sub(RZERO, y))
    difference = ('eq_e', symmetric(target_difference, Sub(y, x), ring(target_difference, Sub(y, x))), V('negative_order_placeholder', 'R'), Le(RZERO, V('negative_order_placeholder', 'R')), difference)
    result = apply(ref('order_from_difference_nonnegative', Sub(RZERO, y), Sub(RZERO, x)), difference)
    kernel.theorem('negation_reverses_order', alls((x, y), Imp(Le(x, y), Le(Sub(RZERO, y), Sub(RZERO, x)))), close(result, (x, y), conditions))
    nonnegative, nonpositive = Le(RZERO, x), Le(x, RZERO)
    negx = Sub(RZERO, x)
    neg_nonnegative = apply(ref('difference_nonnegative_from_order', x, RZERO), hyp(nonpositive))
    neg_nonpositive = apply(ref('negation_reverses_order', RZERO, x), hyp(nonnegative))
    neg_nonpositive = rewrite(kernel, neg_nonpositive, ring(Sub(RZERO, RZERO), RZERO))
    positive_square = apply(ref('product_nonnegative', x, x), hyp(nonnegative), hyp(nonnegative))
    negative_square = apply(ref('product_nonnegative', negx, negx), neg_nonnegative, neg_nonnegative)
    negative_square = rewrite(kernel, negative_square, ring(Mul(negx, negx), Mul(x, x)))
    square_nonnegative = ('or_e', ax('real_total_order', RZERO, x), positive_square, negative_square)
    kernel.theorem('real_square_nonnegative', All(x, Le(RZERO, Mul(x, x))), close(square_nonnegative, (x,)))
    positive_part_x, negative_part_x = A(RMAX, RZERO, x), A(RMAX, RZERO, negx)
    branch_data = {}
    for nonnegative_case in (True, False):
        if nonnegative_case:
            p_identity = apply(ax('real_max_right_definition', RZERO, x), hyp(nonnegative))
            n_identity = apply(ax('real_max_left_definition', RZERO, negx), neg_nonpositive)
            p_nonnegative, n_nonnegative = hyp(nonnegative), ax('real_order_reflexive', RZERO)
            p_bound = ax('real_order_reflexive', Mul(x, x))
            n_bound = ref('real_square_nonnegative', x)
            p_value, n_value = x, RZERO
        else:
            p_identity = apply(ax('real_max_left_definition', RZERO, x), hyp(nonpositive))
            n_identity = apply(ax('real_max_right_definition', RZERO, negx), neg_nonnegative)
            p_nonnegative, n_nonnegative = ax('real_order_reflexive', RZERO), neg_nonnegative
            p_bound = ref('real_square_nonnegative', x)
            n_bound = ax('real_order_reflexive', Mul(x, x))
            p_value, n_value = RZERO, negx
        placeholder = V('jordan_placeholder', 'R')
        p_nonnegative = ('eq_e', symmetric(positive_part_x, p_value, p_identity), placeholder, Le(RZERO, placeholder), p_nonnegative)
        n_nonnegative = ('eq_e', symmetric(negative_part_x, n_value, n_identity), placeholder, Le(RZERO, placeholder), n_nonnegative)
        decomposition = ring(x, Sub(p_value, n_value))
        decomposition = ('eq_e', symmetric(positive_part_x, p_value, p_identity), placeholder, Eq(x, Sub(placeholder, n_value)), decomposition)
        decomposition = ('eq_e', symmetric(negative_part_x, n_value, n_identity), placeholder, Eq(x, Sub(positive_part_x, placeholder)), decomposition)
        square_identity = ring(Mul(x, x), Add(Mul(p_value, p_value), Mul(n_value, n_value)))
        square_identity = ('eq_e', symmetric(positive_part_x, p_value, p_identity), placeholder, Eq(Mul(x, x), Add(Mul(placeholder, placeholder), Mul(n_value, n_value))), square_identity)
        square_identity = ('eq_e', symmetric(negative_part_x, n_value, n_identity), placeholder, Eq(Mul(x, x), Add(Mul(positive_part_x, positive_part_x), Mul(placeholder, placeholder))), square_identity)
        p_bound = ('eq_e', symmetric(Mul(p_value, p_value), RZERO if p_value == RZERO else Mul(x, x), ring(Mul(p_value, p_value), RZERO if p_value == RZERO else Mul(x, x))), placeholder, Le(placeholder, Mul(x, x)), p_bound)
        n_bound = ('eq_e', symmetric(Mul(n_value, n_value), RZERO if n_value == RZERO else Mul(x, x), ring(Mul(n_value, n_value), RZERO if n_value == RZERO else Mul(x, x))), placeholder, Le(placeholder, Mul(x, x)), n_bound)
        p_bound = ('eq_e', symmetric(positive_part_x, p_value, p_identity), placeholder, Le(Mul(placeholder, placeholder), Mul(x, x)), p_bound)
        n_bound = ('eq_e', symmetric(negative_part_x, n_value, n_identity), placeholder, Le(Mul(placeholder, placeholder), Mul(x, x)), n_bound)
        branch_data[nonnegative_case] = ('and_i', ('and_i', p_nonnegative, n_nonnegative), ('and_i', decomposition, ('and_i', square_identity, ('and_i', p_bound, n_bound))))
    conclusion = And(And(Le(RZERO, positive_part_x), Le(RZERO, negative_part_x)), And(Eq(x, Sub(positive_part_x, negative_part_x)), And(Eq(Mul(x, x), Add(Mul(positive_part_x, positive_part_x), Mul(negative_part_x, negative_part_x))), And(Le(Mul(positive_part_x, positive_part_x), Mul(x, x)), Le(Mul(negative_part_x, negative_part_x), Mul(x, x))))))
    result = ('or_e', ax('real_total_order', RZERO, x), branch_data[True], branch_data[False])
    kernel.theorem('jordan_parts_pointwise', All(x, conclusion), close(result, (x,)))
    one_nonnegative = apply(ax('positive_implies_nonnegative', RONE), ('axiom', 'real_one_positive'))
    square_positive = ref('real_square_nonnegative', x)
    one_below = apply(ax('addition_monotone', RONE, RONE, RZERO, Mul(x, x)), ax('real_order_reflexive', RONE), square_positive)
    one_below = rewrite(kernel, one_below, ring(Add(RONE, RZERO), RONE))
    small_case = apply(ax('real_order_transitive', x, RONE, Add(RONE, Mul(x, x))), hyp(Le(x, RONE)), one_below)
    x_nonnegative = apply(ax('real_order_transitive', RZERO, RONE, x), one_nonnegative, hyp(Le(RONE, x)))
    large_case = apply(ax('nonnegative_multiplication_monotone', x, RONE, x), x_nonnegative, hyp(Le(RONE, x)))
    large_case = rewrite(kernel, large_case, ring(Mul(x, RONE), x))
    square_below = apply(ax('addition_monotone', RZERO, RONE, Mul(x, x), Mul(x, x)), one_nonnegative, ax('real_order_reflexive', Mul(x, x)))
    square_below = rewrite(kernel, square_below, ring(Add(RZERO, Mul(x, x)), Mul(x, x)))
    large_case = apply(ax('real_order_transitive', x, Mul(x, x), Add(RONE, Mul(x, x))), large_case, square_below)
    result = ('or_e', ax('real_total_order', x, RONE), small_case, large_case)
    kernel.theorem('real_value_below_one_plus_square', All(x, Le(x, Add(RONE, Mul(x, x)))), close(result, (x,)))
    s = V('nonnegative_test_value', 'R')
    for kind in ('positive', 'negative'):
        parts = ref('jordan_parts_pointwise', x)
        selected = positive_part_x if kind == 'positive' else negative_part_x
        selected_nonnegative = ('and_l' if kind == 'positive' else 'and_r', ('and_l', parts))
        selected_square_bound = ('and_l' if kind == 'positive' else 'and_r', ('and_r', ('and_r', ('and_r', parts))))
        conditions = (Le(RZERO, s), Le(s, selected))
        bound = apply(ref('nonnegative_product_monotone', s, s, selected, selected), hyp(conditions[0]), selected_nonnegative, hyp(conditions[1]), hyp(conditions[1]))
        bound = apply(ax('real_order_transitive', Mul(s, s), Mul(selected, selected), Mul(x, x)), bound, selected_square_bound)
        statement = alls((x, s), imps(conditions, Le(Mul(s, s), Mul(x, x))))
        kernel.theorem('square_below_' + kind + '_part_square', statement, close(bound, (x, s), conditions))
    return kernel


def negate_function(function):
    point = V('negated_function_point', OMEGA)
    return Lam(point, Sub(RZERO, A(function, point)))


def upper_levels_in(function, family):
    level = V('upper_family_level', 'R')
    return All(level, A(family, upper_level(function, level)))


def derive_jordan_measurability(kernel):
    x, r = V('real_value', 'R'), V('level', 'R')
    positive, negative = Le(RZERO, x), Le(x, RZERO)
    maximum = A(RMAX, RZERO, x)
    identities = {
        True: apply(ax('real_max_right_definition', RZERO, x), hyp(positive)),
        False: apply(ax('real_max_left_definition', RZERO, x), hyp(negative))
    }
    upper_branches, lower_branches = {}, {}
    placeholder = V('maximum_placeholder', 'R')
    for nonnegative_case in (True, False):
        if nonnegative_case:
            upper_implication = apply(ax('real_order_transitive', r, RZERO, x), hyp(Le(r, RZERO)), hyp(positive))
            upper_implication = close(upper_implication, assumptions=(Le(r, RZERO),))
            lower_implication = apply(ax('real_order_transitive', RZERO, x, r), hyp(positive), hyp(Le(x, r)))
            lower_implication = close(lower_implication, assumptions=(Le(x, r),))
            value = x
        else:
            upper_implication = apply(ax('real_order_transitive', r, x, RZERO), hyp(Le(r, x)), hyp(negative))
            upper_implication = close(upper_implication, assumptions=(Le(r, x),))
            lower_implication = apply(ax('real_order_transitive', x, RZERO, r), hyp(negative), hyp(Le(RZERO, r)))
            lower_implication = close(lower_implication, assumptions=(Le(RZERO, r),))
            value = RZERO
        upper = apply(logical(Imp(kernel.infer(upper_implication).conclusion, Iff(Le(r, value), Or(Le(r, RZERO), Le(r, x))))), upper_implication)
        lower = apply(logical(Imp(kernel.infer(lower_implication).conclusion, Iff(Le(value, r), And(Le(RZERO, r), Le(x, r))))), lower_implication)
        upper_branches[nonnegative_case] = ('eq_e', symmetric(maximum, value, identities[nonnegative_case]), placeholder, Iff(Le(r, placeholder), Or(Le(r, RZERO), Le(r, x))), upper)
        lower_branches[nonnegative_case] = ('eq_e', symmetric(maximum, value, identities[nonnegative_case]), placeholder, Iff(Le(placeholder, r), And(Le(RZERO, r), Le(x, r))), lower)
    upper = ('or_e', ax('real_total_order', RZERO, x), upper_branches[True], upper_branches[False])
    lower = ('or_e', ax('real_total_order', RZERO, x), lower_branches[True], lower_branches[False])
    kernel.theorem('positive_part_upper_level_scalar', alls((x, r), Iff(Le(r, maximum), Or(Le(r, RZERO), Le(r, x)))), close(upper, (x, r)))
    kernel.theorem('positive_part_lower_level_scalar', alls((x, r), Iff(Le(maximum, r), And(Le(RZERO, r), Le(x, r)))), close(lower, (x, r)))
    f, family = V('function', FUNCTION), V('event_family', EVENT_FAMILY)
    point, level = V('omega', OMEGA), V('level', 'R')
    negf = negate_function(f)
    conditions = (measurable_in(f, family),)
    upper_left, upper_right = upper_level(negf, level), lower_level(f, Sub(RZERO, level))
    lower_left, lower_right = lower_level(negf, level), upper_level(f, Sub(RZERO, level))
    upper_forward = apply(ref('negation_reverses_order', level, Sub(RZERO, A(f, point))), hyp(A(upper_left, point)))
    upper_forward = rewrite(kernel, upper_forward, ring(Sub(RZERO, Sub(RZERO, A(f, point))), A(f, point)))
    upper_backward = apply(ref('negation_reverses_order', A(f, point), Sub(RZERO, level)), hyp(A(upper_right, point)))
    upper_backward = rewrite(kernel, upper_backward, ring(Sub(RZERO, Sub(RZERO, level)), level))
    upper_identity = extensional_event(upper_left, upper_right, close(('and_i', close(upper_forward, assumptions=(A(upper_left, point),)), close(upper_backward, assumptions=(A(upper_right, point),))), (point,)))
    lower_forward = apply(ref('negation_reverses_order', Sub(RZERO, A(f, point)), level), hyp(A(lower_left, point)))
    lower_forward = rewrite(kernel, lower_forward, ring(Sub(RZERO, Sub(RZERO, A(f, point))), A(f, point)))
    lower_backward = apply(ref('negation_reverses_order', Sub(RZERO, level), A(f, point)), hyp(A(lower_right, point)))
    lower_backward = rewrite(kernel, lower_backward, ring(Sub(RZERO, Sub(RZERO, level)), level))
    lower_identity = extensional_event(lower_left, lower_right, close(('and_i', close(lower_forward, assumptions=(A(lower_left, point),)), close(lower_backward, assumptions=(A(lower_right, point),))), (point,)))
    original_levels = instantiate(hyp(conditions[0]), Sub(RZERO, level))
    upper_measurable = rewrite(kernel, ('and_r', original_levels), upper_identity, True)
    lower_measurable = rewrite(kernel, ('and_l', original_levels), lower_identity, True)
    result = close(('and_i', upper_measurable, lower_measurable), (level,))
    kernel.theorem('measurable_in_negation', alls((f, family), Imp(conditions[0], measurable_in(negf, family))), close(result, (f, family), conditions))
    part = positive_part(f)
    universe_member = A(family, universe_event())
    upper_assumption = upper_levels_in(f, family)
    scalar_upper = ref('positive_part_upper_level_scalar', A(f, point), level)
    upper = upper_level(part, level)
    level_nonpositive = Le(level, RZERO)
    upper_universe = apply(logical(imps((Iff(A(upper, point), Or(level_nonpositive, Le(level, A(f, point)))), level_nonpositive), Iff(A(upper, point), A(universe_event(), point)))), scalar_upper, hyp(level_nonpositive))
    upper_original = apply(logical(imps((Iff(A(upper, point), Or(level_nonpositive, Le(level, A(f, point)))), Imp(level_nonpositive, BOTTOM)), Iff(A(upper, point), A(upper_level(f, level), point)))), scalar_upper, hyp(Imp(level_nonpositive, BOTTOM)))
    universe_identity = extensional_event(upper, universe_event(), close(upper_universe, (point,)))
    original_identity = extensional_event(upper, upper_level(f, level), close(upper_original, (point,)))
    first_case = rewrite(kernel, hyp(universe_member), universe_identity, True)
    second_case = rewrite(kernel, instantiate(hyp(upper_assumption), level), original_identity, True)
    upper_membership = by_cases(level_nonpositive, first_case, second_case)
    result = close(upper_membership, (level,))
    statement = alls((f, family), imps((universe_member, upper_assumption), upper_levels_in(part, family)))
    kernel.theorem('positive_part_upper_levels_in_family', statement, close(result, (f, family), (universe_member, upper_assumption)))
    lower = lower_level(part, level)
    level_nonnegative = Le(RZERO, level)
    scalar_lower = ref('positive_part_lower_level_scalar', A(f, point), level)
    lower_original = apply(logical(imps((Iff(A(lower, point), And(level_nonnegative, Le(A(f, point), level))), level_nonnegative), Iff(A(lower, point), A(lower_level(f, level), point)))), scalar_lower, hyp(level_nonnegative))
    lower_empty = apply(logical(imps((Iff(A(lower, point), And(level_nonnegative, Le(A(f, point), level))), Imp(level_nonnegative, BOTTOM)), Iff(A(lower, point), A(empty_event(), point)))), scalar_lower, hyp(Imp(level_nonnegative, BOTTOM)))
    original_identity = extensional_event(lower, lower_level(f, level), close(lower_original, (point,)))
    empty_identity = extensional_event(lower, empty_event(), close(lower_empty, (point,)))
    measurable = measurable_real(f)
    first_case = rewrite(kernel, ('and_r', instantiate(hyp(measurable), level)), original_identity, True)
    second_case = rewrite(kernel, ('axiom', 'sigma_algebra_empty'), empty_identity, True)
    lower_membership = by_cases(level_nonnegative, first_case, second_case)
    original_uppers = close(('and_l', instantiate(hyp(measurable), level)), (level,))
    upper_memberships = apply(ref('positive_part_upper_levels_in_family', f, MEASURABLE), ('axiom', 'sigma_algebra_universe'), original_uppers)
    result = close(('and_i', instantiate(upper_memberships, level), lower_membership), (level,))
    kernel.theorem('positive_part_measurable', All(f, Imp(measurable, measurable_real(part))), close(result, (f,), (measurable,)))
    neg_measurable = apply(ref('measurable_in_negation', f, MEASURABLE), hyp(measurable))
    negative_measurable = apply(ref('positive_part_measurable', negf), neg_measurable)
    kernel.theorem('negative_part_measurable', All(f, Imp(measurable, measurable_real(negative_part(f)))), close(negative_measurable, (f,), (measurable,)))
    family_measurable = measurable_in(f, family)
    negative_measurable = apply(ref('measurable_in_negation', f, family), hyp(family_measurable))
    negative_uppers = close(('and_l', instantiate(negative_measurable, level)), (level,))
    negative_uppers = apply(ref('positive_part_upper_levels_in_family', negf, family), hyp(universe_member), negative_uppers)
    statement = alls((f, family), imps((universe_member, family_measurable), upper_levels_in(negative_part(f), family)))
    kernel.theorem('negative_part_upper_levels_in_family', statement, close(negative_uppers, (f, family), (universe_member, family_measurable)))
    return kernel


def derive_l2_integrability(kernel):
    f = V('function', FUNCTION)
    point = V('omega', OMEGA)
    plus, minus = positive_part(f), negative_part(f)
    parts = ref('jordan_parts_pointwise', A(f, point))
    plus_nn = close(('and_l', ('and_l', parts)), (point,))
    minus_nn = close(('and_r', ('and_l', parts)), (point,))
    measurable = measurable_real(f)
    plus_measurable = apply(ref('positive_part_measurable', f), hyp(measurable))
    minus_measurable = apply(ref('negative_part_measurable', f), hyp(measurable))
    plus_approx = apply(ref('nonnegative_measurable_approximable', plus), plus_nn, plus_measurable)
    minus_approx = apply(ref('nonnegative_measurable_approximable', minus), minus_nn, minus_measurable)
    result = ('and_i', plus_approx, minus_approx)
    statement = All(f, Imp(measurable, And(positive_approximable(plus), positive_approximable(minus))))
    kernel.theorem('jordan_parts_approximable', statement, close(result, (f,), (measurable,)))
    square_value = V('square_integral_value', 'R')
    square_integral = has_positive_integral(square_function(f), square_value)
    simple = V('test_simple', SIMPLE)
    one_info = apply(ref('constant_simple_value_and_integral', RONE), apply(ax('positive_implies_nonnegative', RONE), ('axiom', 'real_one_positive')))
    one_simple = simple_constant(RONE)
    for kind, part, part_nn in (('positive', plus, plus_nn), ('negative', minus, minus_nn)):
        test_hypothesis = And(A(SIMPLE_VALID_NONNEGATIVE, simple), simple_below(simple, part))
        simple_positive = ('and_l', hyp(test_hypothesis))
        simple_information = apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', simple), simple_positive)
        squared_simple = A(SIMPLE_PRODUCT, simple, simple)
        squared_positive = apply(instantiate(apply(ref('nonnegative_simple_product', simple), simple_positive), simple), simple_positive)
        squared_bound = apply(ref('square_below_' + kind + '_part_square', A(f, point), val(simple, point)), instantiate(('and_r', simple_information), point), instantiate(('and_r', hyp(test_hypothesis)), point))
        squared_bound = rewrite(kernel, squared_bound, ref('simple_product_value', simple, simple, point), True)
        squared_below = close(squared_bound, (point,))
        squared_integral_bound = apply(instantiate(('and_l', hyp(square_integral)), squared_simple), ('and_i', squared_positive, squared_below))
        sum_simple = A(SIMPLE_APPEND, one_simple, squared_simple)
        sum_positive = apply(instantiate(apply(ref('nonnegative_simple_append', squared_simple), squared_positive), one_simple), ('and_l', one_info))
        sum_valid = ('and_l', apply(ref('nonnegative_simple_is_valid_and_pointwise_nonnegative', sum_simple), sum_positive))
        sum_value = ref('simple_append_value', squared_simple, one_simple, point)
        sum_value = rewrite(kernel, sum_value, instantiate(('and_l', ('and_r', one_info)), point))
        sum_value = rewrite(kernel, sum_value, ref('simple_product_value', simple, simple, point))
        point_bound = ref('real_value_below_one_plus_square', val(simple, point))
        point_bound = rewrite(kernel, point_bound, sum_value, True)
        integral_bound = apply(ref('simple_integral_monotone_from_measure', simple, sum_simple), ('and_l', simple_information), sum_valid, close(point_bound, (point,)))
        sum_integral = ref('simple_append_integral', squared_simple, one_simple)
        sum_integral = rewrite(kernel, sum_integral, ('and_r', ('and_r', one_info)))
        integral_bound = rewrite(kernel, integral_bound, sum_integral)
        final_bound = apply(ax('addition_monotone', RONE, RONE, si(squared_simple), square_value), ax('real_order_reflexive', RONE), squared_integral_bound)
        integral_bound = apply(ax('real_order_transitive', si(simple), Add(RONE, si(squared_simple)), Add(RONE, square_value)), integral_bound, final_bound)
        integral_bound = close(integral_bound, (simple,), (test_hypothesis,))
        exists = apply(ref('bounded_nonnegative_integral_exists', part, Add(RONE, square_value)), part_nn, integral_bound)
        value = V('part_integral', 'R')
        statement = alls((f, square_value), Imp(square_integral, Ex(value, has_positive_integral(part, value))))
        kernel.theorem('l2_' + kind + '_part_has_finite_integral', statement, close(exists, (f, square_value), (square_integral,)))
    l2 = square_integrable(f)
    l2_value, frames_l2 = open_existentials(kernel, ('and_r', hyp(l2)), (square_value,))
    approximations = apply(ref('jordan_parts_approximable', f), ('and_l', hyp(l2)))
    plus_value, minus_value = V('positive_integral_value', 'R'), V('negative_integral_value', 'R')
    plus_exists = apply(ref('l2_positive_part_has_finite_integral', f, square_value), l2_value)
    minus_exists = apply(ref('l2_negative_part_has_finite_integral', f, square_value), l2_value)
    plus_integral, frames_plus = open_existentials(kernel, plus_exists, (plus_value,))
    minus_integral, frames_minus = open_existentials(kernel, minus_exists, (minus_value,))
    plus_positive_integral = ('and_i', ('and_l', approximations), plus_integral)
    minus_positive_integral = ('and_i', ('and_r', approximations), minus_integral)
    exists = Ex(plus_value, Ex(minus_value, And(positive_integrable(plus, plus_value), positive_integrable(minus, minus_value))))
    result = introduce_existentials(exists, (plus_value, minus_value), ('and_i', plus_positive_integral, minus_positive_integral))
    result = discharge_existentials(discharge_existentials(discharge_existentials(result, frames_minus), frames_plus), frames_l2)
    statement = All(f, Imp(l2, exists))
    kernel.theorem('l2_jordan_parts_integrable', statement, close(result, (f,), (l2,)))
    parts_integrable = apply(ref('l2_jordan_parts_integrable', f), hyp(l2))
    integrals, frames = open_existentials(kernel, parts_integrable, (plus_value, minus_value))
    decomposition = close(('and_l', ('and_r', parts)), (point,))
    signed = signed_integral_witness(f, Sub(plus_value, minus_value), plus, minus, plus_value, minus_value, ('and_l', integrals), ('and_r', integrals), decomposition, ('eq_i', Sub(plus_value, minus_value)))
    integrable_result = apply(ref('signed_integral_implies_integrable', f, Sub(plus_value, minus_value)), signed)
    integrable_result = discharge_existentials(integrable_result, frames)
    kernel.theorem('l2_implies_integrable', planned_probability_interfaces()['l2_implies_integrable'], close(integrable_result, (f,), (l2,)))
    left, right = V('positive_approximants', SIMPLE_SEQUENCE), V('negative_approximants', SIMPLE_SEQUENCE)
    approximations = apply(ref('jordan_parts_approximable', f), hyp(measurable))
    plus_approximation, plus_frames = open_existentials(kernel, ('and_l', approximations), (left,))
    minus_approximation, minus_frames = open_existentials(kernel, ('and_r', approximations), (right,))
    square_plus = apply(ref('positive_approximations_product', left, left, plus, plus), plus_approximation, plus_approximation)
    square_minus = apply(ref('positive_approximations_product', right, right, minus, minus), minus_approximation, minus_approximation)
    left_square_sequence, right_square_sequence = product_simple_sequence(left, left), product_simple_sequence(right, right)
    sum_square_sequence = sum_simple_sequence(left_square_sequence, right_square_sequence)
    sum_approximation = apply(ref('positive_approximations_sum', left_square_sequence, right_square_sequence, square_function(plus), square_function(minus)), square_plus, square_minus)
    point_identity = ('and_l', ('and_r', ('and_r', parts)))
    function_identity = apply(ax('real_function_extensionality', square_function(f), add_function(square_function(plus), square_function(minus))), close(point_identity, (point,)))
    square_approximation = rewrite(kernel, sum_approximation, function_identity, True)
    result = ('ex_i', positive_approximable(square_function(f)), sum_square_sequence, square_approximation)
    result = discharge_existentials(discharge_existentials(result, minus_frames), plus_frames)
    kernel.theorem('measurable_square_positive_approximable', All(f, Imp(measurable, positive_approximable(square_function(f)))), close(result, (f,), (measurable,)))
    square_approximation = apply(ref('measurable_square_positive_approximable', f), ('and_l', hyp(l2)))
    square_integral_value, frames = open_existentials(kernel, ('and_r', hyp(l2)), (square_value,))
    square_positive_integrable = ('and_i', square_approximation, square_integral_value)
    zero_integrable = apply(ref('nonnegative_constant_positive_integrable', RZERO), ax('real_order_reflexive', RZERO))
    point_decomposition = close(ring(A(square_function(f), point), Sub(A(square_function(f), point), RZERO)), (point,))
    signed_square = signed_integral_witness(square_function(f), square_value, square_function(f), constant_function(RZERO), square_value, RZERO, square_positive_integrable, zero_integrable, point_decomposition, ring(square_value, Sub(square_value, RZERO)))
    square_integrable_result = apply(ref('signed_integral_implies_integrable', square_function(f), square_value), signed_square)
    result = discharge_existentials(square_integrable_result, frames)
    kernel.theorem('l2_square_signed_integral', planned_probability_interfaces()['l2_square_signed_integral'], close(result, (f,), (l2,)))
    return kernel



def bound_variables(term):
    if term[0] in ('v', 'c', 'false'):
        return frozenset()
    if term[0] in ('lam', 'all', 'ex'):
        return frozenset([term[1]]) | bound_variables(term[2])
    return frozenset().union(*(bound_variables(child) for child in term[1:]))


def alpha_avoid(term, occupied):
    used = set(occupied) | set(free_variables(term)) | set(bound_variables(term))
    def visit(current):
        if current[0] in ('v', 'c', 'false'):
            return current
        if current[0] in ('lam', 'all', 'ex'):
            binder, body = current[1:]
            if binder in occupied:
                fresh = V(binder[1] + '_alpha', sort_of(binder))
                while fresh in used:
                    fresh = V(fresh[1] + '_fresh', sort_of(binder))
                used.add(fresh)
                body = substitute(body, binder, fresh)
                binder = fresh
            return (current[0], binder, visit(body))
        return (current[0], *(visit(child) for child in current[1:]))
    return visit(term)


def safe_ref(kernel, name, *terms):
    proof = ('ref', name)
    formula = kernel.infer(proof).conclusion
    occupied = frozenset().union(*(free_variables(term) for term in terms))
    target = alpha_avoid(formula, occupied)
    return instantiate(('conversion', target, proof), *terms)


def derive_independent_signed_factorization(kernel):
    f, g = V('function', FUNCTION), V('other_function', FUNCTION)
    a, b = V('integral_value', 'R'), V('other_integral_value', 'R')
    left_family, right_family = V('left_event_family', EVENT_FAMILY), V('right_event_family', EVENT_FAMILY)
    point = V('omega', OMEGA)
    positive_f = positive_integrable(f, a)
    approximation = V('nonnegative_approximants', SIMPLE_SEQUENCE)
    instance, frames = open_existentials(kernel, ('and_l', hyp(positive_f)), (approximation,))
    result = apply(ref('positive_approximation_limit_nonnegative', approximation, f), instance)
    result = discharge_existentials(result, frames)
    kernel.theorem('positive_integrable_nonnegative', alls((f, a), Imp(positive_f, function_nonnegative(f))), close(result, (f, a), (positive_f,)))
    conditions = (positive_integrable(f, a), positive_integrable(g, b), measurable_real(f), measurable_real(g), upper_levels_in(f, left_family), upper_levels_in(g, right_family), independent_event_families(left_family, right_family))
    f_nonnegative = apply(ref('positive_integrable_nonnegative', f, a), hyp(conditions[0]))
    g_nonnegative = apply(ref('positive_integrable_nonnegative', g, b), hyp(conditions[1]))
    f_exists = apply(ref('nonnegative_measurable_adapted_approximable', f, left_family), f_nonnegative, hyp(conditions[2]), hyp(conditions[4]))
    g_exists = apply(ref('nonnegative_measurable_adapted_approximable', g, right_family), g_nonnegative, hyp(conditions[3]), hyp(conditions[5]))
    left, right = V('left_adapted_approximants', SIMPLE_SEQUENCE), V('right_adapted_approximants', SIMPLE_SEQUENCE)
    f_approximation, f_frames = open_existentials(kernel, f_exists, (left,))
    g_approximation, g_frames = open_existentials(kernel, g_exists, (right,))
    left_info, right_info = ('and_l', f_approximation), ('and_l', g_approximation)
    left_positive, left_increasing, left_lub = approximation_parts(left_info)
    right_positive, right_increasing, right_lub = approximation_parts(right_info)
    product_integral = apply(ref('independent_nonnegative_limits_factor', left, right, f, g, a, b, left_family, right_family), left_positive, left_increasing, left_lub, ('and_r', hyp(conditions[0])), ('and_r', f_approximation), right_positive, right_increasing, right_lub, ('and_r', hyp(conditions[1])), ('and_r', g_approximation), hyp(conditions[6]))
    product_approximation = apply(ref('positive_approximations_product', left, right, f, g), left_info, right_info)
    product_exists = ('ex_i', positive_approximable(product_function(f, g)), product_simple_sequence(left, right), product_approximation)
    result = ('and_i', product_exists, product_integral)
    result = discharge_existentials(discharge_existentials(result, g_frames), f_frames)
    statement = alls((f, g, a, b, left_family, right_family), imps(conditions, positive_integrable(product_function(f, g), Mul(a, b))))
    kernel.theorem('independent_nonnegative_integrable_factor', statement, close(result, (f, g, a, b, left_family, right_family), conditions))
    l2f, l2g, independence = square_integrable(f), square_integrable(g), independent_functions(f, g)
    independent_families, family_frames = open_existentials(kernel, hyp(independence), (left_family, right_family))
    universe_families = ('and_l', ('and_r', independent_families))
    variable_measurabilities = ('and_l', ('and_r', ('and_r', independent_families)))
    family_independence = ('and_r', ('and_r', ('and_r', independent_families)))
    f_family, g_family = ('and_l', variable_measurabilities), ('and_r', variable_measurabilities)
    fp, fn, gp, gn = positive_part(f), negative_part(f), positive_part(g), negative_part(g)
    f_measurable, g_measurable = ('and_l', hyp(l2f)), ('and_l', hyp(l2g))
    fp_measurable = apply(ref('positive_part_measurable', f), f_measurable)
    fn_measurable = apply(ref('negative_part_measurable', f), f_measurable)
    gp_measurable = apply(ref('positive_part_measurable', g), g_measurable)
    gn_measurable = apply(ref('negative_part_measurable', g), g_measurable)
    level = V('family_upper_level', 'R')
    f_uppers = close(('and_l', instantiate(f_family, level)), (level,))
    g_uppers = close(('and_l', instantiate(g_family, level)), (level,))
    fp_adapted = apply(ref('positive_part_upper_levels_in_family', f, left_family), ('and_l', universe_families), f_uppers)
    fn_adapted = apply(ref('negative_part_upper_levels_in_family', f, left_family), ('and_l', universe_families), f_family)
    gp_adapted = apply(ref('positive_part_upper_levels_in_family', g, right_family), ('and_r', universe_families), g_uppers)
    gn_adapted = apply(ref('negative_part_upper_levels_in_family', g, right_family), ('and_r', universe_families), g_family)
    ap, an, bp, bn = (V(name, 'R') for name in ('left_positive_integral', 'left_negative_integral', 'right_positive_integral', 'right_negative_integral'))
    f_parts, f_frames = open_existentials(kernel, apply(ref('l2_jordan_parts_integrable', f), hyp(l2f)), (ap, an))
    g_parts, g_frames = open_existentials(kernel, apply(ref('l2_jordan_parts_integrable', g), hyp(l2g)), (bp, bn))
    f_decomposition = close(('and_l', ('and_r', ref('jordan_parts_pointwise', A(f, point)))), (point,))
    g_decomposition = close(('and_l', ('and_r', ref('jordan_parts_pointwise', A(g, point)))), (point,))
    f_signed = signed_integral_witness(f, Sub(ap, an), fp, fn, ap, an, ('and_l', f_parts), ('and_r', f_parts), f_decomposition, ('eq_i', Sub(ap, an)))
    g_signed = signed_integral_witness(g, Sub(bp, bn), gp, gn, bp, bn, ('and_l', g_parts), ('and_r', g_parts), g_decomposition, ('eq_i', Sub(bp, bn)))
    f_expectation = apply(ref('expectation_of_signed_integral', f, Sub(ap, an)), f_signed)
    g_expectation = apply(ref('expectation_of_signed_integral', g, Sub(bp, bn)), g_signed)
    products = {}
    for fsign, ff, af, fi, fm, fa in (('p', fp, ap, ('and_l', f_parts), fp_measurable, fp_adapted), ('n', fn, an, ('and_r', f_parts), fn_measurable, fn_adapted)):
        for gsign, gg, ag, gi, gm, ga in (('p', gp, bp, ('and_l', g_parts), gp_measurable, gp_adapted), ('n', gn, bn, ('and_r', g_parts), gn_measurable, gn_adapted)):
            products[fsign + gsign] = apply(ref('independent_nonnegative_integrable_factor', ff, gg, af, ag, left_family, right_family), fi, gi, fm, gm, fa, ga, family_independence)
    positive = add_function(product_function(fp, gp), product_function(fn, gn))
    negative = add_function(product_function(fp, gn), product_function(fn, gp))
    positive_value = Add(Mul(ap, bp), Mul(an, bn))
    negative_value = Add(Mul(ap, bn), Mul(an, bp))
    positive_integral = apply(safe_ref(kernel, 'positive_integrable_add', product_function(fp, gp), product_function(fn, gn), Mul(ap, bp), Mul(an, bn)), products['pp'], products['nn'])
    negative_integral = apply(safe_ref(kernel, 'positive_integrable_add', product_function(fp, gn), product_function(fn, gp), Mul(ap, bn), Mul(an, bp)), products['pn'], products['np'])
    point_identity = equality_congruence(kernel, instantiate(f_decomposition, point), lambda x: Mul(x, A(g, point)))
    point_identity = rewrite_right(kernel, point_identity, instantiate(g_decomposition, point))
    original, current = kernel.infer(point_identity).conclusion[1:]
    target = Sub(A(positive, point), A(negative, point))
    point_identity = eq_trans(original, current, target, point_identity, ring(current, target))
    value_identity = equality_congruence(kernel, f_expectation, lambda x: Mul(x, expectation(g)))
    value_identity = rewrite_right(kernel, value_identity, g_expectation)
    original, current = kernel.infer(value_identity).conclusion[1:]
    target = Sub(positive_value, negative_value)
    value_identity = eq_trans(original, current, target, value_identity, ring(current, target))
    result = signed_integral_witness(product_function(f, g), Mul(expectation(f), expectation(g)), positive, negative, positive_value, negative_value, positive_integral, negative_integral, close(point_identity, (point,)), value_identity)
    result = discharge_existentials(discharge_existentials(discharge_existentials(result, g_frames), f_frames), family_frames)
    kernel.theorem('independent_l2_product_integral', planned_probability_interfaces()['independent_l2_product_integral'], close(result, (f, g), (l2f, l2g, independence)))
    return kernel


def kernel_self_test():
    x, y = V('x', 'R'), V('y', 'R')
    p = C('P', FT('R', 'Prop'))
    px, py = A(p, x), A(p, y)
    kernel = Kernel({})
    identity = close(('assume', px), (x,), (px,))
    kernel.theorem('identity', All(x, Imp(px, px)), identity)
    checks = {
        'identity_closed': not kernel.infer(('ref', 'identity')).assumptions,
        'open_hypothesis_rejected': rejects(lambda: kernel.theorem('open', All(x, px), ('all_i', x, ('assume', px)))),
        'wrong_conclusion_rejected': rejects(lambda: kernel.theorem('wrong', All(x, Imp(px, py)), identity)),
        'capturing_substitution_rejected': rejects(lambda: substitute(All(y, px), x, y)),
        'application_type_mismatch_rejected': rejects(lambda: sort_of(A(p, C('zero_nat', 'N')))),
        'unknown_theorem_rejected': rejects(lambda: kernel.infer(('ref', 'factorization'))),
        'existential_escape_rejected': rejects(lambda: kernel.infer(('ex_e', ('assume', Ex(x, px)), y, ('assume', py)))),
        'wrong_modus_ponens_rejected': rejects(lambda: kernel.infer(('mp', ('assume', Imp(px, px)), ('assume', py)))),
        'non_tautology_rejected': rejects(lambda: kernel.infer(('tautology', Imp(px, py)))),
        'alpha_conversion': same(All(x, px), All(y, py)),
        'beta_conversion': same(A(Lam(x, px), y), py)
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    return checks


def base_probability_certificates():
    kernel = derived_order_certificates()
    for builder in (derive_simple_limit_bound, derive_measure_continuity, derive_intersection_continuity, derive_finite_simple_continuity, derive_simple_finite_algebra, derive_simple_positivity, derive_simple_operations, derive_simple_restriction, derive_simple_threshold_measurable, derive_nonnegative_simple, derive_monotone_convergence, derive_simple_product_factorization, derive_nonnegative_operations, derive_nonnegative_factorization_limit, derive_positive_integral_basics, derive_positive_linear, derive_signed_linear, derive_jordan_scalar, derive_jordan_measurability):
        kernel = builder(kernel)
    return kernel


def probability_certificates():
    scripts_path = str(Path(__file__).resolve().parents[1])
    if scripts_path not in sys.path:
        sys.path.insert(0, scripts_path)
    from capitulo_07.aproximacoes import derive_canonical_approximations
    kernel = base_probability_certificates()
    kernel = derive_canonical_approximations(kernel)
    kernel = derive_l2_integrability(kernel)
    return derive_independent_signed_factorization(kernel)


def certificate_record(kernel, name):
    matches = [record for record in kernel.records if record[0] == name]
    if len(matches) != 1:
        raise ValueError(('certificate record must be unique', name))
    return matches[0]


def proves(kernel, formula, proof):
    result = kernel.infer(proof)
    if sort_of(formula) != 'Prop' or free_variables(formula) or result.assumptions or not same(result.conclusion, formula):
        raise ValueError('certificate does not prove the closed expected formula')
    return True


def certified(kernel, name, expected):
    record = certificate_record(kernel, name)
    if not same(record[1], expected):
        raise ValueError(('record differs from independently specified interface', name))
    return proves(kernel, expected, record[2])


def remove_discharge(proof, assumption):
    if not isinstance(proof, tuple):
        return proof, 0
    if proof and proof[0] == 'imp_i' and same(proof[1], assumption):
        return proof[2], 1
    result, count = [], 0
    for component in proof:
        changed, changed_count = remove_discharge(component, assumption)
        result.append(changed)
        count += changed_count
    return tuple(result), count


def first_replay_failure(kernel, axiom_name, replacement):
    axioms = dict(kernel.axioms)
    axioms[axiom_name] = replacement
    replay = Kernel(axioms)
    for name, formula, proof in kernel.records:
        try:
            replay.theorem(name, formula, proof)
        except (ValueError, KeyError, TypeError, IndexError):
            return name
    return None


def probability_self_test(kernel):
    checks = {}
    f, g = V('function', FUNCTION), V('other_function', FUNCTION)
    record = certificate_record(kernel, 'independent_l2_product_integral')
    independence = independent_functions(f, g)
    mutated, changed = remove_discharge(record[2], independence)
    checks['independence_hypothesis_removal_rejected'] = changed == 1 and rejects(lambda: proves(kernel, record[1], mutated))
    mutated, changed = remove_discharge(record[2], square_integrable(f))
    checks['l2_hypothesis_removal_rejected'] = changed == 1 and rejects(lambda: proves(kernel, record[1], mutated))
    wrong_product = replace_subterm(record[1], Mul(expectation(f), expectation(g)), Add(expectation(f), expectation(g)))
    checks['expectation_product_changed_to_sum_rejected'] = not same(record[1], wrong_product) and rejects(lambda: proves(kernel, wrong_product, record[2]))
    mct = certificate_record(kernel, 'monotone_simple_approximation_integral_bound')
    sequence, function, bound = mct[1][1], mct[1][2][1], mct[1][2][2][1]
    original_bound = positive_integral_bound(function, bound)
    wrong_bound = replace_subterm(mct[1], original_bound, positive_integral_bound(function, Sub(bound, RONE)))
    checks['mct_bound_decreased_by_one_rejected'] = not same(mct[1], wrong_bound) and rejects(lambda: proves(kernel, wrong_bound, mct[2]))
    checks['countable_additivity_cannot_be_accepted_by_name'] = first_replay_failure(kernel, 'measure_countable_additivity_partial_unions', Eq(RZERO, RZERO)) == 'measure_union_lub_of_finite_unions'
    original = kernel.axioms['simple_integral_cons']
    head, tail = original[1], original[2][1]
    changed_integral = alls((head, tail), Eq(si(A(SIMPLE_CONS, head, tail)), Add(Add(A(SIMPLE_COEFFICIENT, head), A(MEASURE, A(SIMPLE_EVENT, head))), si(tail))))
    checks['simple_integral_coefficient_mutation_rejected'] = first_replay_failure(kernel, 'simple_integral_cons', changed_integral) == 'simple_integral_is_unrestricted_weighted_sum'
    xs, h, t = V('induction_list', ('List', 'R')), V('induction_head', 'R'), V('induction_tail', ('List', 'R'))
    nil = C('list_nil', ('List', 'R'))
    cons = A(C('list_cons', FT('R', FT(('List', 'R'), ('List', 'R')))), h, t)
    body = Eq(xs, xs)
    base = ('eq_i', nil)
    step = close(('eq_i', cons), (h, t), (Eq(t, t),))
    induction = ('list_induction', xs, h, t, body, base, step)
    checks['list_induction_actual_recurrence_accepted'] = proves(Kernel({}), All(xs, body), induction)
    checks['list_induction_wrong_base_rejected'] = rejects(lambda: Kernel({}).infer(('list_induction', xs, h, t, body, ('eq_i', RZERO), step)))
    wrong_step = close(('eq_i', t), (h, t), (Eq(t, t),))
    checks['list_induction_wrong_step_rejected'] = rejects(lambda: Kernel({}).infer(('list_induction', xs, h, t, body, base, wrong_step)))
    checks['list_induction_nonfresh_head_rejected'] = rejects(lambda: Kernel({}).infer(('list_induction', xs, h, t, And(body, Eq(h, h)), base, step)))
    x, y = V('polynomial_x', 'R'), V('polynomial_y', 'R')
    checks['ring_identity_accepted'] = proves(Kernel({}), alls((x, y), Eq(Mul(Add(x, y), Sub(x, y)), Sub(Mul(x, x), Mul(y, y)))), close(ring(Mul(Add(x, y), Sub(x, y)), Sub(Mul(x, x), Mul(y, y))), (x, y)))
    checks['ring_wrong_sign_rejected'] = rejects(lambda: Kernel({}).infer(ring(Add(x, y), Sub(x, y))))
    checks['division_cancellation_without_nonzero_rejected'] = rejects(lambda: Kernel({}).infer(ring(Div(x, x), RONE)))
    if not all(checks.values()):
        raise AssertionError(checks)
    return checks


CHECKS = {}


def check(name, condition):
    if name in CHECKS or not condition:
        raise AssertionError(name)
    CHECKS[name] = True


def probability_verification():
    certificates = probability_certificates()
    interfaces = planned_probability_interfaces()
    check('signed_integral_add', certified(certificates, 'signed_integral_add', interfaces['signed_integral_add']))
    check('signed_integral_scale', certified(certificates, 'signed_integral_scale', interfaces['signed_integral_scale']))
    check('signed_integral_unique', certified(certificates, 'signed_integral_unique', interfaces['signed_integral_unique']))
    check('expectation_of_signed_integral', certified(certificates, 'expectation_of_signed_integral', interfaces['expectation_of_signed_integral']))
    check('l2_implies_integrable', certified(certificates, 'l2_implies_integrable', interfaces['l2_implies_integrable']))
    check('l2_square_signed_integral', certified(certificates, 'l2_square_signed_integral', interfaces['l2_square_signed_integral']))
    check('independent_l2_product_integral', certified(certificates, 'independent_l2_product_integral', interfaces['independent_l2_product_integral']))
    check('constant_signed_integral', certified(certificates, 'constant_signed_integral', interfaces['constant_signed_integral']))
    return {'backend': 'Python 3', 'checks': CHECKS, 'kernel_checks': kernel_self_test(), 'adversarial_checks': probability_self_test(certificates), 'derived_certificates': list(certificates.verified), 'axioms': list(certificates.axioms), 'scope': 'Arbitrary measurable real functions on a probability space, with finite second moments and independent event families; simple integration, monotone convergence, canonical approximations, signed linearity and expectation factorization are derived by checked proof terms.', 'general_probability_complete': True}


if __name__ == '__main__':
    print(json.dumps(probability_verification(), ensure_ascii=False))
