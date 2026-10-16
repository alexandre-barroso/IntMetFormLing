from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
from pathlib import Path
import json
import sys
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from capitulo_06 import fundamentos_area, fundamentos_log, fundamentos_pi, fundamentos_informacao, integracao_polinomial, substituicao_geral


EXPECTED_ANALYTICAL_INTERFACES = {'exponential_series_decomposition': {'formula': '|- ( exp ` A ) = ( sum_ k e. ( 0 ... ( M - 1 ) ) ( ( n e. '
                                                 'NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) ) ` k ) + sum_ k e. ( '
                                                 'ZZ>= ` M ) ( ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) ) ` '
                                                 'k ) )',
                                      'hypotheses': ['|- A e. CC', '|- M e. NN']},
 'exponential_series_tail_bound': {'formula': '|- ( abs ` sum_ k e. ( ZZ>= ` M ) ( ( n e. NN0 |-> ( ( A ^ n '
                                              ') / ( ! ` n ) ) ) ` k ) ) <_ ( ( ( abs ` A ) ^ M ) x. ( ( M + '
                                              '1 ) / ( ( ! ` M ) x. M ) ) )',
                                   'hypotheses': ['|- ( abs ` A ) <_ 1', '|- A e. CC', '|- M e. NN']},
 'logarithm_series_decomposition': {'formula': '|- -u ( log ` ( 1 - A ) ) = ( sum_ k e. ( 1 ... ( M - 1 ) ) '
                                               '( ( A ^ k ) / k ) + sum_ k e. ( ZZ>= ` M ) ( ( A ^ k ) / k ) '
                                               ')',
                                    'hypotheses': ['|- 0 <_ A', '|- A < 1', '|- A e. RR', '|- M e. NN']},
 'logarithm_series_tail_nonnegative': {'formula': '|- 0 <_ sum_ k e. ( ZZ>= ` M ) ( ( A ^ k ) / k )',
                                       'hypotheses': ['|- 0 <_ A', '|- A < 1', '|- A e. RR', '|- M e. NN']},
 'logarithm_series_tail_bound': {'formula': '|- sum_ k e. ( ZZ>= ` M ) ( ( A ^ k ) / k ) <_ ( ( A ^ M ) / ( '
                                            '1 - A ) )',
                                 'hypotheses': ['|- 0 <_ A', '|- A < 1', '|- A e. RR', '|- M e. NN']},
 'arctangent_addition_one': {'formula': '|- ( ( arctan ` A ) + ( arctan ` B ) ) = ( _pi / 4 )',
                             'hypotheses': ['|- ( ( A + B ) / ( 1 - ( A x. B ) ) ) = 1',
                                            '|- ( A x. B ) =/= 1',
                                            '|- 0 < A',
                                            '|- 0 < B',
                                            '|- A < 1',
                                            '|- A e. RR',
                                            '|- B < 1',
                                            '|- B e. RR']},
 'pi_two_arctangents': {'formula': '|- ( 4 x. ( ( arctan ` ( 1 / 2 ) ) + ( arctan ` ( 1 / 3 ) ) ) ) = _pi',
                        'hypotheses': []},
 'arctangent_series_decomposition': {'formula': '|- ( arctan ` A ) = ( sum_ k e. ( 0 ... ( M - 1 ) ) ( ( -u '
                                                '1 ^ k ) x. ( ( A ^ ( ( 2 x. k ) + 1 ) ) / ( ( 2 x. k ) + 1 '
                                                ') ) ) + sum_ k e. ( ZZ>= ` M ) ( ( -u 1 ^ k ) x. ( ( A ^ ( '
                                                '( 2 x. k ) + 1 ) ) / ( ( 2 x. k ) + 1 ) ) ) )',
                                     'hypotheses': ['|- 0 <_ A', '|- A < 1', '|- A e. RR', '|- M e. NN0']},
 'arctangent_series_tail_lower': {'formula': '|- ( -u 1 x. ( ( A ^ M ) / ( 1 - A ) ) ) <_ sum_ k e. ( ZZ>= ` '
                                             'M ) ( ( -u 1 ^ k ) x. ( ( A ^ ( ( 2 x. k ) + 1 ) ) / ( ( 2 x. '
                                             'k ) + 1 ) ) )',
                                  'hypotheses': ['|- 0 <_ A', '|- A < 1', '|- A e. RR', '|- M e. NN0']},
 'arctangent_series_tail_upper': {'formula': '|- sum_ k e. ( ZZ>= ` M ) ( ( -u 1 ^ k ) x. ( ( A ^ ( ( 2 x. k '
                                             ') + 1 ) ) / ( ( 2 x. k ) + 1 ) ) ) <_ ( ( A ^ M ) / ( 1 - A ) '
                                             ')',
                                  'hypotheses': ['|- 0 <_ A', '|- A < 1', '|- A e. RR', '|- M e. NN0']},
 'gaussian_normalizer_positive': {'formula': '|- 0 < ( sqrt ` ( 2 x. _pi ) )', 'hypotheses': []},
 'gaussian_normalizer_real': {'formula': '|- ( sqrt ` ( 2 x. _pi ) ) e. RR', 'hypotheses': []},
 'gaussian_normalizer_square': {'formula': '|- ( ( sqrt ` ( 2 x. _pi ) ) ^ 2 ) = ( 2 x. _pi )',
                                'hypotheses': []},
 'finite_polynomial_integrable': {'formula': '|- ( x e. ( A [,] B ) |-> sum_ k e. I ( ( F ` k ) x. ( x ^ k ) '
                                             ') ) e. L^1',
                                  'hypotheses': ['|- A e. RR',
                                                 '|- B e. RR',
                                                 '|- F : I --> CC',
                                                 '|- I C_ NN0',
                                                 '|- I e. Fin']},
 'finite_polynomial_integral': {'formula': '|- S. ( A [,] B ) sum_ k e. I ( ( F ` k ) x. ( x ^ k ) ) _d x = '
                                           'sum_ k e. I ( ( F ` k ) x. ( ( ( B ^ ( k + 1 ) ) - ( A ^ ( k + 1 '
                                           ') ) ) / ( k + 1 ) ) )',
                                'hypotheses': ['|- A <_ B',
                                               '|- A e. RR',
                                               '|- B e. RR',
                                               '|- F : I --> CC',
                                               '|- I C_ NN0',
                                               '|- I e. Fin']},
 'integral_approximation_sandwich': {'formula': '|- ( ( S. ( A [,] B ) ( F ` x ) _d x - ( E x. ( B - A ) ) ) '
                                                '<_ S. ( A [,] B ) ( G ` x ) _d x /\\ S. ( A [,] B ) ( G ` x '
                                                ') _d x <_ ( S. ( A [,] B ) ( F ` x ) _d x + ( E x. ( B - A '
                                                ') ) ) )',
                                     'hypotheses': ['|- ( x e. ( A [,] B ) |-> ( F ` x ) ) e. L^1',
                                                    '|- ( x e. ( A [,] B ) |-> ( G ` x ) ) e. L^1',
                                                    '|- A <_ B',
                                                    '|- A e. RR',
                                                    '|- A. x e. ( A [,] B ) ( ( ( F ` x ) e. RR /\\ ( G ` x '
                                                    ') e. RR ) /\\ ( ( ( F ` x ) - E ) <_ ( G ` x ) /\\ ( G '
                                                    '` x ) <_ ( ( F ` x ) + E ) ) )',
                                                    '|- B e. RR',
                                                    '|- E e. RR']},
 'gaussian_continuous': {'formula': '|- ( x e. ( A [,] B ) |-> ( exp ` ( ( 0 - ( x x. x ) ) / 2 ) ) ) e. ( ( '
                                    'A [,] B ) -cn-> CC )',
                         'hypotheses': ['|- A e. RR', '|- B e. RR']},
 'gaussian_integrable': {'formula': '|- ( x e. ( A [,] B ) |-> ( exp ` ( ( 0 - ( x x. x ) ) / 2 ) ) ) e. L^1',
                         'hypotheses': ['|- A e. RR', '|- B e. RR']},
 'gaussian_normalizer_outside_integral': {'formula': '|- S. ( A [,] B ) ( ( exp ` ( ( 0 - ( x x. x ) ) / 2 ) '
                                                     ') / ( sqrt ` ( 2 x. _pi ) ) ) _d x = ( ( 1 / ( sqrt ` '
                                                     '( 2 x. _pi ) ) ) x. S. ( A [,] B ) ( exp ` ( ( 0 - ( x '
                                                     'x. x ) ) / 2 ) ) _d x )',
                                          'hypotheses': ['|- A e. RR', '|- B e. RR']},
 'gaussian_standard_form_integral': {'formula': '|- S. ( A [,] B ) ( ( exp ` ( ( 0 - ( x ^ 2 ) ) / 2 ) ) / ( '
                                                'sqrt ` ( 2 x. _pi ) ) ) _d x = ( ( 1 / ( sqrt ` ( 2 x. _pi '
                                                ') ) ) x. S. ( A [,] B ) ( exp ` ( ( 0 - ( x x. x ) ) / 2 ) '
                                                ') _d x )',
                                     'hypotheses': ['|- A e. RR', '|- B e. RR']},
 'lognormal_change_of_variables': {'formula': '|- S. ( A [,] B ) ( ( exp ` ( ( 0 - ( ( ( ( log ` x ) - M ) / '
                                              'S ) ^ 2 ) ) / 2 ) ) / ( x x. ( S x. ( sqrt ` ( 2 x. _pi ) ) ) '
                                              ') ) _d x = S. ( ( ( ( log ` A ) - M ) / S ) [,] ( ( ( log ` B '
                                              ') - M ) / S ) ) ( ( exp ` ( ( 0 - ( u ^ 2 ) ) / 2 ) ) / ( '
                                              'sqrt ` ( 2 x. _pi ) ) ) _d u',
                                   'hypotheses': ['|- A <_ B',
                                                  '|- A e. RR+',
                                                  '|- B e. RR',
                                                  '|- M e. RR',
                                                  '|- S e. RR+']},
 'log_positive_quotient': {'formula': '|- ( log ` ( A / B ) ) = ( ( log ` A ) - ( log ` B ) )',
                           'hypotheses': ['|- A e. RR+', '|- B e. RR+']},
 'log_positive_product': {'formula': '|- ( log ` ( A x. B ) ) = ( ( log ` A ) + ( log ` B ) )',
                          'hypotheses': ['|- A e. RR+', '|- B e. RR+']},
 'log_two_positive': {'formula': '|- 0 < ( log ` ( 1 + 1 ) )', 'hypotheses': []},
 'log_one_zero': {'formula': '|- ( log ` 1 ) = 0', 'hypotheses': []},
 'log_mean_value': {'formula': '|- E. x e. ( A (,) B ) ( 1 / x ) = ( ( ( log ` B ) - ( log ` A ) ) / ( B - A '
                               ') )',
                    'hypotheses': ['|- A < B', '|- A e. RR+', '|- B e. RR']},
 'exponential_increasing': {'formula': '|- ( ( A e. RR /\\ B e. RR ) -> ( A < B <-> ( exp ` A ) < ( exp ` B '
                                       ') ) )',
                            'hypotheses': []},
 'real_exponential_positive': {'formula': '|- ( A e. RR -> ( exp ` A ) e. RR+ )', 'hypotheses': []}}

@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __post_init__(self):
        if not isinstance(self.lo, Q) or not isinstance(self.hi, Q) or self.lo > self.hi:
            raise ValueError('Invalid exact rational interval')

    def __add__(self, other):
        other = interval(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -interval(other)

    def __mul__(self, other):
        other = interval(other)
        products = [x * y for x in (self.lo, self.hi) for y in (other.lo, other.hi)]
        return Interval(min(products), max(products))

    def __truediv__(self, other):
        other = interval(other)
        if other.lo <= 0 <= other.hi:
            raise ValueError('Division interval contains zero')
        return self * Interval(1 / other.hi, 1 / other.lo)

    def power(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError('Natural exponent required')
        result = interval(1)
        for _ in range(exponent):
            result = result * self
        return result

    def square(self):
        lower = Q(0) if self.lo <= 0 <= self.hi else min(self.lo ** 2, self.hi ** 2)
        return Interval(lower, max(self.lo ** 2, self.hi ** 2))

    def coarse(self, digits=12):
        scale = 10 ** digits
        return Interval(Q(self.lo.numerator * scale // self.lo.denominator, scale), Q(-((-self.hi.numerator * scale) // self.hi.denominator), scale))

    def encoded(self):
        return [str(self.lo), str(self.hi)]


def interval(value):
    return value if isinstance(value, Interval) else Interval(Q(value), Q(value))


def log_unit(value, count=48):
    value = Q(value)
    if not 1 <= value <= 2 or not isinstance(count, int) or count < 1:
        raise ValueError('Logarithm series domain')
    q = 1 - 1 / value
    if not 0 <= q <= Q(1, 2) or 1 - q != 1 / value:
        raise AssertionError('Logarithm reciprocal substitution')
    polynomial = sum((q ** k / k for k in range(1, count + 1)), Q(0))
    tail = q ** (count + 1) / (1 - q)
    return Interval(polynomial, polynomial + tail)


def logarithm_rescaling(value):
    value = Q(value)
    if value <= 0:
        raise ValueError('Positive logarithm argument required')
    unit, exponent, steps = value, 0, []
    while unit < 1:
        previous = unit
        unit *= 2
        exponent -= 1
        if not previous > 0 or unit != 2 * previous or unit * Q(2) ** exponent != value:
            raise AssertionError('Positive logarithm product step')
        steps.append({'before': str(previous), 'after': str(unit), 'log_two_coefficient': -1, 'law': 'log_positive_product'})
    while unit > 2:
        previous = unit
        unit /= 2
        exponent += 1
        if not unit > 0 or previous != 2 * unit or unit * Q(2) ** exponent != value:
            raise AssertionError('Positive logarithm quotient step')
        steps.append({'before': str(previous), 'after': str(unit), 'log_two_coefficient': 1, 'law': 'log_positive_quotient'})
    if unit * Q(2) ** exponent != value:
        raise AssertionError('Logarithm rescaling identity')
    if sum(row['log_two_coefficient'] for row in steps) != exponent:
        raise AssertionError('Logarithm coefficient accumulation')
    return unit, exponent, steps


def log_bound(value):
    unit, exponent, steps = logarithm_rescaling(value)
    return (log_unit(unit) + log_unit(Q(2)) * exponent).coarse()


def exp_point(value, count=16):
    value = Q(value)
    if abs(value) > 1 or not isinstance(count, int) or count < 1:
        raise ValueError('Exponential remainder domain')
    polynomial = sum((value ** k / factorial(k) for k in range(count)), Q(0))
    tail = abs(value) ** count * Q(count + 1, factorial(count) * count)
    return Interval(polynomial - tail, polynomial + tail)


def exp_bound(value):
    value = interval(value).coarse()
    if value.lo < -1 or value.hi > 1:
        raise ValueError('Exponential interval outside the certified domain')
    return Interval(exp_point(value.lo).lo, exp_point(value.hi).hi)


def arctan_bound(value, count=64):
    value = Q(value)
    if not 0 <= value < 1 or not isinstance(count, int) or count < 0:
        raise ValueError('Arctangent remainder domain')
    polynomial = sum((Q(-1) ** k * value ** (2 * k + 1) / (2 * k + 1) for k in range(count)), Q(0))
    tail = value ** count / (1 - value)
    return Interval(polynomial - tail, polynomial + tail)


def normalizer_bound():
    pi = (arctan_bound(Q(1, 2)) + arctan_bound(Q(1, 3))) * 4
    result = Interval(Q('2.50662827463100'), Q('2.50662827463101'))
    if not 0 < result.lo or not result.lo ** 2 < 2 * pi.lo <= 2 * pi.hi < result.hi ** 2:
        raise AssertionError('Positive square-root enclosure')
    return result


def density_bound(value):
    value = Q(value)
    if value <= 0:
        raise ValueError('Positive density argument required')
    standardized = (log_bound(value) + Q('2.68')) / Q('.59')
    exponent = -standardized.square() / 2
    return exp_bound(exponent) / (interval(value) * Q('.59') * normalizer_bound())


def polynomial_primitive(value, count=12):
    value = interval(value)
    result = interval(0)
    for k in range(count):
        coefficient = Q(-1, 2) ** k / Q(factorial(k) * (2 * k + 1))
        result = result + value.power(2 * k + 1) * coefficient
    return result


def gaussian_area_bound(lower, upper, count=12):
    if not isinstance(count, int) or count < 1:
        raise ValueError('Positive polynomial truncation order required')
    lower, upper = interval(lower), interval(upper)
    if lower.hi > upper.lo:
        raise ValueError('Endpoint order is not certified')
    domain = Interval(lower.lo, upper.hi)
    exponent = -domain.square() / 2
    if exponent.lo < -1 or exponent.hi > 1:
        raise ValueError('Uniform exponential remainder domain')
    tail = Q(count + 1, factorial(count) * count)
    width = upper.hi - lower.lo
    polynomial_integral = polynomial_primitive(upper, count) - polynomial_primitive(lower, count)
    return polynomial_integral + Interval(-width * tail, width * tail)


def valid_analytical_interfaces(formulas):
    return formulas == EXPECTED_ANALYTICAL_INTERFACES


def rejected_analytical_mutations(formulas, field):
    for name, row in formulas.items():
        changed = {**formulas, name: dict(row)}
        if field == 'formula':
            changed[name]['formula'] = '|- 0 = 1'
        elif field == 'hypotheses':
            changed[name]['hypotheses'] = row['hypotheses'][1:] if row['hypotheses'] else ['|- 0 = 1']
        else:
            raise ValueError('Unknown analytical interface field')
        if valid_analytical_interfaces(changed):
            return False
    return True


@lru_cache(maxsize=1)
def analytical_foundations():
    proofs = {}
    proofs.update(fundamentos_area.certificates())
    proofs.update(fundamentos_log.logarithm_series_bounds())
    proofs.update(fundamentos_pi.certificates())
    proofs.update(integracao_polinomial.finite_polynomial_integral())
    proofs['integral_approximation_sandwich'] = integracao_polinomial.integral_approximation_sandwich()
    proofs.update(integracao_polinomial.gaussian_integrable())
    proofs['gaussian_normalizer_outside_integral'] = integracao_polinomial.gaussian_normalizer_outside_integral()
    proofs['gaussian_standard_form_integral'] = integracao_polinomial.gaussian_standard_form_integral()
    proofs['lognormal_change_of_variables'] = substituicao_geral.lognormal_change_of_variables()
    proofs.update({name: row['proof'] for name, row in fundamentos_informacao.logarithm_basic_certificates().items()})
    a = fundamentos_area.a
    proofs['exponential_increasing'] = a.mm('eflt')
    proofs['real_exponential_positive'] = a.mm('rpefcl')
    formulas = {name: {'formula': a.infer(proof)[0], 'hypotheses': sorted(a.infer(proof)[1])} for name, proof in proofs.items()}
    if not valid_analytical_interfaces(formulas):
        raise AssertionError('Analytic rule formula or hypotheses mismatch')
    x = sp.Symbol('x', real=True)
    polynomial = sum(sp.Rational(-1, 2) ** k * x ** (2 * k) / sp.factorial(k) for k in range(12))
    exponential_prefix = sum((-x * x / 2) ** k / sp.factorial(k) for k in range(12))
    if sp.Poly(sp.expand(polynomial - exponential_prefix), x).as_expr() != 0:
        raise AssertionError('Polynomial is not the exponential prefix')
    return formulas


def rational_certificates():
    foundations = analytical_foundations()
    parameters = {'A': Q('.03'), 'B': Q('.14'), 'M': Q('-2.68'), 'S': Q('.59')}
    if not parameters['A'] > 0 or not parameters['A'] <= parameters['B'] or not parameters['S'] > 0 or not all(isinstance(q, Q) for q in parameters.values()):
        raise AssertionError('Change-of-variables parameter obligations')
    lower = (log_bound(Q('.03')) + Q('2.68')) / Q('.59')
    upper = (log_bound(Q('.14')) + Q('2.68')) / Q('.59')
    area = gaussian_area_bound(lower, upper) / normalizer_bound()
    sums = {}
    partitions = {}
    for count in (4, 8, 32):
        step = Q('.11') / count
        points = [Q('.03') + index * step for index in range(1, count + 1)]
        if not points[-1] == Q('.14') or not all(Q('.03') < point <= Q('.14') for point in points):
            raise AssertionError('Invalid right-endpoint partition')
        total = interval(0)
        for point in points:
            total = total + density_bound(point) * step
        sums[count] = total
        partitions[count] = [str(point) for point in points]
    arguments = sorted({Q('.03'), Q('.14')} | {Q(point) for points in partitions.values() for point in points})
    rescalings = {str(value): logarithm_rescaling(value)[2] for value in arguments}
    return {'foundations': foundations, 'lognormal_area': area, 'right_sums': sums, 'partitions': partitions, 'transformed_endpoints': [lower.encoded(), upper.encoded()], 'logarithm_rescalings': rescalings, 'parameters': parameters}


def verify():
    data = rational_certificates()
    checks = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        checks.append({'id': name, 'passed': True})
    area = data['lognormal_area']
    check('certified_scaled_gaussian_area_rounding', Q('.8062405') < area.lo <= area.hi < Q('.8062415'))
    check('certified_original_lognormal_area_rounding', Q('.8062405') < area.lo <= area.hi < Q('.8062415') and 'lognormal_change_of_variables' in data['foundations'])
    sums = data['right_sums']
    check('certified_right_sum_4', Q('.69405') < sums[4].lo <= sums[4].hi < Q('.69415'))
    check('certified_right_sum_8', Q('.75715') < sums[8].lo <= sums[8].hi < Q('.75725'))
    check('certified_right_sum_32', Q('.79525') < sums[32].lo <= sums[32].hi < Q('.79535'))
    check('certified_displayed_error_decrease', sums[4].hi < sums[8].lo <= sums[8].hi < sums[32].lo <= sums[32].hi < area.lo)
    check('reject_wrong_area_rounding', not Q('.8062395') < area.lo <= area.hi < Q('.8062405'))
    check('reject_wrong_right_sum_rounding', not Q('.70005') < sums[4].lo <= sums[4].hi < Q('.70015'))
    check('reject_each_changed_analytic_formula', rejected_analytical_mutations(data['foundations'], 'formula'))
    check('reject_each_changed_analytic_hypothesis', rejected_analytical_mutations(data['foundations'], 'hypotheses'))
    return {'backend': 'Python/exact-rational-interval-certificates', 'passed': True, 'results': checks, 'area_interval': area.encoded(), 'right_sum_intervals': {str(n): result.encoded() for n, result in sums.items()}, 'analytic_proofs': sorted(data['foundations']), 'logarithm_rescalings': data['logarithm_rescalings'], 'parameters': {name: str(value) for name, value in data['parameters'].items()}, 'scope': 'The original lognormal integral and right-endpoint sums, with analytic series, finite polynomial integration, uniform error bounds, normalization and change of variables verified independently of Lean.'}


if __name__ == '__main__':
    print(json.dumps(verify()))
