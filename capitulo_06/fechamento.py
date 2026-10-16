import json
import sympy as sp

results = []


def check(identifier, condition):
    results.append({'id': identifier, 'passed': bool(condition)})


def equal(left, right):
    return sp.simplify(sp.expand_log(left - right, force=False)) == 0


def color_model(prior, meaning, encoder):
    p = tuple(map(sp.Rational, prior))
    r = tuple(tuple(map(sp.Rational, row)) for row in meaning)
    q = tuple(tuple(map(sp.Rational, row)) for row in encoder)
    if not p or len(p) != len(r) or len(p) != len(q) or not r[0] or not q[0]:
        raise ValueError('Dimensões incompatíveis')
    if any(len(row) != len(r[0]) for row in r) or any(len(row) != len(q[0]) for row in q):
        raise ValueError('Dimensões incompatíveis')
    if any(v < 0 for row in (p, *r, *q) for v in row) or any(sum(row) != 1 for row in (p, *r, *q)):
        raise ValueError('Probabilidades inválidas')
    nm, nw, nu = len(p), len(q[0]), len(r[0])
    pw = [sum(p[m] * q[m][w] for m in range(nm)) for w in range(nw)]
    pu = [sum(p[m] * r[m][u] for m in range(nm)) for u in range(nu)]
    joint = [[sum(p[m] * q[m][w] * r[m][u] for m in range(nm)) for u in range(nu)] for w in range(nw)]
    decoder = [[joint[w][u] / pw[w] if pw[w] else sp.S.Zero for u in range(nu)] for w in range(nw)]
    source_information = sum(p[m] * r[m][u] * sp.log(r[m][u] / pu[u], 2) for m in range(nm) for u in range(nu) if p[m] * r[m][u])
    word_information = sum(joint[w][u] * sp.log(decoder[w][u] / pu[u], 2) for w in range(nw) for u in range(nu) if joint[w][u])
    distortion = sp.S.Zero
    for m in range(nm):
        for w in range(nw):
            pair = p[m] * q[m][w]
            if not pair:
                continue
            for u in range(nu):
                if r[m][u]:
                    if decoder[w][u] <= 0 or pu[u] <= 0:
                        raise ValueError('Suporte incompatível')
                    distortion += pair * r[m][u] * sp.log(r[m][u] / decoder[w][u], 2)
    return source_information, word_information, distortion, pw, pu, joint, decoder


r, d, u, p, q, a, b, c = sp.symbols('r d u p q a b c', positive=True)
t, x, y = sp.symbols('t x y', real=True)
check('positive_log_split', equal(sp.log(r / d, 2), sp.log(r / u, 2) - sp.log(d / u, 2)))
check('weighted_log_split', equal(t * sp.log(r / d, 2), t * sp.log(r / u, 2) - t * sp.log(d / u, 2)))
check('zero_weight_branch', sp.S.Zero * x == 0)
check('mutual_information_cancel_prior', equal(p * r / (p * u), r / u))
check('mutual_information_decoder_ratio', equal((q / p) / u, q / (p * u)))
check('finite_aggregation_induction_step', sp.expand((a + b) * t - a * t - b * t) == 0)
check('finite_aggregation_empty', sum(()) == 0)
check('posterior_decoder_summand', equal(p * q * r / d, (p * q / d) * r))
check('fixed_source_difference', sp.expand((t - x) - (t - y) - (y - x)) == 0)
models = [
    ([sp.Rational(1, 2), sp.Rational(1, 2)], [[1, 0], [0, 1]], [[1, 0], [0, 1]]),
    ([sp.Rational(1, 2), sp.Rational(1, 2)], [[1, 0], [0, 1]], [[1], [1]]),
    ([1, 0], [[sp.Rational(1, 3), sp.Rational(2, 3), 0], [0, 0, 1]], [[1, 0], [0, 1]]),
    ([sp.Rational(1, 3), sp.Rational(2, 3)], [[sp.Rational(1, 4), sp.Rational(3, 4)], [sp.Rational(1, 2), sp.Rational(1, 2)]], [[sp.Rational(1, 2), sp.Rational(1, 2), 0], [sp.Rational(1, 3), sp.Rational(2, 3), 0]])
]
evaluated = [color_model(*model) for model in models]
check('finite_models_information_identity', all(equal(v[2], v[0] - v[1]) for v in evaluated))
check('finite_models_probability_marginals', all(sum(v[3]) == 1 and sum(v[4]) == 1 and sum(map(sum, v[5])) == 1 for v in evaluated))
check('finite_models_decoder_normalization', all(sum(v[6][w]) == 1 for v in evaluated for w in range(len(v[3])) if v[3][w]))
check('finite_models_zero_probability_boundaries', evaluated[2][3][1] == 0 and evaluated[2][4][2] == 0 and evaluated[3][3][2] == 0)
check('different_vocabulary_order', equal(evaluated[0][0], evaluated[1][0]) and evaluated[0][2] < evaluated[1][2] and evaluated[0][1] > evaluated[1][1])
rejected = False
try:
    color_model([1], [[1]], [[2]])
except ValueError:
    rejected = True
check('invalid_normalization_rejected', rejected)
report = {'backend': 'Python/SymPy', 'checks': len(results), 'passed': all(item['passed'] for item in results), 'results': results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
