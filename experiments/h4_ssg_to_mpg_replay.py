"""Exact replay of the two SSG threshold compilers in H4.

Run with python3 experiments/h4_ssg_to_mpg_replay.py. The optional Z3 CLI
cross-check solves small integer games from their adjacency lists alone.
Use --dump CASE --route direct to print one complete instance and certificate.
Use --verify FILE to check the target witness alone after a JSON round trip.
All expectation, threshold and certificate arithmetic is exact.
"""

import argparse
import json
import shutil
import subprocess
from collections import deque
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import lcm
from pathlib import Path
from random import Random
from tempfile import mkdtemp


WIN, LOSE = -1, -2


@dataclass(frozen=True)
class SSG:
    # Nonterminal rows contain ('max'/'min'/'coin', tuple of successor IDs).
    rows: tuple
    start: int = 0


@dataclass
class MPG:
    owners: list
    edges: list
    start: int


@dataclass
class Certificate:
    # For YES, fix Max and allow every Min edge. For NO, exchange the roles.
    yes: bool
    choices: list
    heights: list


def policies(game, owner):
    states = [i for i, (kind, _) in enumerate(game.rows) if kind == owner]
    return [dict(zip(states, choices)) for choices in
            product(*(dict.fromkeys(game.rows[i][1]) for i in states))]


def solve_linear(rows):
    """Sparse rational Gaussian elimination. Last column is the right side."""
    n = len(rows)
    for j in range(n):
        pivot = next(i for i in range(j, n) if rows[i].get(j, 0))
        rows[j], rows[pivot] = rows[pivot], rows[j]
        base = rows[j]
        for i in range(j + 1, n):
            if not rows[i].get(j, 0):
                continue
            ratio = rows[i][j] / base[j]
            for k, val in base.items():
                rows[i][k] = rows[i].get(k, 0) - ratio * val
                if not rows[i][k]:
                    del rows[i][k]
    x = [F(0)] * n
    for i in reversed(range(n)):
        x[i] = (rows[i].get(n, 0) - sum(v * x[k] for k, v in rows[i].items()
                                        if i < k < n)) / rows[i][i]
    return x


def chain_payoffs(game, profile, boundary, premium=F(0)):
    """Stop on boundary. Closed classes not reaching a nonzero payoff give zero
    for plain reachability. With a premium the caller supplies absorbing classes.
    """
    n = len(game.rows)
    children = [game.rows[i][1] if i not in profile else (profile[i],)
                for i in range(n)]
    fixed = dict(boundary)
    if not premium:
        predecessors = {}
        for i, successors in enumerate(children):
            if i not in fixed:
                for j in successors:
                    predecessors.setdefault(j, []).append(i)
        stack = [i for i in fixed if fixed[i]]
        reaches = set(stack)
        while stack:
            for i in predecessors.get(stack.pop(), ()):
                if i not in reaches:
                    reaches.add(i)
                    stack.append(i)
        fixed.update((i, F(0)) for i in range(n) if i not in reaches and i not in fixed)
    active = [i for i in range(n) if i not in fixed]
    index = {i: j for j, i in enumerate(active)}
    size = len(active)
    rows = []
    for i in active:
        row = {index[i]: F(1), size: premium}
        probability = F(1, len(children[i]))
        for j in children[i]:
            if j in fixed:
                row[size] += probability * fixed[j]
            else:
                k = index[j]
                row[k] = row.get(k, 0) - probability
        rows.append(row)
    fixed.update(zip(active, solve_linear(rows)))
    return tuple(fixed[i] for i in range(n))


def source_solution(game):
    """Enumerate stationary pairs and verify the coordinatewise max-min saddle."""
    max_strats, min_strats = policies(game, 'max'), policies(game, 'min')
    outcomes = [[chain_payoffs(game, a | b, {WIN: F(1), LOSE: F(0)})
                 for b in min_strats] for a in max_strats]
    lows = [tuple(map(min, zip(*row))) for row in outcomes]
    highs = [tuple(map(max, zip(*col))) for col in zip(*outcomes)]
    value = tuple(map(max, zip(*lows)))
    assert value == tuple(map(min, zip(*highs)))
    return value, max_strats[lows.index(value)], min_strats[highs.index(value)]


def read_state(values, index):
    return F(index == WIN) if index in (WIN, LOSE) else values[index]


def leak_game(game, bits):
    """At every nonterminal entry toss until first failure or all bits succeed."""
    n = len(game.rows)

    def entry(i):
        return i if i < 0 else n + i * bits

    rows = [(owner, tuple(entry(j) for j in successors)) for owner, successors in game.rows]
    for i in range(n):
        for k in range(bits):
            continuation = entry(i) + k + 1 if k + 1 < bits else LOSE
            rows.append(('coin', (i, continuation)))
    return SSG(tuple(rows), entry(game.start))


def dual(game):
    swap = {'max': 'min', 'min': 'max', 'coin': 'coin'}
    def flip(j):
        return {WIN: LOSE, LOSE: WIN}.get(j, j)
    return SSG(tuple((swap[k], tuple(map(flip, js))) for k, js in game.rows),
               flip(game.start))


class Compiled:
    """Expanded variable/row mean-payoff graph, with shared fold intermediates."""

    def __init__(self, game, threshold, rounds, scale):
        self.n = n = len(game.rows)
        self.scale = scale
        self.rounds = rounds
        self.ref = ref = n + 2
        self.gates = []
        count = ref + 1
        rows = []

        def variable(j):
            return n if j == WIN else n + 1 if j == LOSE else j

        def add_gate(owner, terms):
            nonlocal count
            v = count
            count += 1
            self.gates.append((owner, terms))
            if owner == 'max':
                rows.append((v, terms))
            else:
                rows.extend((v, (term,)) for term in terms)
            return v

        for i in range(n + 2):
            rows.append((ref, ((i, 0),)))
            rows.append((i, ((ref, scale),)))
        rows.extend([(ref, ((n, -scale),)), (n + 1, ((ref, 0),)),
                     (ref, ((variable(game.start), -int(threshold * scale)),))])
        assert (threshold * scale).denominator == 1 and scale % (1 << (rounds + 1)) == 0
        for i, (owner, successors) in enumerate(game.rows):
            terms = tuple((variable(j), 0) for j in successors)
            if owner == 'max':
                rows.append((i, terms))
            elif owner == 'min':
                rows.extend((i, (term,)) for term in terms)
            else:
                assert owner == 'coin' and len(terms) == 2
                hi, lo = add_gate('max', terms), add_gate('min', terms)
                for j in range(1, rounds + 1):
                    shift = scale // (1 << (j + 1))
                    pair = ((hi, -shift), (lo, shift))
                    hi, lo = add_gate('max', pair), add_gate('min', pair)
                rows.append((i, ((hi, 0),)))
        self.variables = count
        edges = [[] for _ in range(count)]
        for lhs, terms in rows:
            edges[lhs].append((len(edges), 0))
            edges.append(terms)
        start = len(edges)
        edges.append([(i, 0) for i in range(count)])
        self.graph = MPG(['min'] * count + ['max'] * len(rows) + ['min'], edges, start)

    def suggest(self, x, yes):
        """Certificate candidate only. The checker below never sees source data."""
        h = [v * self.scale for v in (*x, F(1), F(0), F(0))]
        for owner, terms in self.gates:
            h.append((max if owner == 'max' else min)(h[j] + w for j, w in terms))
        graph = self.graph
        for i in range(self.variables, graph.start):
            h.append(max(h[j] + w for j, w in graph.edges[i]))
        h.append(min(h[:self.variables]) if yes else h[self.ref])
        choices = []
        for i, edges in enumerate(graph.edges):
            if i == graph.start and not yes:
                choices.append(self.ref)
            elif graph.owners[i] == ('max' if yes else 'min'):
                compare = max if yes else min
                choices.append(compare(range(len(edges)), key=lambda k: h[edges[k][0]] + edges[k][1]))
            else:
                choices.append(None)
        return Certificate(yes, choices, h)


def inspect_certificate(graph, cert):
    """Use only the explicitly emitted graph, starting vertex and witness.

    A negative certificate tolerates zero reduced edges if their reachable
    subgraph is acyclic. Then each reachable simple cycle is strictly negative.
    Return topological ranks for the equality subgraph on the losing side.
    """
    n = len(graph.edges)
    assert len(cert.choices) == len(cert.heights) == len(graph.owners) == n
    fixed = 'max' if cert.yes else 'min'
    seen = {graph.start}
    work = [graph.start]
    tight = {}
    while work:
        i = work.pop()
        edges = graph.edges[i]
        if graph.owners[i] == fixed:
            k = cert.choices[i]
            assert isinstance(k, int) and 0 <= k < len(edges)
            edges = (edges[k],)
        tight[i] = []
        for j, w in edges:
            assert isinstance(w, int)
            reduced = w + cert.heights[j] - cert.heights[i]
            if (reduced < 0 if cert.yes else reduced > 0):
                return None
            if not cert.yes and reduced == 0:
                tight[i].append(j)
            if j not in seen:
                seen.add(j)
                work.append(j)
    if cert.yes:
        return {}
    indeg = dict.fromkeys(seen, 0)
    for js in tight.values():
        for j in js:
            indeg[j] += 1
    ready = deque(i for i in seen if not indeg[i])
    order = []
    while ready:
        i = ready.popleft()
        order.append(i)
        for j in tight[i]:
            indeg[j] -= 1
            if not indeg[j]:
                ready.append(j)
    if len(order) != len(seen):
        return None
    rank = {}
    for i in reversed(order):
        rank[i] = max((1 + rank[j] for j in tight[i]), default=0)
    return rank


def complement_game(graph):
    n = len(graph.edges)
    return MPG(['min' if o == 'max' else 'max' for o in graph.owners],
               [[(j, -n * w - 1) for j, w in edges] for edges in graph.edges], graph.start)


def complement_certificate(graph, cert):
    n = len(graph.edges)
    if cert.yes:
        heights = [-n * x for x in cert.heights]
    else:
        # Integer weights preserve inequalities after flooring. A zero-weight
        # cycle after flooring would already have been zero before flooring.
        floors = [x // 1 for x in cert.heights]
        ranks = inspect_certificate(graph, Certificate(False, cert.choices, floors))
        assert ranks is not None
        heights = [-n * x - ranks.get(i, 0) for i, x in enumerate(floors)]
    return Certificate(not cert.yes, cert.choices, heights)


def upper_suggestion(game, minimizing_policy, fixed, premium):
    # All plays under this Min policy hit fixed almost surely. The per-step
    # premium makes surviving Bellman edges strict; box caps cover value one.
    outcomes = [chain_payoffs(game, maximizing_policy | minimizing_policy, fixed, premium)
                for maximizing_policy in policies(game, 'max')]
    return tuple(min(F(1), x) for x in map(max, zip(*outcomes)))


def encode(game, threshold, route):
    """Build the complete target without solving either game.

    Return the target first. The remaining metadata is used only when suggesting
    independently checkable certificates for the replay.
    """
    n = len(game.rows)
    if game.start < 0 or threshold <= 0 or threshold > 1:
        answer = threshold <= 0 or (game.start == WIN and threshold <= 1)
        graph = MPG(['max'], [[(0, 1 if answer else -1)]], 0)
        return graph, None, None
    if route == 'direct':
        denominator = threshold.denominator * 3**(n + 1)
        underlying = dual(game)
        cutoff = 1 - threshold + F(1, denominator)
        rounds = denominator.bit_length() + 2 * (n + 1)
        scale = denominator << (rounds + 1)
    else:
        if route == 'leak':
            bits = 4 * n + threshold.denominator.bit_length() + 2
            underlying = leak_game(game, bits)
            cutoff = threshold - F(1, 2 * 4**n * threshold.denominator)
        else:
            assert route == 'stopping'
            underlying, cutoff = game, threshold
        count = len(underlying.rows)
        rounds = 2 * (count + 1) + cutoff.denominator.bit_length()
        scale = lcm(cutoff.denominator, 1 << (rounds + 1))
    compiled = Compiled(underlying, cutoff, rounds, scale)
    target = complement_game(compiled.graph) if route == 'direct' else compiled.graph
    return target, underlying, compiled


def replay(game, threshold, route, original):
    target, underlying, compiled = encode(game, threshold, route)
    if compiled is None:
        return target, Certificate(target.edges[0][0][1] >= 0, [0], [0])
    fixed = {WIN: F(1), LOSE: F(0)}
    if route == 'direct':
        original_values, original_max, _ = original
        lower = tuple(1 - x for x in original_values)
        # The dual's greatest fixed point corresponds to nontermination paying
        # one. Under an optimal original Max policy, any nonterminal recurrent
        # class of a positional opponent consists of original value-zero states.
        fixed.update((i, F(1)) for i, v in enumerate(lower) if v == 1)
        minimizing = {i: {WIN: LOSE, LOSE: WIN}.get(j, j) for i, j in original_max.items()}
    else:
        lower, _, minimizing = source_solution(underlying)
    yes = compiled.suggest(lower, True)
    if inspect_certificate(compiled.graph, yes) is not None:
        cert = yes
    else:
        upper = upper_suggestion(underlying, minimizing, fixed, F(1, 1 << compiled.rounds))
        cert = compiled.suggest(upper, False)
        if inspect_certificate(compiled.graph, cert) is None:
            dump_failure(game, threshold, route, compiled.graph, cert)
    if route == 'direct':
        cert = complement_certificate(compiled.graph, cert)
    return target, cert


def smt_label(graph):
    """Graph-only cross-check, allowing a closed winning subset from the start.

    Unlike the cycle/potential checker above this neither receives a strategy nor
    knows the compiler's fresh-start layout. The primary check never trusts UNSAT.
    """
    lines = ['(set-logic QF_IDL)']
    for i in range(len(graph.edges)):
        lines.extend([f'(declare-const p{i} Int)', f'(declare-const a{i} Bool)'])
    lines.append(f'(assert a{graph.start})')
    for i, edges in enumerate(graph.edges):
        op = 'or' if graph.owners[i] == 'max' else 'and'
        terms = []
        for j, w in edges:
            number = str(w) if w >= 0 else f'(- {-w})'
            terms.append(f'(and a{j} (<= (- p{i} p{j}) {number}))')
        lines.append(f'(assert (=> a{i} ({op} {" ".join(terms)})))')
    lines.append('(check-sat)')
    result = subprocess.run(['z3', '-in'], input='\n'.join(lines), text=True,
                            capture_output=True, check=True, timeout=60)
    assert result.stdout.strip() in ('sat', 'unsat'), result.stdout
    return result.stdout.strip() == 'sat'


def record(game, threshold, route, graph, cert):
    return {'source': {'rows': game.rows, 'start': game.start, 'threshold': str(threshold)},
            'route': route, 'mpg': {'owners': graph.owners, 'edges': graph.edges, 'start': graph.start},
            'certificate': {'yes': cert.yes, 'choices': cert.choices,
                            'heights': [str(x) for x in cert.heights]}}


def verify_dump(path):
    payload = json.loads(Path(path).read_text())
    data, witness = payload['mpg'], payload['certificate']
    graph = MPG(data['owners'], data['edges'], data['start'])
    n = len(graph.owners)
    if not (0 <= graph.start < n and len(graph.edges) == n
            and all(owner in ('min', 'max') for owner in graph.owners)
            and all(edges and all(0 <= j < n and type(w) is int for j, w in edges)
                    for edges in graph.edges)):
        raise ValueError('invalid encoded target game')
    if type(witness['yes']) is not bool:
        raise ValueError('certificate must specify the winning side')
    cert = Certificate(witness['yes'], witness['choices'], [F(x) for x in witness['heights']])
    if inspect_certificate(graph, cert) is None:
        raise ValueError('the target certificate failed')
    return graph, cert


def dump_failure(game, threshold, route, graph, cert):
    path = Path(mkdtemp(prefix='h4-ssg-counterexample-')) / 'example.json'
    path.write_text(json.dumps(record(game, threshold, route, graph, cert)) + '\n')
    raise AssertionError(f'candidate or decision mismatch; full diagnostic at {path}')


def cases(random_count, systematic):
    half = SSG((('coin', (WIN, LOSE)),))
    third = SSG((('coin', (1, LOSE)), ('coin', (0, WIN))))
    competitive = SSG((('max', (1, 2)), ('min', (2, 3)), ('coin', (0, LOSE)),
                       ('coin', (WIN, 1))))
    traps = SSG((('max', (1, 3)), ('min', (2, 3)), ('coin', (WIN, LOSE)),
                 ('coin', (3, 3))))
    slow = SSG(tuple(('coin', (i+1 if i < 4 else WIN, 0)) for i in range(5)))
    mixed = SSG((('max', (1, LOSE)), ('min', (2, WIN)), ('coin', (WIN, 3)),
                 ('coin', (0, LOSE))))
    fixtures = [
        ('half-equal', half, F(1, 2), True), ('half-above', half, F(257, 512), True),
        ('third-equal', third, F(1, 3), True), ('third-above', third, F(334, 1001), True),
        ('third-below', third, F(333, 1000), True),
        ('competition', competitive, F(1, 2), True),
        ('nonstopping-trap', traps, F(1, 7), False),
        ('trapped-zero', SSG((('coin', (0, 0)),)), F(1, 37), False),
        ('optional-loop-equality', SSG((('max', (0, 1)), ('coin', (WIN, LOSE)))),
         F(1, 2), False),
        ('closed-third-equal', SSG((('coin', (1, 2)), ('coin', (0, WIN)),
                                    ('max', (2,)))), F(1, 3), False),
        ('half-large-denominator', half, F(1, 2) + F(1, 2**31 + 1), True),
        ('mixed-cycle-equal', mixed, F(2, 3), True),
        ('mixed-cycle-above', mixed, F(683, 1024), True),
        ('forced-escape', slow, F(1), True),
        ('duplicate-coin', SSG((('coin', (WIN, WIN)),)), F(1), True),
        ('terminal-win', SSG((), WIN), F(3, 5), True),
        ('terminal-lose', SSG((), LOSE), F(1, 7), True),
        ('threshold-negative', half, F(-2, 3), True),
        ('threshold-zero', half, F(0), True), ('threshold-high', half, F(7, 5), True),
    ]
    rng = Random(16891)
    for k in range(random_count):
        n = 1 + k % 4
        states = [WIN, LOSE, *range(n)]
        rows = tuple((rng.choice(('min', 'max', 'coin')),
                      tuple(rng.choice(states) for _ in range(2))) for _ in range(n))
        game = SSG(rows, rng.randrange(n))
        value = read_state(source_solution(game)[0], game.start)
        t = (value, value + F(1, 251), F(rng.randrange(1, 13), 13))[k % 3]
        fixtures.append((f'random-{k}', game, t, False))
    yield from fixtures
    for n in range(1, systematic + 1):
        successors = combinations_with_replacement((WIN, LOSE, *range(n)), 2)
        options = list(product(('max', 'min', 'coin'), successors))
        for i, rows in enumerate(product(options, repeat=n)):
            game = SSG(rows)
            v = source_solution(game)[0][0]
            for j, t in enumerate(dict.fromkeys((v, v + F(1, 257), F(1, 2), v - F(1, 257)))):
                yield f'systematic-{n}-{i}-{j}', game, t, False


def mutation_checks():
    # At equality both a weak threshold and an undersized positive margin
    # incorrectly certify strict source NO. The finite fold overshoots the
    # midpoint of (1, 1/3) by 1/(6 * 2**r).
    game = SSG((('coin', (1, 2)), ('coin', (0, WIN)), ('max', (2,))))
    values, _, _ = source_solution(game)
    assert values == (F(1, 3), F(2, 3), 0)
    denominator = 3 * 3**4
    r = denominator.bit_length() + 8
    for margin in (F(0), F(1, 12 * 2**r)):
        cutoff = F(2, 3) + margin
        scale = lcm(cutoff.denominator, 1 << (r + 1))
        mutated = Compiled(dual(game), cutoff, r, scale)
        wrong = mutated.suggest((cutoff, F(1, 3), F(1)), True)
        assert inspect_certificate(mutated.graph, wrong) is not None
        final_wrong = complement_certificate(mutated.graph, wrong)
        assert not final_wrong.yes
        assert inspect_certificate(complement_game(mutated.graph), final_wrong) is not None

    # One unrefined max can turn 1/2 into 1 and accept the false 3/4 bound.
    coarse = Compiled(SSG((('coin', (WIN, LOSE)),)), F(3, 4), 0, 4)
    false_positive = coarse.suggest((F(3, 4),), True)
    assert inspect_certificate(coarse.graph, false_positive) is not None
    false_positive.heights[coarse.graph.start] += 100
    assert inspect_certificate(coarse.graph, false_positive) is None

    # A nonpositive potential is insufficient when a reachable zero cycle
    # survives. Conversely, an unreachable zero cycle cannot invalidate a win.
    zero = MPG(['min', 'min'], [[(1, 0)], [(0, 0)]], 0)
    assert inspect_certificate(zero, Certificate(False, [0, 0], [0, 0])) is None
    isolated = MPG(['min', 'max'], [[(0, -1)], [(1, 0)]], 0)
    assert inspect_certificate(isolated, Certificate(False, [0, None], [0, 0])) is not None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--random', type=int, default=12, help='number of seeded tiny games')
    parser.add_argument('--systematic', type=int, choices=(0, 1, 2), default=0,
                        help='all labelled games of up to N states with unordered binary successors (direct route)')
    parser.add_argument('--route', choices=('all', 'direct', 'leak', 'stopping'), default='all')
    parser.add_argument('--dump', metavar='CASE', help='print graph and certificate JSON for one case')
    parser.add_argument('--verify', metavar='FILE', help='check just the target certificate from a JSON dump')
    smt = parser.add_mutually_exclusive_group()
    smt.add_argument('--smt-limit', type=int, default=200, help='optional Z3 cross-check vertex limit, 0 disables')
    smt.add_argument('--require-smt', action='store_true',
                     help='require Z3 and cross-check every emitted target graph')
    args = parser.parse_args()
    if args.dump and args.route == 'all':
        parser.error('--dump also needs one explicit --route')
    if args.systematic and args.route != 'direct':
        parser.error('--systematic needs --route direct')
    if not __debug__:
        parser.error('run without -O to keep witness validation enabled')
    if args.verify:
        if args.require_smt:
            parser.error('--require-smt needs a source replay, not --verify')
        graph, cert = verify_dump(args.verify)
        print(f'Verified {"YES" if cert.yes else "NO"} on {len(graph.owners)} vertices')
        return
    have_z3 = shutil.which('z3') is not None
    if args.require_smt and not have_z3:
        parser.error('--require-smt needs the z3 executable on PATH')
    mutation_checks()
    results = {}
    for name, game, threshold, stopping in cases(args.random, args.systematic):
        if args.dump and name != args.dump:
            continue
        original = source_solution(game)
        answer = read_state(original[0], game.start) >= threshold
        for route in ('direct', 'stopping', 'leak'):
            if args.route not in ('all', route) or (route == 'stopping' and not stopping):
                continue
            graph, cert = replay(game, threshold, route, original)
            if cert.yes != answer or inspect_certificate(graph, cert) is None:
                dump_failure(game, threshold, route, graph, cert)
            vertices = len(graph.edges)
            via_smt = have_z3 and (args.require_smt or vertices <= args.smt_limit)
            if via_smt and smt_label(graph) != answer:
                dump_failure(game, threshold, route, graph, cert)
            if args.dump:
                print(json.dumps(record(game, threshold, route, graph, cert)))
                return
            stats = results.setdefault(route, [0, 0, 0, 0, 0])
            stats[0] += 1
            stats[1] += int(answer)
            stats[2] += int(via_smt)
            stats[3] = max(stats[3], vertices)
            stats[4] = max(stats[4], sum(map(len, graph.edges)))
    if args.dump:
        parser.error('unknown case or unavailable route')
    for route, (count, yes, smt, vertices, edges) in results.items():
        print(f'{route}: {count} exact graph certificates ({yes} YES, {count-yes} NO), '
              f'{smt} graph-only SMT checks, largest target {vertices} vertices and {edges} edges')


if __name__ == '__main__':
    main()
