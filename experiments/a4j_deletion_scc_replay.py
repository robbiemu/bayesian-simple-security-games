"""Exact replay for the additive deletion-component bound in A4i1b.

OpenAI Dot supplied the square chain and original solver replay, inspired by
Cinna Davis's catalogue of Hartke–Stolee–West–Yancey's matching-excess problem
and their binary matching construction. Dot's background comparison supplied
the componentwise count, its enumeration, and the return edge. The decomposition
is Tassa's balanced perfect-matching algorithm (arXiv:1107.4711, §2.1).
Survival and strict progress come from the project's pre-existing A4i1b ascent.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import prod

import a4j_unit_prices as auction
from a4j_deletion_product_replay import (
    chain, first_primes, matching_products, solve_with_steps,
)


def deletion_components(viable, omitted):
    """Find one viable matching, then the SCCs of its contracted pairs."""
    matched = {}
    for buyer in range(len(viable)):
        if buyer != omitted:
            assert auction.augment_or_reach(buyer, matched, viable) is None
    owner = {g: i for i, g in matched.items()}
    arcs = {i: {owner[g] for g in viable[i]} for i in matched}

    # These fixtures are small. Compute SCCs directly by mutual reachability.
    reachable = {}
    for start in arcs:
        seen = {start}
        queue = [start]
        for i in queue:
            new = arcs[i] - seen
            seen.update(new)
            queue.extend(new)
        reachable[start] = seen

    remaining = set(matched)
    components = []
    while remaining:
        i = min(remaining)
        rows = {j for j in reachable[i] if i in reachable[j]}
        goods = {matched[j] for j in rows}
        remaining -= rows
        components.append((rows, goods))
    return components


def rank(component, viable):
    rows, goods = component
    return sum(len(viable[i] & goods) for i in rows) - 2 * len(rows) + 1


def product_counts(rows, goods, demand, slopes):
    return Counter(matching_products(rows, goods, demand, slopes))


def factored_counts(components, demand, slopes):
    counts = Counter({1: 1})
    for rows, goods in components:
        local = product_counts(rows, goods, demand, slopes)
        combined = Counter()
        for p, count in counts.items():
            for q, ways in local.items():
                combined[p * q] += count * ways
        counts = combined
    return counts


def viable_goods(bids):
    return [{j for j, b in enumerate(row) if b > 0} for row in bids]


def check_chain(m):
    bids, slopes = chain(first_primes(m), Fraction(0))
    viable = viable_goods(bids)
    root = 2 * m
    total = 0
    for omitted in range(root + 1):
        components = deletion_components(viable, omitted)
        ranks = [rank(c, viable) for c in components]
        free_squares = m if omitted == root else m - (omitted // 2 + 1)
        assert all(h in (0, 1) for h in ranks) and sum(ranks) == free_squares
        for c, h in zip(components, ranks):
            assert len(product_counts(*c, viable, slopes)) == 2**h
        total += sum(2**h - 1 for h in ranks)
    assert total == m**2
    print(f"chain m={m}: max rank 1, additive product and rank bounds {total}")
    if m >= 2:
        viable[root - 1].add(1)  # b_m to B_1, with unit slope already in the matrix
        assert max(map(len, viable)) == 3
        assert max(sum(j in row for row in viable) for j in range(root)) == 3
        component, = deletion_components(viable, root)
        assert rank(component, viable) == m + 1
        counts = product_counts(*component, viable, slopes)
        assert sum(counts.values()) == 2**m + 1 and len(counts) == 2**m
        print(f"return m={m}: one root-deletion component, rank {m + 1}")


def check_tight_subgraphs():
    """Exhaust both realizable and arbitrary tight-edge restrictions for m=2."""
    bids, slopes = chain(first_primes(2), Fraction(0))
    viable = viable_goods(bids)
    root = len(bids) - 1
    cases = 0
    for omitted in range(root + 1):
        rows, goods = set(range(root + 1)) - {omitted}, set(range(root))
        components = deletion_components(viable, omitted)
        edges = [(i, j) for i in rows for j in viable[i]]
        for mask in range(1 << len(edges)):
            demand = [set() for _ in viable]
            for k, (i, j) in enumerate(edges):
                if mask & (1 << k):
                    demand[i].add(j)
            assert factored_counts(components, demand, slopes) == product_counts(
                rows, goods, demand, slopes)
            cases += 1
    print(f"m=2: exact matching product multiplicities factor on all {cases} restrictions")


def check_survival(m):
    bids, slopes = chain(first_primes(m), Fraction(1, m + 1))
    viable = viable_goods(bids)
    _, stats, steps = solve_with_steps(bids, slopes, exhaustive=True)
    components = {r: deletion_components(viable, r) for r in range(len(bids))}
    previous = {}
    old_step = None
    for step in steps:
        assert set(step.buyers) == components.keys() and len(step.goods) == 2 * m
        minima = {}
        for r, parts in components.items():
            for k, (rows, goods) in enumerate(parts):
                local = min(matching_products(rows, goods, step.demand, slopes))
                plan = step.plans[r]
                assert {plan[i] for i in rows} == goods
                assert prod(slopes[i][plan[i]] for i in rows) == local
                minima[r, k] = local
                if old_step is not None:
                    assert all(old_step.plans[r][i] in step.demand[i] for i in rows)
        if previous:
            assert all(minima[key] <= old for key, old in previous.items())
            assert any(minima[key] < old for key, old in previous.items())
        previous, old_step = minima, step
    assert len(steps) - 1 == stats["internal"] == m
    print(f"shaded m={m}: old local plans stay feasible and a component minimum drops at all {m} events")


def check_subdivided_clique(t):
    """Squares at vertices, one private buyer and good per undirected clique edge."""
    edges = list(combinations(range(t), 2))
    n = 2 * t + len(edges)
    viable = [set() for _ in range(n + 1)]
    slopes = [[1] * n for _ in viable]
    primes = iter(first_primes(t + 2 * len(edges)))
    for u in range(t):
        a, b = 2 * u, 2 * u + 1
        viable[a] = {a, b}
        viable[b] = {a, b}
        viable[n].add(a)
        slopes[a][a] = next(primes)
    for e, (u, v) in enumerate(edges, 2 * t):
        viable[e].add(e)
        viable[2 * u + 1].add(e)
        viable[2 * v + 1].add(e)
        slopes[2 * u + 1][e] = next(primes)
        slopes[2 * v + 1][e] = next(primes)
    assigned = {i: i for i in range(n)}
    buyers, goods = auction.augment_or_reach(n, assigned, viable)
    assert len(buyers) == n + 1 and len(goods) == n
    products = product_counts(set(range(n)), set(range(n)), viable, slopes)
    assert len(products) == sum(products.values()) == 2**t

    # The lexicographically first traversal of each undirected clique cycle
    # starts at its smallest vertex, with its two neighbors in ascending order.
    edge_good = {pair: j for j, pair in enumerate(edges, 2 * t)}
    cycles = 0
    for length in range(3, t + 1):
        for cycle in permutations(range(t), length):
            if cycle[0] != min(cycle) or cycle[1] > cycle[-1]:
                continue
            forward, backward = 1, 1
            for u, v in zip(cycle, cycle[1:] + cycle[:1]):
                g = edge_good[min(u, v), max(u, v)]
                forward *= slopes[2 * u + 1][g]
                backward *= slopes[2 * v + 1][g]
            assert forward != backward
            cycles += 1
    for omitted in range(n + 1):
        parts = deletion_components(viable, omitted)
        nontrivial = sorted(h for c in parts if (h := rank(c, viable)) > 0)
        if omitted == n:
            assert nontrivial == [1] * t
        elif omitted < 2 * t:
            assert nontrivial == [1] * (t - 1)
        else:
            assert nontrivial == [1] * (t - 2) + [3]
    print(f"subdivided K_{t}: max deletion-component rank 3, {len(products)} root products, "
          f"{cycles} nonunit cycles in the clique subdivision")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to enable the verification assertions.")
    for size in (1, 2, 3, 5, 8, 10):
        check_chain(size)
    check_tight_subgraphs()
    for size in (1, 2, 3, 5):
        check_survival(size)
    for size in (3, 4, 5):
        check_subdivided_clique(size)
