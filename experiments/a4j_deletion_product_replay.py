"""Replay the A4i1b chain control, staggered switches, and four-type transfer."""

from dataclasses import dataclass, field
from fractions import Fraction
from math import prod
from unittest.mock import patch

import a4j_unit_prices as auction


@dataclass
class Step:
    root: int
    buyers: tuple
    goods: tuple
    prices: tuple
    demand: tuple
    plans: dict = field(default_factory=dict)


def solve_with_steps(bids, slopes, exhaustive):
    """Record the public solver's calls without changing its auction rules."""
    steps = []
    current_prices = ()
    find_demands = auction.demands_at
    augment = auction.augment_or_reach

    def trace_demands(bids, slopes, prices):
        nonlocal current_prices
        current_prices = tuple(prices)
        return find_demands(bids, slopes, prices)

    def trace_reach(root, assigned, demand):
        reached = augment(root, assigned, demand)
        if reached is not None:
            buyers, goods = reached
            steps.append(Step(root, tuple(buyers), tuple(goods), current_prices,
                              tuple(map(frozenset, demand))))
        return reached

    def trace_matching(rows, goods, demand, slopes):
        step = steps[-1]
        omitted, = set(step.buyers).difference(rows)
        plan = auction.smallest_product_matching(rows, goods, demand, slopes)
        step.plans[omitted] = plan
        return plan

    with (patch.object(auction, "demands_at", trace_demands),
          patch.object(auction, "augment_or_reach", trace_reach)):
        prices, assigned, counts = auction.solve(bids, slopes, matching_solver=trace_matching)
    auction.check_certificate(bids, slopes, prices, assigned, exhaustive=exhaustive)
    assert len(steps) == counts["updates"]
    for step in steps:
        assert set(step.plans) == set(step.buyers)
    return tuple(prices), counts, steps


def first_primes(count):
    primes = []
    candidate = 2
    while len(primes) < count:
        if all(candidate % p for p in primes if p * p <= candidate):
            primes.append(candidate)
        candidate += 1
    return primes


def chain(primes, shade):
    """Buyers are a_1, b_1, ..., a_m, b_m, root. Goods are A_1, B_1, ..., A_m, B_m."""
    goods = 2 * len(primes)
    bids = [[Fraction(0)] * goods for _ in range(goods + 1)]
    slopes = [[Fraction(1)] * goods for _ in bids]
    two = Fraction(2)
    for i, prime in enumerate(primes):
        a, b = 2 * i, 2 * i + 1
        bids[a][a] = bids[a][b] = bids[b][b] = two
        bids[b][a] = two - shade
        slopes[a][a] = Fraction(prime)
        if a + 2 < goods:
            bids[b][a + 2] = two
    bids[-1][0] = two
    assert max(sum(b > 0 for b in row) for row in bids) <= 3
    assert max(sum(b > 0 for b in col) for col in zip(*bids)) <= 3
    return bids, slopes


def matching_products(rows, goods, demand, slopes):
    """Enumerate supported matchings of the given rows to the given goods."""
    if not rows:
        yield Fraction(1)
        return
    buyer = min(rows, key=lambda i: (len(goods & demand[i]), i))
    for good in goods & demand[buyer]:
        for suffix in matching_products(rows - {buyer}, goods - {good}, demand, slopes):
            yield slopes[buyer][good] * suffix


def check_minima(step, slopes):
    for omitted, plan in step.plans.items():
        rows = set(step.buyers) - {omitted}
        minimum = min(matching_products(rows, set(step.goods), step.demand, slopes))
        assert auction.matching_product(plan, slopes) == minimum


def check_control(primes):
    m = len(primes)
    root = 2 * m
    bids, slopes = chain(primes, Fraction(0))
    prices, counts, steps = solve_with_steps(bids, slopes, exhaustive=m <= 5)
    assert prices == (Fraction(2),) * root
    assert counts == {"updates": 1}
    step, = steps
    assert step.root == root and step.buyers == tuple(range(root + 1))
    assert step.goods == tuple(range(root)) and step.prices == (Fraction(0),) * root
    assert step.demand == tuple(frozenset(j for j, b in enumerate(row) if b > 0) for row in bids)
    products = list(matching_products(set(range(root)), set(step.goods), step.demand, slopes))
    assert len(products) == len(set(products)) == 2**m
    assert all(auction.matching_product(plan, slopes) == 1 for plan in step.plans.values())
    if m <= 5:
        check_minima(step, slopes)
    print(f"control m={m}: {len(products)} products, every deletion minimum 1, one update")


def chain_prices(primes, delta, first):
    prices = []
    for prime in primes:
        second = min(prime * first, first + delta)
        prices.extend((first, second))
        first = second
    return tuple(prices)


def check_shaded_chain(primes):
    m = len(primes)
    root = 2 * m
    delta = Fraction(1, m + 1)
    bids, slopes = chain(primes, delta)
    prices, counts, steps = solve_with_steps(bids, slopes, exhaustive=m <= 5)
    assert prices == chain_prices(primes, delta, 2 - m * delta)
    assert counts == {"updates": m + 1, "internal": m}
    switches = [delta / ((prime - 1) * prod(primes[:i])) for i, prime in enumerate(primes)]
    for k, (step, first) in enumerate(zip(steps, [Fraction(0), *reversed(switches)])):
        assert step.root == root and step.buyers == tuple(range(root + 1))
        assert step.goods == tuple(range(root))
        assert step.prices == chain_prices(primes, delta, first)
        assert auction.matching_product(step.plans[root], slopes) == prod(primes[:m - k])
        if m <= 5:
            check_minima(step, slopes)
    print(f"shaded m={m}: {m} strict minimum drops in one phase, {m + 1} updates")


def forced_flow_market():
    """Use B3f's three-path example and a degree-one buyer inserted last."""
    n = 4
    allowed = {(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (0, 3), (1, 3), (2, 3), (3, 0)}
    intercept = [[Fraction(0 if (i, j) in allowed else -900) for j in range(n)]
                 for i in range(n)]
    gradient = [[Fraction(0)] * n for _ in range(n)]
    intercept[0][1], gradient[0][1] = Fraction(-14, 3), Fraction(-32 * n, 3)
    intercept[0][2], gradient[0][2] = Fraction(-40, 3), Fraction(-64 * n, 3)
    epsilon = Fraction(1, 64 * n * 900**2)
    bids = [[2 + epsilon * b for b in row] for row in intercept]
    slopes = [[1 + epsilon * c for c in row] for row in gradient]
    bids.append(list(map(Fraction, (2, 0, 0, 0))))
    slopes.append([Fraction(1)] * n)
    return bids, slopes


def demanded_goods(bids, slopes, prices):
    demand = []
    for row, rates in zip(bids, slopes):
        utilities = [b - d * p for b, d, p in zip(row, rates, prices)]
        best = max(0, *utilities)
        demand.append({j for j, u in enumerate(utilities) if u == best})
    return demand


FORCED_BUDGETS = (Fraction(1, 4), Fraction(5, 8), Fraction(1))
FORCED_MATCHINGS = ((3, 1, 2, 0), (1, 3, 2, 0), (2, 1, 3, 0))
FORCED_PRODUCTS = (Fraction(1), Fraction(4859999, 4860000), Fraction(2429999, 2430000))


def check_budget_witnesses(bids, slopes, starts, final, permutations):
    endpoints = starts[1:] + [final]
    for start, end, budget, actual, expected in zip(
            starts, endpoints, FORCED_BUDGETS, permutations, FORCED_MATCHINGS):
        assert sum(start) < budget < sum(end)
        fraction = (budget - sum(start)) / (sum(end) - sum(start))
        witness = [a + fraction * (b - a) for a, b in zip(start, end)]
        demand = demanded_goods(bids, slopes, witness)
        indices = set(range(len(bids)))
        products = list(matching_products(indices, indices, demand, slopes))
        assert all(j in demand[i] for i, j in enumerate(expected))
        assert products == [prod(slopes[i][j] for i, j in enumerate(expected))]
        assert actual == expected


def check_forced_flow():
    bids, slopes = forced_flow_market()
    prices, counts, steps = solve_with_steps(bids, slopes, exhaustive=True)
    assert counts == {"updates": 4, "internal": 2}
    assert steps[0].goods == (0,)
    assert all(step.goods == (0, 1, 2, 3) for step in steps[1:])
    assert all(step.root == 4 for step in steps)
    assert tuple(sum(step.prices) for step in steps[1:]) == tuple(
        Fraction(i, 230400) for i in (1, 100801, 187201))
    assert tuple(auction.matching_product(step.plans[4], slopes)
                 for step in steps[1:]) == FORCED_PRODUCTS
    assert prices == (Fraction(2),) + (Fraction(460799, 230400),) * 3
    for step in steps:
        check_minima(step, slopes)
    check_budget_witnesses(bids[:4], slopes[:4], [step.prices for step in steps[1:]],
                           prices, [tuple(step.plans[4][i] for i in range(4)) for step in steps[1:]])
    print("B3f four-type transfer: four updates, two internal, three forced products in one phase")


def split_forced_flow(bids, slopes):
    """Apply the degree-three path splits to the complete, balanced core."""
    n = len(bids) - 1
    first_private = n * n
    goods = n * (2 * n - 1)
    expanded_bids = [[Fraction(0)] * goods for _ in range(goods + 1)]
    expanded_slopes = [[Fraction(1)] * goods for _ in expanded_bids]
    private_bid = Fraction(4)
    for i in range(n):
        for j in range(n):
            clone, port = n * i + j, n * j + i
            expanded_bids[clone][port] = bids[i][j]
            expanded_slopes[clone][port] = slopes[i][j]
            if j + 1 < n:
                private = first_private + (n - 1) * i + j
                expanded_bids[clone][private] = expanded_bids[clone + 1][private] = private_bid
            if i + 1 < n:
                guard = first_private + (n - 1) * j + i
                expanded_bids[guard][port] = expanded_bids[guard][port + 1] = private_bid
    expanded_bids[-1][0] = bids[-1][0]
    return expanded_bids, expanded_slopes


def port_maxima(prices, n):
    return tuple(max(prices[n * j:n * (j + 1)]) for j in range(n))


def check_split_forced_flow():
    bids, slopes = forced_flow_market()
    n = len(bids) - 1
    expanded_bids, expanded_slopes = split_forced_flow(bids, slopes)
    assert max(sum(b > 0 for b in row) for row in expanded_bids) == 3
    assert max(sum(b > 0 for b in col) for col in zip(*expanded_bids)) == 3
    prices, counts, steps = solve_with_steps(expanded_bids, expanded_slopes, exhaustive=False)
    assert counts == {"updates": 10, "internal": 2}
    root = len(prices)
    final_insertion = [step for step in steps if step.root == root]
    assert [len(step.goods) for step in final_insertion] == [7, 25, 26, 28, 28, 28]
    full_phase = final_insertion[-3:]
    projected = [port_maxima(step.prices, n) for step in full_phase]
    projected_final = port_maxima(prices, n)
    assert projected_final == (Fraction(2),) + (Fraction(460799, 230400),) * 3
    assert tuple(sum(p) for p in projected) == (
        Fraction(143, 31104000), Fraction(100801, 230400), Fraction(187201, 230400))
    assert tuple(auction.matching_product(step.plans[root], expanded_slopes)
                 for step in full_phase) == FORCED_PRODUCTS
    for step in steps:
        check_minima(step, expanded_slopes)
    permutations = []
    expanded_endpoints = [step.prices for step in full_phase[1:]] + [prices]
    for step, end in zip(full_phase, expanded_endpoints):
        external = {clone // n: port for clone, port in step.plans[root].items()
                    if clone < n * n and port < n * n}
        assert len(external) == n
        ports = sorted(external.values())
        assert tuple(p // n for p in ports) == tuple(range(n))
        # The same maximizing port at both ends makes each projected coordinate affine.
        for vector in (step.prices, end):
            assert tuple(vector[p] for p in ports) == port_maxima(vector, n)
        permutations.append(tuple(external[i] // n for i in range(n)))
    check_budget_witnesses(bids[:n], slopes[:n], projected, projected_final, permutations)
    print("B3f degree-three transfer: 28 goods, ten updates, two internal, three forced products")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to keep the exact checks enabled.")
    for size in (1, 2, 3, 5, 8, 10):
        primes = first_primes(size)
        check_control(primes)
        check_shaded_chain(primes)
    check_forced_flow()
    check_split_forced_flow()
