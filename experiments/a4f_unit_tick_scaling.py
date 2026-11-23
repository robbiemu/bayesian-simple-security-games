"""Check every unit tick and price bracket against the exact A4j solver."""

from collections import deque
from fractions import Fraction as F
from itertools import product
from math import prod
from random import Random
from a4j_unit_prices import check_certificate, solve


def price_error_bound(bids, slopes):
    n = len(bids[0])
    row_spreads = []
    for bs, ds in zip(bids, slopes):
        active = [d for b, d in zip(bs, ds) if b > 0]
        row_spreads.append(max(active) / min(active) if active else F(1))
    return (n + 1) * prod(sorted(row_spreads, reverse=True)[:n], start=F(1))


def run_phase(bids, slopes, floors, delta, c, prices_star, template_matching=None):
    k, n = len(bids), len(bids[0])
    assert all(l <= p for l, p in zip(floors, prices_star))
    prices = list(floors)
    owners = {}
    jobs = deque(range(k))
    step_counts = [0] * n
    while jobs:
        i = jobs.popleft()
        values = [b - d * p for b, d, p in zip(bids[i], slopes[i], prices)]
        j = max(range(n), key=values.__getitem__)
        if values[j] <= 0:
            continue
        prices[j] += delta
        step_counts[j] += 1
        assert prices[j] <= prices_star[j] + c * delta
        if j in owners:
            jobs.append(owners[j])
        owners[j] = i
    assert all(abs(q - p) <= c * delta for p, q in zip(prices_star, prices))
    assignment = {buyer: good for good, buyer in owners.items()}
    if template_matching is not None:
        for i in range(k):
            values = [b - d * p for b, d, p in zip(bids[i], slopes[i], prices)]
            best = max([0] + values)
            if i in assignment:
                j = assignment[i]
                assert best - values[j] <= slopes[i][j] * delta
            else:
                assert best == 0
            jstar = template_matching[i]
            support_value = 0 if jstar < 0 else values[jstar]
            assert best - support_value <= 2 * max(slopes[i]) * c * delta
        assert set(j for j, q in enumerate(prices) if q > c * delta) <= set(template_matching.values())
    return prices, step_counts


def replay(bids, slopes, phases):
    prices_star, assignment_star, _ = solve(bids, slopes)
    check_certificate(bids, slopes, prices_star, assignment_star, exhaustive=True)
    n = len(bids[0])
    c = price_error_bound(bids, slopes)
    h = max([F(1)] + [b / d for bs, ds in zip(bids, slopes) for b, d in zip(bs, ds)])
    delta = F(1)
    while delta < h:
        delta *= 2
    floors = [F(0)] * n
    total = 0
    worst = F(0)
    for t in range(phases):
        q, counts = run_phase(bids, slopes, floors, delta, c, prices_star, assignment_star)
        if t:
            assert max(counts) <= 5 * c
        else:
            assert max(counts) <= 1 + c
        total += sum(counts)
        worst = max([worst] + [abs(a-b)/delta for a, b in zip(q, prices_star)])
        floors = [max(F(0), p - c * delta) for p in q]
        delta /= 2
    return total, worst


def obstruction(m):
    n = 2*m+1
    bids = [[F(-1)]*n for _ in range(2*m+2)]
    slopes = [[F(1)]*n for _ in bids]
    bids[0][0] = bids[1][0] = F(1)
    for t in range(m):
        a, b, x, y = 2+2*t, 3+2*t, 1+2*t, 2+2*t
        bids[a][0] = F(1, 4)
        for i in (a,b):
            for j in (x,y):
                bids[i][j] = F(1, 2)
        slopes[a][y] = slopes[b][x] = F(2)
    c = price_error_bound(bids, slopes)
    op = [F(1)] + [F(0)]*(n-1)
    floor = [F(0)]*n
    old_delta=F(1)
    while old_delta >= F(4,c):
        old_delta /= 2
    assert F(2,c) <= old_delta < F(4,c)
    old_q, _ = run_phase(bids, slopes, floor, old_delta, c, op)
    floor = [max(F(0), q - c * old_delta) for q in old_q]
    assert floor[0] == 0
    _, counts = run_phase(bids, slopes, floor, old_delta / 2, c, op)
    assert counts[0] >= c/2
    return str(c), str(old_delta), counts[0]


if __name__ == "__main__":
    rng = Random(122183)
    cases = phases = count_bids = 0
    worst = F(0)
    for k, n in product(range(1,6), range(1,5)):
        for _ in range(12):
            bids = [[F(rng.randrange(-1,9), rng.randrange(1,4)) for j in range(n)] for i in range(k)]
            slopes = [[F(rng.randrange(4,9), 4) for j in range(n)] for i in range(k)]
            steps, ratio = replay(bids, slopes, 9)
            count_bids += steps
            worst = max(worst, ratio)
            cases += 1
            phases += 9
    print(f"{cases} markets, {phases} phases, {count_bids} bids, max observed price error/mesh {worst}")
    for m in range(1,5):
        print(f"{m} squares: C, old mesh, bids on g", obstruction(m))
