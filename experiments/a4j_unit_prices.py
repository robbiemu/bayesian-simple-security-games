"""Exact unit-market ascending auction and a small independent certificate check.

Input JSON has matrices "bids" and "slopes" in buyer insertion order, and may
specify vectors "reserves" and "outside_utilities". Bids are intercepts at price
zero. Give each rational as an integer or a string such as "7/10". Prices are
reported in the original units. Assignments are zero-based, with -1 for outside.

The default finds minimum-product matchings by shortest augmenting paths using
exact fractions. Use --brute to cross-check small instances by enumeration.
"""

import argparse
import json
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import prod
from random import Random
from sys import stdin


def matching_product(matching, slopes):
    return prod((slopes[i][g] for i, g in matching.items()), start=Fraction(1))


def brute_minimum(rows, goods, demand, slopes):
    candidates = (
        dict(zip(rows, perm)) for perm in permutations(goods)
        if all(g in demand[i] for i, g in zip(rows, perm))
    )
    return min(candidates, key=lambda match: matching_product(match, slopes))


def smallest_product_matching(rows, goods, demand, slopes):
    """Successive shortest augmentations with a layered multiplicative Bellman-Ford."""
    matching = {}
    for _ in rows:
        occupied = set(matching.values())
        arcs = []
        for i in rows:
            for g in goods:
                if g not in demand[i]:
                    continue
                left, right = (0, i), (1, g)
                rate = slopes[i][g]
                if matching.get(i) == g:
                    arcs.append((right, left, 1 / rate))
                else:
                    arcs.append((left, right, rate))
        # A minimum-product current matching has no improving residual cycle.
        # Thus a shortest augmenting path with minimum hops is simple.
        labels = {
            (0, i): (Fraction(1), 0, ((0, i),)) for i in rows if i not in matching
        }
        for _ in range(len(rows) + len(goods) - 1):
            next_labels = dict(labels)
            for tail, head, rate in arcs:
                if tail not in labels:
                    continue
                value, hops, path = labels[tail]
                candidate = (value * rate, hops + 1, path + (head,))
                if head not in next_labels or candidate < next_labels[head]:
                    next_labels[head] = candidate
            if labels == next_labels:
                break
            labels = next_labels
        _, _, path = min(labels[(1, g)] for g in goods
                         if g not in occupied and (1, g) in labels)
        assert len(path) == len(set(path))
        for k in range(0, len(path) - 1, 2):
            matching[path[k][1]] = path[k + 1][1]
    return matching


def demands_at(bids, slopes, prices):
    offers = [[b - d * p for b, d, p in zip(row, ds, prices)]
              for row, ds in zip(bids, slopes)]
    best = [max([Fraction(0)] + row) for row in offers]
    demand = [{g for g, offer in enumerate(row) if offer == best[i]}
              | ({-1} if best[i] == 0 else set()) for i, row in enumerate(offers)]
    return offers, best, demand


def augment_or_reach(root, assigned, demand):
    """Either assign the root on a demand path or return the reached buyers and goods."""
    owner = {g: i for i, g in assigned.items() if g >= 0}
    parent = {}
    reached = {root}
    queue = [root]
    for i in queue:
        for g in sorted(demand[i]):
            if g in parent:
                continue
            parent[g] = i
            if g not in owner:
                while True:
                    buyer = parent[g]
                    old = assigned.get(buyer)
                    assigned[buyer] = g
                    if buyer == root:
                        return None
                    g = old
            other = owner[g]
            if other not in reached:
                reached.add(other)
                queue.append(other)
    return sorted(reached), sorted(parent)


def rates_from_matchings(plans, buyers, goods, demand, slopes):
    support = {(i, g) for plan in plans.values() for i, g in plan.items()}
    speeds = {goods[0]: Fraction(1)}
    utility_loss = {}
    # Each component of the average planning matrix balances s/t unit rows
    # against unit columns, with gcd(s,t)=1. Consequently the support is connected.
    while len(speeds) + len(utility_loss) < len(buyers) + len(goods):
        old_size = len(speeds) + len(utility_loss)
        for i, g in support:
            if g in speeds:
                utility_loss[i] = slopes[i][g] * speeds[g]
            if i in utility_loss:
                speeds[g] = utility_loss[i] / slopes[i][g]
        assert len(speeds) + len(utility_loss) > old_size
    for i in buyers:
        assert utility_loss[i] == min(slopes[i][g] * speeds[g] for g in demand[i])
    return speeds, utility_loss


def solve(bids, slopes, matching_solver=smallest_product_matching):
    ng = len(bids[0]) if bids else 0
    if len(slopes) != len(bids) or any(len(v) != ng for v in bids + slopes):
        raise ValueError("The two matrices must be rectangular and have identical shape")
    if any(d <= 0 for row in slopes for d in row):
        raise ValueError("All slopes must be positive")
    prices = [Fraction(0)] * ng
    assigned = {}
    stats = Counter()
    for root in range(len(bids)):
        phase = None
        while True:
            offers, best, demand = demands_at(bids, slopes, prices)
            result = augment_or_reach(root, assigned, demand)
            if result is None:
                break
            buyers, goods = result
            assert len(buyers) == len(goods) + 1 and -1 not in goods
            plans = {}
            values = {}
            for r in buyers:
                others = [i for i in buyers if i != r]
                plans[r] = matching_solver(others, goods, demand, slopes)
                values[r] = matching_product(plans[r], slopes)
            if phase is not None:
                old_buyers, old_goods, old_values = phase
                assert set(old_buyers) <= set(buyers) and set(old_goods) <= set(goods)
                if old_goods == goods:
                    assert all(values[r] <= old_values[r] for r in buyers)
                    assert any(values[r] < old_values[r] for r in buyers)
                    stats["internal"] += 1
            phase = buyers, goods, values
            assigned.update(plans[root])
            speeds, losses = rates_from_matchings(plans, buyers, goods, demand, slopes)
            candidates = [best[i] / losses[i] for i in buyers]
            for i in buyers:
                for g in range(ng):
                    gap = best[i] - offers[i][g]
                    catchup = losses[i] - slopes[i][g] * speeds.get(g, 0)
                    if bids[i][g] > 0 and gap > 0 and catchup > 0:
                        candidates.append(gap / catchup)
            step = min(candidates)
            assert step > 0
            for g in goods:
                prices[g] += step * speeds[g]
            stats["updates"] += 1
    return prices, assigned, stats


def check_certificate(bids, slopes, prices, assigned, exhaustive=False):
    """Check the matching and strict Hall independently of the price trajectory."""
    assert all(p >= 0 for p in prices)
    _, _, demand = demands_at(bids, slopes, prices)
    assert set(assigned) == set(range(len(bids)))
    assert all(g in demand[i] for i, g in assigned.items())
    real = [g for g in assigned.values() if g >= 0]
    assert len(set(real)) == len(real)
    positive = {g for g, p in enumerate(prices) if p > 0}
    assert positive <= set(real)
    reached = {-1} | {g for g, p in enumerate(prices) if p == 0}
    while True:
        more = set(reached)
        for i, assigned_good in assigned.items():
            if assigned_good in reached:
                more.update(demand[i])
        if more == reached:
            break
        reached = more
    assert positive <= reached
    if exhaustive:
        for size in range(1, len(positive) + 1):
            for subset in combinations(positive, size):
                assert sum(bool(set(subset) & row) for row in demand) > size


def exact_rational(value):
    if type(value) not in (int, str):
        raise ValueError("Give rational entries as integers or strings, not JSON decimals")
    return Fraction(value)


def solve_input(data, matching_solver):
    bids, slopes = (
        [[exact_rational(value) for value in row] for row in data[key]]
        for key in ("bids", "slopes")
    )
    number_of_goods = len(bids[0]) if bids else len(data.get("reserves", []))
    reserves = [exact_rational(value) for value in data.get("reserves", [0] * number_of_goods)]
    outside = [exact_rational(value) for value in data.get("outside_utilities", [0] * len(bids))]
    if len(reserves) != number_of_goods or len(outside) != len(bids):
        raise ValueError("Reserve and outside vectors must match the input dimensions")
    if len(slopes) != len(bids) or any(len(row) != number_of_goods for row in bids + slopes):
        raise ValueError("The two matrices must be rectangular and have identical shape")
    if not bids:
        return {"prices": [str(price) for price in reserves], "assignments": [],
                "updates": 0, "internal": 0}

    normalized = [
        [b - d * reserve - value for b, d, reserve in zip(row, ds, reserves)]
        for row, ds, value in zip(bids, slopes, outside)
    ]
    result, assignment, stats = solve(normalized, slopes, matching_solver=matching_solver)
    check_certificate(normalized, slopes, result, assignment)
    return {
        "prices": [str(price + reserve) for price, reserve in zip(result, reserves)],
        "assignments": [assignment[i] for i in range(len(bids))],
        "updates": stats["updates"],
        "internal": stats["internal"],
    }


def benchmark(cases):
    bids = [[Fraction(2), Fraction(2)], [Fraction(1), Fraction(2)],
            [Fraction(2, 5), Fraction(0)]]
    slopes = [[Fraction(2), Fraction(1)], [Fraction(1), Fraction(2)],
              [Fraction(1), Fraction(1)]]
    q, assignment, counts = solve(bids, slopes)
    assert q == [Fraction(2, 5), Fraction(7, 10)]
    assert counts == {"updates": 2, "internal": 1}
    check_certificate(bids, slopes, q, assignment, exhaustive=True)
    print("Two-good example", q, counts)
    rng = Random(67103)
    totals = Counter()
    largest = 0
    for k in range(cases):
        nrows, ng = rng.randrange(1, 9), rng.randrange(1, 6)
        bids = [[Fraction(rng.randrange(-1, 17), rng.randrange(1, 4))
                 for _ in range(ng)] for _ in range(nrows)]
        slopes = [[Fraction(rng.randrange(1, 9), rng.randrange(1, 5))
                   for _ in range(ng)] for _ in range(nrows)]
        if k % 3 == 1:
            for i in range(nrows):
                viable = set(rng.sample(range(ng), min(2, ng)))
                for g in range(ng):
                    if g not in viable:
                        bids[i][g] = Fraction(0)
        if k % 3 == 2:
            for g in range(ng):
                viable = set(rng.sample(range(nrows), min(2, nrows)))
                for i in range(nrows):
                    if i not in viable:
                        bids[i][g] = Fraction(0)
        q, assignment, counts = solve(bids, slopes)
        brute_q, _, brute_stats = solve(bids, slopes, matching_solver=brute_minimum)
        assert q == brute_q
        if k % 3 == 2:
            assert counts["internal"] == 0
        check_certificate(bids, slopes, q, assignment, exhaustive=True)
        totals.update(counts)
        largest = max(largest, counts["updates"])
    print(f"Checked {cases} rational markets against exhaustive matching costs and Hall",
          dict(totals), f"maximum updates {largest}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", type=int, metavar="CASES")
    parser.add_argument("--brute", action="store_true")
    args = parser.parse_args()
    if args.self_test is not None:
        benchmark(args.self_test)
    else:
        solver = brute_minimum if args.brute else smallest_product_matching
        try:
            result = solve_input(json.load(stdin), solver)
        except (KeyError, ValueError, TypeError, ZeroDivisionError) as error:
            parser.error(str(error))
        print(json.dumps(result))
