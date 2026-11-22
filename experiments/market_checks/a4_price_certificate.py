"""Check projected Hall cuts at three witness budgets and certify two fractional examples."""

from fractions import Fraction as F
from itertools import combinations, permutations

n = 4
epsilon = F(1, 207360000)
goods = set(range(n))
permitted_zero = {(0, 3), (1, 3), (2, 3), (3, 0), (0, 0), (1, 1), (2, 2)}
linear_weights = {(0, 1): (-F(14, 3), F(128, 3)), (0, 2): (-F(40, 3), F(256, 3))}
intercepts = {}
slopes = {}
for buyer in goods:
    for good in goods:
        base, slope = linear_weights.get(
            (buyer, good), (0, 0) if (buyer, good) in permitted_zero else (-900, 0)
        )
        intercepts[buyer, good] = 2 + epsilon * base
        slopes[buyer, good] = 1 - epsilon * slope

subsets = [
    set(s) for count in range(1, n + 1) for s in combinations(sorted(goods), count)
]
for budget, expected in [
    (F(1, 4), (3, 1, 2, 0)),
    (F(5, 8), (1, 3, 2, 0)),
    (F(1), (2, 1, 3, 0)),
]:
    price = budget / n
    singleton = {
        i: {j: intercepts[i, j] - slopes[i, j] * price for j in goods} for i in goods
    }
    core_demand = {
        i: {j for j in goods if singleton[i][j] == max(singleton[i].values())}
        for i in goods
    }
    assignments = [
        perm
        for perm in permutations(sorted(goods))
        if all(perm[i] in core_demand[i] for i in goods)
    ]
    assert assignments == [expected], (budget, assignments)

    # Discount only strictly inferior trades, keeping the projected good prices unchanged.
    charges = {}
    demand = {}
    for i in goods:
        for copy in range(2):
            name = (i, copy)
            charges[name] = {}
            utilities = {}
            for j in goods:
                gap = max(singleton[i].values()) - singleton[i][j]
                discount = min(price / 4, gap / (2 * slopes[i, j]))
                charges[name][j] = price - discount
                utilities[j] = intercepts[i, j] - slopes[i, j] * charges[name][j]
            demand[name] = {j for j in goods if utilities[j] == max(utilities.values())}
    charges["extra"] = {j: price / 2 for j in goods}
    demand["extra"] = goods
    assert all(max(bids[j] for bids in charges.values()) == price for j in goods)
    for subset in subsets:
        contributing_buyers = sum(
            any(j in demand[name] and bids[j] == price for j in subset)
            for name, bids in charges.items()
        )
        assert contributing_buyers >= 2 * len(subset)

    print(
        f"Budget {budget}: unique assignment {expected}, all {len(subsets)} projected Hall cuts checked"
    )

# Positive price p_A=1/2 gives the first buyer a tie with her outside option.
# The second buyer uses good B at its reserve. Good A's capacity is 2/3.
capacity_a = F(2, 3)
for mass_a, expected_minimum in [(capacity_a, False), (F(1), True)]:
    flow = {
        "buyer A": {"good A": capacity_a, "outside": mass_a - capacity_a},
        "buyer B": {"good B": F(1, 3)},
    }
    arcs = {"good A": {"buyer A"}, "good B": {"buyer B"}}
    arcs.update(
        {i: {j for j, amount in row.items() if amount > 0} for i, row in flow.items()}
    )
    reached = {"good B", "outside"}
    while True:
        expanded = reached | {start for start, ends in arcs.items() if ends & reached}
        if reached == expanded:
            break
        reached = expanded
    assert ("good A" in reached) == (mass_a > capacity_a) == expected_minimum

print("Weighted verifier agrees with both exact fractional examples.")
