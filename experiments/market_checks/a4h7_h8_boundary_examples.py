"""Check forced-tie and conditional boundary examples at the prices in the research notes."""

from fractions import Fraction as F
from itertools import product


def verify_minimum(price, capacities, mass, offers, allocation):
    n = len(price)
    demand = []
    for row in offers:
        values = [F(b) - F(d) * p for (b, d), p in zip(row, price)] + [F(0)]
        demand.append({j for j, v in enumerate(values) if v == max(values)})
    assert all(sum(row) == m for row, m in zip(allocation, mass))
    assert all(
        x == 0 or j in best
        for row, best in zip(allocation, demand)
        for j, x in enumerate(row)
    )
    sold = [sum(row[j] for row in allocation) for j in range(n)]
    assert all(
        0 <= x <= c and (p == 0 or x == c) for x, c, p in zip(sold, capacities, price)
    )
    positive = [j for j, p in enumerate(price) if p > 0]
    for flags in product((False, True), repeat=len(positive)):
        S = {j for j, flag in zip(positive, flags) if flag}
        if S:
            assert sum(m for m, best in zip(mass, demand) if best & S) > sum(
                capacities[j] for j in S
            )
    return demand


g = verify_minimum(
    (3, 3, 0, 0),
    (F(11, 2), F(11, 2), 2, 2),
    (10, 2),
    [[(10, 1), (10, 1), (1, 1), (0, 1)], [(9, 3), (7, 1), (0, 1), (4, 1)]],
    [[F(11, 2), F(9, 2), 0, 0, 0], [0, 1, 0, 1, 0]],
)
assert g == [{0, 1}, {1, 3}]
t = verify_minimum(
    (0, 1), (1, 1), (1, 1), [[(4, 1), (5, 1)], [(4, 1), (7, 2)]], [[1, 0, 0], [0, 1, 0]]
)
assert t == [{0, 1}, {1}]
for k in range(1, 10):
    weights = [2**i for i in range(k)]
    M = sum(weights)
    loads = {
        sum(w for w, b in zip(weights, bits) if b) for bits in product((0, 1), repeat=k)
    }
    assert len(loads) == 2**k and loads == set(range(M + 1))
    for local in loads:
        compatible = {
            external
            for external in loads
            if local + external == M and (M - local) + (M - external) == M
        }
        assert compatible == {M - local}
print(
    "Verified both forced-tie examples and all boundary complements for k = 1 through 9."
)
