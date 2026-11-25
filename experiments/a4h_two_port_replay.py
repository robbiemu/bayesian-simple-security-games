"""Exact finite checks for raw port-load scaling and projected Hall cuts."""

from fractions import Fraction as F
from itertools import combinations, product

from a4j_unit_prices import check_certificate, demands_at, solve


BIDS = ((20, 20), (20, 24))
SLOPES = ((1, 1), (1, 2))


def subsets(vertices):
    for size in range(len(vertices) + 1):
        for group in combinations(vertices, size):
            yield set(group)


def neighbors(bids, slopes, outside, prices):
    net_bids = [[bid - floor for bid in row] for row, floor in zip(bids, outside)]
    return demands_at(net_bids, slopes, prices)[2]


def trapped(demand, goods):
    return sum(choices <= goods for choices in demand)


def check_scalings_and_midpoint():
    # Isolate one switch at a time. The other buyer has a strict preference.
    cases = (
        ((F(17, 4), F(17, 4)), (F(3, 32), F(2, 32)), (1, 2)),
        ((F(9, 2), F(17, 4)), (F(-3, 32), F(-2, 32)), (1, 1)),
    )
    for center, step, scales in cases:
        before = tuple(p - h for p, h in zip(center, step))
        after = tuple(p + h for p, h in zip(center, step))
        old = neighbors(BIDS, SLOPES, (0, 0), before)
        new = neighbors(BIDS, SLOPES, (0, 0), after)
        change = [sum(j in row for row in old) - sum(j in row for row in new)
                  for j in range(2)]
        assert change == [1, -1]
        assert sum(d * s * (b - a) for d, s, a, b in zip(change, scales, before, after)) == -F(1, 16)

    low, high = (F(25, 8), F(7, 2)), (F(37, 8), F(9, 2))
    center = tuple((a + b) / 2 for a, b in zip(low, high))
    assert neighbors(BIDS, SLOPES, (0, 0), low) == [{0}, {1}]
    assert neighbors(BIDS, SLOPES, (0, 0), high) == [{1}, {0}]
    assert neighbors(BIDS, SLOPES, (0, 0), center) == [{0}, {0}]
    assert center == (F(31, 8), F(4))
    print("Two isolated switches have dot product -1/16 at the tested scales.")
    print("Two clearing quotes have a midpoint overloading good 1:", center)


def check_hall_cut_after_reoptimization():
    # Ports 0 and 1, private good 2, all unit capacities and buyer masses.
    # Buyer 3 only has a viable offer on the private good.
    bids = ((6, 6, 8),) * 3 + ((-100, -100, F(13, 4)),)
    slopes = ((1, 1, 1),) * 4
    outside = (4, 4, 4, 0)

    def at_ports(prices):
        folded = tuple(max(floor, row[0] - prices[0], row[1] - prices[1])
                       for row, floor in zip(bids, outside))
        reduced_bids = [(row[2] - floor,) for row, floor in zip(bids, folded)]
        private, assignment, _ = solve(reduced_bids, [(1,)] * len(bids))
        check_certificate(reduced_bids, [(1,)] * len(bids), private, assignment, exhaustive=True)
        quotes = prices + tuple(private)
        return quotes, neighbors(bids, slopes, outside, quotes)

    trial = (F(1), F(3))
    quotes, demand = at_ports(trial)
    assert quotes == (1, 3, 3)
    assert demand == [{0, 2}, {0, 2}, {0, 2}, {2}]
    assert trapped(demand, {0}) == 0
    assert trapped(demand, {2}) == 1
    assert trapped(demand, {0, 2}) == 4

    # At the trial, fold port 1 into outside and replace port 0 by the
    # aggregate good with price z and trial utility 5 at z=0.
    reduced_bids = ((4, 1),) * 3 + ((F(13, 4), -100),)
    reduced_slopes = ((1, 1),) * 4
    prices, assignment, _ = solve(reduced_bids, reduced_slopes)
    assert tuple(prices) == (4, 1)
    check_certificate(reduced_bids, reduced_slopes, prices, assignment, exhaustive=True)

    # This trial leaves the sign orthant and changes the private best options.
    moved = (F(11, 8), F(5, 2))
    new_quotes, new_demand = at_ports(moved)
    assert new_quotes == moved + (F(27, 8),)
    assert new_demand[-1] == {-1}
    assert trapped(new_demand, {0, 2}) == 3

    eta = F(1, 2)
    grid = [F(i, 4) for i in range(17)]
    tested = 0
    for point in product(grid, repeat=2):
        if point[0] > trial[0] + eta or point[1] < 2:
            continue
        _, demand = at_ports(point)
        assert any(trapped(demand, goods) > len(goods) for goods in subsets(range(3)))
        tested += 1
    clearing_quotes, clearing_demand = at_ports((F(2), F(2)))
    assert clearing_quotes == (2, 2, 4)
    assert all(good in choices for good, choices in enumerate(clearing_demand[:3]))
    assert clearing_demand[-1] == {-1}
    assert all(trapped(clearing_demand, goods) <= len(goods) for goods in subsets(range(3)))
    print(f"Projected Hall cut: {tested} exact quote pairs rejected, including {moved} "
          "after re-solving the private good and changing its demand graph.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to retain exact assertions.")
    check_scalings_and_midpoint()
    check_hall_cut_after_reoptimization()
