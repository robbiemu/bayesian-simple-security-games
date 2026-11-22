"""Check the endpoint tie, reserve-query minima, and budget-one allocation."""

from fractions import Fraction as Q

from a4h9_hybrid_examples import best_options
from clearing_replay_checks import check_clearance


# The offers subtract the original outside payoffs (-5, -2, 0).
OFFERS = {
    1: {"A": (6, 8), "B": (5, 5)},
    2: {"A": (2, 2), "B": (4, 5)},
    3: {"A": (1, 1), "B": (1, 1)},
}
MASSES = {1: Q(3, 8), 2: Q(3, 8), 3: Q(1, 4)}
CAPACITIES = {"A": Q(1, 2), "B": Q(1, 2)}


def check_extreme_allocations():
    for price, first, second in ((0, "A", "B"), (1, "B", "A")):
        prices = {"A": price, "B": price}
        assert best_options(OFFERS[1], prices)[1] - {None} == {first}
        assert best_options(OFFERS[2], prices)[1] - {None} == {second}
        assert best_options(OFFERS[3], prices)[1] - {None} == {"A", "B"}
        assert sum(MASSES.values()) == sum(CAPACITIES.values())
        allocation = {
            1: {first: MASSES[1]},
            2: {second: MASSES[2]},
            3: {"A": Q(1, 8), "B": Q(1, 8)},
        }
        check_clearance(OFFERS, MASSES, CAPACITIES, prices, allocation)


def check_reserve_query(t, allocation):
    # Under p_A >= t, a lower p_B forces both large rows into B.
    strict_b_cutoffs = []
    for buyer in (1, 2):
        a, a_slope = OFFERS[buyer]["A"]
        b, b_slope = OFFERS[buyer]["B"]
        strict_b_cutoffs.append(min(Q(b, b_slope), (b - a + a_slope * t) / b_slope))
    b_price = min(strict_b_cutoffs)
    assert b_price == (8 * t - 1) / 5 > t
    assert MASSES[1] + MASSES[2] > CAPACITIES["B"]
    prices = {"A": t, "B": b_price}
    assert best_options(OFFERS[3], prices)[1] == {"A"}
    assert allocation[3] == {"A": MASSES[3]}
    check_clearance(OFFERS, MASSES, CAPACITIES, prices, allocation)
    return prices


if __name__ == "__main__":
    check_extreme_allocations()
    mid = check_reserve_query(
        Q(1, 2), {1: {"B": Q(3, 8)}, 2: {"A": Q(1, 4), "B": Q(1, 8)}, 3: {"A": Q(1, 4)}}
    )
    assert mid == {"A": Q(1, 2), "B": Q(3, 5)}

    at_budget_one = check_reserve_query(
        Q(6, 13), {1: {"A": Q(1, 4), "B": Q(1, 8)}, 2: {"B": Q(3, 8)}, 3: {"A": Q(1, 4)}}
    )
    assert at_budget_one == {"A": Q(6, 13), "B": Q(7, 13)}
    assert sum(at_budget_one.values()) == 1
    print("Checked the endpoint ties and both reserve minima. At budget one, row 3 sends all 1/4 to A.")
