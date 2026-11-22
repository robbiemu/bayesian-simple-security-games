"""Replay the A4h9 transient-tie and mixed-boundary examples with exact arithmetic."""

from fractions import Fraction as Q
from itertools import combinations


def best_options(offers, prices):
    values = {good: intercept - slope * prices[good] for good, (intercept, slope) in offers.items()}
    values[None] = 0  # Outside
    utility = max(values.values())
    return utility, {good for good, value in values.items() if value == utility}


def check_clearance(offers, masses, capacities, prices, allocation):
    loads = dict.fromkeys(capacities, Q(0))
    for buyer, row in allocation.items():
        _, best = best_options(offers[buyer], prices)
        assert sum(row.values()) == masses[buyer]
        for good, amount in row.items():
            assert amount >= 0
            if amount > 0:
                assert good in best
                if good is not None:
                    loads[good] += amount
    assert allocation.keys() == masses.keys()
    for good, capacity in capacities.items():
        assert loads[good] <= capacity
        if prices[good] > 0:
            assert loads[good] == capacity


def check_strict_hall(offers, masses, capacities, prices):
    positive = [good for good, price in prices.items() if price > 0]
    demand = {buyer: best_options(row, prices)[1] for buyer, row in offers.items()}
    for size in range(1, len(positive) + 1):
        for subset in combinations(positive, size):
            touching = sum(masses[buyer] for buyer, best in demand.items() if best.intersection(subset))
            assert touching > sum(capacities[good] for good in subset)


def transient_tie():
    offers = {
        "A": {1: (4, 1), 2: (3, 1)},
        "B": {1: (4, 1), 2: (5, 4)},
        "C": {1: (2, 1)},
    }
    masses = {"A": 1, "B": 1, "C": 1}
    first = {1: 1, 2: 0}
    second = {1: Q(5, 3), 2: Q(2, 3)}
    minimum = {1: 2, 2: Q(3, 4)}
    assert best_options(offers["A"], first)[1] == {1, 2}
    assert best_options(offers["B"], second)[1] == {1, 2}
    assert best_options(offers["A"], minimum)[1] == {2}

    original = {1: 1, 2: 1}
    enlarged = {1: Q(5, 4), 2: Q(5, 4)}
    check_clearance(offers, masses, original, minimum, {"A": {2: 1}, "B": {1: 1}, "C": {None: 1}})
    check_strict_hall(offers, masses, original, minimum)

    # On A's line, a merged capacity of 5/2 forces half of C's mass to buy.
    # B has to use alias 1, as does the real purchase of C.
    trial = {1: 2, 2: 1}
    assert best_options(offers["A"], trial) == (2, {1, 2})
    assert best_options(offers["B"], trial) == (2, {1})
    assert best_options(offers["C"], trial) == (0, {1, None})
    real_mass_from_c = sum(enlarged.values()) - masses["A"] - masses["B"]
    must_use_alias_one = masses["B"] + real_mass_from_c
    assert must_use_alias_one == Q(3, 2) > enlarged[1]
    assert minimum[1] - minimum[2] > 1

    # On B's line, the individual capacities clear without any transfer.
    assert minimum[1] == 4 * minimum[2] - 1
    allocation = {"A": {2: 1}, "B": {1: Q(3, 4), 2: Q(1, 4)}, "C": {1: Q(1, 2), None: Q(1, 2)}}
    check_clearance(offers, masses, enlarged, minimum, allocation)
    print("Transient tie and both grouping outcomes verified at exact prices.")


def mixed_ports():
    offers = {
        "A": {"X": (3, 1), "Z": (2, Q(1, 2))},
        "B": {"X": (6, 2), "Y": (2, 1)},
        "C": {"Z": (2, 1)},
    }
    masses = {"A": 1, "B": 1, "C": Q(1, 2)}
    original = {"X": 1, "Y": Q(1, 2), "Z": 1}
    enlarged = {good: capacity + Q(1, 12) for good, capacity in original.items()}
    prices = {"X": 2, "Y": 0, "Z": 2}
    assert best_options(offers["A"], prices) == (1, {"X", "Z"})

    # The shared good X ties a reserve-priced private good Y at quote 2.
    # At any lower quote, X strictly beats Y even when Y is at reserve.
    assert best_options(offers["B"], prices) == (2, {"X", "Y"})
    assert best_options(offers["B"], {**prices, "X": Q(11, 6)})[1] == {"X"}
    good_interval = (masses["B"] - enlarged["Y"], masses["B"])
    assert good_interval == (Q(5, 12), 1)

    # In the transpose, Z is a buyer with mass c_Z and offers
    # 4 - 2 u_A and 2 - u_C. At u_A = 1 it can buy at C's reserve.
    transpose_offers = {"A": (4, 2), "C": (2, 1)}
    assert best_options(transpose_offers, {"A": 1, "C": 0}) == (2, {"A", "C"})
    assert best_options(transpose_offers, {"A": Q(5, 6), "C": 0})[1] == {"A"}
    buyer_interval = (enlarged["Z"] - masses["C"], enlarged["Z"])
    assert buyer_interval == (Q(7, 12), Q(13, 12))

    enlarged_flow = {
        "A": {"X": Q(1, 4), "Z": Q(3, 4)},
        "B": {"X": Q(5, 6), "Y": Q(1, 6)},
        "C": {"Z": Q(1, 3), None: Q(1, 6)},
    }
    assert good_interval[0] < enlarged_flow["B"]["X"] < good_interval[1]
    assert buyer_interval[0] < enlarged_flow["A"]["Z"] < buyer_interval[1]
    check_clearance(offers, masses, enlarged, prices, enlarged_flow)
    original_flow = {
        "A": {"X": Q(1, 4), "Z": Q(3, 4)},
        "B": {"X": Q(3, 4), "Y": Q(1, 4)},
        "C": {"Z": Q(1, 4), None: Q(1, 4)},
    }
    check_clearance(offers, masses, original, prices, original_flow)
    check_strict_hall(offers, masses, original, prices)
    print("Both mixed boundary intervals accept interior loads, and the original capacities clear.")


if __name__ == "__main__":
    transient_tie()
    mixed_ports()
