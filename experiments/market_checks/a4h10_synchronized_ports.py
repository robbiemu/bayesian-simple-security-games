"""Check the signed-load counterexample and a three-group market."""

from fractions import Fraction as Q

from a4h9_hybrid_examples import best_options, check_strict_hall
from clearing_replay_checks import check_clearance


def check_aggregate_load_counterexample():
    one_row = {"first": (6, 1), "second": (6, 2)}
    offers = {"A": one_row, "B": one_row}
    masses = {"A": 1, "B": 1}
    caps = {"first": 1, "second": 1}
    at_zero = {"first": 0, "second": 0}
    at_one = {"first": 1, "second": 1}

    check_clearance(offers, masses, caps, at_zero, {"A": {"first": 1}, "B": {"second": 1}})
    assert best_options(one_row, at_zero)[1] == {"first", "second"}
    assert best_options(one_row, at_one)[1] == {"first"}
    assert sum(masses.values()) == sum(caps.values()) > caps["first"]


def check_grouped_core():
    target_prices = [Q(1), Q(3, 2), Q(2)]
    group_count = len(target_prices)
    individual_share = Q(1, 4 * group_count)
    offers, masses, capacities, prices, flow = {}, {}, {}, {}, {}

    for index, price in enumerate(target_prices):
        home, private, connector = ("h", index), ("k", index), ("s", index)
        prices.update({home: price, private: 0, connector: 0})
        capacities.update({home: Q(9, 4), private: 1, connector: individual_share})
        home_buyer, private_buyer, connector_buyer = (
            ("home", index), ("private", index), ("connector", index)
        )
        masses.update({home_buyer: 2, private_buyer: 1, connector_buyer: individual_share})
        offers[home_buyer] = {
            home: (9 + price, 1),
            private: (9, 2),
            **{("s", other): (9, 1) for other in range(group_count)},
        }
        offers[private_buyer] = {home: (2 + price, 1), private: (1, 1)}
        offers[connector_buyer] = {
            ("h", other): (2 + target, 1) for other, target in enumerate(target_prices)
        }
        flow[home_buyer] = {home: Q(5, 4) - individual_share, private: Q(3, 4) + individual_share}
        flow[private_buyer] = {home: 1}
        flow[connector_buyer] = {
            ("h", other): individual_share / group_count for other in range(group_count)
        }

    check_clearance(offers, masses, capacities, prices, flow)
    check_strict_hall(offers, masses, capacities, prices)
    connector_capacity = sum(cap for good, cap in capacities.items() if good[0] == "s")
    for index, price in enumerate(target_prices):
        row = ("home", index)
        utility, _ = best_options(offers[row], prices)
        assert utility == 9
        assert capacities["k", index] + connector_capacity < masses[row]
        assert utility + prices["h", index] == 9 + price


if __name__ == "__main__":
    check_aggregate_load_counterexample()
    check_grouped_core()
    print("Checked the aggregate-load counterexample and the three-group clearing witness.")
