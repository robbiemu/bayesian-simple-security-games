"""Replay the buyer proxy fixture and the 240 seeded rational lift checks."""

from fractions import Fraction as Q
from random import Random

from a4h9_hybrid_examples import best_options, check_strict_hall
from clearing_replay_checks import check_clearance


def check_proxy_lift(offers, masses, capacities, prices, allocation):
    check_clearance(offers, masses, capacities, prices, allocation)
    new_offers, new_masses, new_flow = {}, {}, {}
    new_capacities = capacities.copy()
    new_prices = prices.copy()

    for buyer, mass in masses.items():
        row = offers[buyer]
        assert all(bid > 0 for bid, _ in row.values())
        proxy_good = ("proxy", buyer)
        utility, _ = best_options(row, prices)
        ceiling = 1 + max([0] + [bid for bid, _ in row.values()])
        new_prices[proxy_good] = ceiling - utility
        new_capacities[proxy_good] = (2 * len(row) + 1) * mass

        guard = ("guard", buyer)
        outside = allocation[buyer].get(None, 0)
        new_offers[guard] = {proxy_good: (ceiling, 1)}
        new_masses[guard] = 2 * mass
        new_flow[guard] = {proxy_good: 2 * mass - outside, None: outside}

        for good, (bid, slope) in row.items():
            edge_buyer = ("edge", buyer, good)
            amount = allocation[buyer].get(good, 0)
            new_offers[edge_buyer] = {proxy_good: (1 + ceiling, 1), good: (1 + bid, slope)}
            new_masses[edge_buyer] = 2 * mass
            new_flow[edge_buyer] = {proxy_good: 2 * mass - amount, good: amount}

    assert all(new_prices["proxy", buyer] > 0 for buyer in masses)
    check_clearance(new_offers, new_masses, new_capacities, new_prices, new_flow)

    recovered = {}
    for buyer, row in offers.items():
        recovered[buyer] = {good: new_flow["edge", buyer, good][good] for good in row}
        recovered[buyer][None] = new_flow["guard", buyer][None]
        assert {j: x for j, x in recovered[buyer].items() if x} == {
            j: x for j, x in allocation[buyer].items() if x
        }
    check_clearance(offers, masses, capacities, prices, recovered)
    return new_prices, new_flow


def check_displayed_fixture():
    offers = {"row": {"a": (1, 1), "b": (1, 2)}}
    masses = {"row": 2}
    capacities = {"a": 1, "b": Q(1, 2)}
    prices = {"a": 1, "b": Q(1, 2)}
    flow = {"row": {"a": 1, "b": Q(1, 2), None: Q(1, 2)}}
    check_strict_hall(offers, masses, capacities, prices)
    lifted_prices, lifted_flow = check_proxy_lift(offers, masses, capacities, prices, flow)
    assert lifted_prices["proxy", "row"] == 2
    assert lifted_flow["guard", "row"][None] == Q(1, 2)


def seeded_markets(seed, count):
    rng = Random(seed)
    for _ in range(count):
        goods = list(range(rng.randrange(1, 7)))
        buyers = list(range(rng.randrange(1, 7)))
        prices = {good: Q(rng.randrange(0, 9), 3) for good in goods}
        offers, masses, flow = {}, {}, {}

        for buyer in buyers:
            utility = Q(rng.randrange(0, 7), 4)
            anchor = rng.choice(goods) if utility else None
            row, purchases = {}, {}
            for good in goods:
                slope = Q(rng.randrange(1, 7), rng.randrange(1, 5))
                tight = good == anchor or bool(rng.randrange(2))
                gap = 0 if tight else Q(rng.randrange(1, 6), 3)
                bid = utility + slope * prices[good] - gap
                if bid > 0 and (tight or rng.randrange(2)):
                    row[good] = (bid, slope)
                    if tight:
                        purchases[good] = Q(rng.randrange(1, 5), 5)
            if utility == 0:
                purchases[None] = Q(rng.randrange(1, 7), 4)
            offers[buyer] = row
            flow[buyer] = purchases
            masses[buyer] = sum(purchases.values())

        capacities = {
            good: sum(row.get(good, 0) for row in flow.values())
            + (Q(rng.randrange(0, 4), 4) if prices[good] == 0 else 0)
            for good in goods
        }
        yield offers, masses, capacities, prices, flow


if __name__ == "__main__":
    check_displayed_fixture()
    for market in seeded_markets(seed=96391, count=240):
        check_proxy_lift(*market)
    print("Checked the displayed proxy fixture and 240 seeded rational clearing witnesses (seed 96391).")
