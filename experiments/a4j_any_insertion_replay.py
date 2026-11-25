"""Check the forced deletion products under different buyer insertion orders."""

from itertools import permutations
from random import Random

import a4j_unit_prices as auction
from a4j_deletion_product_replay import (
    FORCED_BUDGETS,
    FORCED_PRODUCTS,
    demanded_goods,
    forced_flow_market,
    matching_products,
    port_maxima,
    solve_with_steps,
    split_forced_flow,
)


def check_order(bids, slopes, order, project):
    # Permute the rows instead of changing the solver's insertion rules.
    ordered_bids = [bids[i] for i in order]
    ordered_slopes = [slopes[i] for i in order]
    prices, _, steps = solve_with_steps(ordered_bids, ordered_slopes, exhaustive=False)
    goods = set(range(len(prices)))
    last_row = len(order) - 1
    distinguished = len(bids) - 1
    omitted = order.index(distinguished)
    core = set(range(len(order))) - {omitted}
    endpoints = [step.prices for step in steps[1:]] + [prices]
    final_steps = [(step, end) for step, end in zip(steps, endpoints) if step.root == last_row]
    assert sum(project(final_steps[0][0].prices)) < FORCED_BUDGETS[0]
    assert sum(project(prices)) > FORCED_BUDGETS[-1]

    for budget, expected in zip(FORCED_BUDGETS, FORCED_PRODUCTS):
        step, end = next(
            (step, end) for step, end in final_steps
            if sum(project(step.prices)) < budget < sum(project(end))
        )
        assert set(step.goods) == goods
        plan = step.plans[omitted]
        assert auction.matching_product(plan, ordered_slopes) == expected

        # The selected external ports maximize their blocks at both endpoints,
        # so the projected budget is affine along this step.
        start_budget, end_budget = sum(project(step.prices)), sum(project(end))
        ratio = (budget - start_budget) / (end_budget - start_budget)
        witness = tuple(a + ratio * (b - a) for a, b in zip(step.prices, end))
        assert sum(project(witness)) == budget
        demand = demanded_goods(ordered_bids, ordered_slopes, witness)
        assert all(j in demand[i] for i, j in plan.items())
        assert set(matching_products(core, goods, demand, ordered_slopes)) == {expected}


def main():
    bids, slopes = forced_flow_market()
    for order in permutations(range(len(bids))):
        check_order(bids, slopes, order, tuple)
    print("All 120 unsplit insertion orders: three forced products in the final insertion.")

    n = len(bids) - 1
    bids, slopes = split_forced_flow(bids, slopes)
    random = Random(20261125)
    for last in range(len(bids)):
        order = [i for i in range(len(bids)) if i != last]
        random.shuffle(order)
        check_order(bids, slopes, order + [last], lambda prices: port_maxima(prices, n))
    print("All 29 split choices of last buyer, one order each: 87 exact witness checks.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to retain exact assertions.")
    main()
