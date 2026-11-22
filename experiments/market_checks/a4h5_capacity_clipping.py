"""Exhaust the small clipping cases and test the two Hall cuts at their conditional minima."""

from itertools import product

cases = 0
for bounds in product(range(5), repeat=3):
    for local_max in range(5):
        total_upper = sum(bounds) + local_max
        for c in range(total_upper + 3):
            deficit = max(total_upper - c, 0)
            for y in product(*(range(u + 1) for u in bounds)):
                clipped = tuple(
                    max(upper - deficit, min(load, c + 1), 0)
                    for load, upper in zip(y, bounds)
                )
                assert all(load <= upper for load, upper in zip(clipped, bounds))
                for a in range(local_max + 1):
                    assert (a + sum(y) <= c) == (a + sum(clipped) <= c), (
                        bounds,
                        local_max,
                        c,
                        y,
                        a,
                    )
                    cases += 1
            for upper in bounds:
                values = {
                    max(upper - deficit, min(load, c + 1), 0)
                    for load in range(upper + 1)
                }
                assert len(values) <= 2 + min(c, deficit, upper)


def loads(t):
    prices = [t, min(t, 1), min(t, 3)]

    def best(bids):
        utilities = [bid - price for bid, price in zip(bids, prices)] + [0]
        high = max(utilities)
        return {i for i, value in enumerate(utilities) if value == high}

    demand = [(best([1, 1, 0]), 4), (best([3, 0, 3]), 3)]
    cuts = [{good for good in range(3) if mask & (1 << good)} for mask in range(8)]
    return [
        sum(mass for best_set, mass in demand if best_set <= cut) - len(cut)
        for cut in cuts
    ]


assert loads(0) == [0, -1, -1, 2, -1, 1, -2, 4]
assert loads(1) == [0, -1, -1, -2, -1, 1, -2, 0]
print(
    f"Clipping preserved every capacity comparison in {cases:,} exhaustive small cases. Hall counterexample verified at both exact conditional minima."
)
