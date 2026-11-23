"""Check exact primal and lower-bound certificates for the box exclusion LP."""

from fractions import Fraction
from itertools import permutations

from a4j_unit_prices import check_certificate


def assignment_with_owner(size, owner):
    """Return a padded perfect assignment with good zero held by owner."""
    remaining = iter(range(1, size))
    return tuple(0 if i == owner else next(remaining) for i in range(size))


def check_exclusion_lp(intercepts, slopes, forced_buyer, box, mixture, lower_quote):
    # Pad one real good with one outside slot per buyer and a dummy buyer.
    intercepts = tuple(intercepts) + (Fraction(0),)
    slopes = tuple(slopes) + (Fraction(1),)
    size = len(intercepts)
    assignments = tuple(permutations(range(size)))
    forced = [assignment for assignment in assignments if assignment[forced_buyer] == 0]

    plan = [[Fraction(0) for _ in range(size)] for _ in range(size)]
    for owner, weight in mixture:
        for i, j in enumerate(assignment_with_owner(size, owner)):
            plan[i][j] += weight
    assert all(entry >= 0 for row in plan for entry in row)
    assert all(sum(row) == 1 for row in plan)
    assert all(sum(column) == 1 for column in zip(*plan))

    b_x = sum(intercepts[i] * plan[i][0] for i in range(size))
    s_x = sum(slopes[i] * plan[i][0] for i in range(size))
    alpha = [Fraction(0) for _ in range(size)]
    beta = [Fraction(0) for _ in range(size)]
    alpha[forced_buyer] = intercepts[forced_buyer]
    # The only real column has the same slope in X as on the forced edge.
    assert s_x == slopes[forced_buyer]
    allowed_edges = {(i, j) for assignment in forced for i, j in enumerate(assignment)}
    for i, j in allowed_edges:
        for quote in box:
            rhs = intercepts[i] + (s_x - slopes[i]) * quote if j == 0 else 0
            assert alpha[i] + beta[j] >= rhs
    objective = sum(alpha) + sum(beta) - b_x

    def value(assignment, price):
        owner = assignment.index(0)
        return intercepts[owner] - slopes[owner] * price

    # At this quote the full assignment optimum upper-bounds every fractional X.
    assert box[0] <= lower_quote <= box[1]
    forced_value = max(value(assignment, lower_quote) for assignment in forced)
    full_value = max(value(assignment, lower_quote) for assignment in assignments)
    assert objective == forced_value - full_value

    # Independently maximize the gap of this X over the box and forced assignments.
    worst = max(
        value(assignment, price) - (b_x - s_x * price)
        for assignment in forced for price in box
    )
    assert worst == objective
    return objective, assignments, forced, value


def strict_exclusion_and_recovery():
    intercepts = (Fraction(5), Fraction(7, 2), Fraction(3))
    slopes = (Fraction(3), Fraction(2), Fraction(1))
    box = (Fraction(0), Fraction(2))
    excluded = 1
    objective, assignments, forced, value = check_exclusion_lp(
        intercepts, slopes, excluded, box, ((0, Fraction(1, 2)), (2, Fraction(1, 2))),
        Fraction(1),
    )
    assert objective == Fraction(-1, 2)
    # Every integral comparison assignment has a nonnegative worst gap.
    assert all(
        max(value(rival, price) - value(assignment, price) for rival in forced for price in box)
        >= 0 for assignment in assignments
    )

    # With buyer 2 assigned the good, the support LP reduces to the outside floors
    # of buyers 0 and 1 and the upper bound from buyer 2's nonnegative utility.
    matching = {0: -1, 1: -1, 2: 0}
    full_floor = max(intercepts[i] / slopes[i] for i in (0, 1))
    floor_without_offer = intercepts[0] / slopes[0]
    upper = intercepts[2] / slopes[2]
    assert box[0] <= floor_without_offer < full_floor <= upper
    assert full_floor == Fraction(7, 4) and floor_without_offer == Fraction(5, 3)
    assert intercepts[excluded] - slopes[excluded] * full_floor == 0
    assert intercepts[excluded] - slopes[excluded] * floor_without_offer == Fraction(1, 6)
    check_certificate(
        [[bid] for bid in intercepts], [[slope] for slope in slopes],
        [full_floor], matching, exhaustive=True,
    )


def inconclusive_zero():
    objective, _, _, _ = check_exclusion_lp(
        (Fraction(2), Fraction(2)), (Fraction(1), Fraction(1)), 1,
        (Fraction(0), Fraction(2)), ((1, Fraction(1)),), Fraction(1),
    )
    assert objective == 0
    # The forced edge actually participates in a minimum-price matching.
    check_certificate(
        [[Fraction(2)], [Fraction(2)]], [[Fraction(1)], [Fraction(1)]],
        [Fraction(2)], {0: -1, 1: 0}, exhaustive=True,
    )


if __name__ == "__main__":
    strict_exclusion_and_recovery()
    inconclusive_zero()
    print("Verified exclusion LP optima -1/2 and 0, and a tight excluded offer required in recovery.")
