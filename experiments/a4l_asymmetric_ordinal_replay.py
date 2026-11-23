"""Exercise separated but asymmetric cutoffs on weighted clearing supports."""

from fractions import Fraction
from itertools import product

from a4l_weighted_ordinal import cover_faces, verify_flow


EDGES = ((0, 2), (0, 3), (1, 2), (1, 3))


def cutoff_ratios(a, b):
    def lower_ratio(cutoffs, edge, same_side):
        return max(
            (Fraction(cutoffs[k], cutoffs[edge]) for k in range(4)
             if same_side(k) == same_side(edge) and cutoffs[k] < cutoffs[edge]),
            default=Fraction(0),
        )

    return [
        (lower_ratio(a, edge, lambda k: k // 2), lower_ratio(b, edge, lambda k: k % 2))
        for edge in range(4)
    ]


def check_asymmetric_case(a, b, quotas, witness, expect_cycle, both_ratios):
    ratios = cutoff_ratios(a, b)
    assert max(r + s for r, s in ratios) == Fraction(99, 100)
    if both_ratios:
        assert any(r > 0 and s > 0 and r + s == Fraction(99, 100) for r, s in ratios)

    masks = cover_faces(a, b)
    assert verify_flow(a, b, quotas, witness, masks) == (True, True, expect_cycle)
    assert all(q > 0 for q in quotas)
    assert all(sum(witness[e] for e, endpoints in enumerate(EDGES) if v in endpoints) == q
               for v, q in enumerate(quotas))

    # Compare the two definitions on every feasible sixth-unit allocation.
    # verify_flow independently tests support feasibility against exact cover vertices.
    possible = [
        [Fraction(k, 6) for k in range(1 + int(6 * min(quotas[i], quotas[j])))]
        for i, j in EDGES
    ]
    feasible = stable = 0
    for allocation in product(*possible):
        result = verify_flow(a, b, quotas, allocation, masks)
        if result is not None:
            feasible += 1
            stable += result[0]
    assert stable > 0
    return feasible, stable


if __name__ == "__main__":
    split = check_asymmetric_case(
        (100, 60, 4, 9), (100, 8, 39, 20),
        (Fraction(11, 6), Fraction(2, 3), Fraction(3, 2), Fraction(1)),
        (Fraction(3, 2), Fraction(1, 3), Fraction(0), Fraction(2, 3)),
        expect_cycle=False, both_ratios=True,
    )
    cycle = check_asymmetric_case(
        (100, 99, 3, 10), (33, 20, 40, 9),
        (Fraction(7, 6), Fraction(5, 3), Fraction(3, 2), Fraction(4, 3)),
        (Fraction(1, 3), Fraction(5, 6), Fraction(7, 6), Fraction(1, 2)),
        expect_cycle=True, both_ratios=False,
    )
    print("Asymmetric ordinal checks (feasible, stable)", split, cycle, "with edgewise maximum 99/100.")
