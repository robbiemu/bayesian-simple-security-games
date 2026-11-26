#!/usr/bin/env python3
"""Reproduce the exact four- and three-target witnesses in B3f and B3g."""

from fractions import Fraction
from itertools import combinations, permutations
from math import prod


def affine_game(size, arc_scores, penalty, epsilon):
    """Convert assignment scores B - C*s into uncovered utility and loss."""
    offsets = []
    losses = []
    for row in range(size):
        row_offsets = []
        row_losses = []
        for target in range(size):
            offset, loss = arc_scores.get((row, target), (-penalty, 0))
            row_offsets.append(epsilon * offset)
            row_losses.append(1 + epsilon * loss)
        offsets.append(row_offsets)
        losses.append(row_losses)
    return offsets, losses


def preferences_hold(coverage, assignment, offsets, losses):
    for row, assigned in enumerate(assignment):
        utilities = [
            offset - loss * probability
            for offset, loss, probability in zip(offsets[row], losses[row], coverage)
        ]
        if utilities[assigned] < max(utilities):
            return False
    return True


def check_four_targets():
    # Rows and columns follow o, a, b, t. The two indirect first arcs
    # have scores 2*lambda-2 and 4*lambda-8 after substituting lambda.
    arcs = {
        (0, 3): (0, 0), (0, 1): (Fraction(-14, 3), Fraction(-128, 3)),
        (0, 2): (Fraction(-40, 3), Fraction(-256, 3)),
        (1, 3): (0, 0), (2, 3): (0, 0), (3, 0): (0, 0),
        (0, 0): (0, 0), (1, 1): (0, 0), (2, 2): (0, 0),
    }
    fixtures = [
        (Fraction(1, 4), (3, 1, 2, 0), Fraction(1)),
        (Fraction(5, 8), (1, 3, 2, 0), Fraction(4859999, 4860000)),
        (Fraction(1), (2, 1, 3, 0), Fraction(2429999, 2430000)),
    ]
    offsets, losses = affine_game(4, arcs, 900, Fraction(1, 207360000))
    assert (offsets[0][0], losses[0][0]) == (offsets[0][3], losses[0][3])
    for budget, expected, expected_product in fixtures:
        uniform = budget / 4
        scores = []
        for assignment in permutations(range(4)):
            score = 0
            for row, target in enumerate(assignment):
                offset, loss = arcs.get((row, target), (-900, 0))
                score += offset - loss * uniform
            scores.append((score, assignment))
        scores.sort(reverse=True)
        winner_score, winner = scores[0]
        assert winner == expected and winner_score - scores[1][0] == 2
        assert preferences_hold((uniform,) * 4, winner, offsets, losses)
        assert prod(losses[row][target] for row, target in enumerate(winner)) == expected_product
        print(f"B3f budget {budget}: {winner}, assignment gap 2")


def three_target_coverage(budget, assignment, offsets, losses):
    """Find a vertex of the coverage box with best-response inequalities."""
    size = len(assignment)
    lower = [(tuple(int(j == k) for j in range(size)), 0) for k in range(size)]
    upper = [(tuple(-value for value in direction), -1) for direction, _ in lower]
    inequalities = lower + upper
    for row, assigned in enumerate(assignment):
        for alternative in range(size):
            if alternative == assigned:
                continue
            coefficients = tuple(
                (int(j == alternative) - int(j == assigned)) * losses[row][j]
                for j in range(size)
            )
            inequalities.append((coefficients, offsets[row][alternative] - offsets[row][assigned]))
    # Substitute x_2 = budget - x_0 - x_1 and enumerate pairs of tight lines.
    lines = [(a - c, b - c, rhs - c * budget) for (a, b, c), rhs in inequalities]
    for (a, b, rhs), (d, e, other_rhs) in combinations(lines, 2):
        determinant = a * e - b * d
        if determinant == 0:
            continue
        x0 = (rhs * e - b * other_rhs) / determinant
        x1 = (a * other_rhs - rhs * d) / determinant
        if all(c0 * x0 + c1 * x1 >= limit for c0, c1, limit in lines):
            return x0, x1, budget - x0 - x1
    return None


def check_three_targets():
    arcs = {
        (0, 1): (3, 12), (1, 2): (0, 0), (0, 2): (0, 0),
        (2, 0): (0, 0), (0, 0): (0, 0), (1, 1): (0, 0),
    }
    offsets, losses = affine_game(3, arcs, 25, Fraction(1, 2**18))
    for budget, expected in [(Fraction(1, 2), (1, 2, 0)), (Fraction(1), (2, 1, 0))]:
        feasible = []
        for assignment in permutations(range(3)):
            coverage = three_target_coverage(budget, assignment, offsets, losses)
            if coverage is not None:
                assert preferences_hold(coverage, assignment, offsets, losses)
                feasible.append(assignment)
        assert feasible == [expected]
        print(f"B3g budget {budget}: unique feasible permutation {expected}")


if __name__ == "__main__":
    check_four_targets()
    check_three_targets()
