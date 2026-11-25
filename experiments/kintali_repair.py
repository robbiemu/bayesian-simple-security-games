"""Exact contact-pattern test and slack-window repair for the Kintali replay."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import factorial, prod

from kintali_model import Game, Strategy


@dataclass(frozen=True)
class _Scale:
    denominator: int
    radix: int
    precision: Fraction
    tolerance: Fraction


@lru_cache(maxsize=16)
def _scale(game: Game) -> _Scale:
    # ExactRecovery.Scale takes a product over distinct rational VALUES.
    data = {Fraction(1), Fraction(game.resources), *game.prior, *game.gain}
    for table in (game.intercept, game.slope):
        for row in table:
            data.update(row)
    denominator = prod(v.denominator for v in data)
    coefficient_height = 2 * denominator * max(abs(v.numerator) for v in data)
    k, m = game.types, game.targets
    n = k * m + m + 2
    row_count = 6 * m + 4 * k * m + 2 * k + 6
    eta = Fraction(1, 4 * (n * coefficient_height) ** n)
    minor_height = factorial(n + 1) * coefficient_height ** (n + 1)
    radix = 2 + n * n * coefficient_height * minor_height
    precision = Fraction(1, minor_height * radix ** (row_count + 1))
    return _Scale(denominator, radix, precision, min(eta, precision))


def contact_tolerance(game: Game) -> Fraction:
    """The shared grid, pattern-marking and contact tolerance of Recovery.lean."""
    return _scale(game).tolerance


# Each inequality is a sparse integer coefficient row followed by its integer RHS.
_Row = tuple[tuple[tuple[int, int], ...], int]


def _pattern_rows(game, coverage, references, marked, denominator):
    """Compile ExactRecovery.Rows in rowIndex order, including all inactive rows."""
    k, m = game.types, game.targets
    x = range(k * m, k * m + m)
    t, e = x.stop, x.stop + 1
    d = denominator

    def scaled(value):
        return value.numerator * (d // value.denominator)

    def row(terms=(), rhs=0):
        coefficients = {}
        for index, value in terms:
            coefficients[index] = coefficients.get(index, 0) + value
        return tuple((c, v) for c, v in coefficients.items() if v), rhs

    def pressure_row(j, sign):
        terms = [(i * m + j, sign * scaled(game.gain[j])) for i in range(k)]
        return row([*terms, (t, -sign * d), (e, -d)])

    def cost_row(i, left, right):
        # cost(left) <= cost(right) + residual, including when left == right.
        terms = [(x[left], scaled(game.slope[i][left])),
                 (x[right], -scaled(game.slope[i][right])), (e, -d)]
        return row(terms, scaled(game.intercept[i][right]) - scaled(game.intercept[i][left]))

    empty = row()
    yield from (row([(c, -d)]) for c in x)
    yield from (row([(c, d)], d) for c in x)
    yield from (row([(c, d)]) if coverage[j] == 0 else empty for j, c in enumerate(x))
    yield from (row([(c, -d)], -d) if coverage[j] == 1 else empty for j, c in enumerate(x))
    yield from (pressure_row(j, 1) if coverage[j] != 1 else empty for j in range(m))
    yield from (pressure_row(j, -1) if coverage[j] != 0 else empty for j in range(m))

    yield from (row([(c, -d)]) for c in range(k * m))
    for i in range(k):
        for j in range(m):
            yield empty if marked[i][j] else row([(i * m + j, d)])
    for i, ref in enumerate(references):
        yield from (cost_row(i, ref, j) for j in range(m))
    for i, ref in enumerate(references):
        yield from (cost_row(i, j, ref) if marked[i][j] else empty for j in range(m))
    for sign in (1, -1):
        for i in range(k):
            yield row(((i * m + j, sign * d) for j in range(m)), sign * scaled(game.prior[i]))

    yield row(((c, d) for c in x), game.resources * d)
    yield row(((c, -d) for c in x), -game.resources * d)
    yield row([(t, -d)])
    yield row([(e, -d)])
    yield row([(e, d)], d)
    yield row([(e, 1)])  # Additional, unscaled residual <= 0 of exactSystem.


def _slack(row: _Row, point) -> Fraction:
    terms, rhs = row
    return rhs - sum((value * point[c] for c, value in terms), Fraction(0))


def _cutoff(slacks, scale):
    lower = scale.precision
    for _ in range(len(slacks) + 1):
        upper = lower * scale.radix
        if not any(lower < slack <= upper for slack in slacks):
            return lower
        lower = upper
    raise ArithmeticError("Every slack window was occupied by a distinct row")


def _repair_point(rows, slacks, point, cutoff):
    """Solve the selected minor for a displacement, fixing all other coordinates.

    After elimination in the previous pivot columns, a nonzero column entry
    is equivalent to a nonsingular bordered minor. Scanning rows and then
    columns in increasing index order therefore selects Lean's first valid
    pair. Previously dependent rows stay dependent as the basis grows.
    """
    pivots = []
    for (terms, _), slack in zip(rows, slacks):
        if abs(slack) > cutoff:
            continue
        values = [Fraction(0)] * len(point)
        for col, value in terms:
            values[col] = Fraction(value)
        rhs = slack
        for col, basis, basis_rhs in pivots:
            factor = values[col]
            if factor:
                values = [v - factor * b for v, b in zip(values, basis)]
                rhs -= factor * basis_rhs
        col = next((c for c, value in enumerate(values) if value), None)
        if col is not None:
            pivot = values[col]
            pivots.append((col, [v / pivot for v in values], rhs / pivot))

    delta = [Fraction(0)] * len(point)
    for col, basis, rhs in reversed(pivots):
        delta[col] = rhs - sum(v * step for v, step in zip(basis, delta) if v and step)
    return tuple(value + step for value, step in zip(point, delta))


def try_repair(game: Game, coverage: tuple[Fraction, ...],
               joint: tuple[tuple[Fraction, ...], ...], pressure: Fraction,
               epsilon: Fraction) -> Strategy | None:
    """Reject a failed relaxed pattern, or repair a point at Lean's precision.

    The solver supplies contact_tolerance(game) for epsilon. For an explicitly
    supplied pattern test and residual, the recovery theorem requires epsilon
    at most roundingPrecision once the relaxed rows pass.
    """
    k, m = game.types, game.targets
    if not m or len(coverage) != m or len(joint) != k or any(len(row) != m for row in joint):
        raise ValueError("Contact dimensions must match the game and include a target")
    coverage = tuple(map(Fraction, coverage))
    costs = [tuple(game.cost(i, j, coverage[j]) for j in range(m)) for i in range(k)]
    refs = [min(range(m), key=row.__getitem__) for row in costs]
    marked = [[value <= row[ref] + epsilon for value in row] for ref, row in zip(refs, costs)]
    scale = _scale(game)
    rows = list(_pattern_rows(game, coverage, refs, marked, scale.denominator))
    point = (*[Fraction(v) for row in joint for v in row], *coverage, Fraction(pressure), Fraction(epsilon))
    slacks = [_slack(row, point) for row in rows]
    if any(s < 0 for s in slacks[:-1]):
        return None
    if epsilon > scale.precision:
        raise ValueError("Relaxed residual exceeds the exact recovery precision")
    repaired = _repair_point(rows, slacks, point, _cutoff(slacks, scale))
    if any(_slack(row, repaired) < 0 for row in rows):
        raise ArithmeticError("Repaired point violates the compiled exact pattern")

    attacks = tuple(
        tuple(repaired[i * m + j] / p if p else Fraction(j == refs[i]) for j in range(m))
        for i, p in enumerate(game.prior)
    )
    return Strategy(coverage=repaired[k * m:k * m + m], attacks=attacks)
