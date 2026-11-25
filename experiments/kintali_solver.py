"""Exact Python implementation of the Kintali quote-sweep variant in PR #15."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import accumulate
from math import ceil, floor

from kintali_market import contact
from kintali_model import Game, Strategy, Vector
from kintali_repair import contact_tolerance, try_repair


WeightRuns = tuple[tuple[int, int], ...]


def _quantiles(runs: WeightRuns, divisions: int) -> tuple[int, ...]:
    """Select zero-based indices from runs of (length, number of doublings)."""
    if not runs:
        return ()
    total = sum(length << exponent for length, exponent in runs)
    run = 0
    preceding_quotes = 0
    preceding_weight = 0
    length, exponent = runs[run]
    unit = 1 << exponent
    selected = []
    for part in range(1, divisions):
        threshold = part * total
        while divisions * (preceding_weight + length * unit) < threshold:
            preceding_quotes += length
            preceding_weight += length * unit
            run += 1
            length, exponent = runs[run]
            unit = 1 << exponent
        remaining = threshold - divisions * preceding_weight
        quote = preceding_quotes + (remaining - 1) // (divisions * unit)
        # Repeated quantiles select the same bid in the sparse market.
        if not selected or selected[-1] != quote:
            selected.append(quote)
    return tuple(selected)


def _split_runs(runs: WeightRuns, count: int) -> tuple[WeightRuns, WeightRuns]:
    before = []
    for index, (length, exponent) in enumerate(runs):
        if count < length:
            if count:
                before.append((count, exponent))
            return tuple(before), ((length - count, exponent),) + runs[index + 1 :]
        before.append((length, exponent))
        count -= length
    if count:
        raise ValueError("Quote split exceeds the eligible prefix.")
    return tuple(before), ()


def _double_interval(runs: WeightRuns, lo: int, hi: int) -> WeightRuns:
    if lo == hi:
        return runs
    before, rest = _split_runs(runs, lo)
    middle, after = _split_runs(rest, hi - lo)
    return before + tuple((length, exponent + 1) for length, exponent in middle) + after


def prepare_quotes(
    game: Game, epsilon: Fraction
) -> tuple[int, Fraction, tuple[int, ...], tuple[int, ...]]:
    """Build the grid and eligible prefixes from the normalized costs."""
    active = tuple(j for j, gain in enumerate(game.gain) if gain > 0)
    max_slope = max((row[j] for row in game.slope for j in active), default=Fraction(0))
    grid = max(1, ceil(max_slope / epsilon))
    private_scale = epsilon / max(1, max(game.gain))
    endpoints = tuple(Fraction(gain > 0) for gain in game.gain)
    redirects = []
    eligible = []
    for i in range(game.types):
        outside = min(range(game.targets), key=lambda j: game.cost(i, j, endpoints[j]))
        reserve_cost = game.cost(i, outside, endpoints[outside])
        redirects.append(outside)
        for j in range(game.targets):
            headroom = reserve_cost - game.intercept[i][j]
            slope = game.slope[i][j]
            if not endpoints[j] or headroom < 0:
                eligible.append(0)
            elif slope == 0:
                eligible.append(grid)
            else:
                eligible.append(min(grid, floor(headroom * grid / slope) + 1))
    return grid, private_scale, tuple(redirects), tuple(eligible)


def _direct_solution(game: Game) -> Strategy:
    covered = sorted(range(game.targets), key=lambda j: (game.gain[j] == 0, j))
    chosen = set(covered[: game.resources])
    coverage = tuple(Fraction(j in chosen) for j in range(game.targets))
    attacks = []
    for i in range(game.types):
        best = min(range(game.targets), key=lambda j: game.cost(i, j, coverage[j]))
        attacks.append(tuple(Fraction(j == best) for j in range(game.targets)))
    return Strategy(coverage, tuple(attacks))


def solve(game: Game) -> Strategy:
    """Return an exact compact equilibrium for a valid rational game."""
    active_count = sum(gain > 0 for gain in game.gain)
    if game.resources == 0 or game.resources >= active_count:
        return _direct_solution(game)

    epsilon = contact_tolerance(game)
    grid, private_scale, redirects, eligible = prepare_quotes(game, epsilon)
    witness_bound = game.types + active_count + game.types * active_count
    runs = [((count, 0),) if count else () for count in eligible]
    for _ in range(2 * witness_bound * grid.bit_length()):
        selected = tuple(_quantiles(row, 4 * witness_bound) for row in runs)
        point = contact(game, grid, private_scale, redirects, eligible, selected)
        strategy = try_repair(game, point.coverage, point.joint, point.pressure, epsilon)
        if strategy is not None:
            return strategy

        intervals = point.blocker_intervals()
        if len(intervals) != len(eligible):
            raise RuntimeError("A blocked trial must report one interval per buyer and target.")
        if not any(lo < hi for lo, hi in intervals):
            raise RuntimeError("A failed trial did not identify an omitted blocker.")
        for pair, (lo, hi) in enumerate(intervals):
            if not 0 <= lo <= hi <= eligible[pair] or any(
                lo <= quote < hi for quote in selected[pair]
            ):
                raise RuntimeError("A blocker interval must lie inside the eligible unselected quotes.")
            runs[pair] = _double_interval(runs[pair], lo, hi)
    raise RuntimeError("Quote search exhausted its trial bound.")


def defender_lottery(coverage: Vector) -> tuple[tuple[tuple[int, ...], Fraction], ...]:
    """Realize compact coverage by a rational lottery on at most m defenses."""
    prefix = (Fraction(0), *accumulate(coverage))
    cuts = sorted({Fraction(0), Fraction(1)} | {x - floor(x) for x in prefix[1:-1]})
    result = []
    for lo, hi in zip(cuts, cuts[1:]):
        midpoint = (lo + hi) / 2
        targets = tuple(
            j for j, (a, b) in enumerate(zip(prefix, prefix[1:]))
            if ceil(b - midpoint) > ceil(a - midpoint)
        )
        result.append((targets, hi - lo))
    return tuple(result)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "game", nargs="?", default="-", type=argparse.FileType("r", encoding="utf-8"),
        help="Cost-form game as JSON, or - for standard input.",
    )
    args = parser.parse_args()
    try:
        game = Game(**json.load(args.game, parse_float=Fraction))
    except (TypeError, ValueError, ZeroDivisionError) as exc:
        parser.error(f"Invalid game. {exc}")
    strategy = solve(game)
    print(json.dumps({
        "coverage": list(map(str, strategy.coverage)),
        "attacks": [list(map(str, row)) for row in strategy.attacks],
        "defender_lottery": [
            {"targets": list(targets), "probability": str(weight)}
            for targets, weight in defender_lottery(strategy.coverage)
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
