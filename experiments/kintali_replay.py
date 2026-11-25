#!/usr/bin/env python3
"""Replay small exact games through Python and Lean's public binary solver.

Build with lake --wfail build Kintali from lean/ before a cross-language run.
The replay checks concrete strategies and does not prove solver equivalence.
"""

import argparse
from fractions import Fraction
from itertools import product
from pathlib import Path
import shutil
import subprocess

from kintali_market import contact
from kintali_model import Game, Strategy
from kintali_repair import contact_tolerance, try_repair
from kintali_solver import _double_interval, _quantiles, defender_lottery, prepare_quotes, solve


def _nat(value):
    # Mathlib writes least-significant bits first and uses no bits for zero.
    return format(value, "b")[::-1] if value else ""


def _block(bits):
    return "".join("1" + bit for bit in bits) + "0"


def _rational(value):
    numerator = value.numerator
    signed = _block(_nat(max(0, numerator))) + _nat(max(0, -numerator))
    return _block(signed) + _nat(value.denominator)


def _payoffs(uncovered, covered):
    return _block(_rational(uncovered)) + _rational(covered)


def encode_game(game):
    """Serialize a cost-form game using InputOutput.writeGame and Binary.input."""
    defense = "".join(_block(_payoffs(0, gain)) for gain in game.gain)
    attackers = []
    for prior, intercepts, slopes in zip(game.prior, game.intercept, game.slope):
        offers = "".join(
            _block(_payoffs(-intercept, -intercept - slope))
            for intercept, slope in zip(intercepts, slopes)
        )
        attackers.append(_block(_block(_rational(prior)) + offers))
    return _block(_nat(game.resources)) + _block(defense) + "".join(attackers)


def _split_block(bits):
    for offset in range(0, len(bits), 2):
        if bits[offset] == "0":
            return bits[1:offset:2], bits[offset + 1:]
    raise ValueError("Unterminated bit block.")


def _fields(bits):
    while bits:
        field, bits = _split_block(bits)
        yield field


def _read_nat(bits):
    return int(bits[::-1], 2) if bits else 0


def _read_rational(bits):
    signed, denominator = _split_block(bits)
    positive, negative = _split_block(signed)
    den = _read_nat(denominator)
    if not den:
        raise ValueError("Zero rational denominator.")
    value = Fraction(_read_nat(positive) - _read_nat(negative), den)
    if _rational(value) != bits:
        raise ValueError("Noncanonical rational encoding.")
    return value


def decode_strategy(bits):
    """Read a canonical Binary.output bitstream without Lean."""
    if not bits or set(bits) - {"0", "1"}:
        raise ValueError("Expected a nonempty binary strategy.")
    coverage, attacks = _split_block(bits)
    return Strategy(
        tuple(map(_read_rational, _fields(coverage))),
        tuple(tuple(map(_read_rational, _fields(row))) for row in _fields(attacks)),
    )


def check_strategy(label, game, strategy, expected=None):
    """Compare each player's expected payoff with its best pure deviation."""
    coverage, attacks = strategy.coverage, strategy.attacks
    if len(coverage) != game.targets or len(attacks) != game.types:
        raise ValueError(f"{label} has incorrect strategy dimensions.")
    if any(len(row) != game.targets for row in attacks):
        raise ValueError(f"{label} has an attack row of the wrong length.")
    if any(type(x) not in (int, Fraction) for row in (coverage, *attacks) for x in row):
        raise ValueError(f"{label} has a non-exact probability.")
    if sum(coverage) != game.resources or any(not 0 <= x <= 1 for x in coverage):
        raise ValueError(f"{label} has infeasible coverage.")
    for i, row in enumerate(attacks):
        if sum(row) != 1 or any(q < 0 for q in row):
            raise ValueError(f"{label} has an infeasible attack row {i}.")
        costs = [
            intercept + slope * x
            for intercept, slope, x in zip(game.intercept[i], game.slope[i], coverage)
        ]
        if sum(q * cost for q, cost in zip(row, costs)) != min(costs):
            raise ValueError(f"{label} has a profitable deviation for attacker type {i}.")
    gains = [
        game.gain[j] * sum(prior * row[j] for prior, row in zip(game.prior, attacks))
        for j in range(game.targets)
    ]
    best_defense = sum(sorted(gains, reverse=True)[:game.resources])
    if sum(x * gain for x, gain in zip(coverage, gains)) != best_defense:
        raise ValueError(f"{label} has a profitable defender deviation.")
    if expected is not None and strategy != expected:
        raise ValueError(f"{label} returned {strategy}, expected {expected}.")


def check_lottery(label, game, strategy):
    lottery = defender_lottery(strategy.coverage)
    if len(lottery) > game.targets or sum(weight for _, weight in lottery) != 1:
        raise ValueError(f"{label} has an invalid defender lottery size or total.")
    for defense, weight in lottery:
        if (len(defense) != game.resources or len(set(defense)) != len(defense)
                or any(not 0 <= j < game.targets for j in defense) or weight <= 0):
            raise ValueError(f"{label} emitted an illegal pure defense.")
    marginals = tuple(
        sum(weight for defense, weight in lottery if j in defense) for j in range(game.targets)
    )
    if marginals != strategy.coverage:
        raise ValueError(f"{label} has incorrect defender lottery marginals.")


def fixtures():
    """Supply the exact expected strategy when the equilibrium is unique."""
    yield (
        "zero-budget",
        Game(0, (1,), ((0, 5),), ((1, 1),), (1, 1)),
        Strategy((0, 0), ((1, 0),)),
    )
    yield (
        "full-budget",
        Game(
            2, ("1/3", "2/3"), (("-1/2", 2), (1, "-1/3")),
            (("1/3", 1), ("3/2", "1/2")), (2, 3),
        ),
        Strategy((1, 1), ((1, 0), (0, 1))),
    )
    yield (
        "zero-gain",
        Game(1, (1, 0), ((5, 0), (0, 5)), ((0, 0), (0, 0)), (0, 0)),
        None,
    )
    yield "flat-costs", Game(1, (1,), ((0, 0),), ((0, 0),), (1, 1)), None
    yield (
        "strict-affine",
        Game(1, (1,), ((0, 5),), ((1, 1),), (1, 1)),
        Strategy((1, 0), ((1, 0),)),
    )
    # Neither endpoint is stable. Attacker cost equality gives coverage
    # (5/8, 3/8), and defender gain equality gives attacks (3/5, 2/5).
    yield (
        "mixed-affine",
        Game(1, (1,), ((0, "1/2"),), ((2, 2),), (2, 3)),
        Strategy((Fraction(5, 8), Fraction(3, 8)), ((Fraction(3, 5), Fraction(2, 5)),)),
    )


def systematic_games():
    """Enumerate small payoff tables for additional Python-only checks."""
    binary_rows = tuple(product((0, 1), repeat=2))
    for budget, intercept, slope, gain in product((0, 2), binary_rows, binary_rows, binary_rows):
        yield Game(budget, (1,), (intercept,), (slope,), gain)
    for intercept, gain in product(binary_rows, repeat=2):
        yield Game(1, (1,), (intercept,), ((0, 0),), gain)
    # These affine rows have a strict preferred target at every coverage.
    strict_rows = ((0, 2), (2, 0))
    for intercept, slope, gain in product(strict_rows, binary_rows, binary_rows):
        yield Game(1, (1,), (intercept,), (slope,), gain)
    priors = ((1, 0), ("1/3", "2/3"))
    slopes = (((1, 0), (0, 1)), ((1, 1), (1, 1)))
    gains = ((1, 1), (1, 2), (2, 1))
    for prior, first, second, slope, gain in product(priors, strict_rows, strict_rows, slopes, gains):
        yield Game(1, prior, (first, second), slope, gain)


def check_nonzero_repair():
    """Replay Lean's repair of a nonzero coverage perturbation."""
    game = Game(1, (1,), ((0, 0),), ((1, 1),), (1, 1))
    epsilon = contact_tolerance(game)
    half = Fraction(1, 2)
    coverage = (half + epsilon / 4, half - epsilon / 4)
    joint = ((half, half),)
    strategy = try_repair(game, coverage, joint, half, epsilon)
    if strategy is None:
        raise ValueError("Repair rejected the perturbed coverage fixture.")
    check_strategy("nonzero repair", game, strategy, Strategy((half, half), joint))


def check_zero_prior_response():
    game = Game(1, (1, 0), ((0, 5), (0, -1)), ((1, 1), (1, 0)), (2, 3))
    strategy = solve(game)
    expected = Strategy((1, 0), ((1, 0), (0, 1)))
    check_strategy("interior zero-prior response", game, strategy, expected)
    check_lottery("interior zero-prior response", game, strategy)


def crossed_game(off_diagonal):
    return Game(
        1, ("1/2", "1/2"), ((0, off_diagonal), (off_diagonal, 0)), ((2, 0), (0, 2)), (1, 1)
    )


def check_crossed_restriction():
    """The crossed holdings fail even though the diagonal holdings work."""
    game = crossed_game("3/2")
    epsilon = contact_tolerance(game)
    point = contact(game, *prepare_quotes(game, epsilon), ((),) * 4)
    half = Fraction(1, 2)
    if point.coverage != (half, half) or point.joint != ((0, half), (half, 0)):
        raise ValueError("The empty quote restriction did not produce the crossed holdings.")
    if try_repair(game, point.coverage, point.joint, point.pressure, epsilon) is not None:
        raise ValueError("The trial accepted the crossed holdings.")
    if not any(lo < hi for lo, hi in point.blocker_intervals()):
        raise ValueError("The crossed holdings did not expose an omitted blocker.")
    check_strategy(
        "diagonal holdings at the crossed contact", game, Strategy(point.coverage, ((1, 0), (0, 1)))
    )


def check_default_update():
    """At these costs the default schedule clears after one interval doubling."""
    game = crossed_game("33/32")
    epsilon = contact_tolerance(game)
    grid, scale, redirects, eligible = prepare_quotes(game, epsilon)
    runs = tuple(((count, 0),) if count else () for count in eligible)
    divisions = 4 * (game.types + game.targets + game.types * game.targets)
    selected = tuple(_quantiles(row, divisions) for row in runs)
    point = contact(game, grid, scale, redirects, eligible, selected)
    if try_repair(game, point.coverage, point.joint, point.pressure, epsilon) is not None:
        raise ValueError("The first default trial should expose a blocker.")
    updated = tuple(
        _double_interval(row, lo, hi) for row, (lo, hi) in zip(runs, point.blocker_intervals())
    )
    selected = tuple(_quantiles(row, divisions) for row in updated)
    point = contact(game, grid, scale, redirects, eligible, selected)
    repaired = try_repair(game, point.coverage, point.joint, point.pressure, epsilon)
    expected = Strategy((Fraction(1, 2), Fraction(1, 2)), ((1, 0), (0, 1)))
    if repaired != expected:
        raise ValueError("The second default trial failed to recover the expected equilibrium.")
    check_strategy("default search with one update", game, solve(game), expected)


def lean_outputs(games):
    lean_dir = Path(__file__).resolve().parents[1] / "lean"
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "Replay/KintaliBinary.lean"],
        cwd=lean_dir,
        input="".join(encode_game(game) + "\n" for game in games),
        encoding="utf-8",
        stdout=subprocess.PIPE,
    )
    if result.returncode:
        raise RuntimeError(f"Lean binary replay failed\n{result.stdout}")
    lines = result.stdout.splitlines()
    if len(lines) != len(games):
        raise RuntimeError(f"Expected {len(games)} Lean bitstreams, received {len(lines)}.")
    return lines


def replay(*, python_only, systematic):
    cases = tuple(fixtures())
    python_outputs = []
    for name, game, expected in cases:
        strategy = solve(game)
        check_strategy(f"{name} Python", game, strategy, expected)
        check_lottery(f"{name} Python", game, strategy)
        python_outputs.append(strategy)
    check_zero_prior_response()
    check_nonzero_repair()
    check_crossed_restriction()
    check_default_update()
    print(
        f"{len(cases) + 1} Python equilibrium and lottery fixtures passed. Repair and quote update checks passed.",
        flush=True,
    )
    if systematic:
        count = 0
        for count, game in enumerate(systematic_games(), 1):
            strategy = solve(game)
            check_strategy(f"systematic case {count} Python", game, strategy)
            check_lottery(f"systematic case {count} Python", game, strategy)
        print(f"{count} systematic Python checks passed.", flush=True)
    if python_only:
        return

    records = lean_outputs([game for _, game, _ in cases])
    matches = 0
    for (name, game, expected), python_output, bits in zip(cases, python_outputs, records):
        try:
            strategy = decode_strategy(bits)
        except ValueError as exc:
            raise ValueError(f"{name} could not read the Lean strategy.") from exc
        check_strategy(f"{name} Lean", game, strategy, expected)
        matches += strategy == python_output
    print(f"{len(cases)} Lean binary fixture checks passed and {matches} matched Python exactly.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--python-only", action="store_true", help="skip the Lean binary replay")
    parser.add_argument("--systematic", action="store_true", help="add 224 Python-only cases")
    args = parser.parse_args()
    if not args.python_only and shutil.which("lake") is None:
        parser.error("the lake executable must be on PATH for the cross-language replay")
    replay(python_only=args.python_only, systematic=args.systematic)


if __name__ == "__main__":
    main()
