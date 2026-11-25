"""Exact cost-form inputs and compact outputs for Kintali's algorithm."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


Vector = tuple[Fraction, ...]
Matrix = tuple[Vector, ...]


def _rational(value: int | str | Fraction) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, str, Fraction)):
        raise ValueError("Expected an exact rational number.")
    return Fraction(value)


def _vector(values: Vector) -> Vector:
    if not isinstance(values, (tuple, list)):
        raise ValueError("Expected a sequence of rational numbers.")
    return tuple(_rational(value) for value in values)


def _matrix(rows: Matrix) -> Matrix:
    if not isinstance(rows, (tuple, list)):
        raise ValueError("Expected a sequence of payoff rows.")
    return tuple(_vector(row) for row in rows)


@dataclass(frozen=True)
class Game:
    """Buying target j costs intercept[i][j] + slope[i][j] * coverage[j]."""

    resources: int
    prior: Vector
    intercept: Matrix
    slope: Matrix
    gain: Vector

    def __post_init__(self) -> None:
        object.__setattr__(self, "prior", _vector(self.prior))
        object.__setattr__(self, "intercept", _matrix(self.intercept))
        object.__setattr__(self, "slope", _matrix(self.slope))
        object.__setattr__(self, "gain", _vector(self.gain))
        if not self.targets:
            raise ValueError("A game must have at least one target.")
        if type(self.resources) is not int or not 0 <= self.resources <= self.targets:
            raise ValueError("The defender budget must be an integer between zero and the number of targets.")
        if any(p < 0 for p in self.prior) or sum(self.prior) != 1:
            raise ValueError("Attacker priors must be nonnegative and sum to one.")
        for table in (self.intercept, self.slope):
            if len(table) != self.types or any(len(row) != self.targets for row in table):
                raise ValueError("Each payoff table must have one row per type and one column per target.")
        if any(d < 0 for row in self.slope for d in row) or any(g < 0 for g in self.gain):
            raise ValueError("Attacker cost slopes and defender gains must be nonnegative.")

    @property
    def types(self) -> int:
        return len(self.prior)

    @property
    def targets(self) -> int:
        return len(self.gain)

    def cost(self, i: int, j: int, coverage: Fraction) -> Fraction:
        return self.intercept[i][j] + self.slope[i][j] * coverage


@dataclass(frozen=True)
class Strategy:
    coverage: Vector
    attacks: Matrix
