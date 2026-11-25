"""Grouped quota sweep and blocking intervals from §2–3 of Shiva Kintali's short proof."""

from collections import deque
from dataclasses import dataclass, field
from fractions import Fraction
from math import ceil, floor

from kintali_model import Game


@dataclass(frozen=True)
class Contact:
    pressure: Fraction
    coverage: tuple[Fraction, ...]
    joint: tuple[tuple[Fraction, ...], ...]
    _intervals: tuple[tuple[int, int], ...] = field(repr=False)

    def blocker_intervals(self) -> tuple[tuple[int, int], ...]:
        """Half-open intervals of blocking optional quotes, in buyer/site order."""
        return self._intervals


@dataclass(frozen=True)
class _Bid:
    buyer: int
    site: int
    quote: int  # A private group's representative is its highest elementary gap.
    cost: Fraction

    @property
    def buyer_key(self) -> tuple[Fraction, int, int]:
        return self.cost, self.site, self.quote


def _grouped_bids(game, grid, scale, redirects, eligible, selected):
    bids = []
    masses = list(game.prior)
    cuts = [{0, grid} for _ in game.gain]
    for i, dest in enumerate(redirects):
        outside_cost = game.cost(i, dest, Fraction(game.gain[dest] > 0))
        for j, gain in enumerate(game.gain):
            if gain <= 0:
                continue
            pair = i * game.targets + j
            quotes = {z for z in selected[pair] if 0 <= z < eligible[pair]}
            if game.cost(i, j, Fraction(1)) <= outside_cost:
                quotes.add(grid)
            for z in sorted(quotes):
                bids.append(_Bid(i, j, z, game.cost(i, j, Fraction(z, grid))))
            cuts[j].update(quotes)

    for j, boundaries in enumerate(cuts):
        if game.gain[j] > 0:
            ordered = sorted(boundaries)
            for lo, hi in zip(ordered, ordered[1:]):
                bids.append(_Bid(len(masses), j, hi - 1, Fraction(0)))
                masses.append(scale * (hi - lo) / grid)
    return bids, masses


def _route(successor, injection):
    """Peel the functional graph to propagate site injections or select one cycle."""
    indegree = [0] * len(successor)
    for dest in successor:
        if dest is not None:
            indegree[dest] += 1
    ready = deque(v for v, count in enumerate(indegree) if not count)
    flow = injection.copy()
    while ready:
        v = ready.popleft()
        dest = successor[v]
        if dest is not None:
            if flow[v]:
                flow[dest] += flow[v]
            indegree[dest] -= 1
            if not indegree[dest]:
                ready.append(dest)

    # Exactly the cyclic vertices survive. Real buyers come first in index order.
    seed = next((v for v, count in enumerate(indegree) if count), None)
    if seed is None:
        return True, flow
    flow = [Fraction(0)] * len(successor)
    v = seed
    while not flow[v]:
        flow[v] = Fraction(1)
        v = successor[v]
    return False, flow


class _Sweep:
    """Ordinary bid IDs are followed by one outside ID per buyer and one vacancy per site."""

    def __init__(self, bids, masses, gains, types):
        self.bids = bids
        self.types = types
        self.buyers = len(masses)
        self.outside = len(bids)
        self.vacancy = self.outside + self.buyers
        self.amount = [Fraction(0)] * len(bids) + masses + [Fraction(0)] * len(gains)
        self.injection = [Fraction(0)] * self.buyers + [
            Fraction(1) / gain if gain > 0 else Fraction(0) for gain in gains
        ]

        self.buyer_rows = [[] for _ in masses]
        self.site_rows = [[] for _ in gains]
        self.rank = [0] * len(bids)
        for e, bid in enumerate(bids):
            self.buyer_rows[bid.buyer].append(e)
            self.site_rows[bid.site].append(e)
        for b, row in enumerate(self.buyer_rows):
            row.sort(key=lambda e: bids[e].buyer_key)
            for rank, e in enumerate(row):
                self.rank[e] = rank
            row.append(self.outside + b)
        for j, row in enumerate(self.site_rows):
            # Real quote z ranks at 2z, private gap q at 2q+1; higher is better.
            row.sort(key=lambda e: (-(2 * bids[e].quote + (bids[e].buyer >= types)), bids[e].buyer))
            row.append(self.vacancy + j)
        self.worst_pos = [len(row) - 1 for row in self.buyer_rows]
        self.offer_pos = [0] * len(gains)

    def choices(self):
        worst = []
        for b, row in enumerate(self.buyer_rows):
            pos = self.worst_pos[b]
            # A buyer only improves its worst holding; exhausted worse bids stay empty.
            while pos >= 0 and not self.amount[row[pos]]:
                pos -= 1
            self.worst_pos[b] = pos
            worst.append(row[pos] if pos >= 0 else self.outside + b)

        offers = []
        for j, row in enumerate(self.site_rows):
            pos = self.offer_pos[j]
            while row[pos] < self.outside:
                e = row[pos]
                if self.rank[e] < self.worst_pos[self.bids[e].buyer]:
                    break
                pos += 1
            self.offer_pos[j] = pos
            offers.append(row[pos])
        return worst, offers

    def at_budget(self, private_needed, upper):
        """Buy the requested private mass, circulating at fixed pressure on a cycle."""
        pressure = Fraction(0)
        if not private_needed:
            return pressure
        for _ in range(len(self.amount) + 1):
            worst, offers = self.choices()
            successor = [self.buyers + self.bids[e].site if e < self.outside else None for e in worst]
            successor.extend(self.bids[e].buyer if e < self.outside else None for e in offers)
            advancing, flow = _route(successor, self.injection)
            times = [self.amount[e] / flow[b] for b, e in enumerate(worst) if flow[b]]
            if advancing:
                times.append(upper - pressure)
            duration = min(times)
            # A private buyer accepts only with a positive outside balance.
            private_rate = sum((rate for rate in flow[self.types:self.buyers] if rate), Fraction(0))
            if private_rate:
                duration = min(duration, private_needed / private_rate)
            if duration <= 0:
                raise ArithmeticError("quota sweep failed to advance or exhaust a positive holding")
            for b, e in enumerate(worst):
                if flow[b]:
                    self.amount[e] -= duration * flow[b]
            for j, e in enumerate(offers):
                if flow[self.buyers + j]:
                    self.amount[e] += duration * flow[self.buyers + j]
            if advancing:
                pressure += duration
            private_needed -= duration * private_rate
            if not private_needed:  # Stop before any further cycle at the contact pressure.
                return pressure
            if pressure == upper:
                raise ValueError("upper pressure reached before the requested coverage budget")
        raise ArithmeticError("quota sweep exceeded the number of exhaustible records")


def _buyer_prefix(game, i, j, grid, count, outside, worst):
    if outside:
        return count
    if worst is None:  # The buyer has zero mass.
        return 0
    cost, site, quote = worst
    intercept, slope = game.intercept[i][j], game.slope[i][j]
    if not slope:
        if (intercept, j) == (cost, site):
            return min(count, quote)
        return count if (intercept, j) < (cost, site) else 0
    # Integer quotes below this crossing strictly improve cost. At an integral
    # crossing the site/quote order decides whether one more index is included.
    crossing = (cost - intercept) * grid / slope
    end = ceil(crossing)
    if crossing.denominator == 1 and (j, end) < (site, quote):
        end += 1
    return min(count, max(0, end))


def _view(game, grid, scale, redirects, eligible, sweep, pressure):
    k, m = game.types, game.targets
    private = [Fraction(0)] * m
    joint = [[Fraction(0)] * m for _ in range(k)]
    outside = sweep.amount[sweep.outside:sweep.outside + k]
    worst = [None] * k
    # At equality, a site accepts above a lower-priority real holding or a vacancy.
    lowest_at_quote = [{} for _ in range(m)]
    for e, bid in enumerate(sweep.bids):
        mass = sweep.amount[e]
        if not mass:
            continue
        i, j = bid.buyer, bid.site
        if i >= k:
            private[j] += mass
        else:
            joint[i][j] += mass
            if worst[i] is None or worst[i] < bid.buyer_key:
                worst[i] = bid.buyer_key
            lowest_at_quote[j][bid.quote] = max(i, lowest_at_quote[j].get(bid.quote, -1))
    for i, dest in enumerate(redirects):
        joint[i][dest] += outside[i]
    coverage = tuple(1 - mass / scale if gain > 0 else Fraction(0)
                     for mass, gain in zip(private, game.gain))
    cutoffs = [x * grid for x in coverage]
    intervals = []
    for pair, count in enumerate(eligible):
        i, j = divmod(pair, m)
        hi = _buyer_prefix(game, i, j, grid, count, outside[i], worst[i])
        q = cutoffs[j]
        lo = floor(q) + 1
        if q.denominator == 1 and (sweep.amount[sweep.vacancy + j]
                                    or i < lowest_at_quote[j].get(q.numerator, -1)):
            lo -= 1
        intervals.append((min(lo, hi), hi))
    return Contact(pressure, coverage, tuple(map(tuple, joint)), tuple(intervals))


def contact(game: Game, grid: int, private_scale: Fraction, redirects: tuple[int, ...],
            eligible: tuple[int, ...], selected: tuple[tuple[int, ...], ...]) -> Contact:
    """Sweep a restriction to its first budget contact.

    `eligible[i*m+j]` is the number of eligible optional quotes at the pair.
    The outside targets are the supplied endpoint minimizers. All eligible cap
    bids are permanent. The paper's scale satisfies gain[j] * scale < 1,
    ensuring the budget is reached by pressure 1 + max(gain).
    """
    scale = Fraction(private_scale)
    if grid <= 0 or scale <= 0:
        raise ValueError("grid and private scale must be positive")
    if (len(redirects) != game.types or len(eligible) != game.types * game.targets
            or len(selected) != len(eligible) or any(not 0 <= n <= grid for n in eligible)
            or any(not 0 <= dest < game.targets for dest in redirects)):
        raise ValueError("invalid restriction dimensions, eligible counts or outside target")
    active = sum(gain > 0 for gain in game.gain)
    if not 0 <= game.resources <= active:
        raise ValueError("coverage budget outside the active-site interval")
    bids, masses = _grouped_bids(game, grid, scale, redirects, eligible, selected)
    sweep = _Sweep(bids, masses, game.gain, game.types)
    upper = 1 + max(game.gain, default=Fraction(0))
    pressure = sweep.at_budget(scale * (active - game.resources), upper)
    return _view(game, grid, scale, redirects, eligible, sweep, pressure)
