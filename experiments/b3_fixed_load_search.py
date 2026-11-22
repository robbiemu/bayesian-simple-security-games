"""Replay Algorithms 2–3 up to the first cap or budget, in exact arithmetic."""

from argparse import ArgumentParser
from dataclasses import dataclass
from fractions import Fraction
from random import Random


def witness(name):
    if name == "active":
        baselines = ((0, -5, -2), (-32, 0, -3), (-32, -2, 0))
        slopes = ((2, 1, 2), (1, 2, 1), (1, 2, 2))
        scale, budget = 16, 1
    else:
        baselines = ((0, -14, -23, -6), (-4, 0, -7, -11), (-15, -10, 0, -21), (-18, -3, -7, 0))
        slopes = ((71, 42, 34, 53), (42, 55, 47, 70), (56, 60, 80, 13), (17, 36, 54, 79))
        scale, budget = 4, 3
    return tuple(tuple(Fraction(a, scale) for a in row) for row in baselines), slopes, budget


@dataclass(frozen=True)
class Step:
    coverage: tuple
    active: tuple
    matching: tuple
    product: int
    rates: tuple
    length: Fraction
    optimizer_count: int

    @property
    def reach(self):
        return tuple(target for target, rate in enumerate(self.rates) if rate)


def optimize(active, slopes, loads):
    """Find an exact min-cost transportation vertex at equal row supplies."""
    row_order = sorted(range(len(active)), key=lambda row: len(active[row]))
    remainder = list(loads)
    matching = [None] * len(active)
    best = None
    count = 0

    def visit(depth, product):
        nonlocal best, count
        if depth == len(row_order):
            candidate = (product, tuple(matching))
            if best is None or candidate[0] < best[0]:
                best, count = candidate, 1
            elif candidate[0] == best[0]:
                best, count = min(best, candidate), count + 1
            return

        row = row_order[depth]
        for target in active[row]:
            if remainder[target]:
                matching[row] = target
                remainder[target] -= 1
                visit(depth + 1, product * slopes[row][target])
                remainder[target] += 1

    visit(0, 1)
    if best is None:
        raise ValueError("The active graph lost its feasible matching")
    return best[0], best[1], count


def coverage_rates(active, matching, slopes, seed):
    """Collapse target -> assigned row -> active target into target arcs."""
    size = len(slopes[0])
    arcs = [
        (source, target, Fraction(slopes[row][target], slopes[row][source]))
        for row, source in enumerate(matching)
        for target in active[row]
        if source != target
    ]
    distances = [None] * size
    distances[seed] = Fraction(1)
    for _ in range(size - 1):
        next_distances = distances.copy()
        for source, target, multiplier in arcs:
            distance = distances[source]
            if distance is None:
                continue
            candidate = distance * multiplier
            if next_distances[target] is None or candidate < next_distances[target]:
                next_distances[target] = candidate
        if next_distances == distances:
            break
        distances = next_distances
    return tuple(Fraction(0) if distance is None else 1 / distance for distance in distances)


def trace(baselines, slopes, budget, seed=0):
    """Use equal priors and choose gains equal to inverse initial counts."""
    target_count = len(baselines[0])
    initial = [row.index(max(row)) for row in baselines]
    loads = tuple(initial.count(target) for target in range(target_count))
    if not all(loads):
        raise ValueError("Every target must start with positive mass")
    coverage = (Fraction(0),) * target_count
    while sum(coverage) < budget and max(coverage) < 1:
        payoffs = tuple(
            tuple(a - d * x for a, d, x in zip(row, deltas, coverage))
            for row, deltas in zip(baselines, slopes)
        )
        maxima = tuple(map(max, payoffs))
        active = tuple(
            tuple(target for target, payoff in enumerate(row) if payoff == maximum)
            for row, maximum in zip(payoffs, maxima)
        )
        product, matching, count = optimize(active, slopes, loads)
        rates = coverage_rates(active, matching, slopes, seed)
        length = min(
            (budget - sum(coverage)) / sum(rates),
            *((1 - x) / rate for x, rate in zip(coverage, rates) if rate),
        )
        for row, assigned in enumerate(matching):
            row_rate = slopes[row][assigned] * rates[assigned]
            for target, payoff in enumerate(payoffs[row]):
                gap = maxima[row] - payoff
                closing_rate = row_rate - slopes[row][target] * rates[target]
                if gap and closing_rate > 0:
                    length = min(length, gap / closing_rate)
                if not gap:
                    assert closing_rate <= 0
        assert length > 0
        yield Step(coverage, active, matching, product, rates, length, count)
        coverage = tuple(x + length * rate for x, rate in zip(coverage, rates))


def score(steps):
    strict_fixed_reach = [
        (old, new) for old, new in zip(steps, steps[1:])
        if old.product > new.product and old.reach == new.reach
    ]
    resets = sum(
        any(after < before for before, after in zip(old.rates, new.rates))
        for old, new in strict_fixed_reach
    )
    return len(strict_fixed_reach), resets, len(steps)


def history_events(steps, slopes):
    history = [set() for _ in slopes]
    used = [set() for _ in slopes]
    loads = tuple(steps[0].matching.count(target) for target in range(len(slopes[0])))
    previous = None
    events = {}
    for index, step in enumerate(steps):
        if previous is not None and step.product < previous.product:
            entering = [
                (row, target)
                for row, active in enumerate(step.active)
                for target in active
                if target not in previous.active[row]
            ]
            if all(target in history[row] for row, target in entering):
                events.setdefault("reentry", (index, tuple(entering)))
            if all(target in used[row] for row, target in enumerate(step.matching)):
                events.setdefault("used-reentry", (index, step.matching, step.product))
        for seen, active in zip(history, step.active):
            seen.update(active)
        if "history" not in events:
            unions = tuple(tuple(sorted(seen)) for seen in history)
            product, matching, _ = optimize(unions, slopes, loads)
            if product < step.product:
                events["history"] = (index, matching, product)
        for row, target in enumerate(step.matching):
            used[row].add(target)
        if "used-history" not in events:
            unions = tuple(tuple(sorted(seen)) for seen in used)
            product, matching, _ = optimize(unions, slopes, loads)
            if product < step.product:
                events["used-history"] = (index, matching, product)
        previous = step
    return events


def random_input(random, size):
    baselines = tuple(
        tuple(0 if row == target else -random.randint(1, 24) for target in range(size))
        for row in range(size)
    )
    slopes = tuple(
        tuple(random.randint(1, 80) for target in range(size))
        for _ in range(size)
    )
    return baselines, slopes


def show(baselines, slopes, steps):
    print(f"baselines = {baselines}\nslopes = {slopes}\nscore = {score(steps)}")
    for index, step in enumerate(steps):
        rates = ", ".join(map(str, step.rates))
        coverage = ", ".join(map(str, step.coverage))
        print(f"{index:2d} x=({coverage}) active={step.active} "
              f"matching={step.matching} product={step.product} rates=({rates}) "
              f"length={step.length} optima={step.optimizer_count}")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--replay", choices=("active", "used"))
    parser.add_argument("--size", type=int, default=4)
    parser.add_argument("--samples", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument(
        "--objective",
        choices=("drops", "reentry", "history", "used-reentry", "used-history"),
        default="drops",
    )
    args = parser.parse_args()

    if args.replay:
        baselines, slopes, budget = witness(args.replay)
        steps = list(trace(baselines, slopes, budget))
        print(f"Historical events = {history_events(steps, slopes)}")
        show(baselines, slopes, steps)
        return

    random = Random(args.seed)
    winner = None
    for index in range(args.samples):
        baselines, slopes = random_input(random, args.size)
        steps = list(trace(baselines, slopes, args.size))
        if args.objective == "drops":
            rank = score(steps)
        else:
            event = history_events(steps, slopes).get(args.objective)
            if event is None:
                continue
            rank = (-event[0], -len(steps))
        if winner is None or rank > winner[0]:
            winner = rank, index, baselines, slopes, steps
    if winner is not None:
        _, index, baselines, slopes, steps = winner
        print(f"Sample {index} at n={args.size}, seed={args.seed}")
        print(f"Historical events = {history_events(steps, slopes)}")
        show(baselines, slopes, steps)
    else:
        print(f"No {args.objective} witness in {args.samples} samples "
              f"at n={args.size}, seed={args.seed}")


if __name__ == "__main__":
    main()
