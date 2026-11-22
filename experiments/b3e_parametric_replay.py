"""Replay the five-vertex B3e example with exact arithmetic."""

from fractions import Fraction
from itertools import combinations


N = 5
SINK = N - 1
VERTICES = tuple(range(N))
BUDGET = Fraction(1)
PATH_WEIGHTS = (
    ((1, 3), (-2, -1)),
    ((1, -2), (-1, 2)),
    ((-1, 1), (2, -7)),
)


def shifted_edges():
    # Substitute lambda = 8(4ns - 1) in the maximization weights.
    coefficients = {}
    for middle, pair in enumerate(PATH_WEIGHTS, 1):
        for edge, (slope, offset) in zip(((0, middle), (middle, SINK)), pair):
            coefficients[edge] = (32 * N * slope, offset - 8 * slope)
    largest = max(abs(value) for pair in coefficients.values() for value in pair)
    bound = 1 << (largest - 1).bit_length()
    epsilon = Fraction(1, 128 * N**2 * bound**2)
    shift = [Fraction(v, 16 * N**2) for v in VERTICES]
    edges = {}
    for (u, v), (slope, offset) in coefficients.items():
        gain = 1 + epsilon * slope
        edges[u, v] = (gain, gain * shift[u] + epsilon * offset - shift[v])
    return edges


def envelope(source, edges):
    coverage = [source] + [Fraction(0)] * (N - 1)
    for v in VERTICES[1:]:
        offers = [
            gain * coverage[u] + offset
            for (u, target), (gain, offset) in edges.items()
            if target == v
        ]
        coverage[v] = max(Fraction(0), *offers)
    return coverage


def tight_edges(coverage, edges):
    return {
        (u, v)
        for (u, v), (gain, offset) in edges.items()
        if gain * coverage[u] + offset == coverage[v]
    }


def check_steps(edges):
    coverage = [Fraction(0)] * N
    steps = 0
    while sum(coverage) < BUDGET:
        rates = [Fraction(1)] + [Fraction(0)] * (N - 1)
        tight = tight_edges(coverage, edges)
        for u, v in sorted(tight):
            gain, _ = edges[u, v]
            rates[v] = max(rates[v], gain * rates[u])

        events = [(BUDGET - sum(coverage)) / sum(rates)]
        events.extend((1 - x) / rate for x, rate in zip(coverage, rates) if rate)
        for (u, v), (gain, offset) in edges.items():
            slack = coverage[v] - gain * coverage[u] - offset
            closing_rate = gain * rates[u] - rates[v]
            assert slack >= 0
            if slack > 0 and closing_rate > 0:
                events.append(slack / closing_rate)
        step = min(events)
        assert step > 0
        endpoint = [x + step * rate for x, rate in zip(coverage, rates)]
        midpoint = [(x + y) / 2 for x, y in zip(coverage, endpoint)]
        assert midpoint == envelope(midpoint[0], edges)
        assert endpoint == envelope(endpoint[0], edges)
        coverage = endpoint
        steps += 1
    assert sum(coverage) == BUDGET and steps == 7
    return steps


def check_hall_witnesses(edges):
    families = []
    for parameter, winner in (
        (Fraction(1, 2), 1),
        (Fraction(4), 2),
        (Fraction(15, 2), 3),
    ):
        source = (1 + parameter / 8) / (4 * N)
        coverage = envelope(source, edges)
        tight = tight_edges(coverage, edges)
        assert {u for u, v in tight if v == SINK} == {winner}
        # Each row always demands its own good. The other demands are its tight arcs.
        demands = [{u} | {v for tail, v in tight if tail == u} for u in VERTICES]
        family = set()
        for size in range(1, N + 1):
            for subset in combinations(VERTICES, size):
                goods = frozenset(subset)
                ratio = Fraction(sum(row <= goods for row in demands), N * size)
                assert ratio <= Fraction(1, N)
                closed = all(u not in goods or v in goods for u, v in tight)
                assert (ratio == Fraction(1, N)) == closed
                if closed:
                    family.add(goods)
        source_witness = set.intersection(*(set(s) for s in family if 0 in s))
        assert source_witness == set(VERTICES)
        families.append(frozenset(family))
    assert len(set(families)) == 3


if __name__ == "__main__":
    edges = shifted_edges()
    steps = check_steps(edges)
    check_hall_witnesses(edges)
    print(
        f"Verified {steps} exact steps and three distinct Hall-witness families at threshold 1/5."
    )
