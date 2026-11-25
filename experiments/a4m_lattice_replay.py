"""Finite rational checks for the unit-increment discretization of the A4f map.

Run with python3 experiments/a4m_lattice_replay.py. Mesh coordinates are
integers; the continuous reference uses the signed physical variables (u,-p).
"""

from fractions import Fraction as F
from itertools import combinations, product
from math import floor


def clip(value, lower, upper):
    return min(upper, max(lower, value))


class Market:
    def __init__(self, masses, supplies, offers, width, epsilon, step):
        self.width, self.epsilon, self.step = F(width), F(epsilon), F(step)
        self.g = tuple(map(F, masses)) + tuple(-F(c) for c in supplies)
        self.dimension = len(self.g)
        self.lower = (F(0),) * len(masses) + (-self.width,) * len(supplies)
        self.edges = [(i, len(masses) + j, F(b), F(d)) for i, j, b, d in offers]
        self.rho = self.step / self.epsilon
        self.q = 1 - self.step * self.epsilon
        self.bias = [((self.q - 1) * lo - self.step * g) / self.width
                     for lo, g in zip(self.lower, self.g)]
        self.beta = [self.rho * (b - self.lower[i] + d * self.lower[j]) / self.width
                     for i, j, b, d in self.edges]

        # Each list holds the incident edge shares, followed by self and leak.
        self.weights = [[] for _ in self.g]
        self.ports = []
        for i, j, _, d in self.edges:
            self.ports.append((len(self.weights[i]), len(self.weights[j])))
            self.weights[i].append(self.rho)
            self.weights[j].append(self.rho * d)
        for weights in self.weights:
            weights.extend([self.q - sum(weights), 1 - self.q])
            assert min(weights) >= 0 and sum(weights) == 1
        self.depth = max((len(w) - 1).bit_length() for w in self.weights)
        self.error_constant = ((2 * len(self.edges) + self.dimension) * self.depth
                               + len(self.edges) + self.dimension)

    def exact(self, z):
        h = [lo + self.width * x for lo, x in zip(self.lower, z)]
        residual = [g + self.epsilon * y for g, y in zip(self.g, h)]
        for i, j, b, d in self.edges:
            flow = max(0, b - h[i] + d * h[j]) / self.epsilon
            residual[i] -= flow
            residual[j] += flow
        return tuple(clip((y - self.step * r - lo) / self.width, 0, 1)
                     for y, r, lo in zip(h, residual, self.lower))

    def rounded(self, x, mesh):
        pieces = [split(count, weights) for count, weights in zip(x, self.weights)]
        out = [p[-2] + round(mesh * bias) for p, bias in zip(pieces, self.bias)]
        for (i, j, _, _), (ip, jp), beta in zip(self.edges, self.ports, self.beta):
            s, t = pieces[i][ip], pieces[j][jp]
            offset = round(mesh * beta)
            out[i] += max(s, offset + t)
            out[j] += min(t, s - offset)
        return tuple(clip(value, 0, mesh) for value in out)


def split(count, weights):
    """Recursively floor the left count and send its complement to the right."""
    if len(weights) == 1:
        return [count]
    total = sum(weights)
    if not total:
        assert count == 0
        return [0] * len(weights)
    middle = len(weights) // 2
    left, right = weights[:middle], weights[middle:]
    left_count = floor(count * sum(left) / total)
    return split(left_count, left) + split(count - left_count, right)


def kleene(mapping, dimension, mesh):
    point = (0,) * dimension
    for _ in range(mesh * dimension + 1):
        nxt = mapping(point)
        if nxt == point:
            return point
        assert all(a <= b <= mesh for a, b in zip(point, nxt))
        point = nxt
    raise AssertionError("ascending Kleene orbit exceeded the box height")


def check_covers(table, mesh):
    count = 0
    for x, output in table.items():
        for i, value in enumerate(x):
            if value < mesh:
                y = x[:i] + (value + 1,) + x[i + 1:]
                deltas = [b - a for a, b in zip(output, table[y])]
                assert min(deltas) >= 0 and sum(deltas) <= 1
                count += 1
    return count


def check_elimination(table, boundary, mesh, full_fixed):
    interior = tuple(v for v in range(len(full_fixed)) if v not in boundary)

    def lift(b, u):
        x = [0] * len(full_fixed)
        for indices, values in ((boundary, b), (interior, u)):
            for v, value in zip(indices, values):
                x[v] = value
        return tuple(x)

    reduced, lifted = {}, {}
    for b in product(range(mesh + 1), repeat=len(boundary)):
        def interior_map(u):
            output = table[lift(b, u)]
            return tuple(output[v] for v in interior)

        lifted[b] = lift(b, kleene(interior_map, len(interior), mesh))
        reduced[b] = tuple(table[lifted[b]][v] for v in boundary)
    assert lifted[kleene(reduced.__getitem__, len(boundary), mesh)] == full_fixed
    return check_covers(reduced, mesh)


def verify_box(market, mesh):
    table = {}
    max_error = F(0)
    for x in product(range(mesh + 1), repeat=market.dimension):
        table[x] = market.rounded(x, mesh)
        continuous = market.exact(tuple(F(v, mesh) for v in x))
        error = sum(abs(F(y, mesh) - f) for y, f in zip(table[x], continuous))
        assert error <= F(market.error_constant, mesh)
        max_error = max(max_error, error)
    covers = check_covers(table, mesh)
    fixed = kleene(table.__getitem__, market.dimension, mesh)
    for x, output in table.items():
        if x == output:
            assert all(a <= b for a, b in zip(fixed, x))
    reduced_covers = 0
    for size in range(1, market.dimension):
        for boundary in combinations(range(market.dimension), size):
            reduced_covers += check_elimination(table, boundary, mesh, fixed)
    return len(table), covers, reduced_covers, max_error, fixed


def check_one_offer(market):
    mesh = 16
    before, after = (0, 7), (1, 7)

    def coordinate_floor(x):
        exact = market.exact(tuple(F(v, mesh) for v in x))
        return tuple(floor(mesh * v) for v in exact)

    assert (coordinate_floor(before), coordinate_floor(after)) == ((0, 6), (1, 7))
    star = (F(1, 3), F(2, 3))
    assert market.exact(star) == star
    print("coordinate floor:", before, after, "map to", coordinate_floor(before),
          coordinate_floor(after))
    for mesh in (16, 128, 1024, 8192, 65536):
        fixed = kleene(lambda x: market.rounded(x, mesh), 2, mesh)
        z = tuple(F(v, mesh) for v in fixed)
        error = sum(abs(v - w) for v, w in zip(z, star))
        residual = sum(abs(v - w) for v, w in zip(z, market.exact(z)))
        assert (1 - market.q) * error <= residual <= F(market.error_constant, mesh)
        print(f"N={mesh}, integer least fixed point {fixed}, normalized l1 error {error}")


if __name__ == "__main__":
    single = Market([1], [1], [(0, 0, 2, 1)], 2, F(1, 2), F(1, 8))
    fixtures = [
        (single, 16),
        (Market([F(1, 2), 2], [F(3, 2)],
                [(0, 0, 1, F(1, 2)), (1, 0, 5, F(3, 2))],
                3, F(2, 3), F(1, 5)), 7),
        (Market([1, F(5, 4)], [2, F(1, 2)],
                [(0, 0, F(5, 2), F(1, 2)), (0, 1, 3, F(4, 3)),
                 (1, 0, 1, 2), (1, 1, F(7, 2), 1)],
                3, F(1, 2), F(1, 8)), 5),
        # Isolated nodes and a zero self share at the degree-two buyer.
        (Market([1, F(1, 2)], [1, 2, F(3, 4)],
                [(0, 0, 3, F(3, 2)), (0, 1, 1, F(1, 2))],
                2, 1, F(1, 3)), 3),
    ]
    for market, mesh in fixtures:
        points, covers, reduced, error, fixed = verify_box(market, mesh)
        print(f"D={market.dimension}, N={mesh}: {points} points, {covers} covers, "
              f"{reduced} reduced covers, max normalized l1 error {error}, "
              f"least fixed point {fixed}")
    check_one_offer(single)
