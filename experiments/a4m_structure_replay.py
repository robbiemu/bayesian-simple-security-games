"""Exact examples for A4m conditional quadratic programs and cut circuits."""

from fractions import Fraction as Q
from itertools import combinations, product
from random import Random

from a4m_lattice_replay import Market, clip
from a4m_maxnorm_replay import cut_vector


def subsets(items):
    return [tuple(x for i, x in enumerate(items) if mask & (1 << i))
            for mask in range(1 << len(items))]


def level(star, point, sigma, t):
    """Direct scalar solution by independently sorting the breakpoints z/f."""
    sign, entries = star
    items = [(b - sign * e * point[i], f) for i, b, e, f in entries]
    total, rate, y = -sigma, t, Q(0)
    for z, f in sorted(items, key=lambda item: item[0] / item[1], reverse=True):
        total, rate = total + z, rate + f
        y = max(y, total / rate)
    load = sum(max(Q(0), z - f * y) for z, f in items)
    assert load <= sigma + t * y and (y == 0 or load == sigma + t * y)
    return y


class ReducedCutCircuit:
    def __init__(self, masses, capacities, offers, cover):
        self.buyers = len(masses)
        self.g = tuple(map(Q, masses)) + tuple(-Q(c) for c in capacities)
        self.offers = [(i, self.buyers + j, Q(b), Q(d)) for i, j, b, d in offers]
        self.cover = tuple(cover)
        self.size = len(self.cover)
        self.width, self.eps, self.step = Q(16), Q(1, 4), Q(1, 128)
        self.market = Market(masses, capacities, offers, self.width, self.eps, self.step)
        self.t, self.rho = self.eps**2, self.step / self.eps
        self.q = 1 - self.step * self.eps
        self.indices = {v: k for k, v in enumerate(cover)}
        self.stars, self.internal = {}, []
        for v in range(len(self.g)):
            if v not in self.indices:
                self.stars[v] = (-1 if v < self.buyers else 1, [])
        for i, j, b, d in self.offers:
            if i in self.indices and j in self.indices:
                self.internal.append((self.indices[i], self.indices[j], b, d))
            elif i in self.indices:
                self.stars[j][1].append((self.indices[i], b, Q(1), d))
            else:
                assert j in self.indices
                self.stars[i][1].append((self.indices[j], b, d, Q(1)))
        self.bound = self.size * self.width
        self.rows = [self.compile_row(mask) for mask in range(1 << self.size)]

    def bounds(self, v):
        return (Q(0), self.width) if v < self.buyers else (-self.width, Q(0))

    def reference(self, point):
        """Apply the full physical node map after independent interior clearing."""
        h = [Q(0)] * len(self.g)
        for v, x in zip(self.cover, point):
            h[v] = x
        for v, star in self.stars.items():
            unsigned = level(star, point, self.eps * abs(self.g[v]), self.t)
            h[v] = unsigned if v < self.buyers else -unsigned
        lower = self.market.lower
        normalized = tuple((value - lo) / self.width for value, lo in zip(h, lower))
        updated = tuple(lo + self.width * value for lo, value in zip(lower, self.market.exact(normalized)))
        assert all(updated[v] == h[v] for v in self.stars)
        return tuple(updated[v] for v in self.cover), tuple(h)

    def atom(self, own, cap, offset, changes):
        """Give each nonnegative level-set difference its independent cut input."""
        weights = [cap if own & (1 << i) else Q(0) for i in range(self.size)]
        for i, change in changes:
            weights[i] += change
        assert all(0 <= w <= cap for w in weights)
        levels = sorted(set(weights) | {Q(0)})
        terms = tuple((sum(1 << i for i, w in enumerate(weights) if w >= hi), hi - lo)
                      for lo, hi in zip(levels, levels[1:]))
        assert sum(w for _, w in terms) <= cap
        return offset, terms

    def compile_row(self, mask):
        groups, allocated = [], Q(0)
        for v, (sign, entries) in self.stars.items():
            if not entries:
                continue
            cap = self.rho * max(e for _, _, e, _ in entries)
            allocated += cap
            inside = [entry for entry in entries if mask & (1 << entry[0])]
            outside = [entry for entry in entries if not mask & (1 << entry[0])]
            sigma = self.eps * abs(self.g[v])
            outer = []
            for picked in subsets(inside):
                pick_b = sum((b for _, b, _, _ in picked), Q(0))
                pick_f = sum((f for _, _, _, f in picked), Q(0))
                choices = [self.atom(mask, cap, sign * self.rho * pick_b,
                                     [(i, -self.rho * e) for i, _, e, _ in picked])]
                for opposed in subsets(outside):
                    opp_b = sum((b for _, b, _, _ in opposed), Q(0))
                    opp_f = sum((f for _, _, _, f in opposed), Q(0))
                    denominator = pick_f + opp_f + self.t
                    wt = (opp_f + self.t) / denominator
                    wv = pick_f / denominator
                    offset = sign * self.rho * (wt * pick_b - wv * opp_b + wv * sigma)
                    changes = ([(i, -self.rho * e * wt) for i, _, e, _ in picked]
                               + [(i, self.rho * e * wv) for i, _, e, _ in opposed])
                    choices.append(self.atom(mask, cap, offset, changes))
                outer.append(choices)
            groups.append((sign, outer))
        for i, j, bid, slope in self.internal:
            sign = int(bool(mask & (1 << i))) - int(bool(mask & (1 << j)))
            if not sign:
                continue
            cap = self.rho * max(1, slope)
            allocated += cap
            unused = self.atom(mask, cap, Q(0), [])
            active = self.atom(mask, cap, sign * self.rho * bid,
                               [(i, -sign * self.rho), (j, sign * self.rho * slope)])
            groups.append((sign, [[unused], [active]]))
        assert allocated <= self.q
        offset = -self.step * sum(self.g[v] for k, v in enumerate(self.cover) if mask & (1 << k))
        return offset, self.q - allocated, groups

    def lift(self, cuts):
        result = []
        for mask, (offset, remaining, groups) in enumerate(self.rows):
            value = offset + remaining * cuts[mask]
            for sign, outer in groups:
                lower, upper = (min, max) if sign > 0 else (max, min)
                value += upper(lower(c + sum(w * cuts[s] for s, w in terms)
                                     for c, terms in choices) for choices in outer)
            result.append(value)
        for i, v in enumerate(self.cover):
            lo, hi = self.bounds(v)
            bit = 1 << i
            result = [clip(x, result[mask ^ bit] + lo, result[mask ^ bit] + hi)
                      if mask & bit else x for mask, x in enumerate(result)]
        return tuple(clip(x, -self.bound, self.bound) for x in result)


def fixture_a():
    return ReducedCutCircuit([Q(3, 2), 2, Q(5, 3), Q(3, 4)], [Q(4, 3), 2, 0, Q(7, 4)],
                  [(0, 0, Q(5, 2), Q(3, 2)), (1, 1, 2, Q(1, 2)),
                   (2, 0, 4, 2), (2, 1, 3, Q(1, 2)), (3, 0, Q(1, 3), 2),
                   (0, 2, 4, Q(3, 2)), (1, 2, 5, Q(2, 3)),
                   (0, 3, Q(2, 3), Q(5, 4)), (1, 3, 4, 3)], (0, 1, 4, 5))


def fixture_b():
    """Build a second mixed cover from a known rational regularized solution."""
    u, p, eps = (Q(2, 3), Q(7, 4), Q(4, 3)), (Q(6, 5), Q(5, 4), Q(3, 2)), Q(1, 4)
    flows = ((0, 0, 1, Q(3, 4)), (0, 2, 2, Q(3, 2)), (1, 2, Q(3, 2), Q(5, 4)),
             (2, 0, Q(2, 3), Q(2, 3)), (2, 1, Q(3, 2), Q(7, 4)))
    offers = [(i, j, u[i] + d * p[j] + eps * x, d) for i, j, x, d in flows]
    offers += [(1, 1, Q(1, 8), Q(1, 2))]
    masses = [sum(x for i, _, x, _ in flows if i == k) - eps * u[k] for k in range(3)]
    caps = [sum(x for _, j, x, _ in flows if j == k) - eps * p[k] for k in range(3)]
    return ReducedCutCircuit(masses, caps, offers, (0, 1, 3, 4)), u + tuple(-x for x in p)


def check(market, seed):
    rng, physical, off_image = Random(seed), 0, 0
    for magnitudes in product((0, 2, 4, 16), repeat=market.size):
        point = tuple(Q(n if v < market.buyers else -n) for n, v in zip(magnitudes, market.cover))
        expected, _ = market.reference(point)
        assert market.lift(cut_vector(point)) == cut_vector(expected)
        physical += 1
    for k in range(128):
        cuts = tuple(Q(rng.randint(-64, 64), 2) for _ in market.rows)
        direction = tuple(Q(rng.randrange(8) if k % 2 else rng.randrange(-5, 6), 8)
                          for _ in market.rows)
        other = tuple(v + d for v, d in zip(cuts, direction))
        fst, snd = market.lift(cuts), market.lift(other)
        assert max(abs(a - b) for a, b in zip(fst, snd)) <= market.q * max(map(abs, direction))
        if k % 2:
            assert all(a <= b for a, b in zip(fst, snd))
        assert all(abs(v) <= market.bound for v in fst + snd)
        off_image += 1
    return physical, off_image


def balanced_on_vertices(offers, interior):
    weights = {}
    neighbors = {v: [] for v in interior}
    for i, j, _, slope in offers:
        if i in neighbors and j in neighbors:
            neighbors[i].append((j, slope))
            neighbors[j].append((i, 1 / slope))
    for root in interior:
        if root in weights:
            continue
        weights[root] = Q(1)
        stack = [root]
        while stack:
            u = stack.pop()
            for v, ratio in neighbors[u]:
                if v in weights:
                    if weights[v] != ratio * weights[u]:
                        return False
                else:
                    weights[v] = ratio * weights[u]
                    stack.append(v)
    return True


def check_balanced_interior():
    width, epsilon, step = Q(8), Q(1, 2), Q(1, 32)
    bids = ((4, 7, 1), (8, 4, Q(1, 4)), (2, Q(9, 4), Q(1, 2)))
    slopes = ((2, 5, 1), (7, 3, 6), (3, 2, 4))
    market = Market((1, Q(7, 4), 2), (1, 3, 2),
                    [(i, j, bids[i][j], slopes[i][j])
                     for i, j in product(range(3), repeat=2)], width, epsilon, step)
    inside = (1, 2, 4, 5)
    weights = dict(zip(inside, map(Q, (2, 3, 6, 12))))
    vertices = tuple(range(6))
    assert balanced_on_vertices(market.edges, inside)
    assert not any(balanced_on_vertices(market.edges, s) for s in combinations(vertices, 5))
    # The ordinary cover number of K_3,3 is 3, by the three diagonal edges.
    signed = tuple(map(Q, (1, Q(1, 2), 0, -1, -1, 0)))
    lower = market.lower
    upper = tuple(x + width for x in lower)
    z = tuple((value - lo) / width for value, lo in zip(signed, lower))
    applied = tuple(lo + width * value for lo, value in zip(lower, market.exact(z)))
    assert applied == (Q(69, 64), Q(1, 2), 0, Q(-67, 64), -1, 0)
    gradient = {v: weights[v] * (market.g[v] + epsilon * signed[v]) for v in inside}
    residual = [g + epsilon * h for g, h in zip(market.g, signed)]
    flows = []
    for i, j, bid, slope in market.edges:
        flow = max(0, bid - signed[i] + slope * signed[j]) / epsilon
        flows.append(flow)
        residual[i] -= flow
        residual[j] += flow
        if i not in weights and j not in weights:
            continue
        scale = weights[i] if i in weights else weights[j] / slope
        if i in weights:
            gradient[i] -= scale * flow
        if j in weights:
            assert scale * slope == weights[j]
            gradient[j] += scale * slope * flow
    assert flows == [2, 2, 0, 1, 1, 0, 0, Q(1, 2), 1]
    assert tuple(gradient.values()) == (0, Q(3, 2), 0, -12)
    for v in inside:
        assert gradient[v] == weights[v] * residual[v]
        assert gradient[v] == 0 or (signed[v] == lower[v] and gradient[v] > 0) or (
            signed[v] == upper[v] and gradient[v] < 0)
    print("Mixed boundary (1,-1), residual weights", tuple(weights.values()),
          "unique conditional optimizer", tuple(signed[v] for v in inside),
          "weighted KKT gradient", tuple(gradient.values()),
          "boundary image", (applied[0], applied[3]))


def check_block_gluing():
    # The first four offers form an unbalanced K2,2. The next four form a
    # balanced K2,2 at the shared articulation Y. The last two reach pins.
    offers = (
        ("a", "X", 3, 1), ("a", "Y", 2, 1),
        ("b", "X", 2, 1), ("b", "Y", Q(5, 2), 2),
        ("c", "Y", Q(5, 4), Q(3, 2)), ("c", "Z", Q(1, 2), 3),
        ("d", "Y", 1, 1), ("d", "Z", 2, 2),
        ("b", "W", Q(5, 2), 3), ("e", "Z", Q(3, 2), 5),
    )
    vertices = ("a", "b", "c", "d", "X", "Y", "Z")
    scale = dict(zip(vertices, map(Q, (5, 7, 6, 4, 6, 4, 2))))
    signed = dict(zip(vertices, map(Q, (1, Q(1, 2), 0, 1, -1, Q(-1, 2), 0))))
    signed.update({"e": Q(1), "W": Q(-1, 2)})
    eps, width = Q(1, 2), Q(6)
    g = dict(zip(vertices, map(Q, (Q(5, 2), Q(15, 4), 3, Q(3, 2),
                                   Q(-5, 2), Q(-15, 4), -5))))
    active, unresolved = offers[:4], offers[4:]
    zlo = {v: (Q(0) if v.islower() else -width) / scale[v] for v in vertices}
    z = {v: signed[v] / scale[v] for v in vertices}
    shift = {v: z[v] - zlo[v] for v in vertices}
    boxwidth = {v: width / scale[v] for v in vertices}
    upper = {v: Q(v == "Z") for v in vertices}

    laplacian = {(v, w): Q(0) for v, w in product(vertices, repeat=2)}
    for i, j, _, d in active:
        for v, a in ((i, 1), (j, -1)):
            laplacian[v, i] += a * scale[i]
            laplacian[v, j] -= a * d * scale[j]
    assert all(sum(laplacian[v, w] for w in vertices) == 0 for v in vertices)
    assert all(sum(laplacian[v, w] for v in vertices) == 0 for w in vertices)
    assert all(laplacian[v, w] <= 0 for v, w in laplacian if v != w)
    assert [scale[i] - d * scale[j] for i, j, _, d in active] == [-1, 1, 1, -1]

    residual = {v: g[v] + eps * signed[v] for v in vertices}
    node_slack = {v: g[v] + eps * scale[v] * (zlo[v] + shift[v]) + upper[v]
                  for v in vertices}
    trade, trade_slack = [], []
    for e, (i, j, bid, d) in enumerate(offers):
        raw = bid - signed[i] + d * signed[j]
        flow = max(Q(0), raw) / eps
        if i in residual:
            residual[i] -= flow
        if j in residual:
            residual[j] += flow
        if e < len(active):
            assert raw > 0
            for v, sign in ((i, 1), (j, -1)):
                node_slack[v] += sign * (scale[i] * z[i] - d * scale[j] * z[j] - bid) / eps
            continue
        incident = [(v, sign) for v, sign in ((i, 1), (j, -1)) if v in scale]
        k = scale[i] if i in scale else d * scale[j]
        if i in scale and j in scale:
            assert k == d * scale[j]
        shifted_bid = bid - (signed[i] if i not in scale else 0) + (
            d * signed[j] if j not in scale else 0)
        constraint = eps * flow / k - shifted_bid / k + sum(a * z[v] for v, a in incident)
        for v, a in incident:
            node_slack[v] -= a * flow
        trade.append(flow)
        trade_slack.append(constraint)
    assert tuple(residual.values()) == (0, 0, 1, 0, 0, 0, -1)
    assert tuple(node_slack.values()) == (0, 0, 1, 0, 0, 0, 0)
    assert trade == [1, 1, 0, 2, 1, 1]
    assert trade_slack == [0, 0, Q(1, 8), 0, 0, 0]
    pairs = list(zip(shift.values(), node_slack.values())) + list(zip(trade, trade_slack))
    pairs.extend((upper[v], boxwidth[v] - shift[v]) for v in vertices)
    assert all(a >= 0 and b >= 0 and a * b == 0 for a, b in pairs)
    print("Glued scales", tuple(scale.values()), "signed solution", tuple(signed[v] for v in vertices),
          "LCP complementarity pairs", len(pairs), "convex quadratic gap", sum(a * b for a, b in pairs))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to retain exact assertions.")
    check_balanced_interior()
    check_block_gluing()
    m1, (m2, h) = fixture_a(), fixture_b()
    print("mixed covers (physical grid, independent proposal pairs):", check(m1, 19), check(m2, 41))
    reduced = tuple(h[v] for v in m2.cover)
    cuts = cut_vector(reduced)
    assert m2.reference(reduced) == (reduced, h)
    assert m2.lift(cuts) == cuts
    approx = tuple(Q(round(x * 2**36), 2**36) for x in cuts)
    residual = max(abs(x-y) for x, y in zip(approx, m2.lift(approx)))
    assert 0 < residual / (1-m2.q) < Q(1, 2 * 100**2)
    decoded = tuple(approx[1 << i].limit_denominator(100) for i in range(m2.size))
    assert m2.reference(decoded) == (reduced, h)
    print("mixed-cover fixed point and rational reconstruction:", h, "residual", residual)
