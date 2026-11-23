"""Exact checks for the post-PR 8 unit-market endpoint certificates."""

from collections import defaultdict, deque
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from itertools import permutations, product
from math import prod
from random import Random
from a4j_unit_prices import solve


def label_profiles(rng, cases=360):
    profiles = compatible = maxima_checked = 0
    for _ in range(cases):
        k, n = rng.randint(1, 4), rng.randint(1, 4)
        aa = [tuple(sorted({Q(1), Q(rng.randint(1, 4))})) for i in range(k)]
        cc = [tuple(sorted({Q(1), Q(rng.randint(1, 4))})) for j in range(n)]
        d = [[rng.choice(cc[j]) / rng.choice(aa[i]) for j in range(n)] for i in range(k)]
        b = [[Q(rng.randint(-2, 7), rng.randint(1, 2)) for j in range(n)] for i in range(k)]
        p, _, _ = solve(b, d)
        u = [max([0] + [b[i][j] - d[i][j] * p[j] for j in range(n)]) for i in range(k)]
        matchings = [
            m for m in product(range(-1, n), repeat=k)
            if len([j for j in m if j >= 0]) == len({j for j in m if j >= 0})
            and all(j < 0 or b[i][j] > 0 for i, j in enumerate(m))
        ]

        def supports(m):
            return all(
                (u[i] == 0 if j < 0 else b[i][j] - d[i][j] * p[j] == u[i])
                for i, j in enumerate(m)
            ) and all(pj == 0 or j in m for j, pj in enumerate(p))

        winners = {m for m in matchings if supports(m)}
        assert winners
        recovered = False
        for a in product(*aa):
            for c in product(*cc):
                profiles += 1
                allowed = [
                    m for m in matchings
                    if all(j < 0 or a[i] * d[i][j] == c[j] for i, j in enumerate(m))
                ]
                if not winners.intersection(allowed):
                    continue
                compatible += 1
                weights = [sum(a[i] * b[i][j] for i, j in enumerate(m) if j >= 0) for m in allowed]
                best = max(weights)
                maxima = [m for m, v in zip(allowed, weights) if v == best]
                assert set(maxima) <= winners
                maxima_checked += len(maxima)
                recovered = True
        assert recovered
    print("mixed labels", cases, profiles, compatible, maxima_checked)


def box_check(b, d, lo, hi):
    size = len(b)
    perms = list(permutations(range(size)))

    def value(m, p):
        return sum(b[i][j] - d[i][j] * p[j] for i, j in enumerate(m))

    mid = [(l + h) / 2 for l, h in zip(lo, hi)]
    candidate = max(perms, key=lambda v: value(v, mid))
    inverse = {j: i for i, j in enumerate(candidate)}
    gain = [
        [
            b[i][j] - b[inverse[j]][j]
            + max((d[inverse[j]][j] - d[i][j]) * t for t in (lo[j], hi[j]))
            for j in range(size)
        ]
        for i in range(size)
    ]
    calculated = max(sum(gain[i][j] for i, j in enumerate(other)) for other in perms)
    corners = list(product(*[sorted({l, h}) for l, h in zip(lo, hi)]))
    direct = max(value(other, p) - value(candidate, p) for p in corners for other in perms)
    assert calculated == direct
    at_corners = []
    for p in corners:
        vals = {m: value(m, p) for m in perms}
        best = max(vals.values())
        at_corners.append({m for m, v in vals.items() if v == best})
    assert (calculated == 0) == bool(set.intersection(*at_corners))
    return calculated == 0


def random_boxes(rng, cases=80):
    universal = 0
    for _ in range(cases):
        k, n = rng.randint(1, 2), rng.randint(1, 3)
        s = k + n
        b = [
            [Q(rng.randint(-1, 8)) if i < k and j < n else Q(0) for j in range(s)]
            for i in range(s)
        ]
        d = [
            [Q(rng.randint(1, 4)) if i < k and j < n else Q(1 if j < n else 0) for j in range(s)]
            for i in range(s)
        ]
        lo = [Q(rng.randint(0, 1)) if j < n else Q(0) for j in range(s)]
        hi = [lo[j] + Q(rng.randint(0, 4)) if j < n else Q(0) for j in range(s)]
        universal += box_check(b, d, lo, hi)
    print("box criterion", cases, universal)


def minimum_cut_source_side(arcs, source, sink):
    """Small integer max-flow replay for the label cut."""
    residual = defaultdict(dict)
    for tail, head, capacity in arcs:
        residual[tail][head] = residual[tail].get(head, 0) + capacity
        residual[head].setdefault(tail, 0)

    while True:
        predecessor = {source: None}
        queue = deque([source])
        while queue and sink not in predecessor:
            tail = queue.popleft()
            for head, capacity in residual[tail].items():
                if capacity > 0 and head not in predecessor:
                    predecessor[head] = tail
                    queue.append(head)
        if sink not in predecessor:
            return set(predecessor)

        path = []
        head = sink
        while head != source:
            tail = predecessor[head]
            path.append((tail, head))
            head = tail
        amount = min(residual[tail][head] for tail, head in path)
        for tail, head in path:
            residual[tail][head] -= amount
            residual[head][tail] += amount


def check_label_cut(slopes):
    rows, columns = len(slopes), len(slopes[0])
    residual_edges = [
        ((i, slope), (rows + j, slope))
        for i, row in enumerate(slopes)
        for j, slope in enumerate(row)
        if slope != 1
    ]
    labels = set(label for edge in residual_edges for label in edge)
    if not labels:
        return
    groups = [[label for label in labels if label[0] == v] for v in range(rows + columns)]
    source, sink = "source", "sink"
    arcs = []
    product_bound = 1 << (2 * len(residual_edges))
    scale = 16 * (len(groups) + 1) * product_bound * (len(residual_edges) + 1) ** 2
    with localcontext() as context:
        context.prec = scale.bit_length() + 10
        for v, group in enumerate(groups):
            size = len(group)
            if not size:
                continue
            counts = range(size + 1) if v < rows else range(size, -1, -1)
            logs = [int((Decimal(count + 1).ln() * scale).to_integral_value())
                    for count in counts]
            increments = [b - a for a, b in zip(logs, logs[1:])]
            last = increments[-1]
            if last >= 0:
                arcs.extend((label, sink, last) for label in group)
            else:
                arcs.extend((source, label, -last) for label in group)
            for t in range(1, size):
                auxiliary = ("auxiliary", v, t)
                weight = increments[t - 1] - increments[t]
                assert weight > 0
                arcs.extend((label, auxiliary, weight) for label in group)
                arcs.append((auxiliary, sink, t * weight))

    prohibit = 1 + sum(capacity for _, _, capacity in arcs)
    arcs.extend((right, left, prohibit) for left, right in residual_edges)
    side = minimum_cut_source_side(arcs, source, sink)
    selected = {
        label for label in labels if (label in side) == (label[0] < rows)
    }

    def cover_product(chosen):
        if any(left not in chosen and right not in chosen for left, right in residual_edges):
            return None
        return prod(1 + sum(label in chosen for label in group) for group in groups)

    label_order = sorted(labels)
    feasible_products = []
    for flags in product((False, True), repeat=len(label_order)):
        chosen = {label for label, take in zip(label_order, flags) if take}
        value = cover_product(chosen)
        if value is not None:
            feasible_products.append(value)
    assert cover_product(selected) == min(feasible_products)


def replay_label_cuts():
    generator = Random(795781)
    for _ in range(80):
        slopes = [[Q(generator.choice((1, 2, 3, 4))) for _ in range(3)] for _ in range(2)]
        check_label_cut(slopes)
    print("Compared 80 multiplier-product cuts with exhaustive residual covers.")


if __name__ == "__main__":
    generator = Random(802417)
    label_profiles(generator)
    random_boxes(generator)
    replay_label_cuts()
