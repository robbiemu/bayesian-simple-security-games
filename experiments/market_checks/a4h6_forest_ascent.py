"""Compare A4h6 price jumps with exact arrangement enumeration on 240 seeded two-good markets."""

from collections import deque
from fractions import Fraction as Q
from itertools import combinations
from random import Random


def demands(b, d, p):
    result = []
    for bi, di in zip(b, d):
        offers = [a - s * t for a, s, t in zip(bi, di, p)] + [Q(0)]
        u = max(offers)
        result.append((u, {j for j, value in enumerate(offers) if value == u}))
    return result


def augmented(m, c, d, support):
    k = len(m)
    n = len(c)
    end = k + n + 1
    edges = []
    for i, cap in enumerate(m):
        edges.append((0, 1 + i, cap, Q(1), None))
    for i, S in enumerate(support):
        edges.extend((1 + i, 1 + k + j, sum(m), d[i][j], (i, j)) for j in S)
    for j, cap in enumerate(c):
        edges.append((1 + k + j, end, cap, Q(1), None))
    flow = [Q(0)] * len(edges)
    while True:
        adj = [[] for _ in range(end + 1)]
        for i, (a, b, cap, cost, _) in enumerate(edges):
            if flow[i] < cap:
                adj[a].append((b, cap - flow[i], cost, i, 1))
            if flow[i] > 0:
                adj[b].append((a, flow[i], 1 / cost, i, -1))
        labels = [None] * (end + 1)
        labels[0] = Q(1)
        for _ in range(end):
            for a, outgoing in enumerate(adj):
                if labels[a] is None:
                    continue
                for b, _, cost, _, _ in outgoing:
                    z = labels[a] * cost
                    if labels[b] is None or z < labels[b]:
                        labels[b] = z
        if labels[end] is None:
            break
        parents = {0: None}
        todo = deque([0])
        while todo and end not in parents:
            a = todo.popleft()
            for b, cap, cost, i, s in adj[a]:
                if b not in parents and labels[a] * cost == labels[b]:
                    parents[b] = (a, cap, i, s)
                    todo.append(b)
        assert end in parents
        path = []
        t = end
        while t:
            step = parents[t]
            path.append(step)
            t = step[0]
        amount = min(step[1] for step in path)
        for _, _, i, s in path:
            flow[i] += s * amount
    assert sum(flow[-n:]) == sum(c)
    a = {i: Q(1) for i in range(k) if flow[i] < m[i]}
    v = {}
    used = [
        tag for idx, (*_, tag) in enumerate(edges) if tag is not None and flow[idx] > 0
    ]
    for _ in range(k + n):
        for i, j in used:
            if i in a:
                v[j] = a[i] / d[i][j]
            if j in v:
                a[i] = d[i][j] * v[j]
    assert len(v) == n and len(a) == k
    for i, S in enumerate(support):
        assert all(a[i] <= d[i][j] * v[j] for j in S)
    return v


def arrangement_minimum(b, d, m, c):
    ceilings = [max(bi[j] / di[j] for bi, di in zip(b, d)) for j in range(2)]
    lines = {(Q(1), Q(0), Q(0)), (Q(0), Q(1), Q(0))}
    for bi, di in zip(b, d):
        lines.update(
            [(di[0], -di[1], bi[0] - bi[1]), (di[0], 0, bi[0]), (0, di[1], bi[1])]
        )
    out = []
    for (a, b1, c1), (d1, e, f) in combinations(lines, 2):
        det = a * e - b1 * d1
        if not det:
            continue
        p = ((c1 * e - b1 * f) / det, (a * f - c1 * d1) / det)
        if any(x < 0 or x > h for x, h in zip(p, ceilings)):
            continue
        dom = demands(b, d, p)
        if all(
            sum(mi for mi, (_, s) in zip(m, dom) if s <= S) <= sum(c[j] for j in S)
            for S in ({0}, {1}, {0, 1})
        ):
            out.append(p)
    assert out
    p = min(out, key=sum)
    assert all(x <= q for cand in out for x, q in zip(p, cand))
    return p


def run(b, d, m, c):
    target = arrangement_minimum(b, d, m, c)
    p = (Q(0), Q(0))
    steps = 0
    while True:
        dom = demands(b, d, p)
        options = []
        for S in (set(), {0}, {1}, {0, 1}):
            I = [i for i, (_, s) in enumerate(dom) if s <= S]
            options.append((sum(m[i] for i in I) - sum(c[j] for j in S), S, I))
        D, S, I = max(options, key=lambda item: (item[0], -len(item[1])))
        if D == 0:
            assert p == target, (p, target, b, d, m, c)
            return steps
        J = sorted(S)
        local_d = [[d[i][j] for j in J] for i in I]
        support = [{l for l, j in enumerate(J) if j in dom[i][1]} for i in I]
        delta = Q(1, 8)
        v0 = augmented([m[i] for i in I], [c[j] + delta for j in J], local_d, support)
        v = [v0[J.index(j)] if j in S else Q(0) for j in range(2)]
        z = [
            min(d[i][j] * v[j] for j in dom[i][1]) if i in I else Q(0)
            for i in range(len(m))
        ]
        ratios = []
        for i, (u, _) in enumerate(dom):
            if u > 0 and z[i] > 0:
                ratios.append(u / z[i])
            for j in range(2):
                slack = u + d[i][j] * p[j] - b[i][j]
                velocity = z[i] - d[i][j] * v[j]
                if velocity > 0:
                    assert slack > 0
                    ratios.append(slack / velocity)
        assert ratios
        step = min(ratios)
        p = tuple(p[j] + step * v[j] for j in range(2))
        assert all(x <= q for x, q in zip(p, target)), (p, target, b, d, m, c)
        steps += 1
        assert steps < 100


rng = Random(6276)
hist = []
for _ in range(240):
    k = rng.randrange(1, 6)
    b = [[Q(rng.randrange(0, 10)) for _ in range(2)] for _ in range(k)]
    d = [
        [rng.choice([Q(1, 2), Q(1), Q(2), Q(3), Q(5, 2)]) for _ in range(2)]
        for _ in range(k)
    ]
    m = [Q(rng.randrange(1, 8), 2) for _ in range(k)]
    c = [Q(rng.randrange(0, 9), 2) for _ in range(2)]
    hist.append(run(b, d, m, c))
print(
    f"Exact ascent matched arrangement enumeration on {len(hist)} rational markets, including all intermediate no-overshoot tests. Longest run: {max(hist)} jumps."
)
