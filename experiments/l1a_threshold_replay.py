#!/usr/bin/env python3
"""Exact L1a replay for the padded two-gain family. Uses only the Python standard library."""

from fractions import Fraction as Q
from math import lcm
import sys


def base_data(h):
    """Return the padded recursive network, row masses, and complete cost matrix."""
    n = 2 * h + 2
    F = 2 ** h
    D = 4 * F - 3
    S = (n - 2) * F
    P = 8 * D * F + 1
    K = 16 * P * F * (D + n * F)
    edges = [(0, 1, 1, 0)]
    for i in range(1, h + 1):
        s, t = (2 * i, 2 * i + 1)
        old_s, old_t = (2 * i - 2, 2 * i - 1)
        cap = 2 ** (i - 1)
        A = 2 ** i - 1
        edges.extend([
            (s, old_s, cap, 0),
            (old_t, t, cap, 0),
            (s, old_t, cap, A),
            (old_s, t, cap, A),
        ])
    rows = []
    cost = []
    O = [0] * n
    for a, b, m, c in edges:
        O[a] += m
        allowed = [P] * n
        allowed[a] = 0
        allowed[b] = c
        cost.append(allowed)
        rows.append(m)
    s, t = (2 * h, 2 * h + 1)
    for j in range(n):
        if j in (s, t) or O[j] == F:
            continue
        allowed = [P] * n
        allowed[j] = 0
        cost.append(allowed)
        rows.append(F - O[j])
    allowed = [P] * n
    allowed[t] = 0
    cost.append(allowed)
    rows.append(K)
    assert sum(rows) == K + F + S
    return n, F, P, K, s, t, rows, cost


def reflow(p, Demand, kappa, oldz, B, mu):
    """Saturate column lower bounds with a unit reward on their first slots."""
    nr, nc = (len(p), len(kappa))
    A = [[] for _ in range(nr + nc + 2)]
    s = nr + nc
    t = s + 1
    N = t + 1
    lo = [mu * kappa[j] if j in B else oldz[j] for j in range(nc)]
    hi = [mu * kappa[j] for j in range(nc)]
    den = lcm(*[v.denominator for v in lo + hi])

    def add(i, j, w, c):
        e = len(A[i])
        r = len(A[j])
        A[i].append([j, r, w, c])
        A[j].append([i, e, 0, -c])
        return e

    ptr = {}
    for i, m in enumerate(p):
        add(s, i, m * den, 0)
        for j in sorted(Demand[i]):
            ptr[i, j] = add(i, nr + j, m * den, 0)
    slots = []
    for j in range(nc):
        slots.append(add(nr + j, t, int(lo[j] * den), -1))
        add(nr + j, t, int((hi[j] - lo[j]) * den), 0)
    sent = 0
    total = sum(p) * den
    while sent < total:
        prev = [None] * N
        dist = [None] * N
        dist[s] = 0
        for _ in range(N - 1):
            change = False
            for a, adj in enumerate(A):
                if dist[a] is None:
                    continue
                for e, (b, rev, cap, c) in enumerate(adj):
                    if cap > 0 and (dist[b] is None or dist[b] > dist[a] + c):
                        dist[b] = dist[a] + c
                        prev[b] = (a, e)
                        change = True
            if not change:
                break
        assert dist[t] is not None
        v = t
        m = total - sent
        while v != s:
            a, e = prev[v]
            m = min(m, A[a][e][2])
            v = a
        v = t
        while v != s:
            a, e = prev[v]
            rv = A[a][e][1]
            A[a][e][2] -= m
            A[v][rv][2] += m
            v = a
        sent += m
    assert all(A[nr + j][slots[j]][2] == 0 for j in range(nc))
    f = [[Q(0) for _ in range(nc)] for _ in p]
    for (i, j), e in ptr.items():
        f[i][j] = Q(p[i] * den - A[i][e][2], den)
    return f


def replay(h):
    """Replay the exact first eligible seed, using the identity logarithmic optimizer."""
    n, F, P, K, s, t, p, ct = base_data(h)
    R = len(p)
    tab = [[(4 * P if j != s else 0) - row[j] for j in range(n)] for row in ct]
    X = [Q(0)] * n
    q = [[Q(0) for _ in range(n)] for _ in p]
    cap = Q(8 * n * P)
    budget = cap
    for i in range(R):
        q[i][tab[i].index(max(tab[i]))] = Q(p[i])
    kappa = [K if j in (s, t) else F for j in range(n)]
    lo = Q(1)
    hi = 1 + (F - Q(1, 2)) / K
    expected = set(range(n)) - {s}
    drops = []
    suc = 0
    while sum(X) < budget:
        z = [sum((r[j] for r in q)) for j in range(n)]
        score = [z[j] / kappa[j] for j in range(n)]
        lam = max(score)
        B = {j for j in range(n) if score[j] == lam}
        assert max(X) < cap
        if lo <= lam <= hi:
            assert B == expected
        v = [max((tab[i][j] - X[j] for j in range(n))) for i in range(R)]
        Di = [{j for j in range(n) if tab[i][j] - X[j] == v[i]} for i in range(R)]
        for i, row in enumerate(q):
            assert sum(row) == p[i]
            assert all(not row[j] or j in Di[i] for j in range(n))
        for b in sorted(B):
            Sj = {b}
            Ui = set()
            frontier = {b}
            while frontier:
                newrows = {i for i in range(R) if any((q[i][j] for j in frontier))} - Ui
                Ui.update(newrows)
                frontier = set().union(*(Di[i] for i in newrows)) - Sj
                Sj.update(frontier)
            if Sj <= B:
                break
        else:
            mu = max([Q(0)] + [score[j] for j in range(n) if j not in B])
            # For these small replays, enumerate the upper Hall inequalities directly.
            masks = [sum(1 << j for j in Di[i]) for i in range(R)]
            for mask in range(1, 1 << n):
                demand = sum(m for i, m in enumerate(p) if masks[i] & mask == masks[i])
                kk = sum(kappa[j] for j in range(n) if mask & 1 << j)
                mu = max(mu, Q(demand, kk))
            assert mu < lam, (mu, lam)
            f = reflow(p, Di, kappa, z, B, mu)
            nz = [sum((row[j] for row in f)) for j in range(n)]
            after = {j for j in range(n) if nz[j] == kappa[j] * mu}
            drops.append((lam, mu, B, after))
            q = f
            continue
        dt = min((budget - sum(X)) / len(Sj), min((cap - X[j] for j in Sj)))
        times = [v[i] - (tab[i][j] - X[j]) for i in Ui for j in range(n) if j not in Sj]
        if times:
            dt = min(dt, min(times))
        assert dt > 0
        for j in Sj:
            X[j] += dt
        suc += 1
    windows = [[] for _ in range(F - 1)]
    for _, new, B, after in drops:
        landing = (new - 1) * K
        if B == after == expected:
            for j in range(1, F):
                if abs(landing - j) < Q(1, 4):
                    windows[j - 1].append(landing)
    assert all(windows)
    fixed_drops = sum(before == after == expected for _, _, before, after in drops)
    print(
        f"h={h}, successful steps={suc}, Algorithm 4 calls={len(drops)}, "
        f"fixed-boundary drops={fixed_drops}, "
        f"witness landings={sum(len(window) for window in windows)}"
    )


if __name__ == "__main__":
    for h in (map(int, sys.argv[1:]) if len(sys.argv) > 1 else (1, 2, 3, 4)):
        replay(h)
