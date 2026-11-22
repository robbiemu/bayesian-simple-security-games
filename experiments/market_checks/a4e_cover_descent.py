"""Compare the A4e descent rule with exact vertex enumeration on 48 seeded two-by-two markets."""

from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from random import Random


def solve(equations, n):
    matrix = [[F(a) for a in row] + [F(rhs)] for row, rhs in equations]
    for i in range(n):
        pivot = next((j for j in range(i, n) if matrix[j][i]), None)
        if pivot is None:
            return None
        matrix[i], matrix[pivot] = matrix[pivot], matrix[i]
        diagonal = matrix[i][i]
        matrix[i] = [v / diagonal for v in matrix[i]]
        for j in range(n):
            if j != i and matrix[j][i]:
                factor = matrix[j][i]
                matrix[j] = [v - factor * w for v, w in zip(matrix[j], matrix[i])]
    return tuple(row[-1] for row in matrix)


def dot(a, b):
    return sum(v * w for v, w in zip(a, b))


def vertices(rows):
    out = set()
    for basis in combinations(rows, 4):
        point = solve(basis, 4)
        if (
            point is not None
            and point not in out
            and all(dot(a, point) >= v for a, v in rows)
        ):
            out.add(point)
    return out


nonnegative = [(tuple(int(i == j) for j in range(4)), 0) for i in range(4)]
pairs = list(product(range(2), repeat=2))


def cover(d, b):
    return nonnegative + [
        (
            tuple(int(i == h) for h in range(2))
            + tuple(d[2 * i + j] * int(j == h) for h in range(2)),
            b[2 * i + j],
        )
        for i, j in pairs
    ]


def allocation(m, c):
    return (
        nonnegative
        + [(tuple(-int(i == h) for i, j in pairs), -m[h]) for h in range(2)]
        + [(tuple(-int(j == h) for i, j in pairs), -c[h]) for h in range(2)]
    )


def clear(z, x, m, c, d, b):
    u, p = z[:2], z[2:]
    return (
        all(not x[e] or u[i] + d[e] * p[j] == b[e] for e, (i, j) in enumerate(pairs))
        and all(not u[i] or x[2 * i] + x[2 * i + 1] == m[i] for i in range(2))
        and all(not p[j] or x[j] + x[j + 2] == c[j] for j in range(2))
    )


rng = Random(408796)
maximum = 0
for rep in range(48):
    m = tuple(F(rng.randint(1, 6), 2) for h in range(2))
    c = tuple(F(rng.randint(1, 7), 2) for h in range(2))
    d = tuple(F(rng.randint(1, 8), rng.randint(1, 4)) for h in range(4))
    b = tuple(F(rng.randint(-2, 12), 2) for h in range(4))
    C = vertices(cover(d, b))
    X = vertices(allocation(m, c))
    start = tuple(max(0, b[2 * i], b[2 * i + 1]) for i in range(2)) + (F(0), F(0))
    assert start in C
    z = start
    last = None
    for step in range(len(C) + 1):
        p = z[2:]
        bids = tuple(b[e] - (d[e] - 1) * p[j] for e, (i, j) in enumerate(pairs))
        frozen = vertices(cover((1, 1, 1, 1), bids))
        dual = min(frozen, key=lambda v: (dot(m + c, v), v))
        signs = tuple((dual[j + 2] > p[j]) - (dual[j + 2] < p[j]) for j in range(2))
        base = max(dot(bids, x) for x in X)
        primary = [x for x in X if dot(bids, x) == base]
        denominator = lcm(*(v.denominator for x in primary for v in x))

        def second(x):
            value = F(1)
            for e, (i, j) in enumerate(pairs):
                value *= d[e] ** int(-signs[j] * x[e] * denominator)
            return value

        x = max(primary, key=lambda x: (second(x), x))
        gap = dot(m + c, z) - base
        assert gap >= 0 and (last is None or gap < last)
        if not gap:
            assert clear(z, x, m, c, d, b)
            maximum = max(maximum, step)
            break
        last = gap
        weights = tuple(
            c[j] + sum((d[2 * i + j] - 1) * x[2 * i + j] for i in range(2))
            for j in range(2)
        )
        z = min(C, key=lambda v: (dot(m + weights, v), v))
    else:
        raise AssertionError(rep)
print(
    f"Exact 2×2 vertex enumeration verified strict descent and clearing on 48 rational markets. Maximum updates {maximum}."
)
