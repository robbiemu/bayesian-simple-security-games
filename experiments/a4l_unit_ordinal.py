"""Check the strict ordinal matching construction and unit minimum prices."""

from itertools import combinations, permutations, product
from fractions import Fraction
from random import Random


def half_witness_and_stability(a, b, match):
    n = len(a)
    held_a = [a[i][j] if j is not None else 0 for i, j in enumerate(match)]
    held_b = [0] * len(b[0])
    for i, j in enumerate(match):
        if j is not None:
            held_b[j] = b[i][j]
    stable = True
    clearing = True
    for i in range(n):
        for j in range(len(held_b)):
            if not a[i][j]:
                continue
            aa, bb = a[i][j], b[i][j]
            stable &= (held_a[i] >= aa or held_b[j] >= bb)
            cover = held_a[i] * bb + held_b[j] * aa
            if match[i] == j:
                assert cover == 2 * aa * bb
            clearing &= cover >= 2 * aa * bb
    return stable, clearing


def complete_profiles(n):
    a_values = tuple(permutations(4 ** r for r in range(1, n + 1)))
    matchings = tuple(permutations(range(n)))
    profiles = tested = stable_count = 0
    for rows in product(a_values, repeat=n):
        for columns in product(a_values, repeat=n):
            b = tuple(zip(*columns))
            stables = []
            for matching in matchings:
                stable, clearing = half_witness_and_stability(rows, b, matching)
                assert stable == clearing
                tested += 1
                if stable:
                    stables.append(matching)
            assert stables
            opt = [m for m in stables if all(rows[i][m[i]] >= rows[i][p[i]] for p in stables for i in range(n))]
            assert len(opt) == 1
            stable_count += len(stables)
            profiles += 1
    return profiles, tested, stable_count


def determinants(rows):
    if len(rows) == 2:
        (a, b), (c, d) = rows
        return a*d - b*c
    (a,b,c), (d,e,f), (g,h,i) = rows
    return a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g)


def clearing_vertices(a, b, matching):
    # Each inequality is z.p >= r, with integer-normalized coefficients.
    n = len(a)
    rows = []
    for i, g in enumerate(matching):
        row = [0] * n
        row[g] = 1
        rows.append((tuple(row), 0))
        row[g] = -1
        rows.append((tuple(row), -b[i][g]))
        for j in range(n):
            if j == g:
                continue
            row = [0] * n
            row[j] = a[i][j] * b[i][g]
            row[g] = -a[i][g] * b[i][j]
            rhs = (a[i][j] - a[i][g]) * b[i][j] * b[i][g]
            rows.append((tuple(row), rhs))
    result = set()
    for chosen in combinations(rows, n):
        a_mat, rhs = zip(*chosen)
        den = determinants(a_mat)
        if not den:
            continue
        nums = [determinants([row[:j] + (value,) + row[j+1:] for row, value in zip(a_mat, rhs)]) for j in range(n)]
        if den < 0:
            nums = [-x for x in nums]
            den = -den
        if all(sum(z*x for z,x in zip(zs, nums)) >= r*den for zs,r in rows):
            result.add(tuple(Fraction(x, den) for x in nums))
    return result


def exact_minimum(a, b):
    n = len(a)
    ordinals = []
    feasible = {}
    for m in permutations(range(n)):
        st, _ = half_witness_and_stability(a, b, m)
        if st:
            ordinals.append(m)
        vertices = clearing_vertices(a, b, m)
        assert st == bool(vertices)
        for p in vertices:
            feasible.setdefault(p, set()).add(m)
    best = min(feasible, key=sum)
    assert all(all(x<=y for x,y in zip(best, candidate)) for candidate in feasible)
    optimal, = [m for m in ordinals if all(a[i][m[i]] >= a[i][h[i]] for i in range(n) for h in ordinals)]
    assert feasible[best] == {optimal}
    return len(feasible)


def sampled_minima():
    rng = Random(20261122)
    vertices = cases = 0
    for words in product((0,1), repeat=4):
        family = ((4,16),(16,4))
        a = tuple(family[t] for t in words[:2])
        b = tuple(zip(*(family[t] for t in words[2:])))
        vertices += exact_minimum(a,b)
        cases += 1
    for _ in range(50):
        n = 3
        # Adjacent ratios vary by agent and between consecutive choices.
        def rank_values():
            values = [rng.randrange(1,8)]
            for _ in range(n-1):
                values.append(rng.randint(3,6)*values[-1]+rng.randint(0,2))
            rng.shuffle(values)
            return values
        a = [rank_values() for _ in range(n)]
        b = tuple(zip(*(rank_values() for _ in range(n))))
        vertices += exact_minimum(a,b)
        cases += 1
    # No a priori uniform ratio bound: 7/10 and 7/10 appear, on disjoint edges.
    a = [[10,7,1],[1,20,4],[8,1,32]]
    b = [[2,10,1],[7,2,16],[10,3,4]]
    for i in range(3):
        for j in range(3):
            av, bv = a[i][j], b[i][j]
            ra = max([Fraction(x,av) for x in a[i] if x < av] + [0])
            rb = max([Fraction(row[j],bv) for row in b if row[j] < bv] + [0])
            assert ra+rb < 1
    vertices += exact_minimum(a,b)
    cases += 1
    return cases, vertices


if __name__ == '__main__':
    print('Complete n=3 profiles, tested perfect matchings, stable witnesses', *complete_profiles(3))
    print('Exact unit-market minima and distinct feasible support vertices', *sampled_minima())
