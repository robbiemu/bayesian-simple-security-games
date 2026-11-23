"""Compare ordinal stability to exact affine support feasibility on a small grid."""

from fractions import Fraction as F
from itertools import combinations, product


def solve(rows):
    n = len(rows)
    rows = [[F(v) for v in row] for row in rows]
    for k in range(n):
        pivot = next((i for i in range(k, n) if rows[i][k]), None)
        if pivot is None:
            return None
        rows[k], rows[pivot] = rows[pivot], rows[k]
        rows[k] = [v/rows[k][k] for v in rows[k]]
        for i in range(n):
            if i != k and rows[i][k]:
                fac = rows[i][k]
                rows[i] = [v - fac*w for v, w in zip(rows[i], rows[k])]
    return tuple(row[-1] for row in rows)


def cover_faces(a, b):
    rows = []
    for e in range(4):
        row = [0]*5
        row[e//2], row[2+e%2], row[-1] = b[e], a[e], a[e]*b[e]
        rows.append(row)
    for v in range(4):
        row = [0]*5
        row[v] = 1
        rows.append(row)
    masks = []
    for base in combinations(rows, 4):
        q = solve(base)
        if q is None:
            continue
        val = [sum(x*y for x,y in zip(row,q)) - row[-1] for row in rows]
        if min(val) >= 0:
            masks.append(sum(1 << k for k,z in enumerate(val) if not z))
    return masks


def verify_flow(a, b, q, x, cover_masks):
    ends = ((0,2),(0,3),(1,2),(1,3))
    capacities = [q[v] for v in range(4)]
    for e, (i,j) in enumerate(ends):
        capacities[i] -= x[e]
        capacities[j] -= x[e]
    if min(capacities) < 0:
        return None
    floor = [min(((a[e] if v<2 else b[e],e) for e,edge in enumerate(ends) if v in edge and x[e]), default=(0,None)) if capacities[v]==0 else (0,None) for v in range(4)]
    ord_stable = all(floor[i][0]>=a[e] or floor[j][0]>=b[e] for e,(i,j) in enumerate(ends))
    mask = sum(1 << e for e in range(4) if x[e]) + sum(1 << (4+v) for v,w in enumerate(capacities) if w)
    supp_feasible = any(mask & ~face == 0 for face in cover_masks)
    assert ord_stable == supp_feasible
    if not ord_stable:
        return False, False, False
    rows = []
    for v, (_,e) in enumerate(floor):
        row = [0]*5
        row[v] = 1
        if e is None:
            rows.append(row)
            continue
        i,j = ends[e]
        w = i if v==j else j
        if floor[w][1] == e:
            r = max([F(a[k],a[e]) for k in range(4) if k//2==e//2 and a[k]<a[e]]+[0])
            s = max([F(b[k],b[e]) for k in range(4) if k%2==e%2 and b[k]<b[e]]+[0])
            t = F(r+1-s,2)
            row[-1] = t if v==i else 1-t
        else:
            row[w] = F(floor[w][0], a[e] if w==i else b[e])
            row[-1] = 1
        rows.append(row)
    z = solve(rows)
    assert z and all(0<=coord<=1 for coord in z)
    quotes = [w*value for (w,_), value in zip(floor,z)]
    slack = [quotes[i]*b[e]+quotes[j]*a[e]-a[e]*b[e] for e,(i,j) in enumerate(ends)]
    assert all(not sl if amount else sl>0 for sl,amount in zip(slack,x))
    assert all(not open_cap or not value for open_cap,value in zip(capacities,quotes))
    split = sum(bool(v) for v in x)>=3
    is_cycle = all(x) and all(not v for v in capacities) and all(floor[i][1]!=floor[j][1] for i,j in ends)
    return True, split, is_cycle


def run():
    total = feasible = stable = split = cycle = 0
    for aa,bb,cc,dd in product(((4,16),(16,4)), repeat=4):
        a = aa+bb
        b = cc[:1]+dd[:1]+cc[1:]+dd[1:]
        masks = cover_faces(a,b)
        for quota in product((2,3),repeat=4):
            # Units of one half, so physical quotas are 1 or 3/2.
            for amounts in product(range(4), repeat=4):
                total += 1
                result = verify_flow(a,b,quota,amounts,masks)
                if result is None:
                    continue
                feasible += 1
                stable += result[0]
                split += result[1]
                cycle += result[2]
    return total, feasible, stable, split, cycle


if __name__=='__main__':
    print('Candidates, feasible, ordinal stable = affine clearable, split, nonmutual four-cycle', *run())
