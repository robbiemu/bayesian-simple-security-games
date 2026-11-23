"""Check rational price-contract phases using small token reference allocations."""

from collections import Counter, deque
from fractions import Fraction as F
from math import floor
from random import Random
from a4j_unit_prices import solve, check_certificate
from a4f_unit_tick_scaling import price_error_bound


def min_prices_by_cloning(bids, slopes, buyer_num, good_num):
    n = len(good_num)
    orig_i = [i for i, m in enumerate(buyer_num) for _ in range(m)]
    orig_j = [j for j, c in enumerate(good_num) for _ in range(c)]
    p = [F(0)] * n
    if orig_j:
        bs = [[bids[i][j] for j in orig_j] for i in orig_i]
        ds = [[slopes[i][j] for j in orig_j] for i in orig_i]
        cp, ass, _ = solve(bs, ds)
        check_certificate(bs, ds, cp, ass)
        for j, t in zip(orig_j, cp):
            p[j] = t
        assert all(p[j] == t for j, t in zip(orig_j, cp))
    u = [max([F(0)] + [bs[j] - ds[j] * p[j] for j, c in enumerate(good_num) if c]) for bs, ds in zip(bids, slopes)]
    for j, c in enumerate(good_num):
        if not c:
            p[j] = max([F(0)] + [(bs[j] - u[i]) / ds[j] for i,(bs,ds) in enumerate(zip(bids,slopes))])
    return p


def contract_rx(bids, slopes, floor_prices, upper, ticks, mua, cap, buyer_proposes):
    n, k = len(upper), len(bids)
    contracts = []
    for i in range(k):
        for j in range(n):
            t = floor_prices[j]
            while t <= upper[j]:
                utility = bids[i][j] - slopes[i][j]*t
                if utility > 0:
                    contracts.append((i,j,t,utility))
                t += ticks
    # Individual token simulations only for finite verification; the proof instead calls a rational-capacity stable-flow algorithm.
    from_num, to_num = (mua,cap) if buyer_proposes else (cap,mua)
    orders = [[] for _ in from_num]
    offered_to, payoff, priority = [], [], []
    for edge,(i,j,t,v) in enumerate(contracts):
        s,r = (i,j) if buyer_proposes else (j,i)
        orders[s].append(edge)
        offered_to.append(r)
        # Fixed strict tie resolution per endpoint.
        payoff.append((v,-j,-edge) if buyer_proposes else (t,-i,-edge))
        priority.append((t,-i,-edge) if buyer_proposes else (v,-j,-edge))
    for s in range(len(from_num)):
        orders[s].sort(key=lambda e: payoff[e], reverse=True)
    token_type = [s for s, num in enumerate(from_num) for _ in range(num)]
    ptr = [0]*len(token_type)
    waiting = deque(range(len(token_type)))
    residents = [[] for _ in to_num]
    while waiting:
        token = waiting.popleft()
        opts = orders[token_type[token]]
        if ptr[token] == len(opts):
            continue
        e = opts[ptr[token]]
        ptr[token] += 1
        r = offered_to[e]
        pool = residents[r]
        pool.append((priority[e],-token,e,token))
        if len(pool) > to_num[r]:
            bad = min(pool)
            pool.remove(bad)
            waiting.append(bad[-1])
    used = Counter(x[2] for pool in residents for x in pool)
    col = [[] for _ in range(n)]
    row = [[] for _ in range(k)]
    for e,amount in used.items():
        i,j,t,v = contracts[e]
        col[j].append((t,amount))
        row[i].append((j,t,v,amount))
    result = [min(t for t,a in col[j]) if sum(a for t,a in col[j]) == cap[j] else floor_prices[j] for j in range(n)]
    assert all(q < hi for q,hi in zip(result,upper))
    for i in range(k):
        options = [bids[i][j]-slopes[i][j]*result[j] for j in range(n)]
        bound_rhs = max([F(0)] + [w-slopes[i][j]*ticks for j,w in enumerate(options)])
        if sum(a for _,_,_,a in row[i]) < mua[i]:
            assert F(0) >= bound_rhs
        for j,t,v,amount in row[i]:
            assert options[j] >= bound_rhs
    return result, len(contracts)


if __name__ == "__main__":
    rng = Random(20261122)
    cases = phases = ncontracts = zero_count = fraction_count = 0
    max_err = F(0)
    for _ in range(100):
        k,n = rng.randrange(1,5),rng.randrange(1,4)
        g = rng.randrange(1,5)
        mua = [rng.randrange(1,4) for i in range(k)]
        cap = [rng.randrange(0,3) for j in range(n)]
        zero_count += 0 in cap
        fraction_count += any(c % g for c in cap + mua)
        bids = [[F(rng.randrange(-1,7), rng.randrange(1,3)) for j in range(n)] for i in range(k)]
        slopes = [[F(rng.randrange(3,6),3) for j in range(n)] for i in range(k)]
        star = min_prices_by_cloning(bids,slopes,mua,cap)
        c = price_error_bound(bids, slopes)
        maxima = [max([F(0)]+[bids[i][j]/slopes[i][j] for i in range(k)]) for j in range(n)]
        for proposer in (True,False):
            l = [F(0)]*n
            u = list(maxima)
            delta = F(1)
            while delta < max(u):
                delta *= 2
            for t in range(7):
                assert all(a <= p <= z for a,z,p in zip(l,u,star))
                top = [a + (floor((z-a)/delta+c)+1)*delta for a,z in zip(l,u)]
                bm = [m*4*n for m in mua]
                cm = [x*4*n+1 for x in cap]   # Physical m/g and c/g + 1/(4ng).
                p, ne = contract_rx(bids,slopes,l,top,delta,bm,cm,proposer)
                ratio=max(abs(v-q)/delta for v,q in zip(star,p))
                assert ratio <= c
                max_err = max(max_err,ratio)
                ncontracts += ne
                l = [max(F(0),q-c*delta) for q in p]
                u = [q+c*delta for q in p]
                delta /= 2
                phases += 1
        cases += 1
    print(f"{cases} rational markets ({zero_count} with zero capacity, {fraction_count} with fractional quantities), {phases} stable-contract phases (each proposer side), {ncontracts} total positive contracts, maximum price error / mesh {max_err}")
