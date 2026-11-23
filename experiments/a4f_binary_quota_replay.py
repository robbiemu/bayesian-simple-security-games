"""Replay direct stable flow and exact recovery at large binary quotas.

The augmentations implement Cseh and Matuschke, Algorithm 1, using exact
rational capacities. Contract edges have separate vertices for each quote.
"""

from fractions import Fraction
from math import floor

from a4f_unit_tick_scaling import price_error_bound
from a4l_weighted_ordinal import solve as solve_equalities


def stable_flow(arcs, outgoing, incoming, source, sink):
    # Proposals progress from best to worst. After that, incoming refusals
    # progress from worst to best, traversing each such arc backwards.
    moves = [
        [(edge, 1) for edge in offers] + [(edge, -1) for edge in reversed(receipts)]
        for offers, receipts in zip(outgoing, incoming)
    ]
    cursor = [0] * len(moves)
    incoming_rank = {edge: rank for edges in incoming for rank, edge in enumerate(edges)}
    vertices = [v for v in range(len(moves)) if v != sink]
    flow = [Fraction(0)] * len(arcs)
    path_count = cycle_count = 0

    def residual(edge, direction):
        return arcs[edge][2] - flow[edge] if direction == 1 else flow[edge]

    def head_refuses(edge):
        head = arcs[edge][1]
        if head == sink or cursor[head] < len(outgoing[head]):
            return False
        if cursor[head] == len(moves[head]):
            return True
        refusal, _ = moves[head][cursor[head]]
        return incoming_rank[edge] >= incoming_rank[refusal]

    while True:
        advanced = True
        while advanced:
            advanced = False
            for v in vertices:
                while cursor[v] < len(moves[v]):
                    edge, direction = moves[v][cursor[v]]
                    if residual(edge, direction) > 0 and (direction == -1 or not head_refuses(edge)):
                        break
                    cursor[v] += 1
                    advanced = True

        if cursor[source] == len(moves[source]):
            assert path_count + cycle_count <= 2 * len(arcs)
            return flow, path_count, cycle_count

        # The current pointers give at most one continuation at every vertex.
        walk, seen = [], {}
        vertex = source
        while vertex != sink and vertex not in seen:
            seen[vertex] = len(walk)
            edge, direction = moves[vertex][cursor[vertex]]
            walk.append((edge, direction))
            tail, head, _ = arcs[edge]
            vertex = head if direction == 1 else tail
        if vertex == sink:
            path_count += 1
        else:
            walk = walk[seen[vertex]:]
            cycle_count += 1
        amount = min(residual(edge, direction) for edge, direction in walk)
        assert amount > 0
        for edge, direction in walk:
            flow[edge] += direction * amount


def check_stable_flow(arcs, outgoing, incoming, source, sink, flow):
    """Independently rule out all forward residual blocking walks."""
    assert all(0 <= quantity <= capacity for quantity, (_, _, capacity) in zip(flow, arcs))
    for v in range(len(outgoing)):
        if v not in (source, sink):
            assert sum(flow[e] for e in outgoing[v]) == sum(flow[e] for e in incoming[v])

    def preferred_to_used(edge, ranking):
        return any(flow[worse] > 0 for worse in ranking[ranking.index(edge) + 1:])

    residual = {e for e, (_, _, cap) in enumerate(arcs) if flow[e] < cap}
    active = [
        e for e in residual
        if arcs[e][0] == source or preferred_to_used(e, outgoing[arcs[e][0]])
    ]
    reached = set(active)
    for e in active:
        v = arcs[e][1]
        assert v != sink and not preferred_to_used(e, incoming[v])
        for next_edge in outgoing[v]:
            if next_edge in residual and next_edge not in reached:
                reached.add(next_edge)
                active.append(next_edge)


def contract_phase(bids, slopes, masses, capacities, lower, upper, tick):
    buyers, goods = len(masses), len(capacities)
    source, sink = 0, 1 + buyers + goods
    contracts = []
    for i in range(buyers):
        for j in range(goods):
            quote = lower[j]
            while quote <= upper[j]:
                utility = bids[i][j] - slopes[i][j] * quote
                if utility > 0:
                    contracts.append((i, j, quote, utility))
                quote += tick

    vertices = sink + 1 + len(contracts)
    outgoing = [[] for _ in range(vertices)]
    incoming = [[] for _ in range(vertices)]
    arcs = []

    def add_arc(tail, head, capacity):
        edge = len(arcs)
        arcs.append((tail, head, capacity))
        outgoing[tail].append(edge)
        incoming[head].append(edge)
        return edge

    for i, mass in enumerate(masses):
        add_arc(source, 1 + i, mass)
    for j, cap in enumerate(capacities):
        add_arc(1 + buyers + j, sink, cap)

    first_edges = []
    offer_rank, receipt_rank = {}, {}
    unbounded = sum(masses) + 1
    for offset, (i, j, quote, utility) in enumerate(contracts):
        relay = sink + 1 + offset
        first = add_arc(1 + i, relay, unbounded)
        last = add_arc(relay, 1 + buyers + j, unbounded)
        first_edges.append(first)
        offer_rank[first] = (-utility, j, quote)
        receipt_rank[last] = (-quote, i)
    for i in range(buyers):
        outgoing[1 + i].sort(key=offer_rank.__getitem__)
    for j in range(goods):
        incoming[1 + buyers + j].sort(key=receipt_rank.__getitem__)

    flow, paths, cycles = stable_flow(arcs, outgoing, incoming, source, sink)
    check_stable_flow(arcs, outgoing, incoming, source, sink, flow)
    purchases = [[Fraction(0)] * goods for _ in masses]
    used_quotes = [[] for _ in capacities]
    for (i, j, quote, _), first in zip(contracts, first_edges):
        if flow[first]:
            purchases[i][j] += flow[first]
            used_quotes[j].append(quote)
    marginals = [
        min(used_quotes[j]) if sum(row[j] for row in purchases) == cap else lower[j]
        for j, cap in enumerate(capacities)
    ]
    assert all(price < cap for price, cap in zip(marginals, upper))
    for i, row in enumerate(purchases):
        values = [bid - slope * p for bid, slope, p in zip(bids[i], slopes[i], marginals)]
        comparison = max([Fraction(0)] + [value - d * tick for value, d in zip(values, slopes[i])])
        assert all(not quantity or values[j] >= comparison for j, quantity in enumerate(row))
        if sum(row) < masses[i]:
            assert comparison == 0
    return marginals, purchases, paths, cycles


def check_clearance(bids, slopes, masses, capacities, prices, purchases):
    assert all(price >= 0 for price in prices)
    for i, row in enumerate(purchases):
        values = [bid - slope * price for bid, slope, price in zip(bids[i], slopes[i], prices)]
        best = max([Fraction(0)] + values)
        assert sum(row) <= masses[i]
        assert sum(row) == masses[i] or best == 0
        assert all(quantity >= 0 and (not quantity or value == best)
                   for quantity, value in zip(row, values))
    for j, cap in enumerate(capacities):
        sales = sum(row[j] for row in purchases)
        assert sales <= cap and (prices[j] == 0 or sales == cap)


def recover_from_support(bids, slopes, masses, capacities, purchases):
    # In this fixture the retained support and its outside anchor pin a square
    # system. The full recovery LP also covers every original unused offer.
    k, n = len(masses), len(capacities)
    assert all(sum(row[j] for row in purchases) == cap
               for j, cap in enumerate(capacities))
    equations = []
    for i, row in enumerate(purchases):
        if sum(row) < masses[i]:
            outside_anchor = [0] * (k + n + 1)
            outside_anchor[i] = 1
            equations.append(outside_anchor)
        for j, quantity in enumerate(row):
            if quantity:
                equation = [0] * (k + n + 1)
                equation[i], equation[k + j], equation[-1] = 1, slopes[i][j], bids[i][j]
                equations.append(equation)
    assert len(equations) == k + n
    solution = solve_equalities(equations)
    assert solution is not None and min(solution) >= 0
    recovered = list(solution[k:])
    check_clearance(bids, slopes, masses, capacities, recovered, purchases)
    return recovered


def replay_large_quotas(exponent):
    big = 1 << exponent
    bids = [[1, -1], [3, 6], [-1, 4]]
    slopes = [[Fraction(d) for d in row] for row in [[1, 1], [1, 2], [1, 1]]]
    masses = [big + Fraction(a, 7) for a in (5, 1, 4)]
    capacities = [big + Fraction(a, 7) for a in (3, 6)]
    expected = [Fraction(1), Fraction(2)]
    original = [[Fraction(4, 7), 0], [big - Fraction(1, 7), Fraction(2, 7)], [0, masses[2]]]
    check_clearance(bids, slopes, masses, capacities, expected, original)
    # At these prices all the viable offers are tight. Each positive-price set
    # has strictly more neighboring mass than stock, certifying the minimum.
    assert masses[0] + masses[1] > capacities[0]
    assert masses[1] + masses[2] > capacities[1]
    assert sum(masses) > sum(capacities)

    enlarged = [cap + Fraction(1, 28) for cap in capacities]
    error_bound = price_error_bound(bids, slopes)
    lower, upper = [Fraction(0)] * 2, [Fraction(4)] * 2
    tick = Fraction(4)
    paths = cycles = 0
    for _ in range(16):
        caps = [lo + (floor((hi - lo) / tick + error_bound) + 1) * tick
                for lo, hi in zip(lower, upper)]
        prices, purchases, path_count, cycle_count = contract_phase(
            bids, slopes, masses, enlarged, lower, caps, tick,
        )
        assert all(abs(p - q) <= error_bound * tick for p, q in zip(prices, expected))
        lower = [max(Fraction(0), p - error_bound * tick) for p in prices]
        upper = [p + error_bound * tick for p in prices]
        tick /= 2
        paths += path_count
        cycles += cycle_count
    assert recover_from_support(bids, slopes, masses, enlarged, purchases) == expected
    print(f"2^{exponent}-scale quotas: 16 stable-flow phases, {paths} paths and {cycles} cycles, exact prices (1, 2).")


def replay_helper_cycle():
    # The path/cycle example from Cseh and Matuschke, Fig. 2, at large capacities.
    scale = 1 << 100
    arcs = [(0, 1, 2 * scale), (0, 2, scale), (1, 2, 2 * scale),
            (1, 3, scale), (2, 3, scale)]
    outgoing = [[0, 1], [2, 3], [4], []]
    incoming = [[], [0], [1, 2], [3, 4]]
    flow, paths, cycles = stable_flow(arcs, outgoing, incoming, 0, 3)
    check_stable_flow(arcs, outgoing, incoming, 0, 3, flow)
    assert flow == [scale, scale, 0, scale, scale]
    assert (paths, cycles) == (2, 1)
    print("The stable-flow helper cycle replaces flow of 2^100 in one augmentation.")


if __name__ == "__main__":
    replay_helper_cycle()
    replay_large_quotas(80)
    replay_large_quotas(160)
