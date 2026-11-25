"""Exact checks for the A4m frozen map, max-norm interface, and cut-coordinate lift."""

from fractions import Fraction as F
from itertools import product

from a4j_unit_prices import check_certificate, demands_at, solve


def linear_solution(matrix, rhs):
    """Solve a nonsingular square system over the rationals."""
    rows = [[F(value) for value in row] + [F(value)] for row, value in zip(matrix, rhs)]
    size = len(rows)
    for j in range(size):
        pivot = next(i for i in range(j, size) if rows[i][j])
        rows[j], rows[pivot] = rows[pivot], rows[j]
        rows[j] = [value / rows[j][j] for value in rows[j]]
        for i in range(size):
            if i != j:
                factor = rows[i][j]
                rows[i] = [value - factor * other for value, other in zip(rows[i], rows[j])]
    return tuple(row[-1] for row in rows)


def market_map(h, bids, slopes, margins, epsilon, step, bounds):
    n = len(bids)
    residual = [g + epsilon * value for g, value in zip(margins, h)]
    for i, (row, rates) in enumerate(zip(bids, slopes)):
        for j, (bid, slope) in enumerate(zip(row, rates), n):
            flow = max(0, bid - h[i] + slope * h[j]) / epsilon
            residual[i] -= flow
            residual[j] += flow
    return tuple(max(lo, min(hi, v - step * r)) for v, r, (lo, hi) in
                 zip(h, residual, bounds))


def regularized_tree(bids, slopes, margins, epsilon, edges):
    matrix = []
    rhs = []
    for v in range(3):
        balance = [epsilon if v == i else F(0) for i in range(4)]
        balance += [-int(v == i) + int(v == j) for i, j in edges]
        matrix.append(balance)
        rhs.append(-margins[v])
    matrix.append([1, 1, 1, 1, 0, 0, 0])
    rhs.append(0)
    for k, (i, j) in enumerate(edges):
        row = [F(0)] * 7
        row[i], row[j], row[4 + k] = F(1), -slopes[i][j - 2], epsilon
        matrix.append(row)
        rhs.append(bids[i][j - 2])
    result = linear_solution(matrix, rhs)
    return result[:4], result[4:]


def check_local_formulas():
    slopes = ((F(1, 2), F(8)), (F(1, 2), F(4)))
    bids_a, bids_b = ((1, 50), (7, 23)), ((F(11, 2), 34), (1, 25))
    edges_a = ((0, 3), (1, 2), (1, 3))
    edges_b = ((0, 2), (0, 3), (1, 3))
    margins = (3, 3, -1, -5)
    trial = (6, 6, -6, -6)
    bounds = ((0, 20),) * 2 + ((-20, 0),) * 2
    for epsilon in (F(1, 100), F(1, 4096), F(1, 2**30)):
        step = epsilon / 16
        outputs = []
        signs = []
        for bids, tree in ((bids_a, edges_a), (bids_b, edges_b)):
            answer, flows = regularized_tree(bids, slopes, margins, epsilon, tree)
            assert all(flow > 0 for flow in flows)
            for i, j in product(range(2), range(2, 4)):
                assert bids[i][j - 2] - trial[i] + slopes[i][j - 2] * trial[j] < 0
                if (i, j) not in tree:
                    assert bids[i][j - 2] - answer[i] + slopes[i][j - 2] * answer[j] < 0
            assert market_map(answer, bids, slopes, margins, epsilon, step, bounds) == answer
            error = tuple(a - b for a, b in zip(answer, trial))
            assert abs(error[0]) > max(map(abs, error[1:]))
            assert sum(answer) == sum(trial)
            signs.append(error[0] > 0)
            outputs.append(market_map(trial, bids, slopes, margins, epsilon, step, bounds))
        assert outputs[0] == outputs[1] and signs == [True, False]
    print("Local oracle: identical replies, different active trees, opposite unique signs")


def check_separate_coordinates():
    bids = ((2, 2), (2, 3))
    slopes = ((F(1), F(1)), (F(1), F(2)))
    margins = (1, 1, -1, -1)
    bounds = ((0, 5),) * 2 + ((-5, 0),) * 2
    # Signed-coordinate order for the comparison is (buyer 1, good 1, buyer 2, good 2).
    increase = (8, 10, 9, 6)
    for epsilon in (F(1, 8), F(1, 64), F(1, 1024)):
        t = epsilon**2
        u1, p1, u2, p2 = linear_solution(
            ((1 + t, 1, 0, 0), (0, 1 + t, 1, 0), (0, 0, 1 + t, 2), (1, 0, 0, 1 + t)),
            (2 - epsilon, 2 - epsilon, 3 - epsilon, 2 - epsilon))
        bases = (u1, u2, -p1, -p2)
        step, tau = epsilon / 16, epsilon / 512
        for row, (i, j) in ((0, (0, 2)), (2, (1, 2)), (1, (1, 3)), (3, (0, 3))):
            start = [4, 4, -4, -4]
            start[i], start[j] = bases[i], bases[j]
            end = start.copy()
            for v in (i, j):
                end[v] += tau * increase[v]
            for value in (start, end):
                active = {(i0, j0) for i0, j0 in product(range(2), range(2, 4))
                          if bids[i0][j0 - 2] - value[i0] + slopes[i0][j0 - 2] * value[j0] > 0}
                assert active == {(i, j)}
            before = market_map(start, bids, slopes, margins, epsilon, step, bounds)
            after = market_map(end, bids, slopes, margins, epsilon, step, bounds)
            assert before[row] == bases[row]
            assert after[row] - before[row] > tau * increase[row]
    print("Separate coordinates: four expanding row comparisons at three regularizations")


def cut_vector(h):
    return tuple(sum(h[i] for i in range(len(h)) if mask & (1 << i))
                 for mask in range(1 << len(h)))


def lift(cuts, bids, slopes, margins, epsilon, step, bounds):
    rho, decay = step / epsilon, 1 - step * epsilon
    n = len(bids)
    outputs = []
    for mask, own in enumerate(cuts):
        allocated = F(0)
        total = -step * sum(g for i, g in enumerate(margins) if mask & (1 << i))
        for i, j in product(range(n), range(n, len(margins))):
            j_col = j - n
            slope, bid = slopes[i][j_col], bids[i][j_col]
            buyer, good = 1 << i, 1 << j
            if mask & buyer and not mask & good:
                total += rho * max((1 + slope) * own,
                                   bid + cuts[mask ^ buyer] + slope * cuts[mask | good])
            elif mask & good and not mask & buyer:
                total += rho * min((1 + slope) * own,
                                   -bid + cuts[mask | buyer] + slope * cuts[mask ^ good])
            else:
                continue
            allocated += rho * (1 + slope)
        assert allocated <= decay
        outputs.append(total + (decay - allocated) * own)
    for i, (lo, hi) in enumerate(bounds):
        bit = 1 << i
        outputs = [max(outputs[mask ^ bit] + lo, min(outputs[mask ^ bit] + hi, value))
                   if mask & bit else value for mask, value in enumerate(outputs)]
    return tuple(outputs)


def check_cut_lift():
    bids, slopes = ((2, 2), (2, 3)), ((F(1), F(1)), (F(1), F(2)))
    margins, epsilon, step = (1, 1, -1, -1), F(1, 4), F(1, 64)
    bounds = ((0, 2),) * 2 + ((-2, 0),) * 2
    parameters = bids, slopes, margins, epsilon, step, bounds
    for h in product((0, 1, 2), (0, 1, 2), (-2, -1, 0), (-2, -1, 0)):
        assert lift(cut_vector(h), *parameters) == cut_vector(market_map(h, *parameters))
    print("Cut lift: exact agreement on 81 physical cut vectors")


def check_frozen_boundary():
    bids = ((1, -20), (9, 9), (-20, 9))
    slopes = ((F(1), F(1)), (F(3, 2), F(1, 2)), (F(1), F(1)))
    uniform = [[F(1)] * 2 for _ in bids]
    # Taking one option per good gives a dual bound of one on this fixture.
    for j in range(2):
        errors = [slopes[i][j] - 1 for i in range(len(bids)) if bids[i][j] > 0]
        assert max(map(abs, errors)) == F(1, 2)
        assert max(abs(first - second) for first, second in product(errors, repeat=2)) == F(1, 2)
    def frozen_solve(trial):
        adjusted = [[F(b) - (s - 1) * p for b, s, p in zip(row, rates, trial)]
                    for row, rates in zip(bids, slopes)]
        prices, matching, _ = solve(adjusted, uniform)
        check_certificate(adjusted, uniform, prices, matching, exhaustive=True)
        return tuple(prices), matching, demands_at(adjusted, uniform, prices)[2]

    for trial, expected in (((0, 0), (1, 1)), ((1, 1), (1, 2)), ((1, 3), (1, 3))):
        assert frozen_solve(trial)[0] == expected
    print("Frozen assignment: certified boundary factor one and exact least price (1, 3)")

    delta = F(1, 2**30)
    trial = (1, 3 - 2 * delta)
    frozen, matching, demand = frozen_solve(trial)
    assert frozen == (1, 3 - delta)
    assert max(abs(p - t) for p, t in zip(frozen, trial)) == delta
    assert demand[0] == {-1, 0} and demand[1] == {0, 1}

    # Preserve the outside tie and the two-good tie in the original slopes.
    repaired = linear_solution(((slopes[0][0], 0), (slopes[1][0], -slopes[1][1])),
                               (bids[0][0], bids[1][0] - bids[1][1]))
    assert repaired == (1, 3)
    assert demands_at(bids, slopes, repaired)[2] == demand
    check_certificate(bids, slopes, repaired, matching, exhaustive=True)

    # Both goods also sell at the higher prices with this same matching.
    higher = (2, 7)
    _, _, higher_demand = demands_at(bids, slopes, higher)
    assert all(good in higher_demand[buyer] for buyer, good in matching.items())
    assert set(matching.values()) == {-1, 0, 1}
    assert sum(bool(choices & {0, 1}) for choices in higher_demand) == 2
    print("Tie repair: positive residual 2^-30, least price (1, 3), higher clearing price (2, 7)")



if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to keep the exact checks enabled.")
    check_local_formulas()
    check_separate_coordinates()
    check_cut_lift()
    check_frozen_boundary()
