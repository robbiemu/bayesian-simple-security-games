"""Replay the exact certificates and Hall comparisons in the two A4i records."""

from bisect import bisect_left
from fractions import Fraction as Q

from a4h9_hybrid_examples import check_strict_hall
from clearing_replay_checks import check_clearance


def check_market(masses, capacity, price, sales):
    offers = {0: {"good": (5, 2)}, 1: {"good": (4, 1)}}
    masses = dict(enumerate(masses))
    capacities = {"good": capacity}
    prices = {"good": price}
    allocation = {
        buyer: {"good": sale, None: masses[buyer] - sale}
        for buyer, sale in enumerate(sales)
    }
    check_clearance(offers, masses, capacities, prices, allocation)
    check_strict_hall(offers, masses, capacities, prices)


def defender_scores(coverage, priors, gains, intercepts, slopes, attacks):
    """Validate exact mutual best responses at a one-resource coverage."""
    assert sum(coverage) == sum(priors) == 1
    assert all(0 <= value <= 1 for value in coverage)
    assert all(prior > 0 for prior in priors)
    assert len(coverage) == len(gains)
    assert all(gain > 0 for gain in gains)
    assert len(priors) == len(intercepts) == len(slopes) == len(attacks)

    for prior, bids, losses, row in zip(priors, intercepts, slopes, attacks):
        assert len(coverage) == len(bids) == len(losses) == len(row)
        assert all(loss > 0 for loss in losses)
        assert sum(row) == prior and all(mass >= 0 for mass in row)
        utilities = [bid - loss * x for bid, loss, x in zip(bids, losses, coverage)]
        best = max(utilities)
        assert all(mass == 0 or utility == best for mass, utility in zip(row, utilities))

    scores = tuple(gain * sum(column) for gain, column in zip(gains, zip(*attacks)))
    least_covered = min(score for score, x in zip(scores, coverage) if x > 0)
    greatest_available = max((score for score, x in zip(scores, coverage) if x < 1), default=0)
    assert least_covered >= greatest_available
    return scores


def check_uniform_priors(masses, capacity, price, sales):
    prior = Q(1, 3)
    gamma = prior / (1 + sum(masses))
    private = [prior - gamma * mass for mass in masses]
    good_coverage = price / 15
    private_coverages = (Q(2, 7), Q(7, 36))
    pad_coverage = 1 - good_coverage - sum(private_coverages)
    attacks = (
        (gamma * sales[0], gamma * (masses[0] - sales[0]), 0, private[0], 0),
        (gamma * sales[1], 0, 0, 0, private[1]),
        (0, 0, prior, 0, 0),
    )
    scores = defender_scores(
        (good_coverage, 0, pad_coverage, *private_coverages),
        (prior,) * 3,
        (1 / (gamma * capacity), Q(1, 2), 1 / prior, 1 / private[0], 1 / private[1]),
        ((5, 0, -2, 6, -2), (4, 0, -2, -2, 5), (-2, -2, 1, -2, -2)),
        ((30, 1, 1, 21, 1), (15, 1, 1, 1, 18), (1,) * 5),
        attacks,
    )
    assert scores[0] == scores[2] == scores[3] == scores[4] == 1
    check_market(masses, capacity, price, [row[0] / gamma for row in attacks[:2]])


def check_unit_gains(masses, capacity, price, sales):
    pad_mass = 1 + sum(masses) + capacity
    dedicated_mass = pad_mass - capacity
    scale = sum(masses) + pad_mass + dedicated_mass
    attacks = (
        (sales[0] / scale, (masses[0] - sales[0]) / scale, 0),
        (sales[1] / scale, 0, 0),
        (0, 0, pad_mass / scale),
        (dedicated_mass / scale, 0, 0),
    )
    scores = defender_scores(
        (price / 5, 0, 1 - price / 5),
        tuple(mass / scale for mass in (*masses, pad_mass, dedicated_mass)),
        (1, 1, 1),
        ((5, 0, -2), (4, 0, -2), (-2, -2, 1), (1, -2, -2)),
        ((10, 1, 1), (5, 1, 1), (1, 1, 1), (1, 1, 1)),
        attacks,
    )
    assert scores[0] == scores[2] == pad_mass / scale
    assert scale * scores[0] - dedicated_mass == capacity
    check_market(masses, capacity, price, [scale * row[0] for row in attacks[:2]])


def check_general_reduction():
    masses = (Q(3, 5), Q(2, 3))
    capacity = 1 + Q(1, 2 * masses[0].denominator * masses[1].denominator)
    sales = (Q(11, 30), Q(2, 3))
    price = Q(5, 2)
    scale = sum(masses) + 1
    attacks = (
        (sales[0] / scale, (masses[0] - sales[0]) / scale, 0),
        (sales[1] / scale, 0, 0),
        (0, 0, 1 / scale),
    )
    scores = defender_scores(
        (price / 5, 0, 1 - price / 5),
        tuple(mass / scale for mass in (*masses, 1)),
        (scale / capacity, Q(1, 2), scale),
        ((5, 0, -2), (4, 0, -2), (-2, -2, 1)),
        ((10, 1, 1), (5, 1, 1), (1, 1, 1)),
        attacks,
    )
    assert capacity == Q(31, 30)
    assert scores == (1, Q(7, 136), 1)
    check_market(masses, capacity, price, [scale * row[0] for row in attacks[:2]])
    check_market(masses, 1, price, (Q(1, 3), masses[1]))
    check_uniform_priors(masses, capacity, price, sales)
    check_unit_gains(masses, capacity, price, sales)


def check_jointly_uniform_reduction():
    price = Q(5, 2)
    attacks = (
        (Q(1, 10), Q(1, 20), Q(1, 20), 0, 0),
        (Q(1, 5), 0, 0, 0, 0),
    ) + ((0, 0, 0, Q(1, 10), Q(1, 10)),) * 3
    scores = defender_scores(
        (price / 5, 0, 0, Q(1, 4), Q(1, 4)),
        (Q(1, 5),) * 5,
        (1,) * 5,
        ((5, 0, 0, -2, -2), (4, 0, 0, -2, -2)) + ((-2, -2, -2, 1, 1),) * 3,
        ((10, 1, 1, 1, 1), (5, 1, 1, 1, 1)) + ((1,) * 5,) * 3,
        attacks,
    )
    threshold = Q(3, 10)
    assert scores == (threshold, Q(1, 20), Q(1, 20), threshold, threshold)
    assert threshold in {Q(a, 5 * b) for a in range(6) for b in range(1, 6)}
    check_market((1, 1), 5 * threshold, price, [5 * row[0] for row in attacks[:2]])
    check_market((1, 1), 1, price, (0, 1))


def hall_ratios(buyers, goods):
    return sorted({Q(a, b) for a in range(buyers + 1) for b in range(1, goods + 1)})


def small_capacity(capacity, ratios):
    index = bisect_left(ratios, capacity)
    if index == len(ratios):
        return ratios[-1] + 1
    upper = ratios[index]
    if upper == capacity:
        return capacity
    lower = ratios[index - 1]
    return Q(lower.numerator + upper.numerator, lower.denominator + upper.denominator)


def check_capacity_comparisons():
    count = 0
    for buyers in range(1, 9):
        for goods in range(1, 8):
            ratios = hall_ratios(buyers, goods)
            midpoints = [(lo + hi) / 2 for lo, hi in zip(ratios, ratios[1:])]
            for capacity in ratios[1:] + midpoints + [buyers + Q(1, 2)]:
                representative = small_capacity(capacity, ratios)
                assert representative > 0
                assert representative.numerator <= 2 * buyers + 1
                assert representative.denominator <= 2 * goods
                for size in range(1, goods + 1):
                    original = size * capacity
                    replacement = size * representative
                    for buyers_in_cut in range(buyers + 1):
                        assert (buyers_in_cut <= original) == (buyers_in_cut <= replacement)
                        assert (buyers_in_cut >= original) == (buyers_in_cut >= replacement)
                count += 1

    assert small_capacity(Q(7, 10), hall_ratios(3, 2)) == Q(2, 3)
    assert count == 1546
    return count


if __name__ == "__main__":
    check_general_reduction()
    print("Verified the general A4i certificate and both separate variants.")
    check_jointly_uniform_reduction()
    print("Verified the jointly uniform A4i certificate and original-capacity clearance.")
    print(f"Verified {check_capacity_comparisons():,} common-capacity comparison cases.")
