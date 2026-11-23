"""Replay the degree-three price-preserving split on exact unit markets."""

from fractions import Fraction
from random import Random

from a4j_unit_prices import check_certificate, solve


def split_market(bids, slopes):
    buyer_count, good_count = len(bids), len(bids[0])
    viable = [
        (i, j) for i in range(buyer_count) for j in range(good_count)
        if bids[i][j] > 0
    ]
    high_offer = 1 + max(
        [Fraction(0)]
        + [bids[i][j] for i, j in viable]
        + [bids[i][j] / slopes[i][j] for i, j in viable]
    )
    buyer_ports, good_ports = {}, {}
    offers = {}
    next_buyer = next_good = 0

    for i in range(buyer_count):
        neighbors = [j for buyer, j in viable if buyer == i]
        ports = range(next_buyer, next_buyer + max(1, len(neighbors)))
        next_buyer += len(ports)
        for j, port in zip(neighbors, ports):
            buyer_ports[i, j] = port
        for left, right in zip(ports, ports[1:]):
            offers[left, next_good] = offers[right, next_good] = (high_offer, Fraction(1))
            next_good += 1

    good_copies = []
    for j in range(good_count):
        neighbors = [i for i, good in viable if good == j]
        ports = range(next_good, next_good + max(1, len(neighbors)))
        next_good += len(ports)
        good_copies.append(ports)
        for i, port in zip(neighbors, ports):
            good_ports[i, j] = port
        for left, right in zip(ports, ports[1:]):
            offers[next_buyer, left] = offers[next_buyer, right] = (high_offer, Fraction(1))
            next_buyer += 1

    for i, j in viable:
        offers[buyer_ports[i, j], good_ports[i, j]] = (bids[i][j], slopes[i][j])

    split_bids = [[Fraction(-1)] * next_good for _ in range(next_buyer)]
    split_slopes = [[Fraction(1)] * next_good for _ in range(next_buyer)]
    for (i, j), (bid, slope) in offers.items():
        split_bids[i][j], split_slopes[i][j] = bid, slope

    assert all(sum(bid > 0 for bid in row) <= 3 for row in split_bids)
    assert all(sum(bid > 0 for bid in column) <= 3 for column in zip(*split_bids))
    assert len(set(buyer_ports.values())) == len(viable)
    assert len(set(good_ports.values())) == len(viable)
    return split_bids, split_slopes, good_copies, buyer_ports, good_ports


def check_split(bids, slopes):
    prices, matching, _ = solve(bids, slopes)
    check_certificate(bids, slopes, prices, matching, exhaustive=True)
    split_bids, split_slopes, copies, buyer_ports, good_ports = split_market(bids, slopes)
    split_prices, split_matching, _ = solve(split_bids, split_slopes)
    check_certificate(split_bids, split_slopes, split_prices, split_matching)

    projected_prices = [max(split_prices[j] for j in ports) for ports in copies]
    assert projected_prices == prices
    projected_matching = dict.fromkeys(range(len(bids)), -1)
    for edge, buyer in buyer_ports.items():
        i, j = edge
        if split_matching[buyer] == good_ports[edge]:
            assert projected_matching[i] == -1
            projected_matching[i] = j
    check_certificate(bids, slopes, projected_prices, projected_matching, exhaustive=True)


if __name__ == "__main__":
    generator = Random(671031)
    for _ in range(80):
        buyers, goods = generator.randint(1, 5), generator.randint(1, 4)
        bids = [
            [Fraction(generator.randrange(-2, 12), generator.randint(1, 4)) for _ in range(goods)]
            for _ in range(buyers)
        ]
        slopes = [
            [Fraction(generator.randint(1, 7), generator.randint(1, 5)) for _ in range(goods)]
            for _ in range(buyers)
        ]
        check_split(bids, slopes)
    print("Checked degree, projected prices, and projected clearance on 80 unit markets.")
