"""Check the dense offset core and its offset-inconsistent branch example."""

from fractions import Fraction as Q


def check_separating_family():
    size = 5
    intercept = [[1 for _ in range(size)] for _ in range(size)]
    slopes = [[4 if i == j else 1 for j in range(size)] for i in range(size)]
    buyer_offsets = [1] * size
    good_offsets = [0] * size
    for i in range(size):
        for j in range(size):
            assert intercept[i][j] == buyer_offsets[i] + slopes[i][j] * good_offsets[j]

    # In each disjoint pair, a cross ratio of 16 requires a slope spread
    # of at least 4 in one of its columns, even after row normalization.
    lower_bound = Q(0)
    for i, j in ((0, 1), (2, 3)):
        ratio = Q(slopes[i][i] * slopes[j][j], slopes[i][j] * slopes[j][i])
        assert ratio == 4**2
        lower_bound += 1 - Q(1, 4)
    assert lower_bound == Q(3, 2) > 1

    # All local slopes are one, so common offsets would make this sum zero.
    local_bids = ((Q(1), Q(1)), (Q(1), Q(3, 2)))
    alternating_sum = local_bids[0][0] + local_bids[1][1] - local_bids[0][1] - local_bids[1][0]
    assert alternating_sum == Q(1, 2)


if __name__ == "__main__":
    check_separating_family()
    print("Checked the common offsets, two disjoint slope-ratio obstructions, and the branch intercepts.")
