"""Validate goods keys before running the pinned exact clearance checker."""

from a4h9_hybrid_examples import check_clearance as check_recorded_clearance


def check_clearance(offers, masses, capacities, prices, allocation):
    assert prices.keys() == capacities.keys(), "Price and capacity keys differ"
    check_recorded_clearance(offers, masses, capacities, prices, allocation)


def check_extra_price_rejected():
    try:
        check_clearance(
            {"buyer": {"a": (1, 1)}},
            {"buyer": 1},
            {"a": 1},
            {"a": 0, "undeclared": 7},
            {"buyer": {"a": 1}},
        )
    except AssertionError as error:
        assert str(error) == "Price and capacity keys differ"
    else:
        raise AssertionError("The checker accepted an extra price key")


if __name__ == "__main__":
    check_extra_price_rejected()
    print("Checked that an extra price key is rejected.")
