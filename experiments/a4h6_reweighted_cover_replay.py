#!/usr/bin/env python3
"""Reproduce the A4h6 extremal iteration counts using exact rational LPs."""

from fractions import Fraction
import re
import subprocess


def smt_number(value):
    value = Fraction(value)
    if value < 0:
        return f"(- {smt_number(-value)})"
    if value.denominator == 1:
        return str(value.numerator)
    return f"(/ {value.numerator} {value.denominator})"


def linear_sum(terms):
    return "(+ 0 " + " ".join(f"(* {smt_number(a)} {v})" for a, v in terms) + " 0)"


def parse_expression(result_tokens):
    token = result_tokens.pop()
    if token != "(":
        return token
    result = []
    while result_tokens[-1] != ")":
        result.append(parse_expression(result_tokens))
    result_tokens.pop()
    return result


def model_number(tree):
    if isinstance(tree, str):
        return Fraction(tree)
    if tree[0] == "/":
        return model_number(tree[1]) / model_number(tree[2])
    assert tree[0] == "-"
    return -model_number(tree[1])


def solve_lp(names, inequalities, objectives, query):
    """Send a rational linear optimization or feasibility problem to Z3."""
    statements = [f"(declare-const {v} Real)\n(assert (>= {v} 0))" for v in names]
    statements += [f"(assert {inequality})" for inequality in inequalities]
    statements += [f"({sense} {expr})" for sense, expr in objectives]
    statements += ["(check-sat)", f"(get-value ({' '.join(query)}))"]
    process = subprocess.run(
        ["z3", "-in"], input="\n".join(statements), text=True, capture_output=True
    )
    status, _, model = process.stdout.partition("\n")
    if status == "unsat":
        return None
    if process.returncode != 0 or status != "sat":
        raise RuntimeError(process.stdout + process.stderr)
    tokens = re.findall(r"\(|\)|[^\s()]+", model)
    return {name: model_number(value) for name, value in parse_expression(tokens[::-1])}


def replay(depth, m, policy):
    """Run the exact market rule with one extremal source quote policy."""
    arcs = [(0, 1, 1, 1)]
    source, sink, F, n = 0, 1, 1, 2
    for _ in range(depth):
        arcs += [(n, source, F, 0), (sink, n + 1, F, 0),
                 (n, sink, F, 2*F), (source, n + 1, F, 2*F)]
        source, sink, F, n = n, n + 1, 2*F, n + 2
    eta = Fraction(1, 2*m)
    exit_quote = (2*F+1)/eta
    high_bid = exit_quote + (n+2)*max(cost for _, _, _, cost in arcs) + 2
    capacity = [0]*n
    mass, offers = [], []
    for i, (tail, head, limit, cost) in enumerate(arcs + [(sink, source, F, 0)]):
        capacity[tail] += 2*limit
        mass.append(2*limit)
        slope = 1-eta if i == len(arcs) else 1
        offers += [(i, tail, high_bid, 1, f"purchases{i}_0"), (i, head, high_bid-cost, slope, f"purchases{i}_1")]
    extra = f"purchases{len(mass)}_0"
    offers.append((len(mass), source, exit_quote, 1, extra))
    mass.append(1)
    return_head = f"purchases{len(arcs)}_1"
    prices = [f"prices{j}" for j in range(n)]
    utilities = [f"utilities{i}" for i in range(len(mass))]
    purchases = [var for _, _, _, _, var in offers]
    row_totals = [linear_sum((1, var) for a, _, _, _, var in offers if a == i) for i in range(len(mass))]
    column_totals = [linear_sum((1, var) for _, b, _, _, var in offers if b == j) for j in range(n)]
    assignment = [f"(<= {total} {limit})" for total, limit in zip(row_totals+column_totals, mass+capacity)]
    covering = [f"(>= (+ {utilities[i]} (* {smt_number(d)} {prices[j]})) {smt_number(b)})" for i, j, b, d, _ in offers]

    quote, count = Fraction(0), 0
    while quote < exit_quote:
        objective = linear_sum((b+(1-d)*quote, var) for _, _, b, d, var in offers)
        frozen = solve_lp(purchases, assignment, [("maximize", objective), ("maximize", return_head)],
                    [return_head, extra])
        frozen_throughput = frozen[return_head]/2
        assert frozen[extra] == 0
        assert frozen_throughput == sum(2*j-1 <= quote*eta for j in range(1, F+1))
        weights = capacity.copy()
        weights[source] -= 2*eta*frozen_throughput
        reweighted = linear_sum(list(zip(mass, utilities)) + list(zip(weights, prices)))
        updated = solve_lp(utilities+prices, covering, [("minimize", reweighted), (policy, prices[source])], utilities+prices)
        actual = updated[prices[source]]
        if frozen_throughput == F and policy == "maximize":
            assert actual >= exit_quote
        else:
            if frozen_throughput+m > F or (frozen_throughput+m == F and policy == "maximize"):
                expected = exit_quote
            else:
                expected = (2*(frozen_throughput+m+(policy == "maximize"))-1)/eta
            assert actual == expected, (frozen_throughput, m, actual, expected)
        clear = [f"(= {var} 0)" for i, j, b, d, var in offers
                 if b-d*updated[prices[j]] < updated[utilities[i]]]
        clear += [f"(= {total} {limit})" for total, limit, name in zip(row_totals+column_totals, mass+capacity, utilities+prices)
                  if updated[name] > 0]
        assert (solve_lp(purchases, assignment+clear, [], [extra]) is not None) == (actual >= exit_quote)
        assert actual > quote
        quote = actual
        count += 1
    assert count == ((F+m+1)//(m+1) if policy == "maximize" else F//m+1)
    return count


def main():
    for depth in range(1, 4):
        for m in (1, 2, 3):
            lower_count = replay(depth, m, "maximize")
            upper_count = replay(depth, m, "minimize")
            print(f"depth={depth}, m={m}, reweighted solves {lower_count}–{upper_count}")


if __name__ == "__main__":
    main()
