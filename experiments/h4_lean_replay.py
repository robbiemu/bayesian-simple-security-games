#!/usr/bin/env python3
"""Compare Lean's binary compiler output with exact source answers using graph-only Z3."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

from h4_ssg_to_mpg_replay import MPG, cases, read_state, smt_label, source_solution


def decoded_game(record):
    owners = ["max" if is_max else "min" for is_max in record["owners"]]
    start = record["start"]
    if not 0 <= start < len(owners):
        raise ValueError("start outside the target graph")
    edges = [[] for _ in owners]
    for src, dst, weight in record["arcs"]:
        if not (0 <= src < len(owners) and 0 <= dst < len(owners)):
            raise ValueError("arc endpoint outside the target graph")
        edges[src].append((dst, weight))
    if not all(edges):
        raise ValueError("target graph contains a vertex without moves")
    return MPG(owners, edges, start)


def replay(systematic):
    fixtures = list(cases(random_count=0, systematic=systematic))
    requests = [
        {
            "name": name,
            "rows": game.rows,
            "start": game.start,
            "numerator": threshold.numerator,
            "denominator": threshold.denominator,
        }
        for name, game, threshold, _ in fixtures
    ]
    lean_dir = Path(__file__).resolve().parents[1] / "lean"
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "Replay/H4Binary.lean"],
        cwd=lean_dir,
        input="".join(json.dumps(request) + "\n" for request in requests),
        stdout=subprocess.PIPE,
        text=True,
        check=True,
    )
    tables = result.stdout.splitlines()
    if len(tables) != len(fixtures):
        raise RuntimeError(f"expected {len(fixtures)} Lean tables, got {len(tables)}")

    yes = 0
    for (name, source, threshold, _), line in zip(fixtures, tables):
        record = json.loads(line)
        if record["name"] != name:
            raise RuntimeError(f"expected {name}, got {record['name']}")
        graph = decoded_game(record)
        values, _, _ = source_solution(source)
        expected = read_state(values, source.start) >= threshold
        if smt_label(graph) != expected:
            raise RuntimeError(f"{name}: Z3 disagreed with the exact source answer {expected}")
        yes += expected
        if name == "closed-third-equal":
            arc_count = sum(map(len, graph.edges))
            print(f"{name}: {len(graph.owners)} vertices, {arc_count} arcs", flush=True)

    print(f"{len(fixtures)} Lean binary tables checked by Z3 ({yes} YES, {len(fixtures) - yes} NO)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--systematic", type=int, choices=(0, 1, 2), default=0,
        help="include all labelled binary-move games with up to N nonterminal states",
    )
    args = parser.parse_args()
    if not __debug__:
        parser.error("run without -O to keep source and SMT checks enabled")
    if shutil.which("z3") is None:
        parser.error("the z3 executable must be on PATH")
    replay(args.systematic)


if __name__ == "__main__":
    main()
