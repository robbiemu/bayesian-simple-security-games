"""Run the exact affine-market research replays from the public checkout."""

from pathlib import Path
import subprocess
import sys


EXPERIMENTS = Path(__file__).resolve().parents[1]


def main():
    replays = [
        ("a4j_unit_prices.py", "--self-test", "2000"),
        ("a4j_degree_three_replay.py",),
        ("a4j_endpoint_support_replay.py",),
        ("a4j_exclusion_lp_replay.py",),
        ("a4f_unit_tick_scaling.py",),
        ("a4f_contract_scaling_replay.py",),
        ("a4f_binary_quota_replay.py",),
        ("a4l_unit_ordinal.py",),
        ("a4l_weighted_ordinal.py",),
        ("a4l_asymmetric_ordinal_replay.py",),
    ]
    for name, *args in replays:
        print(f"Running {name}", flush=True)
        subprocess.run([sys.executable, "-B", str(EXPERIMENTS / name), *args], check=True)


if __name__ == "__main__":
    main()
