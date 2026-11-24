#!/usr/bin/env python3
"""Consolidated Phase-1 results: k_min table and saturation for k = 0..14."""

import sys
from math import gcd

sys.path.insert(0, "analysis")
from lifting import enumerate_cycles_exact, k_min, lifting_levels, exact_cycle


def order(a, n):
    x = 1
    for k in range(1, n * n + 1):
        x = x * a % n
        if x == 1:
            return k
    return None


def discrete_log_2(a, n, o2):
    """lambda with 3 == 2^lambda (mod n), if 3 is in <2>."""
    x = 1
    for lam in range(o2):
        if x == a % n:
            return lam
        x = x * 2 % n
    return None


def main():
    for dp in (5, 71):
        o2, o3 = order(2, dp), order(3, dp)
        lam = discrete_log_2(3, dp, o2)
        print(f"\n### d' = {dp}: ord_2 = {o2}, ord_3 = {o3}, 3 = 2^{lam} mod {dp}")
        cycles = enumerate_cycles_exact(dp, 3_000_000)
        rows = []
        for cyc, (L, M) in cycles.items():
            km = k_min(cyc, dp, 14)
            lv = lifting_levels(cyc, dp, km, keep=8000)
            a = min(x for x in lv[km] if x <= 3 ** km * dp)
            rows.append((km, L - M, M, min(cyc), a, len(cyc)))
        rows.sort()
        print("  k_min  E   M  min_cycle_state   witness_a   |C|")
        for km, E, M, ms, a, sz in rows:
            print(f"  {km:5d} {E:3d} {M:3d}  {str(ms):16s}  {a:10d}   {sz:3d}")
        # reachable-set sizes per k
        print("  k : 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14")
        print("  # :", " ".join(str(sum(1 for r in rows if r[0] <= k)) for k in range(15)))
        # congruence exponent: A == 3^(lam^-1 * (-E)) a mod d' with E = number
        # of halvings during stripping (equals k for the one-halving-per-step chains)
        if lam is not None and gcd(lam, o2) == 1:
            inv = pow(lam, -1, o2)
            print(f"  congruence: A ≡ 3^{{-{inv}·E}} · a (mod {dp}), "
                  f"with -{inv} ≡ {(-inv) % o2} (mod {o2})")
        print("  cycle equation types:")
        for E in sorted(set(r[1] for r in rows)):
            print(f"    E={E}, 2^{E}-3^{M if False else [r[2] for r in rows if r[1]==E][0]} "
                  f"= {2**E - 3**[r[2] for r in rows if r[1]==E][0]} "
                  f"= {dp} * {(2**E - 3**[r[2] for r in rows if r[1]==E][0])//dp}")


if __name__ == "__main__":
    main()
