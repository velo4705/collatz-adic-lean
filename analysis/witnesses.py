#!/usr/bin/env python3
"""Explicit minimal witnesses for the delayed latent cycles of d' = 5, 71.

For every cycle C at home denominator d' and every level k, we compute the
least starting numerator a <= 3^k d' whose orbit enters C.  The first k for
which such an a exists is k_min(C); the witness a is printed together with the
level-by-level orbit (the "lifting chain").
"""

import sys
from math import gcd

sys.path.insert(0, "analysis")
from lifting import (enumerate_cycles_exact, exact_cycle, k_min, lifting_levels)


def trace_chain(a, dprime, k, target):
    """Return the numerator at each level during the descent to level 0."""
    a, d = a, (3 ** k) * dprime
    chain = [(k, a)]
    for j in range(k, 0, -1):
        # forced halvings until odd
        while a % 2 == 0:
            a //= 2
        a = a + (3 ** (j - 1)) * dprime   # odd step at level j
        d = (3 ** (j - 1)) * dprime
        chain.append((j - 1, a))
    return chain


def main():
    for dprime in (5, 71):
        print("=" * 90)
        print(f"d' = {dprime}: exhaustive witness table (cycles found for a <= 200000)")
        print("=" * 90)
        cycles = enumerate_cycles_exact(dprime, 200000)
        for cyc, (L, M) in sorted(cycles.items(), key=lambda kv: (kv[1][0], min(kv[0]))):
            km = k_min(cyc, dprime, 14)
            if km < 0:
                continue
            lv = lifting_levels(cyc, dprime, km, keep=8000)
            bound = 3 ** km * dprime
            witnesses = sorted(x for x in lv[km] if x <= bound)
            a = witnesses[0] if witnesses else None
            c, L2, M2 = exact_cycle((a, bound))
            assert c == cyc
            print(f"\ncycle: E = {L-M}, M = {M}, |C| = {len(cyc)}, "
                  f"min state = {min(cyc)}, k_min = {km}")
            print(f"  witness a = {a}  (level {km} denominator = {bound})")
            print(f"  lifting chain (level, numerator): {trace_chain(a, dprime, km, cyc)}")
            print(f"  first cycle state reached: {min(cyc)}")
            print(f"  cycle equation: d' | 2^{L-M} - 3^{M} = {2**(L-M) - 3**M} "
                  f"= {dprime} * {(2**(L-M) - 3**M)//dprime}")


if __name__ == "__main__":
    main()
