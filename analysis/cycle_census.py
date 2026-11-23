#!/usr/bin/env python3
"""Fast exact cycle census at a home denominator d' (coprime to 6)."""

import sys
from math import gcd


def main():
    dprime = int(sys.argv[1]) if len(sys.argv) > 1 else 71
    bound = int(sys.argv[2]) if len(sys.argv) > 2 else 3_000_000
    found = {}
    for a0 in range(1, bound + 1):
        if gcd(a0, dprime) != 1:
            continue
        a, d = a0, dprime
        seen = {}
        path = []
        t = 0
        while (a, d) not in seen:
            seen[(a, d)] = t
            path.append((a, d))
            if a & 1 == 0:
                a >>= 1
            else:
                g = gcd(3 * a + d, d)
                a = (3 * a + d) // g
                d //= g
            t += 1
        i = seen[(a, d)]
        cyc = frozenset(path[i:])
        if cyc not in found:
            found[cyc] = sum(1 for x, _ in cyc if x & 1)
    print(f"d' = {dprime}, scanned a <= {bound}: {len(found)} exact cycles")
    for cyc, M in sorted(found.items(), key=lambda kv: (len(kv[0]), min(kv[0]))):
        print(f"  L={len(cyc):3d} M={M:2d} E={len(cyc)-M:3d}  min={min(cyc)}")


if __name__ == "__main__":
    main()
