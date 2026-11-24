#!/usr/bin/env python3
"""
Exact rational-arithmetic analysis of the Collatz-adic "latent cycle" problem.

State model (matches CollatzAdicBase/RationalDescent.lean):

    a reduced positive rational x = a/d is stored as the pair (a, d) with
    0 < a, 0 < d, d odd, gcd(a, d) = 1.

    step(a, d) = (a/2, d)                       if a is even
    step(a, d) = ((3a + d)/g, d/g), g = gcd(3a + d, d)   if a is odd

Since g | 3 (Lemma 2.1/2.2), the only prime that can disappear from the
denominator is 3.  Hence every cycle lives at a denominator d' coprime to 3
("home denominator d'"), and a state at level 3^k d' needs exactly k odd
steps before its denominator is 3-free.

This script:
  1. enumerates all cycles at a home denominator d';
  2. for each k, enumerates all reduced states (a, 3^k d') and records which
     cycle is reached (the "reachable cycle set under 3^k d'");
  3. reports the first level k at which each cycle becomes reachable, plus
     multiplicative orders ord_{d'}(2), ord_{d'}(3) and cycle parameters
     (L, M) satisfying d' | 2^L - 3^M.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from math import gcd
from typing import Dict, FrozenSet, Iterable, List, Optional, Set, Tuple

State = Tuple[int, int]  # (numerator, denominator), both positive, d odd, coprime


def valid(a: int, d: int) -> bool:
    return a > 0 and d > 0 and d % 2 == 1 and gcd(a, d) == 1


def step(st: State) -> State:
    a, d = st
    assert valid(a, d), (a, d)
    if a % 2 == 0:
        return a // 2, d
    g = gcd(3 * a + d, d)
    return (3 * a + d) // g, d // g


def as_fraction(st: State) -> Fraction:
    a, d = st
    return Fraction(a, d)


def iterate(st: State, n: int) -> State:
    for _ in range(n):
        st = step(st)
    return st


def canonical_cycle(st: State, max_steps: int = 100000) -> Tuple[FrozenSet[int], int, int]:
    """Follow an orbit until a cycle is detected; return (states mod d, L, M).

    The returned canonical form lives at the (3-free) home denominator, with
    numerators reduced modulo d.  L = number of steps in the cycle, M = number
    of odd steps in the cycle.
    """
    seen: Dict[State, int] = {}
    path: List[State] = []
    cur = st
    t = 0
    while cur not in seen:
        if t > max_steps:
            raise RuntimeError(f"orbit did not cycle within {max_steps} steps: {st}")
        seen[cur] = t
        path.append(cur)
        cur = step(cur)
        t += 1
    start = seen[cur]
    cycle_states = path[start:]
    d = cycle_states[0][1]
    assert all(s[1] == d for s in cycle_states), cycle_states
    assert d % 3 != 0, f"cycle denominator has a factor 3: {cycle_states}"
    residues = frozenset(a % d for a, _ in cycle_states)
    L = len(cycle_states)
    M = sum(1 for a, _ in cycle_states if a % 2 == 1)
    return residues, L, M


def enumerate_cycles(dprime: int, a_bound_multiplier: int = 40) -> Dict[FrozenSet[int], Tuple[int, int]]:
    """Enumerate cycles whose home denominator is dprime (coprime to 3, odd)."""
    assert dprime % 2 == 1 and dprime % 3 != 0
    found: Dict[FrozenSet[int], Tuple[int, int]] = {}
    for a in range(1, dprime * a_bound_multiplier + 1):
        if gcd(a, dprime) != 1:
            continue
        res, L, M = canonical_cycle((a, dprime))
        if res not in found:
            found[res] = (L, M)
    return found


def reachable_cycles_at_level(dprime: int, k: int, a_bound: int = 4) -> Dict[FrozenSet[int], Tuple[int, int]]:
    """All cycles reachable from reduced states (a, 3^k d') with a <= a_bound*3^k d'."""
    d = (3 ** k) * dprime
    found: Dict[FrozenSet[int], Tuple[int, int]] = {}
    for a in range(1, a_bound * d + 1):
        if gcd(a, d) != 1:
            continue
        res, L, M = canonical_cycle((a, d))
        if res not in found:
            found[res] = (L, M)
    return found


def multiplicative_order(a: int, n: int) -> Optional[int]:
    """ord_n(a) for gcd(a, n) = 1, via brute force (fine for small n)."""
    if gcd(a, n) != 1:
        return None
    x = 1
    for k in range(1, n * n + 1):
        x = (x * a) % n
        if x == 1:
            return k
    return None


def cycle_fingerprint(res: FrozenSet[int], dprime: int, found: Dict) -> str:
    L, M = found[res]
    elems = ",".join(str(x) for x in sorted(res))
    return f"(L={L},M={M},res={{{elems}}})"


def main() -> None:
    for dprime in (5, 71):
        print("=" * 78)
        print(f"HOME DENOMINATOR d' = {dprime}")
        print("=" * 78)
        o2 = multiplicative_order(2, dprime)
        o3 = multiplicative_order(3, dprime)
        print(f"ord_{dprime}(2) = {o2}, ord_{dprime}(3) = {o3}")

        all_cycles = enumerate_cycles(dprime)
        print(f"\nCycles at d' = {dprime}: {len(all_cycles)}")
        for i, (res, params) in enumerate(sorted(all_cycles.items(), key=lambda kv: (kv[1][0], sorted(kv[0]))), 1):
            L, M = params
            print(f"  C{i}: {cycle_fingerprint(res, dprime, all_cycles)}  "
                  f"2^{L}-{M} = {2**L - 3**M}  mod d' = {(2**L - 3**M) % dprime}")

        print("\nReachable cycle sets by level k (full enumeration for small k):")
        first_seen: Dict[FrozenSet[int], int] = {}
        for k in range(0, 9):
            d = (3 ** k) * dprime
            if d > 3_000_000:
                print(f"  k = {k}: denominator {d} too large for full scan; skipped")
                continue
            found = reachable_cycles_at_level(dprime, k, a_bound=2)
            for res in found:
                first_seen.setdefault(res, k)
            print(f"  k = {k} (d={d}): {len(found)} cycles reachable")
            for res, params in sorted(found.items(), key=lambda kv: (kv[1][0], sorted(kv[0]))):
                print(f"      {cycle_fingerprint(res, dprime, found)}")
        print("\nFirst appearance level k_min for each cycle:")
        for res, kmin in sorted(first_seen.items(), key=lambda kv: kv[1]):
            print(f"  k_min = {kmin}: {cycle_fingerprint(res, dprime, all_cycles)}")


if __name__ == "__main__":
    main()
