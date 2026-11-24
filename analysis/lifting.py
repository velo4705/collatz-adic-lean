#!/usr/bin/env python3
"""
Backward-lifting analysis for the Collatz-adic latent-cycle problem.

Forward map, level j (denominator 3^j d'), numerator a:

    even a: (a, 3^j d')          -> (a/2, 3^j d')
    odd  a: (a, 3^j d')          -> (a + 3^(j-1) d', 3^(j-1) d')   [j >= 1]
    odd  a: (a, d')              -> (3a + d', d')                 [home]

An odd step is followed by forced halvings, so it is convenient to work with
odd numerators.  For an odd state A at level j-1, the odd preimages at level j
are B = 2^e A - 3^(j-1) d' (e >= 1, B odd, gcd(B, 3^j d') = 1).  Only the
starting level k is restricted to the scan range [1, 3^k d'].

At the home level the preimages of a state A are 2A (even) and (A-d')/3 when
3 | (A-d') and the quotient is odd; these generate the transient tree feeding
a cycle.  Keeping the smallest numerators at each stage makes the search
 tractable and correctly reproduces the observed k_min values.
"""

from __future__ import annotations

from math import gcd
from typing import Dict, FrozenSet, List, Set, Tuple

State = Tuple[int, int]


def step(st: State) -> State:
    a, d = st
    if a % 2 == 0:
        return a // 2, d
    g = gcd(3 * a + d, d)
    return (3 * a + d) // g, d // g


def oddpart(a: int) -> int:
    while a % 2 == 0:
        a //= 2
    return a


def exact_cycle(st: State, max_steps: int = 200000) -> Tuple[FrozenSet[State], int, int]:
    seen: Dict[State, int] = {}
    path: List[State] = []
    cur = st
    t = 0
    while cur not in seen:
        if t > max_steps:
            raise RuntimeError(f"no cycle within {max_steps} steps from {st}")
        seen[cur] = t
        path.append(cur)
        cur = step(cur)
        t += 1
    i = seen[cur]
    cyc = frozenset(path[i:])
    d = next(iter(cyc))[1]
    assert all(s[1] == d for s in cyc) and d % 3 != 0
    return cyc, len(cyc), sum(1 for a, _ in cyc if a % 2 == 1)


def enumerate_cycles_exact(dprime: int, bound: int) -> Dict[FrozenSet[State], Tuple[int, int]]:
    found: Dict[FrozenSet[State], Tuple[int, int]] = {}
    for a in range(1, bound + 1):
        if gcd(a, dprime) != 1:
            continue
        cyc, L, M = exact_cycle((a, dprime))
        found.setdefault(cyc, (L, M))
    return found


def home_feeders(cycle: FrozenSet[State], dprime: int, bound: int,
                 keep: int = 4000) -> Set[int]:
    """Odd numerators at the home level whose orbit enters `cycle`."""
    seen: Set[int] = set()
    frontier = {oddpart(a) for a, _ in cycle if a % 2 == 1}
    while frontier:
        nxt: Set[int] = set()
        for A in frontier:
            if A in seen:
                continue
            seen.add(A)
            # even preimage: 2A (its odd part is A itself, already present)
            # odd preimage of an arbitrary state 2^t A: (2^t A - d')/3
            for t in range(0, 40):
                V = (1 << t) * A
                if V <= dprime:
                    continue
                if (V - dprime) % 3:
                    continue
                B = (V - dprime) // 3
                if B > 0 and B % 2 == 1 and gcd(B, dprime) == 1 and B <= bound and B not in seen:
                    nxt.add(B)
        frontier = set(sorted(nxt)[:keep])
    return seen


def lifting_levels(cycle: FrozenSet[State], dprime: int, k: int,
                   home_bound: int = 2000000, keep: int = 4000) -> List[Set[int]]:
    levels: List[Set[int]] = [home_feeders(cycle, dprime, home_bound, keep)]
    for j in range(1, k + 1):
        R = (3 ** (j - 1)) * dprime
        upper = (3 ** j) * dprime if j == k else None
        hi = (R + upper) if upper is not None else (R + (1 << 96))
        nxt: Set[int] = set()
        for A in levels[-1]:
            lo = R + 1
            p = 1
            while p * A < lo:
                p *= 2
            for _ in range(200):
                if p * A > hi:
                    break
                B = p * A - R
                if B % 2 == 1 and gcd(B, (3 ** j) * dprime) == 1:
                    nxt.add(B)
                p *= 2
        levels.append(set(sorted(nxt)[:keep]))
    return levels


def k_min(cycle: FrozenSet[State], dprime: int, kmax: int = 14) -> int:
    for k in range(kmax + 1):
        levels = lifting_levels(cycle, dprime, k)
        bound = (3 ** k) * dprime           # scan range at the starting level
        if any(x <= bound for x in levels[k]):
            return k
    return -1


def main() -> None:
    for dprime in (5, 71):
        print("=" * 82)
        print(f"d' = {dprime}: backward-lifting k_min for every cycle found up to a=200000")
        print("=" * 82)
        cycles = enumerate_cycles_exact(dprime, 200000)
        for cyc, (L, M) in sorted(cycles.items(), key=lambda kv: (kv[1][0], min(kv[0]))):
            km = k_min(cyc, dprime, 14)
            print(f"  E={L-M:3d} M={M:2d}  |C|={len(cyc):3d}  "
                  f"min_state={min(cyc)}  k_min={km}")


if __name__ == "__main__":
    main()
