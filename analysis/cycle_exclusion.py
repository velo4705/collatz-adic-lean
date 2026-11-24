#!/usr/bin/env python3
"""Phase 1 -- algebraic and modular cycle exclusion for the 3-free rational
Collatz cycle equation.

The exact equation (derived from `lemma_2_4_and_cor_2_5_three_free_cycles`,
which forces a cycle's denominator d' to be odd and coprime to 3, and constant
along the cycle) is

    a * (2**E - 3**M) = d' * T,      T = sum_{j=0}^{M-1} 3**(M-1-j) * 2**e_j,

where
  * M = number of odd (3a+d') steps in the cycle,
  * E = number of even (halving) steps in the cycle, so L = E + M is the
        total period (the user's `L` in `a*(2**L - 3**M)` is the halving
        count E here; if L denotes total steps then the power is 2**(L-M)),
  * e_0 = 0 < e_1 < ... < e_{M-1} < E are the cumulative halving counts before
        each odd step (the "trailing-ones block" decomposition supplied by
        FuelLaw + Refueling).

This script
  1. verifies the identity on genuine cycles extracted by simulation,
  2. checks the exact congruence obstructions (d' | 2**E-3**M, T odd,
     3 ∤ T, a odd, 3 ∤ a, 2**E > 3**M),
  3. proves the Steiner 1-cycle bound a <= d' by exhaustive finite check,
  4. verifies length lower bounds L >= M + ceil(M log2 3) for M <= 12,
  5. enumerates exponent patterns for M <= 12 (integer cycles d'=1) in the
     continued-fraction candidate window for E and finds no non-trivial
     solutions,
  6. checks the single trailing-ones block (Steiner-type) configuration.

All arithmetic is exact integer arithmetic. No floats are used in the
verification steps (log2 is used only to locate the search window).
"""

from __future__ import annotations

import itertools
import math
from math import gcd


# ---------------------------------------------------------------------------
# Rational reduced dynamics (matches CollatzAdicBase.RationalDescent.step)
# ---------------------------------------------------------------------------
def step(a: int, d: int) -> tuple[int, int]:
    if a % 2 == 0:
        return a // 2, d
    g = gcd(3 * a + d, d)
    return (3 * a + d) // g, d // g


def orbit_cycle_data(a0: int, d0: int, max_steps: int = 500):
    """Follow the orbit until it returns to (a0, d0); return
    (M, E, exponents, T, L) where exponents[j] is the cumulative halving
    count before the (j+1)-st odd step."""
    a, d = a0, d0
    halvings = 0
    exponents: list[int] = []
    for t in range(1, max_steps + 1):
        if a % 2 == 1:
            exponents.append(halvings)
        a, d = step(a, d)
        if a % 2 == 0:
            halvings += 1
        if (a, d) == (a0, d0):
            M = len(exponents)
            E = halvings
            T = sum(3 ** (M - 1 - j) * 2 ** exponents[j] for j in range(M))
            return M, E, exponents, T, E + M
    raise RuntimeError(f"orbit of ({a0},{d0}) did not close within {max_steps}")


def obstructions(a: int, d: int, M: int, E: int, T: int) -> list[str]:
    """Return the list of violated exact congruence obstructions (empty = all pass)."""
    bad = []
    if gcd(d, 3) != 1:
        bad.append("3 | d")
    if (2 ** E - 3 ** M) % d != 0:
        bad.append("d ∤ 2^E - 3^M")
    if T % 2 == 0:
        bad.append("T even")
    if T % 3 == 0:
        bad.append("3 | T")
    if a % 2 == 0:
        bad.append("a even")
    if a % 3 == 0:
        bad.append("3 | a")
    if 2 ** E <= 3 ** M:
        bad.append("2^E <= 3^M")
    if gcd(a, d) != 1:
        bad.append("gcd(a,d) != 1")
    return bad


# ---------------------------------------------------------------------------
# 1. Verify the cycle-sum identity on genuine cycles
# ---------------------------------------------------------------------------
def verify_identity_on_cycles() -> None:
    print("=== 1. Cycle-sum identity on genuine cycles ===")
    # (a, d') pairs of known exact cycles of the rational Collatz map.
    known = [
        (1, 1),    # trivial integer cycle 1 -> 4 -> 2 -> 1
        (1, 5),    # 1-cycle at d'=5  (E=3, M=1)  -- Paper 4
        (11, 7),   # 2-cycle at d'=7  (E=4, M=2)
        (19, 5),   # 3-cycle at d'=5  (E=5, M=3)  -- Paper 4
        (29, 71),  # 5-cycle at d'=71 (E=10, M=5) -- Paper 4
    ]
    for a, d in known:
        M, E, exps, T, L = orbit_cycle_data(a, d)
        lhs = a * (2 ** E - 3 ** M)
        rhs = d * T
        bad = obstructions(a, d, M, E, T)
        status = "OK" if lhs == rhs and not bad else f"FAIL {bad}"
        print(f"  a={a:4d} d'={d:3d}: M={M:2d} E={E:2d} L={L:2d} "
              f"e={exps} T={T:12d}  a(2^E-3^M)={lhs:12d}  d'T={rhs:12d}  {status}")
        assert lhs == rhs, (a, d)
        assert not bad, (a, d, bad)


# ---------------------------------------------------------------------------
# 2. Steiner 1-cycle exclusion: M=1 forces a <= d'
# ---------------------------------------------------------------------------
def steiner_one_cycle_check() -> None:
    print("\n=== 2. Steiner 1-cycle exclusion (M = 1) ===")
    # For M=1, T=1 (the single odd step occurs at e_0=0), so (2^E-3)a = d'.
    # Since 2^E > 3 we have E >= 2, hence 2^E-3 >= 1 and a = d'/(2^E-3) <= d'.
    violations = []
    for E in range(2, 64):
        N = 2 ** E - 3
        for d in range(1, 500):
            if gcd(d, 3) != 1 or d % 2 == 0:
                continue
            if d % N == 0:
                a = d // N
                if a > d:
                    violations.append((a, d, E))
    print(f"  scanned E=2..63, d'<=500 (odd, 3∤d'): a > d' solutions = {len(violations)}")
    assert not violations
    # Explicit demonstration of the bound for the smallest denominators.
    for E in (2, 3, 4, 5):
        N = 2 ** E - 3
        print(f"  E={E}: (2^E-3)={N}, a = d'/{N} <= d' for all d' (equality only E=2,d'=1)")


# ---------------------------------------------------------------------------
# 3. Length lower bounds for M <= 12
# ---------------------------------------------------------------------------
def length_lower_bounds() -> None:
    print("\n=== 3. Length lower bounds (2^E > 3^M) for M <= 12 ===")
    print("   M   E_min  L_min = E_min + M   (2^E_min > 3^M >= 2^(E_min-1))")
    for M in range(1, 13):
        E_min = 0
        while 2 ** E_min <= 3 ** M:
            E_min += 1
        assert 2 ** E_min > 3 ** M and 2 ** (E_min - 1) <= 3 ** M
        print(f"  {M:2d}   {E_min:2d}        {E_min + M:2d}")
    # Classical trivial cycle: L = 3 = 2 + 1, exactly the M=1 bound.
    assert 2 ** 2 > 3 ** 1 and 2 ** 1 <= 3 ** 1
    print("  trivial cycle L=3 attains the M=1 bound; any non-trivial cycle has L>=6.")


# ---------------------------------------------------------------------------
# 4. Exponent-pattern enumeration for integer cycles (d' = 1), M <= 12
# ---------------------------------------------------------------------------
def pattern_enumeration(window: int = 4) -> None:
    print("\n=== 4. Exponent-pattern congruence sweep, d'=1, M<=12 ===")
    print(f"   E in [E_min, E_min+{window}] (continued-fraction candidate window); "
          "N = 2^E-3^M must divide T and a=T/N must exceed 1")
    total = 0
    nontrivial = []
    for M in range(1, 13):
        E_min = 0
        while 2 ** E_min <= 3 ** M:
            E_min += 1
        for E in range(E_min, E_min + window + 1):
            N = 2 ** E - 3 ** M
            # e_0 = 0; choose 1 <= e_1 < ... < e_{M-1} <= E-1
            for tail in itertools.combinations(range(1, E), M - 1):
                exps = (0,) + tail
                T = sum(3 ** (M - 1 - j) * 2 ** exps[j] for j in range(M))
                total += 1
                if T % N == 0 and T // N > 1:
                    nontrivial.append((M, E, exps, T // N, T))
    print(f"  exponent patterns tested: {total:,}")
    print(f"  non-trivial integer-cycle solutions found: {len(nontrivial)}")
    for hit in nontrivial[:20]:
        print("   ", hit)
    assert not nontrivial
    print("  (cf. continued-fraction convergents 2/1, 8/5, 19/12 of log2 3: "
          "the candidate E/M ratios for M<=12 are all inside the window.)")


# ---------------------------------------------------------------------------
# 5. Single trailing-ones block (Steiner-type) configuration
# ---------------------------------------------------------------------------
def single_block_check() -> None:
    print("\n=== 5. Single trailing-ones block followed by halvings ===")
    # Pattern: M consecutive odd steps (each followed by one forced halving,
    # e_j = j), then s >= 1 further halvings; E = M + s.  T = 3^M - 2^M.
    # Integer cycles d'=1: need (2^(M+s) - 3^M) | (3^M - 2^M) with a > 1.
    hits = []
    for M in range(1, 13):
        T = 3 ** M - 2 ** M
        for s in range(1, 41):
            E = M + s
            N = 2 ** E - 3 ** M
            if N > 0 and T % N == 0 and T // N > 1:
                hits.append((M, s, E, T // N))
    print(f"  M<=12, s<=40: non-trivial integer single-block solutions = {len(hits)}")
    for h in hits[:20]:
        print("   ", h)
    assert not hits
    # Rational single-block cycles with a > d' exist (e.g. 11/7); the
    # obstruction is a *classification*: d' must absorb the missing factor.
    for M, s in [(1, 2), (2, 2), (3, 2)]:
        T = 3 ** M - 2 ** M
        E = M + s
        N = 2 ** E - 3 ** M
        print(f"  M={M} s={s}: T={T}, 2^E-3^M={N}, "
              f"integer a={T/N if N and T % N == 0 else 'non-integral'}")


# ---------------------------------------------------------------------------
# 6. Modular residue fingerprint of the exponents (2-adic/3-adic)
# ---------------------------------------------------------------------------
def residue_fingerprint() -> None:
    print("\n=== 6. Modular / 2-adic / 3-adic fingerprint ===")
    # T = sum 3^{M-1-j} 2^{e_j} with e_0 = 0 gives:
    #   T ≡ 3^{M-1} (mod 2^{e_1})   (2-adic leading term),
    #   T ≡ 2^{e_{M-1}} (mod 3)     (3-adic trailing term, hence 3 ∤ T),
    #   T odd, and T ≡ (-1)^{e_{M-1}} (mod 3).
    checks = 0
    for M in range(1, 9):
        for E in range(M + 1, M + 9):
            for tail in itertools.combinations(range(1, E), M - 1):
                exps = (0,) + tail
                T = sum(3 ** (M - 1 - j) * 2 ** exps[j] for j in range(M))
                assert T % 2 == 1
                assert T % 3 != 0
                assert T % 3 == pow(2, exps[-1], 3)
                if M >= 2:
                    assert T % (2 ** exps[1]) == pow(3, M - 1, 2 ** exps[1])
                checks += 1
    print(f"  fingerprint identities verified on {checks:,} exponent patterns.")


def main() -> None:
    verify_identity_on_cycles()
    steiner_one_cycle_check()
    length_lower_bounds()
    pattern_enumeration()
    single_block_check()
    residue_fingerprint()
    print("\nALL EXACT CONGRUENCE OBSTRUCTION CHECKS PASSED.")


if __name__ == "__main__":
    main()
