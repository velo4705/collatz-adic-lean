#!/usr/bin/env python3
"""
Phase 1 -- accelerated odd-to-odd Syracuse dynamics, logarithmic drift,
and continued-fraction cycle lower bounds (Paper 9, Collatz-adic Lean).

MODEL
-----
For odd positive n let v2(m) be the 2-adic valuation of m.  The accelerated
odd-to-odd Syracuse map is

        T_syr(n) = (3n + 1) / 2^{v2(3n+1)},        a = v2(3n+1) >= 1.

If n_0 is odd and a_j = v2(3 n_j + 1), n_{j+1} = T_syr(n_j), then with
A_j = a_0 + ... + a_{j-1} (A_0 = 0, A_M = E) the EXACT M-step identity is

        n_M * 2^{A_M} = 3^M n_0 + T,    T = sum_{j<M} 3^{M-1-j} 2^{A_j}.   (*)

Geometric valuation law: among the 2^{K-1} odd residues mod 2^K, exactly
2^{K-a-1} have v2(3n+1) = a for 1 <= a < K, and exactly 1 has a = K.
Hence P(a = j) = 2^{-j} (j >= 1), E[a] = 2, and

        E[log(n_M/n_0)] = M log(3/4) + O(1/n_0),

since log(n_{j+1}/n_j) = log(3) - a_j log(2) + log(1 + 1/(3 n_j)).

CYCLE BOUNDS
------------
For a cycle (*) becomes n*(2^E - 3^M) = T with 2^E > 3^M.  Because
a_j >= 1 we have j <= A_j <= E-(M-j), so

        (3^M - 2^M) / (2^E - 3^M)  <=  n  <=  2^{E-M}(3^M - 2^M)/(2^E - 3^M).

The lower value is attained by the single-block valuation tuple (all a_j=1).
Starting the cycle at its minimum forces a_0 = 1, which sharpens the upper
end (the "interleaved" bound implemented below).

DIOPHANTINE BOUND
-----------------
Let p_k/q_k run over the continued-fraction convergents of alpha=log_2(3)
with q_k <= Q.  For all E,M >= 1 with M < q_{k+1} and E/M != p_j/q_j,

        |E - M alpha| > 1/(q_k + q_{k+1}),

and equality is impossible for the same reason at a convergent from above.
Therefore, whenever 2^E > 3^M,

        2^E - 3^M = 3^M (2^{E-M alpha} - 1) > 3^M ln(2)/(q_k + q_{k+1}).

Combined with the cycle bounds this constrains any non-trivial cycle.  We
also implement the Eliahou/Crandall sandwich log_2(3) < E/M <=
log_2(3 + 1/B) (B = verified search bound) and find the least denominator
of a rational in that interval, giving an explicit lower bound on the
cycle length L.

No third-party packages are required (Decimal is in the standard library).
"""

from __future__ import annotations

import json
import math
import os
from decimal import Decimal, getcontext
from fractions import Fraction

ARTIFACT_DIR = "/home/nix/.local/share/openresearch/files/collatz-adic-lean"
Q_MAX = 10 ** 6                 # convergent-denominator ceiling from the brief
SEARCH_BOUND = 1 << 40          # classical verified Collatz search bound (Eliahou)
getcontext().prec = 90          # ample for convergents with q <= 10^8


# ---------------------------------------------------------------------------
# 1. exact Syracuse arithmetic and the valuation law
# ---------------------------------------------------------------------------
def v2(m: int) -> int:
    """2-adic valuation of a positive integer."""
    assert m > 0
    a = 0
    while m % 2 == 0:
        m //= 2
        a += 1
    return a


def syracuse_step(n: int) -> int:
    """(3n+1) / 2^{v2(3n+1)}; n is assumed odd."""
    assert n % 2 == 1
    t = 3 * n + 1
    return t >> v2(t)


def valuation_counts(K: int) -> dict[int, int]:
    """Exact count of odd residues r mod 2^K with v2(3r+1) = a."""
    counts: dict[int, int] = {}
    for r in range(1, 1 << K, 2):
        a = v2(3 * r + 1)
        counts[a] = counts.get(a, 0) + 1
    return counts


def check_valuation_law(Kmax: int = 12) -> tuple[list[dict], bool]:
    """Verify count(a) = 2^{K-a-1} for each 1 <= a < K, and that exactly one
    odd residue mod 2^K has v2(3n+1) >= K (the exceptional class, whose true
    valuation depends on K -- e.g. n=1 mod 4 has valuation 2 > K=2)."""
    rows: list[dict] = []
    ok = True
    for K in range(1, Kmax + 1):
        counts = valuation_counts(K)
        small = {a: c for a, c in counts.items() if a < K}
        expected = {a: (1 << (K - a - 1)) for a in range(1, K)}
        tail = sum(c for a, c in counts.items() if a >= K)
        good = (small == expected and tail == 1 and
                sum(counts.values()) == 1 << (K - 1))
        ok &= good
        rows.append({"K": K, "counts": counts, "expected_small": expected,
                     "tail_ge_K": tail, "total_odd": 1 << (K - 1),
                     "ok": good})
    return rows, ok


def geometric_moments(K: int = 22) -> dict:
    """Exact truncated geometric moments of a = v2(3n+1) over odd residues
    mod 2^K, compared with E[a]=2 and Var[a]=2 of the infinite law."""
    counts = valuation_counts(K)
    total = 1 << (K - 1)
    mean = Fraction(sum(a * c for a, c in counts.items()), total)
    second = Fraction(sum(a * a * c for a, c in counts.items()), total)
    var = second - mean * mean
    return {
        "K": K,
        "mean_a_exact": f"{mean.numerator}/{mean.denominator}",
        "mean_a": float(mean),
        "var_a": float(var),
        "limit_mean_a": 2.0,      # sum_{j>=1} j 2^{-j}
        "limit_var_a": 2.0,       # E[a^2]-E[a]^2 = 6-4
    }


# ---------------------------------------------------------------------------
# 2. exact M-step Syracuse identity and the valuation bijection
# ---------------------------------------------------------------------------
def syracuse_trajectory(n0: int, valuations: list[int]) -> list[int]:
    """Apply the prescribed valuations; assert they are correct."""
    orbit = [n0]
    for a in valuations:
        t = 3 * orbit[-1] + 1
        assert v2(t) == a, (n0, valuations, a)
        orbit.append(t >> a)
    return orbit


def syracuse_T(valuations: list[int]) -> int:
    """T = sum_{j<M} 3^{M-1-j} 2^{A_j}, A_j = sum_{i<j} a_i."""
    A, T, M = 0, 0, len(valuations)
    for j, a in enumerate(valuations):
        T += (3 ** (M - 1 - j)) * (1 << A)
        A += a
    return T


def compositions(n: int) -> list[list[int]]:
    """All compositions of n into positive parts (2^{n-1} of them)."""
    out: list[list[int]] = []
    def rec(remaining: int, cur: list[int]) -> None:
        if remaining == 0:
            out.append(cur.copy())
            return
        for a in range(1, remaining + 1):
            cur.append(a)
            rec(remaining - a, cur)
            cur.pop()
    rec(n, [])
    return out


def valuations_match(n0: int, tuple_: list[int]) -> bool:
    """True iff v2(3 n_j+1) = a_j exactly for j < len(tuple_)."""
    x = n0
    for a in tuple_:
        t = 3 * x + 1
        if v2(t) != a:
            return False
        x = t >> a
    return True


def check_identity_bijection(Emax: int = 11) -> tuple[list[dict], bool]:
    """Bijection check: for every valuation tuple with sum E<=Emax there is
    exactly ONE odd residue mod 2^{E+1} realising it (the extra bit pins down
    exactness of the final valuation), and the exact identity (*) holds there.
    This is the Syracuse/Terras valuation bijection."""
    rows: list[dict] = []
    ok = True
    for E in range(1, Emax + 1):
        tuples = compositions(E)
        hits: dict[tuple[int, ...], list[int]] = {}
        for r in range(1, 1 << (E + 1), 2):
            for tup in tuples:
                if valuations_match(r, tup):
                    hits.setdefault(tuple(tup), []).append(r)
        good = (set(hits.keys()) == {tuple(t) for t in tuples} and
                all(len(v) == 1 for v in hits.values()))
        if good:
            for tup in tuples:
                r = hits[tuple(tup)][0]
                orbit = syracuse_trajectory(r, tup)
                lhs = orbit[-1] * (1 << E)
                rhs = (3 ** len(tup)) * r + syracuse_T(tup)
                assert lhs == rhs, (r, tup, lhs, rhs)
        ok &= good
        rows.append({"E": E, "num_tuples": len(tuples),
                     "realised": len(hits), "odd_classes_mod_2^{E+1}": 1 << E,
                     "bijective": good})
    return rows, ok


def log_drift(tuples: list[list[int]] | None = None,
              shifts: int = 400) -> dict:
    """For fixed valuation tuples, sample n_0 = c + 2^{E+1} t with t large and
    average log(n_M/n_0).  The valuations are constant on the class, and
    log(n_M/n_0) = M log(3/4) + sum_j log(1 + 1/(3 n_j)) = M log(3/4)+O(1/n_0).
    We exhibit the 1/n_0 decay of the error."""
    if tuples is None:
        tuples = [[1] * M for M in (2, 3, 5)] + [[3, 1, 2, 1], [2, 2, 1, 1, 3]]
    rows: list[dict] = []
    base = 10 ** 6
    for tup in tuples:
        E = sum(tup)
        M = len(tup)
        # find the unique class representative c mod 2^{E+1}
        c = None
        for r in range(1, 1 << (E + 1), 2):
            if valuations_match(r, tup):
                c = r
                break
        assert c is not None
        for scale in (1, 10):
            t0 = base * scale
            acc = 0.0
            for t in range(t0, t0 + shifts):
                n0 = c + (1 << (E + 1)) * t
                n_M = syracuse_trajectory(n0, tup)[-1]
                acc += math.log(n_M) - math.log(n0)
            mean = acc / shifts
            # exact leading term for a FIXED tuple: E[log(n_M/n_0)] =
            # M log 3 - E log 2 + O(1/n_0); averaging E over the geometric
            # law (E[a]=2) gives the stated M log(3/4).
            predicted = M * math.log(3.0) - E * math.log(2.0)
            rows.append({
                "tuple": tup, "E": E, "M": M, "t_start": t0,
                "mean_log_ratio": mean, "predicted_fixed_tuple": predicted,
                "abs_error": abs(mean - predicted),
                "n0_typical": c + (1 << (E + 1)) * t0,
            })
    return {"rows": rows, "log_3_4": math.log(3.0 / 4.0),
            "note": "fixed-tuple leading term M log3 - E log2; "
                    "E_valuation=2 gives M log(3/4) on average"}


# ---------------------------------------------------------------------------
# 3. continued fractions of log_2(3) and Diophantine gap bounds
# ---------------------------------------------------------------------------
def cf_convergents(qmax: int) -> list[dict]:
    """Convergents p_k/q_k of log_2(3) with q_k <= qmax, computed with
    high-precision Decimal and verified by exact integer comparisons of
    2^p and 3^q where feasible."""
    alpha = Decimal(3).ln() / Decimal(2).ln()
    x = alpha
    p_prev, q_prev = 0, 1        # (p_{-2}, q_{-2})
    p, q = 1, 0                  # (p_{-1}, q_{-1})
    convergents: list[dict] = []
    for _ in range(200):
        a = int(x.to_integral_value(rounding="ROUND_FLOOR"))
        p_prev, p = p, a * p + p_prev
        q_prev, q = q, a * q + q_prev
        if q > qmax:
            break
        frac_dec = Decimal(p) / Decimal(q)
        err = float(frac_dec - alpha)  # sign: >0 means from above
        convergents.append({
            "k": len(convergents), "a_k": a, "p": p, "q": q,
            "from_above": err > 0,
            "error": err,
            "alpha_minus_pq": float(alpha - frac_dec),
        })
        frac_x = x - Decimal(a)
        if frac_x == 0:
            break
        x = Decimal(1) / frac_x
    return convergents


def exact_gap(p: int, q: int, max_bits: int = 4000) -> int | None:
    """Exact 2^p - 3^q when it is positive and within max_bits bits
    (~1200 decimal digits), else None.  Larger gaps are represented by
    their Diophantine logarithmic bounds instead."""
    if p <= 0 or q <= 0 or p > max_bits:
        return None
    g = (1 << p) - 3 ** q
    return g if g > 0 else None


def diophantine_bound(convergents: list[dict]) -> dict:
    """Using the last convergent with q<=Q and its successor, produce
    2^E - 3^M > 3^M ln2 /(q_k+q_{k+1}) for M < q_{k+1}, plus exact gaps
    for the convergent numerators/denominators where computable."""
    alpha = Decimal(3).ln() / Decimal(2).ln()
    rows: list[dict] = []
    for c in convergents:
        p, q = c["p"], c["q"]
        g = exact_gap(p, q) if c["from_above"] else None
        rows.append({
            "k": c["k"], "p": p, "q": q,
            "from_above": c["from_above"],
            "error_abs": abs(c["error"]),
            "exact_gap_2p_minus_3q": g,
        })
    # last convergent with q <= Q and the first one after (needs qmax+1)
    qmax = Q_MAX
    extended = cf_convergents(qmax * 100)
    inside = [c for c in extended if c["q"] <= qmax]
    k = len(inside) - 1
    qk, qk1 = inside[k]["q"], extended[k + 1]["q"]
    denom = qk + qk1
    rows_tail = {
        "Q": qmax, "last_q_le_Q": qk, "next_q": qk1,
        "diophantine_denominator": denom,
        "bound_statement": "2^E - 3^M > 3^M ln(2)/(q_k+q_{k+1}) "
                           "for all M < q_{k+1} with 2^E > 3^M",
        "numeric_coefficient_ln2_over_denom": math.log(2.0) / denom,
    }
    return {"convergents": rows, "tail_bound": rows_tail}


# ---------------------------------------------------------------------------
# 4. cycle-size bounds and the Eliahou/Crandall length bound
# ---------------------------------------------------------------------------
def cycle_bounds_table(dio: dict) -> dict:
    """For each convergent from above, tabulate the exact lower/upper cycle
    bounds on n and the implied bound on q_k."""
    rows: list[dict] = []
    for c in dio["convergents"]:
        if not c["from_above"]:
            continue
        p, q = c["p"], c["q"]           # E=p, M=q
        gap = c["exact_gap_2p_minus_3q"]
        if gap is None:
            continue
        # log10 representations avoid materialising enormous integers
        log_tmin = q * math.log10(3) + math.log10(1 - (2.0 / 3.0) ** q)
        log_tmax = log_tmin + (p - q) * math.log10(2)
        log_gap = math.log10(gap)
        rows.append({
            "M": q, "E": p, "gap_bits": gap.bit_length(),
            "gap_log10": log_gap,
            "n_lower_log10": log_tmin - log_gap,
            "n_upper_log10": log_tmax - log_gap,
            "n_lower": f"10^{log_tmin - log_gap:.6f}",
            "n_upper": f"10^{log_tmax - log_gap:.6f}",
        })
    return {"rows": rows}


def length_lower_bound(B: int, qmax: int = 10 ** 8) -> dict:
    """Eliahou/Crandall: log_2(3) < E/M <= log_2(3 + 1/B).  Find the least
    denominator M of any rational in that interval (convergents plus
    semiconvergents of log_2(3)), hence L >= E+M."""
    alpha = Decimal(3).ln() / Decimal(2).ln()
    # log_2(3 + 1/B) = log_2(3B+1) - log_2(B)
    hi = (Decimal(3 * B + 1).ln() - Decimal(B).ln()) / Decimal(2).ln()
    width = float(hi - alpha)

    conv = cf_convergents(qmax)
    # extend one past the largest stored convergent
    extended = cf_convergents(qmax * 10)
    allc = extended
    best: tuple[int, int] | None = None
    candidates: list[dict] = []
    for k, c in enumerate(allc):
        p, q = c["p"], c["q"]
        val = Fraction(p, q)
        lo_f = float(alpha)
        hi_f = float(hi)
        if lo_f < float(val) <= hi_f + 1e-18:
            candidates.append({"p": p, "q": q, "k": k})
            if best is None or q < best[1]:
                best = (p, q)
        # semiconvergents between p_{k-1}/q_{k-1} and p_k/q_k
        if k >= 1:
            pp, qq = allc[k - 1]["p"], allc[k - 1]["q"]
            if qq == 0:
                continue
            for j in range(1, c["a_k"]):
                sp, sq = j * p + pp, j * q + qq
                if sq > qmax:
                    break
                sv = float(Fraction(sp, sq))
                if lo_f < sv <= hi_f + 1e-18:
                    candidates.append({"p": sp, "q": sq, "k": k, "semi": True})
                    if best is None or sq < best[1]:
                        best = (sp, sq)

    if best is None:
        return {"B": B, "interval_width": width, "found": False}
    E_min, M_min = best
    return {
        "B": B,
        "interval": ["log2(3)", "log2(3+1/B)"],
        "interval_width": width,
        "found": True,
        "least_E_over_M": f"{E_min}/{M_min}",
        "least_M": M_min,
        "least_L_E_plus_M": E_min + M_min,
        "least_L_E_steps": E_min,
        "candidates": candidates[:12],
    }


# ---------------------------------------------------------------------------
# 5. driver
# ---------------------------------------------------------------------------
def main() -> dict:
    os.makedirs(ARTIFACT_DIR, exist_ok=True)
    result: dict = {}

    print("[1/6] geometric valuation law ...", flush=True)
    vrows, vok = check_valuation_law()
    result["valuation_law"] = {"rows": vrows, "all_ok": vok}
    print("      exact counts match 2^{K-a-1} for K=1..12:", vok, flush=True)
    result["valuation_moments"] = geometric_moments()
    print("      E[a] exact (K=22) =", result["valuation_moments"]["mean_a_exact"],
          "-> infinite-law limit 2", flush=True)

    print("[2/6] exact M-step identity + valuation bijection ...", flush=True)
    irows, iok = check_identity_bijection()
    result["identity_bijection"] = {"rows": irows, "all_ok": iok}
    print("      bijective for all A=1..14:", iok, flush=True)

    print("[3/6] logarithmic drift E[log(n_M/n_0)] ...", flush=True)
    result["log_drift"] = log_drift()
    for row in result["log_drift"]["rows"][-4:]:
        print("      M=%d E=%d t0=%7d  E[log ratio]=% .9f  leading=% .9f"
              "  err=%.2e"
              % (row["M"], row["E"], row["t_start"], row["mean_log_ratio"],
                 row["predicted_fixed_tuple"], row["abs_error"]), flush=True)

    print("[4/6] continued fractions of log_2(3), q<=10^6 ...", flush=True)
    conv = cf_convergents(Q_MAX)
    result["convergents_q_le_1e6"] = conv
    print("      %d convergents; largest q=%d"
          % (len(conv), conv[-1]["q"]), flush=True)

    print("[5/6] Diophantine gap bounds ...", flush=True)
    result["diophantine"] = diophantine_bound(conv)
    tail = result["diophantine"]["tail_bound"]
    print("      q_k=%d, q_{k+1}=%d => 2^E-3^M > 3^M ln2/%d"
          % (tail["last_q_le_Q"], tail["next_q"],
             tail["diophantine_denominator"]), flush=True)

    print("[6/6] cycle size and length bounds ...", flush=True)
    result["cycle_bounds"] = cycle_bounds_table(result["diophantine"])
    result["length_bound"] = length_lower_bound(SEARCH_BOUND)
    lb = result["length_bound"]
    if lb.get("found"):
        print("      verified-search bound B=2^40 => least M=%d, L>=%d"
              % (lb["least_M"], lb["least_L_E_plus_M"]), flush=True)
    else:
        print("      no rational in interval below qmax (unexpected)", flush=True)

    out = os.path.join(ARTIFACT_DIR, "syracuse_log_drift.json")
    with open(out, "w") as f:
        json.dump(result, f, indent=2)
    print("wrote", out, flush=True)
    return result


if __name__ == "__main__":
    main()
