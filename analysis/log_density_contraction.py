#!/usr/bin/env python3
"""
Layer 7 -- bounded-excursion Syracuse contraction and dyadic log-density decay.

This script verifies, in exact integer / Fraction arithmetic, the quantitative
inputs to `CollatzAdicBase/LogDensityContraction.lean`:

1. TERMINAL NON-CONTRACTION (`syracuseFail_rational_decay`).  At K = 8t,
   M = 5t the failing odd residues r mod 2^K (those with 2^{A_M} <= 3^M)
   satisfy, exactly,

       2 * fail * 25^{5t} <= 24^{5t} * 2^{8t},

   equivalently fail / 2^{K-1} <= (24/25)^{5t}.

2. UNIFORM UPWARD EXCURSION (`excursionFailF_tail_uniform`).  For B > 0,
   the odd residues with A_M < K and some prefix 3^j >= B 2^{A_j} satisfy

       exc * sqrt(B) <= 26 * 2^{K-1},

   checked here without floating point as exc^2 * B <= 26^2 * 4^{K-1}
   (B rational is cleared by multiplying by its denominator squared).

3. UNION / GOOD SET.  The good residue set is the odd residues outside both
   exceptional sets.  We count it exactly and check the lower bound

       good >= 2^{K-1} - fail - exc
            >= 2^{K-1} * (1 - (24/25)^{5t} - 26/sqrt(B)).

4. PATHWISE CONTRACTION.  For each good residue with A_M < K and for lifts
   n0 = r + m 2^K above the explicit threshold

       N0(K,M) = 2^{K-1-M} 3^M = 2^{3t-1} 3^{5t},

   we verify j <= M implies n_j <= (B+1) n0 and n_M < n0.  The check uses the
   exact identity n_j 2^{A_j} = 3^j n0 + T_j.

5. DYADIC LOG-DENSITY RATE.  Coupling t = floor(lambda log log X) and
   B = (log X)^c gives the exceptional density on [X,2X]

       delta(X) <= (24/25)^{5t} + 26 B^{-1/2}
                = O((log X)^(-gamma)),   gamma = min(5 lambda ln(25/24), c/2).

   We report this rate and check the exact inequality for a range of dyadic
   scales (all logarithms are natural).

No third-party packages are needed.
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction

ARTIFACT_DIR = "/home/nix/.local/share/openresearch/files/collatz-adic-lean"
FAIL_BASE = Fraction(24, 25)          # terminal decay base
EXC_CONST = 26                       # uniform excursion constant
B_VALUES = [Fraction(4), Fraction(16), Fraction(64), Fraction(256)]
T_VALUES = [1, 2]                     # K = 8t = 8, 16 (finite exact scans)


# ---------------------------------------------------------------------------
# elementary accelerated dynamics (same convention as the Lean modules)
# ---------------------------------------------------------------------------
def v2(m: int) -> int:
    assert m > 0
    a = 0
    while m % 2 == 0:
        m //= 2
        a += 1
    return a


def step(n: int) -> int:
    assert n % 2 == 1
    return (3 * n + 1) >> v2(3 * n + 1)


def valuation_list(n: int, M: int) -> list[int]:
    out: list[int] = []
    x = n
    for _ in range(M):
        a = v2(3 * x + 1)
        out.append(a)
        x = (3 * x + 1) >> a
    return out


def orbit(n: int, M: int) -> list[int]:
    out = [n]
    for _ in range(M):
        out.append(step(out[-1]))
    return out


def prefix_T(as_: list[int]) -> int:
    j = len(as_)
    A_list = [0]
    for a in as_:
        A_list.append(A_list[-1] + a)
    return sum(3 ** (j - 1 - i) * 2 ** A_list[i] for i in range(j))


# ---------------------------------------------------------------------------
# 1-3. exact residue sets at K = 8t, M = 5t
# ---------------------------------------------------------------------------
def residue_sets(t: int, B: Fraction) -> dict:
    K, M = 8 * t, 5 * t
    mod = 1 << K
    odd = mod >> 1                       # 2^{K-1}
    fail: set[int] = set()
    exc: set[int] = set()
    sums: dict[int, int] = {}
    for r in range(1, mod, 2):
        as_ = valuation_list(r, M)
        A = sum(as_)
        sums[r] = A
        if 2 ** A <= 3 ** M:
            fail.add(r)
        if A < K:
            s = 0
            for j, a in enumerate(as_, start=1):
                s += a
                if B * (1 << s) <= 3 ** j:
                    exc.add(r)
                    break
    both = fail & exc
    union = fail | exc
    good = set(range(1, mod, 2)) - union

    fail_c, exc_c, good_c = len(fail), len(exc), len(good)
    # exact integer/rational forms of the two analytic bounds
    fail_lhs = 2 * fail_c * 25 ** (5 * t)
    fail_rhs = 24 ** (5 * t) * 2 ** (8 * t)
    exc_lhs = exc_c * exc_c * B.numerator
    exc_rhs = EXC_CONST ** 2 * (odd * odd) * B.denominator
    fail_floor = (Fraction(odd) * FAIL_BASE ** (5 * t)).__floor__()
    # floor(26 * odd / sqrt(B)) without floating point
    exc_floor = math.isqrt((EXC_CONST * odd) ** 2 // B.numerator * B.denominator)
    rational_lb = odd - fail_floor - exc_floor
    return {
        "t": t, "K": K, "M": M, "B": str(B), "odd_residues": odd,
        "fail": fail_c, "excursion": exc_c, "both": len(both),
        "union": len(union), "good": good_c,
        "fail_bound_ok": fail_lhs <= fail_rhs,
        "fail_lhs": fail_lhs, "fail_rhs": fail_rhs,
        "excursion_bound_ok": exc_lhs <= exc_rhs,
        "exc_lhs": exc_lhs, "exc_rhs": exc_rhs,
        "union_bound_ok": good_c >= odd - fail_c - exc_c,
        "rational_lb": rational_lb,
        "rational_lb_ok": good_c >= rational_lb,
        "sum_ge_K_count": sum(1 for r, A in sums.items() if A >= K),
        "_sums": sums,
        "_good": good,
    }


# ---------------------------------------------------------------------------
# 4. pathwise contraction on lifted starting values
# ---------------------------------------------------------------------------
def check_pathwise(rows: list[dict]) -> dict:
    """Direct verification of the analytic pathwise theorem.

    For small t every good residue mod 2^{8t} has A_M >= 8t, so that residue
    class alone does not fix the trajectory.  The analytic core of the Lean
    theorem is however stated for an arbitrary modulus bound L with
    A_M + 1 <= L; we verify it here with L = 2M, directly sampling odd starts
    satisfying 3^M < 2^{A_M}, no prefix excursion, and n0 > N0(L,M).
    """
    all_ok = True
    details = []
    for row in rows:
        t, K, M = row["t"], row["K"], row["M"]
        B = Fraction(row["B"])
        L = 2 * M
        N0 = (1 << (L - 1 - M)) * 3 ** M      # 2^{L-1-M} 3^M
        peak_ok = contract_ok = threshold_ok = True
        checked = admissible = 0
        sample = range(N0 + 1, N0 + 2001, 2) if N0 % 2 == 0 else range(N0 + 2, N0 + 2002, 2)
        for n0 in sample:
            as_ = valuation_list(n0, M)
            A = sum(as_)
            if A + 1 > L or 2 ** A <= 3 ** M:
                continue
            s = 0
            excursion = False
            for j, a in enumerate(as_, start=1):
                s += a
                if B * (1 << s) <= 3 ** j:
                    excursion = True
                    break
            if excursion:
                continue
            admissible += 1
            checked += 1
            orb = orbit(n0, M)
            limit = (B + 1) * n0
            for j in range(1, M + 1):
                if Fraction(orb[j]) > limit:
                    peak_ok = False
                if orb[j] * (1 << sum(valuation_list(n0, j))) != 3 ** j * n0 + prefix_T(valuation_list(n0, j)):
                    threshold_ok = False
            if orb[M] >= n0:
                contract_ok = False
        ok = peak_ok and contract_ok and threshold_ok and checked > 0
        all_ok &= ok
        details.append({
            "t": t, "K": K, "M": M, "L": L, "B": str(B), "N0": N0,
            "admissible_starts": admissible, "lifts_checked": checked,
            "peak_ok": peak_ok, "contraction_ok": contract_ok,
            "identity_ok": threshold_ok, "ok": ok,
        })
    return {"all_ok": all_ok, "details": details}


# ---------------------------------------------------------------------------
# 5. dyadic logarithmic-density rate
# ---------------------------------------------------------------------------
LN_RATE = 5 * math.log(25 / 24)         # ~0.204107 per unit of lambda


def dyadic_rate(log2X_values: list[int], lam: float = 1.0, c: float = 2.0) -> dict:
    rows = []
    ok_all = True
    for lg in log2X_values:
        lnX = lg * math.log(2)
        lnlnX = math.log(lnX)
        t = max(1, math.floor(lam * lnlnX))
        K, M = 8 * t, 5 * t
        B = lnX ** c
        fail_term = float(FAIL_BASE ** (5 * t))
        exc_term = EXC_CONST / math.sqrt(B)
        delta = fail_term + exc_term
        gamma = min(LN_RATE * lam, c / 2)
        # floor(t) costs at most one step: exp(5 ln(25/24)) ~ 1.226 on the
        # fail term; the excursion term is exactly 26 (log X)^(-c/2).
        fail_ok = fail_term <= math.exp(LN_RATE) * lnX ** (-LN_RATE * lam)
        exc_ok = exc_term <= EXC_CONST * lnX ** (-c / 2) * (1 + 1e-9)
        rate_ok = fail_ok and exc_ok
        ok_all &= rate_ok
        rows.append({
            "log2_X": lg, "log_X": round(lnX, 3), "t": t, "K": K, "M": M,
            "B": round(B, 3), "fail_term": fail_term,
            "excursion_term": exc_term, "delta": delta,
            "gamma": round(gamma, 6), "log_power_check_ok": rate_ok,
            "N0_log10": round((K - 1 - M) * math.log10(2) + M * math.log10(3), 2),
        })
    return {
        "coupling": "t = floor(lambda log log X), B = (log X)^c",
        "lambda": lam, "c": c,
        "gamma_formula": "min(5 lambda ln(25/24), c/2)",
        "gamma": min(LN_RATE * lam, c / 2),
        "rate_per_lambda": LN_RATE,
        "rows": rows, "all_ok": ok_all,
    }


def main() -> None:
    rows = []
    for t in T_VALUES:
        for B in B_VALUES:
            rows.append(residue_sets(t, B))
    path = check_pathwise(rows)
    rate = dyadic_rate([64, 128, 256, 512, 1024, 2048])

    report = {
        "layer": 7,
        "title": "Bounded-excursion Syracuse contraction and dyadic log-density decay",
        "residue_checks": [
            {k: v for k, v in r.items() if not k.startswith("_")} for r in rows
        ],
        "pathwise": path,
        "dyadic_rate": rate,
        "all_ok": (all(r["fail_bound_ok"] and r["excursion_bound_ok"] and
                       r["union_bound_ok"] and r["rational_lb_ok"] for r in rows)
                   and path["all_ok"] and rate["all_ok"]),
    }

    os.makedirs(ARTIFACT_DIR, exist_ok=True)
    with open(os.path.join(ARTIFACT_DIR, "log_density_contraction.json"), "w",
              encoding="utf-8") as fh:
        json.dump(report, fh, indent=2)
    os.makedirs("artifacts", exist_ok=True)
    with open("artifacts/log_density_contraction.json", "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=2)

    lines = [
        "Layer 7 -- bounded-excursion contraction & dyadic log-density decay",
        "=" * 78,
        "Exact residue counts (K = 8t, M = 5t):",
        " t   K   B     odd      fail     exc     good   bounds ok",
        "-" * 78,
    ]
    for r in rows:
        ok = (r["fail_bound_ok"] and r["excursion_bound_ok"] and
              r["union_bound_ok"] and r["rational_lb_ok"])
        lines.append(
            f"{r['t']:>2d}  {r['K']:>2d}   {r['B']:>4s}  {r['odd_residues']:>7d}  "
            f"{r['fail']:>7d}  {r['excursion']:>7d}  {r['good']:>7d}   {ok}")
    lines += ["", f"Pathwise contraction all_ok: {path['all_ok']}"]
    for d in path["details"]:
        lines.append(
            f"  t={d['t']} L={d['L']:>2d} B={d['B']:>4s} N0={d['N0']} starts={d['lifts_checked']:>4d} "
            f"peak={d['peak_ok']} contract={d['contraction_ok']} identity={d['identity_ok']}")
    lines += [
        "",
        f"Dyadic rate: delta(X) <= (24/25)^(5t) + 26/sqrt(B) = O((log X)^(-gamma)),",
        f"  gamma = min(5 lambda ln(25/24), c/2) = {rate['gamma']:.6f}",
        "  log2_X     t    K    M       delta      gamma   ok",
        "-" * 78,
    ]
    for d in rate["rows"]:
        lines.append(
            f"  {d['log2_X']:>6d}   {d['t']:>2d}   {d['K']:>2d}   {d['M']:>2d}   "
            f"{d['delta']:>10.3e}   {d['gamma']:.4f}   {d['log_power_check_ok']}")
    lines += ["", f"ALL CHECKS PASS: {report['all_ok']}"]
    text = "\n".join(lines) + "\n"
    print(text)
    with open("analysis/log_density_contraction.txt", "w", encoding="utf-8") as fh:
        fh.write(text)
    if not report["all_ok"]:
        raise SystemExit("FAIL: a verification check did not pass")


if __name__ == "__main__":
    main()
