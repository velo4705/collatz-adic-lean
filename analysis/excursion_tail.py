#!/usr/bin/env python3
"""
Layer 6 -- prefix-maximum upward excursions of multi-step Syracuse orbits.

We verify, with exact integer/Fraction arithmetic, the two ingredients of
`CollatzAdicBase/ExcursionTail.lean`:

1. THE PREFIX RATIO BOUND.  For an odd start n_0 with valuation list
   a_0, ..., a_{M-1}, A_j = sum_{i<j} a_i and
       T_j = sum_{i<j} 3^{j-1-i} 2^{A_i},
   the identity n_j 2^{A_j} = 3^j n_0 + T_j gives

       n_j / n_0 = 3^j/2^{A_j} + T_j/(n_0 2^{A_j})
                 <= 3^j/2^{A_j} + (3^j - 2^j)/(n_0 2^j),

   the last step because a_i >= 1 implies A_j - A_i >= j - i and hence
   T_j / 2^{A_j} = sum_{i<j} 3^{j-1-i} 2^{A_i-A_j} <= (3/2)^j - 1.

2. THE UNIFORM POWER-LAW TAIL.  With the rational tilt x = 5/7 of
   lambda = 1/2 (indeed x^2 = 25/49 > 1/2), beta = 26/15 (beta^2 > 3),
   z = x/2 = 5/14 and m = z/(1-z) = 5/9:

       sqrt(B) * #{odd r mod 2^K : max_{1<=j<=M} 3^j/2^{A_j} >= B}
             <= C * 2^{K-1},        C = (26/15)/(1 - 26/27) = 26,

   uniformly in the horizon M (and K).  This is Markov + a union bound +
   the exact composition generating function sum_E compCount(j,E) z^E
   <= (z/(1-z))^j.  Numerically optimal C = sqrt(3)/(2 sqrt(2)-1)
   / (1 - sqrt(3)/(2 sqrt(2)-1)) = 17.9717..., so C = 26 is a valid
   rational certificate.

The finite-modulus excursion event is the exact one: for an odd residue
r mod 2^K we follow its accelerated orbit only while A_j + 1 <= K, so the
prefix valuation (and hence the event) is determined by r mod 2^K.  Every
comparison below is made with integers (squaring the sqrt) or Fractions.

No third-party packages are needed.
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction
from functools import lru_cache

ARTIFACT_DIR = "/home/nix/.local/share/openresearch/files/collatz-adic-lean"
THRESHOLDS = [2, 4, 8, 16, 32]
EXTRA_THRESHOLDS = [2 ** 12, 2 ** 16, 2 ** 20]  # where the bound is nontrivial
C_RATIONAL = 26                                  # certified constant
X_TILT = Fraction(5, 7)                          # >= 2^{-1/2}
BETA = Fraction(26, 15)                          # >= 3^{1/2}
Z_TILT = X_TILT / 2                              # 5/14
M_TILT = Z_TILT / (1 - Z_TILT)                   # 5/9
RHO = BETA * M_TILT                              # 26/27


# ---------------------------------------------------------------------------
# elementary accelerated dynamics
# ---------------------------------------------------------------------------
def v2(m: int) -> int:
    assert m > 0
    a = 0
    while m % 2 == 0:
        m //= 2
        a += 1
    return a


def syracuse_step(n: int) -> int:
    assert n % 2 == 1
    t = 3 * n + 1
    return t >> v2(t)


def valuation_list(n: int, M: int) -> list[int]:
    """Exact accelerated valuation list of length M (n odd)."""
    out: list[int] = []
    x = n
    for _ in range(M):
        a = v2(3 * x + 1)
        out.append(a)
        x = (3 * x + 1) >> a
    return out


def prefix_T(as_: list[int]) -> int:
    """T_j = sum_{i<j} 3^{j-1-i} 2^{A_i}."""
    j = len(as_)
    A_list = [0]
    for a in as_:
        A_list.append(A_list[-1] + a)
    return sum(3 ** (j - 1 - i) * 2 ** A_list[i] for i in range(j))


# ---------------------------------------------------------------------------
# 1. prefix ratio bound
# ---------------------------------------------------------------------------
def check_prefix_ratio_bound() -> dict:
    rows = []
    ok_all = True
    for n in [1, 3, 5, 7, 11, 27, 97, 703, 871, 6171, 77031, 837799]:
        if n % 2 == 0:
            continue
        row = {"n0": n, "checks": []}
        for M in [1, 2, 3, 5, 8, 12]:
            as_ = valuation_list(n, M)
            n_j = n
            A = 0
            for j, a in enumerate(as_, start=1):
                A += a
                n_j = (3 * n_j + 1) >> a
                Tj = prefix_T(as_[:j])
                # exact identity  n_j * 2^A = 3^j * n_0 + T_j
                identity = n_j * 2 ** A == 3 ** j * n + Tj
                # T_j / 2^A <= (3^j - 2^j) / 2^j   <=>  T_j 2^j <= 2^A(3^j-2^j)
                drift = Tj * 2 ** j <= 2 ** A * (3 ** j - 2 ** j)
                # n_j/n0 <= 3^j/2^A + T_j/(n0 2^A)   (equality over Q)
                exact = Fraction(n_j, n) == Fraction(3 ** j, 2 ** A) + Fraction(Tj, n * 2 ** A)
                good = identity and drift and exact
                ok_all &= good
                row["checks"].append({"j": j, "A": A, "identity": identity,
                                      "drift": drift, "exact_ratio": exact, "ok": good})
        rows.append(row)
    return {"all_ok": ok_all, "rows": rows}


# ---------------------------------------------------------------------------
# 2. exact finite-modulus prefix-maximum excursion counts
# ---------------------------------------------------------------------------
def prefix_max_excursion_counts(K: int, thresholds: list[int]) -> dict:
    mod = 1 << K
    odd_count = mod >> 1                     # 2^{K-1}
    fail = {B: 0 for B in thresholds}
    best_ratio = [Fraction(0)] * len(thresholds)
    max_seen = Fraction(0)
    for r in range(1, mod, 2):
        n = r
        A = 0
        hit = [False] * len(thresholds)
        for j in range(1, K + 1):
            a = v2(3 * n + 1)
            A += a
            if A > K - 1:                    # prefix no longer determined mod 2^K
                break
            ratio = Fraction(3 ** j, 2 ** A)
            max_seen = max(max_seen, ratio)
            for idx, B in enumerate(thresholds):
                if 3 ** j >= B * 2 ** A:
                    hit[idx] = True
                    best_ratio[idx] = max(best_ratio[idx], ratio)
            n = (3 * n + 1) >> a
        for idx, h in enumerate(hit):
            if h:
                fail[thresholds[idx]] += 1
    checks = []
    for B in thresholds:
        count = fail[B]
        # exact form of  count/2^{K-1} <= C / sqrt(B):  count^2 * B <= C^2 * 4^{K-1}
        lhs = count * count * B
        rhs = C_RATIONAL * C_RATIONAL * (odd_count * odd_count)
        checks.append({"B": B, "fail": count, "survivors": odd_count - count,
                       "odd_residues": odd_count,
                       "fraction": float(Fraction(count, odd_count)),
                       "bound": C_RATIONAL / math.sqrt(B),
                       "integer_lhs": lhs, "integer_rhs": rhs, "ok": lhs <= rhs})
    return {"K": K, "checks": checks, "max_ratio_seen": float(max_seen),
            "all_ok": all(c["ok"] for c in checks)}


# ---------------------------------------------------------------------------
# 3. rational tilt certificates and composition generating function
# ---------------------------------------------------------------------------
def check_tilt_certificates() -> dict:
    certs = {
        "x_sq_ge_half": X_TILT ** 2 >= Fraction(1, 2),
        "beta_sq_ge_three": BETA ** 2 >= 3,
        "z": str(Z_TILT), "m": str(M_TILT), "rho": str(RHO),
        "rho_lt_one": RHO < 1,
        "C": str(RHO / (1 - RHO)),
        "C_eq_26": RHO / (1 - RHO) == C_RATIONAL,
    }
    certs["all_ok"] = (certs["x_sq_ge_half"] and certs["beta_sq_ge_three"]
                       and certs["rho_lt_one"] and certs["C_eq_26"])
    return certs


@lru_cache(maxsize=None)
def compCount(M: int, E: int) -> int:
    """Number of M-tuples of positive naturals summing to E."""
    if M == E:
        return 1
    if M == 0 or E == 0 or E < M:
        return 0
    return compCount(M - 1, E - 1) + compCount(M, E - 1)


def check_gen_function() -> dict:
    rows = []
    ok_all = True
    for j in range(1, 13):
        for K in [j, 2 * j, 4 * j]:
            lhs = sum(Fraction(compCount(j, E)) * Z_TILT ** E for E in range(j, K + 1))
            rhs = M_TILT ** j
            ok = lhs <= rhs
            ok_all &= ok
            rows.append({"j": j, "K": K, "lhs": float(lhs),
                         "rhs": float(rhs), "ok": ok})
    return {"all_ok": ok_all, "rows": rows}


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------
def main() -> None:
    ratio = check_prefix_ratio_bound()
    certs = check_tilt_certificates()
    genf = check_gen_function()
    k_rows = [prefix_max_excursion_counts(K, THRESHOLDS) for K in range(1, 17)]
    # additional large thresholds where the certificate is genuinely restrictive
    big = prefix_max_excursion_counts(16, EXTRA_THRESHOLDS)

    optimal_C = (math.sqrt(3) / (2 * math.sqrt(2) - 1)) / (1 - math.sqrt(3) / (2 * math.sqrt(2) - 1))

    report = {
        "layer": 6,
        "title": "Uniform prefix-maximum upward excursion tail for Syracuse orbits",
        "certified_constant": C_RATIONAL,
        "optimal_constant_at_lambda_half": optimal_C,
        "tilt": {"lambda": "1/2", "x": str(X_TILT), "beta": str(BETA),
                 "z": str(Z_TILT), "m": str(M_TILT), "rho": str(RHO)},
        "prefix_ratio_bound": ratio,
        "tilt_certificates": certs,
        "composition_generating_function": genf,
        "modulus_scan_K_1_to_16": k_rows,
        "large_threshold_scan_K16": big,
        "all_ok": (ratio["all_ok"] and certs["all_ok"] and genf["all_ok"]
                   and all(r["all_ok"] for r in k_rows) and big["all_ok"]),
    }

    os.makedirs(ARTIFACT_DIR, exist_ok=True)
    out = os.path.join(ARTIFACT_DIR, "excursion_tail.json")
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=2)

    lines = [
        "Layer 6 -- prefix-maximum upward excursion tail (exact verification)",
        "=" * 72,
        f"prefix ratio bound all_ok            : {ratio['all_ok']}",
        f"rational tilt certificates all_ok    : {certs['all_ok']}",
        f"composition generating fn all_ok     : {genf['all_ok']}",
        f"C (certified)                        : {C_RATIONAL}",
        f"C (optimal at lambda=1/2)            : {optimal_C:.6f}",
        f"ALL CHECKS PASS                      : {report['all_ok']}",
        "",
        "K   B    fail/odd         empirical      bound 26/sqrt(B)   ok",
        "-" * 72,
    ]
    for row in k_rows:
        for c in row["checks"]:
            lines.append(f"{row['K']:<3d} {c['B']:<4d} {c['fail']:>6d}/{c['odd_residues']:<8d} "
                         f"{c['fraction']:>10.5f}      {c['bound']:>10.5f}      {c['ok']}")
    lines += ["", "Large thresholds (K=16), where the bound is nontrivial:", "-" * 72]
    for c in big["checks"]:
        lines.append(f"16  {c['B']:<4d} {c['fail']:>6d}/{c['odd_residues']:<8d} "
                     f"{c['fraction']:>10.8f}      {c['bound']:>10.8f}      {c['ok']}")
    text = "\n".join(lines) + "\n"
    print(text)
    with open("analysis/excursion_tail.txt", "w", encoding="utf-8") as fh:
        fh.write(text)
    if not report["all_ok"]:
        raise SystemExit("FAIL: a verification check did not pass")


if __name__ == "__main__":
    main()
