#!/usr/bin/env python3
"""
Phase 1 -- Syracuse renewal, exact valuation MGF, Cramer rate, and the
exponential concentration of multi-step Syracuse products (Layer 5,
Collatz-adic Lean).

MODEL
-----
For odd n let a(n) = v2(3n+1) >= 1 and T_syr(n) = (3n+1)/2^{a(n)}.
The accelerated valuations a_0, a_1, ... along the odd-to-odd orbit are i.i.d.
with the geometric law  P(a = j) = 2^{-j}  (j >= 1).  This is the exact
K -> infinity form of the verified finite counting law

    #{odd r mod 2^K : v2(3r+1) = a} = 2^{K-a-1}   (1 <= a < K),
    #{odd r mod 2^K : v2(3r+1) >= K} = 1,

i.e. `exactValF_card` in CollatzAdicBase/SyracuseLogDrift.lean.

EXACT MOMENT GENERATING FUNCTION
--------------------------------
With x = 2^{-lambda} in (0, 2) (equivalently lambda > -1):

    E[x^a] = sum_{j>=1} 2^{-j} x^j = x/(2-x) = 1/(2^{lambda+1}-1).

We check this as an EXACT identity of Fractions for rational x = 1/u, and
verify that the finite valuation counts mod 2^K converge to it.

CRAMER / CHERNOFF RATE
----------------------
A_M = a_0 + ... + a_{M-1} has E[A_M] = 2M.  The non-contraction event is
3^M >= 2^{A_M}, i.e. A_M <= M log_2 3 (log_2 3 = 1.58496... < 2), a LEFT
large deviation.  Markov's inequality applied to x^{A_M}, 0 < x < 1, gives

    P(3^M >= 2^{A_M}) <= ( x^{-log_2 3} * x/(2-x) )^M
                       = ( t^{c} / (2t-1) )^M,   t = 1/x = 2^lambda > 1,

with c = log_2 3.  The Cramer optimum satisfies the tilted-mean equation
c = u/(u-1) with u = 2^{lambda+1} = 2t, whose solution is

    t* = c / (2(c-1)) = 1.3547556...,   rho* = (t*)^c/(2t*-1) = 0.94650...,
    I*  = -ln rho*     = 0.054979...   (nats per accelerated step).

Using the certified rational upper bound  log_2 3 <= 8/5  (3^5 = 243 < 256)
the same argument with a rational tilt t = (21/20)^5 gives the fully rational
bound P <= rho^M with

    rho = (21/20)^8 / (2*(21/20)^5 - 1) = 37822859361/39745616000 < 1.

The sharper irrational optimum rho* = 0.94650... is below this rational base.

INDEPENDENT TERRAS CERTIFICATE
------------------------------
Because the accelerated valuation sum A_M is the index of the (M+1)-st odd
half-step, failure with M = 5t forces the parity weight w_{8t} >= 5t+1.
The verified GlideMarkovChain bound then gives the fraction of failing odd
classes <= (6561/8192)^t <= (24/25)^{5t}.

No third-party packages are required (only fractions / math / json).
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction

ARTIFACT_DIR = "/home/nix/.local/share/openresearch/files/collatz-adic-lean"
C = math.log2(3.0)                       # log_2 3 ~ 1.5849625007
RATIONAL_C = Fraction(8, 5)              # 3^5 < 2^8 => log_2 3 < 8/5
CERT_RHO = Fraction(21, 20) ** 8 / (2 * Fraction(21, 20) ** 5 - 1)
TERRAS_CERT = Fraction(24, 25)           # (24/25)^5 > 6561/8192
CRAMER_CERT = CERT_RHO                   # fully rational Chernoff base < 1


# ---------------------------------------------------------------------------
# 1. exact valuation law (the finite law behind the renewal MGF)
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


def valuation_counts(K: int) -> dict[int, int]:
    counts: dict[int, int] = {}
    for r in range(1, 1 << K, 2):
        a = v2(3 * r + 1)
        counts[a] = counts.get(a, 0) + 1
    return counts


def check_geometric_law(Kmax: int = 14) -> dict:
    rows, ok = [], True
    for K in range(1, Kmax + 1):
        counts = valuation_counts(K)
        expected = {a: 1 << (K - a - 1) for a in range(1, K)}
        small = {a: c for a, c in counts.items() if a < K}
        tail = sum(c for a, c in counts.items() if a >= K)
        good = small == expected and tail == 1 and sum(counts.values()) == 1 << (K - 1)
        ok &= good
        rows.append({"K": K, "counts": counts, "expected": expected,
                     "tail_ge_K": tail, "ok": good})
    return {"rows": rows, "all_ok": ok}


# ---------------------------------------------------------------------------
# 2. exact moment generating function
# ---------------------------------------------------------------------------
def mgf_finite_from_counts(K: int, x: Fraction) -> Fraction:
    """E[x^a] under the exact finite law on odd residues mod 2^K, where the
    exceptional class (a >= K) is evaluated at its exact representative."""
    counts = valuation_counts(K)
    total = Fraction(1 << (K - 1), 1)
    s = Fraction(0)
    for a, c in counts.items():
        s += c * x ** min(a, K)          # valuation >= K contributes x^K or more
    return s / total


def mgf_partial_sum(x: Fraction, N: int) -> tuple[Fraction, Fraction]:
    """Exact partial geometric sum and its closed form; converges to x/(2-x)."""
    y = x / 2
    s = sum((y ** j for j in range(1, N + 1)), Fraction(0))
    closed = y * (1 - y ** N) / (1 - y)
    return s, closed


def check_mgf() -> dict:
    rows, ok = [], True
    for u in [Fraction(2), Fraction(3), Fraction(4), Fraction(5),
              Fraction(3, 2), Fraction(4, 3), Fraction(21, 20)]:
        x = 1 / u
        target = x / (2 - x)             # = 1/(2u - 1)
        alt = 1 / (2 * u - 1)
        s, closed = mgf_partial_sum(x, 80)
        exact_ok = s == closed and target == alt
        # Finite-law expectation converges to the infinite-law MGF.
        finite = mgf_finite_from_counts(12, x)
        tail_bound = (x / 2) ** 12 / (1 - x / 2)
        close_ok = abs(finite - target) <= tail_bound
        ok &= exact_ok and close_ok
        rows.append({
            "u": str(u), "lambda_log2_u": math.log2(float(u)),
            "E_x_pow_a": str(target), "one_over_2u_minus_1": str(alt),
            "finite_K12": str(finite), "partial_sum_N80": str(s),
            "exact_identity": exact_ok, "finite_law_close": close_ok,
        })
    return {"rows": rows, "all_ok": ok}


# ---------------------------------------------------------------------------
# 3. Cramer rate: analytic optimum, numeric check, rational certificates
# ---------------------------------------------------------------------------
def rho_of_t(t: float, c: float = C) -> float:
    return t ** c / (2 * t - 1)


def rate_optimum(c: float = C) -> dict:
    t_star = c / (2 * (c - 1))
    u_star = 2 * t_star
    lam_star = math.log2(t_star)
    rho_star = rho_of_t(t_star, c)
    I_star = -math.log(rho_star)
    # Numeric golden-section confirmation of the analytic minimiser.
    lo, hi = 1.0000001, 2.5
    phi = (math.sqrt(5) - 1) / 2
    a, b = hi - phi * (hi - lo), lo + phi * (hi - lo)
    for _ in range(200):
        if rho_of_t(a, c) < rho_of_t(b, c):
            hi, b = b, a
            a = hi - phi * (hi - lo)
        else:
            lo, a = a, b
            b = lo + phi * (hi - lo)
    t_num = (lo + hi) / 2
    return {
        "c_log2_3": c, "t_star": t_star, "u_star_2lambda_plus_1": u_star,
        "lambda_star": lam_star, "rho_star": rho_star, "I_star_nats": I_star,
        "numeric_argmin": t_num, "numeric_min_rho": rho_of_t(t_num, c),
        "argmin_matches": abs(t_num - t_star) < 1e-7,
        "rho_star_lt_certified": rho_star <= float(CRAMER_CERT),
    }


def rational_threshold_rate() -> dict:
    r = float(RATIONAL_C)
    t_star_r = r / (2 * (r - 1))         # = 4/3 exactly
    rho_star_r = rho_of_t(t_star_r, r)
    s = Fraction(21, 20)                 # t = s^5, so t^{8/5} = s^8
    return {
        "rational_c": str(RATIONAL_C),
        "c_le_r": C <= r,
        "t_star_rational": str(Fraction(4, 3)),
        "rho_star_rational_threshold": rho_star_r,
        "certified_tilt_s": str(s),
        "certified_rho": str(CERT_RHO),
        "certified_rho_float": float(CERT_RHO),
        "certified_rho_lt_one": CERT_RHO < 1,
        "rho_star_le_certified": rho_star_r <= float(CERT_RHO),
    }


# ---------------------------------------------------------------------------
# 4. exact survival probabilities P(3^M >= 2^{A_M}) via compositions
# ---------------------------------------------------------------------------
def max_failing_sum(M: int) -> int:
    """Largest integer E with 2^E <= 3^M."""
    E = 0
    while (1 << (E + 1)) <= 3 ** M:
        E += 1
    return E


def survival_exact(M: int) -> Fraction:
    """P(A_M <= M log_2 3) = sum_{E <= M log_2 3} C(E-1, M-1) 2^{-E}."""
    Emax = max_failing_sum(M)
    return sum((Fraction(math.comb(E - 1, M - 1), 1 << E)
                for E in range(M, Emax + 1)), Fraction(0))


def survival_dp(M: int, Emax: int) -> Fraction:
    """Independent DP check: convolve the geometric law M times."""
    dist = [Fraction(0)] * (Emax + 1)
    dist[0] = Fraction(1)
    for _ in range(M):
        nxt = [Fraction(0)] * (Emax + 1)
        for e, p in enumerate(dist):
            for j in range(1, Emax + 1 - e):
                nxt[e + j] += p * Fraction(1, 1 << j)
        dist = nxt
    return sum(dist[:max_failing_sum(M) + 1], Fraction(0))


def check_survival(Mmax: int = 20) -> dict:
    rows, ok = [], True
    for M in range(1, Mmax + 1):
        surv = survival_exact(M)
        dp = survival_dp(M, max_failing_sum(M))
        Emax = max_failing_sum(M)
        cramer_bound = CRAMER_CERT ** M
        ration_bound = CERT_RHO ** M
        checks = {
            "dp_matches": surv == dp,
            "le_certified_rho": surv <= cramer_bound,
            "le_rational_rho": surv <= ration_bound,
            "le_sharp_rho_star": float(surv) <= rho_of_t(
                C / (2 * (C - 1))) ** M + 1e-12,
        }
        ok &= all(checks.values())
        rows.append({
            "M": M, "failing_sum_max": Emax,
            "survival_exact": f"{surv.numerator}/{surv.denominator}",
            "survival": float(surv),
            "certified_rho_pow_M": float(cramer_bound),
            "rational_rho_pow_M": float(ration_bound),
            "checks": checks,
        })
    return {"rows": rows, "all_ok": ok}


def check_terras_certificate(tmax: int = 4) -> dict:
    """For M = 5t, failing odd classes mod 2^{8t} are Terras survivors, so
    their fraction is <= (6561/8192)^t <= (24/25)^{5t}."""
    rows, ok = [], True
    base = Fraction(6561, 8192)
    for t in range(1, tmax + 1):
        M = 5 * t
        terras = base ** t
        cert = TERRAS_CERT ** M
        good = terras <= cert and cert < 1
        ok &= good
        rows.append({"t": t, "M": M, "terras": str(terras),
                     "cert_24_25_pow_M": str(cert), "ok": good})
    return {"rows": rows, "all_ok": ok,
            "base_relation": "6561/8192 < (24/25)^5"}


# ---------------------------------------------------------------------------
# 5. driver
# ---------------------------------------------------------------------------
def main() -> dict:
    os.makedirs(ARTIFACT_DIR, exist_ok=True)
    result: dict = {}

    print("[1/5] exact geometric valuation law ...", flush=True)
    result["geometric_valuation_law"] = check_geometric_law()
    print("      count 2^{K-a-1} for K=1..14:",
          result["geometric_valuation_law"]["all_ok"], flush=True)

    print("[2/5] exact moment generating function E[2^{-lambda a}] ...", flush=True)
    result["mgf"] = check_mgf()
    print("      E[x^a] = x/(2-x) = 1/(2^{lambda+1}-1):",
          result["mgf"]["all_ok"], flush=True)

    print("[3/5] Cramer / Chernoff rate ...", flush=True)
    result["cramer_rate"] = rate_optimum()
    result["rational_threshold_rate"] = rational_threshold_rate()
    cr = result["cramer_rate"]
    print("      t*=%.8f  lambda*=%.8f  rho*=%.8f  I*=%.8f nats"
          % (cr["t_star"], cr["lambda_star"], cr["rho_star"],
             cr["I_star_nats"]), flush=True)
    print("      certified rational rho =", str(CERT_RHO), "< 1:",
          result["rational_threshold_rate"]["certified_rho_lt_one"], flush=True)

    print("[4/5] exact survival fractions for M=1..20 ...", flush=True)
    result["survival"] = check_survival(20)
    print("      all exact survival fractions <= rho^M:",
          result["survival"]["all_ok"], flush=True)
    for row in result["survival"]["rows"]:
        print("      M=%2d  P=% .9f  rho^M=% .9f"
              % (row["M"], row["survival"], row["certified_rho_pow_M"]),
              flush=True)

    print("[5/5] independent Terras certificate ...", flush=True)
    result["terras_certificate"] = check_terras_certificate()
    print("      (6561/8192)^t <= (24/25)^{5t}:",
          result["terras_certificate"]["all_ok"], flush=True)

    result["all_checks_pass"] = all([
        result["geometric_valuation_law"]["all_ok"],
        result["mgf"]["all_ok"],
        cr["argmin_matches"] and cr["rho_star_lt_certified"],
        result["rational_threshold_rate"]["certified_rho_lt_one"],
        result["survival"]["all_ok"],
        result["terras_certificate"]["all_ok"],
    ])

    out = os.path.join(ARTIFACT_DIR, "syracuse_renewal.json")
    with open(out, "w") as f:
        json.dump(result, f, indent=2)
    print("wrote", out, " all checks pass:", result["all_checks_pass"], flush=True)
    return result


if __name__ == "__main__":
    main()
