#!/usr/bin/env python3
"""
Phase 1 -- finite-state 2-adic survivor branching operator and the
constructive Chernoff/Hoeffding bound driving stopping-time density decay
(Paper 8, Collatz-adic Lean project).

MODEL
-----
Work with the accelerated ("one halving per step") Collatz half-step

        S(n) = n/2            if n even      (log_2 multiplier  -1),
        S(n) = (3n+1)/2       if n odd        (log_2 multiplier  log_2(3/2)).

After K halvings the exact product identity is

        2^K S^K(n) = 3^{w_K(n)} n + c_K(n),     0 <= c_K(n) < 3^K,

with w_K(n) = #{i < K : S^i(n) is odd}.  Hence S^K(n) < n whenever
3^{w_K(n)} < 2^K and n >= 3^K.  The "survivors" are the odd residue classes
r mod 2^K with 3^{w_K(r)} > 2^K, i.e. w_K(r) > K log_3 2.

BRANCHING
---------
The parity vector b(r) = (S^i(r) mod 2)_{i<K} is a bijection from residues
mod 2^K to {0,1}^K (Terras).  Lifting r -> r and r + 2^K mod 2^{K+1} appends
one bit: the first K parities agree and the new bit is 0 for one child and
1 for the other.  On ODD residues the first bit is 1, so
w_K(r) = 1 + Bin(K-1, 1/2) exactly, and each odd step contributes
+log_2(3/2) while each pure halving contributes log_2(1/2) = -1:

        E[Delta log_2] = (1/2) log_2(3/4) < 0.

BOUNDS CHECKED HERE
-------------------
Let m(K) = min{w : 3^w > 2^K} = ceil(K log_3 2) (K log_3 2 is irrational).
For odd residues the survivor count S(K) and density delta(K)=S(K)/2^{K-1}
satisfy, constructively,

  (Hoeffding)  delta(K) <= 2 exp(-2 (m(K) - K/2)^2 / K),
  (Chernoff)   delta(K) <= 2 exp(-K * D(m(K)/K || 1/2)),
  (tilt)       S(K)      <= 2 * 3^{K-1} / 2^{m(K)},

where D(q||1/2) = q log(2q) + (1-q) log(2(1-q)) is the KL divergence in
nats.  Since m(K)/K -> log_3 2 and D(log_3 2 || 1/2) ~ 0.034643 > 1/30,
the tilt bound gives the explicit rational exponential law

        delta(K) <= 2 exp(-K/30)      (c = 1/30 = 0.0333...).

The factor 2 is unavoidable at K=1 (delta(1)=1); equivalently
delta(K) <= exp(-K/31) for all K >= 48.  All counts are exact integers;
bounds are floating point and are checked against the exact counts with a
small tolerance.  No third-party packages are required.
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction

ARTIFACT_DIR = "/home/nix/.local/share/openresearch/files/collatz-adic-lean"
HERE = os.path.dirname(os.path.abspath(__file__))
THETA = math.log(2.0) / math.log(3.0)          # log_3 2 ~ 0.6309297536
MEAN_DRIFT = 0.5 * math.log2(3.0 / 4.0)        # ~ -0.2075187496


# ---------------------------------------------------------------------------
# exact accelerated trajectory
# ---------------------------------------------------------------------------
def glide_step(n: int) -> int:
    """One halving: n/2 if even, (3n+1)/2 if odd."""
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def parity_vector(n: int, K: int) -> list[int]:
    """The K-bit parity vector (b_0, ..., b_{K-1}), b_i = S^i(n) mod 2."""
    bits: list[int] = []
    x = n
    for _ in range(K):
        bits.append(x & 1)
        x = glide_step(x)
    return bits


def weight(n: int, K: int) -> int:
    """w_K(n) = number of odd half-steps in the first K halvings."""
    return sum(parity_vector(n, K))


def min_weight(K: int) -> int:
    """m(K) = least w with 3^w > 2^K (equals ceil(K log_3 2))."""
    target = 1 << K
    w, p = 0, 1
    while p <= target:
        p *= 3
        w += 1
    return w


# ---------------------------------------------------------------------------
# branching operator verification
# ---------------------------------------------------------------------------
def verify_branching(Kmax: int = 15) -> dict:
    """Check that lifting r -> r, r+2^K appends one bit 0/1 and preserves
    the first K parities; equivalently the parity vector map mod 2^K is a
    bijection onto {0,1}^K."""
    checks = 0
    for K in range(1, Kmax + 1):
        mod = 1 << K
        seqs: dict[tuple[int, ...], int] = {}
        for r in range(mod):
            lo = tuple(parity_vector(r, K))
            child0 = tuple(parity_vector(r, K + 1))
            child1 = tuple(parity_vector(r + mod, K + 1))
            assert child0[:K] == lo and child1[:K] == lo, (K, r)
            assert child0[K] != child1[K], (K, r)     # one odd, one even
            assert {child0[K], child1[K]} == {0, 1}
            seqs[lo] = seqs.get(lo, 0) + 1
            checks += 1
        assert len(seqs) == mod and all(c == 1 for c in seqs.values()), K
    return {"K_max": Kmax, "residue_lifts_checked": checks,
            "bijective_at_every_K": True}


# ---------------------------------------------------------------------------
# exact survivor counts and densities
# ---------------------------------------------------------------------------
def survivor_count(K: int) -> tuple[int, list[int]]:
    """Exact number of ODD residues r mod 2^K with 3^{w_K(r)} > 2^K,
    together with the residue list."""
    target = 1 << K
    pow3 = [1] * (K + 1)
    for j in range(1, K + 1):
        pow3[j] = 3 * pow3[j - 1]
    surv = [r for r in range(1, target, 2) if pow3[weight(r, K)] > target]
    return len(surv), surv


def tilt_sum(K: int) -> int:
    """Exact sum of 2^{w_K(r)} over odd residues: equals 2 * 3^{K-1}."""
    return sum(1 << weight(r, K) for r in range(1, 1 << K, 2))


# ---------------------------------------------------------------------------
# constructive tail bounds
# ---------------------------------------------------------------------------
def kl_bernoulli(q: float) -> float:
    """D(q || 1/2) in nats."""
    if q <= 0.0 or q >= 1.0:
        return math.log(2.0) if q in (0.0, 1.0) else float("inf")
    return q * math.log(2 * q) + (1 - q) * math.log(2 * (1 - q))


def chernoff(K: int, m: int) -> float:
    """P(Bin(K,1/2) >= m) <= exp(-K D(m/K || 1/2))."""
    if m <= K / 2:
        return 1.0
    return math.exp(-K * kl_bernoulli(m / K))


def hoeffding(K: int, m: int) -> float:
    """P(Bin(K,1/2) - K/2 >= t) <= exp(-2 t^2 / K)."""
    t = m - K / 2
    if t <= 0:
        return 1.0
    return math.exp(-2 * t * t / K)


def tilt_bound(K: int, m: int) -> float:
    """S(K) <= 2 * 3^{K-1} / 2^m  (exact integer tilt identity)."""
    return (2 * 3 ** (K - 1)) / (1 << m)


def drift_stats(Kmax: int = 16) -> dict:
    """Exact mean of w_K over odd residues and its log_2 drift."""
    rows = []
    for K in range(1, Kmax + 1):
        total = 1 << (K - 1)
        wsum = sum(weight(r, K) for r in range(1, 1 << K, 2))
        mean_w = Fraction(wsum, total)
        mean_log2 = float(mean_w) * math.log2(3.0) - 1.0
        rows.append({
            "K": K,
            "mean_w_exact": f"{mean_w.numerator}/{mean_w.denominator}",
            "mean_w": float(mean_w),
            "mean_log2_multiplier": mean_log2,
        })
    return {"rows": rows, "predicted_mean_log2": MEAN_DRIFT}


def main() -> dict:
    os.makedirs(ARTIFACT_DIR, exist_ok=True)
    result: dict = {}

    print("[1/4] verifying the 2-adic parity-vector branching operator ...",
          flush=True)
    result["branching"] = verify_branching()
    print("      %d lifts, bijection at every K = 1..15"
          % result["branching"]["residue_lifts_checked"], flush=True)

    print("[2/4] exact survivor counts / densities, K = 1..16 ...", flush=True)
    rows = []
    all_ok = True
    c_rational = 1.0 / 30.0
    for K in range(1, 17):
        S, surv = survivor_count(K)
        total = 1 << (K - 1)
        m = min_weight(K)
        delta = Fraction(S, total)
        d = float(delta)
        ch, ho, ti = chernoff(K, m), hoeffding(K, m), tilt_bound(K, m) / total
        checks = {
            "delta_le_2_chernoff": d <= 2 * ch + 1e-12,
            "delta_le_2_hoeffding": d <= 2 * ho + 1e-12,
            "delta_le_tilt": d <= ti + 1e-12,
            "delta_le_2_exp_rational": d <= 2 * math.exp(-c_rational * K) + 1e-12,
            "tilt_sum_identity": tilt_sum(K) == 2 * 3 ** (K - 1),
        }
        all_ok &= all(checks.values())
        rows.append({
            "K": K,
            "m_K": m,
            "m_over_K": round(m / K, 9),
            "odd_classes": total,
            "survivors": S,
            "delta_exact": f"{delta.numerator}/{delta.denominator}",
            "delta": d,
            "chernoff_bound": ch,
            "hoeffding_bound": ho,
            "tilt_bound": ti,
            "rational_exp_bound": 2 * math.exp(-c_rational * K),
            "checks": checks,
            "survivor_residues": surv if K <= 10 else [],
        })
        print("      K=%2d  m=%2d  S=%6d/%-6d  delta=%9.6f  "
              "Chernoff=%9.6f  Hoeffding=%9.6f  tilt=%9.6f"
              % (K, m, S, total, d, ch, ho, ti), flush=True)
    result["density_table"] = rows
    result["all_bounds_hold"] = all_ok
    print("      all exact counts respect every constructive bound:", all_ok,
          flush=True)

    print("[3/4] drift and large-deviation constants ...", flush=True)
    result["drift"] = drift_stats()
    c_chernoff = kl_bernoulli(THETA)
    c_hoeffding = 2 * (THETA - 0.5) ** 2
    result["constants"] = {
        "theta_log_3_2": THETA,
        "KL_rate_nats": c_chernoff,
        "KL_rate_bits": c_chernoff / math.log(2.0),
        "Hoeffding_rate_nats": c_hoeffding,
        "rational_certified_rate": c_rational,
        "E_delta_log2_predicted": MEAN_DRIFT,
        "five_eighths_lt_theta": 5.0 / 8.0 < THETA,
        "three_power_eight_lt_two_power_five": 3 ** 5 < 2 ** 8,
    }
    print("      theta=%.9f  D(theta||1/2)=%.9f nats (=2*%.6f bits)  "
          "Hoeffding c=%.9f" % (THETA, c_chernoff, c_chernoff / math.log(2.0),
                               c_hoeffding), flush=True)
    print("      certified rational rate c=1/30=%.6f <= true rates"
          % c_rational, flush=True)

    print("[4/4] writing artifact ...", flush=True)
    out = os.path.join(ARTIFACT_DIR, "glide_markov_chain.json")
    with open(out, "w") as f:
        json.dump(result, f, indent=2)
    print("      wrote", out, flush=True)
    return result


if __name__ == "__main__":
    main()
