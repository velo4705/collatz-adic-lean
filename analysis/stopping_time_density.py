#!/usr/bin/env python3
"""
Phase 1 -- two-block 2-adic drift and stopping-time residue densities
for the Collatz-adic Lean project (Paper 7).

Two distinct computations are performed, both with exact integer arithmetic:

(A) EXACT TWO-BLOCK DRIFT
    Start at an odd landing n with k = tau(n) = v2(n+1) >= 1, so n = 2^k q - 1
    with q odd.  FuelLaw burns the k-bit reservoir in 2k ordinary Collatz
    steps:  T^(2k)(n) = 3^k q - 1 = 2^s u  (u odd, s = v2(3^k q - 1) >= 1).
    Refueling then lands on u after s further halvings.  Composing the two
    blocks gives the EXACT affine identity

        2^(k+s) * u = 3^k * n + (3^k - 2^k),     n = 2^k q - 1,

    so the two-block net multiplier is u/n and the logarithmic drift is

        log(u/n) = k log(3/2) - s log 2  +  o(1)   (large q).

    Under the translation-invariant 2-adic measure on odd integers,
    P(k=j) = P(s=j) = P(r=j) = 2^-j (j>=1), E[k]=E[s]=E[r]=2, and the joint
    refueling density of Refueling is P(s=i, r=j) = 2^-(i+j).  Hence

        E[log drift per cycle] = 2 log 3 - 4 log 2 = log(9/16) ~ -0.575364,
        E[steps per cycle]     = E[2k+s] = 6,
        E[log drift per step]  = log(9/16)/6 ~ -0.095894.

    The script verifies the affine identity, the exact valuation laws, and the
    empirical drift against these predictions over odd n up to a large limit.

(B) STOPPING-TIME RESIDUE DENSITY delta(K)
    For an odd residue r mod 2^K we follow the Collatz trajectory *symbolically*:
    after t ordinary steps,

        T^t(n) = (a*n + b) / 2^e,     a odd,

    valid for every n == r (mod 2^K) as long as e+1 <= K (the parity of the
    current value is then determined by n mod 2^(e+1)).  Update rules:

        even value:  (a,b,e) -> (a, b, e+1)
        odd  value:  (a,b,e) -> (3a, 3b + 2^e, e)

    If a < 2^e at some step t, then T^t(n) < n for every n > b/(2^e-a) in the
    class (small exceptions checked directly), i.e. the class has a finite
    stopping-time certificate.  delta(K) = (# odd classes mod 2^K with NO such
    certificate within K bits) / 2^(K-1).

    The all-ones class r = 2^K - 1 always survives (after K shortcuts the
    multiplier is 3^K > 2^K), so delta(K) >= 2^-(K-1) > 0 for EVERY K:
    100% certification at a finite modulus is impossible.  The script computes
    the exact table for K = 1..14 and the kernel-checked K = 8 partition
    (109 certified / 19 surviving odd classes).

Output: a JSON artifact in the project artifacts directory, plus a console
summary.  No third-party packages are required.
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction

ARTIFACT_DIR = "/home/nix/.local/share/openresearch/files/collatz-adic-lean"
HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------
# exact 2-adic primitives
# ---------------------------------------------------------------------------
def v2(x: int) -> int:
    """2-adic valuation; v2(0) = 0 by convention."""
    return 0 if x == 0 else (x & -x).bit_length() - 1


def tau(n: int) -> int:
    """Trailing ones of an odd n: tau(n) = v2(n+1)."""
    return v2(n + 1)


def collatz(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def burn_fuel(n: int):
    """Return (k, q, s, u, r) for odd n = 2^k q - 1.

    k = tau(n), q = odd core, s = v2(3^k q - 1), u = odd landing after
    2k+s Collatz steps, r = tau(u) = v2(u+1).
    """
    assert n % 2 == 1 and n >= 1
    k = tau(n)
    q = (n + 1) >> k
    assert q % 2 == 1
    A = 3 ** k * q
    s = v2(A - 1)
    assert s >= 1
    u = (A - 1) >> s
    assert u % 2 == 1 and u >= 1
    r = v2(u + 1)
    return k, q, s, u, r


# ---------------------------------------------------------------------------
# (A) two-block drift
# ---------------------------------------------------------------------------
def two_block_identity(n: int) -> dict:
    """Verify the exact two-block affine identity on a single odd n."""
    k, q, s, u, r = burn_fuel(n)
    lhs = 2 ** (k + s) * u
    rhs = 3 ** k * n + (3 ** k - 2 ** k)
    assert lhs == rhs, (n, k, q, s, u, r, lhs, rhs)
    # independent check: landing via Refueling.refuel_landing
    x = n
    for _ in range(2 * k + s):
        x = collatz(x)
    assert x == u, (n, k, q, s, u, x)
    # refuel congruence: 2^(s+r) | 3^k q + 2^s - 1, exact at r
    M = 1 << (s + r)
    assert (3 ** k * q + (1 << s) - 1) % M == 0
    assert (3 ** k * q + (1 << s) - 1) % (2 * M) != 0
    return {
        "n": n, "k": k, "q": q, "s": s, "u": u, "r": r,
        "log_drift": math.log(u / n),
        "predicted_drift": k * math.log(1.5) - s * math.log(2.0),
        "net_multiplier": u / n,
    }


def verify_drift(limit: int = 1_000_000) -> dict:
    """Exhaustive verification of two-block identities over odd n <= limit."""
    checked = 0
    sk = ss = sld = spred = 0.0
    k_hist = [0] * 24
    s_hist = [0] * 24
    r_hist = [0] * 24
    sample = []
    for n in range(1, limit + 1, 2):
        k, q, s, u, r = burn_fuel(n)
        lhs = 2 ** (k + s) * u
        rhs = 3 ** k * n + (3 ** k - 2 ** k)
        assert lhs == rhs
        if k < len(k_hist):
            k_hist[k] += 1
        if s < len(s_hist):
            s_hist[s] += 1
        if r < len(r_hist):
            r_hist[r] += 1
        ld = math.log(u / n)
        pd = k * math.log(1.5) - s * math.log(2.0)
        sk += k
        ss += s
        sld += ld
        spred += pd
        checked += 1
        if n <= 21:
            sample.append(two_block_identity(n))

    # exact combinatorial expectation from the geometric 2-adic law
    # P(k=j)=P(s=j)=P(r=j)=2^-j, E[k]=E[s]=E[r]=2
    E_k = sum(j * Fraction(1, 2 ** j) for j in range(1, 80))
    E_s = E_k
    exact_coeff_log3, exact_coeff_log2 = E_k, E_k + E_s  # =2, 4
    pred = float(exact_coeff_log3) * math.log(3) - float(exact_coeff_log2) * math.log(2)

    return {
        "odd_n_checked": checked,
        "E_k_empirical": sk / checked,
        "E_s_empirical": ss / checked,
        "mean_log_drift_empirical": sld / checked,
        "mean_predicted_drift_klog3_2_slog2": spred / checked,
        "exact_expectation_log9_16": pred,
        "exact_coefficients": {
            "log3": str(exact_coeff_log3), "log2": str(exact_coeff_log2),
        },
        "E_steps_per_cycle": 6,
        "log_drift_per_step": pred / 6,
        "k_distribution": {j: c for j, c in enumerate(k_hist) if c},
        "s_distribution": {j: c for j, c in enumerate(s_hist) if c},
        "r_distribution": {j: c for j, c in enumerate(r_hist) if c},
        "sample_identities": sample,
        "small_n_checks": [two_block_identity(n) for n in (6631675,)],
    }


# ---------------------------------------------------------------------------
# (B) residue sieve
# ---------------------------------------------------------------------------
def template(r: int, K: int, max_steps: int = 400):
    """Run the symbolic Collatz template on odd residue r mod 2^K.

    Returns (certified, t, a, b, e, max_e) where max_e is the largest exponent
    used (the certificate is valid iff max_e + 1 <= K and a < 2^e).
    """
    a, b, e = 1, 0, 0
    max_e = 0
    for t in range(max_steps):
        if e + 1 > K:
            break
        val = (a * r + b) % (1 << (e + 1))
        assert val % (1 << e) == 0
        parity = val >> e
        if parity == 0:                     # even: halve
            e += 1
        else:                                # odd: 3x+1
            b = 3 * b + (1 << e)
            a = 3 * a
        max_e = max(max_e, e)
        if a < (1 << e):
            threshold = b // ((1 << e) - a)
            return True, t + 1, a, b, e, max_e, threshold
    return False, max_steps, a, b, e, max_e, None


def sieve(K: int, max_steps: int = 400):
    """Return (certified dict, survivors list) over odd residues mod 2^K."""
    certified, survivors = {}, []
    for r in range(1, 1 << K, 2):
        res = template(r, K, max_steps)
        # The template itself stops before any step needing e+1 > K; the final
        # exponent e may equal K, which is still a valid certificate.
        if res[0]:
            certified[r] = {
                "t": res[1], "a": res[2], "b": res[3],
                "e": res[4], "max_e": res[5], "threshold": res[6],
            }
        else:
            survivors.append(r)
    return certified, survivors


def density_table(Kmax: int = 14) -> dict:
    rows = []
    for K in range(1, Kmax + 1):
        certified, survivors = sieve(K)
        total = 1 << (K - 1)
        frac = Fraction(len(survivors), total)
        mersenne = (1 << K) - 1
        rows.append({
            "K": K,
            "odd_classes": total,
            "certified": len(certified),
            "survivors": len(survivors),
            "delta_exact": f"{frac.numerator}/{frac.denominator}",
            "delta_float": float(frac),
            "mersenne_survives": mersenne in survivors,
        })
    return {"table": rows, "k8_certified": [], "k8_survivors": []}


def k8_certificate() -> dict:
    """Kernel-style explicit residue partition at K = 8 (modulus 256)."""
    K = 8
    certified, survivors = sieve(K)
    # Verify the symbolic lifting on concrete n = r + 256*m for m in range.
    lift_checks = 0
    for r, data in certified.items():
        a, b, e, t = data["a"], data["b"], data["e"], data["t"]
        den = 1 << e
        assert a < den
        for m in range(0, 60):
            n = r + (1 << K) * m
            if n <= 1:
                continue
            # symbolic landing: den * T^t(n) = a*n + b
            x = n
            for _ in range(t):
                x = collatz(x)
            assert den * x == a * n + b, (r, m, n, t, a, b, e)
            assert x < n, (r, m, n, x)
            lift_checks += 1
    return {
        "modulus": 1 << K,
        "odd_classes": 128,
        "certified_count": len(certified),
        "survivor_count": len(survivors),
        "certified_density": f"{len(certified)}/128",
        "delta_8": f"{len(survivors)}/128",
        "survivor_residues": sorted(survivors),
        "certified_residues": sorted(certified),
        "template_examples": {str(r): certified[r] for r in sorted(certified)[:20]},
        "lift_checks": lift_checks,
    }


def main():
    os.makedirs(ARTIFACT_DIR, exist_ok=True)
    results = {}

    print("[1/3] two-block drift verification, odd n <= 1,000,000 ...", flush=True)
    results["drift"] = verify_drift()
    d = results["drift"]
    print("      E[k] = %.6f, E[s] = %.6f" % (d["E_k_empirical"], d["E_s_empirical"]))
    print("      mean log drift = %.9f  |  log(9/16) = %.9f"
          % (d["mean_log_drift_empirical"], d["exact_expectation_log9_16"]), flush=True)

    print("[2/3] stopping-time densities delta(K), K = 1..14 ...", flush=True)
    results["density"] = density_table()
    for row in results["density"]["table"]:
        print("      K=%2d: %4d/%4d certified, delta=%8s  (Mersenne survives: %s)"
              % (row["K"], row["certified"], row["odd_classes"],
                 row["delta_exact"], row["mersenne_survives"]), flush=True)

    print("[3/3] K=8 residue partition certificate ...", flush=True)
    results["k8"] = k8_certificate()
    print("      certified = %d/128, delta(8) = %d/128, lift checks = %d"
          % (results["k8"]["certified_count"], results["k8"]["survivor_count"],
             results["k8"]["lift_checks"]), flush=True)

    out = os.path.join(ARTIFACT_DIR, "stopping_time_density.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print("      wrote", out, flush=True)
    return results


if __name__ == "__main__":
    main()
