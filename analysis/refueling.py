#!/usr/bin/env python3
"""
Phase 1 -- exact 2-adic "mid-flight refueling" analysis for
"Trailing Ones and High-Altitude Backbones" (Paper 2, Section 6).

 mathematics
 -----------
 For an odd n with tau(n) = v2(n+1) = k >= 1 write n = 2^k q - 1 with q odd.
 The shortcut phi(m) = (3m+1)/2 satisfies phi^j(n) = 3^j 2^(k-j) q - 1 for
 0 <= j <= k (Paper 2, Prop. 4 / FuelLaw.lean).  After k shortcut steps
 (= 2k ordinary Collatz steps) the fuel block is exhausted:

     phi^k(n) = 3^k q - 1 = 2^s * u,   u odd,  s = v2(3^k q - 1) >= 1.

 s further halvings land on the odd core u (the "next odd landing"), whose
 trailing-ones reservoir is r = tau(u) = v2(u+1).  Since

     3^k q + 2^s - 1 = 2^s (u + 1),

 we obtain the EXACT REFUELING CONGRUENCE (for every R >= 1):

     v2(u+1) >= R   <=>   2^(s+R) | 3^k q + 2^s - 1
                     <=>  3^k q = 1 - 2^s   (mod 2^(s+R))
                     <=>  q = (1-2^s) * (3^k)^(-1)   (mod 2^(s+R)).

 The last equivalence uses that 3^k is odd, hence invertible mod 2^m; the
 inverse exists by Hensel lifting (formalized in Refueling.lean).

 This script verifies the criterion exhaustively for odd n <= 10^7, traces the
 record n = 6,631,675 and the tau = 18 witnesses, and re-derives the 97
 high-altitude backbones from the cached top-500 CSV.
"""

from __future__ import annotations

import csv
import json
import os
import sys
from collections import Counter, defaultdict

LIMIT = 10_000_000
ARTIFACT_DIR = "/home/nix/.local/share/openresearch/files/collatz-adic-lean"
HERE = os.path.dirname(os.path.abspath(__file__))


# --------------------------------------------------------------------------
# basic 2-adic primitives (exact integer arithmetic)
# --------------------------------------------------------------------------
def v2(x: int) -> int:
    """2-adic valuation; v2(0) = 0 by convention."""
    if x == 0:
        return 0
    return (x & -x).bit_length() - 1


def tau(n: int) -> int:
    """Trailing ones of an odd n: tau(n) = v2(n+1)."""
    return v2(n + 1)


def collatz(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def shortcut(m: int) -> int:
    return (3 * m + 1) // 2


def burn_fuel(n: int):
    """Return (k, q, s, u, r) for odd n = 2^k q - 1 (q odd).

    k = initial trailing ones, q = odd core, s = v2(3^k q - 1),
    u = odd landing after 2k+s Collatz steps, r = tau(u) = v2(u+1).
    """
    assert n % 2 == 1 and n >= 1
    k = tau(n)
    q = (n + 1) >> k
    assert q % 2 == 1
    A = 3 ** k * q                 # A - 1 = phi^k(n)
    s = v2(A - 1)
    assert s >= 1
    u = (A - 1) >> s
    assert u % 2 == 1 and u >= 1
    r = v2(u + 1)
    return k, q, s, u, r


def criterion_holds(q: int, k: int, s: int, R: int) -> bool:
    """True iff 3^k q = 1 - 2^s (mod 2^(s+R)), i.e. v2(u+1) >= R."""
    M = 1 << (s + R)
    return (3 ** k * q + (1 << s) - 1) % M == 0


def residue_class(k: int, s: int, R: int) -> int:
    """The unique odd residue c mod 2^(s+R) with v2(u+1) >= R."""
    M = 1 << (s + R)
    inv = pow(3 ** k, -1, M)          # (3^k)^(-1) mod 2^(s+R)
    return ((1 - (1 << s)) * inv) % M


# --------------------------------------------------------------------------
# Phase 1a -- exhaustive verification of the criterion, n <= 10^7
# --------------------------------------------------------------------------
def verify_exhaustive(limit: int = LIMIT):
    checked = 0
    failures = []
    r_hist = Counter()
    pair_hist = Counter()            # (s, r) -> exact joint count
    for n in range(1, limit + 1, 2):  # odd n only
        k, q, s, u, r = burn_fuel(n)
        checked += 1
        r_hist[r] += 1
        pair_hist[(s, r)] += 1
        # direction 1: exact r => congruence mod 2^(s+r) and failure at s+r+1
        if not criterion_holds(q, k, s, r):
            failures.append((n, "missing divisibility", k, q, s, u, r))
        if criterion_holds(q, k, s, r + 1):
            failures.append((n, "non-exact valuation", k, q, s, u, r))
        # direction 2: explicit residue class (Hensel inverse)
        if q % (1 << (s + r)) != residue_class(k, s, r):
            failures.append((n, "residue mismatch", k, q, s, u, r))
        # direction 3: the algebraic landing itself (closed form)
        if (3 ** k * q - 1) >> s != u or ((u + 1) >> r) % 2 == 0:
            failures.append((n, "landing mismatch", k, q, s, u, r))
        if len(failures) >= 10:
            break
    # theoretical joint density: P(s = v2(3^k q - 1), r = v2(u+1)) = 2^-(s+r)
    joint = []
    for (s, r), count in sorted(pair_hist.items()):
        if s <= 8 and r <= 10:
            expected = checked / (1 << (s + r))
            joint.append({"s": s, "r": r, "observed": count,
                          "expected": round(expected, 1),
                          "ratio": round(count / expected, 4)})
    return {
        "odd_n_checked": checked,
        "failures": failures,
        "r_histogram": dict(sorted(r_hist.items())),
        "joint_s_r_density": joint,
        "even_reduction_note": "even n reduce to their odd part n/2^v2(n)",
    }


# --------------------------------------------------------------------------
# Phase 1b -- full trajectory tracing & refuel events
# --------------------------------------------------------------------------
def odd_landings(n: int, upto_value: int | None = None):
    """Yield (step, odd_value, tau) for each odd iterate of the trajectory."""
    cur = n
    step = 0
    seen = set()
    while True:
        if cur % 2 == 1:
            t = tau(cur)
            yield step, cur, t
        if upto_value is not None and cur >= upto_value:
            # stop after the first crossing of the altitude threshold
            pass
        cur = collatz(cur)
        step += 1
        if cur == 1 or step > 3000:
            break
        if cur in seen:
            break
        seen.add(cur)


def refuel_events(seed: int, max_step: int = 4000):
    """List every refuel event along a trajectory.

    An event is recorded at an odd landing m with tau(m)=k>0: after burning
    the k-bit block (2k steps) and s halvings we reach odd u with tau(u)=r.
    """
    events = []
    cur = seed
    step = 0
    while step < max_step and cur != 1:
        if cur % 2 == 1:
            k = tau(cur)
            if k >= 1:
                q = (cur + 1) >> k
                A = 3 ** k * q
                s = v2(A - 1)
                u = (A - 1) >> s
                r = v2(u + 1)
                events.append({
                    "t_odd": step,
                    "m": cur,
                    "k": k,
                    "q": q,
                    "s": s,
                    "u": u,
                    "r": r,
                    "modulus": 1 << (s + r),
                    "residue_q": residue_class(k, s, r),
                    "congruence": f"3^{k}*q = 1-2^{s} (mod 2^{s+r})",
                    "reach_step": step + 2 * k + s,
                })
        cur = collatz(cur)
        step += 1
    return events


def trace_to_apex(seed: int, apex: int):
    cur = seed
    path = [cur]
    while cur != apex:
        cur = collatz(cur)
        path.append(cur)
        if len(path) > 5000:
            raise RuntimeError(f"apex {apex} not reached from {seed}")
    return path


# --------------------------------------------------------------------------
# Phase 1c -- verify backbone clustering from cached records
# --------------------------------------------------------------------------
def load_records(path: str):
    rows = []
    with open(path, newline="") as f:
        for row in csv.DictReader(f):
            if row.get("section") == "record":
                rows.append(row)
    return rows


def verify_backbones(records, threshold: int = 10**9):
    paths = []
    for row in records:
        seed = int(row["n"])
        apex = int(row["peak_value"])
        p = trace_to_apex(seed, apex)
        assert p[-1] == apex
        paths.append((seed, apex, p))

    # clustering by shared values above threshold (union-find on seeds)
    parent = list(range(len(paths)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    value_to_index = {}
    for i, (_seed, _apex, p) in enumerate(paths):
        for v in p:
            if v > threshold:
                if v in value_to_index:
                    union(i, value_to_index[v])
                else:
                    value_to_index[v] = i
    comps = defaultdict(list)
    for i in range(len(paths)):
        comps[find(i)].append(i)
    shared_value_backbones = len(comps)

    apex_groups = defaultdict(list)
    for i, (seed, apex, _p) in enumerate(paths):
        apex_groups[apex].append(seed)
    apex_backbones = len(apex_groups)
    multi_apex = sum(1 for g in apex_groups.values() if len(g) >= 2)
    records_in_multi_apex = sum(len(g) for g in apex_groups.values() if len(g) >= 2)
    largest = sorted(((len(v), k) for k, v in apex_groups.items()), reverse=True)[:10]
    rank1_apex = 60342610919632
    rank1 = apex_groups.get(rank1_apex, [])
    return {
        "records": len(paths),
        "threshold": threshold,
        "shared_value_backbones": shared_value_backbones,
        "exact_apex_backbones": apex_backbones,
        "multi_record_apex_groups": multi_apex,
        "records_in_multi_record_apex": records_in_multi_apex,
        "largest_apex_groups": largest,
        "rank1_backbone_seeds": rank1,
        "rank1_backbone_size": len(rank1),
    }


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------
def main():
    os.makedirs(ARTIFACT_DIR, exist_ok=True)
    results = {}

    print("[1/5] exhaustive congruence verification, odd n <= 10^7 ...", flush=True)
    results["exhaustive"] = verify_exhaustive()
    print("      checked", results["exhaustive"]["odd_n_checked"],
          "failures", len(results["exhaustive"]["failures"]), flush=True)

    print("[2/5] trace n = 6,631,675 ...", flush=True)
    n0 = 6_631_675
    k, q, s, u, r = burn_fuel(n0)
    results["rank1"] = {
        "n": n0, "k": k, "q": q, "s": s, "u": u, "r": r,
        "phi_k": 3 ** k * q - 1,
        "reach_step": 2 * k + s,
        "congruence": f"3^{k}*q = 1-2^{s} (mod 2^{s+r})",
        "M": 1 << (s + r),
        "residue_q": residue_class(k, s, r),
        "verified": criterion_holds(q, k, s, r) and not criterion_holds(q, k, s, r + 1),
        "all_refuel_events": refuel_events(n0),
        "max_tau_on_path": max(t for _st, _m, t in odd_landings(n0)),
    }
    print("      k,q,s,u,r =", k, q, s, u, r, flush=True)

    print("[3/5] trace tau=18 witnesses ...", flush=True)
    witnesses = {}
    for rank in (19, 38, 45):
        p = os.path.join(
            "/home/nix/.local/share/openresearch/files/collatz-integers/collatz-sweep",
            "integer_collatz_records.csv")
        rows = load_records(p)
        row = next(x for x in rows if int(x["rank"]) == rank)
        seed = int(row["n"])
        evs = refuel_events(seed)
        first18 = next((e for e in evs if e["r"] >= 18), None)
        witnesses[rank] = {
            "n": seed,
            "apex": int(row["peak_value"]),
            "first_refuel_to_18": first18,
            "num_refuel_events": len(evs),
            "max_tau_on_path": max(t for _st, _m, t in odd_landings(seed)),
        }
    results["tau18_witnesses"] = witnesses

    print("[4/5] verify backbone clustering ...", flush=True)
    rows = load_records(os.path.join(
        "/home/nix/.local/share/openresearch/files/collatz-integers/collatz-sweep",
        "integer_collatz_records.csv"))
    results["backbones"] = verify_backbones(rows)
    print("      backbones:", results["backbones"]["shared_value_backbones"],
          "rank1 size:", results["backbones"]["rank1_backbone_size"], flush=True)

    print("[5/5] write results ...", flush=True)
    out = os.path.join(ARTIFACT_DIR, "refueling_analysis.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print("      wrote", out, flush=True)

    # compact console summary
    print("\nR histogram (immediate refuel r, odd n <= 10^7):",
          results["exhaustive"]["r_histogram"])
    print("Backbones:", results["backbones"]["shared_value_backbones"])
    return results


if __name__ == "__main__":
    main()
