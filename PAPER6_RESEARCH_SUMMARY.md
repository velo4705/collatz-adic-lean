# Paper 6 — Research Summary: Algebraic and Modular Cycle Exclusion

**Goal.** Attack the next structural layer of the Collatz problem on top of the
verified `CollatzAdicBase` library: derive the exact 3-free rational cycle
equation, decompose its cycle sum into trailing-ones blocks using `FuelLaw` and
`Refueling`, extract modular / 2-adic / 3-adic obstructions, and formalize the
results in Lean 4 with a clean axiom audit.

**Deliverables.** `analysis/cycle_exclusion.py` (exact integer computation),
`CollatzAdicBase/CycleExclusion.lean` (kernel-checked formalization), and this
summary. All numerical claims below were recomputed by the script.

---

## 0. Exact model (inherited from the verified library)

A reduced positive rational with odd denominator is a state `(a, d)` with
`a > 0`, `d > 0`, `d` odd, `gcd(a, d) = 1`. The reduced step is

```
step(a,d) = (a/2, d)                                   if a even
step(a,d) = ((3a+d)/g, d/g),  g = gcd(3a+d, d)          if a odd
```

with `g ∣ 3` (`gcd_dvd_three`). `lemma_2_4_and_cor_2_5_three_free_cycles`
proves that a cycle has `3 ∤ d` and constant denominator; then `g = 1` at
every odd step, so on a cycle the map is simply

```
a ↦ a/2          (even step),        a ↦ 3a + d        (odd step).
```

---

## 1. Phase 1 — number-theoretic analysis

### 1.1 The exact cycle-sum equation

Let a cycle have `M` odd steps and `E` halving steps, so its total period is
`L = E + M`. Let `e_0 = 0 < e_1 < … < e_{M-1} < E` be the cumulative halving
counts before each odd step (each odd step is followed by at least one halving,
by `lemma_2_3_forced_halving`). Unrolling the affine maps around the cycle gives

$$
  (2^{E} - 3^{M})\,a \;=\; d\,\widetilde T,
  \qquad
  \widetilde T \;=\; \sum_{j=0}^{M-1} 3^{M-1-j}\,2^{e_j}.
$$

**Notation note.** The user's shorthand `a(2^L − 3^M) = d'·T̃` is the same
identity with `L` denoting the halving count `E`; if `L` denotes the total
step count then the power is `2^{L−M}`. `cycleAcc_EM` in the formalization
proves `L = E + M` exactly, and `cycle_sum_identity` proves the identity.

The sum `T̃` is precisely the trailing-ones-block decomposition: the recursion
`T ← 3T + 2^E` at each odd step (and unchanged at each halving) mirrors the
fuel exhaustion `φ^k(2^k q − 1) = 3^k q − 1` of `FuelLaw` followed by the
`s`-halving refueling landing of `Refueling`. For `M = 1` the single block has
`T̃ = 1`; for `M` consecutive odd steps (one block of length `M`) followed by
`s` halvings one gets `T̃ = 3^M − 2^M`.

### 1.2 Exact obstructions

From `(2^E − 3^M)a = d·T̃`, `gcd(a,d) = 1`, `gcd(d,3) = 1`:

| obstruction | reason |
|---|---|
| `d ∣ 2^E − 3^M` | cancel `a` by coprimality (`cycle_dvd`) |
| `2^E > 3^M` | RHS positive; hence `E ≥ ⌈M log₂3⌉` |
| `T̃` odd | `e_0 = 0` ⇒ `T̃ ≡ 3^{M−1} ≡ 1 (mod 2)` |
| `3 ∤ T̃` | `T̃ ≡ 2^{e_{M−1}} ∈ {1,2} (mod 3)` (`cycT_three_free`) |
| `a` odd, `3 ∤ a` | LHS factors are odd and 3-free |
| `(2^E − 3^M) ∣ T̃` | integer case `d = 1`, with `a = T̃/(2^E−3^M)` |

The first two give a **length lower bound**: `L = E + M ≥ ⌈M log₂3⌉ + M`.

### 1.3 Verification on genuine cycles

The script extracts exponents from simulated orbits and checks the identity:

| `(a, d')` | `M` | `E` | `L` | exponents `e_j` | `T̃` | `a(2^E−3^M) = d'T̃` |
|---|---:|---:|---:|---|---:|---|
| (1, 1) | 1 | 2 | 3 | `[0]` | 1 | 1 = 1 (trivial) |
| (1, 5) | 1 | 3 | 4 | `[0]` | 1 | 5 = 5 |
| (11, 7) | 2 | 4 | 6 | `[0,3]` | 11 | 77 = 77 |
| (19, 5) | 3 | 5 | 8 | `[0,1,2]` | 19 | 95 = 95 |
| (29, 71) | 5 | 10 | 15 | `[0,1,3,4,6]` | 319 | 22649 = 22649 |

All five exact obstructions pass for every cycle.

> **Scope note.** Non-trivial rational cycles genuinely exist — `(11,7)` above
> is the 6-cycle `11 → 40 → 20 → 10 → 5 → 22 → 11`. The obstructions therefore
> **classify** cycles (and exclude whole configuration families) rather than
> globally forbid them. The exclusion statements below are for non-trivial
> *integer* cycles (`d = 1`, the Collatz conjecture itself) and for the
> Steiner 1-cycle / single-block families.

### 1.4 Steiner's 1-cycle exclusion

For `M = 1` starting at an odd numerator, `T̃ = 1` and

$$
  (2^E - 3)\,a = d.
$$

Since `2^E a = 3a + d > 3a` we get `E ≥ 2`, hence `2^E − 3 ≥ 1` and
`a = d/(2^E−3) ≤ d`. **Therefore a non-trivial cycle (`a > d`) cannot be a
1-cycle.** Exhaustive finite check (`E ≤ 63`, `d' ≤ 500`) found zero violations.
(Equality `a = d` occurs only for `E = 2, d = 1`: the trivial cycle `1 → 4 → 2 → 1`.)

### 1.5 Length lower bounds for `M ≤ 12`

Since `2^E > 3^M`, the minimal halving count `E_min` and period `L_min=E_min+M`:

| `M` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `E_min` | 2 | 4 | 5 | 7 | 8 | 10 | 12 | 13 | 15 | 16 | 18 | 20 |
| `L_min` | 3 | 6 | 8 | 11 | 13 | 16 | 19 | 21 | 24 | 26 | 29 | 32 |

The trivial cycle attains the `M=1` bound (`L=3`); every cycle with `a > d` has
`M ≥ 2` and hence `L ≥ 6` (attained by the rational 2-cycle `(11,7)`).

### 1.6 Congruence sweep and single-block check

* **Exponent-pattern sweep (`d = 1`).** For each `M ≤ 12` and
  `E ∈ [E_min, E_min+4]` (the continued-fraction candidate window around
  `M log₂3`, containing convergents `2/1`, `8/5`, `19/12`), the script
  enumerated **3,657,993** exponent patterns `0 = e_0 < … < e_{M-1} < E`,
  computed `T̃ = Σ 3^{M−1−j}2^{e_j}`, and tested whether
  `N = 2^E − 3^M` divides `T̃` with quotient `a > 1`. **Zero** non-trivial
  integer cycles found.
* **Single trailing-ones block.** For `M ≤ 12` and `s ≤ 40` (so `T̃ = 3^M−2^M`,
  `E = M+s`), no `d = 1` solution with `a > 1` exists. The same congruence for
  general `d'` *classifies* rational single-block cycles: e.g. `M=1, s=2`
  gives `2^3−3 = 5 ∤ 1` (no integer `a`), while `M=2, s=2` gives
  `2^4−9 = 7 ∤ 5`; the block obstruction is that `d'` must absorb the quotient.
* **Fingerprint identities.** On 24,301 exponent patterns: `T̃` odd and
  `T̃ ≡ 2^{e_{M−1}} (mod 3) ≠ 0` verified exactly.

---

## 2. Phase 2 — Lean 4 formalization

New file `CollatzAdicBase/CycleExclusion.lean` imports
`CollatzAdicBase.RationalDescent` and `CollatzAdicBase.FuelLaw`, and is wired
into `CollatzAdicBase.lean` and `CollatzAdicBase/Axioms.lean`.

| Declaration | Content |
|---|---|
| `step_three_free` | at a 3-free valid state, odd step is `(a,d) ↦ (3a+d, d)` |
| `denom_const_of_three_free` | denominator is constant along any 3-free orbit |
| `cycleAcc` | accumulator `t ↦ (E, M, T)` with `T ← 3T + 2^E` at odd steps |
| `cycleAcc_EM`, `cycleAcc_M_eq_oddCount` | `E + M = t`; `M = oddCount x t` |
| **`cycleAcc_spec`** | affine unrolling `2^E·(orbit x t).1 = 3^M·x.1 + d·T` |
| **`cycle_sum_identity`** | `(2^E − 3^M)·a = d·T̃` for every cycle |
| `cycle_dvd` | `d ∣ 2^E − 3^M` |
| `cycT_three_free`, `two_pow_mod_three_ne_zero` | 3-adic fingerprint `3 ∤ T̃` |
| `cycleAcc_T_eq_one` | `T̃ = 1` for a one-odd-step cycle started at an odd numerator |
| **`one_odd_step_le_denominator`** | **Steiner exclusion: `M = 1 ⇒ a ≤ d`** |
| `no_integer_cycles_M_le_six` | kernel-checked: no non-trivial integer cycle for `M ≤ 6`, `E` window 4 |
| `no_single_block_integer_cycles` | kernel-checked: no non-trivial integer single-block cycle for `M ≤ 12`, `s ≤ 40` |
| `cycT_patterns_odd_M_le_six` | kernel-checked 2-adic fingerprint |

### 2.1 Build and axiom audit

```
$ lake build
Build completed successfully (18268 jobs).
```

`#print axioms` for every new principal theorem reports only
`[propext, Classical.choice, Quot.sound]` (Lean core) for the proved theorems,
and `[propext]` for the `decide`-based finite checks. **Zero `sorryAx`, zero
custom axioms.** No `sorry`/`admit` anywhere in the new module.

### 2.2 Notes on the formalization

* The cycle equation is proved for *actual cycles* (`orbit x L = x`), not just
  for abstract exponent data: `cycleAcc_spec` is an induction over the orbit
  that tracks the affine transformation step by step, using
  `step_three_free` and the constant-denominator lemma. `cycle_sum_identity`
  then specializes to `t = L` and converts the equality into the characteristic
  `(2^E − 3^M)a = d·T̃` form.
* Steiner's exclusion is stated with an odd starting numerator: `a ≤ d` is not
  rotation-invariant (the trivial cycle started at the even value `2` has
  `a = 2 > d = 1`). Starting at the odd representative is the canonical choice.
* The kernel-checked sweeps are for `d = 1` (integer Collatz cycles). The
  Python script additionally covers `M ≤ 12` with a wider exponent enumeration
  and verifies the classification on rational cycles.

---

## 3. Scope and honest limits

* The obstructions are **exact and universal** for 3-free cycles, and they
  fully exclude Steiner 1-cycles and single-block integer cycles in the tested
  ranges.
* The `M ≤ 12` integer-cycle exclusion is verified computationally over the
  continued-fraction candidate window for `E` (and kernel-checked for `M ≤ 6`).
  A proof for *all* `E` at fixed `M` uses linear forms in logarithms
  (Simons–de Weger); that lies beyond elementary congruences and is **not**
  claimed here.
* Rational cycles with `a > d'` exist (e.g. `11/7`); the framework classifies
  them via `(2^E − 3^M)a = d' T̃` rather than forbidding them.

---

## 4. Reproduction

```bash
cd <repo>
python3 analysis/cycle_exclusion.py    # exact obstruction checks (~2 s)
lake build                             # full library + #print axioms audit
grep -n 'sorry\|admit\|axiom' CollatzAdicBase/CycleExclusion.lean   # no hits
```

Machine-readable results of the Python sweep are printed to stdout; this
summary is the durable project artifact `PAPER6_RESEARCH_SUMMARY.md`.
