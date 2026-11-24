# collatz-adic-lean

Kernel-checked Lean 4 formalizations surrounding the "Trailing Ones and
High-Altitude Backbones" papers.  Five verified modules are exported together
from the single root `CollatzAdicBase` and audited with `#print axioms` during
every build.

See [CORRIGENDUM.md](CORRIGENDUM.md) for the step-index correction in Lemma 3
($n_0 = 3$: the value 1 is reached at step 7, not step 6). A revised version of
Paper 2 is intentionally **not** being uploaded to Zenodo until Paper 3 is
finished, so that the verified Lean repository can be cross-linked directly.

Build with `lake build`. Everything is pinned to Lean/Mathlib v4.36.0;
`Basic.lean` reuses Mathlib's `Nat.iterate` definition (identical to the one
originally defined locally), and `RationalDescent.lean` uses Mathlib's
arithmetic and tactics.  No project-specific axioms and no `sorry` appear
anywhere: the full axiom audit is recorded in
[AXIOM_AUDIT.txt](AXIOM_AUDIT.txt).

## Files

- `CollatzAdicBase/Basic.lean` — `collatz`, `shortcut`, `Nat.iterate`, glide predicates.
- `CollatzAdicBase/FuelLaw.lean` — Proposition 4 (initial 2-adic fuel law).
- `CollatzAdicBase/RationalDescent.lean` — rational 3-adic descent, Lemmas 2.1–2.4,
  Theorem 1, and the small-$k$ kernel-checked computation (Paper 1).
- `CollatzAdicBase/Refueling.lean` — the mid-flight refueling congruence
  (Paper 2, Section 6): $r \le v_2(u+1) \leftrightarrow 2^{s+r} \mid 3^k q + 2^s - 1$.
- `CollatzAdicBase/AlternatingGlide.lean` — Theorem 1 and Lemma 3 (Paper 2).
- `CollatzAdicBase/LatentSaturation.lean` — denominator lifting and cycle
  saturation lemmas (Paper 4).
- `CollatzAdicBase/Axioms.lean` — `#print axioms` audit over all five modules,
  run during `lake build`.

## Results

### Fuel law (Paper 2, Proposition 4)

For `k ≥ 1, q ≥ 1` and `n = 2^k q - 1`:

- `iterate shortcut j n = 3^j 2^(k-j) q - 1` for all `j ≤ k`;
- each `j < k` value is odd and strictly smaller than the next one;
- `iterate collatz t n > n` for `1 ≤ t ≤ 2k`, and
  `iterate collatz (2k) n = 3^k q - 1`; hence
  `GlideAtLeast (2^k q - 1) (2k)` (`G(n) ≥ 2k+1`).

### Rational descent (Paper 1)

For a reduced rational state `(a, d)` with `d` odd and `Coprime a d`:

- `gcd (3a + d) d ∣ 3`: only the prime 3 can change in the denominator;
- all primes `p ≠ 3` have stable $p$-adic valuation (Lemma 2.1);
- each odd step at a denominator divisible by 3 removes exactly one factor of 3
  (Lemma 2.2), and cycles are 3-free (Lemma 2.4);
- `theorem_1_pure_three_power_descent`: for `0 < a` coprime to `3^k`, the orbit
  from `(a, 3^k)` reaches `(m, 1)` using at most `k` odd steps;
- `verification_all_reduced_small_k`: all reduced numerators for `1 ≤ k ≤ 6`
  reach `(1, 1)` within 100 reduced steps (kernel-checked `decide`).

### Refueling (Paper 2, Section 6)

Writing the exhausted block as `3^k q - 1 = 2^s u` with `u` odd:

- `refuel_landing`: after `2k + s` Collatz steps the orbit reaches `u`;
- `refuel_exhausts_fuel`: `v₂(3^k q - 1) = s`;
- `refuel_congruence`: `r ≤ v₂(u+1) ↔ 2^(s+r) ∣ 3^k q + 2^s - 1`;
- `refuel_mod_invariant`: the criterion depends only on `q mod 2^(s+r)`;
- concrete witnesses include `n = 6,631,675` and the `τ = 18` backbone.

### Alternating glide (Paper 2)

For `n_alt k = (2^(2k+3)+1)/3`, `k ≥ 1`:

- `3 ∣ 2^(2k+3)+1` for every `k`;
- `iterate collatz 2 (n_alt k) = 2^(2k+2)+1`;
- `iterate collatz 5 (n_alt k) = 3·2^(2k)+1`;
- `iterate collatz 8 (n_alt k) = 9·2^(2k-2)+1`;
- `iterate collatz t (n_alt k) > n_alt k` for `1 ≤ t ≤ 7`, and
  `iterate collatz 8 (n_alt k) < n_alt k`, formalized as
  `GlideEq (n_alt k) 8` (`G(n_alt k) = 8`).

### Latent saturation (Paper 4)

- `gcd_lift`: at level `k ≥ 1`, `gcd (3a + 3^k d') (3^k d') = 3`;
- `ratStep_lift`: the odd step strips exactly one factor of 3;
- `lift_congruence` and `cycle_dvd_pow_sub`: $2^E A \equiv a \pmod{d'}$ and
  $d \mid 2^E - 3^M$;
- `three_free_preserved` and `ratStep_valid`: validity and 3-freeness are
  preserved, so every cycle lives at a 3-free home denominator.

## Corrigendum

The requested Lemma 3 statement "`iterate collatz 6 3 = 1`" is an off-by-one
error under the stated definition of `collatz`: the kernel-checked orbit is

`3 → 10 → 5 → 16 → 8 → 4 → 2 → 1 → 4`,

so `iterate collatz 6 3 = 2`, `iterate collatz 7 3 = 1`, and
`iterate collatz 8 3 = 4`. The formalized Lemma 3 uses the correct step 7
(and also records `iterate collatz 6 3 = 2 < 3`).
