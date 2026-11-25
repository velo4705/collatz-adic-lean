# collatz-adic-lean

Kernel-checked Lean 4 formalizations surrounding the "Trailing Ones and
High-Altitude Backbones" papers.  Nine verified modules are exported together
from the single root `CollatzAdicBase` and audited with `#print axioms` during
every build.  The library proves 186 theorems/lemmas in total (183 in the nine
audited modules, 3 in `Basic.lean`) with zero `sorry` and zero project-specific
axioms.

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
- `CollatzAdicBase/CycleExclusion.lean` — algebraic and modular cycle
  exclusion, cycle-sum identity and kernel-checked small-cycle checks (Paper 6).
- `CollatzAdicBase/StoppingTimeDensity.lean` — two-block drift identity and
  stopping-time residue-class certificates (Paper 7).
- `CollatzAdicBase/GlideMarkovChain.lean` — accelerated parity-vector branching,
  exact trajectory product bound, Terras injectivity and exponential survivor
  density decay (Paper 8).  30 theorems/lemmas, including the main density bound.
- `CollatzAdicBase/SyracuseLogDrift.lean` — accelerated odd-to-odd Syracuse step,
  exact $M$-step identity, geometric valuation law and cycle-minimum bound from
  continued-fraction gaps (Paper 9).  19 theorems/lemmas.
- `CollatzAdicBase/Axioms.lean` — `#print axioms` audit over all nine modules,
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

### Glide Markov chain (Paper 8, v1.2.0)

For the accelerated half-step $S(n)=n/2$ (even) or $(3n+1)/2$ (odd), with
$w_K(n)$ counting odd steps:

- `glide_identity`: $2^K S^K(n)=3^{w_K(n)}n+c_K(n)$ with $0\le c_K<3^K$;
  `glide_drop`: $3^{w_K(n)}<2^K$ and $n\ge3^K$ imply $S^K(n)<n$.
- `parityMap_injective_mod` and `glideVal_child`: the $K$-bit parity vector
  determines $r\bmod 2^K$, and the two children $r,r+2^K$ satisfy
  $S^K(r+2^K)=S^K(r)+3^{w_K(r)}$ (one odd step, one halving).
- `heavyCount_tilt`: $\#\{b\in\{0,1\}^K: \mathrm{wt}(b)\ge m\}\cdot 2^m\le3^K$;
  `survF_card_le_heavy` transfers this to residue classes by injectivity.
- `true_survivor_decay`: at $K=8t$, the number of odd survivors satisfies
  $\#\text{survivors}\cdot2\cdot32^t\le6561^t$, i.e.
  $\delta(8t)\le(6561/8192)^t=e^{-0.02775\ldots K}$ — a kernel-checked Terras
  density theorem in constructive form.  The exact $K=1,\dots,16$ comparison
  against Chernoff/Hoeffding bounds is in `analysis/glide_markov_chain.py` and
  `artifacts/glide_markov_chain.json`.

### Syracuse log drift (Paper 9, v1.2.0)

For odd $n$, $T_{\mathrm{Syr}}(n)=(3n+1)/2^{v_2(3n+1)}$:

- `syracuseStep` and `syracuse_identity`: the exact $M$-step law
  $n_M 2^{A_M}=3^M n_0+\sum_{j<M}3^{M-1-j}2^{A_j}$, $A_j=\sum_{i<j}a_i$.
- `exactValF_card`: exactly $2^{K-a-1}$ odd residues mod $2^K$ have
  $v_2(3n+1)=a$ for $1\le a<K$, giving the geometric law $\mathbb P(a=j)=2^{-j}$
  and $\mathbb E[a]=2$, hence $\mathbb E[\log(n_M/n_0)]=M\log(3/4)+O(1/n_0)$.
- `cycle_min_upper_bound`: $n_{\min}(2^E-3^M)\le\widetilde T_{\max}(M,E)
  =2^{E-M}(3^M-2^M)$, linking the Diophantine gap to the cycle size.
- Convergents of $\log_2 3$ with $q\le10^6$ give
  $2^E-3^M>3^M\ln 2/10\,781\,874$; with the verified search bound $2^{40}$ the
  least fraction in $(\log_2 3,\log_2(3+2^{-40}))$ is $17\,087\,915/10\,781\,274$
  ($L=E+M\ge27\,869\,189$).  Script: `analysis/syracuse_log_drift.py`;
  data: `artifacts/syracuse_log_drift.json`.  Full write-up:
  [PAPER9_RESEARCH_SUMMARY.md](PAPER9_RESEARCH_SUMMARY.md).

## Corrigendum

The requested Lemma 3 statement "`iterate collatz 6 3 = 1`" is an off-by-one
error under the stated definition of `collatz`: the kernel-checked orbit is

`3 → 10 → 5 → 16 → 8 → 4 → 2 → 1 → 4`,

so `iterate collatz 6 3 = 2`, `iterate collatz 7 3 = 1`, and
`iterate collatz 8 3 = 4`. The formalized Lemma 3 uses the correct step 7
(and also records `iterate collatz 6 3 = 2 < 3`).
