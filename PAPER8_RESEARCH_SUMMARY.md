# Paper 8 — Research Summary: Finite-State 2-adic Survivor Branching and Exponential Density Decay

**Goal.** Formalize the finite-state 2-adic survivor branching operator that drives stopping-time density decay, on top of the verified `CollatzAdicBase` library at `v1.1.0`. Two phases, strictly separated:

- **Phase 1 (probabilistic/combinatorial):** exact parity-vector expansion at $2^K$, Hoeffding/Chernoff large deviations for the drift sum, and a Python verification of the exact survivor fraction against the constructive bounds for $K=1,\dots,16$.
- **Phase 2 (Lean 4):** a kernel-checked module `CollatzAdicBase/GlideMarkovChain.lean` with the exact trajectory product identity, the parity-vector/Terras branching law, and the binomial tail bound giving exponential decay; wired into the library and audited with `#print axioms`.

---

## 1. Phase 1 — model and large deviations

### 1.1 The accelerated half-step and the exact product identity

Work at one halving per step:

$$S(n)=\begin{cases}n/2,& n\ \text{even},\\[2pt](3n+1)/2,& n\ \text{odd}.\end{cases}$$

Let $w_K(n)=\#\{i<K : S^i(n)\ \text{odd}\}$. Unrolling the two update rules gives the exact affine identity

$$2^K S^K(n)=3^{w_K(n)}\,n+c_K(n),\qquad 0\le c_K(n)<3^K. \tag{1}$$

In fact the sharp bound $c_K\le 3^K-2^K$ holds (proved by induction with the recurrence $c_{t+1}=3c_t+2^t$ on odd steps, $c_{t+1}=c_t$ on even steps).

Consequences:

- log-multiplier per step: odd step $\log_2(3/2)$, pure halving $\log_2(1/2)=-1$;
- mean drift $\mathbb E[\Delta\log_2]=\tfrac12\log_2(3/4)\approx-0.2075187<0$;
- **drop criterion:** $3^{w_K(n)}<2^K$ and $n\ge 3^K$ imply $S^K(n)<n$.

### 1.2 The finite-state branching operator

The parity vector $b(r)=(S^i(r)\bmod 2)_{i<K}$ is a bijection from residues mod $2^K$ to $\{0,1\}^K$ (Terras). Lifting a class $r\bmod 2^K$ to its two children

$$r\quad\text{and}\quad r+2^K \pmod{2^{K+1}}$$

preserves the first $K$ bits and appends one bit: $0$ for one child (pure halving), $1$ for the other ($3n+1$ then halve). Equivalently, on odd residues $w_K=1+\mathrm{Bin}(K-1,\tfrac12)$, and the drift sum is an i.i.d. Bernoulli$(\tfrac12)$ sum with mean $\tfrac12\log_2(3/4)<0$.

The exact child relation (formalized below) is

$$S^{j}(r+2^{j})=S^{j}(r)+3^{w_j(r)},$$

and $3^{w}$ is odd, so the two children always have opposite next parity bits — one odd step, one halving.

### 1.3 Survivors and the constructive bounds

The $K$-step multiplier is $3^{w}/2^K$; its exceeding $1$ is equivalent to $w>K\log_3 2$ with $\theta=\log_3 2=\log 2/\log 3\approx0.6309297536$. Define the survivor density over odd residues

$$\delta(K)=\frac{\#\{r<2^K:\ r\ \text{odd},\ 3^{w_K(r)}>2^K\}}{2^{K-1}}.$$

Let $m(K)=\min\{w:3^w>2^K\}=\lceil K\theta\rceil$ (since $K\theta$ is irrational). Three explicit constructive bounds are verified:

| bound | statement | rate |
|---|---|---|
| Hoeffding | $\delta(K)\le 2\exp\!\bigl(-2(m(K)-K/2)^2/K\bigr)$ | $c_H=2(\theta-\tfrac12)^2\approx0.034285$ |
| Chernoff/KL | $\delta(K)\le 2\exp\!\bigl(-K\,D(m(K)/K\|\tfrac12)\bigr)$ | $c_C=D(\theta\|\tfrac12)\approx0.034688$ nats $=0.050044$ bits |
| integer tilt | $\#\{\text{odd survivors}\}\le 2\cdot3^{K-1}/2^{m(K)}$ | certified rational $c=1/30\approx0.03333$ |

Here $D(q\|\tfrac12)=q\ln(2q)+(1-q)\ln(2(1-q))$. The prefactor $2$ is necessary at $K=1$ ($\delta(1)=1$); equivalently $\delta(K)\le e^{-K/31}$ for $K\ge48$. All three give $\delta(K)\to0$ exponentially — Terras's density theorem in constructive form. The tilt proof is a pure integer identity: $\sum_{b\in\{0,1\}^K}2^{\mathrm{wt}(b)}=3^K$, and each heavy string contributes at least $2^m$.

### 1.4 Exact empirical table, $K=1,\dots,16$

Produced by `analysis/glide_markov_chain.py` (pure standard library, exact integer counts), machine-readable at `artifacts/glide_markov_chain.json`. The branching operator was independently checked on $65{,}534$ residue lifts for $K=1,\dots,15$ (bijective at every $K$).

| $K$ | $m(K)$ | survivors / odd classes | $\delta(K)$ | Chernoff | Hoeffding | tilt |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 1/1 | 1.000000 | 0.500000 | 0.606531 | 1.000000 |
| 2 | 2 | 1/2 | 0.500000 | 0.250000 | 0.367879 | 0.750000 |
| 3 | 2 | 3/4 | 0.750000 | 0.843750 | 0.846482 | 1.125000 |
| 4 | 3 | 4/8 | 0.500000 | 0.592593 | 0.606531 | 0.843750 |
| 5 | 4 | 5/16 | 0.312500 | 0.381470 | 0.406570 | 0.632812 |
| 6 | 4 | 16/32 | 0.500000 | 0.711914 | 0.716531 | 0.949219 |
| 7 | 5 | 22/64 | 0.343750 | 0.514714 | 0.525788 | 0.711914 |
| 8 | 6 | 29/128 | 0.226562 | 0.351166 | 0.367879 | 0.533936 |
| 9 | 6 | 93/256 | 0.363281 | 0.600677 | 0.606531 | 0.800903 |
| 10 | 7 | 130/512 | 0.253906 | 0.439188 | 0.449329 | 0.600677 |
| 11 | 7 | 386/1024 | 0.376953 | 0.660790 | 0.664254 | 0.901016 |
| 12 | 8 | 562/2048 | 0.274414 | 0.506822 | 0.513417 | 0.675762 |
| 13 | 9 | 794/4096 | 0.193848 | 0.372779 | 0.382304 | 0.506822 |
| 14 | 9 | 2380/8192 | 0.290527 | 0.560196 | 0.564718 | 0.760232 |
| 15 | 10 | 3473/16384 | 0.211975 | 0.427631 | 0.434598 | 0.570174 |
| 16 | 11 | 4944/32768 | 0.150879 | 0.315697 | 0.324652 | 0.427631 |

Every exact count respects every bound (with the prefactor 2 for the exponential bounds, and the tilt bound as stated). $\delta(K)$ oscillates between jumps of $m(K)$, but the envelope decays; at $K=16$ the exact density is $4944/32768\approx0.1509$ versus Chernoff $0.3157$. Note the accelerated-map survivors here are a different sieve than the paper-7 affine-template sieve, whose $\delta(8)=19/128$; both decay but neither reaches zero at finite modulus (all-ones class survives).

---

## 2. Phase 2 — Lean 4 formalization

New file `CollatzAdicBase/GlideMarkovChain.lean`, importing `CollatzAdicBase.StoppingTimeDensity`. Wired into `CollatzAdicBase.lean` and `CollatzAdicBase/Axioms.lean`. All theorems are proved; no `sorry`, `admit`, or custom axioms.

| Lean declaration | content |
|---|---|
| `glideStep`, `glideVal`, `glideW`, `glideC` | accelerated trajectory and the two recurrence counters |
| **`glide_identity`** | exact product law $2^K S^K(n)=3^{w_K(n)}n+c_K(n)$ |
| `glideC_bound`, `glideC_lt` | sharp constant bound $c_K+2^K\le3^K$, hence $c_K<3^K$ |
| **`glide_drop`** | $3^{w_K(n)}<2^K,\ n\ge3^K\Rightarrow S^K(n)<n$ |
| `sameParity_coeffs`, `parity_agree_of_dvd` | congruence mod $2^K$ forces agreement of the first $K$ parities |
| `parityMap`, **`parityMap_injective_mod`** | Terras injectivity: $K$-bit parity vector determines $r\bmod 2^K$ |
| **`glideVal_child`**, `glideW_child_even/odd` | $S^j(r+2^j)=S^j(r)+3^{w_j}$; children get weights $w_j,w_j+1$ |
| `ones`, `parityList`, `allBitsF`, `heavyF`, `heavyF_card` | bitstring enumeration and the exact binomial tail count |
| **`heavyCount_tilt`** | $\texttt{heavyCount}\,K\,m\cdot2^m\le3^K$ (combinatorial Chernoff) |
| **`heavyCount_exp`** | at $K=8t$: $\texttt{heavyCount}(8t,5t+1)\cdot2\cdot32^t\le6561^t$ |
| `survF_card_le_heavy` | residue survivors inject into heavy bitstrings (injectivity + cardinality) |
| **`odd_survivor_decay`**, **`true_survivor_decay`** | exponential decay of the odd-residue survivor density |

The main theorem `true_survivor_decay` states

$$(\#\text{odd survivors at }K=8t)\cdot2\cdot32^t\le6561^t,$$

so, dividing by the $2^{8t-1}$ odd classes,

$$\delta(8t)\le\frac{6561^t}{2\cdot32^t\cdot2^{8t-1}}=\Bigl(\frac{6561}{8192}\Bigr)^{t}=e^{-0.02775\ldots K}.$$

This is a fully constructive, kernel-checked exponential decay law. The Lean constant is deliberately weaker than the analytic KL rate $0.034688$: it uses only the rational inequality $3^5=243<256=2^8$ and integer power arithmetic, chosen so the proof is a small, auditable induction with no real analysis.

**Axiom audit.** `lake -K jobs=1 build` completed successfully (18,272 jobs). `#print axioms` on every principal theorem of the new module reports only Lean's core axioms:

```
[propext, Quot.sound]                       (glide_identity, glideC_bound, ...)
[propext, Classical.choice, Quot.sound]     (glide_drop, heavyCount_tilt, ...)
```

Zero `sorryAx`, zero project-specific axioms. The complete audit is also emitted from `CollatzAdicBase/Axioms.lean` lines 72–81.

---

## 3. Interpretation and boundaries

1. **The trajectory law is exact.** Equation (1) is an identity in `Nat`; the decay theorem is a count of parity vectors satisfying an exact integer inequality ($2^K<3^{w}$), not an asymptotic heuristic.
2. **The branching law is a theorem, not an assumption.** The child relation and Terras injectivity are proved from the product identity plus coprimality of $3^w$ and $2^K$; in particular $3^{w}$ odd forces opposite child parity bits.
3. **The formalization proves exponential decay, not termination.** The result is Terras's density statement in finite-state form: the *fraction* of surviving odd classes vanishes exponentially. It does not assert that any particular $n$ stops, and it does not close the global Collatz problem; the project's rational descent and cycle-exclusion modules remain the complementary ingredients.
4. **Two different sieves.** Paper 7's affine-template sieve ($\delta(8)=19/128$) certifies stopping by $a<2^e$; Paper 8's operator sieve counts weight $w>K\log_3 2$ in the accelerated dynamics. Their densities differ, but both exhibit exponential envelope decay and neither can certify 100% at finite modulus (the all-ones class always survives).

---

## 4. Reproduction

```bash
cd <repo>
python3 analysis/glide_markov_chain.py     # exact delta(K), K=1..16, vs Chernoff/Hoeffding/tilt
lake -K jobs=1 build                        # full library, #print axioms audit
grep -nE '\bsorry\b|\badmit\b' CollatzAdicBase/GlideMarkovChain.lean  # no code hits
```

Machine-readable results: `artifacts/glide_markov_chain.json` (project artifacts directory).
