# Paper 10 — Research Summary: Syracuse Renewal, Exact Valuation MGF, and Exponential Concentration of Multi-Step Products

**Goal.** Attack Layer 5 of the `CollatzAdicBase` project on top of the verified library at `v1.3.0` (`SyracuseLogDrift.lean`, `GlideMarkovChain.lean`, `StoppingTimeDensity.lean`). Two strictly separated phases:

- **Phase 1 (renewal & excursion tail):** derive the exact moment generating function $\mathbb{E}[2^{-\lambda a}]=1/(2^{\lambda+1}-1)$ of the geometric valuation law `exactValF_card`; compute the exact Cramér/Chernoff rate of the left deviation $A_M\le M\log_2 3$; verify the decay and empirical survival fractions for $M=1,\dots,20$ in `analysis/syracuse_renewal.py`.
- **Phase 2 (Lean 4):** a kernel-checked module `CollatzAdicBase/SyracuseRenewal.lean` importing `CollatzAdicBase.SyracuseLogDrift`, formalizing the accelerated-valuation/half-step renewal identity, the exact binomial/composition count, the geometric MGF over $\mathbb{Q}$, and the exponential decay theorem for the fraction of odd classes failing to contract; wired into the library and audited with `#print axioms`.

---

## 1. Phase 1 — renewal, MGF, and Cramér rate

### 1.1 Exact geometric valuation law and MGF

For odd $n$ set $a(n)=v_2(3n+1)\ge1$ and $T_{\mathrm{Syr}}(n)=(3n+1)/2^{a(n)}$. The verified finite law (`exactValF_card`) says that for $1\le a<K$ exactly $2^{K-a-1}$ odd residues mod $2^K$ have valuation $a$, and one exceptional class has valuation $\ge K$. Hence, as $K\to\infty$, the accelerated valuations are i.i.d. geometric:

$$
\mathbb{P}(a=j)=2^{-j}\ (j\ge1),\qquad \mathbb{E}[a]=2,\qquad \operatorname{Var}[a]=2.
$$

Writing $x=2^{-\lambda}\in(0,2)$ (equivalently $\lambda>-1$, $u=2^\lambda=1/x$), the exact MGF is

$$
\mathbb{E}[x^a]=\sum_{j\ge1}2^{-j}x^j=\frac{x}{2-x}=\frac{1}{2^{\lambda+1}-1}=\frac{1}{2u-1}.
$$

The script checks this as an **exact identity of `Fraction`s** for $u\in\{2,3,4,5,3/2,4/3,21/20\}$ (finite partial sums vs. closed form vs. finite-law expectation at $K=12$ with an explicit tail bound); all checks pass.

### 1.2 Cramér/Chernoff rate for the non-contraction event

$A_M=\sum_{j<M}a_j$ has mean $2M$. The non-contraction event is

$$
3^M\ge 2^{A_M}\iff A_M\le M\log_2 3,\qquad \log_2 3=1.58496\ldots<2,
$$

a **left** large deviation. For $0<x<1$, Markov's inequality on $x^{A_M}$ gives

$$
\mathbb{P}(3^M\ge2^{A_M})\le\left(x^{-c}\,\frac{x}{2-x}\right)^M
=\left(\frac{t^{\,c}}{2t-1}\right)^{M},\quad c=\log_2 3,\quad t=1/x=2^\lambda>1.
$$

The Cramér optimum solves the tilted-mean equation $c=u/(u-1)$ with $u=2^{\lambda+1}$, giving

$$
t^*=\frac{c}{2(c-1)}=1.3547556\ldots,\quad
\lambda^*=\log_2 t^*=0.4380327\ldots,\quad
\rho^*=\frac{(t^*)^c}{2t^*-1}=0.9465046\ldots,
$$

$$
I^*=-\ln\rho^*=0.0549795\ \text{nats per accelerated step}.
$$

A golden-section numeric minimization independently recovers $t^*$ to $10^{-7}$.

**Fully rational certificate.** Since $3^5=243<256=2^8$, we have $\log_2 3\le 8/5$; optimizing the same bound at $r=8/5$ gives $t^*=4/3$ and $\rho^*_{8/5}=0.9507213\ldots$. Choosing the rational tilt $t=(21/20)^5$ makes $t^{8/5}=(21/20)^8$ rational and yields the **certified rational base**

$$
\rho=\frac{(21/20)^8}{2(21/20)^5-1}=\frac{37\,822\,859\,361}{39\,745\,616\,000}=0.9516234\ldots<1,
$$

with $\rho^*\le\rho$. Thus $\mathbb{P}(3^M\ge2^{A_M})\le\rho^M$ for every $M$.

### 1.3 Exact survival fractions for $M=1,\dots,20$

Using $\mathbb{P}(A_M=E)=\binom{E-1}{M-1}2^{-E}$ (composition count) and an independent convolution DP, the script computes the survival probabilities exactly:

| $M$ | $\mathbb{P}(3^M\ge2^{A_M})$ | $\rho^M$ | $M$ | $\mathbb{P}(3^M\ge2^{A_M})$ | $\rho^M$ |
|---:|---:|---:|---:|---:|---:|
| 1 | $1/2=0.500000$ | 0.951623 | 11 | 0.166153 | 0.579584 |
| 2 | $1/2=0.500000$ | 0.905587 | 12 | 0.179642 | 0.551546 |
| 3 | $5/16=0.312500$ | 0.861778 | 13 | 0.131588 | 0.524864 |
| 4 | $11/32=0.343750$ | 0.820088 | 14 | 0.143139 | 0.499473 |
| 5 | $29/128=0.226563$ | 0.780415 | 15 | 0.105020 | 0.475310 |
| 6 | $65/256=0.253906$ | 0.742661 | 16 | 0.114761 | 0.452316 |
| 7 | 0.274414 | 0.706734 | 17 | 0.084319 | 0.430435 |
| 8 | 0.193848 | 0.672544 | 18 | 0.092467 | 0.409612 |
| 9 | 0.211975 | 0.640009 | 19 | 0.100244 | 0.389796 |
| 10 | 0.150879 | 0.609048 | 20 | 0.074806 | 0.370939 |

Every exact fraction satisfies $\mathbb{P}\le\rho^M$, $\mathbb{P}\le\rho_{8/5}^M$, and $\mathbb{P}\le(\rho^*)^M$, and the DP agrees with the composition formula exactly.

### 1.4 Independent Terras certificate

Because the accelerated valuation sum $A_M$ is the half-step index of the $(M+1)$-st odd value, a failure at $M=5t$ forces parity weight $w_{8t}\ge5t+1$ (as $3^{5t}<2^{8t}$). The verified `GlideMarkovChain.odd_survivor_decay` then gives the failing fraction $\le(6561/8192)^t$, and $6561\cdot25^5<24^5\cdot2^{13}$ gives $(6561/8192)^t\le(24/25)^{5t}$. The script checks this for $t=1,\dots,4$ ($M=5,10,15,20$). Machine-readable output: `artifacts/syracuse_renewal.json`.

---

## 2. Phase 2 — Lean 4 formalization

New file `CollatzAdicBase/SyracuseRenewal.lean`, importing `CollatzAdicBase.SyracuseLogDrift`. Wired into `CollatzAdicBase.lean` and `CollatzAdicBase/Axioms.lean`. 28 declarations, all proved; no `sorry`, `admit`, or custom axioms.

| Lean declaration | content |
|---|---|
| `glideVal_eq_div_pow_of_v2` | for odd $m$ with $v_2(3m+1)=a$, half-step values are $(3m+1)/2^j$ for $j\le a$ |
| `glideVal_v2_eq_step`, `glideW_v2_eq_one`, `glideW_le_v2` | after $a$ half-steps the value is $T_{\mathrm{Syr}}(m)$ and only the initial value is odd |
| `glideVal_add_v2`, `glideW_add_v2` | the accelerated step shifts the half-step orbit/weight by $a$ and $+1$ |
| **`glide_at_acc_times`** | renewal identity: $V_{A_j}(n)=n_j$ and $W_{A_j}(n)=j$ along any `ValSeq` |
| `glideW_mono`, `glideW_sum_succ` | monotonicity in time and the final odd bit |
| `syracuseFailF`, `mem_syracuseFailF` | odd residue classes mod $2^K$ whose first $M$ valuations fail to contract ($2^{A_M}\le3^M$) |
| `three_pow_five_mul_lt`, `failing_sum_lt` | $3^{5t}<2^{8t}$, hence failure forces $A_M<8t$ |
| **`syracuseFail_subset_survivor`** | failing classes inject into `oddSurvF(8t,5t+1)` (Terras survivors) |
| **`syracuseFail_decay`** | $\#\text{fail}\cdot(2\cdot32^t)\le6561^t$ |
| `rational_rate_certificate`, **`syracuseFail_rational_decay`** | $2\cdot\#\text{fail}\cdot25^{5t}\le24^{5t}\cdot2^{8t}$, i.e. failing fraction $\le(24/25)^{5t}$ |
| `compCount`, `compCount_zero_right`, `compCount_succ_succ`, `compCount_eq_zero_of_lt`, `compCount_self`, `compCount_one`, **`compCount_eq_choose`** | exact binomial/composition identity $\#\{\mathbf a\in\mathbb{N}_{\ge1}^M:\sum a_j=E\}=\binom{E-1}{M-1}$ |
| `mgfPartial`, **`mgfPartial_closed`**, **`mgf_lambda_closed`**, `mgf_certified_value` | exact geometric MGF $\sum_{a=1}^K2^{-a}x^a=\frac{x}{2-x}(1-(x/2)^K)$ and its $\lambda$-form $\frac{1}{2u-1}$ with exact remainder |

The structural chain is:

$$
\text{ValSeq}(n,\mathbf a)\ \Longrightarrow\ \bigl[\,W_{A_M}(n)=M,\ W_{A_M+1}(n)=M+1\,\bigr]
\ \Longrightarrow\ \text{failing}\subseteq\text{Terras survivor}
\ \Longrightarrow\ \#\text{fail}\cdot(2\cdot32^t)\le6561^t .
$$

The finite K-model is the odd residue classes mod $2^{8t}$ with $K>A_M$ guaranteed by $A_M<8t$; the last implication is the already-verified Paper 8 survivor bound. The exact composition count `compCount_eq_choose` is the arithmetic identity underlying the Python survival computation $\mathbb{P}(A_M=E)=\binom{E-1}{M-1}2^{-E}$; the exact MGF identities underpin the Cramér rate of Phase 1. (The Python script additionally enumerates the exact valuation-tuple distribution and its survival fractions; in Lean the distribution's non-contraction tail is captured directly by `syracuseFailF`.)

**Axiom audit.** `lake -K jobs=1 build` was run **synchronously in the foreground** and completed successfully: **18,276 jobs, zero errors, zero warnings**. `#print axioms` on every principal theorem in the new module reports only Lean's core axioms:

```
'CollatzAdicBase.SyracuseRenewal.glideVal_eq_div_pow_of_v2'     [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseRenewal.glideW_v2_eq_one'              [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseRenewal.glide_at_acc_times'            [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseRenewal.glideW_sum_succ'               [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseRenewal.syracuseFail_subset_survivor'  [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseRenewal.syracuseFail_decay'            [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseRenewal.syracuseFail_rational_decay'   [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseRenewal.compCount_eq_choose'           [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseRenewal.mgfPartial_closed'             [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseRenewal.mgf_lambda_closed'             [propext, Classical.choice, Quot.sound]
```

Zero `sorryAx`, zero project-specific axioms. The complete audit is emitted from `CollatzAdicBase/Axioms.lean` (Paper 10 section, ten verified modules).

---

## 3. Interpretation and boundaries

1. **The renewal identity is exact.** `glide_at_acc_times` is a theorem about the half-step and accelerated orbits, not a probabilistic assumption; it converts accelerated valuation sums into parity weights, which are controlled by the already-verified Terras branching bound.
2. **The decay is finite-state and constructive.** `syracuseFail_decay` holds for odd residues mod $2^{8t}$ with the explicit integer bound $\#\text{fail}\le 6561^t/(2\cdot32^t)$; the rational corollary gives the certified base $24/25$ per accelerated step at $M=5t$. This is weaker than the sharp Cramér constant $\rho^*=0.94650\ldots$ derived in Phase 1, but it is fully formalized with rational arithmetic.
3. **The sharp rate is analytic.** The MGF $1/(2^{\lambda+1}-1)$ and rate $I^*=0.05498$ are exact/real-analytic and are verified numerically and with exact rationals in Phase 1; their Lean counterparts are the algebraic closed forms `mgfPartial_closed`/`mgf_lambda_closed`.
4. **No Collatz claim.** These are large-deviation/excursion-tail statements for the valuation process; they do not resolve the conjecture.

---

## 4. Reproduction

```bash
cd <repo>
python3 analysis/syracuse_renewal.py     # MGF, Cramer rate, survival M=1..20, Terras certificate
lake -K jobs=1 build                     # full library, #print axioms audit
grep -nE '\bsorry\b|\badmit\b' CollatzAdicBase/SyracuseRenewal.lean  # no code hits
```

Machine-readable Phase 1 results: `artifacts/syracuse_renewal.json` (project artifacts directory).
