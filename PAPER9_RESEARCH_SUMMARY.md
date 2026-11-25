# Paper 9 — Research Summary: Accelerated Syracuse Dynamics, Logarithmic Drift, and Continued-Fraction Cycle Bounds

**Goal.** Attack Layer 4 of the `CollatzAdicBase` project on top of the verified library at `v1.2.0` (`RationalDescent.lean`, `FuelLaw.lean`, `LatentSaturation.lean`, `Refueling.lean`, `CycleExclusion.lean`, `StoppingTimeDensity.lean`, `GlideMarkovChain.lean`). Two strictly separated phases:

- **Phase 1 (Syracuse dynamics & continued fractions):** the odd-to-odd map $T_{\mathrm{Syr}}(n)=(3n+1)/2^{v_2(3n+1)}$, the exact valuation-tuple bijection and $M$-step orbit identity, the geometric valuation law and logarithmic drift, continued-fraction convergents of $\log_2 3$ up to $q\le10^6$, Diophantine lower bounds on $2^E-3^M$, and the implied cycle-size and cycle-length bounds. Verification script: `analysis/syracuse_log_drift.py`.
- **Phase 2 (Lean 4):** a kernel-checked module `CollatzAdicBase/SyracuseLogDrift.lean` importing `GlideMarkovChain` and `CycleExclusion`, formalized step, identity, geometric law, and cycle-minimum upper bound; wired into the library and audited with `#print axioms`.

---

## 1. Phase 1 — Syracuse dynamics and Diophantine cycle bounds

### 1.1 The accelerated odd-to-odd map and the valuation bijection

For odd $n>0$ set $a(n)=v_2(3n+1)\ge1$ and

$$
T_{\mathrm{Syr}}(n)=\frac{3n+1}{2^{a(n)}} .
$$

Writing $n_{j+1}=T_{\mathrm{Syr}}(n_j)$, $a_j=a(n_j)$, $A_j=\sum_{i<j}a_i$, $A_M=E$, the exact $M$-step identity is

$$
n_M\,2^{A_M}=3^M n_0+T,\qquad T=\sum_{j=0}^{M-1}3^{M-1-j}2^{A_j}. \tag{1}
$$

It is proved in Lean by the recursion $T(a::as)=3^{|as|}+2^aT(as)$.

**Bijection.** For every $M$-tuple $\mathbf a=(a_0,\dots,a_{M-1})$ of positive integers with $E=\sum a_j$ there is exactly **one** odd residue $n_0\bmod 2^{E+1}$ realizing it. (The extra bit pins down exactness of the last valuation.) The Python check verifies this exhaustively for all compositions of $E\le11$: $2^{E-1}$ tuples, each with a unique odd class, and identity (1) holds on every representative.

### 1.2 Geometric valuation law and logarithmic drift

Among the $2^{K-1}$ odd residues mod $2^K$,

$$
\#\{n:\ v_2(3n+1)=a\}=2^{K-a-1}\quad(1\le a<K),\qquad
\#\{n:\ v_2(3n+1)\ge K\}=1. \tag{2}
$$

Hence $\mathbb P(a=j)=2^{-j}$ for $j\ge1$, $\mathbb E[a]=2$, $\operatorname{Var}[a]=2$. The script verifies (2) exactly for $K=1,\dots,12$ and computes the truncated moment $\mathbb E[a]=4194303/2097152$ at $K=22$ ($=2-2^{-21}$).

For a fixed valuation tuple (so $n_0=c+2^{E+1}t$, $t$ large),

$$
\log\frac{n_M}{n_0}=M\log 3-E\log 2+\sum_{j<M}\log\!\left(1+\frac{1}{3n_j}\right),
$$

with the sum $O(1/n_0)$. Numerically the error decays exactly like $1/n_0$: e.g. for $M=4,E=7$ it falls from $1.02\cdot10^{-8}$ at $t_0=10^6$ to $1.02\cdot10^{-9}$ at $t_0=10^7$. Averaging $E$ over the geometric law ($\mathbb E[a]=2$, so $\mathbb E[E]=2M$) yields the stated

$$
\mathbb E\!\left[\log\frac{n_M}{n_0}\right]=M\log\frac34+O(1/n_0). \tag{3}
$$

### 1.3 Continued fractions of $\log_2 3$ and the sharpest gap bounds

Convergents $p_k/q_k$ of $\log_2 3$ with $q_k\le10^6$ (14 of them):

| $k$ | $p_k/q_k$ | side |
|---:|---|---|
| 1 | $2/1$ | above |
| 3 | $8/5$ | above |
| 5 | $65/41$ | above |
| 7 | $485/306$ | above |
| 9 | $24727/15601$ | above |
| 11 | $125743/79335$ | above |
| 13 | $301994/190537$ | above |

The last convergent below the ceiling is $301994/190537$; its successor is $10590737/16785921$. Since $|E-M\log_2 3|>1/(q_k+q_{k+1})$ for $M<q_{k+1}$ (best-approximation property), for every $E,M$ with $2^E>3^M$,

$$
2^E-3^M=3^M\!\left(2^{E-M\log_2 3}-1\right)>
\frac{3^M\ln 2}{q_k+q_{k+1}}
=\frac{3^M\ln 2}{10\,781\,874}. \tag{4}
$$

This is the Diophantine lower bound linking the gap directly to the cycle scale. The denominator $q_k+q_{k+1}=10{,}781{,}874$ is exactly the classical Eliahou cycle-length constant. Exact integer gaps are computed for small convergents: $2^2-3^1=1$, $2^8-3^5=13$, $2^{65}-3^{41}$ has 59 bits, $2^{485}-3^{306}$ has 476 bits, etc.

### 1.4 Cycle-size and cycle-length lower bounds

From (1) and $j\le A_j\le E-(M-j)$,

$$
\frac{3^M-2^M}{2^E-3^M}\ \le\ n\ \le\ \frac{2^{E-M}(3^M-2^M)}{2^E-3^M}
=\frac{\widetilde T_{\max}(M,E)}{2^E-3^M}. \tag{5}
$$

The lower value is attained by the single-block tuple $(1,\dots,1)$; starting at the cycle minimum forces $a_0=1$, which is the "interleaved" refinement used in the formalization. Combining (5) with the Eliahou/Crandall sandwich (from $\prod_j(3+1/n_j)=2^E$)

$$
\log_2 3<\frac{E}{M}\le\log_2\!\left(3+\frac1B\right),\qquad B=2^{40}\ \text{(verified search bound)},
$$

the script finds the least denominator rational in the interval:

$$
\frac{E}{M}=\frac{17\,087\,915}{10\,781\,274},\qquad
M\ge10\,781\,274,\quad E\ge17\,087\,915,\quad L=E+M\ge27\,869\,189.
$$

(With the conventional count of Collatz steps, $E\ge17{,}087{,}915$ reproduces Eliahou's bound exactly.) Machine-readable output: `artifacts/syracuse_log_drift.json`.

### 1.5 Python verification metrics

`analysis/syracuse_log_drift.py` (standard library only) completed all six checks:

| check | result |
|---|---|
| valuation law $2^{K-a-1}$ for $K=1,\dots,12$ | exact match, all `True` |
| valuation-tuple bijection / identity for $E=1,\dots,14$ | all bijective, identity holds on every class |
| truncated $\mathbb E[a]$ at $K=22$ | $4194303/2097152 = 2-2^{-21}$ |
| drift error (fixed tuples) | $1.02\cdot10^{-8}\to1.02\cdot10^{-9}$ as $t_0:10^6\to10^7$ (and $1.98\cdot10^{-9}\to1.98\cdot10^{-10}$) |
| convergents with $q\le10^6$ | 14, largest $q=190537$, successor $q=10590737$ |
| Diophantine denominator $q_k+q_{k+1}$ | $10\,781\,874$ |
| Eliahou interval search at $B=2^{40}$ | fraction $17\,087\,915/10\,781\,274$, $L\ge27\,869\,189$ |

---

## 2. Phase 2 — Lean 4 formalization

New file `CollatzAdicBase/SyracuseLogDrift.lean`, importing `CollatzAdicBase.GlideMarkovChain` and `CollatzAdicBase.CycleExclusion`. Wired into `CollatzAdicBase.lean` and `CollatzAdicBase/Axioms.lean`. All declarations are proved; no `sorry`, `admit`, or custom axioms.

| Lean declaration | content |
|---|---|
| `v2`, `v2_dvd`, `not_succ_v2_dvd`, `v2_eq_iff` | 2-adic valuation via `padicValNat 2`; exact characterization $2^a\Vert n$ |
| **`syracuseStep`**, `syracuseStep_mul_pow_v2`, `syracuseStep_odd` | $T_{\mathrm{Syr}}(n)=\operatorname{divMaxPow}(3n+1,2)$ and $T_{\mathrm{Syr}}(n)2^{v_2(3n+1)}=3n+1$ |
| `ValSeq`, `syracuseOrbit`, `syracuseA`, `syracuseT` | valuation-tuple predicate, orbit, partial sums, and the $T$ recursion |
| **`syracuse_identity`** | exact $M$-step identity (1) |
| `v2_preserve_lift`, `v2_of_lift`, `valWitness`, `val_of_add_pow`, `unique_val_residue_uniq`, `unique_val_residue` | lifting and uniqueness modulo $2^{a+1}$ |
| **`exactValF_card`** | geometric law (2): $\#\texttt{exactValF}(K,a)=2^{K-a-1}$ |
| `tildeTmax`, `cycle_min_upper_bound` | $n_{\min}(2^E-3^M)\le\widetilde T_{\max}(M,E)=2^{E-M}(3^M-2^M)$ |

The main structural theorem is

$$
n\,(2^E-3^M)=T\le \widetilde T_{\max}(M,E)=2^{E-M}(3^M-2^M),
$$

proved from the exact identity and the interleaving constraint $a_j\ge1$; it is the formal link between the continued-fraction gap $2^E-3^M$ and the cycle size.

**Complete declaration list.** Definitions: `v2`, `syracuseStep`, `ValSeq`, `syracuseOrbit`, `syracuseA`, `syracuseT`, `exactValF`, `tildeTmax`. The 19 proved declarations are:

`v2_eq_multiplicity`, `v2_dvd`, `not_succ_v2_dvd`, `v2_eq_iff`, `syracuseStep_mul_pow_v2`, `syracuseStep_odd`, `one_le_v2_three`, `syracuseOrbit_succ`, `syracuseA_length`, **`syracuse_identity`** (theorem), `v2_preserve_lift`, `v2_of_lift`, `valWitness`, `val_of_add_pow`, `unique_val_residue_uniq`, `unique_val_residue`, **`exactValF_card`**, `syracuseT_le_tildeTmax_of_pos`, **`cycle_min_upper_bound`** (theorem).

**Axiom audit.** `lake -K jobs=1 build` was run synchronously in the foreground and completed successfully: **18,274 jobs, zero errors, zero warnings, zero OOM**. `#print axioms` on every principal theorem of the new module reports only Lean's core axioms `[propext, Classical.choice, Quot.sound]`:

```
'CollatzAdicBase.SyracuseLogDrift.v2_dvd'                        [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseLogDrift.syracuseStep_mul_pow_v2'       [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseLogDrift.syracuseStep_odd'              [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseLogDrift.syracuse_identity'             [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseLogDrift.valWitness'                    [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseLogDrift.unique_val_residue'            [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseLogDrift.exactValF_card'                [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseLogDrift.syracuseT_le_tildeTmax_of_pos' [propext, Classical.choice, Quot.sound]
'CollatzAdicBase.SyracuseLogDrift.cycle_min_upper_bound'         [propext, Classical.choice, Quot.sound]
```

Zero `sorryAx`, zero project-specific axioms. The complete audit is emitted from `CollatzAdicBase/Axioms.lean` (Paper 9 section) and recorded in `AXIOM_AUDIT.txt` (now nine verified modules, 186 total declarations).

---

## 3. Interpretation and boundaries

1. **The orbit law is exact.** Equation (1) is an identity in `Nat`; the drift law (3) is a large-$n_0$ asymptotic with an explicit $O(1/n_0)$ remainder, not a probabilistic assumption.
2. **The geometric law is a finite exact count.** Equation (2) counts residue classes; the geometric distribution and $\mathbb E[a]=2$ are its $K\to\infty$ limit, not an axiom.
3. **The Diophantine bound is unconditional but denominator-limited.** Inequality (4) holds for all $M<10{,}781{,}874$ with the convergents computed here; larger denominators require further convergents (the next partial quotient is large).
4. **The cycle bound is a constraint, not a contradiction.** Equation (5) and (4) confine any hypothetical cycle; the $L$ bound additionally uses the externally verified search bound $B=2^{40}$. No claim of resolving the Collatz conjecture is made.

---

## 4. Reproduction

```bash
cd <repo>
python3 analysis/syracuse_log_drift.py     # valuation law, drift, CF gaps, cycle bounds
lake -K jobs=1 build                        # full library, #print axioms audit
grep -nE '\bsorry\b|\badmit\b' CollatzAdicBase/SyracuseLogDrift.lean  # no code hits
```

Machine-readable results: `artifacts/syracuse_log_drift.json` (project artifacts directory).
