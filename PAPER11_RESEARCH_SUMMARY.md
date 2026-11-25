# Paper 11 — Research Summary: Maximum Upward Excursion Bounds for Multi-Step Syracuse Trajectories (Layer 6)

**Baseline.** The verified `CollatzAdicBase` library, using the `v1.4.0` modules
`SyracuseRenewal.lean`, `SyracuseLogDrift.lean`, `GlideMarkovChain.lean` and
`StoppingTimeDensity.lean`.

> **State note.** The current HEAD (`e659c92`, "Remove SyracuseRenewal module
> and analysis scripts") had *deleted* `SyracuseRenewal.lean` and its audit
> lines after the `v1.4.0` tag. To honour the stated baseline, the v1.4.0
> version of that single module was restored verbatim (with its imports and
> `#print axioms` lines in `CollatzAdicBase.lean` / `CollatzAdicBase/Axioms.lean`);
> no other deleted artifacts were reintroduced. All 10 audited modules still
> use core axioms only.

**Two phases.**
1. Analysis: prefix ratio bound, definition of the peak-excursion event, and an
   explicit uniform rational power-law tail derived with the geometric valuation
   MGF; exact finite-modulus verification in `analysis/excursion_tail.py`.
2. Formalization: `CollatzAdicBase/ExcursionTail.lean`, wired into the library
   and axiom-audited.

---

## 1. Phase 1 — prefix bound and excursion tail

### 1.1 Exact prefix ratio bound

For odd $n_0$, valuation list $a_0,\dots,a_{M-1}$,
$A_j=\sum_{i<j}a_i$ and drift $T_j=\sum_{i<j}3^{j-1-i}2^{A_i}$, the verified
identity (`SyracuseLogDrift.syracuse_identity`) reads

$$n_j\,2^{A_j}=3^j n_0+T_j .$$

Dividing by $n_0 2^{A_j}$ gives the *exact* rational ratio

$$\frac{n_j}{n_0}=\frac{3^j}{2^{A_j}}+\frac{T_j}{n_0\,2^{A_j}} .$$

Since every $a_i\ge 1$, $A_j-A_i\ge j-i$, hence

$$\frac{T_j}{2^{A_j}}=\sum_{i<j}3^{j-1-i}2^{A_i-A_j}
 \le \sum_{i<j}\frac{3^{j-1-i}}{2^{j-i}}
 =\left(\tfrac32\right)^j-1=\frac{3^j-2^j}{2^j},$$

so

$$\frac{n_j}{n_0}\le\frac{3^j}{2^{A_j}}+\frac{3^j-2^j}{n_0\,2^j}.$$

Both inequalities are formalised in `syracuseOrbit_ratio_le`. The second is the
sharp envelope `tildeTmax(j, A_j)=2^{A_j-j}(3^j-2^j)` already proved in
`SyracuseLogDrift.syracuseT_le_tildeTmax_of_pos`.

### 1.2 Excursion event

For $B>1$ define the *multiplicative* peak-excursion event

$$\mathcal E(M,B)=\Bigl\{\exists\,1\le j\le M:\;3^j\ge B\,2^{A_j}\Bigr\}
 =\Bigl\{\max_{1\le j\le M}\tfrac{3^j}{2^{A_j}}\ge B\Bigr\}.$$

By the displayed bound, an excursion forces $n_j\ge B\,n_0$ (the additive drift
is nonnegative), so controlling $\mathcal E(M,B)$ controls genuine upward
excursions of the orbit, up to the explicitly bounded additive term.

### 1.3 Uniform power-law tail, $\lambda=1/2$

The exact geometric valuation law gives
$\mathbb E[2^{-\lambda a}]=1/(2^{\lambda+1}-1)$; at $\lambda=1/2$ the optimal
contraction is $\rho^*=\sqrt3/(2\sqrt2-1)=0.94729\ldots$, i.e. $C^*=17.97\ldots$.
We certify this with pure rationals:

* tilt $x=5/7\ge 2^{-1/2}$ because $(5/7)^2=25/49>1/2$;
* envelope $\beta=26/15\ge\sqrt3$ because $(26/15)^2=676/225>3$;
* MGF $x/(2-x)=5/9$, so $\rho=\beta\cdot 5/9=26/27<1$ and
  $C=\rho/(1-\rho)=26$.

A union bound over $j$ (equivalently, the composition generating function
$\sum_E \mathrm{compCount}(j,E)(5/14)^E\le(5/9)^j$; verified in Python) gives

$$\mathbb P\!\left(\max_{1\le j\le M}\frac{3^j}{2^{A_j}}\ge B\right)\le
 \frac{\rho}{1-\rho}\,B^{-1/2}=26\,B^{-1/2},$$

**uniformly in the horizon $M$**. This is the algebraic (rather than exponential)
rate: almost every trajectory's prefix multiplier stays $O(B)$ outside a set of
density $O(B^{-1/2})$, a finite-density analogue of the direction of Tao's
logarithmic-density theorem. It is *not* a proof of that theorem.

The Lean proof uses a slightly different, cleaner induction that avoids explicit
composition counting: a residue with first valuation $a$ maps injectively into
the excursion problem at modulus $2^{K-a}$ with tilted threshold
$B'=B2^a/3$, and the certificate
$\sqrt{B'}\ge(15/26)(7/5)^a\sqrt B$ makes the induction multiplicative with
contraction $\rho=26/27<1$. The result is therefore uniform in $K$ as well:

$$\#\{\text{odd }r\bmod 2^K\text{ with an excursion}\}\cdot\sqrt B\le 26\cdot2^{K-1}.$$

### 1.4 Python verification — `analysis/excursion_tail.py`

Exact integer/`Fraction` checks, no third-party packages:

* the prefix identity and both inequalities of §1.1 for 12 starting values and
  $j=1,2,3,5,8,12$ — all pass;
* the rational certificates $x^2\ge1/2$, $\beta^2\ge3$, $\rho<1$, $C=26$ — pass;
* the composition generating-function bound for $j=1,\dots,12$ — pass;
* **exact prefix-maximum survivor/failure counts** for every modulus
  $K=1,\dots,16$ and every threshold $B\in\{2,4,8,16,32\}$ (counted from the
  exact valuation prefixes determined by $r\bmod 2^K$, with both `fail` and
  `survivors` recorded), checked in the exact squared form
  $\mathrm{fail}^2\cdot B\le 26^2\cdot4^{K-1}$ — all 80 checks pass;
* additional large thresholds at $K=16$ — pass.

Machine-readable output: `/home/nix/.local/share/openresearch/files/collatz-adic-lean/excursion_tail.json`;
text table: `analysis/excursion_tail.txt`.

**Honest caveat on the numerical strength.** For the requested $B\le32$ the
bound $26/\sqrt B\ge4.6>1$ is weaker than the trivial bound, so these checks
validate consistency, not sharpness. At $K=16$ every prefix has sum $<16$, so
the largest attainable ratio is $<3^{15}/2^{15}\approx207$; thresholds
$B\in\{4096,2^{16},2^{20}\}$ consequently have zero excursions at that modulus.
A non-vacuous numerical test of the *decay rate* requires larger $K$ (or the
infinite geometric model); the Lean theorem itself is uniform in $K$ and $M$.

---

## 2. Phase 2 — Lean 4 formalization

New file `CollatzAdicBase/ExcursionTail.lean` (imports
`CollatzAdicBase.SyracuseRenewal`). Principal declarations:

| Declaration | Content |
|---|---|
| `valSeq_pos`, `valSeq_take`, `syracuseA_take`, `length_le_sum_of_pos` | prefix bookkeeping from `ValSeq` |
| `syracuseOrbit_ratio_eq` | exact rational ratio equality from `syracuse_identity` |
| `syracuseT_prefix_mul_le` | $T_j2^j\le 2^{A_j}(3^j-2^j)$ |
| **`syracuseOrbit_ratio_le`** | the two-sided prefix ratio bound of §1.1 |
| `valList`, `valList_ValSeq`, `excursionAux`, `excursionAux_iff` | computable valuation prefixes and the rational excursion predicate |
| **`excursionFailF`**, `mem_excursionFailF`, `excursionFailF_witness` | finite-modulus excursion set and witness extraction |
| `excursionFailF_orbit_ge` | excursion $\Rightarrow n_j\ge B n_0$ |
| `cancel_six_pow`, `lift_step_eq`, `val_first_decomp`, `valSeq_modEq`, `valList_eq_of_modEq`, `oneStep_inj` | valuation-code congruence and one-step injectivity on the valuation-$a$ fibre |
| `excursionAux_shift`, `excursionFailF_tail_mem` | renewal of the tail at threshold $B2^a/3$, modulus $K-a$ |
| `oddFin_card_le`, `pow_seven_five_sq_le_two`, `sqrt_tilt_mul` | finite counting and rational sqrt certificates |
| **`excursionFailF_tail_uniform`** | $\#\mathcal E\cdot\sqrt B\le 26\cdot2^{K-1}$, uniform in $M$ and $K$ |

All proofs are constructive over core Lean; no `sorry`, `admit`, or custom axiom.
`CompCount` and the geometric MGF identity from `SyracuseRenewal` remain available
but the final induction uses only the renewal map and the rational certificate.

### Axiom audit

`#print axioms` for `syracuseOrbit_ratio_le`, `excursionFailF`,
`excursionFailF_orbit_ge`, `oneStep_inj`, `valList_eq_of_modEq` and
`excursionFailF_tail_uniform` reports only
`[propext, Classical.choice, Quot.sound]` — **zero `sorryAx`, zero custom
axioms**. The audit lines are in `CollatzAdicBase/Axioms.lean`.

### Build

`lake -K jobs=1 build` was run synchronously in the foreground: **Build completed
successfully (18278 jobs)**, zero errors, zero warnings.  The Prompt 11 build
log is `AXIOM_PAPER11.txt`; the regenerated **complete** audit across all eleven
modules is `AXIOM_AUDIT.txt` (153 axiom printouts, `grep -c sorryAx` = **0**,
no project-specific axiom).

---

## 3. Deliverables

* `analysis/excursion_tail.py`, `analysis/excursion_tail.txt`
* `CollatzAdicBase/ExcursionTail.lean`
* `CollatzAdicBase.lean`, `CollatzAdicBase/Axioms.lean` (wiring + audit)
* `PAPER11_RESEARCH_SUMMARY.md` (this file)
