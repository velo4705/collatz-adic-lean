# Paper 12 — Research Summary: Bounded-Excursion Syracuse Contraction and Dyadic Logarithmic-Density Decay (Layer 7)

**Baseline.** The verified `CollatzAdicBase` library at `v1.5.0`, in particular
`ExcursionTail.lean`, `SyracuseRenewal.lean`, `SyracuseLogDrift.lean` and
`GlideMarkovChain.lean`.

**Two phases.**
1. Analysis: union-bound the Layer 5 terminal-decay and Layer 6 uniform
   excursion-tail events; derive the explicit good-residue density, the
   pathwise peak/contraction theorem, and the dyadic logarithmic-density rate;
   verify exact survivor counts in `analysis/log_density_contraction.py`.
2. Formalization: `CollatzAdicBase/LogDensityContraction.lean`, wired into the
   library and axiom-audited.

---

## 1. Phase 1 — union bound, pathwise contraction, dyadic rate

### 1.1 The two exceptional events at `K = 8t`, `M = 5t`

For an odd start with accelerated valuations $a_0,\dots,a_{M-1}$,
$A_j=\sum_{i<j}a_i$, the verified identity is

$$n_j 2^{A_j}=3^j n_0+T_j,\qquad T_j=\sum_{i<j}3^{j-1-i}2^{A_i}\ge 0,$$

and `ExcursionTail.syracuseOrbit_ratio_le` gives

$$\frac{n_j}{n_0}\le \frac{3^j}{2^{A_j}}+\frac{3^j-2^j}{n_0 2^j}
\le \frac{3^j}{2^{A_j}}+\frac{(3/2)^j}{n_0}.$$

At modulus $2^K$, horizon $M$, threshold $B>0$, the two exceptional sets of odd residues are

* $\mathcal F_t=\texttt{syracuseFailF}(8t,5t)=\{r: 2^{A_M}\le 3^M\}$ (terminal non-contraction),
* $\mathcal E_{t,B}=\texttt{excursionFailF}(8t,5t,B)=\{r: A_M<K,\; \exists j\le M,\;3^j\ge B\,2^{A_j}\}$.

The verified bounds are, in exact integer form,

$$2\,|\mathcal F_t|\,25^{5t}\le 24^{5t}2^{8t}
\quad\Longleftrightarrow\quad \frac{|\mathcal F_t|}{2^{K-1}}\le\Bigl(\frac{24}{25}\Bigr)^{5t},$$

$$|\mathcal E_{t,B}|\sqrt B\le 26\cdot 2^{K-1}
\quad\Longleftrightarrow\quad \frac{|\mathcal E_{t,B}|}{2^{K-1}}\le \frac{26}{\sqrt B}.$$

### 1.2 Union bound and the good set

With $\mathcal X(t,B)=\mathcal F_t\cup\mathcal E_{t,B}$ and
$\mathcal G=\mathcal X^c$ (among odd residues), a union bound gives

$$\delta(t,B):=\frac{|\mathcal X|}{2^{K-1}}
 \le \Bigl(\frac{24}{25}\Bigr)^{5t}+\frac{26}{\sqrt B},
\qquad \frac{|\mathcal G|}{2^{K-1}}\ge 1-\Bigl(\frac{24}{25}\Bigr)^{5t}-\frac{26}{\sqrt B}.$$

This is the content of `goodTrajectory_card_lower`; note that both exceptional
sets consist of odd classes, and that the odd classes mod $2^K$ number exactly
$2^{K-1}$ for $K\ge1$ (`oddFin_card_ge`).

### 1.3 Pathwise peak bound and net contraction

Let $n_0$ be odd, $A_M+1\le K$ (so the residue mod $2^K$ determines the first
$M$ accelerated valuations, via `valList_eq_of_modEq`), let its residue lie in
$\mathcal G$, and put

$$N_0(K,M)=2^{K-1}\Bigl(\frac32\Bigr)^M = 2^{K-1-M}3^M
\qquad\bigl(=2^{3t-1}3^{5t}\text{ at }K=8t,M=5t\bigr).$$

*Goodness forbids the excursion*, so for every $j\le M$,
$3^j/2^{A_j}<B$. Combined with the ratio bound and
$(3/2)^j/n_0\le (3/2)^M/n_0<2^{-(K-1)}\le1$:

$$\frac{n_j}{n_0}< B+1\quad\Longrightarrow\quad n_j\le (B+1)n_0 .$$

*Goodness forbids terminal non-contraction*, so $3^M<2^{A_M}$; since these are
integers, $3^M/2^{A_M}\le 1-2^{-A_M}\le 1-2^{-(K-1)}$. The drift term is
$(3^j-2^j)/(n_0 2^j)\le (3/2)^M/n_0<2^{-(K-1)}$, hence

$$\frac{n_M}{n_0}\le \underbrace{\bigl(1-2^{-(K-1)}\bigr)}_{\text{contractFloor}}+\frac{(3/2)^M}{n_0}<1,$$

so $n_M<n_0$. More generally, for any $\alpha\ge 1-2^{-(K-1)}$ with
$(3/2)^M\le(\alpha-\texttt{contractFloor}(K))\,n_0$, we get $n_M\le\alpha n_0$.

**Necessary conditioning.** For small $t$ (in fact $t\le 13$), every
non-contracting-free residue mod $2^{8t}$ has $A_M\ge 8t=K$ because
$3^{5t}>2^{8t-1}$; then the class mod $2^K$ alone does *not* determine the
orbit. The hypothesis $A_M+1\le K$ is therefore essential and is stated
explicitly in the theorem. The analytic core is valid for any modulus bound
$L\ge A_M+1$; the Python checks use $L=2M$ for this reason.

### 1.4 Dyadic logarithmic-density rate

On $[X,2X]$ take $t=\lfloor\lambda\log\log X\rfloor$ and $B=(\log X)^c$
(natural logs). Then $2^K=(\log X)^{8\lambda\log 2}\ll X$ and
$N_0=(\log X)^{\lambda(8\log 2+5\log(3/2))}\ll X$, so each residue class is
equidistributed and the threshold is below the scale. The exceptional density is

$$\delta(X)\le \exp\!\bigl(-5\lambda\log(25/24)\,\log\log X\bigr)
              +26(\log X)^{-c/2}
            = O\!\bigl((\log X)^{-\gamma}\bigr),$$

$$\gamma=\min\bigl(5\lambda\log(25/24),\,c/2\bigr)
       \approx \min(0.20411\,\lambda,\,c/2).$$

With $\lambda=1$, $c=2$ we get $\gamma\approx0.20411$. Because $\lambda$ may grow
slowly with $X$ (subject to $2^{8t}\le X$), the density decays faster than any
fixed power of $\log X$ — but only on the logarithmic scale; this is **not** a
power-of-$X$ density bound and **not** a proof of Tao's logarithmic-density
theorem.

### 1.5 Python verification — `analysis/log_density_contraction.py`

Exact integer/`Fraction` checks, no third-party packages. For $t=1,2$
($K=8,16$, $M=5,10$) and $B\in\{4,16,64,256\}$ the script counts every odd
residue, every terminal-failure class, every excursion class, their union and
the good complement; it checks both analytic inequalities in integer form, the
union bound, and the rational lower bound. It also verifies the pathwise peak,
contraction and exact identity on samples above $N_0$, and the dyadic rate.
All checks pass (`ALL CHECKS PASS: True`).

| $t$ | $K$ | $B$ | odd residues | fail | excursion | good |
|---|---|---|---|---|---|---|
| 1 | 8 | 4 | 128 | 29 | 7 | 99 |
| 1 | 8 | 16 | 128 | 29 | 0 | 99 |
| 2 | 16 | 4 | 32768 | 4944 | 2922 | 27824 |
| 2 | 16 | 16 | 32768 | 4944 | 436 | 27824 |

The bound $26/\sqrt B$ exceeds 1 for these small $B$, so the finite scans
validate consistency, not sharpness; at $B=64,256$ the excursion count is 0.
Machine-readable output: `/home/nix/.local/share/openresearch/files/collatz-adic-lean/log_density_contraction.json`;
text table: `analysis/log_density_contraction.txt`.

---

## 2. Phase 2 — Lean 4 formalization

New file `CollatzAdicBase/LogDensityContraction.lean` (imports
`CollatzAdicBase.ExcursionTail`). Principal declarations:

| Declaration | Content |
|---|---|
| `goodTrajectoryF`, `mem_goodTrajectoryF` | odd classes avoiding both exceptional sets |
| `valList_eq_of_ValSeq` | a `ValSeq` witness equals the canonical valuation list |
| `mem_syracuseFailF_iff_valList`, `not_mem_syracuseFailF_contracts` | non-membership $\Rightarrow 3^M<2^{A_M}$ |
| `not_mem_excursionFailF_no_excursion` | non-membership $\Rightarrow$ no prefix reaches $B$ |
| `oddFin_card_ge` | $\ge 2^{K-1}$ odd classes mod $2^K$ |
| `contractThreshold`, `contractFloor` | $N_0=2^{K-1}(3/2)^M$, floor $1-2^{-(K-1)}$ |
| **`bounded_and_contracts_of_vals`** | analytic core: peak $\le B+1$ and $n_M/n\le\text{floor}+(3/2)^M/n$ |
| **`goodTrajectory_card_lower`** | union-bound density $\ge 1-(24/25)^{5t}-26/\sqrt B$ |
| `goodTrajectory_vals_of_residue` | transfer from residue class to valuation list |
| **`goodTrajectory_bounded_and_contracts`** | $n_j\le(B+1)n_0$ for $1\le j\le M$ and $n_M<n_0$ |
| `goodTrajectory_contracts_to_alpha` | arbitrary target factor $\alpha$ above the floor |

All proofs are constructive over core Lean; no `sorry`, `admit`, or custom
axiom. The residue transfer uses `valList_eq_of_modEq` from Layer 6 and
requires $A_M+1\le K$, as discussed in §1.3.

### Axiom audit and build

`lake -K jobs=1 build` was run **synchronously in the foreground**: **Build
completed successfully (18280 jobs)**, zero errors, zero failures. The complete
build log is `AXIOM_PAPER12.txt`; the regenerated full audit across all twelve
audited modules is `AXIOM_AUDIT.txt` (91 `#print axioms` declarations: 90 with
axiom lists and `StoppingTimeDensity.k8_partition` axiom-free; `grep -c sorryAx`
= **0**; the only axioms are `propext`, `Classical.choice`, `Quot.sound`). Every
new declaration's `#print axioms` reports only those three.

---

## 3. Deliverables

* `analysis/log_density_contraction.py`, `analysis/log_density_contraction.txt`,
  `artifacts/log_density_contraction.json`
* `CollatzAdicBase/LogDensityContraction.lean`
* `CollatzAdicBase.lean`, `CollatzAdicBase/Axioms.lean` (wiring + audit)
* `AXIOM_PAPER12.txt`, `AXIOM_AUDIT.txt`
* `PAPER12_RESEARCH_SUMMARY.md` (this file)
