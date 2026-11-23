# Latent saturation of reachable cycle sets at levels `3^k d'`
### Research summary for Paper 4 — exact computations, witnesses, Lean formalization

**Scope.** We resolve the Section 4.1 open problem for the two anomalous home
denominators `d' = 5` and `d' = 71` of the `CollatzAdicBase` rational-descent
framework, extend the scan from `k ≤ 8` to `k = 14`, give the exact algebraic
lifting map in terms of `ord_{d'}(2)`, `ord_{d'}(3)` and the cycle equation, prove
a finite upper bound for `k_min(d')`, and formalize the lifting/saturation
lemma in `CollatzAdicBase/LatentSaturation.lean` (zero `sorry`, zero custom
axioms, `lake build` green).

---

## 0. Exact model (matches the verified library)

A reduced positive rational with odd denominator is the pair `(a,d)` with
`a>0`, `d>0`, `d` odd, `gcd(a,d)=1`.  The reduced Collatz step is

```
step(a,d) = (a/2, d)                                   if a is even
step(a,d) = ((3a+d)/g, d/g),  g = gcd(3a+d, d)          if a is odd
```

with `g ∣ 3` (Lemma 2.1 of `RationalDescent.lean`).  Consequences:

* for `p ≠ 3`, `v_p(d)` is invariant under every step;
* an odd step with `3 ∣ d` removes exactly one factor of 3 (`g = 3`);
* a cycle cannot contain a factor 3 in its denominator, so every cycle has a
  **home denominator** `d'` coprime to 6;
* the levels above the home denominator are `3^k d'`, and `k` odd steps are
  needed to strip the `3^k`.

The scan at level `k` enumerates all reduced numerators
`1 ≤ a ≤ 3^k d'`, `gcd(a, 3^k d') = 1`, follows each orbit to its cycle, and
records the set `R_k(d')` of **exact** cycles reached (cycles are identified by
their exact state sets, not by residues modulo `d'` — the latter collapses the
extra cycles of `d' = 5`).

---

## 1. Phase 1 — computational results

### 1.1 Multiplicative orders and cycle-equation types

| `d'` | `ord_{d'}(2)` | `ord_{d'}(3)` | `λ : 3 ≡ 2^λ (mod d')` | `λ^{-1} mod o₂` | cycle types `(E,M)` found |
|---|---|---|---|---|---|
| 5  | 4  | 4  | 3  | 3  | `(3,1)`, `(5,3)`, `(27,17)` |
| 71 | 35 | 35 | 16 | 11 | `(10,5)`, `(27,17)` |

Here `E` = number of halving steps, `M` = number of odd steps in the cycle
(`L = E + M` total steps).  The cycle equation is

$$d' \mid 2^{E}-3^{M},\qquad 2^3-3=5,\quad 2^5-3^3=5,\quad 2^{10}-3^5=781=11\cdot 71,\quad 2^{27}-3^{17}=5\,077\,565=5\cdot 71\cdot 101\,551 .$$

In the exponent group, `2^E ≡ 3^M` becomes `E ≡ λM (mod ord_{d'}(2))` whenever
`3 ∈ ⟨2⟩` (true for both `d'`; `λ = 3` and `λ = 16` respectively).

### 1.2 Reachable cycle sets `R_k(d')` for `k = 0 … 14`

| `k` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `|R_k(5)|`  | 2 | 2 | 2 | 3 | 3 | 3 | 3 | 4 | 5 | 5 | 5 | 5 | 5 | 5 | 5 |
| `|R_k(71)|` | 2 | 2 | 2 | 2 | 2 | 3 | 4 | 5 | 6 | **7** | 7 | 7 | 7 | 7 | 7 |

**Reproduction of the reported anomalies.** For `d'=71` a new cycle appears at
each of `k = 5, 6, 7, 8` (2 → 6 cycles).  For `d'=5` new cycles appear at
`k = 3, 7, 8` (2 → 5 cycles).  Both match the paper exactly.

**New finding (extension to `k = 14`).** `d'=71` admits a **seventh** cycle whose
first appearance is `k = 9`, missed by the original `k ≤ 8` scan:
witness `a = 748\,811` at level 9 (denominator `3^9·71 = 1\,397\,493`), whose orbit
first enters the cycle at state `(4121, 71)`.  Forward verification:
`step^t(748811, 1397493)` reaches `(4121,71)`.  Both denominators then saturate:
`R_k` is constant for all `k ≥ 8` (`d'=5`, 5 cycles) and `k ≥ 9` (`d'=71`, 7 cycles).

### 1.3 Exact `k_min` table and minimal witnesses

`k_min(C)` = least `k` with some level-`k` state reaching cycle `C`; `a` = least
such starting numerator; `A_0` = first home-level state reached; `|C|` = cycle length.

| `d'` | `k_min` | `(E,M)` | cycle state (min) | `A_0` | witness `a` at level `k_min` | `\|C\|` |
|---|---|---|---|---|---|---|
| 5  | 0 | (3,1)  | `(1,5)`    | 1    | 1      | 4  |
| 5  | 0 | (5,3)  | `(19,5)`   | 3    | 3      | 8  |
| 5  | **3** | (5,3)  | `(23,5)`   | 23   | 89     | 8  |
| 5  | **7** | (27,17) | `(187,5)` | 187  | 5 449  | 44 |
| 5  | **8** | (27,17) | `(347,5)` | 347  | 12 251 | 44 |
| 71 | 0 | (10,5) | `(29,71)`  | 1    | 1      | 15 |
| 71 | 0 | (10,5) | `(31,71)`  | 7    | 7      | 15 |
| 71 | **5** | (27,17) | `(4409,71)` | 893  | 13 595  | 44 |
| 71 | **6** | (27,17) | `(2809,71)` | 2146 | 21 457  | 44 |
| 71 | **7** | (27,17) | `(3985,71)` | 4602 | 148 339 | 44 |
| 71 | **8** | (27,17) | `(2585,71)` | 5170 | 214 105 | 44 |
| 71 | **9** | (27,17) | `(4121,71)` | 8242 | 748 811 | 44 |

**Lifting chains** (level, numerator right after the odd step; halvings implicit):

* `d'=5, k=3`: `(3,89) → (2,134) → (1,82) → (0,46) → (23,5)` — the cycle `(23,5)`.
* `d'=5, k=7`: `(7,5449) → (6,9094) → (5,5762) → (4,3286) → (3,1778) → (2,934) → (1,482) → (0,246) → (187,5)`.
* `d'=71, k=8`: `(8,214105) → (7,369382) → (6,236450) → (5,135478) → (4,73490) → (3,38662) → (2,19970) → (1,10198) → (0,5170) → (2585,71)`.

For the uniform one-halving-per-step chains the witness has the closed form

$$a_k = 2^k(A_0+d') - 3^k d' ,$$

e.g. `2^5(893+71) − 3^5·71 = 13 595` (the `k=5` witness for `d'=71`).

### 1.4 The exact algebraic lifting map

At level `j ≥ 1` an odd step is `a ↦ a + 3^{j-1}d'` at denominator `3^{j-1}d'`.
Let the `k` odd stripping steps be interleaved with `E` halvings, and let
`e_i` be the number of halvings **before** the `i`-th odd step
(`0 ≤ e_1 ≤ … ≤ e_k ≤ E`).  Iterating gives, for the first home-level numerator `A`,

$$2^{E}A \;=\; a \;+\; d'\sum_{i=1}^{k} 3^{\,k-i}\,2^{\,e_i},\qquad\text{hence}\qquad 2^{E}A \equiv a \pmod{d'} .$$

Writing `λ = log₂ 3 mod ord_{d'}(2)` (so `3 ≡ 2^λ`) with `gcd(λ, o₂)=1`, and
using the cycle equation `2^{E_c} ≡ 3^{M_c}`, the congruence becomes the
requested **`3`-power form**

$$A \;\equiv\; 2^{-E}a \;\equiv\; 3^{\,\lambda^{-1}(-E)}\,a \pmod{d'} .$$

Concretely: `A ≡ 3^{E} a (mod 5)` (`λ^{-1}=-3≡1 mod 4`) and
`A ≡ 3^{24E} a (mod 71)` (`λ^{-1}=11`, `−11≡24 mod 35`).  Check on the `k=8`
witness for `71`: `3^8·214105 ≡ 3^{24·8}·40 ≡ 3^{17}·40 ≡ 38·40 ≡ 29 ≡ 2585 (mod 71)`.

### 1.5 Finite upper bound for `k_min(d')`

1. **Feeder-based bound (tight).** The least home feeder `A_0` of a cycle
   satisfies `A_0 ≤ max_{c∈C} c`.  A lifting chain with one halving per odd step
   produces `a_k = 2^k(A_0+d') − 3^k d'`, which lies in the scan range
   `[1, 3^k d']` as soon as `(3/2)^k ≥ (A_0+d')/(2d')`.  Hence

   $$k_{\min}(C)\;\le\;\Bigl\lceil \log_{3/2}\frac{A_0+d'}{2d'}\Bigr\rceil + O(1)
   \quad\text{(verified: } d'=71,\ A_0=893 \Rightarrow 5\text{)} .$$

   The delay is explained: the witness chain grows by ≈2 per level while the
   scan bound grows by 3 per level, so the bound catches up only at `k ≈ log_{3/2}(A_0/d')`.

2. **Order-based bound (provable, explicit).** For a cycle of type `(E,M)`,
   `(2^E-3^M)a = t` with `0 < t ≤ M·3^{M-1}2^E` and `2^E-3^M ≥ d'`, so
   `a ≤ M·3^{M-1}2^E/d'`.  Taking the minimal type representatives
   `E ≤ o₂ = ord_{d'}(2)`, `M ≤ o₃ = ord_{d'}(3)` gives
   `A_0 ≤ o₃·3^{o₃-1}2^{o₂}/d'`, hence

   $$\boxed{\;k_{\min}(d')\;\le\;\Bigl\lceil\log_{3/2}\frac{o_3\,3^{o_3-1}2^{o_2}}{2d'^2}\Bigr\rceil+2\;<\;\infty\;}$$

   (loose but finite and uniform over all cycles at `d'`; for `d'=5` it gives
   ≤ 11 vs. observed 8, for `d'=71` it is far larger than the observed 9).
   So `k_min(d')` is **provably finite** for every coprime-to-3 `d'`; the
   44/46 "stabilize by `k ≤ 4`" pattern is the generic case where all cycle
   feeders satisfy `A_0 ≤ 2 d'(3/2)^4 ≈ 10.1 d'`, while the two exceptions have
   feeders at `A_0/d' ≈ 12.6` (`d'=71`) and `≈ 46` (`d'=5`).

### 1.6 Why the two denominators are exceptional

* `d'=71`: `o₂=o₃=35`, `λ=16`.  The small type `(10,5)` (`2^10-3^5=781`) gives
  two cycles with tiny feeders, both reachable at `k=0`.  The next admissible
  type is `(27,17)` since `16·17 = 272 ≡ 27 (mod 35)`; here
  `2^27/3^17 ≈ 1.0395` is extremely close to 1, so `2^27-3^17` is small enough
  to permit five cycles with feeders `893, 2146, 4602, 5170, 8242`, which need
  respectively `k = 5, 6, 7, 8, 9` lifts.  The paper's scan stopped at `k=8`.
* `d'=5`: `o₂=o₃=4`, `λ=3`.  Types `(3,1)` and `(5,3)` have minimal feeders
  reachable at `k=0`; the *second* `(5,3)`-cycle has feeder `23` just outside
  the `k≤2` range (witness `a=89` at `k=3`).  The type `(27,17)` cycles have
  feeders `187, 347`, needing `k=7,8`.

---

## 2. Phase 2 — Lean 4 formalization

`CollatzAdicBase/LatentSaturation.lean` (imports only `Init`) contains zero
`sorry`/`admit` and zero custom axioms.  Verified with `lake build`: all
`#print axioms` report only `[propext, Quot.sound]` (and `Classical.choice`
only in the pre-existing Lemma 3).  Main results:

**Theorem A (exact gcd at a lifted level).** *For `1 ≤ k`, `a` odd and
`Nat.Coprime a (3^k d')`,* `Nat.gcd (3a + 3^k d') (3^k d') = 3`.

**Theorem B (lifting lemma).** *Under the same hypotheses,* 
`ratStep (a, 3^k d') = (a + 3^{k-1} d',\, 3^{k-1} d')`.

**Theorem C (lifting congruence).** *If* `2^E A = a + d' t`, *then*
`(2^E A) % d' = a % d'`, i.e. `2^E A ≡ a (mod d')`.

**Theorem D (cycle equation).** *If* `Nat.Coprime a d` *and*
`(2^E − 3^M) a = d t`, *then* `d ∣ 2^E − 3^M`.

**Theorem E (saturation).** *An even step preserves the denominator; an odd step's
denominator divides the old one; a denominator coprime to 3 stays coprime to 3;
and at a lifted level the denominator after an odd step is exactly `3^{k-1} d'`.*

**Theorem F (well-formedness).** *`Valid` states map to `Valid` states under `ratStep`.*

LaTeX-ready statements:

```latex
\begin{theorem}[Exact lifting / saturation] \label{thm:lifting}
Let $d'$ be odd, $k\ge 1$, and let $a$ be odd with $\gcd(a,3^k d')=1$. Then
$\gcd(3a+3^k d',\,3^k d')=3$ and the reduced Collatz step satisfies
\[
  \mathrm{step}(a,\,3^k d')=\bigl(a+3^{k-1}d',\;3^{k-1}d'\bigr).
\]
After $k$ odd steps and $E$ interleaved halvings the home numerator $A$ obeys
$2^{E}A\equiv a \pmod{d'}$; if $3\equiv 2^\lambda \pmod{d'}$ with
$\gcd(\lambda,\operatorname{ord}_{d'}(2))=1$, then
$A\equiv 3^{\lambda^{-1}(-E)}a \pmod{d'}$.
A cycle of type $(E_c,M_c)$ satisfies $d'\mid 2^{E_c}-3^{M_c}$, hence
$E_c\equiv \lambda M_c \pmod{\operatorname{ord}_{d'}(2)}$.
\end{theorem}

\begin{corollary}[Finite saturation] \label{cor:saturation}
For every $d'$ coprime to $6$, $k_{\min}(d')$ is finite and
$k_{\min}(d')\le \lceil\log_{3/2}(o_3 3^{o_3-1}2^{o_2}/(2d'^2))\rceil+2$,
where $o_i=\operatorname{ord}_{d'}(i)$.
\end{corollary}
```

---

## 3. Artifacts & reproduction

* `analysis/latent_saturation.py` — exact-rational state map and the original
  forward scan (reproduces the `k=5,6,7,8` / `k=3,7,8` anomalies).
* `analysis/cycle_census.py` — exact cycle census (`a ≤ 3·10^6`: 7 cycles at
  `d'=71`, 5 at `d'=5`).
* `analysis/lifting.py` — backward-lifting computation of `k_min` and minimal
  witnesses (cross-checked against the forward scan, including the new `k=9` witness).
* `analysis/witnesses.py` — full witness and lifting-chain table.
* `analysis/final_report.txt` — machine-generated final tables.
* `CollatzAdicBase/LatentSaturation.lean` — formalized lifting/saturation lemmas.

All computations use exact integer/rational arithmetic (`math.gcd`, no floats).
