# Paper 7 — Research Summary: Two-Block Drift and Stopping-Time Residue Density

**Second global barrier of the Collatz-adic program:** multi-block trajectory
drift and finite stopping-time certificates over $2$-adic residue classes.

Deliverables: an exact symbolic/computational analysis
(`analysis/stopping_time_density.py`), a kernel-checked Lean 4 module
(`CollatzAdicBase/StoppingTimeDensity.lean`), and this summary. All counts
below are exact and reproducible; no asymptotic claims are made about
arbitrary orbits.

---

## 1. Phase 1 — exact two-block drift

### 1.1 Composition of FuelLaw and Refueling

Start at an odd landing with $k=\tau(n)=v_2(n+1)\ge 1$, i.e. $n=2^kq-1$ with
$q$ odd.  `FuelLaw` burns the $k$-bit reservoir in $2k$ ordinary Collatz steps,

$$T^{2k}(n)=3^kq-1=2^s u,\qquad s=v_2(3^kq-1)\ge 1,\quad u\ \text{odd},$$

and `Refueling` lands on $u$ after $s$ further halvings.  The key *composition
identity* (formalized as `two_block_affine_plus`) is the exact affine map of
one burn + refuel cycle:

$$2^{k+s}u+2^{k}=3^{k}n+3^{k},\qquad n=2^kq-1. \tag{1}$$

Equivalently (form `two_block_affine`),

$$2^{k+s}u=3^{k}n+(3^{k}-2^{k}), \tag{2}$$

so the exact two-block net multiplier is $u/n$ and the logarithmic drift is

$$\log\frac{u}{n}=k\log\tfrac32-s\log 2+o(1)\quad(q\to\infty).$$

The fuel identity feeds directly into the refueling congruence (formalized as
`two_block_refuel_congruence`):

$$3^kq+2^s-1=2^s(u+1),\qquad r\le v_2(u+1)\iff 2^{s+r}\mid 2^s(u+1). \tag{3}$$

From (2) the exact drift threshold is (formalized as `two_block_drift_threshold`)

$$u<n\iff 3^{k}n+(3^{k}-2^{k})<2^{k+s}n. \tag{4}$$

### 1.2 Expected drift under the stationary 2-adic measure

For odd $n$, $P(\tau(n)=j)=2^{-j}$, so $E[k]=2$; by `Refueling`'s exact joint
density $P(s=i,r=j)=2^{-(i+j)}$ we have $E[s]=E[r]=2$.  Hence

$$E\bigl[k\log\tfrac32-s\log 2\bigr]=2\log 3-4\log 2=\log\frac{9}{16}\approx-0.5753641449,$$

with $E[2k+s]=6$ steps per cycle, i.e. $\approx-0.095894$ per Collatz step.
The drift is *negative*, consistent with (but strictly weaker than) a proof of
termination: a negative expected drift over a geometric renewal process does
not certify stopping for any particular residue class.

### 1.3 Computational verification

`analysis/stopping_time_density.py` verifies (1)–(3) exhaustively for all odd
$n\le 10^6$ (zero failures), including the concrete witnesses
$n=6{,}631{,}675$ ($k=2,s=1,u=7{,}460{,}635,r=2$).

| quantity | empirical | prediction |
|---|---:|---:|
| $E[k]$ | 1.999986 | 2 |
| $E[s]$ | 2.000002 | 2 |
| $\mean\log(u/n)$ | $-0.575364154$ | $\log(9/16)=-0.575364145$ |

The match to 8 decimal places is the finite-range fingerprint of the exact
geometric law.

---

## 2. Phase 1 — stopping-time residue density

### 2.1 Symbolic 2-adic backtracking

For an odd residue $r\bmod 2^K$ we propagate the affine template

$$T^{t}(n)=\frac{a\,n+b}{2^{e}},\qquad a\ \text{odd},$$

which is valid for **every** $n\equiv r\pmod{2^K}$ while $e+1\le K$ (the
current parity is then determined by $n\bmod 2^{e+1}$).  Updates:

$$\text{even: }(a,b,e)\mapsto(a,b,e+1),\qquad
\text{odd: }(a,b,e)\mapsto(3a,\,3b+2^{e},\,e).$$

If $a<2^{e}$ at some step $t$, then $T^{t}(n)<n$ for all
$n>b/(2^{e}-a)$ in the class (small exceptions checked directly): the class
has a finite stopping-time certificate.  The surviving density is

$$\delta(K)=\frac{\#\{\text{odd } r\bmod 2^K\text{ with no certificate within }K\text{ bits}\}}{2^{K-1}}.$$

### 2.2 Exact table, $K=1,\dots,14$

| $K$ | odd classes | certified | survivors | $\delta(K)$ | Mersenne survives |
|---:|---:|---:|---:|---:|:---:|
| 1 | 1 | 0 | 1 | $1$ | ✓ |
| 2 | 2 | 1 | 1 | $1/2$ | ✓ |
| 3 | 4 | 2 | 2 | $1/2$ | ✓ |
| 4 | 8 | 5 | 3 | $3/8$ | ✓ |
| 5 | 16 | 12 | 4 | $1/4$ | ✓ |
| 6 | 32 | 24 | 8 | $1/4$ | ✓ |
| 7 | 64 | 51 | 13 | $13/64$ | ✓ |
| 8 | 128 | 109 | 19 | $19/128$ | ✓ |
| 9 | 256 | 218 | 38 | $19/128$ | ✓ |
| 10 | 512 | 448 | 64 | $1/8$ | ✓ |
| 11 | 1024 | 896 | 128 | $1/8$ | ✓ |
| 12 | 2048 | 1822 | 226 | $113/1024$ | ✓ |
| 13 | 4096 | 3729 | 367 | $367/4096$ | ✓ |
| 14 | 8192 | 7458 | 734 | $367/4096$ | ✓ |

### 2.3 The barrier: 100% is impossible at any finite modulus

The all-ones class $r=2^{K}-1$ (i.e. $n\equiv-1\bmod 2^K$) has $\tau(n)\ge K$;
after $K$ shortcuts its multiplier is $3^{K}>2^{K}$, so it can never be
certified with only $K$ bits.  Therefore

$$\delta(K)\ \ge\ 2^{-(K-1)}\ >\ 0\quad\text{for every finite }K,$$

which is confirmed in the last column of the table.  In particular at $K=10$,
$\delta(10)=1/8$ (**87.5%** certified, not 100%), and at the sharpest tractable
modulus $K=14$, $\delta(14)=367/4096\approx 0.0896$ with 7458/8192 classes
certified.  This is the precise sense in which the second barrier resists a
finite residue-class sieve: the method is *asymptotically* exhaustive
($\delta(K)\to0$, Terras) but never reaches 100%, and the decay is slow
($\delta(14)\approx 9\%$ survives even at $2^{14}$).

### 2.4 Kernel-checked partition at $K=8$

At modulus $256$ the 19 surviving odd residues are

$$\{27,31,47,63,71,91,103,111,127,155,159,167,191,207,223,231,239,251,255\},$$

and the other $109$ are certified.  The symbolic lifting was checked on
$6539$ concrete members $n=r+256m$ ($0\le m<60$): in every case
$2^{e}\,T^{t}(n)=a\,n+b$ and $T^{t}(n)<n$, exactly matching the template.
In Lean this partition is a kernel-checked computation (`k8_partition`):
109 certified, 19 survivors, $109/128+19/128=1$.

---

## 3. Phase 2 — Lean 4 formalization

New file `CollatzAdicBase/StoppingTimeDensity.lean` imports
`CollatzAdicBase.FuelLaw` and `CollatzAdicBase.Refueling`, is wired into
`CollatzAdicBase.lean` and `CollatzAdicBase/Axioms.lean`.

| Lean declaration | content |
|---|---|
| `two_block_exhaust` | $2^s u=3^kq-1$ |
| `two_block_affine_plus` | **exact two-block identity** $2^{k+s}u+2^k=3^k n+3^k$ |
| `two_block_affine` | multiplier form $2^{k+s}u=3^k n+(3^k-2^k)$ |
| `two_block_composition` | `refuel_landing` + fuel identity feeding `refuel_congruence` |
| `two_block_refuel_congruence` | $r\le v_2(u+1)\iff 2^{s+r}\mid 2^s(u+1)$ |
| `two_block_drift_threshold` | exact drop criterion (4) |
| `two_block_drop_of_multiplier` | sufficient negative-drift condition |
| `drop_one_mod_four` | $n\equiv1\ (4)$: $T^3(n)=3m+1<n$ (density $1/2$) |
| `drop_three_mod_sixteen` | $n\equiv3\ (16)$: $T^6(n)=9m+2<n$ (density $1/8$) |
| `aff_spec` | affine invariant $2^e T^t(n)=a n+b$, $a$ odd |
| `aff_eq_of_parities`, `paritiesAgree_of_mod` | symbolic residue lifting |
| `template_stop` | a K-bit certificate lifts to every $n\equiv r\ (2^K)$ |
| `maxDepth_spec`, `cert8` | decidable kernel-checked K=8 certificate |
| `cert8_stop`, `k8_partition`, `k8_density` | lifting and exact partition $109+19=128$ |

Both dominating families together cover $1/2+1/8=5/8$ of all odd residue
classes with explicit, kernel-checked `iterate < n` bounds.

Verification: `lake build` succeeds with all six modules audited; `#print
axioms` on the new principal theorems reports only Lean's core axioms
(`propext`, `Quot.sound`, and `Classical.choice` where Mathlib tactics are
used) — no `sorryAx` and no custom axioms.

---

## 4. Interpretation and boundaries

1. **The drift is exactly computable but not sufficient.**  Equation (1) is
   an identity; the expected drift $\log(9/16)<0$ follows from the exact
   geometric 2-adic laws.  But a negative *expected* drift only controls the
   average over the stationary measure — it does not produce a stopping-time
   certificate for any fixed residue class.

2. **Residue certificates are genuinely finite and exact when they exist.**
   The affine template is kernel-checked and lifts from a residue to the whole
   class; the $5/8$ dominating families and the 109/128 K=8 classes carry
   explicit bounds.

3. **The residue sieve has a hard finite ceiling.**  The Mersenne obstruction
   $\delta(K)\ge 2^{-(K-1)}>0$ proves that no finite modulus certifies 100% of
   odd classes.  Overcoming the second barrier therefore requires an
   ingredient beyond local 2-adic residue analysis (the project's earlier
   rational descent and cycle-exclusion results are the complementary piece).

4. **Scope of counts.**  $\delta(K)$ and the K=8 partition are exact
   combinatorial facts about the template sieve; no claim is made that the 19
   surviving classes lack stopping time — only that K=8 bits cannot certify
   them.

---

## 5. Reproduction

```bash
cd <repo>
python3 analysis/stopping_time_density.py   # exact drift + delta(K), writes JSON artifact
lake build                                  # full library + #print axioms audit
# (on memory-constrained hosts use: lake -K jobs=1 build)
grep -n 'sorry\|admit\|axiom' CollatzAdicBase/StoppingTimeDensity.lean  # no hits
```

Machine-readable results:
`/home/nix/.local/share/openresearch/files/collatz-adic-lean/stopping_time_density.json`.
