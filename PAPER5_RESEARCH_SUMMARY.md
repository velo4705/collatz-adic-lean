# Paper 5 — Research Summary: The Mid-Flight Refueling Congruence

**Investigation of the open phenomenon in Section 6 of Paper 2,
"Trailing Ones and High-Altitude Backbones":** why trajectories that start
with only $\tau(n)=2$ trailing ones (e.g. $n=6{,}631{,}675$) acquire
$\tau=18$ mid-flight and funnel onto 97 shared high-altitude backbones.

Deliverables: a Python 2-adic analysis (`analysis/refueling.py`), a
kernel-checked Lean 4 formalization (`CollatzAdicBase/Refueling.lean`), and
this summary. All numbers below are exact; the sweep claims were recomputed
from cached top-500 records, not assumed from Paper 2.

---

## 1. The exact mechanism

### 1.1 Notation

$T(m)=m/2$ for even $m$, $T(m)=3m+1$ for odd $m$;
$\varphi(m)=(3m+1)/2$ is the odd *shortcut*;
$\tau(m)=v_2(m+1)$ is the number of trailing 1-bits of an odd $m$;
$v_2$ is the 2-adic valuation.

Start at an odd landing $n$ with $k=\tau(n)\ge 1$ and write
$n=2^k q-1$ with $q$ **odd** (forced by $v_2(n+1)=k$). Paper 2's fuel law
gives $\varphi^j(n)=3^j2^{k-j}q-1$ for $0\le j\le k$, so after $2k$ ordinary
Collatz steps the $k$-bit reservoir is exhausted:

$$\varphi^k(n)=3^k q-1,\qquad \tau(3^k q-1)=v_2(3^k q)=0 .$$

Because $3^k q$ is odd, $3^k q-1$ is even; write its exact 2-adic content as

$$3^k q-1=2^s u,\qquad\text{equivalently}\qquad 3^k q=2^s u+1,
\qquad u\ \text{odd},\quad s=v_2(3^k q-1)\ge 1 .$$

Then $s$ further halvings reach the **next odd landing**

$$T^{\,2k+s}(n)=u=\frac{3^k q-1}{2^s},\qquad \tau(u)=v_2(u+1)=r .$$

### 1.2 Main congruence (LaTeX-ready)

> **Lemma 1 (fuel exhaustion).** For $k\ge1$ and odd $q$,
> $\varphi^k(2^k q-1)=3^k q-1$ and $\tau(3^k q-1)=0$.

> **Lemma 2 (odd landing).** Let $k\ge1$, $q$ odd, and
> $3^k q=2^s u+1$ with $u$ odd, $s\ge1$. Then $v_2(3^k q-1)=s$ and
> $T^{2k+s}(2^k q-1)=u$.

> **Theorem 1 (mid-flight refueling congruence).** *In the notation above,
> for every $r\ge1$,*
> $$
>   \tau(u)=v_2(u+1)\ \ge\ r
>   \quad\Longleftrightarrow\quad
>   3^k q \equiv 1-2^s \pmod{2^{\,s+r}}
>   \quad\Longleftrightarrow\quad
>   2^{\,s+r}\mid 3^k q+2^s-1 .
> $$
> *Proof.* $3^k q+2^s-1=2^s(u+1)$; cancel the positive factor $2^s$ using
> $2^{s+r}=2^s2^r$ and $2^r\mid u+1\iff r\le v_2(u+1)$. $\square$

> **Corollary 1 (explicit residue class).** Since $3^k$ is odd it is
> invertible modulo $2^m$ ($m=s+r$). Hence the criterion singles out exactly
> one odd residue class:
> $$
>   q\equiv c_{k,s,r}:=(1-2^s)(3^k)^{-1}\pmod{2^{\,s+r}},
> $$
> represented in $\mathbb N$ by
> $c_{k,s,r}=\bigl(2^{s+r}+1-2^s\bigr)\,(3^k)^{-1}\bmod 2^{s+r}$.
> Conversely, if $q$ lies in this class then $v_2(3^k q-1)=s$ automatically,
> because $1-2^s\equiv1\pmod{2^s}$ but $\not\equiv1\pmod{2^{s+1}}$.

> **Corollary 2 (density).** At a random odd landing the exact event
> $(s,r)$ has probability $2^{-(s+r)}$ (one residue class modulo
> $2^{s+r}$), so $\Pr[\tau(u)=r]=2^{-r}$ marginally. High refuels are rare
> but not exceptional: reaching $r=18$ with $s=1$ requires membership in one
> class modulo $2^{19}$ (probability $2^{-19}$).

Theorem 1 is the *exact congruence criterion determining when a trajectory
refills its trailing-ones reservoir by $r$ bits immediately after exhausting
an initial $k$-bit fuel block*. Applying it afresh at **every** odd landing
explains all "mid-flight" refuels — the initial $\tau(n)$ only sets the length
of the *first* block.

---

## 2. Phase 1 — computational verification

Script: `analysis/refueling.py` (Python 3, exact integer arithmetic, runtime
$\approx 10$ s). It computes $k,q,s,u,r$, checks
$2^{s+r}\mid 3^kq+2^s-1$, checks failure at $2^{s+r+1}$, checks the explicit
residue $q\bmod 2^{s+r}=c_{k,s,r}$, and checks the closed-form landing.

### 2.1 Exhaustive check over all odd $n\le 10^7$

| quantity | value |
|---|---|
| odd integers checked | **5,000,000** |
| criterion / residue / landing failures | **0** |
| even $n$ | reduced to odd part $n/2^{v_2(n)}$ (same criterion) |

### 2.2 Distribution of the immediate refuel amount $r$ (odd $n\le10^7$)

| $r$ | observed | $10^7/2^{r+1}$ | ratio |
|---:|---:|---:|---:|
| 1 | 2,500,013 | 2,500,000 | 1.0000 |
| 2 | 1,249,989 | 1,250,000 | 1.0000 |
| 3 | 625,000 | 625,000 | 1.0000 |
| 4 | 312,492 | 312,500 | 1.0000 |
| 5 | 156,268 | 156,250 | 1.0000 |
| 6 | 78,122 | 78,125 | 1.0000 |
| 7 | 39,075 | 39,062.5 | 1.0003 |
| 8 | 19,522 | 19,531.25 | 0.9995 |
| 9 | 9,755 | 9,765.6 | 0.9989 |
| 10 | 4,877 | 4,882.8 | 0.9988 |
| 11 | 2,450 | 2,441.4 | 1.0035 |
| 12 | 1,221 | 1,220.7 | 1.0002 |
| 13 | 609 | 610.4 | 0.9977 |
| 18 | 18 | 19.1 | 0.94 |

Joint density $P(s,r)=2^{-(s+r)}$, sample:

| $(s,r)$ | observed | expected $5\cdot10^6/2^{s+r}$ | ratio |
|---|---:|---:|---:|
| (1,1) | 1,250,005 | 1,250,000 | 1.0000 |
| (1,5) | 78,125 | 78,125 | 1.0000 |
| (1,10) | 2,437 | 2,441.4 | 0.9982 |
| (2,1) | 624,999 | 625,000 | 1.0000 |
| (2,10) | 1,221 | 1,220.7 | 1.0002 |

This is the finite-range fingerprint of Corollary 2 and explains Paper 2's
"enrichment $\approx 2\times$ per trailing one": a long fuel block is valuable
precisely because it is a rare residue class at the *previous* landing.

### 2.3 The rank-1 record $n=6{,}631{,}675$

$\tau(n)=2$, so $n=2^2\cdot1{,}657{,}919-1$ ($q=1{,}657{,}919$ odd).
First burn: $\varphi^2(n)=3^2q-1=14{,}921{,}270=2^1\cdot7{,}460{,}635$
(equivalently $3^2q=2^1\cdot7{,}460{,}635+1$),
so $s=1$, $u=7{,}460{,}635$, and
$2^{1+2}\mid 3^2q+2^1-1$ with $q\equiv7\bmod 8$ — a **small** refuel ($r=2$).
The large reservoir is earned later. Exact trajectory events:

| step $t$ of odd landing | odd value $m$ | $k=\tau(m)$ | $q$ | $s$ | refuel landing $u$ | $r$ | modulus $2^{s+r}$ | $q\bmod 2^{s+r}$ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 6,631,675 | 2 | 1,657,919 | 1 | 7,460,635 | 2 | $2^3$ | 7 |
| 5 | 7,460,635 | 2 | 1,865,159 | 1 | 8,393,215 | **9** | $2^{10}$ | 455 |
| 10 | 8,393,215 | 9 | 16,393 | 1 | 161,331,709 | 1 | $2^2$ | 1 |
| 33 | 60,499,391 | 6 | 945,303 | 1 | 344,562,943 | **8** | $2^9$ | 151 |
| 105 | 2,832,232,063 | 7 | 22,126,813 | 1 | 24,195,670,015 | **13** | $2^{14}$ | 8,413 |

The maximum trailing-ones reached on this trajectory is $\tau=13$, exactly as
Paper 2 reports (mid-flight, not at $t=0$). Note that the first two landing
values are themselves records: **the rank-1, rank-2 and rank-3 seeds
$6{,}631{,}675\to7{,}460{,}635\to8{,}393{,}215$ are consecutive refuel
landings of one trajectory** — a direct, exact explanation of why the top
records share a backbone.

### 2.4 The $\tau=18$ refuel (ranks 19, 38, 45)

All three records pass through the odd value $m=43{,}841{,}695$. At that
landing $k=\tau(m)=5$, $q=1{,}370{,}053$, and

$$3^5q-1=2^1\cdot166{,}461{,}439\ \ (3^5q=2^1\cdot166{,}461{,}439+1),
\qquad 2^{19}\mid 3^5q+2^1-1,\qquad
q\equiv321{,}477\pmod{2^{19}},$$

forcing the next odd landing $u=166{,}461{,}439$ to have $\tau(u)=18$.
Kernel check: $3^5\cdot1{,}370{,}053\bmod 2^{19}=524{,}287=2^{19}-1$.

| rank | seed $n$ | step of $m$ | shared $m$ | $k$ | $q$ | $s$ | $u$ | $r$ | $q\bmod2^{19}$ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 19 | 3,041,127 | 22 | 43,841,695 | 5 | 1,370,053 | 1 | 166,461,439 | 18 | 321,477 |
| 38 | 4,561,691 | 20 | 43,841,695 | 5 | 1,370,053 | 1 | 166,461,439 | 18 | 321,477 |
| 45 | 5,131,903 | 15 | 43,841,695 | 5 | 1,370,053 | 1 | 166,461,439 | 18 | 321,477 |

Moreover ranks 19, 38 and 45 *merge earlier still*: $3{,}041{,}127$ and
$4{,}561{,}691$ each refuel directly into $5{,}131{,}903$ (with $r=7$), which
then refuels into $43{,}841{,}695$ — the backbone is a chain of congruent
refuel landings.

### 2.5 Backbone clustering (recomputed from the top-500 CSV)

| quantity | recomputed value | Paper 2 |
|---|---:|---:|
| records traced | 500 | 500 |
| threshold for shared values | $10^9$ | $10^9$ |
| distinct backbones (shared-value components) | **97** | 97 |
| distinct exact apex values | **97** | — |
| multi-record apex groups | 61 | — |
| records sharing an apex with another | **464** | 464 |
| rank-1 backbone size | **5** (ranks 1–5) | 5 |

Largest exact-apex groups reproduced: 28 records at apex $24{,}648{,}077{,}896$
and $156{,}914{,}378{,}224$; 24 at $352{,}617{,}812{,}944$; 23 at
$90{,}239{,}155{,}648$; 20 at $139{,}646{,}736{,}808$; 19 at
$151{,}629{,}574{,}372$ and $294{,}475{,}592{,}320$; 17 at
$17{,}202{,}377{,}752$; 5 at the rank-1 apex $60{,}342{,}610{,}919{,}632$.

---

## 3. Why the phenomenon occurs

1. **$\tau$ is not carried, it is manufactured.** The fuel law only bounds the
   *first* $2k$ steps. At the end of every fuel block the value
   $3^kq-1$ has $\tau=0$ (Lemma 1); the *next* reservoir size is dictated
   solely by which residue class mod $2^{s+r}$ the odd core $q$ occupies
   (Theorem 1). Starting with $\tau=2$ therefore says nothing about later
   maxima — it merely makes the first block short.

2. **Large refuels are rare but exact.** By Corollary 2 the event "refuel by
   $r$ with valuation shift $s$" occupies one class mod $2^{s+r}$. Over
   hundreds of odd landings per record, a top-500 set will sample such rare
   classes; $\tau=18$ is the largest that occurs in this range, and all three
   instances are the *same* congruence event at the *same* odd value
   $43{,}841{,}695$ (§2.4).

3. **Backbones are chains of refuel landings.** When two trajectories land on
   the same odd value (e.g. ranks 1–3, or ranks 19/38 → 45), all downstream
   refuel congruences coincide, so they share every subsequent apex. The
   97 backbones and the 464/500 apex-sharing records are the large-number
   consequence of this deterministic coalescence; the rank-1 chain
   $6{,}631{,}675\to7{,}460{,}635\to8{,}393{,}215$ exhibits it in miniature.

4. **Boundary of the claim.** Theorem 1 is exact and universal for odd
   landings. The counts (97, 464, 500, the $\tau=18$ maximum) are exhaustive
   measurements for $n\le10^7$ / top-500 records only; no asymptotic
   statement about arbitrary orbits is made.

---

## 4. Phase 2 — Lean 4 formalization

New file `CollatzAdicBase/Refueling.lean` (imports `CollatzAdicBase.FuelLaw`,
core `Init` only, 251 lines). Wired into `CollatzAdicBase.lean` and
`CollatzAdicBase/Axioms.lean`.

| Lean declaration | content |
|---|---|
| `v2`, `v2_of_odd`, `v2_of_even`, `v2_two_pow_mul` | 2-adic valuation |
| `two_pow_dvd_iff_le_v2` | $2^r\mid n\iff r\le v_2(n)$ |
| `three_pow_odd`, `fuel_exhausted` | Lemma 1 (odd successor ⇒ $\tau=0$) |
| `iterate_collatz_halve_pow` | $T^s(2^su)=u$ |
| `refuel_landing` | $T^{2k+s}(2^kq-1)=u$ (Lemma 2) |
| `refuel_exhausts_fuel` | $v_2(3^kq-1)=s$ |
| `refuel_divisibility_shift` | $2^{s+r}\mid3^kq+2^s-1\iff2^r\mid u+1$ |
| **`refuel_congruence`** | **Theorem 1: $r\le v_2(u+1)\iff2^{s+r}\mid3^kq+2^s-1$** |
| `refuel_mod_invariant` | criterion depends only on $q\bmod 2^{s+r}$ |
| 5 concrete `example`s | kernel checks of §2.3/§2.4 witnesses |

Verification:

```
$ lake build          # Build completed successfully (16 jobs).
```

`#print axioms` for all five new principal theorems reports exactly
`[propext, Quot.sound]` — the same core axioms as the pre-existing library.
No `sorry`, no `admit`, no custom axioms. (The pre-existing
`AlternatingGlide.lemma_three_k_zero` additionally reports
`Classical.choice`, as before.)

---

## 5. Reproduction

```bash
cd <repo>
python3 analysis/refueling.py       # ~10 s; writes refueling_analysis.json artifact
lake build                          # full library + #print axioms audit
grep -n 'sorry\|admit\|axiom' CollatzAdicBase/Refueling.lean   # no hits
```

Machine-readable results:
`/home/nix/.local/share/openresearch/files/collatz-adic-lean/refueling_analysis.json`.
This summary is also copied there as `PAPER5_RESEARCH_SUMMARY.md`.
