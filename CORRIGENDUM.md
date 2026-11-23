# Corrigendum — "Trailing Ones and High-Altitude Backbones" (Paper 2)

## Lemma 3: the `k = 0` exceptional case, $n_0 = 3$

Lemma 3 as printed states that for $n_0 = n_{\mathrm{alt}}(0) = 3$,

$$\mathrm{collatz}^{6}(n_0) = 1 < n_0, \qquad \mathrm{collatz}^{8}(n_0) = 4 > n_0 .$$

The second equality is correct; the first is off by one. Under the step actually
used in the paper, and formalized here as

```lean
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1
```

the orbit of $3$ is

| $t$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| $\mathrm{collatz}^{t}(3)$ | 3 | 10 | 5 | 16 | 8 | 4 | **2** | **1** | 4 |

Hence

$$\mathrm{collatz}^{6}(3) = 2, \qquad \mathrm{collatz}^{7}(3) = 1 < 3, \qquad \mathrm{collatz}^{8}(3) = 4 > 3 .$$

**Corrected Lemma 3.** For $n_0 = 3$, $\mathrm{collatz}^{7}(n_0) = 1 < n_0$ and
$\mathrm{collatz}^{8}(n_0) = 4 > n_0$. Equivalently, the total stopping time of
$3$ is $7$ applications of the map, not $6$.

The qualitative claim of the printed lemma is unchanged: by step 6 the orbit has
already dropped below the start ($\mathrm{collatz}^{6}(3) = 2 < 3$). Only the
value attached to index 6 was misstated; the value $1$ occurs one step later.

## Scope

Theorem 1 (for $k \ge 1$) and Proposition 4 are unaffected. For $k \ge 1$ we have
$n_{\mathrm{alt}}(k) \ge 11$ and $G(n_{\mathrm{alt}}(k)) = 8$; the $k = 0$ case is
the isolated exception treated by Lemma 3.

## Verification

The orbit table is kernel-checked in Lean 4.36 in
`CollatzAdicBase/AlternatingGlide.lean` (`lemma_three_orbit`, `lemma_three_k_zero`).
The `#print axioms` audit reports only `propext`, `Classical.choice`, and
`Quot.sound` — no `sorryAx` and no custom axioms.

## Publication note

No v2 of Paper 2 (`collatz_integer_glide.pdf`) has been uploaded to Zenodo. The
revised PDF and this corrigendum will be issued together with Paper 3, so that
the verified Lean 4 repository can be cross-linked directly.
