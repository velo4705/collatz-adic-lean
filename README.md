# collatz-adic-lean

Formalizations of the two exact integer Collatz theorems from
"Trailing Ones and High-Altitude Backbones".

See [CORRIGENDUM.md](CORRIGENDUM.md) for the step-index correction in Lemma 3
($n_0 = 3$: the value 1 is reached at step 7, not step 6). A revised version of
Paper 2 is intentionally **not** being uploaded to Zenodo until Paper 3 is
finished, so that the verified Lean repository can be cross-linked directly.

Build with `lake build`. The project depends only on Lean's core library
(`Init`); `Nat.iterate` is given the same definition as Mathlib's.

## Files

- `CollatzAdicBase/Basic.lean` — `collatz`, `shortcut`, `Nat.iterate`.
- `CollatzAdicBase/FuelLaw.lean` — Proposition 4 (initial 2-adic fuel law).
- `CollatzAdicBase/AlternatingGlide.lean` — Theorem 1 and Lemma 3.
- `CollatzAdicBase/Axioms.lean` — `#print axioms` audit, run during `lake build`.

## Results

For `k ≥ 1, q ≥ 1` and `n = 2^k q - 1`:

- `iterate shortcut j n = 3^j 2^(k-j) q - 1` for all `j ≤ k`;
- each `j < k` value is odd and strictly smaller than the next one;
- `iterate collatz t n > n` for `1 ≤ t ≤ 2k`, and
  `iterate collatz (2k) n = 3^k q - 1`; hence
  `GlideAtLeast (2^k q - 1) (2k)` (`G(n) ≥ 2k+1`).

For `n_alt k = (2^(2k+3)+1)/3`, `k ≥ 1`:

- `3 ∣ 2^(2k+3)+1` for every `k`;
- `iterate collatz 2 (n_alt k) = 2^(2k+2)+1`;
- `iterate collatz 5 (n_alt k) = 3·2^(2k)+1`;
- `iterate collatz 8 (n_alt k) = 9·2^(2k-2)+1`;
- `iterate collatz t (n_alt k) > n_alt k` for `1 ≤ t ≤ 7`, and
  `iterate collatz 8 (n_alt k) < n_alt k`, formalized as
  `GlideEq (n_alt k) 8` (`G(n_alt k) = 8`).

## Corrigendum

The requested Lemma 3 statement "`iterate collatz 6 3 = 1`" is an off-by-one
error under the stated definition of `collatz`: the kernel-checked orbit is

`3 → 10 → 5 → 16 → 8 → 4 → 2 → 1 → 4`,

so `iterate collatz 6 3 = 2`, `iterate collatz 7 3 = 1`, and
`iterate collatz 8 3 = 4`. The formalized Lemma 3 uses the correct step 7
(and also records `iterate collatz 6 3 = 2 < 3`).
