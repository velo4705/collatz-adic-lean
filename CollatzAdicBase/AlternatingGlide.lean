import CollatzAdicBase.Basic
import CollatzAdicBase.FuelLaw

namespace CollatzAdicBase

namespace AlternatingGlide

/-- The alternating-bit numbers: `n_alt k = (2^(2k+3) + 1) / 3`.
    In binary these are `10 10 ... 10 11`, with `k` copies of `10`. -/
def n_alt (k : Nat) : Nat := (2 ^ (2 * k + 3) + 1) / 3

/-- `2^(2k+3) ≡ 2 (mod 3)` because `2^2 ≡ 1 (mod 3)`. -/
theorem two_pow_odd_mod_three (k : Nat) : 2 ^ (2 * k + 3) % 3 = 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hexp : 2 * (k + 1) + 3 = (2 * k + 3) + 2 := by omega
      rw [hexp, Nat.pow_add]
      have h4 : 2 ^ 2 = 4 := by decide
      rw [h4, Nat.mul_mod, ih]

/-- Divisibility needed to make `n_alt` an exact integer. -/
theorem three_dvd_alt (k : Nat) : 3 ∣ 2 ^ (2 * k + 3) + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have h := two_pow_odd_mod_three k
  omega

/-- Exact identity underlying the definition of `n_alt`. -/
theorem three_mul_n_alt (k : Nat) : 3 * n_alt k = 2 ^ (2 * k + 3) + 1 := by
  unfold n_alt
  rcases three_dvd_alt k with ⟨c, hc⟩
  rw [hc]
  omega

/-- Write `2^(2k+3) = 32 * 2^(2k-2)` (valid for `k ≥ 1`). -/
theorem pow_alt_five (k : Nat) (hk : 1 ≤ k) :
    2 ^ (2 * k + 3) = 32 * 2 ^ (2 * k - 2) := by
  have h : 2 * k + 3 = (2 * k - 2) + 5 := by omega
  rw [h, Nat.pow_add]
  have h32 : 2 ^ 5 = 32 := by decide
  rw [h32]
  ac_rfl

/-- `2^(2k+2) = 16 * 2^(2k-2)`. -/
theorem pow_alt_four (k : Nat) (hk : 1 ≤ k) :
    2 ^ (2 * k + 2) = 16 * 2 ^ (2 * k - 2) := by
  have h : 2 * k + 2 = (2 * k - 2) + 4 := by omega
  rw [h, Nat.pow_add]
  have h16 : 2 ^ 4 = 16 := by decide
  rw [h16]
  ac_rfl

/-- `2^(2k) = 4 * 2^(2k-2)`. -/
theorem pow_alt_two (k : Nat) (hk : 1 ≤ k) :
    2 ^ (2 * k) = 4 * 2 ^ (2 * k - 2) := by
  have h : 2 * k = (2 * k - 2) + 2 := by omega
  have hp : 2 ^ (2 * k) = 2 ^ ((2 * k - 2) + 2) := congrArg (fun e : Nat => 2 ^ e) h
  rw [hp, Nat.pow_add]
  have h4 : 2 ^ 2 = 4 := by decide
  rw [h4]
  ac_rfl

/-- The exact linear form of `n_alt`: with `r = 2^(2k-2)`, `3 n_alt k = 32 r + 1`. -/
theorem three_mul_n_alt_linear (k : Nat) (hk : 1 ≤ k) :
    3 * n_alt k = 32 * 2 ^ (2 * k - 2) + 1 := by
  rw [three_mul_n_alt, pow_alt_five k hk]

/-- Step 1: `collatz (n_alt k) = 32 r + 2`. -/
theorem n_alt_step1 (k : Nat) (hk : 1 ≤ k) :
    collatz (n_alt k) = 32 * 2 ^ (2 * k - 2) + 2 := by
  have h3 := three_mul_n_alt_linear k hk
  have hodd : n_alt k % 2 = 1 := by omega
  rw [FuelLaw.collatz_of_odd _ hodd]
  omega

/-- Step 2: `(32 r + 2) / 2 = 16 r + 1`. -/
theorem n_alt_step2 (k : Nat) :
    collatz (32 * 2 ^ (2 * k - 2) + 2) = 16 * 2 ^ (2 * k - 2) + 1 := by
  have heven : (32 * 2 ^ (2 * k - 2) + 2) % 2 = 0 := by omega
  rw [FuelLaw.collatz_of_even _ heven]
  omega

/-- Step 3. -/
theorem n_alt_step3 (k : Nat) :
    collatz (16 * 2 ^ (2 * k - 2) + 1) = 48 * 2 ^ (2 * k - 2) + 4 := by
  have hodd : (16 * 2 ^ (2 * k - 2) + 1) % 2 = 1 := by omega
  rw [FuelLaw.collatz_of_odd _ hodd]
  omega

/-- Step 4. -/
theorem n_alt_step4 (k : Nat) :
    collatz (48 * 2 ^ (2 * k - 2) + 4) = 24 * 2 ^ (2 * k - 2) + 2 := by
  have heven : (48 * 2 ^ (2 * k - 2) + 4) % 2 = 0 := by omega
  rw [FuelLaw.collatz_of_even _ heven]
  omega

/-- Step 5. -/
theorem n_alt_step5 (k : Nat) :
    collatz (24 * 2 ^ (2 * k - 2) + 2) = 12 * 2 ^ (2 * k - 2) + 1 := by
  have heven : (24 * 2 ^ (2 * k - 2) + 2) % 2 = 0 := by omega
  rw [FuelLaw.collatz_of_even _ heven]
  omega

/-- Step 6. -/
theorem n_alt_step6 (k : Nat) :
    collatz (12 * 2 ^ (2 * k - 2) + 1) = 36 * 2 ^ (2 * k - 2) + 4 := by
  have hodd : (12 * 2 ^ (2 * k - 2) + 1) % 2 = 1 := by omega
  rw [FuelLaw.collatz_of_odd _ hodd]
  omega

/-- Step 7. -/
theorem n_alt_step7 (k : Nat) :
    collatz (36 * 2 ^ (2 * k - 2) + 4) = 18 * 2 ^ (2 * k - 2) + 2 := by
  have heven : (36 * 2 ^ (2 * k - 2) + 4) % 2 = 0 := by omega
  rw [FuelLaw.collatz_of_even _ heven]
  omega

/-- Step 8. -/
theorem n_alt_step8 (k : Nat) :
    collatz (18 * 2 ^ (2 * k - 2) + 2) = 9 * 2 ^ (2 * k - 2) + 1 := by
  have heven : (18 * 2 ^ (2 * k - 2) + 2) % 2 = 0 := by omega
  rw [FuelLaw.collatz_of_even _ heven]
  omega

/-- Iterate table, in terms of `r = 2^(2k-2)`. -/
theorem n_alt_iterate_one (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 1 (n_alt k) = 32 * 2 ^ (2 * k - 2) + 2 := by
  simp [Nat.iterate, n_alt_step1 k hk]

theorem n_alt_iterate_two (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 2 (n_alt k) = 16 * 2 ^ (2 * k - 2) + 1 := by
  simp [Nat.iterate, n_alt_step1 k hk, n_alt_step2 k]

theorem n_alt_iterate_three (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 3 (n_alt k) = 48 * 2 ^ (2 * k - 2) + 4 := by
  simp [Nat.iterate, n_alt_step1 k hk, n_alt_step2 k, n_alt_step3 k]

theorem n_alt_iterate_four (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 4 (n_alt k) = 24 * 2 ^ (2 * k - 2) + 2 := by
  simp [Nat.iterate, n_alt_step1 k hk, n_alt_step2 k, n_alt_step3 k, n_alt_step4 k]

theorem n_alt_iterate_five (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 5 (n_alt k) = 12 * 2 ^ (2 * k - 2) + 1 := by
  simp [Nat.iterate, n_alt_step1 k hk, n_alt_step2 k, n_alt_step3 k, n_alt_step4 k,
    n_alt_step5 k]

theorem n_alt_iterate_six (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 6 (n_alt k) = 36 * 2 ^ (2 * k - 2) + 4 := by
  simp [Nat.iterate, n_alt_step1 k hk, n_alt_step2 k, n_alt_step3 k, n_alt_step4 k,
    n_alt_step5 k, n_alt_step6 k]

theorem n_alt_iterate_seven (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 7 (n_alt k) = 18 * 2 ^ (2 * k - 2) + 2 := by
  simp [Nat.iterate, n_alt_step1 k hk, n_alt_step2 k, n_alt_step3 k, n_alt_step4 k,
    n_alt_step5 k, n_alt_step6 k, n_alt_step7 k]

theorem n_alt_iterate_eight (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 8 (n_alt k) = 9 * 2 ^ (2 * k - 2) + 1 := by
  simp [Nat.iterate, n_alt_step1 k hk, n_alt_step2 k, n_alt_step3 k, n_alt_step4 k,
    n_alt_step5 k, n_alt_step6 k, n_alt_step7 k, n_alt_step8 k]

/-- Theorem 1, first equality: after two steps we reach `2^(2k+2) + 1`. -/
theorem n_alt_two_steps (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 2 (n_alt k) = 2 ^ (2 * k + 2) + 1 := by
  rw [n_alt_iterate_two k hk, pow_alt_four k hk]

/-- Theorem 1, second equality: after five steps we reach `3 * 2^(2k) + 1`. -/
theorem n_alt_five_steps (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 5 (n_alt k) = 3 * 2 ^ (2 * k) + 1 := by
  rw [n_alt_iterate_five k hk, pow_alt_two k hk]
  omega

/-- Theorem 1, third equality: after eight steps we reach `9 * 2^(2k-2) + 1`. -/
theorem n_alt_eight_steps (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 8 (n_alt k) = 9 * 2 ^ (2 * k - 2) + 1 := by
  exact n_alt_iterate_eight k hk

/-- The glide is strictly above the starting value for steps 1 through 7. -/
theorem n_alt_glide_gt (k t : Nat) (hk : 1 ≤ k) (ht1 : 1 ≤ t) (ht7 : t ≤ 7) :
    Nat.iterate collatz t (n_alt k) > n_alt k := by
  have h3 := three_mul_n_alt_linear k hk
  have hr : 1 ≤ 2 ^ (2 * k - 2) := Nat.one_le_pow _ 2 (by omega)
  have hcases : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by omega
  rcases hcases with h1 | h2 | h3' | h4 | h5 | h6 | h7
  · subst t
    rw [n_alt_iterate_one k hk]
    omega
  · subst t
    rw [n_alt_iterate_two k hk]
    omega
  · subst t
    rw [n_alt_iterate_three k hk]
    omega
  · subst t
    rw [n_alt_iterate_four k hk]
    omega
  · subst t
    rw [n_alt_iterate_five k hk]
    omega
  · subst t
    rw [n_alt_iterate_six k hk]
    omega
  · subst t
    rw [n_alt_iterate_seven k hk]
    omega

/-- At step 8 the value drops strictly below the start, so `G(n_alt k) = 8`. -/
theorem n_alt_glide_lt (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 8 (n_alt k) < n_alt k := by
  rw [n_alt_iterate_eight k hk]
  have h3 := three_mul_n_alt_linear k hk
  have hr : 1 ≤ 2 ^ (2 * k - 2) := Nat.one_le_pow _ 2 (by omega)
  omega

/-- The exact glide time: `G(n_alt k) = 8`. -/
theorem n_alt_glide_eq (k : Nat) (hk : 1 ≤ k) : GlideEq (n_alt k) 8 := by
  constructor
  · intro t ht1 ht8
    exact n_alt_glide_gt k t hk ht1 (by omega)
  · exact n_alt_glide_lt k hk

/-- Theorem 1 (Alternating-Bit Glide Quantization), combined statement. -/
theorem alternating_bit_glide (k : Nat) (hk : 1 ≤ k) :
    Nat.iterate collatz 2 (n_alt k) = 2 ^ (2 * k + 2) + 1 ∧
    Nat.iterate collatz 5 (n_alt k) = 3 * 2 ^ (2 * k) + 1 ∧
    Nat.iterate collatz 8 (n_alt k) = 9 * 2 ^ (2 * k - 2) + 1 ∧
    (∀ t, 1 ≤ t → t ≤ 7 → Nat.iterate collatz t (n_alt k) > n_alt k) ∧
    Nat.iterate collatz 8 (n_alt k) < n_alt k := by
  refine ⟨n_alt_two_steps k hk, n_alt_five_steps k hk, n_alt_eight_steps k hk, ?_,
    n_alt_glide_lt k hk⟩
  intro t ht1 ht7
  exact n_alt_glide_gt k t hk ht1 ht7

/-- Lemma 3: the `k = 0` exceptional case. `n_alt 0 = 3`. -/
theorem n_alt_zero : n_alt 0 = 3 := by
  decide

/-- The exact orbit of `3` around the first return below the start.
    Note: with the standard Collatz step, step 6 gives `2` and step 7 gives `1`;
    the paper's "`step 6 = 1`" is an off-by-one typo. -/
theorem lemma_three_orbit :
    Nat.iterate collatz 6 3 = 2 ∧
    Nat.iterate collatz 7 3 = 1 ∧
    Nat.iterate collatz 8 3 = 4 := by
  decide

/-- Lemma 3, the two inequalities: `3` first drops below itself at step 7 and
    is back above it at step 8. -/
theorem lemma_three_k_zero :
    n_alt 0 = 3 ∧
    Nat.iterate collatz 7 3 = 1 ∧ Nat.iterate collatz 7 3 < 3 ∧
    Nat.iterate collatz 8 3 = 4 ∧ Nat.iterate collatz 8 3 > 3 := by
  constructor
  · exact n_alt_zero
  · have h := lemma_three_orbit
    omega

end AlternatingGlide
end CollatzAdicBase
