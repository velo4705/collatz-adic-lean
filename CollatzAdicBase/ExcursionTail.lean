import CollatzAdicBase.SyracuseRenewal
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# Maximum upward excursion bounds for multi-step Syracuse trajectories (Layer 6)

For an odd start `n₀` with accelerated valuation list `as = [a₀, ..., a_{M-1}]`,
`A_j = a₀ + ... + a_{j-1}` and additive drift
`T_j = Σ_{i<j} 3^{j-1-i} 2^{A_i}`, the exact identity of `SyracuseLogDrift` is

    n_j · 2^{A_j} = 3^j · n₀ + T_j.

Dividing by `n₀ · 2^{A_j}` gives the prefix ratio bound

    n_j / n₀ ≤ 3^j / 2^{A_j} + T_j / (n₀ 2^{A_j})
             ≤ 3^j / 2^{A_j} + (3^j - 2^j) / (n₀ 2^j),

the last inequality because every `a_i ≥ 1`.

The **upward excursion event** at threshold `B > 1` is
`∃ j ≤ M, 3^j ≥ B · 2^{A_j}`, i.e. `max_j 3^j / 2^{A_j} ≥ B`.  Using the
rational tilt `x = 5/7` of `λ = 1/2` (so `x² = 25/49 > 1/2`), the envelope
`β = 26/15` with `β² > 3`, and the composition generating function
`Σ_E compCount j E · (5/14)^E ≤ (5/9)^j`, we obtain the **uniform** tail

    #{odd r mod 2^K with an excursion} · √B ≤ 26 · 2^{K-1},

independent of the trajectory horizon `M` and of the modulus `K`.  Equivalently
`P(max_j 3^j/2^{A_j} ≥ B) ≤ 26 · B^{-1/2}`.  All proofs use core Lean axioms
only: no `sorry`, no `admit`, no custom axioms.
-/

namespace CollatzAdicBase

namespace ExcursionTail

open SyracuseLogDrift
open SyracuseRenewal

-- =========================================================================
-- Section 1 -- prefix exact identity and ratio bound
-- =========================================================================

/-- Every valuation of an odd-start Syracuse trajectory is at least one. -/
lemma valSeq_pos {n : Nat} (hn : n % 2 = 1) :
    ∀ {as : List Nat}, ValSeq n as → ∀ a ∈ as, 1 ≤ a := by
  intro as hval
  induction as generalizing n with
  | nil => intro a ha; simp at ha
  | cons a as ih =>
      simp only [ValSeq] at hval
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · simpa [hval.1] using one_le_v2_three hn
      · exact ih (syracuseStep_odd n) hval.2 b hb

/-- Truncating a valuation sequence preserves `ValSeq`. -/
lemma valSeq_take (n : Nat) (as : List Nat) (j : Nat) :
    ValSeq n as → ValSeq n (as.take j) := by
  intro hval
  induction as generalizing n j with
  | nil => simp [ValSeq]
  | cons a as ih =>
      cases j with
      | zero => simp [ValSeq]
      | succ j =>
          simp only [List.take_cons, ValSeq] at hval ⊢
          exact ⟨hval.1, ih (syracuseStep n) j hval.2⟩

/-- The prefix sum `A_j` is unchanged by taking the first `j` valuations. -/
lemma syracuseA_take (as : List Nat) (j : Nat) :
    syracuseA (as.take j) j = syracuseA as j := by
  induction j generalizing as with
  | zero => cases as <;> simp [syracuseA]
  | succ j ih =>
      cases as with
      | nil => simp [syracuseA]
      | cons a as => simp [syracuseA, ih]

/-- A list of positive naturals has at least as large a sum as its length. -/
lemma length_le_sum_of_pos (l : List Nat) (h : ∀ a ∈ l, 1 ≤ a) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have ha : 1 ≤ a := h a (by simp)
      have has : ∀ b ∈ as, 1 ≤ b := by intro b hb; exact h b (by simp [hb])
      have := ih has
      simp only [List.length_cons, List.sum_cons]
      omega

/-- The exact rational ratio equality from `syracuse_identity`. -/
lemma syracuseOrbit_ratio_eq (n : Nat) (as : List Nat) (j : Nat)
    (hval : ValSeq n as) (hj : j ≤ as.length) (hnpos : 0 < n) :
    (syracuseOrbit n j : ℚ) / (n : ℚ) =
      (3 : ℚ) ^ j / (2 : ℚ) ^ syracuseA as j +
        (syracuseT (as.take j) : ℚ) /
          ((n : ℚ) * (2 : ℚ) ^ syracuseA as j) := by
  have hval' := valSeq_take n as j hval
  have hid := syracuse_identity n (as.take j) hval'
  have hlen : (as.take j).length = j := by
    simp [List.length_take, Nat.min_eq_left hj]
  have hid' : syracuseOrbit n j * 2 ^ syracuseA as j =
      3 ^ j * n + syracuseT (as.take j) := by
    simpa [hlen, syracuseA_take] using hid
  have hq : (syracuseOrbit n j : ℚ) * (2 : ℚ) ^ syracuseA as j =
      (3 : ℚ) ^ j * (n : ℚ) + (syracuseT (as.take j) : ℚ) := by
    exact_mod_cast hid'
  have hnq : (n : ℚ) ≠ 0 := by positivity
  have h2q : (2 : ℚ) ^ syracuseA as j ≠ 0 := by positivity
  field_simp [hnq, h2q]
  nlinarith [hq]

/-- The sharp envelope of the additive drift on a prefix:
    `T_j · 2^j ≤ 2^{A_j} (3^j - 2^j)`. -/
lemma syracuseT_prefix_mul_le (n : Nat) (as : List Nat) (j : Nat)
    (hn : n % 2 = 1) (hval : ValSeq n as) (hj : j ≤ as.length) :
    syracuseT (as.take j) * 2 ^ j ≤
      2 ^ syracuseA as j * (3 ^ j - 2 ^ j) := by
  have hpos : ∀ a ∈ as.take j, 1 ≤ a := fun a ha =>
    valSeq_pos hn (valSeq_take n as j hval) a ha
  have hle := syracuseT_le_tildeTmax_of_pos (as.take j) hpos
  have hlen : (as.take j).length = j := by
    simp [List.length_take, Nat.min_eq_left hj]
  have hsum : (as.take j).sum = syracuseA as j := by
    rw [← syracuseA_length (as.take j), hlen, syracuseA_take]
  have hjA : j ≤ syracuseA as j := by
    rw [← hsum]
    simpa [hlen] using length_le_sum_of_pos (as.take j) hpos
  rw [hlen, hsum] at hle
  dsimp [tildeTmax] at hle
  calc
    syracuseT (as.take j) * 2 ^ j
        ≤ 2 ^ (syracuseA as j - j) * (3 ^ j - 2 ^ j) * 2 ^ j :=
          Nat.mul_le_mul_right (2 ^ j) hle
    _ = 2 ^ (syracuseA as j - j + j) * (3 ^ j - 2 ^ j) := by
      ring
    _ = 2 ^ syracuseA as j * (3 ^ j - 2 ^ j) := by
      rw [Nat.sub_add_cancel hjA]

/-- **PREFIX RATIO BOUND.**  The exact prefix identity and the uniform
    envelope of the additive drift, in rational arithmetic. -/
theorem syracuseOrbit_ratio_le (n : Nat) (as : List Nat) (j : Nat)
    (hn : n % 2 = 1) (hval : ValSeq n as) (hj : j ≤ as.length) (hnpos : 0 < n) :
    (syracuseOrbit n j : ℚ) / (n : ℚ) ≤
        (3 : ℚ) ^ j / (2 : ℚ) ^ syracuseA as j +
          (syracuseT (as.take j) : ℚ) /
            ((n : ℚ) * (2 : ℚ) ^ syracuseA as j) ∧
    (syracuseOrbit n j : ℚ) / (n : ℚ) ≤
        (3 : ℚ) ^ j / (2 : ℚ) ^ syracuseA as j +
          (3 ^ j - 2 ^ j : Nat) / ((n : ℚ) * (2 : ℚ) ^ j) := by
  have heq := syracuseOrbit_ratio_eq n as j hval hj hnpos
  have hTnat := syracuseT_prefix_mul_le n as j hn hval hj
  have h2le3 : 2 ^ j ≤ 3 ^ j := GlideMarkovChain.two_le_three_pow j
  have hcast : ((3 ^ j - 2 ^ j : Nat) : ℚ) = (3 : ℚ) ^ j - (2 : ℚ) ^ j := by
    rw [Nat.cast_sub h2le3]
    norm_num
  have hTq : (syracuseT (as.take j) : ℚ) * (2 : ℚ) ^ j ≤
      (2 : ℚ) ^ syracuseA as j * ((3 : ℚ) ^ j - (2 : ℚ) ^ j) := by
    rw [← hcast]
    exact_mod_cast hTnat
  have hnq : 0 < (n : ℚ) := by positivity
  have h2j : 0 < (2 : ℚ) ^ j := by positivity
  have h2A : 0 < (2 : ℚ) ^ syracuseA as j := by positivity
  have hdiv : (syracuseT (as.take j) : ℚ) /
        ((n : ℚ) * (2 : ℚ) ^ syracuseA as j) ≤
      ((3 ^ j - 2 ^ j : Nat) : ℚ) / ((n : ℚ) * (2 : ℚ) ^ j) := by
    field_simp [hnq.ne', h2j.ne', h2A.ne']
    nlinarith [hTq]
  constructor
  · rw [heq]
  · rw [heq]
    nlinarith [hdiv]

-- =========================================================================
-- Section 2 -- computable valuation prefixes and the excursion set
-- =========================================================================

/-- The exact accelerated valuation list of length `M` from a starting value. -/
def valList (n : Nat) : Nat → List Nat
  | 0 => []
  | M + 1 => v2 (3 * n + 1) :: valList (syracuseStep n) M

lemma syracuseA_one (a : Nat) (as : List Nat) : syracuseA (a :: as) 1 = a := by
  cases as <;> simp [syracuseA]

lemma valList_length (n M : Nat) : (valList n M).length = M := by
  induction M generalizing n with
  | zero => rfl
  | succ M ih => simp [valList, ih]

lemma valList_ValSeq (n M : Nat) : ValSeq n (valList n M) := by
  induction M generalizing n with
  | zero => simp [valList, ValSeq]
  | succ M ih => simp [valList, ValSeq, ih]

/-- The boolean upward-excursion test on a valuation list, with `s` the
    accumulated valuation sum and `j` the current prefix length.  The
    threshold `B` is rational so the recurrence below stays closed. -/
def excursionAux (B : ℚ) (s j : Nat) : List Nat → Bool
  | [] => false
  | a :: as => decide (B * (2 : ℚ) ^ (s + a) ≤ (3 : ℚ) ^ j) ||
      excursionAux B (s + a) (j + 1) as

/-- The upward-excursion test on a whole valuation list. -/
def excursionPrefix (B : ℚ) (as : List Nat) : Bool := excursionAux B 0 1 as

/-- `excursionPrefix B as = true` iff some prefix reaches the multiplier `B`. -/
lemma excursionAux_iff (B : ℚ) (s j : Nat) : ∀ as : List Nat,
    excursionAux B s j as = true ↔
      ∃ i, i < as.length ∧
        B * (2 : ℚ) ^ (s + syracuseA as (i + 1)) ≤ (3 : ℚ) ^ (j + i) := by
  intro as
  induction as generalizing s j with
  | nil => simp [excursionAux]
  | cons a as ih =>
      constructor
      · intro h
        simp only [excursionAux, Bool.or_eq_true] at h
        rcases h with hfirst | htail
        · refine ⟨0, by simp, ?_⟩
          simpa [syracuseA_one] using (of_decide_eq_true hfirst)
        · rcases (ih (s + a) (j + 1)).1 htail with ⟨i, hi, hineq⟩
          refine ⟨i + 1, by simpa using hi, ?_⟩
          have hA : syracuseA (a :: as) (i + 1 + 1) = a + syracuseA as (i + 1) := by
            simp [syracuseA]
          have hpow : j + (i + 1) = (j + 1) + i := by omega
          rw [hA, hpow]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hineq
      · rintro ⟨i, hi, hineq⟩
        cases i with
        | zero =>
            simp only [excursionAux, Bool.or_eq_true]
            left
            apply decide_eq_true
            simpa [syracuseA_one] using hineq
        | succ i =>
            simp only [excursionAux, Bool.or_eq_true]
            right
            apply (ih (s + a) (j + 1)).2
            refine ⟨i, by simpa using hi, ?_⟩
            have hA : syracuseA (a :: as) (i + 1 + 1) = a + syracuseA as (i + 1) := by
              simp [syracuseA]
            have hpow : j + (i + 1) = (j + 1) + i := by omega
            rw [hA, hpow] at hineq
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hineq

/-- The finite-modulus upward excursion set: odd residues `r` mod `2^K` whose
    first `M` accelerated valuations have sum `< K` (so every prefix is
    determined by `r` mod `2^K`) and whose prefix ratio reaches `B`. -/
def excursionFailF (K M : Nat) (B : ℚ) : Finset (Fin (2 ^ K)) :=
  Finset.univ.filter (fun r => decide
    (r.val % 2 = 1 ∧ (valList r.val M).sum < K ∧
      excursionPrefix B (valList r.val M) = true))

/-- Membership in `excursionFailF`, unpacked. -/
lemma mem_excursionFailF {K M : Nat} {B : ℚ} {r : Fin (2 ^ K)} :
    r ∈ excursionFailF K M B ↔
      r.val % 2 = 1 ∧ (valList r.val M).sum < K ∧
        excursionPrefix B (valList r.val M) = true := by
  simp [excursionFailF]

/-- Every member of the excursion set has an explicit bad prefix. -/
lemma excursionFailF_witness {K M : Nat} {B : ℚ} {r : Fin (2 ^ K)}
    (hr : r ∈ excursionFailF K M B) :
    ∃ i, i < M ∧
      B * (2 : ℚ) ^ syracuseA (valList r.val M) (i + 1) ≤ (3 : ℚ) ^ (i + 1) := by
  rcases (mem_excursionFailF.mp hr) with ⟨_hr_odd, hsum, hbad⟩
  rcases (excursionAux_iff B 0 1 (valList r.val M)).1 hbad with ⟨i, hi, hineq⟩
  refine ⟨i, ?_, ?_⟩
  · simpa [valList_length] using hi
  · simpa [Nat.add_comm] using hineq

/-- An excursion forces the actual orbit value to reach `B · n₀` (the additive
    drift is nonnegative). -/
lemma excursionFailF_orbit_ge {K M : Nat} {B : ℚ} {r : Fin (2 ^ K)}
    (hr : r ∈ excursionFailF K M B) (hrpos : 0 < r.val) :
    ∃ i, i < M ∧ B * (r.val : ℚ) ≤ (syracuseOrbit r.val (i + 1) : ℚ) := by
  rcases excursionFailF_witness hr with ⟨i, hi, hineq⟩
  refine ⟨i, hi, ?_⟩
  let as := valList r.val M
  have hj : i + 1 ≤ as.length := by simpa [as, valList_length] using Nat.succ_le_of_lt hi
  have hid := syracuse_identity r.val (as.take (i + 1))
    (valSeq_take r.val as (i + 1) (valList_ValSeq r.val M))
  have hlen : (as.take (i + 1)).length = i + 1 := by
    simp [List.length_take, Nat.min_eq_left hj]
  have hid' : syracuseOrbit r.val (i + 1) * 2 ^ syracuseA (valList r.val M) (i + 1) =
      3 ^ (i + 1) * r.val + syracuseT (as.take (i + 1)) := by
    simpa [hlen, syracuseA_take, as] using hid
  have hq : (syracuseOrbit r.val (i + 1) : ℚ) *
        (2 : ℚ) ^ syracuseA (valList r.val M) (i + 1) =
      (3 : ℚ) ^ (i + 1) * (r.val : ℚ) + (syracuseT (as.take (i + 1)) : ℚ) := by
    exact_mod_cast hid'
  have hpowq : 0 < (2 : ℚ) ^ syracuseA (valList r.val M) (i + 1) := by positivity
  have hineq' := hineq
  field_simp at hineq' ⊢
  nlinarith [hq, show 0 ≤ (syracuseT (as.take (i + 1)) : ℚ) by positivity]

-- =========================================================================
-- Section 3 -- congruence of valuation codes and exact fiber counting
-- =========================================================================

/-- Cancelling the factor `6 = 2·3` from a congruence modulo a power of two. -/
lemma cancel_six_pow (q q' t : Nat) (ht : 1 ≤ t)
    (h : 6 * q ≡ 6 * q' [MOD 2 ^ t]) : q ≡ q' [MOD 2 ^ (t - 1)] := by
  have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
    calc
      2 ^ t = 2 ^ ((t - 1) + 1) := by congr 1; omega
      _ = 2 ^ (t - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (t - 1) := by ring
  have h2 : 2 * (3 * q) ≡ 2 * (3 * q') [MOD 2 * 2 ^ (t - 1)] := by
    have hq : 6 * q = 2 * (3 * q) := by ring
    have hq' : 6 * q' = 2 * (3 * q') := by ring
    rw [hq, hq', hpow] at h
    exact h
  have h3 : 3 * q ≡ 3 * q' [MOD 2 ^ (t - 1)] := by
    have hh := Nat.ModEq.cancel_left_div_gcd (by positivity : 0 < 2 * 2 ^ (t - 1)) h2
    simpa [Nat.gcd_mul_left] using hh
  apply Nat.ModEq.cancel_left_of_coprime
  · exact Nat.Coprime.gcd_eq_one
      (show Nat.Coprime (2 ^ (t - 1)) 3 by
        simpa using (Nat.Coprime.pow (t - 1) 1 (by decide : Nat.Coprime 2 3)))
  · simpa [Nat.mul_assoc] using h3

/-- Across the `a` halvings following an odd value of valuation `a`, the
    accelerated step of `s0 + 2^(a+1) q` is `syracuseStep s0 + 6 q`. -/
lemma lift_step_eq (a s0 q : Nat) (ha : 1 ≤ a) (hs0 : s0 < 2 ^ (a + 1))
    (hv0 : v2 (3 * s0 + 1) = a) :
    syracuseStep (s0 + 2 ^ (a + 1) * q) = syracuseStep s0 + 6 * q := by
  have hvq : v2 (3 * (s0 + 2 ^ (a + 1) * q) + 1) = a := v2_preserve_lift hs0 hv0
  have hstepq : syracuseStep (s0 + 2 ^ (a + 1) * q) * 2 ^ a =
      3 * (s0 + 2 ^ (a + 1) * q) + 1 := by
    simpa [hvq] using syracuseStep_mul_pow_v2 (s0 + 2 ^ (a + 1) * q)
  have hstep0 : syracuseStep s0 * 2 ^ a = 3 * s0 + 1 := by
    simpa [hv0] using syracuseStep_mul_pow_v2 s0
  have hrhs : (syracuseStep s0 + 6 * q) * 2 ^ a = 3 * (s0 + 2 ^ (a + 1) * q) + 1 := by
    calc
      (syracuseStep s0 + 6 * q) * 2 ^ a =
          syracuseStep s0 * 2 ^ a + 6 * q * 2 ^ a := by ring
      _ = (3 * s0 + 1) + 6 * q * 2 ^ a := by rw [hstep0]
      _ = 3 * (s0 + 2 ^ (a + 1) * q) + 1 := by rw [pow_succ]; ring
  have heq : syracuseStep (s0 + 2 ^ (a + 1) * q) * 2 ^ a =
      (syracuseStep s0 + 6 * q) * 2 ^ a := by
    rw [hstepq, hrhs]
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ a) heq

/-- An odd residue with valuation `a` decomposes uniquely as the canonical
    witness plus `2^(a+1) q`; if the residue is below `2^K` then
    `q < 2^(K-a-1)`. -/
lemma val_first_decomp {K a : Nat} (ha : 1 ≤ a) (hK : a + 1 ≤ K)
    {r : Fin (2 ^ K)} (hr : r.val % 2 = 1) (hv : v2 (3 * r.val + 1) = a) :
    ∃ q : Nat, r.val = (Classical.choose (unique_val_residue a ha)).val +
        2 ^ (a + 1) * q ∧ q < 2 ^ (K - a - 1) := by
  let s0 := Classical.choose (unique_val_residue a ha)
  have hs0lt : s0.val < 2 ^ (a + 1) := s0.isLt
  have hs0odd : s0.val % 2 = 1 := (Classical.choose_spec (unique_val_residue a ha)).1.1
  have hs0val : v2 (3 * s0.val + 1) = a := (Classical.choose_spec (unique_val_residue a ha)).1.2
  let s := r.val % 2 ^ (a + 1)
  let q := r.val / 2 ^ (a + 1)
  have hslt : s < 2 ^ (a + 1) := Nat.mod_lt _ (by positivity)
  have hdecomp : r.val = s + 2 ^ (a + 1) * q := by
    dsimp [s, q]
    conv_lhs => rw [← Nat.div_add_mod r.val (2 ^ (a + 1))]
    ring
  have hsodd : s % 2 = 1 := by
    have heven : (2 ^ (a + 1) * q) % 2 = 0 := by
      rw [Nat.mul_mod]
      have : 2 ^ (a + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
      simp [this]
    have hmod := congrArg (fun x => x % 2) hdecomp
    rw [Nat.add_mod, heven] at hmod
    norm_num at hmod
    omega
  have hsval : v2 (3 * s + 1) = a := by
    have hv' : v2 (3 * (s + 2 ^ (a + 1) * q) + 1) = a := by simpa [hdecomp] using hv
    exact v2_of_lift hslt hv'
  have hs_eq : s = s0.val := by
    exact unique_val_residue_uniq a s s0.val ha hslt hs0lt ⟨hsodd, hsval⟩ ⟨hs0odd, hs0val⟩
  have hq : q < 2 ^ (K - a - 1) := by
    have hp : 2 ^ (a + 1) * 2 ^ (K - a - 1) = 2 ^ K := by
      rw [← pow_add]
      congr 1
      omega
    have hrlt : r.val < 2 ^ (a + 1) * 2 ^ (K - a - 1) := by simpa [hp] using r.isLt
    dsimp [q]
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [mul_comm]
    exact hrlt
  refine ⟨q, ?_, hq⟩
  simpa [s0, hs_eq] using hdecomp

/-- Two odd numbers with the same valuation list of sum `E` are congruent
    modulo `2^(E+1)`. -/
lemma valSeq_modEq {n m : Nat} : ∀ as : List Nat,
    n % 2 = 1 → m % 2 = 1 → ValSeq n as → ValSeq m as →
    n ≡ m [MOD 2 ^ (as.sum + 1)] := by
  intro as hn hm hvn hvm
  induction as generalizing n m with
  | nil =>
      simp [Nat.ModEq, hn, hm]
  | cons a as ih =>
      simp only [ValSeq] at hvn hvm
      have ha : 1 ≤ a := by simpa [hvn.1] using one_le_v2_three hn
      let s0 := Classical.choose (unique_val_residue a ha)
      have hs0lt : s0.val < 2 ^ (a + 1) := s0.isLt
      have hs0odd : s0.val % 2 = 1 := (Classical.choose_spec (unique_val_residue a ha)).1.1
      have hs0val : v2 (3 * s0.val + 1) = a :=
        (Classical.choose_spec (unique_val_residue a ha)).1.2
      let qn := n / 2 ^ (a + 1)
      let qm := m / 2 ^ (a + 1)
      have hn' : n % 2 ^ (a + 1) = s0.val := by
        have hlt : n % 2 ^ (a + 1) < 2 ^ (a + 1) := Nat.mod_lt _ (by positivity)
        have hodd : (n % 2 ^ (a + 1)) % 2 = 1 := by
          have hdvd : 2 ∣ 2 ^ (a + 1) := ⟨2 ^ a, by rw [pow_succ]; ring⟩
          simpa [Nat.ModEq] using
            (Nat.ModEq.of_dvd hdvd (Nat.mod_modEq n (2 ^ (a + 1)))).trans
              (show n ≡ 1 [MOD 2] by simp [Nat.ModEq, hn])
        have hval : v2 (3 * (n % 2 ^ (a + 1)) + 1) = a := by
          have hd : n = n % 2 ^ (a + 1) + 2 ^ (a + 1) * qn := by
            dsimp [qn]
            conv_lhs => rw [← Nat.div_add_mod n (2 ^ (a + 1))]
            ring
          have hv' : v2 (3 * (n % 2 ^ (a + 1) + 2 ^ (a + 1) * qn) + 1) = a := by
            rw [← hd]
            exact hvn.1
          exact v2_of_lift hlt hv'
        exact unique_val_residue_uniq a (n % 2 ^ (a + 1)) s0.val ha hlt hs0lt
          ⟨hodd, hval⟩ ⟨hs0odd, hs0val⟩
      have hm' : m % 2 ^ (a + 1) = s0.val := by
        have hlt : m % 2 ^ (a + 1) < 2 ^ (a + 1) := Nat.mod_lt _ (by positivity)
        have hodd : (m % 2 ^ (a + 1)) % 2 = 1 := by
          have hdvd : 2 ∣ 2 ^ (a + 1) := ⟨2 ^ a, by rw [pow_succ]; ring⟩
          simpa [Nat.ModEq] using
            (Nat.ModEq.of_dvd hdvd (Nat.mod_modEq m (2 ^ (a + 1)))).trans
              (show m ≡ 1 [MOD 2] by simp [Nat.ModEq, hm])
        have hval : v2 (3 * (m % 2 ^ (a + 1)) + 1) = a := by
          have hd : m = m % 2 ^ (a + 1) + 2 ^ (a + 1) * qm := by
            dsimp [qm]
            conv_lhs => rw [← Nat.div_add_mod m (2 ^ (a + 1))]
            ring
          have hv' : v2 (3 * (m % 2 ^ (a + 1) + 2 ^ (a + 1) * qm) + 1) = a := by
            rw [← hd]
            exact hvm.1
          exact v2_of_lift hlt hv'
        exact unique_val_residue_uniq a (m % 2 ^ (a + 1)) s0.val ha hlt hs0lt
          ⟨hodd, hval⟩ ⟨hs0odd, hs0val⟩
      have hndec : n = s0.val + 2 ^ (a + 1) * qn := by
        calc
          n = n % 2 ^ (a + 1) + 2 ^ (a + 1) * (n / 2 ^ (a + 1)) := by
            conv_lhs => rw [← Nat.div_add_mod n (2 ^ (a + 1))]
            ring
          _ = s0.val + 2 ^ (a + 1) * qn := by rw [hn']
      have hmdec : m = s0.val + 2 ^ (a + 1) * qm := by
        calc
          m = m % 2 ^ (a + 1) + 2 ^ (a + 1) * (m / 2 ^ (a + 1)) := by
            conv_lhs => rw [← Nat.div_add_mod m (2 ^ (a + 1))]
            ring
          _ = s0.val + 2 ^ (a + 1) * qm := by rw [hm']
      have hstepn := lift_step_eq a s0.val qn ha hs0lt hs0val
      have hstepm := lift_step_eq a s0.val qm ha hs0lt hs0val
      have htail := ih (syracuseStep_odd n) (syracuseStep_odd m) hvn.2 hvm.2
      have htail' : 6 * qn ≡ 6 * qm [MOD 2 ^ (as.sum + 1)] := by
        rw [hndec, hmdec] at htail
        rw [hstepn, hstepm] at htail
        exact Nat.ModEq.add_left_cancel' (syracuseStep s0.val) htail
      have hq : qn ≡ qm [MOD 2 ^ as.sum] := cancel_six_pow qn qm (as.sum + 1) (by omega) htail'
      have hmul := Nat.ModEq.mul_left' (2 ^ (a + 1)) hq
      have hadd := Nat.ModEq.add_left s0.val hmul
      have hmodpow : 2 ^ (a + 1) * 2 ^ as.sum = 2 ^ (as.sum + 1 + a) := by
        rw [← pow_add]
        congr 1
        omega
      have htarget : 2 ^ ((a :: as).sum + 1) = 2 ^ (as.sum + 1 + a) := by
        congr 1
        simp
        omega
      rw [hmodpow] at hadd
      rw [htarget]
      simpa [hndec, hmdec, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadd

/-- If two odd numbers are congruent modulo `2^L` and the valuation list of
    the first has sum `E` with `E+1 ≤ L`, then their first valuation lists
    agree. -/
lemma valList_eq_of_modEq {x y L j : Nat} (hxodd : x % 2 = 1)
    (hxy : x ≡ y [MOD 2 ^ L]) (hL : (valList x j).sum + 1 ≤ L) :
    valList x j = valList y j := by
  induction j generalizing x y L with
  | zero => rfl
  | succ j ih =>
      let a := v2 (3 * x + 1)
      have ha : 1 ≤ a := by simpa [a] using one_le_v2_three hxodd
      have hsum : (valList x (j + 1)).sum = a + (valList (syracuseStep x) j).sum := by
        simp [valList, a]
      have hLa : a + 1 ≤ L := by omega
      have hmodpow_a : 2 ^ (a + 1) ∣ 2 ^ L := Nat.pow_dvd_pow 2 hLa
      have hmoda : x ≡ y [MOD 2 ^ (a + 1)] := hxy.of_dvd hmodpow_a
      have hyodd : y % 2 = 1 := by
        have hmod2 : x ≡ y [MOD 2] := hmoda.of_dvd ⟨2 ^ a, by rw [pow_succ]; ring⟩
        simpa [Nat.ModEq, hxodd] using hmod2.symm
      let s0 := Classical.choose (unique_val_residue a ha)
      have hs0lt : s0.val < 2 ^ (a + 1) := s0.isLt
      have hs0odd : s0.val % 2 = 1 := (Classical.choose_spec (unique_val_residue a ha)).1.1
      have hs0val : v2 (3 * s0.val + 1) = a :=
        (Classical.choose_spec (unique_val_residue a ha)).1.2
      have hxmod : x % 2 ^ (a + 1) = s0.val := by
        have hlt : x % 2 ^ (a + 1) < 2 ^ (a + 1) := Nat.mod_lt _ (by positivity)
        have hodd : (x % 2 ^ (a + 1)) % 2 = 1 := by
          have hdvd : 2 ∣ 2 ^ (a + 1) := ⟨2 ^ a, by rw [pow_succ]; ring⟩
          simpa [Nat.ModEq] using
            (Nat.ModEq.of_dvd hdvd (Nat.mod_modEq x (2 ^ (a + 1)))).trans
              (show x ≡ 1 [MOD 2] by simp [Nat.ModEq, hxodd])
        have hval : v2 (3 * (x % 2 ^ (a + 1)) + 1) = a := by
          have hd : x = x % 2 ^ (a + 1) + 2 ^ (a + 1) * (x / 2 ^ (a + 1)) := by
            conv_lhs => rw [← Nat.div_add_mod x (2 ^ (a + 1))]
            ring
          have hv' : v2 (3 * (x % 2 ^ (a + 1) + 2 ^ (a + 1) * (x / 2 ^ (a + 1))) + 1) = a := by
            rw [← hd]
          exact v2_of_lift hlt hv'
        exact unique_val_residue_uniq a (x % 2 ^ (a + 1)) s0.val ha hlt hs0lt
          ⟨hodd, hval⟩ ⟨hs0odd, hs0val⟩
      have hymod : y % 2 ^ (a + 1) = s0.val := by
        have hlt : y % 2 ^ (a + 1) < 2 ^ (a + 1) := Nat.mod_lt _ (by positivity)
        have hodd : (y % 2 ^ (a + 1)) % 2 = 1 := by
          have hdvd : 2 ∣ 2 ^ (a + 1) := ⟨2 ^ a, by rw [pow_succ]; ring⟩
          simpa [Nat.ModEq] using
            (Nat.ModEq.of_dvd hdvd (Nat.mod_modEq y (2 ^ (a + 1)))).trans
              (show y ≡ 1 [MOD 2] by simp [Nat.ModEq, hyodd])
        have hval : v2 (3 * (y % 2 ^ (a + 1)) + 1) = a := by
          have hymod_eq : y % 2 ^ (a + 1) = x % 2 ^ (a + 1) := hmoda.symm
          rw [hymod_eq, hxmod]
          exact hs0val
        exact unique_val_residue_uniq a (y % 2 ^ (a + 1)) s0.val ha hlt hs0lt
          ⟨hodd, hval⟩ ⟨hs0odd, hs0val⟩
      let qx := x / 2 ^ (a + 1)
      let qy := y / 2 ^ (a + 1)
      have hxdec : x = s0.val + 2 ^ (a + 1) * qx := by
        calc
          x = x % 2 ^ (a + 1) + 2 ^ (a + 1) * (x / 2 ^ (a + 1)) := by
            conv_lhs => rw [← Nat.div_add_mod x (2 ^ (a + 1))]
            ring
          _ = s0.val + 2 ^ (a + 1) * qx := by rw [hxmod]
      have hydec : y = s0.val + 2 ^ (a + 1) * qy := by
        calc
          y = y % 2 ^ (a + 1) + 2 ^ (a + 1) * (y / 2 ^ (a + 1)) := by
            conv_lhs => rw [← Nat.div_add_mod y (2 ^ (a + 1))]
            ring
          _ = s0.val + 2 ^ (a + 1) * qy := by rw [hymod]
      have hLdecomp : L = (a + 1) + (L - a - 1) := by omega
      have hq : qx ≡ qy [MOD 2 ^ (L - a - 1)] := by
        rw [hxdec, hydec] at hxy
        have hc := Nat.ModEq.add_left_cancel' s0.val hxy
        have hpow : 2 ^ L = 2 ^ (a + 1) * 2 ^ (L - a - 1) := by
          rw [← pow_add]
          congr 1
        rw [hpow] at hc
        simpa using (Nat.ModEq.mul_left_cancel' (by positivity : 2 ^ (a + 1) ≠ 0) hc)
      have hstepx := lift_step_eq a s0.val qx ha hs0lt hs0val
      have hstepy := lift_step_eq a s0.val qy ha hs0lt hs0val
      have hstepmod : syracuseStep x ≡ syracuseStep y [MOD 2 ^ (L - a)] := by
        rw [hxdec, hydec, hstepx, hstepy]
        have h6 := Nat.ModEq.mul_left' 6 hq
        have hpowdiv : 2 ^ (L - a) ∣ 6 * 2 ^ (L - a - 1) := by
          refine ⟨3, ?_⟩
          have hp : 2 ^ (L - a) = 2 ^ (L - a - 1) * 2 := by
            calc
              2 ^ (L - a) = 2 ^ ((L - a - 1) + 1) := by congr 1; omega
              _ = 2 ^ (L - a - 1) * 2 := by rw [pow_succ]
          rw [hp]
          ring
        exact (h6.add_left (syracuseStep s0.val)).of_dvd hpowdiv
      have htail : (valList (syracuseStep x) j).sum + 1 ≤ L - a := by omega
      have ih' := ih (syracuseStep_odd x) hstepmod htail
      have hvaly : v2 (3 * y + 1) = a := by
        have hv' : v2 (3 * (s0.val + 2 ^ (a + 1) * qy) + 1) = a := v2_preserve_lift hs0lt hs0val
        simpa [hydec] using hv'
      simp [valList, a, ih', hvaly]

/-- On the valuation-`a` fibre, reduction of the accelerated step modulo
    `2^(K-a)` is injective. -/
lemma oneStep_inj {K a : Nat} (ha : 1 ≤ a) (hK : a + 1 ≤ K) :
    Function.Injective
      (fun r : {r : Fin (2 ^ K) // r.val % 2 = 1 ∧ v2 (3 * r.val + 1) = a} =>
        (⟨syracuseStep r.val % 2 ^ (K - a), Nat.mod_lt _ (by positivity)⟩ :
          Fin (2 ^ (K - a)))) := by
  intro r s hrs
  let s0 := Classical.choose (unique_val_residue a ha)
  have hs0lt : s0.val < 2 ^ (a + 1) := s0.isLt
  have hs0odd : s0.val % 2 = 1 := (Classical.choose_spec (unique_val_residue a ha)).1.1
  have hs0val : v2 (3 * s0.val + 1) = a :=
    (Classical.choose_spec (unique_val_residue a ha)).1.2
  rcases val_first_decomp ha hK r.property.1 r.property.2 with ⟨qr, hrq, _⟩
  rcases val_first_decomp ha hK s.property.1 s.property.2 with ⟨qs, hsq, _⟩
  have hstepr := lift_step_eq a s0.val qr ha hs0lt hs0val
  have hsteps := lift_step_eq a s0.val qs ha hs0lt hs0val
  have hmod : syracuseStep r.val ≡ syracuseStep s.val [MOD 2 ^ (K - a)] := by
    simpa [Nat.ModEq] using congrArg Fin.val hrs
  rw [hrq, hsq, hstepr, hsteps] at hmod
  have h6 : 6 * qr ≡ 6 * qs [MOD 2 ^ (K - a)] :=
    Nat.ModEq.add_left_cancel' (syracuseStep s0.val) hmod
  have hq : qr ≡ qs [MOD 2 ^ (K - a - 1)] :=
    cancel_six_pow qr qs (K - a) (by omega) h6
  have hmul := Nat.ModEq.mul_left' (2 ^ (a + 1)) hq
  have hadd := Nat.ModEq.add_left s0.val hmul
  have hmodpow : 2 ^ (a + 1) * 2 ^ (K - a - 1) = 2 ^ K := by
    rw [← pow_add]
    congr 1
    omega
  rw [hmodpow] at hadd
  apply Subtype.ext
  apply Fin.ext
  have hs0eq : s0.val = (Classical.choose (unique_val_residue a ha)).val := rfl
  have hadd' : r.val.val ≡ s.val.val [MOD 2 ^ K] := by
    rw [hrq, hsq, ← hs0eq]
    exact hadd
  exact Nat.ModEq.eq_of_lt_of_lt hadd' r.val.isLt s.val.isLt


-- =========================================================================
-- Section 4 -- uniform power-law tail bound
-- =========================================================================

/-- Odd residue classes modulo `2^K` number exactly `2^(K-1)`. -/
lemma oddFin_card_le (K : Nat) :
    (Finset.univ.filter (fun r : Fin (2 ^ K) => decide (r.val % 2 = 1))).card ≤
      2 ^ (K - 1) := by
  let f : {r : Fin (2 ^ K) // r.val % 2 = 1} → Fin (2 ^ (K - 1)) := fun r =>
    ⟨r.val.val / 2, by
      by_cases hK : K = 0
      · subst K
        have : r.val.val = 0 := by omega
        omega
      · have hpow : 2 ^ K = 2 ^ (K - 1) * 2 := by
          calc
            2 ^ K = 2 ^ ((K - 1) + 1) := by congr 1; omega
            _ = 2 ^ (K - 1) * 2 := by rw [pow_succ]
        have hrlt : r.val.val < 2 ^ (K - 1) * 2 := by simpa [hpow] using r.val.isLt
        rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 2)]
        exact hrlt⟩
  have hinj : Function.Injective f := by
    intro r s h
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    omega
  have hcard := Fintype.card_le_of_injective f hinj
  simpa [Fintype.card_subtype] using hcard

/-- Rational certificate `sqrt 3 ≤ 26/15`. -/
lemma sqrt_three_le : Real.sqrt (3 : ℝ) ≤ (26 : ℝ) / 15 := by
  have hs := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

/-- Rational certificate `7/5 ≤ sqrt 2`. -/
lemma sqrt_two_ge : (7 : ℝ) / 5 ≤ Real.sqrt (2 : ℝ) := by
  have hs := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- Numeric certificate `(7/5)^(2a) ≤ 2^a`. -/
lemma pow_seven_five_sq_le_two (a : Nat) : (((7 : ℝ) / 5) ^ a) ^ 2 ≤ (2 : ℝ) ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
      change (((7 : ℝ) / 5) ^ a * (7 / 5)) ^ 2 ≤ (2 : ℝ) ^ a * 2
      rw [mul_pow]
      norm_num
      have hnon : 0 ≤ (((7 : ℝ) / 5) ^ a) ^ 2 := by positivity
      nlinarith [ih, hnon]

/-- The tilted threshold `B' = B 2^a / 3` satisfies
    `(15/26)(7/5)^a sqrt B ≤ sqrt B'`. -/
lemma sqrt_tilt_mul (B : ℚ) (a : Nat) (hB : 0 < B) :
    (15 : ℝ) / 26 * ((7 : ℝ) / 5) ^ a * Real.sqrt (B : ℝ) ≤
      Real.sqrt ((B * (2 : ℚ) ^ a / 3 : ℚ) : ℝ) := by
  have hBl : 0 < (B : ℝ) := by exact_mod_cast hB
  have hcast : ((B * (2 : ℚ) ^ a / 3 : ℚ) : ℝ) = (B : ℝ) * (2 : ℝ) ^ a / 3 := by
    norm_num
  have hsqB := Real.sq_sqrt (show 0 ≤ (B : ℝ) by exact_mod_cast le_of_lt hB)
  have hpow7 := pow_seven_five_sq_le_two a
  have hl_nonneg : 0 ≤ (15 : ℝ) / 26 * ((7 : ℝ) / 5) ^ a * Real.sqrt (B : ℝ) := by positivity
  have hr_nonneg : 0 ≤ Real.sqrt ((B * (2 : ℚ) ^ a / 3 : ℚ) : ℝ) := Real.sqrt_nonneg _
  -- prove by comparing squares (both sides are nonnegative)
  have hsqr := Real.sq_sqrt (show 0 ≤ (B : ℝ) * (2 : ℝ) ^ a / 3 by positivity)
  have hpow : ((49 : ℝ) / 25) ^ a ≤ (2 : ℝ) ^ a := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) a
  have hc : (225 : ℝ) / 676 * ((49 : ℝ) / 25) ^ a ≤ (2 : ℝ) ^ a / 3 := by
    nlinarith [hpow, show (225 : ℝ) * 3 ≤ 676 by norm_num]
  rw [hcast] at hr_nonneg ⊢
  have hsq_comp : ((15 : ℝ) / 26 * ((7 : ℝ) / 5) ^ a * Real.sqrt (B : ℝ)) ^ 2 ≤
      (B : ℝ) * (2 : ℝ) ^ a / 3 := by
    nlinarith [hsqr, hpow]
  nlinarith [hsq_comp, hl_nonneg, hr_nonneg]

/-- Shifting a rational threshold by one accelerated step. -/
lemma excursionAux_shift (B : ℚ) (a s j : Nat) (as : List Nat) :
    excursionAux B (s + a) (j + 1) as =
      excursionAux (B * (2 : ℚ) ^ a / 3) s j as := by
  induction as generalizing s j with
  | nil => rfl
  | cons b bs ih =>
      simp only [excursionAux]
      have hpowa : (2 : ℚ) ^ (s + a + b) = (2 : ℚ) ^ s * (2 : ℚ) ^ a * (2 : ℚ) ^ b := by
        rw [pow_add, pow_add]
      have hpowb : (2 : ℚ) ^ (s + b) = (2 : ℚ) ^ s * (2 : ℚ) ^ b := by rw [pow_add]
      have hpow3 : (3 : ℚ) ^ (j + 1) = (3 : ℚ) ^ j * 3 := by
        rw [pow_succ]
      have hprop : (B * (2 : ℚ) ^ (s + a + b) ≤ (3 : ℚ) ^ (j + 1)) ↔
          (B * (2 : ℚ) ^ a / 3 * (2 : ℚ) ^ (s + b) ≤ (3 : ℚ) ^ j) := by
        constructor <;> intro h
        · rw [hpowa, hpow3] at h
          rw [hpowb]
          field_simp
          nlinarith
        · rw [hpowb] at h
          rw [hpowa, hpow3]
          field_simp at h
          nlinarith
      have hih : excursionAux B (s + a + b) (j + 2) bs =
          excursionAux (B * (2 : ℚ) ^ a / 3) (s + b) (j + 1) bs := by
        have h0 := ih (s + b) (j + 1)
        have hidx : (s + b) + a = (s + a) + b := by omega
        rw [hidx] at h0
        simpa [Nat.add_assoc] using h0
      by_cases hp : B * (2 : ℚ) ^ (s + a + b) ≤ (3 : ℚ) ^ (j + 1)
      · have hp' := hprop.mp hp
        simp [hp, hp', hih]
      · have hp' : ¬ B * (2 : ℚ) ^ a / 3 * (2 : ℚ) ^ (s + b) ≤ (3 : ℚ) ^ j := by
          intro h; exact hp (hprop.mpr h)
        simp [hp, hp', hih]

/-- A member with first valuation `a` maps to the tail excursion set at
    modulus `K-a` and tilted threshold `B 2^a / 3`. -/
lemma excursionFailF_tail_mem {K M : Nat} {B : ℚ} {r : Fin (2 ^ K)}
    (hr : r ∈ excursionFailF K (M + 1) B) (hB : 3 ≤ B) :
    let a := v2 (3 * r.val + 1)
    let s : Fin (2 ^ (K - a)) := ⟨syracuseStep r.val % 2 ^ (K - a),
      Nat.mod_lt _ (by positivity)⟩
    s ∈ excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3) := by
  dsimp
  rcases (mem_excursionFailF.mp hr) with ⟨hrodd, hsum, hbad⟩
  let a := v2 (3 * r.val + 1)
  have ha : 1 ≤ a := by simpa [a] using one_le_v2_three hrodd
  have haK : a + 1 ≤ K := by
    have hdecomp : (valList r.val (M + 1)).sum =
        a + (valList (syracuseStep r.val) M).sum := by simp [valList, a]
    omega
  let s : Fin (2 ^ (K - a)) := ⟨syracuseStep r.val % 2 ^ (K - a),
    Nat.mod_lt _ (by positivity)⟩
  have hsmod : syracuseStep r.val ≡ s.val [MOD 2 ^ (K - a)] := by
    simpa [s, Nat.ModEq] using (Nat.mod_modEq (syracuseStep r.val) (2 ^ (K - a))).symm
  have htailpos : (valList (syracuseStep r.val) M).sum + 1 ≤ K - a := by
    have hdecomp : (valList r.val (M + 1)).sum =
        a + (valList (syracuseStep r.val) M).sum := by simp [valList, a]
    omega
  have hsodd : s.val % 2 = 1 := by
    have hdvd : 2 ∣ 2 ^ (K - a) := ⟨2 ^ (K - a - 1), by
      have hp : 2 ^ (K - a) = 2 ^ (K - a - 1) * 2 := by
        calc
          2 ^ (K - a) = 2 ^ ((K - a - 1) + 1) := by congr 1; omega
          _ = 2 ^ (K - a - 1) * 2 := by rw [pow_succ]
      rw [hp]
      ring⟩
    have hc := Nat.ModEq.of_dvd hdvd (Nat.mod_modEq (syracuseStep r.val) (2 ^ (K - a)))
    have hstepodd : syracuseStep r.val ≡ 1 [MOD 2] := by
      simpa [Nat.ModEq] using syracuseStep_odd r.val
    have := hc.trans hstepodd
    simpa [s, Nat.ModEq] using this
  have hslist : valList (syracuseStep r.val) M = valList s.val M :=
    valList_eq_of_modEq (syracuseStep_odd r.val) hsmod htailpos
  have hssum : (valList s.val M).sum < K - a := by
    rw [← hslist]
    have hdecomp : (valList r.val (M + 1)).sum =
        a + (valList (syracuseStep r.val) M).sum := by simp [valList, a]
    omega
  have hfirstfalse : ¬ B * (2 : ℚ) ^ a ≤ (3 : ℚ) := by
    intro h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ha
    rw [hk, pow_add] at h
    have hkpos : (1 : ℚ) ≤ (2 : ℚ) ^ k := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1) (by norm_num : (1 : ℚ) ≤ 2) k
      simpa using this
    nlinarith
  have hbad'' : decide (B * (2 : ℚ) ^ a ≤ (3 : ℚ)) ||
      excursionAux B a 2 (valList (syracuseStep r.val) M) = true := by
    simpa [excursionPrefix, valList, excursionAux, a] using hbad
  have htailbad : excursionAux B a 2 (valList (syracuseStep r.val) M) = true := by
    simpa [decide_eq_false_iff_not.mpr hfirstfalse] using hbad''
  have htailbad_s : excursionAux B a 2 (valList s.val M) = true := by
    rw [← hslist]
    exact htailbad
  have hsbad : excursionPrefix (B * (2 : ℚ) ^ a / 3) (valList s.val M) = true := by
    have hshift := excursionAux_shift B a 0 1 (valList s.val M)
    simp at hshift
    rw [hshift] at htailbad_s
    simpa [excursionPrefix] using htailbad_s
  exact (mem_excursionFailF.mpr ⟨hsodd, hssum, hsbad⟩)

/-- **UNIFORM POWER-LAW TAIL BOUND.**  For every horizon `M`, modulus `K`
    and threshold `B > 0`,

        #excursion classes · sqrt(B) ≤ 26 · 2^(K-1).

    Equivalently `P(max_j 3^j/2^{A_j} ≥ B) ≤ 26 / sqrt(B)`, uniformly in `M`. -/
theorem excursionFailF_tail_uniform (K M : Nat) (B : ℚ) (hB : 0 < B) :
    ((excursionFailF K M B).card : ℝ) * Real.sqrt (B : ℝ) ≤
      (26 : ℝ) * (2 : ℝ) ^ (K - 1) := by
  induction M generalizing K B with
  | zero =>
      have hempty : excursionFailF K 0 B = ∅ := by
        ext r
        simp only [excursionFailF, Finset.mem_filter, Finset.mem_univ, true_and,
          decide_eq_true_eq]
        simp [excursionPrefix, excursionAux, valList]
      simp [hempty]
  | succ M ih =>
      by_cases hBsmall : B < 3
      · have hsub : excursionFailF K (M + 1) B ⊆
            (Finset.univ.filter (fun r : Fin (2 ^ K) => decide (r.val % 2 = 1))) := by
          intro r hr
          simpa [excursionFailF] using (mem_excursionFailF.mp hr).1
        have hcard := Finset.card_le_card hsub
        have hsqrt : Real.sqrt (B : ℝ) ≤ (26 : ℝ) := by
          have hle : (B : ℝ) ≤ 3 := by exact_mod_cast le_of_lt hBsmall
          have hsqB' := Real.sq_sqrt (show 0 ≤ (B : ℝ) by exact_mod_cast le_of_lt hB)
          have hsqrtnon : 0 ≤ Real.sqrt (B : ℝ) := Real.sqrt_nonneg _
          have hsq_le : (Real.sqrt (B : ℝ)) ^ 2 ≤ (26 : ℝ) ^ 2 := by nlinarith
          have habs := sq_le_sq.mp hsq_le
          simpa [abs_of_nonneg hsqrtnon] using habs
        have hcardR : ((excursionFailF K (M + 1) B).card : ℝ) ≤
            (2 : ℝ) ^ (K - 1) := by
          exact_mod_cast (le_trans hcard (oddFin_card_le K))
        have hsqrt_nonneg : 0 ≤ Real.sqrt (B : ℝ) := Real.sqrt_nonneg _
        have hsqB := Real.sq_sqrt (show 0 ≤ (B : ℝ) by exact_mod_cast le_of_lt hB)
        have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (K - 1) := by positivity
        nlinarith
      · have hBge : (3 : ℚ) ≤ B := le_of_not_gt hBsmall
        let code : Fin (2 ^ K) → Nat × Nat := fun r =>
          (v2 (3 * r.val + 1),
           syracuseStep r.val % 2 ^ (K - v2 (3 * r.val + 1)))
        let tgt : Finset (Nat × Nat) := ((Finset.range K).filter (fun a => 0 < a)).biUnion (fun a =>
          (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).image
            (fun r => (a, r.val)))
        have hmap : ∀ r ∈ excursionFailF K (M + 1) B, code r ∈ tgt := by
          intro r hr
          rcases (mem_excursionFailF.mp hr) with ⟨hrodd, hsum, hbad⟩
          let a := v2 (3 * r.val + 1)
          have ha : 1 ≤ a := by simpa [a] using one_le_v2_three hrodd
          have haK : a < K := by
            have hdecomp : (valList r.val (M + 1)).sum =
                a + (valList (syracuseStep r.val) M).sum := by simp [valList, a]
            omega
          have hmem := excursionFailF_tail_mem (K := K) (M := M) (B := B) hr hBge
          simp only [tgt, Finset.mem_biUnion]
          refine ⟨a, by simp [haK, show 0 < a by omega], ?_⟩
          simp only [Finset.mem_image]
          refine ⟨⟨syracuseStep r.val % 2 ^ (K - a), Nat.mod_lt _ (by positivity)⟩, hmem, ?_⟩
          simp [code, a]
        have hinj : ∀ r ∈ excursionFailF K (M + 1) B,
            ∀ s ∈ excursionFailF K (M + 1) B, code r = code s → r = s := by
          intro r hr s hs hcode
          change (v2 (3 * r.val + 1), syracuseStep r.val % 2 ^ (K - v2 (3 * r.val + 1))) =
            (v2 (3 * s.val + 1), syracuseStep s.val % 2 ^ (K - v2 (3 * s.val + 1))) at hcode
          have hra : v2 (3 * r.val + 1) = v2 (3 * s.val + 1) := by
            simpa [v2] using congrArg Prod.fst hcode
          let a := v2 (3 * r.val + 1)
          have ha : 1 ≤ a := by
            have hodd := (mem_excursionFailF.mp hr).1
            simpa [a] using one_le_v2_three hodd
          have haK : a + 1 ≤ K := by
            have hsum := (mem_excursionFailF.mp hr).2.1
            have hdecomp : (valList r.val (M + 1)).sum =
                a + (valList (syracuseStep r.val) M).sum := by simp [valList, a]
            omega
          have hmod : (⟨syracuseStep r.val % 2 ^ (K - a),
              Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ (K - a))) =
              ⟨syracuseStep s.val % 2 ^ (K - a), Nat.mod_lt _ (by positivity)⟩ := by
            apply Fin.ext
            have hpair := congrArg Prod.snd hcode
            simpa [a, hra] using hpair
          let rr : {r : Fin (2 ^ K) // r.val % 2 = 1 ∧ v2 (3 * r.val + 1) = a} :=
            ⟨r, ⟨(mem_excursionFailF.mp hr).1, by simp [a]⟩⟩
          let ss : {r : Fin (2 ^ K) // r.val % 2 = 1 ∧ v2 (3 * r.val + 1) = a} :=
            ⟨s, ⟨(mem_excursionFailF.mp hs).1, by simpa [a, hra]⟩⟩
          have heq : rr = ss := (oneStep_inj ha haK) hmod
          exact congrArg Subtype.val heq
        have hcard : (excursionFailF K (M + 1) B).card ≤
            ∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
              (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card := by
          have h1 := Finset.card_le_card_of_injOn code (by simpa [Set.MapsTo] using hmap) hinj
          have h2 : tgt.card ≤ ∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
              (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card := by
            dsimp [tgt]
            calc
              (((Finset.range K).filter (fun a => 0 < a)).biUnion (fun a =>
                  (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).image
                    (fun r => (a, r.val)))).card
                  ≤ ∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
                      ((excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).image
                        (fun r => (a, r.val))).card := Finset.card_biUnion_le
              _ = ∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
                  (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card := by
                apply Finset.sum_congr rfl
                intro a ha
                exact Finset.card_image_of_injective _ (by
                  intro x y h
                  apply Fin.ext
                  exact congrArg Prod.snd h)
          exact le_trans h1 h2
        have hterm : ∀ a ∈ (Finset.range K).filter (fun a => 0 < a),
            ((excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : ℝ) *
                Real.sqrt ((B * (2 : ℚ) ^ a / 3 : ℚ) : ℝ) ≤
              (26 : ℝ) * (2 : ℝ) ^ (K - a - 1) := by
          intro a ha
          exact ih (K - a) (B * (2 : ℚ) ^ a / 3) (by positivity)
        have hsum : ((∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
            (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : Nat) : ℝ) *
              Real.sqrt (B : ℝ) ≤ (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 27) := by
          -- bound each summand using sqrt_tilt_mul and tilt_sqrt_bound
          have hsqrtBpos : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hB)
          have h_each : ∀ a ∈ (Finset.range K).filter (fun a => 0 < a),
              ((excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : ℝ) *
                  Real.sqrt (B : ℝ) ≤
                (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 15) *
                  ((5 : ℝ) / 14) ^ a := by
            intro a ha
            have ht := hterm a ha
            have htilt := sqrt_tilt_mul B a hB
            have hsqpos : 0 < Real.sqrt ((B * (2 : ℚ) ^ a / 3 : ℚ) : ℝ) := by positivity
            have hc_nonneg : (0 : ℝ) ≤ (excursionFailF (K - a) M
                (B * (2 : ℚ) ^ a / 3)).card := by positivity
            have hle1 := mul_le_mul_of_nonneg_left htilt hc_nonneg
            have hpow : (2 : ℝ) ^ (K - a - 1) * (26 : ℝ) / ((15 : ℝ) / 26 * ((7 : ℝ) / 5) ^ a) =
                (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 15) * ((5 : ℝ) / 14) ^ a := by
              have hK : a < K := (Finset.mem_filter.mp ha).1 |> Finset.mem_range.mp
              have hpoweq : (2 : ℝ) ^ (K - 1) = (2 : ℝ) ^ (K - a - 1) * (2 : ℝ) ^ a := by
                rw [← pow_add]
                congr 1
                omega
              rw [hpoweq]
              field_simp
              rw [← mul_pow, ← mul_pow]
              norm_num
            let c : ℝ := (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card
            let sp : ℝ := Real.sqrt ((B * (2 : ℚ) ^ a / 3 : ℚ) : ℝ)
            let k : ℝ := (15 : ℝ) / 26 * ((7 : ℝ) / 5) ^ a
            let R : ℝ := (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 15) * ((5 : ℝ) / 14) ^ a
            have hkpos : 0 < k := by dsimp [k]; positivity
            have hmul1 : k * (c * Real.sqrt (B : ℝ)) ≤ c * sp := by
              dsimp [c, sp, k]
              nlinarith [hle1]
            have hmul2 : k * (c * Real.sqrt (B : ℝ)) ≤ (26 : ℝ) * (2 : ℝ) ^ (K - a - 1) := by
              exact le_trans hmul1 ht
            have hpow' : (26 : ℝ) * (2 : ℝ) ^ (K - a - 1) = k * R := by
              have hp := hpow
              dsimp [k, R]
              field_simp [ne_of_gt hkpos] at hp
              nlinarith [hp]
            have hmul3 : k * (c * Real.sqrt (B : ℝ)) ≤ k * R := by
              rwa [hpow'] at hmul2
            have hfinal : c * Real.sqrt (B : ℝ) ≤ R := le_of_mul_le_mul_left hmul3 hkpos
            dsimp [c, R] at hfinal
            exact hfinal
          have hsum_each := Finset.sum_le_sum h_each
          have hgeom : (∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
              (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 15) * ((5 : ℝ) / 14) ^ a) ≤
              (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 15) * ((5 : ℝ) / 9) := by
            rw [← Finset.mul_sum]
            have hgeom0 : (∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
                ((5 : ℝ) / 14) ^ a) ≤ (5 : ℝ) / 9 := by
              have hge := geom_sum_eq (show (5 : ℝ) / 14 ≠ 1 by norm_num) K
              have hpow_le : ((5 : ℝ) / 14) ^ K ≤ 1 := by
                exact pow_le_one₀ (by norm_num) (by norm_num)
              have hfull : (∑ a ∈ Finset.range K, ((5 : ℝ) / 14) ^ a) ≤ (14 : ℝ) / 9 := by
                have hpow_nonneg : 0 ≤ ((5 : ℝ) / 14) ^ K := by positivity
                rw [hge, show (5 : ℝ) / 14 - 1 = -9 / 14 by norm_num]
                field_simp
                nlinarith
              by_cases hK0 : K = 0
              · subst K
                norm_num
              · have hsplit : (∑ a ∈ Finset.range K, ((5 : ℝ) / 14) ^ a) =
                    1 + ∑ a ∈ (Finset.range K).filter (fun a => 0 < a), ((5 : ℝ) / 14) ^ a := by
                  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range K)
                    (p := fun a => 0 < a)]
                  have hnot : (Finset.range K).filter (fun a => ¬ 0 < a) = {0} := by
                    ext a
                    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
                    constructor
                    · intro h; omega
                    · intro h; subst a; exact ⟨by omega, by omega⟩
                  rw [hnot]
                  simp
                  ac_rfl
                rw [hsplit] at hfull
                nlinarith [hfull]
            have hcoef : 0 ≤ (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 15) := by positivity
            nlinarith [hgeom0, hcoef]
          -- combine
          have hcardR' : ((excursionFailF K (M + 1) B).card : ℝ) ≤
              (∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
                (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : ℝ) := by
            exact_mod_cast hcard
          have hsumcast : ((∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
              (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : Nat) : ℝ) =
              ∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
                ((excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : ℝ) := by
            simp
          have hmul : ((excursionFailF K (M + 1) B).card : ℝ) * Real.sqrt (B : ℝ) ≤
              (∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
                ((excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : ℝ)) *
                  Real.sqrt (B : ℝ) := by
            gcongr
          have hsum_le : (∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
                ((excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : ℝ)) *
                  Real.sqrt (B : ℝ) ≤
              (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 15) * ((5 : ℝ) / 9) := by
            have htmp : (∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
                ((excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : ℝ) *
                  Real.sqrt (B : ℝ)) ≤
              ∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
                (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 15) * ((5 : ℝ) / 14) ^ a :=
              Finset.sum_le_sum h_each
            rw [← Finset.sum_mul] at htmp
            have hcoef : 0 ≤ (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 15) := by positivity
            nlinarith [htmp, hgeom, hcoef]
          have hconst : (26 : ℝ) / 15 * ((5 : ℝ) / 9) = (26 : ℝ) / 27 := by norm_num
          have hfactor : (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 27) ≤
              (26 : ℝ) * (2 : ℝ) ^ (K - 1) := by
            have hp : (0 : ℝ) ≤ (26 : ℝ) * (2 : ℝ) ^ (K - 1) := by positivity
            nlinarith
          nlinarith [hconst, hsum_le, hmul, hfactor]

        have hcardR : ((excursionFailF K (M + 1) B).card : ℝ) ≤
            (∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
              (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : ℝ) := by
          exact_mod_cast hcard
        have hsqrtnon : 0 ≤ Real.sqrt (B : ℝ) := Real.sqrt_nonneg _
        have hmulR : ((excursionFailF K (M + 1) B).card : ℝ) * Real.sqrt (B : ℝ) ≤
            ((∑ a ∈ (Finset.range K).filter (fun a => 0 < a),
              (excursionFailF (K - a) M (B * (2 : ℚ) ^ a / 3)).card : Nat) : ℝ) *
                Real.sqrt (B : ℝ) := by
          gcongr
        have hfactor : (26 : ℝ) * (2 : ℝ) ^ (K - 1) * ((26 : ℝ) / 27) ≤
            (26 : ℝ) * (2 : ℝ) ^ (K - 1) := by
          have hp : (0 : ℝ) ≤ (26 : ℝ) * (2 : ℝ) ^ (K - 1) := by positivity
          nlinarith
        nlinarith [hmulR, hsum, hfactor]

#print axioms syracuseOrbit_ratio_le
#print axioms excursionFailF
#print axioms excursionFailF_orbit_ge
#print axioms oneStep_inj
#print axioms valList_eq_of_modEq
#print axioms excursionFailF_tail_uniform

end ExcursionTail
end CollatzAdicBase
