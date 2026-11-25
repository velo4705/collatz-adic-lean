import CollatzAdicBase.GlideMarkovChain
import CollatzAdicBase.CycleExclusion
import Mathlib.Data.Nat.PadicValNat
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# Accelerated Syracuse dynamics and continued-fraction cycle bounds (Paper 9)

For odd positive `n` the accelerated odd-to-odd Syracuse step is

    T_syr(n) = (3*n+1) / 2^{v2(3*n+1)},     a = v2(3*n+1) >= 1.

We formalize:

* `syracuseStep` and the exact step equation `syracuseStep n * 2^a = 3*n+1`;
* the exact `M`-step identity
    `n_M * 2^{A_M} = 3^M n_0 + sum_{j<M} 3^{M-1-j} 2^{A_j}`, `A_j = sum_{i<j} a_i`;
* the geometric valuation law: the exact number of odd residues mod `2^K` with
  `v2(3n+1) = a` is `2^{K-a-1}` for `1 <= a < K`;
* the cycle minimum bound `n_min * (2^E - 3^M) <= T_max(M,E)` with
  `T_max(M,E) = 2^{E-M} (3^M - 2^M)`, linking the Diophantine gap `2^E - 3^M`
  to cycle size.

All theorems use core Lean axioms only: no `sorry`, no `admit`, no custom axioms.
-/

namespace CollatzAdicBase

namespace SyracuseLogDrift

-- =========================================================================
-- Section 1 -- the 2-adic valuation and the accelerated Syracuse step
-- =========================================================================

/-- The 2-adic valuation `v2(n)` is `padicValNat 2 n`, the exponent of the
    largest power of two dividing `n`. -/
def v2 (n : Nat) : Nat := padicValNat 2 n

lemma v2_eq_multiplicity (n : Nat) : v2 n = multiplicity 2 n := by
  unfold v2
  exact Nat.padicValNat_def

/-- `2^{v2(n)}` divides `n`. -/
lemma v2_dvd (n : Nat) : 2 ^ v2 n ∣ n := by
  refine ⟨Nat.divMaxPow n 2, ?_⟩
  rw [mul_comm]
  unfold v2
  exact (Nat.divMaxPow_mul_pow_padicValNat 2 n).symm

/-- The next power does not divide a nonzero `n`. -/
lemma not_succ_v2_dvd {n : Nat} (hn : n ≠ 0) : ¬ 2 ^ (v2 n + 1) ∣ n := by
  intro h
  have hle : v2 n + 1 ≤ multiplicity 2 n :=
    (Nat.pow_dvd_iff_le_multiplicity (by norm_num) hn).mp h
  rw [v2_eq_multiplicity] at hle
  omega

/-- Characterization of exact valuation: `v2(n) = a` iff `2^a || n`. -/
lemma v2_eq_iff {a n : Nat} (hn : n ≠ 0) :
    v2 n = a ↔ 2 ^ a ∣ n ∧ ¬ 2 ^ (a + 1) ∣ n := by
  constructor
  · intro h
    subst a
    exact ⟨v2_dvd n, not_succ_v2_dvd hn⟩
  · intro h
    have hle : a ≤ v2 n := by
      rw [v2_eq_multiplicity]
      exact (Nat.pow_dvd_iff_le_multiplicity (by norm_num) hn).mp h.1
    have hge : v2 n ≤ a := by
      by_contra hnot
      have hsucc : a + 1 ≤ v2 n := by omega
      rw [v2_eq_multiplicity] at hsucc
      exact h.2 ((Nat.pow_dvd_iff_le_multiplicity (by norm_num) hn).mpr hsucc)
    omega

/-- The accelerated odd-to-odd Syracuse step.  `Nat.divMaxPow m 2` removes
    every factor of two from `m = 3n+1`, so the result is again odd. -/
def syracuseStep (n : Nat) : Nat := Nat.divMaxPow (3 * n + 1) 2

/-- **Exact step equation:** `T_syr(n) * 2^{v2(3n+1)} = 3n+1`. -/
lemma syracuseStep_mul_pow_v2 (n : Nat) :
    syracuseStep n * 2 ^ v2 (3 * n + 1) = 3 * n + 1 := by
  unfold syracuseStep v2
  exact Nat.divMaxPow_mul_pow_padicValNat 2 (3 * n + 1)

/-- The Syracuse step is odd (the maximal power of two has been removed). -/
lemma syracuseStep_odd (n : Nat) : syracuseStep n % 2 = 1 := by
  unfold syracuseStep
  have hnd : ¬ 2 ∣ Nat.divMaxPow (3 * n + 1) 2 :=
    Nat.not_dvd_divMaxPow (by norm_num : 1 < 2) (by omega : 3 * n + 1 ≠ 0)
  by_contra h
  have hmod : Nat.divMaxPow (3 * n + 1) 2 % 2 = 0 := by omega
  exact hnd (Nat.dvd_iff_mod_eq_zero.mpr hmod)

/-- For odd `n`, the valuation `a = v2(3n+1)` is at least one. -/
lemma one_le_v2_three {n : Nat} (hn : n % 2 = 1) : 1 ≤ v2 (3 * n + 1) := by
  rw [v2_eq_multiplicity]
  have hp : 2 ∣ 3 * n + 1 := by omega
  exact (Nat.pow_dvd_iff_le_multiplicity (by norm_num) (by omega)).mp hp

-- =========================================================================
-- Section 2 -- exact M-step trajectory identity
-- =========================================================================

/-- `ValSeq n as`: the list `as` is exactly the sequence of Syracuse valuations
    of `n` for `as.length` steps. -/
def ValSeq (n : Nat) : List Nat → Prop
  | [] => True
  | a :: as => v2 (3 * n + 1) = a ∧ ValSeq (syracuseStep n) as

/-- The Syracuse orbit after `M` accelerated steps. -/
def syracuseOrbit (n : Nat) : Nat → Nat
  | 0 => n
  | M + 1 => syracuseStep (syracuseOrbit n M)

lemma syracuseOrbit_succ (n M : Nat) :
    syracuseOrbit n (M + 1) = syracuseOrbit (syracuseStep n) M := by
  induction M generalizing n with
  | zero => rfl
  | succ M ih =>
      change syracuseStep (syracuseOrbit n (M + 1)) = syracuseOrbit (syracuseStep n) (M + 1)
      rw [ih]
      rfl

/-- `A_j = sum of the first j valuations` (so `A_0 = 0`). -/
def syracuseA : List Nat → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | a :: as, j + 1 => a + syracuseA as j

lemma syracuseA_length (as : List Nat) : syracuseA as as.length = as.sum := by
  induction as with
  | nil => simp [syracuseA]
  | cons a as ih => simp [syracuseA, ih]

/-- `T = sum_{j<M} 3^{M-1-j} 2^{A_j}`, by the recursion
    `T(a::as) = 3^{as.length} + 2^a * T(as)`. -/
def syracuseT : List Nat → Nat
  | [] => 0
  | a :: as => 3 ^ as.length + 2 ^ a * syracuseT as

/-- **THE EXACT M-STEP SYRACUSE IDENTITY:**
    `n_M * 2^{A_M} = 3^M * n_0 + sum_{j<M} 3^{M-1-j} 2^{A_j}`. -/
theorem syracuse_identity (n : Nat) (as : List Nat) (hval : ValSeq n as) :
    syracuseOrbit n as.length * 2 ^ syracuseA as as.length =
      3 ^ as.length * n + syracuseT as := by
  induction as generalizing n with
  | nil => simp [ValSeq, syracuseOrbit, syracuseA, syracuseT]
  | cons a as ih =>
      simp [ValSeq] at hval
      have hv : v2 (3 * n + 1) = a := hval.1
      have hval' : ValSeq (syracuseStep n) as := hval.2
      have ih' := ih (syracuseStep n) hval'
      have hstep : syracuseStep n * 2 ^ a = 3 * n + 1 := by
        simpa [hv] using syracuseStep_mul_pow_v2 n
      have hstep' : 2 ^ a * syracuseStep n = 3 * n + 1 := by
        rw [mul_comm]
        exact hstep
      simp only [List.length_cons, syracuseA, syracuseT]
      change syracuseOrbit n (as.length + 1) * 2 ^ (a + syracuseA as as.length) = _
      rw [syracuseOrbit_succ]
      calc
        syracuseOrbit (syracuseStep n) as.length * 2 ^ (a + syracuseA as as.length)
            = 2 ^ a * (syracuseOrbit (syracuseStep n) as.length *
                2 ^ syracuseA as as.length) := by ring
        _ = 2 ^ a * (3 ^ as.length * syracuseStep n + syracuseT as) := by rw [ih']
        _ = 3 ^ as.length * (2 ^ a * syracuseStep n) + 2 ^ a * syracuseT as := by ring
        _ = 3 ^ as.length * (3 * n + 1) + 2 ^ a * syracuseT as := by rw [hstep']
        _ = 3 ^ (as.length + 1) * n + (3 ^ as.length + 2 ^ a * syracuseT as) := by
          rw [pow_succ]
          ring

-- =========================================================================
-- Section 3 -- geometric valuation law (exact count of odd residues)
-- =========================================================================

/-- The Finset of odd residues modulo `2^K` with `v2(3n+1) = a`. -/
def exactValF (K a : Nat) : Finset (Fin (2 ^ K)) :=
  Finset.univ.filter (fun r => decide (r.val % 2 = 1 ∧ v2 (3 * r.val + 1) = a))

/-- Adding a multiple of `2^(a+1)` preserves the valuation `a`. -/
lemma v2_preserve_lift {a s t : Nat} (hs : s < 2 ^ (a + 1))
    (hv : v2 (3 * s + 1) = a) :
    v2 (3 * (s + 2 ^ (a + 1) * t) + 1) = a := by
  have hsum : 3 * (s + 2 ^ (a + 1) * t) + 1 = (3 * s + 1) + 3 * (2 ^ (a + 1) * t) := by ring
  apply (v2_eq_iff (by omega)).mpr
  constructor
  · have hdivs : 2 ^ a ∣ 3 * s + 1 := (v2_eq_iff (by omega)).mp hv |>.1
    have hadd : 2 ^ a ∣ 3 * (2 ^ (a + 1) * t) := by
      refine ⟨3 * 2 * t, ?_⟩
      rw [pow_succ]
      ring
    rw [hsum]
    exact dvd_add hdivs hadd
  · intro hbad
    have hdivs : ¬ 2 ^ (a + 1) ∣ 3 * s + 1 := (v2_eq_iff (by omega)).mp hv |>.2
    have hadd : 2 ^ (a + 1) ∣ 3 * (2 ^ (a + 1) * t) := by
      refine ⟨3 * t, by ring⟩
    rw [hsum] at hbad
    have hmodadd : (3 * (2 ^ (a + 1) * t)) % 2 ^ (a + 1) = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp hadd
    have hmodsum := Nat.dvd_iff_mod_eq_zero.mp hbad
    rw [Nat.add_mod, hmodadd, Nat.add_zero] at hmodsum
    exact hdivs (Nat.dvd_iff_mod_eq_zero.mpr (by simpa [Nat.mod_mod] using hmodsum))

/-- The converse: if the lifted value has valuation `a`, so does the base. -/
lemma v2_of_lift {a s t : Nat} (hs : s < 2 ^ (a + 1))
    (hv : v2 (3 * (s + 2 ^ (a + 1) * t) + 1) = a) :
    v2 (3 * s + 1) = a := by
  have hsum : 3 * (s + 2 ^ (a + 1) * t) + 1 = (3 * s + 1) + 3 * (2 ^ (a + 1) * t) := by ring
  apply (v2_eq_iff (by omega)).mpr
  constructor
  · have hdivs : 2 ^ a ∣ 3 * (s + 2 ^ (a + 1) * t) + 1 :=
      (v2_eq_iff (by omega)).mp hv |>.1
    have hadd : 2 ^ a ∣ 3 * (2 ^ (a + 1) * t) := by
      refine ⟨3 * 2 * t, ?_⟩
      rw [pow_succ]
      ring
    rw [hsum] at hdivs
    have hmodadd : (3 * (2 ^ (a + 1) * t)) % 2 ^ a = 0 := by
      apply Nat.dvd_iff_mod_eq_zero.mp
      refine ⟨3 * 2 * t, ?_⟩
      rw [pow_succ]
      ring
    have hmodsum := Nat.dvd_iff_mod_eq_zero.mp hdivs
    rw [Nat.add_mod, hmodadd, Nat.add_zero] at hmodsum
    exact Nat.dvd_iff_mod_eq_zero.mpr (by simpa [Nat.mod_mod] using hmodsum)
  · intro hbad
    have hnadd : ¬ 2 ^ (a + 1) ∣ 3 * (s + 2 ^ (a + 1) * t) + 1 :=
      (v2_eq_iff (by omega)).mp hv |>.2
    have hadd : 2 ^ (a + 1) ∣ 3 * (2 ^ (a + 1) * t) := by
      refine ⟨3 * t, by ring⟩
    apply hnadd
    rw [hsum]
    exact dvd_add hbad hadd

/-- Explicit odd witness with valuation `a` below `2^(a+1)`. -/
lemma valWitness (a : Nat) (ha : 1 ≤ a) :
    ∃ s : Nat, s < 2 ^ (a + 1) ∧ s % 2 = 1 ∧ v2 (3 * s + 1) = a := by
  by_cases hae : a % 2 = 0
  · let b := a / 2
    have hab : a = 2 * b := by omega
    have hdiv : 3 ∣ 2 ^ (2 * b) - 1 := by
      induction b with
      | zero => norm_num
      | succ b ih =>
          have hcalc : 2 ^ (2 * (b + 1)) - 1 = 4 * (2 ^ (2 * b) - 1) + 3 := by
            rw [show 2 * (b + 1) = 2 * b + 2 by omega, pow_add]
            norm_num
            have hp : 1 ≤ 2 ^ (2 * b) := Nat.one_le_pow _ _ (by norm_num)
            omega
          rw [hcalc]
          exact dvd_add (dvd_mul_of_dvd_right ih 4) (dvd_refl 3)
    let s := (2 ^ (2 * b) - 1) / 3
    have hmain : 3 * s + 1 = 2 ^ (2 * b) := by
      have hmul : 3 * s = 2 ^ (2 * b) - 1 := by dsimp [s]; exact Nat.mul_div_cancel' hdiv
      have hp : 1 ≤ 2 ^ (2 * b) := Nat.one_le_pow _ _ (by norm_num)
      omega
    refine ⟨s, ?_, ?_, ?_⟩
    · rw [hab]
      have hlt : 2 ^ (2 * b) < 2 ^ (2 * b + 1) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hsle : s ≤ 2 ^ (2 * b) := by omega
      exact lt_of_le_of_lt hsle hlt
    · have heven : (2 ^ (2 * b)) % 2 = 0 := by
        exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
      omega
    · rw [hab]
      apply (v2_eq_iff (by omega)).mpr
      constructor
      · rw [hmain]
      · rw [hmain]
        intro hdvd
        have hlt : 2 ^ (2 * b) < 2 ^ (2 * b + 1) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        exact (Nat.not_lt_of_ge (Nat.le_of_dvd (by positivity : 0 < 2 ^ (2 * b)) hdvd)) hlt
  · let b := a / 2
    have hab : a = 2 * b + 1 := by omega
    have hdiv : 3 ∣ 5 * 2 ^ (2 * b + 1) - 1 := by
      induction b with
      | zero => norm_num
      | succ b ih =>
          have hcalc : 5 * 2 ^ (2 * (b + 1) + 1) - 1 = 4 * (5 * 2 ^ (2 * b + 1) - 1) + 3 := by
            rw [show 2 * (b + 1) + 1 = (2 * b + 1) + 2 by omega, pow_add]
            norm_num
            have hp : 1 ≤ 2 ^ (2 * b + 1) := Nat.one_le_pow _ _ (by norm_num)
            omega
          rw [hcalc]
          exact dvd_add (dvd_mul_of_dvd_right ih 4) (dvd_refl 3)
    let s := (5 * 2 ^ (2 * b + 1) - 1) / 3
    have hmain : 3 * s + 1 = 5 * 2 ^ (2 * b + 1) := by
      have hmul : 3 * s = 5 * 2 ^ (2 * b + 1) - 1 := by dsimp [s]; exact Nat.mul_div_cancel' hdiv
      have hp : 0 < 5 * 2 ^ (2 * b + 1) := by positivity
      omega
    refine ⟨s, ?_, ?_, ?_⟩
    · rw [hab]
      have hpow : 2 ^ ((2 * b + 1) + 1) = 2 * 2 ^ (2 * b + 1) := by
        rw [pow_succ, mul_comm]
      have hlt : 5 * 2 ^ (2 * b + 1) < 3 * 2 ^ ((2 * b + 1) + 1) := by
        rw [hpow]
        nlinarith [show 0 < 2 ^ (2 * b + 1) by positivity]
      have hsle : 3 * s ≤ 5 * 2 ^ (2 * b + 1) := by omega
      omega
    · have heven : (5 * 2 ^ (2 * b + 1)) % 2 = 0 := by
        rw [Nat.mul_mod]
        have : 2 ^ (2 * b + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
        simp [this]
      omega
    · rw [hab]
      apply (v2_eq_iff (by omega)).mpr
      constructor
      · rw [hmain]
        exact (by simpa [mul_comm] using dvd_mul_right (2 ^ (2 * b + 1)) 5)
      · rw [hmain]
        intro hdvd
        have hcancel : 2 ∣ 5 := by
          apply Nat.dvd_of_mul_dvd_mul_left (show 0 < 2 ^ (2 * b + 1) by positivity)
          simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hdvd
        norm_num at hcancel

/-- If `v2(3l+1) = a`, then `3(l + 2^a) + 1` is divisible by `2^(a+1)`:
    adding `2^a` raises the valuation by at least one. -/
lemma val_of_add_pow (a l : Nat) (hv : v2 (3 * l + 1) = a) :
    2 ^ (a + 1) ∣ 3 * (l + 2 ^ a) + 1 := by
  have hdn : 2 ^ a ∣ 3 * l + 1 := (v2_eq_iff (by omega)).mp hv |>.1
  let u := (3 * l + 1) / 2 ^ a
  have hu : 3 * l + 1 = 2 ^ a * u := (Nat.mul_div_cancel' hdn).symm
  have huodd : u % 2 = 1 := by
    by_contra hnot
    have hueven : 2 ∣ u := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have hnv : ¬ 2 ^ (a + 1) ∣ 3 * l + 1 := (v2_eq_iff (by omega)).mp hv |>.2
    apply hnv
    rw [hu, pow_succ]
    exact mul_dvd_mul (dvd_refl _) hueven
  rw [show 3 * (l + 2 ^ a) + 1 = 2 ^ a * (u + 3) by
    rw [show 3 * (l + 2 ^ a) + 1 = (3 * l + 1) + 3 * 2 ^ a by ring, hu]
    ring, pow_succ]
  exact mul_dvd_mul (dvd_refl _) (by omega : 2 ∣ u + 3)

/-- Uniqueness modulo `2^(a+1)`: two odd residues with the same valuation `a`
    are equal. -/
lemma unique_val_residue_uniq (a n s : Nat) (ha : 1 ≤ a)
    (hn : n < 2 ^ (a + 1)) (hs : s < 2 ^ (a + 1))
    (hv_n : n % 2 = 1 ∧ v2 (3 * n + 1) = a)
    (hv_s : s % 2 = 1 ∧ v2 (3 * s + 1) = a) : n = s := by
  have hdn : 2 ^ a ∣ 3 * n + 1 := (v2_eq_iff (by omega)).mp hv_n.2 |>.1
  have hds : 2 ^ a ∣ 3 * s + 1 := (v2_eq_iff (by omega)).mp hv_s.2 |>.1
  have hcop : Nat.Coprime (2 ^ a) 3 :=
    Nat.Coprime.pow a 1 (by decide : Nat.Coprime 2 3)
  by_cases hns : n ≤ s
  · have hdsub : 2 ^ a ∣ 3 * (s - n) := by
      have h : 2 ^ a ∣ (3 * s + 1) - (3 * n + 1) := Nat.dvd_sub hds hdn
      rw [Nat.add_sub_add_right, ← Nat.mul_sub_left_distrib] at h
      exact h
    have hdns : 2 ^ a ∣ s - n := hcop.dvd_of_dvd_mul_left hdsub
    rcases hdns with ⟨c, hc⟩
    have hlt : s - n < 2 ^ (a + 1) := by omega
    have hc_lt : 2 ^ a * c < 2 ^ a * 2 := by
      rw [← pow_succ]
      rw [← hc]
      exact hlt
    have hcle : c ≤ 1 := by
      have hp : 0 < 2 ^ a := by positivity
      nlinarith
    interval_cases c
    · omega
    · have hs_eq : s = n + 2 ^ a := by omega
      have hnv : ¬ 2 ^ (a + 1) ∣ 3 * s + 1 := (v2_eq_iff (by omega)).mp hv_s.2 |>.2
      exact (hnv (by simpa [hs_eq] using val_of_add_pow a n hv_n.2)).elim
  · have hsn : s < n := by omega
    have hdsub : 2 ^ a ∣ 3 * (n - s) := by
      have h : 2 ^ a ∣ (3 * n + 1) - (3 * s + 1) := Nat.dvd_sub hdn hds
      rw [Nat.add_sub_add_right, ← Nat.mul_sub_left_distrib] at h
      exact h
    have hdns : 2 ^ a ∣ n - s := hcop.dvd_of_dvd_mul_left hdsub
    rcases hdns with ⟨c, hc⟩
    have hlt : n - s < 2 ^ (a + 1) := by omega
    have hc_lt : 2 ^ a * c < 2 ^ a * 2 := by
      rw [← pow_succ]
      rw [← hc]
      exact hlt
    have hcle : c ≤ 1 := by
      have hp : 0 < 2 ^ a := by positivity
      nlinarith
    interval_cases c
    · omega
    · have hn_eq : n = s + 2 ^ a := by omega
      have hnv : ¬ 2 ^ (a + 1) ∣ 3 * n + 1 := (v2_eq_iff (by omega)).mp hv_n.2 |>.2
      exact (hnv (by simpa [hn_eq] using val_of_add_pow a s hv_s.2)).elim

/-- There is exactly one odd residue modulo `2^(a+1)` with valuation `a`. -/
lemma unique_val_residue (a : Nat) (ha : 1 ≤ a) :
    ∃! s : Fin (2 ^ (a + 1)), s.val % 2 = 1 ∧ v2 (3 * s.val + 1) = a := by
  obtain ⟨s, hslt, hsodd, hsv⟩ := valWitness a ha
  refine ⟨⟨s, hslt⟩, ⟨hsodd, hsv⟩, ?_⟩
  intro y hy
  apply Fin.ext
  exact (unique_val_residue_uniq a s y.val ha hslt y.isLt ⟨hsodd, hsv⟩ hy).symm

/-- **GEOMETRIC VALUATION LAW:** for `1 <= a < K`, exactly `2^(K-a-1)` odd
    residues modulo `2^K` have `v2(3n+1) = a`. -/
lemma exactValF_card (K a : Nat) (ha : 1 ≤ a) (haK : a + 1 ≤ K) :
    (exactValF K a).card = 2 ^ (K - (a + 1)) := by
  obtain ⟨s0, hs0lt, hs0odd, hv0⟩ := valWitness a ha
  let f : Fin (2 ^ (K - (a + 1))) → Fin (2 ^ K) :=
    fun t => ⟨s0 + 2 ^ (a + 1) * t.val, by
      have hpow : 2 ^ (a + 1) * 2 ^ (K - (a + 1)) = 2 ^ K := by
        rw [← pow_add, Nat.add_sub_of_le haK]
      nlinarith [t.isLt]⟩
  have hmaps : ∀ t : Fin (2 ^ (K - (a + 1))), f t ∈ exactValF K a := by
    intro t
    simp [exactValF, f]
    constructor
    · have heven : (2 ^ (a + 1) * t.val) % 2 = 0 := by
        rw [Nat.mul_mod]
        have : 2 ^ (a + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
        simp [this]
      omega
    · exact v2_preserve_lift hs0lt hv0
  have hinj : Function.Injective f := by
    intro t₁ t₂ h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [f] at hv
    have hv' : 2 ^ (a + 1) * t₁.val = 2 ^ (a + 1) * t₂.val := Nat.add_left_cancel hv
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hv'
  have hsurj : ∀ r ∈ exactValF K a, ∃ t, f t = r := by
    intro r hr
    simp [exactValF] at hr
    let q := r.val / 2 ^ (a + 1)
    let s' := r.val % 2 ^ (a + 1)
    have hs'lt : s' < 2 ^ (a + 1) := Nat.mod_lt _ (by positivity)
    have hdecomp : r.val = s' + 2 ^ (a + 1) * q := by
      dsimp [q, s']
      conv_lhs => rw [← Nat.div_add_mod r.val (2 ^ (a + 1))]
      ring
    have hs'odd : s' % 2 = 1 := by
      have heven : (2 ^ (a + 1) * q) % 2 = 0 := by
        rw [Nat.mul_mod]
        have : 2 ^ (a + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
        simp [this]
      have hmod := congrArg (fun x => x % 2) hdecomp
      rw [Nat.add_mod, heven] at hmod
      norm_num at hmod
      omega
    have hs'val : v2 (3 * s' + 1) = a := by
      have hvq : v2 (3 * (s' + 2 ^ (a + 1) * q) + 1) = a := by
        rw [← hdecomp]
        exact hr.2
      exact v2_of_lift hs'lt hvq
    have hs'eq : s' = s0 := by
      exact unique_val_residue_uniq a s' s0 ha hs'lt hs0lt ⟨hs'odd, hs'val⟩ ⟨hs0odd, hv0⟩
    have hq : q < 2 ^ (K - (a + 1)) := by
      have hpow : 2 ^ (a + 1) * 2 ^ (K - (a + 1)) = 2 ^ K := by
        rw [← pow_add, Nat.add_sub_of_le haK]
      have hrlt : r.val < 2 ^ (a + 1) * 2 ^ (K - (a + 1)) := by
        rw [hpow]
        exact r.isLt
      dsimp [q]
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      rw [mul_comm]
      exact hrlt
    refine ⟨⟨q, hq⟩, ?_⟩
    apply Fin.ext
    dsimp [f]
    rw [hdecomp, hs'eq]
  calc
    (exactValF K a).card = (Finset.univ : Finset (Fin (2 ^ (K - (a + 1))))).card := by
      symm
      exact Finset.card_bij (s := (Finset.univ : Finset (Fin (2 ^ (K - (a + 1))))))
        (t := exactValF K a) (fun t _ => f t) (by intro t ht; exact hmaps t)
        (by intro t₁ _ t₂ _ h; exact hinj h)
        (by intro r hr; rcases hsurj r hr with ⟨t, ht⟩; exact ⟨t, Finset.mem_univ t, ht⟩)
    _ = 2 ^ (K - (a + 1)) := by simp

-- =========================================================================
-- Section 4 -- cycle minimum bound from Diophantine gaps
-- =========================================================================

/-- Maximum possible `T` over all valuation lists with sum `E` and `M` steps:
    `T_max(M,E) = 2^{E-M}(3^M - 2^M)`. -/
def tildeTmax (M E : Nat) : Nat := 2 ^ (E - M) * (3 ^ M - 2 ^ M)

/-- The sharp envelope, proved by induction using positivity of valuations. -/
lemma syracuseT_le_tildeTmax_of_pos (as : List Nat) (h : ∀ a ∈ as, 1 ≤ a) :
    syracuseT as ≤ tildeTmax as.length as.sum := by
  induction as with
  | nil => simp [syracuseT, tildeTmax]
  | cons a as ih =>
      have ha1 : 1 ≤ a := h a (by simp)
      have htail : ∀ x ∈ as, 1 ≤ x := by intro x hx; exact h x (by simp [hx])
      have ih' := ih htail
      simp only [syracuseT, tildeTmax, List.length_cons, List.sum_cons]
      have hlen_pos : ∀ (l : List Nat), (∀ x ∈ l, 1 ≤ x) → l.length ≤ l.sum := by
        intro l hl
        induction l with
        | nil => simp
        | cons x xs ih =>
            have hx : 1 ≤ x := hl x (by simp)
            have hxs : ∀ y ∈ xs, 1 ≤ y := by intro y hy; exact hl y (by simp [hy])
            simp [List.sum_cons, List.length_cons]
            have := ih hxs
            omega
      have hlen : as.length ≤ as.sum := hlen_pos as htail
      have hshift : a + (as.sum - as.length) = (a + as.sum - as.length) := by omega
      let P := 2 ^ (a + as.sum - as.length - 1)
      have hP : 1 ≤ P := by
        dsimp [P]
        exact Nat.one_le_pow _ _ (by norm_num)
      have hfac : 2 ^ (a + (as.sum - as.length)) = 2 * P := by
        dsimp [P]
        rw [show a + (as.sum - as.length) = (a + as.sum - as.length - 1) + 1 by omega]
        rw [pow_succ]
        ring
      have hP_exp : 2 ^ (a + as.sum - (as.length + 1)) = P := by
        dsimp [P]
        congr 1
      calc
        3 ^ as.length + 2 ^ a * syracuseT as
            ≤ 3 ^ as.length + 2 ^ a * (2 ^ (as.sum - as.length) *
                (3 ^ as.length - 2 ^ as.length)) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left (2 ^ a) ih') _
        _ = 3 ^ as.length + (2 ^ a * 2 ^ (as.sum - as.length)) *
              (3 ^ as.length - 2 ^ as.length) := by ring
        _ = 3 ^ as.length + 2 * P * (3 ^ as.length - 2 ^ as.length) := by
              rw [← pow_add, hfac]
        _ ≤ P * 3 ^ as.length + 2 * P * (3 ^ as.length - 2 ^ as.length) := by
              have hPP : 3 ^ as.length ≤ P * 3 ^ as.length := by
                nlinarith [hP, show 0 < 3 ^ as.length by positivity]
              exact Nat.add_le_add_right hPP _
        _ = P * (3 ^ (as.length + 1) - 2 ^ (as.length + 1)) := by
              rw [pow_succ, pow_succ]
              have hyx : 2 ^ as.length ≤ 3 ^ as.length := by
                induction as.length with
                | zero => simp
                | succ k ih =>
                    rw [pow_succ, pow_succ]
                    exact Nat.mul_le_mul ih (by norm_num : 2 ≤ 3)
              have hxy2 : 2 ^ as.length * 2 ≤ 3 ^ as.length * 3 := by
                nlinarith [hyx, show 0 < 3 ^ as.length by positivity]
              have hcalc1 : 3 ^ as.length - 2 ^ as.length + 2 ^ as.length = 3 ^ as.length :=
                Nat.sub_add_cancel hyx
              have hcalc2 : 3 ^ as.length * 3 - 2 ^ as.length * 2 + 2 ^ as.length * 2 =
                  3 ^ as.length * 3 := Nat.sub_add_cancel hxy2
              nlinarith
        _ = 2 ^ (a + as.sum - (as.length + 1)) *
              (3 ^ (as.length + 1) - 2 ^ (as.length + 1)) := by rw [hP_exp]

/-- If a Syracuse cycle attains its minimum at the start and `as` is its
    valuation list, then `n_min * (2^E - 3^M) = T`, hence
    `n_min * (2^E - 3^M) <= T_max(M,E)`. -/
theorem cycle_min_upper_bound (n : Nat) (as : List Nat) (hval : ValSeq n as)
    (hcyc : syracuseOrbit n as.length = n) (hnpos : 0 < n) (ha : ∀ a ∈ as, 1 ≤ a) :
    n * (2 ^ as.sum - 3 ^ as.length) ≤ tildeTmax as.length as.sum := by
  have hid := syracuse_identity n as hval
  rw [hcyc] at hid
  have hid' : 2 ^ as.sum * n = 3 ^ as.length * n + syracuseT as := by
    rw [mul_comm]
    simpa [syracuseA_length] using hid
  have hlepow : 3 ^ as.length ≤ 2 ^ as.sum := by
    have hle : 3 ^ as.length * n ≤ 2 ^ as.sum * n := by nlinarith
    exact Nat.le_of_mul_le_mul_right hle hnpos
  have hrel : n * (2 ^ as.sum - 3 ^ as.length) = syracuseT as := by
    have hmul : (2 ^ as.sum - 3 ^ as.length) * n + 3 ^ as.length * n = 2 ^ as.sum * n := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hlepow]
    rw [hid'] at hmul
    rw [add_comm ((2 ^ as.sum - 3 ^ as.length) * n) (3 ^ as.length * n)] at hmul
    have hc := Nat.add_left_cancel hmul
    rw [mul_comm n (2 ^ as.sum - 3 ^ as.length)]
    exact hc
  rw [hrel]
  exact syracuseT_le_tildeTmax_of_pos as ha

#print axioms v2_dvd
#print axioms syracuseStep_mul_pow_v2
#print axioms syracuseStep_odd
#print axioms syracuse_identity
#print axioms valWitness
#print axioms unique_val_residue
#print axioms exactValF_card
#print axioms syracuseT_le_tildeTmax_of_pos
#print axioms cycle_min_upper_bound

end SyracuseLogDrift
end CollatzAdicBase
