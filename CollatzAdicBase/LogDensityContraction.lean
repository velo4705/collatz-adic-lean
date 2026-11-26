import CollatzAdicBase.ExcursionTail
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# Bounded-excursion Syracuse contraction and dyadic logarithmic density (Layer 7)

This module combines the two verified large-deviation bounds of Layers 5--6:

* `SyracuseRenewal.syracuseFail_rational_decay`: at `M = 5t`, `K = 8t` the
  terminal non-contraction classes obey `fail / 2^(K-1) <= (24/25)^(5t)`;
* `ExcursionTail.excursionFailF_tail_uniform`: the upward-excursion classes
  obey `exc / 2^(K-1) <= 26 / sqrt(B)`, uniformly in `M` and `K`.

A union bound gives the good residue set `goodTrajectoryF K M B`: odd classes
mod `2^K` avoiding both exceptional sets.  Its density is at least
`1 - (24/25)^(5t) - 26/sqrt(B)`.  Coupling `M = 5t ~ log log X` and
`B ~ (log X)^c` makes this `O((log X)^(-gamma))` on dyadic intervals.

For any odd `n₀` in a good class whose first `M` accelerated valuations are
determined by that class (`A_M + 1 <= K`) and which exceeds the explicit
additive-drift threshold `N₀ = 2^(K-1) (3/2)^M`, we prove

  * every prefix satisfies `n_j / n₀ <= B + 1` (bounded peak), and
  * `n_M < n₀` (net contraction), with the explicit factor
    `1 - 2^{-(K-1)}`, so `n_M <= α n₀` for any `α > 1 - 2^{-(K-1)}`
    once `n₀` is large enough.

All proofs use core Lean axioms only: no `sorry`, no `admit`, no custom axioms.
-/

namespace CollatzAdicBase

namespace LogDensityContraction

open SyracuseLogDrift
open SyracuseRenewal
open ExcursionTail

-- =========================================================================
-- Section 1 -- the combined good residue set
-- =========================================================================

/-- Odd residue classes mod `2^K` avoiding terminal non-contraction and the
    intermediate upward excursion. -/
noncomputable def goodTrajectoryF (K M : Nat) (B : ℚ) : Finset (Fin (2 ^ K)) := by
  classical
  exact Finset.univ.filter (fun r => decide
    (r.val % 2 = 1 ∧ r ∉ syracuseFailF K M ∧ r ∉ excursionFailF K M B))

lemma mem_goodTrajectoryF {K M : Nat} {B : ℚ} {r : Fin (2 ^ K)} :
    r ∈ goodTrajectoryF K M B ↔
      r.val % 2 = 1 ∧ r ∉ syracuseFailF K M ∧ r ∉ excursionFailF K M B := by
  simp [goodTrajectoryF]

-- =========================================================================
-- Section 2 -- valuation-list bookkeeping
-- =========================================================================

/-- The valuation list of a `ValSeq` witness equals the canonical list. -/
lemma valList_eq_of_ValSeq {n : Nat} {as : List Nat} (hval : ValSeq n as) :
    valList n as.length = as := by
  induction as generalizing n with
  | nil => simp [valList]
  | cons a as ih =>
      simp only [ValSeq] at hval
      simp [valList, hval.1, ih hval.2]

/-- For an odd residue, membership in `syracuseFailF` is exactly the terminal
    inequality `2^(A_M) <= 3^M` for its canonical valuation list. -/
lemma mem_syracuseFailF_iff_valList {K M : Nat} {r : Fin (2 ^ K)}
    (hr : r.val % 2 = 1) :
    r ∈ syracuseFailF K M ↔ 2 ^ (valList r.val M).sum ≤ 3 ^ M := by
  constructor
  · intro hmem
    rcases (mem_syracuseFailF.mp hmem).2 with ⟨as, hval, hlen, hle⟩
    have hlist : valList r.val M = as := by
      rw [← hlen]
      exact valList_eq_of_ValSeq hval
    rwa [hlist]
  · intro hle
    exact mem_syracuseFailF.mpr ⟨hr, valList r.val M, valList_ValSeq r.val M,
      valList_length r.val M, hle⟩

/-- Avoiding `syracuseFailF` forces strict terminal contraction. -/
lemma not_mem_syracuseFailF_contracts {K M : Nat} {r : Fin (2 ^ K)}
    (hr : r.val % 2 = 1) (hnot : r ∉ syracuseFailF K M) :
    3 ^ M < 2 ^ (valList r.val M).sum := by
  have hle : ¬ 2 ^ (valList r.val M).sum ≤ 3 ^ M := by
    intro hle
    exact hnot ((mem_syracuseFailF_iff_valList hr).mpr hle)
  omega

/-- Avoiding `excursionFailF` (with the orbit determined mod `2^K`) forbids
    every prefix from reaching the multiplier `B`. -/
lemma not_mem_excursionFailF_no_excursion {K M : Nat} {B : ℚ} {r : Fin (2 ^ K)}
    (hr : r.val % 2 = 1) (hA : (valList r.val M).sum < K)
    (hnot : r ∉ excursionFailF K M B) :
    ∀ j, 1 ≤ j → j ≤ M → (3 : ℚ) ^ j < B * (2 : ℚ) ^ syracuseA (valList r.val M) j := by
  intro j hj hjm
  by_contra hnotlt
  have hge : B * (2 : ℚ) ^ syracuseA (valList r.val M) j ≤ (3 : ℚ) ^ j := le_of_not_gt hnotlt
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hi : i < (valList r.val M).length := by simpa [valList_length] using hjm
  have hineq : B * (2 : ℚ) ^ (0 + syracuseA (valList r.val M) (i + 1)) ≤
      (3 : ℚ) ^ (1 + i) := by simpa [Nat.add_comm] using hge
  have hbad : excursionPrefix B (valList r.val M) = true := by
    simpa [excursionPrefix] using
      ((excursionAux_iff B 0 1 (valList r.val M)).2 ⟨i, hi, hineq⟩)
  exact hnot (mem_excursionFailF.mpr ⟨hr, hA, hbad⟩)

/-- The odd residues modulo `2^K` number at least `2^(K-1)`. -/
lemma oddFin_card_ge {K : Nat} (hK : 1 ≤ K) :
    2 ^ (K - 1) ≤
      (Finset.univ.filter (fun r : Fin (2 ^ K) => decide (r.val % 2 = 1))).card := by
  classical
  let f : Fin (2 ^ (K - 1)) → {r : Fin (2 ^ K) // r.val % 2 = 1} := fun i =>
    ⟨⟨2 * i.val + 1, by
        have hi : i.val < 2 ^ (K - 1) := i.isLt
        have hpow : 2 ^ K = 2 * 2 ^ (K - 1) := by
          calc
            2 ^ K = 2 ^ ((K - 1) + 1) := by congr 1; omega
            _ = 2 ^ (K - 1) * 2 := by rw [pow_succ]
            _ = 2 * 2 ^ (K - 1) := by ring
        rw [hpow]
        omega⟩,
      by
        have hdiv : (2 * i.val) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_right 2 i.val)
        rw [Nat.add_mod, hdiv]⟩
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg (fun x : {r : Fin (2 ^ K) // r.val % 2 = 1} => x.val.val) hij
    dsimp [f] at hval
    omega
  have hle := Fintype.card_le_of_injective f hinj
  simpa [Fintype.card_subtype] using hle

-- =========================================================================
-- Section 3 -- analytic pathwise bounds: bounded peak and net contraction
-- =========================================================================

/-- The explicit additive-drift threshold `N₀(K,M) = 2^(K-1) (3/2)^M` in
    rational arithmetic. -/
def contractThreshold (K M : Nat) : ℚ := (2 : ℚ) ^ (K - 1) * ((3 : ℚ) / 2) ^ M

/-- The guaranteed contraction floor from a non-failing terminal multiplier. -/
def contractFloor (K : Nat) : ℚ := 1 - 1 / (2 : ℚ) ^ (K - 1)

/-- **PATHWISE BOUNDED PEAK AND CONTRACTION.**  Let an odd start `n` have
    valuation list `as` of length `M`, with `A = as.sum + 1 <= K`, terminal
    contraction `3^M < 2^A`, no prefix reaching `B`, and `n > N₀(K,M)`.
    Then every prefix obeys `n_j / n <= B + 1`, and

        n_M / n <= (1 - 2^{-(K-1)}) + (3/2)^M / n,

    which is `< 1` by the threshold. -/
lemma bounded_and_contracts_of_vals (n M K : Nat) (B : ℚ) (as : List Nat)
    (hnodd : n % 2 = 1) (hnpos : 0 < n) (hval : ValSeq n as) (hlen : as.length = M)
    (hA : as.sum + 1 ≤ K) (hcontract : 3 ^ M < 2 ^ as.sum)
    (hnoexc : ∀ j, 1 ≤ j → j ≤ M → (3 : ℚ) ^ j < B * (2 : ℚ) ^ syracuseA as j)
    (hthreshold : contractThreshold K M < (n : ℚ)) :
    (∀ j, 1 ≤ j → j ≤ M → (syracuseOrbit n j : ℚ) ≤ (B + 1) * (n : ℚ)) ∧
      (syracuseOrbit n M : ℚ) ≤ contractFloor K * (n : ℚ) + ((3 : ℚ) / 2) ^ M := by
  classical
  have hnq : 0 < (n : ℚ) := by positivity
  have hKpos : 1 ≤ K := by omega
  have h2Kpos : 0 < (2 : ℚ) ^ (K - 1) := by positivity
  -- from the threshold: (3/2)^M / n < 1 / 2^(K-1)
  have hp_lt : ((3 : ℚ) / 2) ^ M < (n : ℚ) / (2 : ℚ) ^ (K - 1) := by
    rw [lt_div_iff₀ h2Kpos]
    simpa [contractThreshold, mul_comm] using hthreshold
  have hthr_div : ((3 : ℚ) / 2) ^ M / (n : ℚ) < 1 / (2 : ℚ) ^ (K - 1) := by
    rw [div_lt_iff₀ hnq]
    have heq : (1 / (2 : ℚ) ^ (K - 1)) * (n : ℚ) = (n : ℚ) / (2 : ℚ) ^ (K - 1) := by ring
    rw [heq]
    exact hp_lt
  have hone_over : 1 / (2 : ℚ) ^ (K - 1) ≤ 1 := by
    rw [div_le_iff₀ h2Kpos]
    have hge : (1 : ℚ) ≤ (2 : ℚ) ^ (K - 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hsecond_aux : ∀ j : Nat,
      ((3 ^ j - 2 ^ j : Nat) : ℚ) / ((n : ℚ) * (2 : ℚ) ^ j) ≤ ((3 : ℚ) / 2) ^ j / (n : ℚ) := by
    intro j
    have h2le3 : 2 ^ j ≤ 3 ^ j := GlideMarkovChain.two_le_three_pow j
    have hcast : ((3 ^ j - 2 ^ j : Nat) : ℚ) = (3 : ℚ) ^ j - (2 : ℚ) ^ j := by
      rw [Nat.cast_sub h2le3]
      norm_num
    have h2non : 0 ≤ (2 : ℚ) ^ j := by positivity
    have hnum : (3 : ℚ) ^ j - (2 : ℚ) ^ j ≤ (3 : ℚ) ^ j := by nlinarith
    have hden : 0 ≤ (n : ℚ) * (2 : ℚ) ^ j := by positivity
    have hle := div_le_div_of_nonneg_right hnum hden
    have heq : (3 : ℚ) ^ j / ((n : ℚ) * (2 : ℚ) ^ j) = ((3 : ℚ) / 2) ^ j / (n : ℚ) := by
      rw [div_pow]
      field_simp [hnq.ne', show (2 : ℚ) ^ j ≠ 0 by positivity]
    rw [hcast]
    exact le_trans hle (le_of_eq heq)
  constructor
  · intro j hj hjm
    have hjlen : j ≤ as.length := by omega
    have hratio := (syracuseOrbit_ratio_le n as j hnodd hval hjlen hnpos).2
    have hfirst : (3 : ℚ) ^ j / (2 : ℚ) ^ syracuseA as j < B := by
      rw [div_lt_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ syracuseA as j)]
      simpa using hnoexc j hj hjm
    have hpow_le : ((3 : ℚ) / 2) ^ j ≤ ((3 : ℚ) / 2) ^ M :=
      pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 3 / 2) hjm
    have hsmall : ((3 : ℚ) / 2) ^ j / (n : ℚ) < 1 :=
      lt_of_le_of_lt (div_le_div_of_nonneg_right hpow_le (le_of_lt hnq))
        (lt_of_lt_of_le hthr_div hone_over)
    have hbound : (syracuseOrbit n j : ℚ) / (n : ℚ) < B + 1 := by
      calc
        (syracuseOrbit n j : ℚ) / (n : ℚ) ≤
            (3 : ℚ) ^ j / (2 : ℚ) ^ syracuseA as j +
              ((3 ^ j - 2 ^ j : Nat) : ℚ) / ((n : ℚ) * (2 : ℚ) ^ j) := hratio
        _ < B + ((3 : ℚ) / 2) ^ j / (n : ℚ) := add_lt_add_of_lt_of_le hfirst (hsecond_aux j)
        _ < B + 1 := by nlinarith [hsmall]
    exact le_of_lt ((div_lt_iff₀ hnq).mp hbound)
  · have hratio := (syracuseOrbit_ratio_le n as M hnodd hval (by simpa [hlen]) hnpos).2
    have hAeq : syracuseA as M = as.sum := by
      rw [← hlen]
      exact syracuseA_length as
    rw [hAeq] at hratio
    have hcontractQ : (3 : ℚ) ^ M + 1 ≤ (2 : ℚ) ^ as.sum := by
      have hnat : 3 ^ M + 1 ≤ 2 ^ as.sum := Nat.succ_le_of_lt hcontract
      exact_mod_cast hnat
    have hfirstM : (3 : ℚ) ^ M / (2 : ℚ) ^ as.sum ≤ 1 - 1 / (2 : ℚ) ^ as.sum := by
      have h2Apos : 0 < (2 : ℚ) ^ as.sum := by positivity
      rw [div_le_iff₀ h2Apos]
      rw [sub_mul, one_mul]
      have hcancel : (1 / (2 : ℚ) ^ as.sum) * (2 : ℚ) ^ as.sum = 1 := by
        field_simp [h2Apos.ne']
      rw [hcancel]
      nlinarith [hcontractQ]
    have hsum_le : as.sum ≤ K - 1 := by omega
    have hpow_le : (2 : ℚ) ^ as.sum ≤ (2 : ℚ) ^ (K - 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hsum_le
    have hinv_le : 1 / (2 : ℚ) ^ (K - 1) ≤ 1 / (2 : ℚ) ^ as.sum :=
      one_div_le_one_div_of_le (by positivity : (0 : ℚ) < (2 : ℚ) ^ as.sum) hpow_le
    have hfirstM' : (3 : ℚ) ^ M / (2 : ℚ) ^ as.sum ≤ contractFloor K := by
      dsimp [contractFloor]
      nlinarith [hfirstM, hinv_le]
    have hsum : (syracuseOrbit n M : ℚ) / (n : ℚ) < 1 := by
      calc
        (syracuseOrbit n M : ℚ) / (n : ℚ) ≤
            (3 : ℚ) ^ M / (2 : ℚ) ^ as.sum +
              ((3 ^ M - 2 ^ M : Nat) : ℚ) / ((n : ℚ) * (2 : ℚ) ^ M) := hratio
        _ ≤ contractFloor K + ((3 : ℚ) / 2) ^ M / (n : ℚ) :=
          add_le_add hfirstM' (hsecond_aux M)
        _ < 1 := by dsimp [contractFloor] at *; nlinarith [hthr_div]
    have hstrict : (syracuseOrbit n M : ℚ) < (n : ℚ) := by
      simpa using (div_lt_iff₀ hnq).mp hsum
    have hbound : (syracuseOrbit n M : ℚ) / (n : ℚ) ≤
        contractFloor K + ((3 : ℚ) / 2) ^ M / (n : ℚ) := by
      calc
        (syracuseOrbit n M : ℚ) / (n : ℚ) ≤
            (3 : ℚ) ^ M / (2 : ℚ) ^ as.sum +
              ((3 ^ M - 2 ^ M : Nat) : ℚ) / ((n : ℚ) * (2 : ℚ) ^ M) := hratio
        _ ≤ contractFloor K + ((3 : ℚ) / 2) ^ M / (n : ℚ) :=
          add_le_add hfirstM' (hsecond_aux M)
    have hmul : (syracuseOrbit n M : ℚ) ≤
        (contractFloor K + ((3 : ℚ) / 2) ^ M / (n : ℚ)) * (n : ℚ) :=
      (div_le_iff₀ hnq).mp hbound
    have heqmul : (contractFloor K + ((3 : ℚ) / 2) ^ M / (n : ℚ)) * (n : ℚ) =
        contractFloor K * (n : ℚ) + ((3 : ℚ) / 2) ^ M := by
      field_simp [hnq.ne']
    rwa [heqmul] at hmul

-- =========================================================================
-- Section 4 -- explicit cardinality lower bound for the good set
-- =========================================================================

/-- **GOOD-SET DENSITY.**  At `K = 8t`, `M = 5t`,

    good / 2^(K-1) >= 1 - (24/25)^(5t) - 26/sqrt(B).

    This is the union bound of the Layer 5 terminal decay and the Layer 6
    uniform excursion tail. -/
theorem goodTrajectory_card_lower (t : Nat) (ht : 1 ≤ t) (B : ℚ) (hB : 0 < B) :
    ((goodTrajectoryF (8 * t) (5 * t) B).card : ℝ) ≥
      (2 : ℝ) ^ (8 * t - 1) *
        (1 - ((24 : ℝ) / 25) ^ (5 * t) - 26 / Real.sqrt (B : ℝ)) := by
  classical
  let K := 8 * t
  let M := 5 * t
  let oddF : Finset (Fin (2 ^ K)) :=
    Finset.univ.filter (fun r : Fin (2 ^ K) => decide (r.val % 2 = 1))
  let goodF := goodTrajectoryF K M B
  let failF := syracuseFailF K M
  let excF := excursionFailF K M B
  have hKpos : 1 ≤ K := by dsimp [K]; omega
  have hodd_ge : (2 : ℝ) ^ (K - 1) ≤ (oddF.card : ℝ) := by
    exact_mod_cast (oddFin_card_ge hKpos)
  have hsubset : oddF ⊆ (goodF ∪ failF) ∪ excF := by
    intro r hr
    have hrodd : r.val % 2 = 1 := by simpa [oddF] using hr
    by_cases hf : r ∈ failF
    · simp [hf]
    · by_cases he : r ∈ excF
      · simp [hf, he]
      · have hg : r ∈ goodF := mem_goodTrajectoryF.mpr ⟨hrodd, hf, he⟩
        simp [hf, he, hg]
  have hcard_union : oddF.card ≤ goodF.card + failF.card + excF.card := by
    have hc := Finset.card_le_card hsubset
    calc
      oddF.card ≤ ((goodF ∪ failF) ∪ excF).card := hc
      _ ≤ (goodF ∪ failF).card + excF.card := Finset.card_union_le _ _
      _ ≤ (goodF.card + failF.card) + excF.card := by
        gcongr
        exact Finset.card_union_le _ _
      _ = goodF.card + failF.card + excF.card := by omega
  have hgood_ge : (goodF.card : ℝ) ≥
      (2 : ℝ) ^ (K - 1) - (failF.card : ℝ) - (excF.card : ℝ) := by
    have hcR : (oddF.card : ℝ) ≤ (goodF.card : ℝ) + (failF.card : ℝ) + (excF.card : ℝ) := by
      exact_mod_cast hcard_union
    nlinarith [hodd_ge, hcR]
  -- Layer 5 terminal decay, converted to real arithmetic
  have hf_nat := syracuseFail_rational_decay t
  have hf_real : (failF.card : ℝ) ≤
      (2 : ℝ) ^ (K - 1) * ((24 : ℝ) / 25) ^ M := by
    have hfq : (2 * (syracuseFailF (8 * t) (5 * t)).card * 25 ^ (5 * t) : ℝ) ≤
        (24 ^ (5 * t) * 2 ^ (8 * t) : ℝ) := by exact_mod_cast hf_nat
    have hmul : ((syracuseFailF (8 * t) (5 * t)).card : ℝ) * (2 * (25 : ℝ) ^ (5 * t)) ≤
        (24 : ℝ) ^ (5 * t) * (2 : ℝ) ^ (8 * t) := by
      nlinarith [hfq]
    have hpos : (0 : ℝ) < 2 * (25 : ℝ) ^ (5 * t) := by positivity
    have hdiv : ((syracuseFailF (8 * t) (5 * t)).card : ℝ) ≤
        ((24 : ℝ) ^ (5 * t) * (2 : ℝ) ^ (8 * t)) / (2 * (25 : ℝ) ^ (5 * t)) :=
      (le_div_iff₀ hpos).mpr hmul
    have heq : ((24 : ℝ) ^ (5 * t) * (2 : ℝ) ^ (8 * t)) /
          (2 * (25 : ℝ) ^ (5 * t)) =
        (2 : ℝ) ^ (K - 1) * ((24 : ℝ) / 25) ^ M := by
      have hpow : (8 * t) = (8 * t - 1) + 1 := by omega
      rw [hpow, pow_succ, div_pow]
      dsimp [K, M]
      field_simp
    rwa [heq] at hdiv
  -- Layer 6 uniform excursion tail
  have he_nat := excursionFailF_tail_uniform K M B hB
  have hsqrtpos : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hB)
  have he_real : (excF.card : ℝ) ≤ (2 : ℝ) ^ (K - 1) * (26 / Real.sqrt (B : ℝ)) := by
    have hq : ((excursionFailF K M B).card : ℝ) * Real.sqrt (B : ℝ) ≤
        (26 : ℝ) * (2 : ℝ) ^ (K - 1) := by exact_mod_cast he_nat
    have hdiv : ((excursionFailF K M B).card : ℝ) ≤
        ((26 : ℝ) * (2 : ℝ) ^ (K - 1)) / Real.sqrt (B : ℝ) :=
      (le_div_iff₀ hsqrtpos).mpr hq
    have heq : ((26 : ℝ) * (2 : ℝ) ^ (K - 1)) / Real.sqrt (B : ℝ) =
        (2 : ℝ) ^ (K - 1) * (26 / Real.sqrt (B : ℝ)) := by ring
    simpa [excF, heq] using hdiv
  dsimp [goodF] at hgood_ge
  dsimp [K, M] at hgood_ge hf_real he_real ⊢
  nlinarith [hgood_ge, hf_real, he_real]

-- =========================================================================
-- Section 5 -- pathwise theorem for good residue classes
-- =========================================================================

/-- Transfer the good-residue hypotheses to the valuation list of `n₀`. -/
lemma goodTrajectory_vals_of_residue (K M : Nat) (B : ℚ) {n0 : Nat}
    (hnodd : n0 % 2 = 1) (hA : (valList n0 M).sum + 1 ≤ K)
    (hgood : (⟨n0 % 2 ^ K, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ K)) ∈
      goodTrajectoryF K M B) :
    3 ^ M < 2 ^ (valList n0 M).sum ∧
      (∀ j, 1 ≤ j → j ≤ M → (3 : ℚ) ^ j < B * (2 : ℚ) ^ syracuseA (valList n0 M) j) := by
  classical
  let r : Fin (2 ^ K) := ⟨n0 % 2 ^ K, Nat.mod_lt _ (by positivity)⟩
  have hmod : n0 ≡ r.val [MOD 2 ^ K] := by
    dsimp [r]
    exact (Nat.mod_modEq n0 (2 ^ K)).symm
  have hlist : valList n0 M = valList r.val M := valList_eq_of_modEq hnodd hmod hA
  have hdiv : 2 ∣ 2 ^ K := by
    refine ⟨2 ^ (K - 1), ?_⟩
    calc
      2 ^ K = 2 ^ ((K - 1) + 1) := by
        have hKpos : 1 ≤ K := by omega
        congr 1
        omega
      _ = 2 ^ (K - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (K - 1) := by ring
  have hrodd : r.val % 2 = 1 := by
    have hmod2 : n0 % 2 = r.val % 2 := hmod.of_dvd hdiv
    omega
  have hgood' := mem_goodTrajectoryF.mp hgood
  have hcontract_r : 3 ^ M < 2 ^ (valList r.val M).sum :=
    not_mem_syracuseFailF_contracts hrodd hgood'.2.1
  have hAr : (valList r.val M).sum < K := by
    rw [← hlist]
    omega
  have hnoexc_r := not_mem_excursionFailF_no_excursion hrodd hAr hgood'.2.2
  constructor
  · rwa [hlist]
  · intro j hj hjm
    rw [hlist]
    exact hnoexc_r j hj hjm

/-- **GOOD-TRAJECTORY BOUNDED CONTRACTION.**  Let `n₀` be odd, let its first
    `M` accelerated valuations be determined by its residue mod `2^K`
    (`A_M + 1 <= K`), let that residue lie in `goodTrajectoryF K M B`, and let
    `n₀ > N₀(K,M) = 2^(K-1)(3/2)^M`.  Then every intermediate value stays
    below `(B+1) n₀` and the orbit strictly contracts: `n_M < n₀`. -/
theorem goodTrajectory_bounded_and_contracts
    (K M : Nat) (B : ℚ) (hB : 0 < B) {n0 : Nat}
    (hnodd : n0 % 2 = 1) (hnpos : 0 < n0)
    (hA : (valList n0 M).sum + 1 ≤ K)
    (hgood : (⟨n0 % 2 ^ K, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ K)) ∈
      goodTrajectoryF K M B)
    (hthreshold : contractThreshold K M < (n0 : ℚ)) :
    (∀ j, 1 ≤ j → j ≤ M → (syracuseOrbit n0 j : ℚ) ≤ (B + 1) * (n0 : ℚ)) ∧
      (syracuseOrbit n0 M : ℚ) < (n0 : ℚ) := by
  classical
  have hvals := goodTrajectory_vals_of_residue K M B hnodd hA hgood
  have hres := bounded_and_contracts_of_vals n0 M K B (valList n0 M)
    hnodd hnpos (valList_ValSeq n0 M) (valList_length n0 M) hA
    hvals.1 hvals.2 hthreshold
  refine ⟨hres.1, ?_⟩
  have hstrict_rhs : contractFloor K * (n0 : ℚ) + ((3 : ℚ) / 2) ^ M < (n0 : ℚ) := by
    have hq : (0 : ℚ) < (2 : ℚ) ^ (K - 1) := by positivity
    dsimp [contractFloor]
    field_simp [hq.ne']
    dsimp [contractThreshold] at hthreshold
    nlinarith [hthreshold]
  exact lt_of_le_of_lt hres.2 hstrict_rhs

/-- The same conclusion for an arbitrary target factor `α` above the
    guaranteed floor `1 - 2^{-(K-1)}`: once `n₀` is large enough that
    `(3/2)^M <= (α - floor(K)) n₀`, we get `n_M <= α n₀`. -/
theorem goodTrajectory_contracts_to_alpha
    (K M : Nat) (B : ℚ) (hB : 0 < B) {n0 : Nat} {α : ℚ}
    (hnodd : n0 % 2 = 1) (hnpos : 0 < n0)
    (hA : (valList n0 M).sum + 1 ≤ K)
    (hgood : (⟨n0 % 2 ^ K, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ K)) ∈
      goodTrajectoryF K M B)
    (hthreshold : contractThreshold K M < (n0 : ℚ))
    (hαfloor : contractFloor K ≤ α)
    (hαn : ((3 : ℚ) / 2) ^ M ≤ (α - contractFloor K) * (n0 : ℚ)) :
    (syracuseOrbit n0 M : ℚ) ≤ α * (n0 : ℚ) := by
  have hvals := goodTrajectory_vals_of_residue K M B hnodd hA hgood
  have hres := bounded_and_contracts_of_vals n0 M K B (valList n0 M)
    hnodd hnpos (valList_ValSeq n0 M) (valList_length n0 M) hA
    hvals.1 hvals.2 hthreshold
  have hdiff : 0 ≤ α - contractFloor K := by linarith
  have hnq : 0 ≤ (n0 : ℚ) := by positivity
  nlinarith [hres.2, mul_le_mul_of_nonneg_right hαfloor hnq, hαn]

#print axioms goodTrajectory_vals_of_residue
#print axioms goodTrajectory_bounded_and_contracts
#print axioms goodTrajectory_contracts_to_alpha
#print axioms goodTrajectory_card_lower
#print axioms bounded_and_contracts_of_vals
#print axioms valList_eq_of_ValSeq
#print axioms mem_syracuseFailF_iff_valList
#print axioms not_mem_syracuseFailF_contracts
#print axioms not_mem_excursionFailF_no_excursion
#print axioms oddFin_card_ge

end LogDensityContraction
end CollatzAdicBase
