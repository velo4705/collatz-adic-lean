import CollatzAdicBase.SyracuseLogDrift
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# Syracuse renewal and exponential concentration of multi-step products (Layer 5)

For odd `n` the accelerated Syracuse step has valuation `a = v2(3n+1) >= 1`.
Under the exact geometric law `exactValF_card` the valuations along the orbit
are i.i.d. geometric with `P(a = j) = 2^{-j}`, `E[a] = 2`.  Since the
non-contraction event `3^M >= 2^{A_M}` is the left large deviation
`A_M <= M log_2 3 < 2M`, a Chernoff/Cramer tilt yields an exponential bound.

We formalize here:

* the exact relation between accelerated valuations and the half-step parity
  weight `glideW`: if `ValSeq n as` with `n` odd then `glideW n (sum as) = as.length`;
* the exact composition count `compCount M E = (E-1).choose (M-1)`;
* the exponential decay theorem: at `M = 5t` the failing odd classes mod
  `2^(8t)` inject into the Terras survivors `oddSurvF (8t) (5t+1)`, hence
      `card * (2 * 32^t) <= 6561^t`,
  i.e. the failing fraction is at most `(6561/8192)^t <= (24/25)^(5t)`.

All theorems use core Lean axioms only: no `sorry`, no `admit`, no custom
axioms.
-/

namespace CollatzAdicBase

namespace SyracuseRenewal

open SyracuseLogDrift
open GlideMarkovChain

-- =========================================================================
-- Section 1 -- accelerated valuations versus half-step parity runs
-- =========================================================================

/-- During the first `a` half-steps after an odd `m` with `v2(3m+1) = a` the
    glide value is exactly `(3m+1)/2^j`. -/
lemma glideVal_eq_div_pow_of_v2 {m a j : Nat} (hv : v2 (3 * m + 1) = a)
    (hj : j ≤ a) :
    glideVal m j = if j = 0 then m else (3 * m + 1) / 2 ^ j := by
  induction j with
  | zero => simp [glideVal]
  | succ j ih =>
      have hjle : j ≤ a := by omega
      have ih' := ih hjle
      have hdvd2a : 2 ^ a ∣ 3 * m + 1 := (v2_eq_iff (by omega)).mp hv |>.1
      by_cases hjz : j = 0
      · subst j
        have hm : m % 2 = 1 := by
          have h2a : 2 ∣ 2 ^ a := ⟨2 ^ (a - 1), by
            rw [show a = 1 + (a - 1) by omega, pow_add]
            norm_num⟩
          have h2 : 2 ∣ 3 * m + 1 := dvd_trans h2a hdvd2a
          omega
        simp [glideVal, ih', glideStep_odd m hm]
      · have hdvd2j : 2 ^ j ∣ 3 * m + 1 :=
          dvd_trans (Nat.pow_dvd_pow 2 hjle) hdvd2a
        have hdvd2j1 : 2 ^ (j + 1) ∣ 3 * m + 1 :=
          dvd_trans (Nat.pow_dvd_pow 2 (by omega : j + 1 ≤ a)) hdvd2a
        have heven : ((3 * m + 1) / 2 ^ j) % 2 = 0 := by
          rw [← Nat.dvd_iff_mod_eq_zero]
          exact (Nat.dvd_div_iff_mul_dvd hdvd2j).mpr (by
            simpa [pow_succ, mul_comm] using hdvd2j1)
        have hstep : glideStep ((3 * m + 1) / 2 ^ j) = (3 * m + 1) / 2 ^ j / 2 :=
          glideStep_even _ heven
        change glideStep (glideVal m j) = (3 * m + 1) / 2 ^ (j + 1)
        rw [ih', ite_eq_right hjz]
        calc
          glideStep ((3 * m + 1) / 2 ^ j) = (3 * m + 1) / 2 ^ j / 2 := hstep
          _ = (3 * m + 1) / (2 ^ j * 2) := Nat.div_div_eq_div_mul _ _ _
          _ = (3 * m + 1) / 2 ^ (j + 1) := by rw [pow_succ]

/-- After exactly `a` half-steps the glide value is the accelerated Syracuse
    image. -/
lemma glideVal_v2_eq_step {m a : Nat} (hm : m % 2 = 1) (hv : v2 (3 * m + 1) = a) :
    glideVal m a = syracuseStep m := by
  have ha : 1 ≤ a := by simpa [hv] using one_le_v2_three hm
  rw [glideVal_eq_div_pow_of_v2 hv le_rfl]
  rw [ite_eq_right (by omega : ¬ a = 0)]
  have hstep := syracuseStep_mul_pow_v2 m
  rw [← hstep, hv]
  exact Nat.mul_div_left (syracuseStep m) (by positivity)

/-- Only the initial value is odd during the first `a` half-steps. -/
lemma glideW_le_v2 {m a : Nat} (hm : m % 2 = 1) (hv : v2 (3 * m + 1) = a) :
    ∀ i, i ≤ a → glideW m i = if i = 0 then 0 else 1 := by
  intro i
  induction i with
  | zero => simp [glideW]
  | succ i ih =>
      intro hsucc
      have hile : i ≤ a := by omega
      have ih' := ih hile
      by_cases hi0 : i = 0
      · subst i
        simp [glideW, glideVal, hm]
      · have hdvd2a : 2 ^ a ∣ 3 * m + 1 := (v2_eq_iff (by omega)).mp hv |>.1
        have hdvd2i1 : 2 ^ (i + 1) ∣ 3 * m + 1 :=
          dvd_trans (Nat.pow_dvd_pow 2 (by omega : i + 1 ≤ a)) hdvd2a
        have hdvd2i : 2 ^ i ∣ 3 * m + 1 :=
          dvd_trans (Nat.pow_dvd_pow 2 (by omega : i ≤ a)) hdvd2a
        have heven : glideVal m i % 2 = 0 := by
          rw [glideVal_eq_div_pow_of_v2 hv hile]
          rw [ite_eq_right hi0]
          rw [← Nat.dvd_iff_mod_eq_zero]
          exact (Nat.dvd_div_iff_mul_dvd hdvd2i).mpr (by
            simpa [pow_succ, mul_comm] using hdvd2i1)
        simp [glideW, hi0, ih', heven]

lemma glideW_v2_eq_one {m a : Nat} (hm : m % 2 = 1) (hv : v2 (3 * m + 1) = a) :
    glideW m a = 1 := by
  have ha : a ≠ 0 := by
    intro h
    subst a
    have hle := one_le_v2_three hm
    omega
  simpa [ha] using glideW_le_v2 hm hv a le_rfl

/-- Shifting by the `a` half-steps of one accelerated step: glide values. -/
lemma glideVal_add_v2 {m a t : Nat} (hm : m % 2 = 1) (hv : v2 (3 * m + 1) = a) :
    glideVal m (a + t) = glideVal (syracuseStep m) t := by
  induction t with
  | zero => simp [glideVal, glideVal_v2_eq_step hm hv]
  | succ t ih =>
      rw [Nat.add_succ, glideVal, ih]
      rfl

/-- Shifting by the `a` half-steps of one accelerated step: parity weights. -/
lemma glideW_add_v2 {m a t : Nat} (hm : m % 2 = 1) (hv : v2 (3 * m + 1) = a) :
    glideW m (a + t) = 1 + glideW (syracuseStep m) t := by
  induction t with
  | zero => simp [glideW, glideW_v2_eq_one hm hv]
  | succ t ih =>
      rw [Nat.add_succ, glideW, ih]
      rw [glideVal_add_v2 hm hv (t := t)]
      change 1 + glideW (syracuseStep m) t +
          (if glideVal (syracuseStep m) t % 2 = 1 then 1 else 0) =
        1 + (glideW (syracuseStep m) t +
          (if glideVal (syracuseStep m) t % 2 = 1 then 1 else 0))
      omega

/-- THE RENEWAL IDENTITY: at the accelerated times `A_j` the half-step orbit
    and parity weight agree with the accelerated orbit and step count. -/
lemma glide_at_acc_times (n : Nat) (as : List Nat) (hm : n % 2 = 1)
    (hval : ValSeq n as) :
    ∀ j, j ≤ as.length →
      glideVal n (syracuseA as j) = syracuseOrbit n j ∧
      glideW n (syracuseA as j) = j := by
  induction as generalizing n with
  | nil =>
      intro j hj
      have hj0 : j = 0 := by simp at hj; omega
      subst j
      simp [glideVal, glideW, syracuseA, syracuseOrbit]
  | cons a as ih =>
      simp [ValSeq] at hval
      rcases hval with ⟨hv, hval'⟩
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        simp [glideVal, glideW, syracuseA, syracuseOrbit]
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        have hj'le : j' ≤ as.length := by simp at hj; omega
        have ih' := ih (syracuseStep n) (syracuseStep_odd n) hval' j' hj'le
        constructor
        · rw [syracuseA, glideVal_add_v2 hm hv, ih'.1, syracuseOrbit_succ]
        · rw [syracuseA, glideW_add_v2 hm hv, ih'.2]
          omega

/-- `glideW` is monotone in the time argument. -/
lemma glideW_mono (n s t : Nat) (h : s ≤ t) : glideW n s ≤ glideW n t := by
  induction h with
  | refl => rfl
  | @step t hst ih =>
      rw [glideW]
      exact Nat.le_add_right_of_le ih

/-- One past the final accelerated time the parity weight has increased by
    one (the accelerated image is odd). -/
lemma glideW_sum_succ {n : Nat} {as : List Nat} (hm : n % 2 = 1) (hval : ValSeq n as) :
    glideW n (as.sum + 1) = as.length + 1 := by
  have hw0 : glideW n as.sum = as.length := by
    have h := (glide_at_acc_times n as hm hval as.length le_rfl).2
    simpa [syracuseA_length] using h
  have hoddbit : ∀ x : Nat, x % 2 = 1 → syracuseOrbit x as.length % 2 = 1 := by
    clear hval hw0
    induction as with
    | nil => intro x hx; simpa [syracuseOrbit] using hx
    | cons a as ih =>
        intro x hx
        rw [List.length_cons, syracuseOrbit_succ]
        exact ih (syracuseStep x) (syracuseStep_odd x)
  have hodd : glideVal n as.sum % 2 = 1 := by
    have h := (glide_at_acc_times n as hm hval as.length le_rfl).1
    rw [syracuseA_length] at h
    rw [h]
    exact hoddbit n hm
  rw [glideW]
  simp [hodd, hw0]

-- =========================================================================
-- Section 2 -- non-contraction classes are Terras survivors
-- =========================================================================

/-- Odd residue classes mod `2^K` whose first `M` accelerated valuations fail
    to contract, i.e. `3^M >= 2^{A_M}` (with `A_M = as.sum`). -/
noncomputable def syracuseFailF (K M : Nat) : Finset (Fin (2 ^ K)) := by
  classical
  exact Finset.univ.filter (fun r => decide
    (r.val % 2 = 1 ∧ ∃ as : List Nat,
      ValSeq r.val as ∧ as.length = M ∧ 2 ^ as.sum ≤ 3 ^ M))

lemma mem_syracuseFailF {K M : Nat} {r : Fin (2 ^ K)} :
    r ∈ syracuseFailF K M ↔
      r.val % 2 = 1 ∧ ∃ as : List Nat,
        ValSeq r.val as ∧ as.length = M ∧ 2 ^ as.sum ≤ 3 ^ M := by
  simp [syracuseFailF]

/-- The exact rational certificate `3^5 = 243 < 256 = 2^8`, raised to `t`. -/
lemma three_pow_five_mul_lt {t : Nat} (ht : 1 ≤ t) : 3 ^ (5 * t) < 2 ^ (8 * t) := by
  have hbase : (3 : Nat) ^ 5 < 2 ^ 8 := by norm_num
  have h := pow_lt_pow_left₀ hbase (by norm_num : (0 : Nat) ≤ 3 ^ 5) (by omega : t ≠ 0)
  simpa [pow_mul] using h

/-- A failing residue with `M = 5t` has valuation sum `< 8t`. -/
lemma failing_sum_lt {t : Nat} (ht : 1 ≤ t) {r : Fin (2 ^ (8 * t))}
    (hr : r ∈ syracuseFailF (8 * t) (5 * t)) :
    ∃ as : List Nat, ValSeq r.val as ∧ as.length = 5 * t ∧ as.sum < 8 * t := by
  rcases (mem_syracuseFailF.mp hr).2 with ⟨as, hval, hlen, hle⟩
  refine ⟨as, hval, hlen, ?_⟩
  by_contra hnot
  have hge : 8 * t ≤ as.sum := by omega
  have hp : 2 ^ (8 * t) ≤ 2 ^ as.sum := Nat.pow_le_pow_right (by norm_num) hge
  have hsmall := three_pow_five_mul_lt ht
  omega

/-- At `M = 5t` every failing class is a Terras survivor with weight at
    least `5t+1` among the first `8t` half-steps. -/
lemma syracuseFail_subset_survivor (t : Nat) :
    syracuseFailF (8 * t) (5 * t) ⊆ GlideMarkovChain.oddSurvF (8 * t) (5 * t + 1) := by
  by_cases ht : t = 0
  · subst t
    intro r hr
    have hodd := (mem_syracuseFailF.mp hr).1
    have hrlt : r.val < 1 := by simpa using r.isLt
    omega
  · have htpos : 1 ≤ t := by omega
    intro r hr
    rcases failing_sum_lt htpos hr with ⟨as, hval, hlen, hsumlt⟩
    have hodd := (mem_syracuseFailF.mp hr).1
    have hwt : glideW r.val as.sum = as.length := by
      have h := (glide_at_acc_times r.val as hodd hval as.length le_rfl).2
      simpa [syracuseA_length] using h
    have hmono := glideW_mono r.val (as.sum + 1) (8 * t) (by omega)
    have hsucc := glideW_sum_succ hodd hval
    have hm : 5 * t + 1 ≤ glideW r.val (8 * t) := by omega
    simpa [GlideMarkovChain.oddSurvF] using And.intro hodd hm

/-- MAIN DECAY THEOREM: the number of failing odd classes obeys the Terras
    constructive Chernoff bound `card * (2 * 32^t) <= 6561^t`. -/
theorem syracuseFail_decay (t : Nat) :
    (syracuseFailF (8 * t) (5 * t)).card * (2 * 32 ^ t) ≤ 6561 ^ t := by
  have hsub := syracuseFail_subset_survivor t
  have hcard := Finset.card_le_card hsub
  have hmul := Nat.mul_le_mul_right (2 * 32 ^ t) hcard
  exact le_trans hmul (GlideMarkovChain.odd_survivor_decay t)

/-- The rational certificate `(6561/8192) <= (24/25)^5`, raised to `t`. -/
lemma rational_rate_certificate (t : Nat) :
    6561 ^ t * 25 ^ (5 * t) ≤ 24 ^ (5 * t) * 2 ^ (13 * t) := by
  have hbase : 6561 * 25 ^ 5 ≤ 24 ^ 5 * 2 ^ 13 := by norm_num
  have h := pow_le_pow_left₀ (by norm_num : (0 : Nat) ≤ 6561 * 25 ^ 5) hbase t
  simpa only [mul_pow, pow_mul] using h

/-- EXPONENTIAL DECAY WITH A CERTIFIED RATIONAL BASE: at `M = 5t` the failing
    fraction of odd classes is at most `(24/25)^(5t)`.  In integer form:
    `2 * card * 25^(5t) <= 24^(5t) * 2^(8t)`. -/
theorem syracuseFail_rational_decay (t : Nat) :
    2 * (syracuseFailF (8 * t) (5 * t)).card * 25 ^ (5 * t) ≤
      24 ^ (5 * t) * 2 ^ (8 * t) := by
  have hdecay := syracuseFail_decay t
  have hcert := rational_rate_certificate t
  have hmul := Nat.mul_le_mul_right (25 ^ (5 * t)) hdecay
  have hchain :
      (syracuseFailF (8 * t) (5 * t)).card * (2 * 32 ^ t) * 25 ^ (5 * t) ≤
        24 ^ (5 * t) * 2 ^ (13 * t) := by
    exact le_trans hmul hcert
  have h32 : (32 : Nat) ^ t = 2 ^ (5 * t) := by
    rw [pow_mul]
    norm_num
  have hpow : 2 ^ (13 * t) = 32 ^ t * 2 ^ (8 * t) := by
    rw [h32, ← pow_add]
    congr 1
    omega
  rw [hpow] at hchain
  refine Nat.le_of_mul_le_mul_right ?_ (by positivity : 0 < 32 ^ t)
  simpa [mul_assoc, mul_comm, mul_left_comm] using hchain

-- =========================================================================
-- Section 3 -- exact binomial / composition counting identity
-- =========================================================================

/-- `compCount M E`: number of `M`-tuples of positive naturals with sum `E`. -/
def compCount : Nat → Nat → Nat
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | M + 1, E + 1 => compCount M E + compCount (M + 1) E

lemma compCount_zero_right (M : Nat) : compCount M 0 = if M = 0 then 1 else 0 := by
  cases M <;> simp [compCount]

lemma compCount_succ_succ (M E : Nat) :
    compCount (M + 1) (E + 1) = compCount M E + compCount (M + 1) E := by
  rfl

lemma compCount_eq_zero_of_lt {M E : Nat} (h : E < M) : compCount M E = 0 := by
  induction E generalizing M with
  | zero =>
      simpa [compCount_zero_right] using (show M ≠ 0 by omega)
  | succ E ih =>
      have hMne : M ≠ 0 := by omega
      obtain ⟨M', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hMne
      rw [compCount_succ_succ]
      have h1 : E < M' := by omega
      have h2 : E < M' + 1 := by omega
      rw [ih h1, ih h2]

lemma compCount_self (M : Nat) : compCount M M = 1 := by
  induction M with
  | zero => simp [compCount]
  | succ M ih =>
      rw [compCount_succ_succ]
      have hz : compCount (M + 1) M = 0 := compCount_eq_zero_of_lt (by omega)
      simpa [ih, hz]

lemma compCount_one (E : Nat) : compCount 1 E = if E = 0 then 0 else 1 := by
  induction E with
  | zero => simp [compCount]
  | succ E ih =>
      rw [compCount_succ_succ]
      have h0 : compCount 0 E = if E = 0 then 1 else 0 := by
        cases E <;> simp [compCount]
      rw [h0, ih]
      by_cases hE : E = 0 <;> simp [hE]

/-- EXACT COMPOSITION COUNT: `compCount M E = choose (E-1) (M-1)`. -/
lemma compCount_eq_choose (M E : Nat) (hM : 1 ≤ M) (hME : M ≤ E) :
    compCount M E = Nat.choose (E - 1) (M - 1) := by
  induction E using Nat.strong_induction_on generalizing M with
  | ind E ih =>
      by_cases hM1 : M = 1
      · subst M
        rw [compCount_one]
        simp [show E ≠ 0 by omega]
      · have hM2 : 2 ≤ M := by omega
        obtain ⟨M', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
        obtain ⟨E', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : E ≠ 0)
        rw [compCount_succ_succ]
        have hM'pos : 1 ≤ M' := by omega
        by_cases hEq : E' = M'
        · subst E'
          rw [compCount_self, compCount_eq_zero_of_lt (by omega : M' < M' + 1)]
          simp
        · have hlt : M' < E' := by omega
          have h1 := ih E' (by omega) M' hM'pos (by omega)
          have h2 := ih E' (by omega) (M' + 1) (by omega) (by omega)
          rw [h1, h2]
          have hpascal := Nat.choose_succ_succ (E' - 1) (M' - 1)
          have hEeq : (E' - 1).succ = E' := by omega
          have hMeq : (M' - 1).succ = M' := by omega
          rw [hEeq, hMeq] at hpascal
          have hs1 : M' + 1 - 1 = M' := by omega
          have hs2 : E'.succ - 1 = E' := by omega
          have hs3 : M'.succ - 1 = M' := by omega
          exact hpascal.symm

-- =========================================================================
-- Section 4 -- exact moment generating function of the geometric law
-- =========================================================================

/-- The truncated first moment `E[x^a]` of the geometric law
    `P(a = j) = 2^{-j}` over `1 <= a <= K`. -/
def mgfPartial (x : ℚ) (K : Nat) : ℚ :=
  ∑ a ∈ Finset.range K, (x / 2) ^ (a + 1)

/-- EXACT MGF IDENTITY: `sum_{a=1}^K 2^{-a} x^a =
    x/(2-x) * (1 - (x/2)^K)`, which tends to `x/(2-x)` as `K -> infinity`. -/
lemma mgfPartial_closed (x : ℚ) (hx : x ≠ 2) (K : Nat) :
    mgfPartial x K = x / (2 - x) * (1 - (x / 2) ^ K) := by
  unfold mgfPartial
  have hr : x / 2 ≠ 1 := by
    intro h
    apply hx
    linarith
  calc
    (∑ a ∈ Finset.range K, (x / 2) ^ (a + 1)) =
        (x / 2) * (∑ a ∈ Finset.range K, (x / 2) ^ a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [pow_succ]
      ring
    _ = (x / 2) * (((x / 2) ^ K - 1) / (x / 2 - 1)) := by
      rw [geom_sum_eq hr K]
    _ = x / (2 - x) * (1 - (x / 2) ^ K) := by
      field_simp [hx]
      ring

/-- The lambda form: with `x = 2^{-lambda}` (so `u = 2^lambda = 1/x`),
    `E[2^{-lambda a}] = 1/(2^{lambda+1}-1) = 1/(2u-1)` with the exact
    finite remainder `-(1/(2u-1)) * (1/(2u))^K`. -/
lemma mgf_lambda_closed (u : ℚ) (hu : u ≠ 0) (hu2 : 2 * u - 1 ≠ 0) (K : Nat) :
    mgfPartial (1 / u) K + (1 / (2 * u - 1)) * (1 / (2 * u)) ^ K =
      1 / (2 * u - 1) := by
  have hx2 : (1 / u : ℚ) ≠ 2 := by
    intro h
    apply hu2
    field_simp [hu] at h
    linarith
  rw [mgfPartial_closed (1 / u) hx2 K]
  have hform : (1 / u) / (2 - 1 / u) = 1 / (2 * u - 1) := by
    field_simp [hu]
  have hpow : (1 / u) / 2 = 1 / (2 * u) := by
    field_simp [hu]
  rw [hform, hpow]
  ring

/-- The certified rational MGF value at `u = 21/20` (the tilt used in the
    Python Cramer bound): the exact limit is `10/11`. -/
lemma mgf_certified_value : (1 / (2 * (21 / 20 : ℚ) - 1)) = 10 / 11 := by
  norm_num

#print axioms glideVal_eq_div_pow_of_v2
#print axioms glideW_v2_eq_one
#print axioms glide_at_acc_times
#print axioms glideW_sum_succ
#print axioms syracuseFail_subset_survivor
#print axioms syracuseFail_decay
#print axioms syracuseFail_rational_decay
#print axioms compCount_eq_choose
#print axioms mgfPartial_closed
#print axioms mgf_lambda_closed

end SyracuseRenewal
end CollatzAdicBase
