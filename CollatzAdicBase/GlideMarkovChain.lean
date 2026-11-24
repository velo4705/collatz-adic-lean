import CollatzAdicBase.StoppingTimeDensity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-!
# Finite-state 2-adic survivor branching operator (Paper 8)

The accelerated Collatz half-step performs exactly one halving:

    S(n) = n/2        (n even),        S(n) = (3*n+1)/2   (n odd).

The K-bit parity vector b_i = S^i(n) mod 2 is a function of n mod 2^K
(Terras): lifting r to r and r + 2^K appends one bit, 0 for one child and
1 for the other.  Odd steps contribute log_2(3/2), pure halvings contribute
log_2(1/2) = -1, with mean (1/2) log_2(3/4) < 0.

We formalize

  * the exact product identity  2^K S^K(n) = 3^{w_K(n)} n + c_K(n), c_K < 3^K;
  the drop criterion 3^{w_K(n)} < 2^K, n >= 3^K implies S^K(n) < n;
  * the parity-vector map and its injectivity modulo 2^K (Terras's theorem),
  plus the exact child relation S^j(r + 2^j) = S^j(r) + 3^{w_j(r)};
  * the combinatorial binomial tail bound (a tilt argument):
  heavyCount K m * 2^m <= 3^K, and the explicit exponential decay at K = 8t.

All theorems are proved with core Lean axioms only: no `sorry`, no `admit`,
no custom axioms.
-/

namespace CollatzAdicBase

namespace GlideMarkovChain

-- =========================================================================
-- Section 1 — the accelerated trajectory and the exact product identity
-- =========================================================================

/-- One accelerated half-step: a halving, preceded by 3n+1 when n is odd. -/
def glideStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The value after K halvings. -/
def glideVal (n : Nat) : Nat → Nat
  | 0 => n
  | t + 1 => glideStep (glideVal n t)

/-- w_K(n): number of odd half-steps among the first K steps. -/
def glideW (n : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => glideW n t + if glideVal n t % 2 = 1 then 1 else 0

/-- c_K(n): additive constant of the exact affine product. -/
def glideC (n : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => if glideVal n t % 2 = 0 then glideC n t else 3 * glideC n t + 2 ^ t

lemma glideStep_even (n : Nat) (h : n % 2 = 0) : glideStep n = n / 2 := by
  simp [glideStep, h]

lemma glideStep_odd (n : Nat) (h : n % 2 = 1) : glideStep n = (3 * n + 1) / 2 := by
  simp [glideStep, h]

lemma three_pow_mod_two (w : Nat) : 3 ^ w % 2 = 1 := by
  induction w with
  | zero => decide
  | succ w ih =>
      rw [Nat.pow_succ]
      omega

/-- EXACT product identity: 2^K S^K(n) = 3^{w_K(n)} n + c_K(n). -/
theorem glide_identity (n K : Nat) :
    2 ^ K * glideVal n K = 3 ^ glideW n K * n + glideC n K := by
  induction K with
  | zero => simp [glideVal, glideW, glideC]
  | succ t ih =>
      by_cases hp : glideVal n t % 2 = 0
      · have hx : 2 * (glideVal n t / 2) = glideVal n t :=
          Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hp)
        simp [glideVal, glideStep, glideW, glideC, hp, Nat.pow_succ]
        calc
          2 ^ t * 2 * (glideVal n t / 2) = 2 ^ t * (2 * (glideVal n t / 2)) := by
            rw [Nat.mul_assoc]
          _ = 2 ^ t * glideVal n t := by rw [hx]
          _ = 3 ^ glideW n t * n + glideC n t := ih
      · have hp1 : glideVal n t % 2 = 1 := by omega
        have hmod : (3 * glideVal n t + 1) % 2 = 0 := by omega
        have hx : 2 * ((3 * glideVal n t + 1) / 2) = 3 * glideVal n t + 1 :=
          Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
        simp [glideVal, glideStep, glideW, glideC, hp1, Nat.pow_succ]
        calc
          2 ^ t * 2 * ((3 * glideVal n t + 1) / 2)
              = 2 ^ t * (2 * ((3 * glideVal n t + 1) / 2)) := by rw [Nat.mul_assoc]
          _ = 2 ^ t * (3 * glideVal n t + 1) := by rw [hx]
          _ = 3 * (2 ^ t * glideVal n t) + 2 ^ t := by ring
          _ = 3 * (3 ^ glideW n t * n + glideC n t) + 2 ^ t := by rw [ih]
          _ = (3 ^ glideW n t * 3) * n + (3 * glideC n t + 2 ^ t) := by ring

lemma two_le_three_pow (t : Nat) : 2 ^ t ≤ 3 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih (by omega)

/-- The additive constant obeys the sharp bound c_K <= 3^K - 2^K. -/
theorem glideC_bound (n K : Nat) : glideC n K + 2 ^ K ≤ 3 ^ K := by
  induction K with
  | zero => simp [glideC]
  | succ t ih =>
      by_cases hp : glideVal n t % 2 = 0
      · have hc : glideC n (t + 1) = glideC n t := by simp [glideC, hp]
        rw [hc, Nat.pow_succ, Nat.pow_succ]
        have hle := two_le_three_pow t
        omega
      · have hp1 : glideVal n t % 2 = 1 := by omega
        have hc : glideC n (t + 1) = 3 * glideC n t + 2 ^ t := by simp [glideC, hp1]
        rw [hc, Nat.pow_succ, Nat.pow_succ]
        omega

theorem glideC_lt (n K : Nat) : glideC n K < 3 ^ K := by
  have h := glideC_bound n K
  have hp : 0 < 2 ^ K := Nat.pow_pos (by omega)
  omega

/-- DROP CRITERION: if 3^{w_K(n)} < 2^K and n >= 3^K, then S^K(n) < n. -/
theorem glide_drop (n K : Nat) (hsmall : 3 ^ glideW n K < 2 ^ K) (hn : 3 ^ K ≤ n) :
    glideVal n K < n := by
  have hid := glide_identity n K
  have hc := glideC_lt n K
  have hle : 3 ^ glideW n K ≤ 2 ^ K - 1 := by omega
  have hprod : 3 ^ glideW n K * n + glideC n K < 2 ^ K * n := by
    calc
      3 ^ glideW n K * n + glideC n K < 3 ^ glideW n K * n + 3 ^ K :=
        Nat.add_lt_add_left hc _
      _ ≤ (2 ^ K - 1) * n + n := Nat.add_le_add (Nat.mul_le_mul_right n hle) hn
      _ = 2 ^ K * n := by
        have hpos : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by omega)
        calc
          (2 ^ K - 1) * n + n = (2 ^ K - 1) * n + 1 * n := by simp
          _ = ((2 ^ K - 1) + 1) * n := by rw [Nat.add_mul]
          _ = 2 ^ K * n := by rw [Nat.sub_add_cancel hpos]
  have hlt : 2 ^ K * glideVal n K < 2 ^ K * n := by rwa [hid]
  exact (Nat.mul_lt_mul_left (Nat.pow_pos (by omega : 0 < 2))).mp hlt

-- =========================================================================
-- Section 2 — parity-vector map, Terras injectivity, child branching
-- =========================================================================

/-- Two arguments have the same first K parity bits. -/
def sameParity (r s K : Nat) : Prop :=
  ∀ i, i < K → glideVal r i % 2 = glideVal s i % 2

/-- The coefficients depend only on the parity vector. -/
theorem sameParity_coeffs {r s K : Nat} (h : sameParity r s K) :
    glideW r K = glideW s K ∧ glideC r K = glideC s K := by
  induction K with
  | zero => simp [glideW, glideC]
  | succ K ih =>
      have h' : sameParity r s K := by intro i hi; exact h i (by omega)
      rcases ih h' with ⟨hw, hc⟩
      have hpar : glideVal r K % 2 = glideVal s K % 2 := h K (by omega)
      by_cases hr : glideVal r K % 2 = 0
      · have hs : glideVal s K % 2 = 0 := by omega
        simp [glideW, glideC, hr, hs, hw, hc]
      · have hr1 : glideVal r K % 2 = 1 := by omega
        have hs1 : glideVal s K % 2 = 1 := by omega
        simp [glideW, glideC, hr1, hs1, hw, hc]

/-- Congruence modulo 2^K forces agreement of the first K parities. -/
theorem parity_agree_of_dvd (K : Nat) {r s : Nat} (hrs : r ≤ s) (hdiv : 2 ^ K ∣ s - r) :
    sameParity r s K := by
  induction K generalizing r s with
  | zero => intro i hi; omega
  | succ K ih =>
      have hpow : 2 ^ K ∣ 2 ^ (K + 1) := by
        exact ⟨2, by rw [Nat.pow_succ]⟩
      obtain ⟨d₀, hd₀⟩ := hdiv
      have hdivK : 2 ^ K ∣ s - r := by
        refine ⟨2 * d₀, ?_⟩
        rw [hd₀, Nat.pow_succ]
        ring
      have hsp := ih (r := r) (s := s) hrs hdivK
      rcases sameParity_coeffs hsp with ⟨hw, hc⟩
      intro i hi
      by_cases hiK : i < K
      · exact hsp i hiK
      · have hieq : i = K := by omega
        subst i
        let d := d₀
        have hs_eq : s = r + 2 ^ (K + 1) * d := by
          rw [← hd₀, Nat.add_sub_of_le hrs]
        have hcalc : 2 ^ K * glideVal s K = 2 ^ K * (glideVal r K + 2 * 3 ^ glideW r K * d) := by
          calc
            2 ^ K * glideVal s K = 3 ^ glideW s K * s + glideC s K := glide_identity s K
            _ = 3 ^ glideW r K * (r + 2 ^ (K + 1) * d) + glideC r K := by rw [← hw, ← hc, hs_eq]
            _ = (3 ^ glideW r K * r + glideC r K) + 3 ^ glideW r K * (2 ^ (K + 1) * d) := by ring
            _ = 2 ^ K * glideVal r K + 2 ^ K * (2 * 3 ^ glideW r K * d) := by
              rw [← glide_identity r K, Nat.pow_succ]
              ring
            _ = 2 ^ K * (glideVal r K + 2 * 3 ^ glideW r K * d) := by ring
        have hrel : glideVal s K = glideVal r K + 2 * 3 ^ glideW r K * d :=
          Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 2)) hcalc
        have heven : (2 * 3 ^ glideW r K * d) % 2 = 0 := by
          rw [Nat.mul_assoc]
          exact Nat.mod_eq_zero_of_dvd ⟨3 ^ glideW r K * d, rfl⟩
        rw [hrel, Nat.add_mod, heven]
        simp

/-- The parity-vector map b(r)_i = 1 iff S^i(r) is odd. -/
def parityMap (n K : Nat) : Fin K → Bool :=
  fun i => decide (glideVal n i.val % 2 = 1)

/-- The injective part of Terras: with s <= r, equality of the first K
    parities gives r = s modulo 2^K. -/
private theorem parity_eq_of_le (K : Nat) {r s : Nat} (hr : r < 2 ^ K) (hsr : s ≤ r)
    (hsp : sameParity r s K) : r = s := by
  rcases sameParity_coeffs hsp with ⟨hw, hc⟩
  have hd1 : 2 ^ K ∣ 3 ^ glideW r K * r + glideC r K := by
    rw [← glide_identity r K]
    exact ⟨glideVal r K, rfl⟩
  have hd2 : 2 ^ K ∣ 3 ^ glideW r K * s + glideC r K := by
    rw [hw, hc]
    rw [← glide_identity s K]
    exact ⟨glideVal s K, rfl⟩
  have hdsub : 2 ^ K ∣ (3 ^ glideW r K * r + glideC r K) -
      (3 ^ glideW r K * s + glideC r K) := Nat.dvd_sub hd1 hd2
  have hdw : (3 ^ glideW r K * r + glideC r K) -
      (3 ^ glideW r K * s + glideC r K) = 3 ^ glideW r K * (r - s) := by
    rw [Nat.add_sub_add_right, ← Nat.mul_sub_left_distrib]
  have hdwdiv : 2 ^ K ∣ 3 ^ glideW r K * (r - s) := by rwa [hdw] at hdsub
  have hcop : Nat.Coprime (2 ^ K) (3 ^ glideW r K) := by
    have h32 : Nat.Coprime 2 3 := by decide
    exact Nat.Coprime.pow K (glideW r K) h32
  have hrsdiv : 2 ^ K ∣ r - s := Nat.Coprime.dvd_of_dvd_mul_left hcop hdwdiv
  have hlt : r - s < 2 ^ K := by omega
  have hzero : r - s = 0 := Nat.eq_zero_of_dvd_of_lt hrsdiv hlt
  omega

/-- Terras injectivity: the K-bit parity vector determines r mod 2^K. -/
theorem parityMap_injective_mod (K : Nat) {r s : Nat} (hr : r < 2 ^ K) (hs : s < 2 ^ K)
    (h : parityMap r K = parityMap s K) : r = s := by
  have hsp : sameParity r s K := by
    intro i hi
    have hb := congrFun h ⟨i, hi⟩
    simp [parityMap] at hb
    by_cases ha : glideVal r i % 2 = 1 <;> by_cases hb' : glideVal s i % 2 = 1 <;>
      simp [ha, hb'] at hb ⊢ <;> omega
  by_cases hsr : s ≤ r
  · exact parity_eq_of_le K hr hsr hsp
  · have hrs : r ≤ s := by omega
    exact (parity_eq_of_le K hs hrs (by intro i hi; exact (hsp i hi).symm)).symm

/-- EXACT CHILD RELATION: the two children r and r + 2^j of a class mod 2^j
    satisfy S^j(r + 2^j) = S^j(r) + 3^{w_j(r)}.  Since 3^w is odd, the next
    parity bit of the two children is different: one odd step, one halving. -/
theorem glideVal_child (j : Nat) {r : Nat} (hr : r < 2 ^ j) :
    glideVal (r + 2 ^ j) j = glideVal r j + 3 ^ glideW r j := by
  have hrs : r ≤ r + 2 ^ j := by omega
  have hdiv : 2 ^ j ∣ (r + 2 ^ j) - r := by
    rw [Nat.add_sub_cancel_left]
  have hsp := parity_agree_of_dvd j hrs hdiv
  rcases sameParity_coeffs hsp with ⟨hw, hc⟩
  have hidr := glide_identity r j
  have hcalc : 2 ^ j * glideVal (r + 2 ^ j) j =
      2 ^ j * (glideVal r j + 3 ^ glideW r j) := by
    calc
      2 ^ j * glideVal (r + 2 ^ j) j =
          3 ^ glideW (r + 2 ^ j) j * (r + 2 ^ j) + glideC (r + 2 ^ j) j :=
        glide_identity (r + 2 ^ j) j
      _ = 3 ^ glideW r j * (r + 2 ^ j) + glideC r j := by rw [← hw, ← hc]
      _ = (3 ^ glideW r j * r + glideC r j) + 3 ^ glideW r j * 2 ^ j := by ring
      _ = 2 ^ j * glideVal r j + 2 ^ j * 3 ^ glideW r j := by
        rw [← hidr]
        ring
      _ = 2 ^ j * (glideVal r j + 3 ^ glideW r j) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 2)) hcalc

/-- If the current child bit is 0, the upper child gains one odd step. -/
theorem glideW_child_even (j r : Nat) (hr : r < 2 ^ j) (hp : glideVal r j % 2 = 0) :
    glideW (r + 2 ^ j) (j + 1) = glideW r (j + 1) + 1 := by
  have hv := glideVal_child j hr
  have hrs : r ≤ r + 2 ^ j := by omega
  have hdiv : 2 ^ j ∣ (r + 2 ^ j) - r := by
    refine ⟨1, ?_⟩
    simp
  have hw := (sameParity_coeffs (parity_agree_of_dvd j hrs hdiv)).1
  have hodd : glideVal (r + 2 ^ j) j % 2 = 1 := by
    rw [hv, Nat.add_mod, hp, three_pow_mod_two]
  simp [glideW, hp, hodd, hw]

/-- If the current child bit is 1, the lower child gains one odd step. -/
theorem glideW_child_odd (j r : Nat) (hr : r < 2 ^ j) (hp : glideVal r j % 2 = 1) :
    glideW r (j + 1) = glideW (r + 2 ^ j) (j + 1) + 1 := by
  have hv := glideVal_child j hr
  have hrs : r ≤ r + 2 ^ j := by omega
  have hdiv : 2 ^ j ∣ (r + 2 ^ j) - r := by
    refine ⟨1, ?_⟩
    simp
  have hw := (sameParity_coeffs (parity_agree_of_dvd j hrs hdiv)).1
  have heven : glideVal (r + 2 ^ j) j % 2 = 0 := by
    rw [hv, Nat.add_mod, hp, three_pow_mod_two]
  simp [glideW, hp, heven, hw]

-- =========================================================================
-- Section 3 — combinatorial binomial tail bound
-- =========================================================================

/-- Popcount of a parity bitstring. -/
def ones : List Bool → Nat
  | [] => 0
  | b :: bs => ones bs + if b then 1 else 0

/-- All 2^K parity bitstrings of length K, generated by the branching operator
    (each class splits into a false child and a true child). -/
def allBits : Nat → List (List Bool)
  | 0 => [[]]
  | K + 1 => (allBits K).flatMap (fun bs => [false :: bs, true :: bs])

/-- Number of length-K bitstrings with at least m ones; this is the exact
    binomial tail  sum_{j >= m} choose(K,j). -/
def heavyCount : Nat → Nat → Nat
  | 0, m => if m = 0 then 1 else 0
  | K + 1, m => heavyCount K m + heavyCount K (m - 1)

/-- COMBINATORIAL CHERNOFF TILT: heavyCount K m * 2^m <= 3^K.
    Proof: sum 2^{weight(b)} over all bitstrings is 3^K, and every heavy
    bitstring contributes at least 2^m. -/
theorem heavyCount_tilt (K m : Nat) : heavyCount K m * 2 ^ m ≤ 3 ^ K := by
  induction K generalizing m with
  | zero =>
      by_cases hm : m = 0
      · subst m; simp [heavyCount]
      · simp [heavyCount, hm]
  | succ K ih =>
      rw [heavyCount, Nat.pow_succ]
      have h1 := ih m
      have h2 := ih (m - 1)
      by_cases hm : m = 0
      · subst m
        simp at h1 h2 ⊢
        omega
      · have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
          cases m with
          | zero => omega
          | succ m' => rw [Nat.pow_succ]; simp
        rw [hpow] at h1 ⊢
        rw [Nat.add_mul]
        have hmul2 : heavyCount K (m - 1) * (2 ^ (m - 1) * 2) =
            2 * (heavyCount K (m - 1) * 2 ^ (m - 1)) := by ring
        rw [hmul2]
        omega

/-- At K = 8t the survivor threshold 3^w > 2^K forces w >= 5t+1 because
    3^5 = 243 < 256 = 2^8.  The tilt bound then gives an explicit contraction. -/
theorem heavyCount_exp (t : Nat) :
    heavyCount (8 * t) (5 * t + 1) * (2 * 32 ^ t) ≤ 6561 ^ t := by
  have h := heavyCount_tilt (8 * t) (5 * t + 1)
  have h2 : 2 ^ (5 * t + 1) = 2 * 32 ^ t := by
    rw [Nat.pow_succ, pow_mul]
    ring
  have h3 : 3 ^ (8 * t) = 6561 ^ t := by
    rw [pow_mul]
    norm_num
  simpa [h2, h3] using h

-- =========================================================================
-- Section 4 — from residues to bitstrings; the survivor density bound
-- =========================================================================

/-- The K-bit parity vector as a chronological list of bits. -/
def parityList (n K : Nat) : List Bool :=
  (List.range K).map (fun i => decide (glideVal n i % 2 = 1))

lemma parityList_length (n K : Nat) : (parityList n K).length = K := by
  simp [parityList]

lemma ones_append (l₁ l₂ : List Bool) : ones (l₁ ++ l₂) = ones l₁ + ones l₂ := by
  induction l₁ with
  | nil => simp [ones]
  | cons b bs ih =>
      simp [ones, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma ones_parityList (n K : Nat) : ones (parityList n K) = glideW n K := by
  induction K with
  | zero => simp [parityList, ones, glideW]
  | succ K ih =>
      unfold parityList
      rw [List.range_succ, List.map_append, ones_append]
      change ones (parityList n K) + ones [decide (glideVal n K % 2 = 1)] =
        glideW n K + (if glideVal n K % 2 = 1 then 1 else 0)
      rw [ih]
      by_cases hp : glideVal n K % 2 = 1 <;> simp [hp, ones]

/-- All 2^K parity bitstrings of length K. -/
def allBitsF : Nat → Finset (List Bool)
  | 0 => {[]}
  | K + 1 => (allBitsF K).image (fun bs => false :: bs) ∪
             (allBitsF K).image (fun bs => true :: bs)

lemma mem_allBitsF (K : Nat) (bs : List Bool) : bs ∈ allBitsF K ↔ bs.length = K := by
  induction K generalizing bs with
  | zero => simp [allBitsF]
  | succ K ih =>
      constructor
      · intro h
        simp [allBitsF] at h
        rcases h with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
        · simpa using (ih t).1 ht
        · simpa using (ih t).1 ht
      · intro hlen
        cases bs with
        | nil => simp at hlen
        | cons b bs' =>
            have htlen : bs'.length = K := by simpa using hlen
            have htmem : bs' ∈ allBitsF K := (ih bs').2 htlen
            cases b <;> simp [allBitsF, htmem]

/-- The heavy bitstrings (at least m ones). -/
def heavyF (K m : Nat) : Finset (List Bool) :=
  (allBitsF K).filter (fun bs => decide (m ≤ ones bs))

lemma le_ones_succ (m a : Nat) : m ≤ a + 1 ↔ m - 1 ≤ a := by omega

/-- The heavy-string count agrees with the recursive binomial tail. -/
lemma heavyF_card (K m : Nat) : (heavyF K m).card = heavyCount K m := by
  induction K generalizing m with
  | zero =>
      by_cases hm : m = 0
      · subst m; simp [heavyF, allBitsF, heavyCount, ones]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hpfalse : ¬ m ≤ ones ([] : List Bool) := by simpa [ones] using (Nat.not_le_of_gt hmpos)
        have hf : ({[]} : Finset (List Bool)).filter (fun x => decide (m ≤ ones x)) = ∅ := by
          ext x
          constructor
          · intro hx
            simp only [Finset.mem_filter, Finset.mem_singleton] at hx
            rcases hx with ⟨rfl, hpred⟩
            have hpred' : m ≤ ones ([] : List Bool) := by simpa using hpred
            exact (hpfalse hpred').elim
          · intro hx
            cases hx
        rw [heavyF, allBitsF, hf]
        simp [heavyCount, hm]
  | succ K ih =>
      have hdisj : Disjoint ((allBitsF K).image fun bs => false :: bs)
          ((allBitsF K).image fun bs => true :: bs) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        simp at ha hb
        rcases ha with ⟨x, hx, rfl⟩
        rcases hb with ⟨y, hy, hxy⟩
        simp at hxy
      simp only [heavyF, allBitsF]
      rw [Finset.filter_union, Finset.card_union_of_disjoint]
      · rw [Finset.filter_image, Finset.filter_image]
        rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
        rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
        simp only [ones, Bool.false_eq_true, ite_false, ite_true, add_zero, zero_add]
        have hfilter : (allBitsF K).filter (fun x => decide (m ≤ ones x + 1)) =
            (allBitsF K).filter (fun x => decide (m - 1 ≤ ones x)) := by
          apply Finset.ext
          intro x
          simp only [Finset.mem_filter, decide_eq_true_eq]
          constructor <;> intro h
          · exact ⟨h.1, (le_ones_succ m (ones x)).mp h.2⟩
          · exact ⟨h.1, (le_ones_succ m (ones x)).mpr h.2⟩
        rw [hfilter]
        change (heavyF K m).card + (heavyF K (m - 1)).card = heavyCount K m + heavyCount K (m - 1)
        rw [ih m, ih (m - 1)]
      · rw [Finset.disjoint_left]
        intro a ha hb
        have ha' : a ∈ (allBitsF K).image (fun bs => false :: bs) := (Finset.mem_filter.mp ha).1
        have hb' : a ∈ (allBitsF K).image (fun bs => true :: bs) := (Finset.mem_filter.mp hb).1
        rw [Finset.disjoint_left] at hdisj
        exact hdisj ha' hb'

/-- A residue class modulo 2^K is determined by its parity bitstring. -/
lemma parityList_injective (K : Nat) :
    Function.Injective (fun r : Fin (2 ^ K) => parityList r.val K) := by
  intro a b h
  apply Fin.ext
  apply parityMap_injective_mod K a.isLt b.isLt
  funext i
  have hidx := congrArg (fun l : List Bool => l[i.val]?) h
  simp [parityList] at hidx
  by_cases ha : glideVal a.val i.val % 2 = 1 <;> by_cases hb : glideVal b.val i.val % 2 = 1 <;>
    simp [parityMap, ha, hb] at hidx ⊢

/-- Residue classes mod 2^K whose weight is at least m, as a Finset. -/
def survF (K m : Nat) : Finset (Fin (2 ^ K)) :=
  Finset.univ.filter (fun r => decide (m ≤ glideW r.val K))

def oddSurvF (K m : Nat) : Finset (Fin (2 ^ K)) :=
  Finset.univ.filter (fun r => decide (r.val % 2 = 1 ∧ m ≤ glideW r.val K))

lemma oddSurvF_le_survF (K m : Nat) : (oddSurvF K m).card ≤ (survF K m).card := by
  apply Finset.card_le_card
  intro r hr
  simp [oddSurvF, survF] at hr ⊢
  exact hr.2

/-- TERRAS COUNTING BOUND: at most heavyCount K m residue classes mod 2^K
    have weight >= m.  Combined with the tilt bound this is the finite-state
    Chernoff bound for the 2-adic survivor branching operator. -/
theorem survF_card_le_heavy (K m : Nat) : (survF K m).card ≤ heavyCount K m := by
  let pv : Fin (2 ^ K) → List Bool := fun r => parityList r.val K
  have hinj : Function.Injective pv := parityList_injective K
  have hcard := Finset.card_image_of_injective (survF K m) hinj
  have hsub : Finset.image pv (survF K m) ⊆ heavyF K m := by
    intro bs hb
    rcases Finset.mem_image.mp hb with ⟨r, hr, rfl⟩
    simp [survF] at hr
    simp [heavyF]
    constructor
    · exact (mem_allBitsF K (parityList r.val K)).2 (parityList_length r.val K)
    · simpa [pv, ones_parityList] using hr
  calc
    (survF K m).card = (Finset.image pv (survF K m)).card := hcard.symm
    _ ≤ (heavyF K m).card := Finset.card_le_card hsub
    _ = heavyCount K m := heavyF_card K m

/-- EXPONENTIAL DECAY of the odd-survivor density.  At K = 8t, the
    constructive bound is (odd survivors) * 2 * 32^t <= 6561^t, i.e.
    delta(8t) <= (6561/8192)^t = exp(-0.0277... * K). -/
theorem odd_survivor_decay (t : Nat) :
    (oddSurvF (8 * t) (5 * t + 1)).card * (2 * 32 ^ t) ≤ 6561 ^ t := by
  have h1 : (oddSurvF (8 * t) (5 * t + 1)).card ≤ heavyCount (8 * t) (5 * t + 1) :=
    le_trans (oddSurvF_le_survF (8 * t) (5 * t + 1))
      (survF_card_le_heavy (8 * t) (5 * t + 1))
  have hmul := Nat.mul_le_mul_right (2 * 32 ^ t) h1
  exact le_trans hmul (heavyCount_exp t)

/-- Since 3^5 = 243 < 256 = 2^8, an excessive weight w > K log_3 2 at
    K = 8t implies w >= 5t+1 (the integer threshold used above). -/
lemma three_five_le_two_eight (t : Nat) : 3 ^ (5 * t) ≤ 2 ^ (8 * t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.mul_succ, Nat.mul_succ, pow_add, pow_add]
      exact Nat.mul_le_mul ih (by decide : 3 ^ 5 ≤ 2 ^ 8)

theorem survivor_weight_bound (t r : Nat) (h : 2 ^ (8 * t) < 3 ^ glideW r (8 * t)) :
    5 * t + 1 ≤ glideW r (8 * t) := by
  by_contra hn
  have hwle : glideW r (8 * t) ≤ 5 * t := by omega
  have hp : 3 ^ glideW r (8 * t) ≤ 3 ^ (5 * t) :=
    Nat.pow_le_pow_right (by omega : 0 < 3) hwle
  have hle := three_five_le_two_eight t
  omega

/-- The literal Terras survivors: odd r mod 2^K whose accelerated image at
    K halvings has multiplier 3^{w_K}/2^K > 1. -/
def trueSurvF (K : Nat) : Finset (Fin (2 ^ K)) :=
  Finset.univ.filter (fun r => decide (r.val % 2 = 1 ∧ 2 ^ K < 3 ^ glideW r.val K))

/-- MAIN DENSITY THEOREM (Terras, finite-state form): the density of odd
    residues whose K-step product multiplier exceeds 1 decays exponentially:
    at K = 8t, (survivors) * 2 * 32^t <= 6561^t, i.e. delta(8t) <= (6561/8192)^t. -/
theorem true_survivor_decay (t : Nat) :
    (trueSurvF (8 * t)).card * (2 * 32 ^ t) ≤ 6561 ^ t := by
  have hsub : trueSurvF (8 * t) ⊆ oddSurvF (8 * t) (5 * t + 1) := by
    intro r hr
    simp [trueSurvF, oddSurvF] at hr ⊢
    exact ⟨hr.1, survivor_weight_bound t r.val hr.2⟩
  have hcard := Finset.card_le_card hsub
  have hodd : (oddSurvF (8 * t) (5 * t + 1)).card ≤ heavyCount (8 * t) (5 * t + 1) :=
    le_trans (oddSurvF_le_survF (8 * t) (5 * t + 1))
      (survF_card_le_heavy (8 * t) (5 * t + 1))
  have h1 : (trueSurvF (8 * t)).card ≤ heavyCount (8 * t) (5 * t + 1) :=
    le_trans hcard hodd
  exact le_trans (Nat.mul_le_mul_right (2 * 32 ^ t) h1) (heavyCount_exp t)

-- Axiom audit for this module.
#print axioms glide_identity
#print axioms glideC_bound
#print axioms glide_drop
#print axioms parity_agree_of_dvd
#print axioms parityMap_injective_mod
#print axioms glideVal_child
#print axioms heavyCount_tilt
#print axioms heavyCount_exp
#print axioms heavyF_card
#print axioms parityList_injective
#print axioms survF_card_le_heavy
#print axioms odd_survivor_decay
#print axioms true_survivor_decay

end GlideMarkovChain
end CollatzAdicBase
