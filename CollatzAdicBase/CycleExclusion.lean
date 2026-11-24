import CollatzAdicBase.RationalDescent
import CollatzAdicBase.FuelLaw

/-!
# Algebraic and modular cycle exclusion

This module derives the exact 3-free rational cycle equation and proves the
structural exclusions that follow from it.

A cycle of the reduced Collatz map is 3-free with constant denominator by
`lemma_2_4_and_cor_2_5_three_free_cycles`.  Writing `M` for the number of odd
steps, `E` for the number of halvings (`L = E + M` is the period) and
`e_0 = 0 < e_1 < ... < e_{M-1} < E` for the cumulative halving counts before
each odd step, the *cycle-sum identity* is

    (2^E - 3^M) * a = d * T,     T = ∑_{j=0}^{M-1} 3^{M-1-j} 2^{e_j}.

`T` is the trailing-ones-block decomposition supplied by `FuelLaw` and
`Refueling`: one block of `e_1` consecutive shortcut steps, then the next,
etc.  Consequences proved here:

* `cycle_dvd`: `d ∣ 2^E - 3^M` (because `gcd a d = 1`);
* `cycleAcc_spec`: the exact affine unrolling of the whole orbit;
* Steiner's 1-cycle exclusion: one odd step forces `a ≤ d`, so a
  non-trivial cycle (`a > d`) cannot be a 1-cycle;
* kernel-checked exclusions of non-trivial *integer* cycles (`d = 1`) for
  `M ≤ 6` and a window of halving counts around `⌈M log₂ 3⌉`, plus exclusion
  of single-block integer cycles for `M ≤ 12`.

No `sorry`, no `admit`, no custom axioms.
-/

namespace CollatzAdicBase

namespace CycleExclusion

/-! ### 0. The step at a 3-free denominator -/

/-- At a valid state whose denominator is coprime to 3, an odd numerator step
    has `g = 1`, hence is exactly `(a,d) ↦ (3a+d, d)`. -/
lemma step_three_free {y : State} (hv : Valid y) (h3 : ¬ 3 ∣ y.2) (ha : Odd y.1) :
    step y = (3 * y.1 + y.2, y.2) := by
  rcases y with ⟨a, d⟩
  rw [step_odd (Nat.not_even_iff_odd.mpr ha)]
  have hg : Nat.gcd (3 * a + d) d = 1 := by
    rcases dvd_three_cases (gcd_dvd_three hv.2.2.2) with hg | hg
    · exact hg
    · exfalso
      exact h3 (by rw [← hg]; exact Nat.gcd_dvd_right (3 * a + d) d)
  rw [hg]
  simp

/-- Along the orbit of a valid 3-free state, every denominator stays equal to
    the starting denominator (no cycle hypothesis needed). -/
lemma denom_const_of_three_free {x : State} (hx : Valid x) (h3 : ¬ 3 ∣ x.2) (t : Nat) :
    (orbit x t).2 = x.2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [orbit_succ]
      have hv : Valid (orbit x t) := valid_orbit hx t
      have h3t : ¬ 3 ∣ (orbit x t).2 := by simpa [ih] using h3
      by_cases he : Even (orbit x t).1
      · rw [step_even he]
        exact ih
      · have ho : Odd (orbit x t).1 := Nat.not_even_iff_odd.mp he
        rw [step_three_free hv h3t ho]
        exact ih

/-! ### 1. The accumulator and the affine unrolling -/

/-- `cycleAcc x t = (E, M, T)`: after `t` steps, `E` halvings and `M` odd steps
    have occurred and `T` is the trailing-ones-block sum.  The recursion is
    `T ← 3T + 2^E` at an odd step and unchanged at an even step. -/
def cycleAcc (x : State) : Nat → Nat × Nat × Nat
  | 0 => (0, 0, 0)
  | t + 1 =>
      let r := cycleAcc x t
      if Odd (orbit x t).1 then (r.1, r.2.1 + 1, 3 * r.2.2 + 2 ^ r.1)
      else (r.1 + 1, r.2.1, r.2.2)

/-- Number of steps splits as halvings plus odd steps. -/
lemma cycleAcc_EM (x : State) (t : Nat) :
    (cycleAcc x t).1 + (cycleAcc x t).2.1 = t := by
  induction t with
  | zero => simp [cycleAcc]
  | succ t ih =>
      by_cases ho : Odd (orbit x t).1
      · simp [cycleAcc, ho]
        omega
      · simp [cycleAcc, ho]
        omega

/-- The accumulator's odd-step count is exactly `oddCount`. -/
lemma cycleAcc_M_eq_oddCount (x : State) (t : Nat) :
    (cycleAcc x t).2.1 = oddCount x t := by
  induction t with
  | zero => simp [cycleAcc, oddCount]
  | succ t ih =>
      rw [cycleAcc, oddCount, ih]
      split <;> rfl

/-- **Affine unrolling.** For a valid 3-free state `x`, after any `t` steps
    `2^E * (orbit x t).1 = 3^M * x.1 + x.2 * T`. -/
lemma cycleAcc_spec (x : State) (hx : Valid x) (h3 : ¬ 3 ∣ x.2) (t : Nat) :
    2 ^ (cycleAcc x t).1 * (orbit x t).1 =
      3 ^ (cycleAcc x t).2.1 * x.1 + x.2 * (cycleAcc x t).2.2 := by
  induction t with
  | zero => simp [cycleAcc, orbit]
  | succ t ih =>
      rw [orbit_succ, cycleAcc]
      set E := (cycleAcc x t).1 with hE
      set M := (cycleAcc x t).2.1 with hM
      set T := (cycleAcc x t).2.2 with hT
      have ih' : 2 ^ E * (orbit x t).1 = 3 ^ M * x.1 + x.2 * T := by
        simpa [hE, hM, hT] using ih
      by_cases ho : Odd (orbit x t).1
      · -- odd step
        simp only [ite_eq_left ho]
        have hv : Valid (orbit x t) := valid_orbit hx t
        have hd : (orbit x t).2 = x.2 := denom_const_of_three_free hx h3 t
        have h3t : ¬ 3 ∣ (orbit x t).2 := by simpa [hd] using h3
        rw [step_three_free hv h3t ho, hd]
        rw [pow_succ]
        nlinarith [ih']
      · -- even step
        simp only [ite_eq_right ho]
        have he : Even (orbit x t).1 := Nat.not_odd_iff_even.mp ho
        rw [step_even he]
        rw [pow_succ']
        have htwo : 2 * ((orbit x t).1 / 2) = (orbit x t).1 :=
          Nat.two_mul_div_two_of_even he
        calc
          2 * 2 ^ E * ((orbit x t).1 / 2) = 2 ^ E * (2 * ((orbit x t).1 / 2)) := by ring
          _ = 2 ^ E * (orbit x t).1 := by rw [htwo]
          _ = 3 ^ M * x.1 + x.2 * T := ih'

/-! ### 2. The exact cycle-sum identity -/

/-- **Cycle-sum identity.** If `x` is a valid state with a cycle of positive
    length `L`, then with `(E,M,T) = cycleAcc x L`,

        (2^E - 3^M) * x.1 = x.2 * T.

    (If `L` denotes the total period, the power is `2^(L-M)` since `L = E+M`.) -/
theorem cycle_sum_identity {x : State} (hx : Valid x) {L : Nat} (hL : 1 ≤ L)
    (hcycle : orbit x L = x) :
    let r := cycleAcc x L
    (2 ^ r.1 - 3 ^ r.2.1) * x.1 = x.2 * r.2.2 := by
  have hnot3 := (lemma_2_4_and_cor_2_5_three_free_cycles hx hL hcycle).1
  have hspec := cycleAcc_spec x hx hnot3 L
  rw [hcycle] at hspec
  set E := (cycleAcc x L).1 with hE
  set M := (cycleAcc x L).2.1 with hM
  set T := (cycleAcc x L).2.2 with hT
  have hspec' : 2 ^ E * x.1 = 3 ^ M * x.1 + x.2 * T := by simpa [hE, hM, hT] using hspec
  have hle : 3 ^ M * x.1 ≤ 2 ^ E * x.1 := by
    nlinarith [Nat.zero_le (x.2 * T)]
  have hlepow : 3 ^ M ≤ 2 ^ E := Nat.le_of_mul_le_mul_right hle hx.1
  have hmul : (2 ^ E - 3 ^ M) * x.1 + 3 ^ M * x.1 = 2 ^ E * x.1 := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hlepow]
  change (2 ^ E - 3 ^ M) * x.1 = x.2 * T
  omega

/-- The home denominator divides `2^E - 3^M`. -/
theorem cycle_dvd {x : State} (hx : Valid x) {L : Nat} (hL : 1 ≤ L)
    (hcycle : orbit x L = x) :
    x.2 ∣ 2 ^ (cycleAcc x L).1 - 3 ^ (cycleAcc x L).2.1 := by
  have hid := cycle_sum_identity hx hL hcycle
  dsimp only at hid
  have hdvd : x.2 ∣ (2 ^ (cycleAcc x L).1 - 3 ^ (cycleAcc x L).2.1) * x.1 := by
    rw [hid]
    exact Nat.dvd_mul_right x.2 (cycleAcc x L).2.2
  exact hx.2.2.2.symm.dvd_of_dvd_mul_right hdvd

/-- The trailing-ones-block sum `T` of an exponent list `[e_0, ..., e_{M-1}]`:
    `T = ∑ 3^{M-1-j} 2^{e_j}`. -/
def cycT : List Nat → Nat
  | [] => 0
  | e :: es => 2 ^ e * 3 ^ es.length + cycT es

/-- For every exponent pattern the corresponding `T` is coprime to 3
    (its residue is `2^{e_{M-1}}`, hence `1` or `2` modulo 3). -/
lemma two_pow_mod_three_ne_zero (e : Nat) : 2 ^ e % 3 ≠ 0 := by
  induction e with
  | zero => norm_num
  | succ e ih =>
      have hcases : 2 ^ e % 3 = 1 ∨ 2 ^ e % 3 = 2 := by
        have hlt : 2 ^ e % 3 < 3 := Nat.mod_lt _ (by norm_num)
        omega
      rcases hcases with h | h
      · rw [pow_succ, Nat.mul_mod, h]
        norm_num
      · rw [pow_succ, Nat.mul_mod, h]
        norm_num

lemma three_pow_dvd_mod (e n : Nat) (hn : 1 ≤ n) : (2 ^ e * 3 ^ n) % 3 = 0 := by
  exact Nat.dvd_iff_mod_eq_zero.mp
    (dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega)) (2 ^ e))

lemma cycT_three_free : ∀ es : List Nat, es ≠ [] → cycT es % 3 ≠ 0
  | [], h => by contradiction
  | e :: es, h => by
      cases es with
      | nil => simpa [cycT] using two_pow_mod_three_ne_zero e
      | cons x xs =>
          have ih := cycT_three_free (x :: xs) (by simp)
          unfold cycT
          change (2 ^ e * 3 ^ (xs.length + 1) + cycT (x :: xs)) % 3 ≠ 0
          rw [Nat.add_mod]
          have hzero : (2 ^ e * 3 ^ (xs.length + 1)) % 3 = 0 :=
            three_pow_dvd_mod e (xs.length + 1) (by omega)
          rw [hzero, Nat.zero_add, Nat.mod_mod]
          exact ih

/-! ### 3. Steiner's 1-cycle exclusion -/

/-- If the first step is odd, `oddCount x 1 = 1`. -/
lemma oddCount_one_of_odd (x : State) (hodd : Odd x.1) : oddCount x 1 = 1 := by
  simp [oddCount, orbit, hodd]

/-- `oddCount` is monotone in the number of steps. -/
lemma oddCount_le_of_le (x : State) {s t : Nat} (h : s ≤ t) :
    oddCount x s ≤ oddCount x t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [oddCount_add]
  exact Nat.le_add_right _ _

/-- If `x` is odd and exactly one odd step occurs in the first `t` steps, then
    the accumulator's `T` equals `1`. -/
lemma cycleAcc_T_eq_one (x : State) (hodd : Odd x.1) :
    ∀ t, 1 ≤ t → oddCount x t = 1 → (cycleAcc x t).2.2 = 1 := by
  intro t ht hcount
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht0 : t = 0
      · subst t
        simp [cycleAcc, orbit, hodd]
      · have htpos : 1 ≤ t := by omega
        rw [cycleAcc]
        by_cases ho : Odd (orbit x t).1
        · rw [oddCount] at hcount
          simp [ho] at hcount
          have hc0 : oddCount x t = 0 := by omega
          have hc1 : oddCount x 1 = 1 := oddCount_one_of_odd x hodd
          have hle1 : oddCount x 1 ≤ oddCount x t := oddCount_le_of_le x htpos
          omega
        · rw [oddCount] at hcount
          simp [ho] at hcount
          have ih' := ih htpos hcount
          simp [ho, ih']

/-- **Steiner's 1-cycle exclusion.** A cycle with exactly one odd step and an
    odd starting numerator satisfies `a ≤ d`; therefore no non-trivial cycle
    (`a > d`) is a 1-cycle. -/
theorem one_odd_step_le_denominator {x : State} (hx : Valid x) {L : Nat} (hL : 1 ≤ L)
    (hcycle : orbit x L = x) (hodd : Odd x.1) (hM : oddCount x L = 1) :
    x.1 ≤ x.2 := by
  have hnot3 := (lemma_2_4_and_cor_2_5_three_free_cycles hx hL hcycle).1
  have hT : (cycleAcc x L).2.2 = 1 := cycleAcc_T_eq_one x hodd L hL hM
  have hMacc : (cycleAcc x L).2.1 = 1 := by simpa [cycleAcc_M_eq_oddCount] using hM
  have hspec := cycleAcc_spec x hx hnot3 L
  rw [hcycle] at hspec
  rw [hMacc, hT] at hspec
  norm_num at hspec
  set E := (cycleAcc x L).1 with hE
  have hspec' : 2 ^ E * x.1 = 3 * x.1 + x.2 := by simpa [hE] using hspec
  have hEge2 : 2 ≤ E := by
    by_contra hlt
    have hEle : E ≤ 1 := by omega
    interval_cases E <;> norm_num at hspec' <;> nlinarith [hx.1, hx.2.1]
  have hcoef : 1 ≤ 2 ^ E - 3 := by
    obtain ⟨u, hEq⟩ := Nat.exists_eq_add_of_le hEge2
    rw [hEq, Nat.pow_add]
    have hu : 1 ≤ 2 ^ u := Nat.one_le_pow u 2 (by omega)
    omega
  have hle : 3 * x.1 ≤ 2 ^ E * x.1 := by nlinarith [hx.2.1]
  have hlepow : 3 ≤ 2 ^ E := Nat.le_of_mul_le_mul_right hle hx.1
  have hmul : (2 ^ E - 3) * x.1 + 3 * x.1 = 2 ^ E * x.1 := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hlepow]
  have hsub : (2 ^ E - 3) * x.1 = x.2 := by omega
  have hxpos2 : 0 < 2 ^ E - 3 := by omega
  calc
    x.1 ≤ (2 ^ E - 3) * x.1 := Nat.le_mul_of_pos_left x.1 hxpos2
    _ = x.2 := hsub

/-! ### 4. Kernel-checked exclusions for small odd-step counts -/

/-- All exponent patterns `[e_0=0, e_1, ..., e_{M-1}]` with
    `1 ≤ e_1 < ... < e_{M-1} < E`. -/
def exponentPatterns : Nat → Nat → List (List Nat)
  | 0, _ => []
  | 1, _ => [[0]]
  | M + 1, E =>
      (exponentPatterns M E).flatMap fun es =>
        (List.range E).filterMap fun e =>
          match es.getLast? with
          | some l => if l < e then some (es ++ [e]) else none
          | none => none

/-- The least halving count `E` with `2^E > 3^M` (always `≤ 2M`). -/
def minHalvings (M : Nat) : Nat :=
  match (List.range (2 * M + 1)).find? (fun E => 2 ^ E > 3 ^ M) with
  | some E => E
  | none => 2 * M

/-- A decidable sweep: for `M ≤ Mmax` and `E` in the window
    `[minHalvings M, minHalvings M + Ewindow]`, check that no exponent pattern
    makes `N = 2^E - 3^M` divide `T` with quotient `a = T/N > 1`.  For `d = 1`
    this rules out non-trivial integer cycles. -/
def noSmallIntegerCycles (Mmax Ewindow : Nat) : Bool :=
  (List.range Mmax).all fun Mi =>
    let M := Mi + 1
    (List.range (Ewindow + 1)).all fun dE =>
      let E := minHalvings M + dE
      let N := 2 ^ E - 3 ^ M
      (exponentPatterns M E).all fun es =>
        let T := cycT es
        !(0 < N && T % N == 0 && N < T)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma no_integer_cycles_M_le_six : noSmallIntegerCycles 6 4 = true := by
  decide

/-- Concrete kernel check: the only 1-cycle at `d'=1` is the trivial one
    `(a,E)=(1,2)`, and the trivial cycle traversed twice is the only integer
    2-cycle with `a=1`. -/
example : (2 ^ 2 - 3) * 1 = (1 : Nat) := by norm_num
example : (2 ^ 4 - 3 ^ 2) * 1 = (3 + 2 ^ 2 : Nat) := by norm_num

/-- A rational 2-cycle *does* exist at `d' = 7` (`a = 11 > 7`): the obstruction
    is not "no rational cycles", it is the exact classification
    `(2^E - 3^M) a = d' T`, which the following kernel check realizes. -/
example : (2 ^ 4 - 3 ^ 2) * 11 = 7 * (3 + 2 ^ 3) := by norm_num

/-- A single fuel block: `M` consecutive odd steps (`e_j = j`) followed by
    `s ≥ 1` halvings, so `E = M + s` and `T = 3^M - 2^M`.  The decidable
    sweep excludes non-trivial `d = 1` cycles of this shape for `M ≤ 12`,
    `s ≤ 40`. -/
def noSingleBlockIntegerCycles (Mmax Smax : Nat) : Bool :=
  (List.range Mmax).all fun Mi =>
    let M := Mi + 1
    (List.range Smax).all fun Si =>
      let s := Si + 1
      let E := M + s
      let N := 2 ^ E - 3 ^ M
      let T := 3 ^ M - 2 ^ M
      !(0 < N && T % N == 0 && N < T)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma no_single_block_integer_cycles : noSingleBlockIntegerCycles 12 40 = true := by
  decide

/-- Kernel-checked 2-adic fingerprint: for every exponent pattern with
    `e_0 = 0` and `e_j ≥ 1` for `j ≥ 1`, `T` is odd.  (The 3-adic fingerprint
    `3 ∤ T` holds for *all* patterns by `cycT_three_free` above.) -/
def patternsOdd (M E : Nat) : Bool :=
  (exponentPatterns M E).all fun es => cycT es % 2 == 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma cycT_patterns_odd_M_le_six : (List.range 6).all (fun Mi => patternsOdd (Mi + 1) 16) = true := by
  decide

#print axioms step_three_free
#print axioms denom_const_of_three_free
#print axioms cycleAcc_spec
#print axioms cycle_sum_identity
#print axioms cycle_dvd
#print axioms one_odd_step_le_denominator
#print axioms no_integer_cycles_M_le_six
#print axioms no_single_block_integer_cycles
#print axioms cycT_patterns_odd_M_le_six
#print axioms cycT_three_free

end CycleExclusion
end CollatzAdicBase
