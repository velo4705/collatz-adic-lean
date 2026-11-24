import Mathlib

/-!
# Rational descent for the 3-adic Collatz map

A reduced positive rational with an odd denominator is represented by a pair
`(a, d) : ℕ × ℕ` with `0 < a`, `0 < d`, `Odd d` and `Nat.Coprime a d`.

The reduced Collatz step is

* `(a, d) ↦ (a / 2, d)` when `a` is even,
* `(a, d) ↦ ((3a + d) / g, d / g)` with `g = gcd (3a + d) d` when `a` is odd.

The key arithmetic observation is that `g ∣ 3`, so the only prime that may
appear in the denominator changes is `3`.
-/

namespace CollatzAdicBase

abbrev State := ℕ × ℕ

def Valid (x : State) : Prop :=
  0 < x.1 ∧ 0 < x.2 ∧ Odd x.2 ∧ Nat.Coprime x.1 x.2

def step (x : State) : State :=
  if _ : Even x.1 then (x.1 / 2, x.2)
  else
    let g := Nat.gcd (3 * x.1 + x.2) x.2
    ((3 * x.1 + x.2) / g, x.2 / g)

@[simp] lemma step_even {a d : ℕ} (h : Even a) : step (a, d) = (a / 2, d) := by
  simp [step, h]

lemma step_odd {a d : ℕ} (h : ¬ Even a) :
    step (a, d) = ((3 * a + d) / Nat.gcd (3 * a + d) d,
                   d / Nat.gcd (3 * a + d) d) := by
  simp [step, h]

/-! ### Arithmetic helpers -/

lemma gcd_dvd_three {a d : ℕ} (hcop : Nat.Coprime a d) :
    Nat.gcd (3 * a + d) d ∣ 3 := by
  let g := Nat.gcd (3 * a + d) d
  have hgd : g ∣ d := Nat.gcd_dvd_right _ _
  have hga : g ∣ 3 * a + d := Nat.gcd_dvd_left _ _
  have hg3a : g ∣ 3 * a := by
    rw [Nat.dvd_iff_mod_eq_zero] at hga hgd ⊢
    rw [Nat.add_mod, hgd] at hga
    simpa using hga
  have hc : Nat.Coprime g a := (hcop.of_dvd_right hgd).symm
  exact (hc.dvd_mul_right).mp hg3a

lemma dvd_three_cases {g : ℕ} (h : g ∣ 3) : g = 1 ∨ g = 3 :=
  (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h

lemma padicValNat_eq_factorization {p n : ℕ} (hp : p.Prime) :
    padicValNat p n = n.factorization p := by
  rw [Nat.padicValNat_def, Nat.multiplicity_eq_factorization hp]

lemma odd_div_of_dvd {d g : ℕ} (hd : Odd d) (hgd : g ∣ d) : Odd (d / g) := by
  rw [← Nat.not_even_iff_odd]
  intro he
  have h2 : 2 ∣ d := by
    rw [← Nat.div_mul_cancel hgd]
    exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp he) g
  exact hd.not_two_dvd_nat h2

lemma step_valid {x : State} (hx : Valid x) : Valid (step x) := by
  rcases x with ⟨a, d⟩
  rcases hx with ⟨ha, hdpos, hdodd, hcop⟩
  by_cases he : Even a
  · rw [step_even he]
    have hadiv : a / 2 ∣ a := by
      refine ⟨2, ?_⟩
      rw [mul_comm, Nat.two_mul_div_two_of_even he]
    refine ⟨?_, hdpos, hdodd, hcop.of_dvd_left hadiv⟩
    rcases (even_iff_exists_two_mul.mp he) with ⟨m, hm⟩
    rw [hm]
    have hmpos : 0 < m := by omega
    simp [hmpos]
  · rw [step_odd he]
    let g := Nat.gcd (3 * a + d) d
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hdpos
    have hgd : g ∣ d := Nat.gcd_dvd_right _ _
    have hgn : g ∣ 3 * a + d := Nat.gcd_dvd_left _ _
    have hnpos : 0 < (3 * a + d) / g :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hgn) hgpos
    have hdpos' : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hdpos hgd) hgpos
    have hdodd' : Odd (d / g) := odd_div_of_dvd hdodd hgd
    have hcop' : Nat.Coprime ((3 * a + d) / g) (d / g) :=
      Nat.coprime_div_gcd_div_gcd hgpos
    exact ⟨hnpos, hdpos', hdodd', hcop'⟩

/-! ### Lemma 2.1 — stability of all primes `p ≠ 3` -/

lemma lemma_2_1_stability (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    {a d : ℕ} (hcop : Nat.Coprime a d) :
    padicValNat p (step (a, d)).2 = padicValNat p d := by
  by_cases he : Even a
  · simp [step_even he]
  · rw [step_odd he]
    let g := Nat.gcd (3 * a + d) d
    have hgd : g ∣ d := Nat.gcd_dvd_right _ _
    have hgfac : g.factorization p = 0 := by
      rcases dvd_three_cases (gcd_dvd_three hcop) with hg | hg
      · dsimp [g]; rw [hg]; simp
      · dsimp [g]; rw [hg]
        have h3 : Nat.Prime 3 := by norm_num
        rw [h3.factorization]
        simp [hp3]
    rw [padicValNat_eq_factorization hp, padicValNat_eq_factorization hp]
    rw [Nat.factorization_div hgd]
    simp [hgfac]

/-! ### Lemma 2.2 — one factor of 3 per odd step when `3 ∣ d` -/

lemma lemma_2_2_one_three_per_odd_step {a d : ℕ} (_ha : Odd a) (_hdpos : 0 < d)
    (hcop : Nat.Coprime a d) (h3d : 3 ∣ d) :
    Nat.gcd (3 * a + d) d = 3 ∧
      padicValNat 3 (d / 3) = padicValNat 3 d - 1 := by
  let g := Nat.gcd (3 * a + d) d
  have hgdvd3 : g ∣ 3 := gcd_dvd_three hcop
  have h3g : 3 ∣ g := by
    apply Nat.dvd_gcd
    · exact dvd_add (dvd_mul_right 3 a) h3d
    · exact h3d
  have hg_eq : g = 3 := by
    rcases dvd_three_cases hgdvd3 with hg | hg
    · rw [hg] at h3g
      norm_num at h3g
    · exact hg
  constructor
  · exact hg_eq
  · have hfac : (d / 3).factorization = d.factorization - (3 : ℕ).factorization :=
      Nat.factorization_div h3d
    have h3 : Nat.Prime 3 := by norm_num
    rw [padicValNat_eq_factorization h3, padicValNat_eq_factorization h3]
    rw [hfac]
    simp [h3.factorization]

/-! ### Lemma 2.3 — the numerator after an odd step is even -/

lemma lemma_2_3_forced_halving {a d : ℕ} (ha : Odd a) (hd : Odd d)
    (hdpos : 0 < d) (_hcop : Nat.Coprime a d) :
    Even ((3 * a + d) / Nat.gcd (3 * a + d) d) := by
  let g := Nat.gcd (3 * a + d) d
  have hgd : g ∣ d := Nat.gcd_dvd_right _ _
  have hgodd : Odd g := by
    rw [← Nat.not_even_iff_odd]
    intro hge
    exact hd.not_two_dvd_nat ((even_iff_two_dvd.mp hge).trans hgd)
  have hnum_even : Even (3 * a + d) :=
    ((show Odd 3 by norm_num).mul ha).add_odd hd
  rcases even_iff_exists_two_mul.mp hnum_even with ⟨m, hm⟩
  have hgn : g ∣ 2 * m := by
    rw [← hm]
    exact Nat.gcd_dvd_left (3 * a + d) d
  have hgm : g ∣ m := (hgodd.coprime_two_right.dvd_mul_left).mp hgn
  rcases hgm with ⟨t, ht⟩
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hdpos
  have hnum : 3 * a + d = g * (2 * t) := by
    rw [hm, ht]
    ring
  have hdiv : (3 * a + d) / g = 2 * t := by
    rw [hnum, Nat.mul_div_right _ hgpos]
  exact even_iff_exists_two_mul.mpr ⟨t, hdiv⟩

/-! ### Denominator behaviour along an orbit -/

def orbit (x : State) (n : ℕ) : State := step^[n] x

lemma orbit_succ (x : State) (n : ℕ) : orbit x (n + 1) = step (orbit x n) := by
  change (step^[n + 1]) x = step ((step^[n]) x)
  rw [Function.iterate_succ']
  rfl

lemma orbit_succ_eq (x : State) (n : ℕ) : orbit x (n + 1) = orbit (step x) n := by
  change (step^[n + 1]) x = (step^[n]) (step x)
  rw [Function.iterate_add_apply]
  simp

lemma orbit_add (x : State) (m n : ℕ) : orbit x (m + n) = orbit (orbit x m) n := by
  change (step^[m + n]) x = (step^[n]) ((step^[m]) x)
  rw [Nat.add_comm m n, Function.iterate_add_apply]

lemma valid_orbit {x : State} (hx : Valid x) (n : ℕ) : Valid (orbit x n) := by
  induction n with
  | zero => simpa [orbit] using hx
  | succ n ih => rw [orbit_succ]; exact step_valid ih

lemma denom_fixed_of_not_three {y : State} (hy : Valid y) (h3 : ¬ 3 ∣ y.2) :
    (step y).2 = y.2 := by
  rcases y with ⟨a, d⟩
  rcases hy with ⟨ha, hdpos, hdodd, hcop⟩
  change ¬ 3 ∣ d at h3
  by_cases he : Even a
  · simp [step_even he]
  · rw [step_odd he]
    let g := Nat.gcd (3 * a + d) d
    have hgnot3 : g ≠ 3 := by
      intro h
      apply h3
      rw [← h]
      exact Nat.gcd_dvd_right (3 * a + d) d
    rcases dvd_three_cases (gcd_dvd_three hcop) with hg | hg
    · dsimp [g]; rw [hg]; simp
    · exact (hgnot3 hg).elim

lemma v3_step_le {y : State} (hy : Valid y) :
    padicValNat 3 (step y).2 ≤ padicValNat 3 y.2 := by
  rcases y with ⟨a, d⟩
  rcases hy with ⟨ha, hdpos, hdodd, hcop⟩
  by_cases he : Even a
  · simp [step_even he]
  · rw [step_odd he]
    let g := Nat.gcd (3 * a + d) d
    have hgd : g ∣ d := Nat.gcd_dvd_right _ _
    have h3 : Nat.Prime 3 := by norm_num
    rw [padicValNat_eq_factorization h3, padicValNat_eq_factorization h3]
    rw [Nat.factorization_div hgd]
    exact Nat.sub_le _ _

lemma v3_step_strict_of_odd_of_three {y : State} (hy : Valid y)
    (haodd : Odd y.1) (h3d : 3 ∣ y.2) :
    padicValNat 3 (step y).2 < padicValNat 3 y.2 := by
  rcases y with ⟨a, d⟩
  rcases hy with ⟨hapos, hdpos, hdodd, hcop⟩
  change padicValNat 3 (step (a, d)).2 < padicValNat 3 d
  change Odd a at haodd
  change 0 < d at hdpos
  change Nat.Coprime a d at hcop
  change 3 ∣ d at h3d
  have h2 := lemma_2_2_one_three_per_odd_step haodd hdpos hcop h3d
  rw [step_odd (Nat.not_even_iff_odd.mpr haodd)]
  rw [h2.1, h2.2]
  have hpos : 0 < padicValNat 3 d := by
    rw [padicValNat_eq_factorization (by norm_num : Nat.Prime 3)]
    exact Nat.Prime.factorization_pos_of_dvd (by norm_num) (Nat.ne_of_gt hdpos) h3d
  exact Nat.sub_lt hpos (by norm_num)

lemma v3_orbit_le {y : State} (hy : Valid y) (n : ℕ) :
    padicValNat 3 (orbit y n).2 ≤ padicValNat 3 y.2 := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
      rw [orbit_succ]
      exact le_trans (v3_step_le (valid_orbit hy n)) ih

lemma v3_orbit_tail {x : State} (hx : Valid x) {m n : ℕ} (hmn : m ≤ n) :
    padicValNat 3 (orbit x n).2 ≤ padicValNat 3 (orbit x m).2 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmn
  calc
    padicValNat 3 (orbit x (m + t)).2 =
        padicValNat 3 (orbit (orbit x m) t).2 := by rw [orbit_add]
    _ ≤ padicValNat 3 (orbit x m).2 := v3_orbit_le (valid_orbit hx m) t

lemma denom_eq_of_all_even {x : State} (_hx : Valid x) {i : ℕ}
    (hall : ∀ j, j < i → Even (orbit x j).1) : (orbit x i).2 = x.2 := by
  induction i with
  | zero => simp [orbit]
  | succ i ih =>
      have hall' : ∀ j, j < i → Even (orbit x j).1 := by
        intro j hj; exact hall j (by omega)
      have ih' := ih hall'
      have hiEven : Even (orbit x i).1 := hall i (by omega)
      rw [orbit_succ, step_even hiEven]
      exact ih'

lemma orbit_allEven_decreases_aux : ∀ L : ℕ, ∀ (x : State), Valid x → 1 ≤ L →
    (∀ i, i < L → Even (orbit x i).1) → (orbit x L).1 < x.1 := by
  intro L
  induction L with
  | zero =>
      intro x hx hL hall
      omega
  | succ L ih =>
      intro x hx hL hall
      have hxpos : 0 < x.1 := hx.1
      by_cases hL0 : L = 0
      · subst L
        have h0 : Even x.1 := by simpa [orbit] using hall 0 (by omega)
        rcases even_iff_exists_two_mul.mp h0 with ⟨m, hm⟩
        have hmpos : 0 < m := by omega
        have hs1 : orbit x 1 = (m, x.2) := by simp [orbit, step_even h0, hm]
        rw [hs1]
        omega
      · have hLpos : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL0
        have h0 : Even x.1 := by simpa [orbit] using hall 0 (by omega)
        rcases even_iff_exists_two_mul.mp h0 with ⟨m, hm⟩
        have hmpos : 0 < m := by omega
        have hs1 : step x = (m, x.2) := by simp [step_even h0, hm]
        have hv1 : Valid (step x) := step_valid hx
        have hall_tail : ∀ j, j < L → Even (orbit (step x) j).1 := by
          intro j hj
          have := hall (j + 1) (by omega)
          simpa [orbit_succ_eq, hs1] using this
        have htail := ih (step x) hv1 hLpos hall_tail
        have htail' : (orbit (m, x.2) L).1 < m := by
          simpa [orbit, hs1] using htail
        have hlt_m : m < x.1 := by omega
        calc
          (orbit x (L + 1)).1 = (orbit (step x) L).1 := by rw [orbit_succ_eq]
          _ = (orbit (m, x.2) L).1 := by simp [orbit, hs1]
          _ < m := htail'
          _ < x.1 := hlt_m

lemma orbit_allEven_decreases {x : State} (hx : Valid x) {L : ℕ} (hL : 1 ≤ L)
    (hall : ∀ i, i < L → Even (orbit x i).1) : (orbit x L).1 < x.1 :=
  orbit_allEven_decreases_aux L x hx hL hall

lemma exists_odd_step_in_cycle {x : State} (hx : Valid x) {L : ℕ} (hL : 1 ≤ L)
    (hcycle : orbit x L = x) : ∃ i, i < L ∧ Odd (orbit x i).1 := by
  by_contra h
  push Not at h
  have hall : ∀ i, i < L → Even (orbit x i).1 := by
    intro i hi
    exact h i hi
  have hlt := orbit_allEven_decreases hx hL hall
  have heq : (orbit x L).1 = x.1 := by rw [hcycle]
  omega

/-! ### Lemma 2.4 / Corollary 2.5 — no factor 3 in a cycle, constant denominator -/

lemma lemma_2_4_and_cor_2_5_three_free_cycles {x : State} (hx : Valid x) {L : ℕ}
    (hL : 1 ≤ L) (hcycle : orbit x L = x) :
    ¬ 3 ∣ x.2 ∧ ∀ i, i ≤ L → (orbit x i).2 = x.2 := by
  have hodd_ex : ∃ i, i < L ∧ Odd (orbit x i).1 := exists_odd_step_in_cycle hx hL hcycle
  let i0 := Nat.find hodd_ex
  have hi0_spec := Nat.find_spec hodd_ex
  have hi0_lt : i0 < L := hi0_spec.1
  have hi0_odd : Odd (orbit x i0).1 := hi0_spec.2
  have hi0_min : ∀ j < i0, ¬ Odd (orbit x j).1 := by
    intro j hj hodd
    exact Nat.find_min hodd_ex hj ⟨by omega, hodd⟩
  have hall_i0 : ∀ j < i0, Even (orbit x j).1 := by
    intro j hj
    exact Nat.not_odd_iff_even.mp (hi0_min j hj)
  have hd_i0 : (orbit x i0).2 = x.2 := denom_eq_of_all_even hx hall_i0
  have hnot3 : ¬ 3 ∣ x.2 := by
    intro h3x
    have h3i0 : 3 ∣ (orbit x i0).2 := by simpa [hd_i0] using h3x
    have hv_i0 : Valid (orbit x i0) := valid_orbit hx i0
    have hstrict : padicValNat 3 (orbit x (i0 + 1)).2 < padicValNat 3 (orbit x i0).2 := by
      rw [orbit_succ]
      exact v3_step_strict_of_odd_of_three hv_i0 hi0_odd h3i0
    have htail : padicValNat 3 (orbit x L).2 ≤ padicValNat 3 (orbit x (i0 + 1)).2 :=
      v3_orbit_tail (x := x) (m := i0 + 1) (n := L) hx (by omega)
    have heqd : (orbit x L).2 = x.2 := by rw [hcycle]
    rw [heqd] at htail
    have hle : padicValNat 3 (orbit x i0).2 ≤ padicValNat 3 (orbit x (i0 + 1)).2 := by
      simpa [hd_i0] using htail
    omega
  refine ⟨hnot3, ?_⟩
  intro i hi
  induction i with
  | zero => simp [orbit]
  | succ i ih =>
      have hi_le : i ≤ L := by omega
      have ih' := ih hi_le
      have hv_i : Valid (orbit x i) := valid_orbit hx i
      have h3_i : ¬ 3 ∣ (orbit x i).2 := by simpa [ih'] using hnot3
      rw [orbit_succ, denom_fixed_of_not_three hv_i h3_i, ih']

/-! ### Theorem 1 — descent for pure powers of three -/

def oddCount (x : State) : ℕ → ℕ
  | 0 => 0
  | n + 1 => oddCount x n + if Odd (orbit x n).1 then 1 else 0

lemma oddCount_add (x : State) (m n : ℕ) :
    oddCount x (m + n) = oddCount x m + oddCount (orbit x m) n := by
  induction n with
  | zero => simp [oddCount]
  | succ n ih =>
      rw [Nat.add_succ, oddCount, ih, orbit_add, oddCount]
      omega

lemma oddCount_eq_zero_of_allEven {x : State} {s : ℕ}
    (hall : ∀ j, j < s → Even (orbit x j).1) : oddCount x s = 0 := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [oddCount]
      have hall' : ∀ j, j < s → Even (orbit x j).1 := by
        intro j hj; exact hall j (by omega)
      rw [ih hall']
      have hno : ¬ Odd (orbit x s).1 := Nat.not_odd_iff_even.mpr (hall s (by omega))
      simp [hno]

lemma even_steps_to_odd_aux (s b d : ℕ) :
    step^[s] (2 ^ s * b, d) = (b, d) ∧
      (∀ j, j < s → Even (orbit (2 ^ s * b, d) j).1) := by
  induction s with
  | zero => simp [orbit]
  | succ s ih =>
      have he : Even (2 ^ (s + 1) * b) := by
        rw [pow_succ']
        exact ⟨2 ^ s * b, by ring⟩
      have hstep : step (2 ^ (s + 1) * b, d) = (2 ^ s * b, d) := by
        rw [step_even he]
        congr 1
        rw [pow_succ']
        simp [Nat.mul_assoc]
      constructor
      · rw [Function.iterate_succ]
        change (step^[s]) (step (2 ^ (s + 1) * b, d)) = (b, d)
        rw [hstep]
        exact ih.1
      · intro j hj
        cases j with
        | zero =>
            change Even (2 ^ (s + 1) * b)
            exact he
        | succ j =>
            rw [orbit_succ_eq, hstep]
            exact ih.2 j (by omega)

lemma even_steps_to_odd (a d : ℕ) (ha : 0 < a) :
    ∃ s b, Odd b ∧ a = 2 ^ s * b ∧ step^[s] (a, d) = (b, d) ∧
      ∀ j, j < s → Even (orbit (a, d) j).1 := by
  obtain ⟨s, b, hbodd, haeq⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt ha)
  refine ⟨s, b, hbodd, haeq, ?_, ?_⟩
  · rw [haeq]
    exact (even_steps_to_odd_aux s b d).1
  · rw [haeq]
    exact (even_steps_to_odd_aux s b d).2

theorem theorem_1_pure_three_power_descent (a k : ℕ) (ha : 0 < a)
    (hcop : Nat.Coprime a (3 ^ k)) :
    ∃ t m, step^[t] (a, 3 ^ k) = (m, 1) ∧ oddCount (a, 3 ^ k) t ≤ k := by
  induction k generalizing a with
  | zero =>
      exact ⟨0, a, by simp, by simp [oddCount]⟩
  | succ k ih =>
      obtain ⟨s, b, hbodd, haeq, htraj_s, hall_s⟩ := even_steps_to_odd a (3 ^ (k + 1)) ha
      have hbne : b ≠ 0 := by intro h; subst b; norm_num at hbodd
      have hbpos : 0 < b := Nat.pos_of_ne_zero hbne
      have hdpos : 0 < 3 ^ (k + 1) := by positivity
      have h3div : 3 ∣ 3 ^ (k + 1) := by
        rw [pow_succ']
        exact dvd_mul_right 3 (3 ^ k)
      have hb_coprime : Nat.Coprime b (3 ^ (k + 1)) := by
        apply hcop.of_dvd_left
        refine ⟨2 ^ s, ?_⟩
        rw [haeq, mul_comm]
      have hval_b : Valid (b, 3 ^ (k + 1)) := ⟨hbpos, hdpos, (show Odd 3 by norm_num).pow, hb_coprime⟩
      have hg_eq : Nat.gcd (3 * b + 3 ^ (k + 1)) (3 ^ (k + 1)) = 3 :=
        (lemma_2_2_one_three_per_odd_step hbodd hdpos hb_coprime h3div).1
      let a' := (3 * b + 3 ^ (k + 1)) / 3
      have hoddstep : step (b, 3 ^ (k + 1)) = (a', 3 ^ k) := by
        rw [step_odd (Nat.not_even_iff_odd.mpr hbodd)]
        rw [hg_eq]
        congr 1
        rw [pow_succ']
        simp
      have ha'pos : 0 < a' := by
        dsimp [a']
        apply Nat.div_pos
        · omega
        · norm_num
      have hval_next : Valid (a', 3 ^ k) := by
        simpa [hoddstep] using step_valid hval_b
      obtain ⟨t', m, htraj', hcount'⟩ := ih a' ha'pos hval_next.2.2.2
      have htraj_orb : orbit (a, 3 ^ (k + 1)) s = (b, 3 ^ (k + 1)) := by
        simpa [orbit] using htraj_s
      refine ⟨s + 1 + t', m, ?_, ?_⟩
      · rw [show s + 1 + t' = t' + (s + 1) by omega, Function.iterate_add_apply]
        have hs1 : step^[s + 1] (a, 3 ^ (k + 1)) = (a', 3 ^ k) := by
          rw [Function.iterate_succ']
          change step (orbit (a, 3 ^ (k + 1)) s) = (a', 3 ^ k)
          rw [htraj_orb, hoddstep]
        rw [hs1, htraj']
      · have hcount_s : oddCount (a, 3 ^ (k + 1)) s = 0 :=
          oddCount_eq_zero_of_allEven hall_s
        have horb_s : orbit (a, 3 ^ (k + 1)) s = (b, 3 ^ (k + 1)) := by
          exact htraj_s
        have hs1_orbit : orbit (a, 3 ^ (k + 1)) (s + 1) = (a', 3 ^ k) := by
          rw [orbit_succ, htraj_orb, hoddstep]
        rw [show s + 1 + t' = (s + 1) + t' by omega, oddCount_add]
        rw [oddCount, hcount_s, horb_s]
        simp [hbodd]
        rw [hs1_orbit]
        omega

/-! ### Computational verification for `1 ≤ k ≤ 6` -/

def reachesOneWithin (k a B : ℕ) : Prop :=
  ∃ t ≤ B, step^[t] (a, 3 ^ k) = (1, 1)

def reachesOneBool (k a B : ℕ) : Bool :=
  (List.range (B + 1)).any (fun t => step^[t] (a, 3 ^ k) == (1, 1))

/-- A decidable, fully computable check: for every `k` with `1 ≤ k ≤ 6` and
every reduced numerator `a < 3^k`, the trajectory reaches `(1, 1)` within
100 reduced steps. -/
def verifyPureThreePowerSmallK : Bool :=
  (List.range 6).all fun ki =>
    (List.range (3 ^ (ki + 1))).all fun ai =>
      if Nat.Coprime ai (3 ^ (ki + 1)) then reachesOneBool (ki + 1) ai 100 else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
lemma verification_pure_three_power_k_le_six : verifyPureThreePowerSmallK = true := by
  decide

lemma reachesOneBool_iff (k a B : ℕ) :
    reachesOneBool k a B = true ↔ reachesOneWithin k a B := by
  simp [reachesOneBool, reachesOneWithin, List.any_eq_true]

/-- The fully propositional form of the computation: for every `k` with
`1 ≤ k ≤ 6` and every reduced numerator `a < 3^k`, the trajectory reaches
`(1, 1)` in at most 100 reduced steps. -/
lemma verification_all_reduced_small_k :
    ∀ k : Fin 6, ∀ a : Fin (3 ^ (k.val + 1)),
      Nat.Coprime a.val (3 ^ (k.val + 1)) →
      reachesOneWithin (k.val + 1) a.val 100 := by
  intro k a hcop
  rw [← reachesOneBool_iff]
  have h := verification_pure_three_power_k_le_six
  simp [verifyPureThreePowerSmallK, List.all_eq_true] at h
  have hcop3 : a.val.gcd 3 = 1 := by
    have h3div : 3 ∣ 3 ^ (k.val + 1) := by
      rw [pow_succ']
      exact dvd_mul_right 3 (3 ^ k.val)
    exact (hcop.of_dvd_right h3div).gcd_eq_one
  have hres := h k.val k.isLt a.val a.isLt
  rcases hres with hbad | hbool
  · exact (hbad hcop3).elim
  · exact hbool

#print axioms lemma_2_1_stability
#print axioms lemma_2_2_one_three_per_odd_step
#print axioms lemma_2_3_forced_halving
#print axioms lemma_2_4_and_cor_2_5_three_free_cycles
#print axioms theorem_1_pure_three_power_descent
#print axioms verification_pure_three_power_k_le_six
#print axioms verification_all_reduced_small_k

end CollatzAdicBase
