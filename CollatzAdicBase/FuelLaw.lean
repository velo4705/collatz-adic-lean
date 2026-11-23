import CollatzAdicBase.Basic

namespace CollatzAdicBase

namespace FuelLaw

/-- A product of powers (with positive base) and a positive integer is positive. -/
private theorem one_le_prod (b j t q : Nat) (hb : 1 ≤ b) (hq : 1 ≤ q) :
    1 ≤ b ^ j * 2 ^ t * q := by
  have hb' : 1 ≤ b ^ j := Nat.one_le_pow j b hb
  have h2 : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
  exact Nat.le_trans (by omega : 1 ≤ 1 * 1 * 1) (Nat.mul_le_mul (Nat.mul_le_mul hb' h2) hq)

/-- The shortcut collapses one odd step and one even step:
    `shortcut (2a - 1) = 3a - 1` whenever `a ≥ 1`. -/
theorem shortcut_two_mul_sub_one (a : Nat) (ha : 1 ≤ a) :
    shortcut (2 * a - 1) = 3 * a - 1 := by
  unfold shortcut
  have h : 3 * (2 * a - 1) + 1 = 2 * (3 * a - 1) := by omega
  rw [h]
  exact Nat.mul_div_right (3 * a - 1) (m := 2) (by omega)

/-- `collatz` on an odd input. -/
theorem collatz_of_odd (m : Nat) (hm : m % 2 = 1) : collatz m = 3 * m + 1 := by
  unfold collatz
  simp [hm]

/-- `collatz` on an even input. -/
theorem collatz_of_even (m : Nat) (hm : m % 2 = 0) : collatz m = m / 2 := by
  unfold collatz
  simp [hm]

/-- Two ordinary Collatz steps starting at an odd `m` are exactly one shortcut step. -/
theorem collatz_twice_odd (m : Nat) (hm : m % 2 = 1) :
    Nat.iterate collatz 2 m = shortcut m := by
  have h1 : collatz m = 3 * m + 1 := collatz_of_odd m hm
  have he : (3 * m + 1) % 2 = 0 := by omega
  have h2 : collatz (3 * m + 1) = (3 * m + 1) / 2 := collatz_of_even _ he
  simp [Nat.iterate, h1, h2, shortcut]

/-- The algebraic core of the fuel law: one shortcut step on `3^j 2^(k-j) q - 1`. -/
theorem shortcut_pow_formula (k q j : Nat) (_hk : 1 ≤ k) (hq : 1 ≤ q) (hj : j < k) :
    shortcut (3 ^ j * 2 ^ (k - j) * q - 1) =
      3 ^ (j + 1) * 2 ^ (k - (j + 1)) * q - 1 := by
  have hsub : k - j = (k - (j + 1)) + 1 := by omega
  let b : Nat := 3 ^ j * 2 ^ (k - (j + 1)) * q
  have hb : 1 ≤ b := by
    dsimp [b]
    exact one_le_prod 3 j (k - (j + 1)) q (by omega) hq
  have heq : 3 ^ j * 2 ^ (k - j) * q = 2 * b := by
    rw [hsub, Nat.pow_succ]
    dsimp [b]
    ac_rfl
  rw [heq, shortcut_two_mul_sub_one b hb]
  dsimp [b]
  congr 1
  rw [Nat.pow_succ]
  ac_rfl

/-- Proposition 4 (first half): after `j ≤ k` shortcut steps the number is
    `3^j * 2^(k - j) * q - 1`. -/
theorem iterate_shortcut_formula (k q j : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (hj : j ≤ k) :
    Nat.iterate shortcut j (2 ^ k * q - 1) = 3 ^ j * 2 ^ (k - j) * q - 1 := by
  induction j with
  | zero =>
      simp [Nat.iterate]
  | succ j ih =>
      have hjle : j ≤ k := by omega
      have hjlt : j < k := by omega
      rw [Nat.iterate_succ', ih hjle]
      exact shortcut_pow_formula k q j hk hq hjlt

/-- Every intermediate value of the shortcut glide is odd. -/
theorem iterate_shortcut_odd (k q j : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (hj : j < k) :
    Nat.iterate shortcut j (2 ^ k * q - 1) % 2 = 1 := by
  rw [iterate_shortcut_formula k q j hk hq (by omega)]
  have hsub : k - j = (k - j - 1) + 1 := by omega
  let b : Nat := 3 ^ j * 2 ^ (k - j - 1) * q
  have hb : 1 ≤ b := by
    dsimp [b]
    exact one_le_prod 3 j (k - j - 1) q (by omega) hq
  have heq : 3 ^ j * 2 ^ (k - j) * q = 2 * b := by
    rw [hsub, Nat.pow_succ]
    dsimp [b]
    ac_rfl
  rw [heq]
  omega

/-- The shortcut glide is strictly increasing for `j < k`. -/
theorem iterate_shortcut_strict_mono (k q j : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (hj : j < k) :
    Nat.iterate shortcut j (2 ^ k * q - 1) < Nat.iterate shortcut (j + 1) (2 ^ k * q - 1) := by
  rw [iterate_shortcut_formula k q j hk hq (by omega)]
  rw [iterate_shortcut_formula k q (j + 1) hk hq (by omega)]
  have hsub : k - j = (k - j - 1) + 1 := by omega
  have hsub2 : k - (j + 1) = k - j - 1 := by omega
  let b : Nat := 3 ^ j * 2 ^ (k - j - 1) * q
  have hb : 1 ≤ b := by
    dsimp [b]
    exact one_le_prod 3 j (k - j - 1) q (by omega) hq
  have heq1 : 3 ^ j * 2 ^ (k - j) * q = 2 * b := by
    rw [hsub, Nat.pow_succ]
    dsimp [b]
    ac_rfl
  have heq2 : 3 ^ (j + 1) * 2 ^ (k - (j + 1)) * q = 3 * b := by
    rw [Nat.pow_succ, hsub2]
    dsimp [b]
    ac_rfl
  rw [heq1, heq2]
  omega

/-- `2^j < 3^j` for `j ≥ 1`. -/
private theorem two_pow_lt_three_pow (j : Nat) (hj : 1 ≤ j) : 2 ^ j < 3 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
      cases j with
      | zero => omega
      | succ j' =>
          rw [Nat.pow_succ, Nat.pow_succ]
          have hih : 2 ^ (Nat.succ j') < 3 ^ (Nat.succ j') := ih (by omega)
          have h1 : 2 ^ (Nat.succ j') * 2 < 2 ^ (Nat.succ j') * 3 :=
            Nat.mul_lt_mul_of_pos_left (by omega : 2 < 3) (Nat.pow_pos (by omega))
          have h2 : 2 ^ (Nat.succ j') * 3 < 3 ^ (Nat.succ j') * 3 :=
            Nat.mul_lt_mul_of_pos_right hih (by omega)
          omega

/-- After `2j` ordinary Collatz steps we are at the `j`-th shortcut value. -/
theorem collatz_iterate_even (k q j : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (hj : j ≤ k) :
    Nat.iterate collatz (2 * j) (2 ^ k * q - 1) = 3 ^ j * 2 ^ (k - j) * q - 1 := by
  induction j with
  | zero =>
      simp [Nat.iterate]
  | succ j ih =>
      have hjle : j ≤ k := by omega
      have hjlt : j < k := by omega
      rw [show 2 * (j + 1) = 2 + 2 * j by omega]
      rw [Nat.iterate_add collatz 2 (2 * j)]
      rw [ih hjle]
      have hodd' : (3 ^ j * 2 ^ (k - j) * q - 1) % 2 = 1 := by
        rw [← iterate_shortcut_formula k q j hk hq hjle]
        exact iterate_shortcut_odd k q j hk hq hjlt
      rw [collatz_twice_odd _ hodd']
      exact shortcut_pow_formula k q j hk hq hjlt

/-- The initial values are nonincreasing under the shortcut indexing:
    `3^j 2^(k-j) q ≥ 2^k q` for `j ≤ k`. -/
private theorem pow_product_ge (k q j : Nat) (hq : 1 ≤ q) (hj : j ≤ k) :
    2 ^ k * q ≤ 3 ^ j * 2 ^ (k - j) * q := by
  by_cases hj0 : j = 0
  · subst j
    simp
  · have hj1 : 1 ≤ j := by omega
    have hkexp : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
      have h : j + (k - j) = k := by omega
      have hp : 2 ^ k = 2 ^ (j + (k - j)) := congrArg (fun e : Nat => 2 ^ e) h.symm
      rw [hp, Nat.pow_add]
    rw [hkexp]
    have hpow_le : 2 ^ j ≤ 3 ^ j := Nat.le_of_lt (two_pow_lt_three_pow j hj1)
    have hfac : 0 < 2 ^ (k - j) * q :=
      Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    have hmul : 2 ^ j * (2 ^ (k - j) * q) ≤ 3 ^ j * (2 ^ (k - j) * q) :=
      Nat.mul_le_mul_right _ hpow_le
    simpa [Nat.mul_assoc] using hmul

/-- Proposition 4 (glide inequality): for `1 ≤ t ≤ 2k`, `collatz^t n > n`. -/
theorem collatz_iterate_gt_initial (k q t : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * k) :
    Nat.iterate collatz t (2 ^ k * q - 1) > 2 ^ k * q - 1 := by
  have hcases : t % 2 = 0 ∨ t % 2 = 1 := by
    have := Nat.mod_lt t (by omega : 0 < 2)
    omega
  rcases hcases with h0 | h1
  · have ht_eq : t = 2 * (t / 2) := by
      have hdm := Nat.div_add_mod t 2
      omega
    let j : Nat := t / 2
    have hj1 : 1 ≤ j := by
      dsimp [j]
      omega
    have hjk : j ≤ k := by
      dsimp [j]
      omega
    rw [ht_eq, collatz_iterate_even k q j hk hq hjk]
    have hkexp : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
      have h : j + (k - j) = k := by omega
      have hp : 2 ^ k = 2 ^ (j + (k - j)) := congrArg (fun e : Nat => 2 ^ e) h.symm
      rw [hp, Nat.pow_add]
    rw [hkexp]
    have hpow : 2 ^ j < 3 ^ j := two_pow_lt_three_pow j hj1
    have hfac : 0 < 2 ^ (k - j) * q :=
      Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    have hmul : 2 ^ j * (2 ^ (k - j) * q) < 3 ^ j * (2 ^ (k - j) * q) :=
      Nat.mul_lt_mul_of_pos_right hpow hfac
    have hmul' : 2 ^ j * 2 ^ (k - j) * q < 3 ^ j * 2 ^ (k - j) * q := by
      simpa [Nat.mul_assoc] using hmul
    have hB : 1 ≤ 2 ^ j * 2 ^ (k - j) * q :=
      one_le_prod 2 j (k - j) q (by omega) hq
    omega
  · have ht_eq : t = 2 * (t / 2) + 1 := by
      have hdm := Nat.div_add_mod t 2
      omega
    let j : Nat := t / 2
    have hjlt : j < k := by
      dsimp [j]
      omega
    have hjk : j ≤ k := by omega
    rw [ht_eq]
    rw [show 2 * j + 1 = 1 + 2 * j by omega]
    rw [Nat.iterate_add collatz 1 (2 * j)]
    simp only [Nat.iterate]
    rw [collatz_iterate_even k q j hk hq hjk]
    have hodd' : (3 ^ j * 2 ^ (k - j) * q - 1) % 2 = 1 := by
      rw [← iterate_shortcut_formula k q j hk hq hjk]
      exact iterate_shortcut_odd k q j hk hq hjlt
    rw [collatz_of_odd _ hodd']
    have hge := pow_product_ge k q j hq hjk
    have hn : 1 ≤ 2 ^ k * q - 1 := by
      have hpow2 : 2 ≤ 2 ^ k := by
        have hk' : k = 1 + (k - 1) := by omega
        rw [hk', Nat.pow_add]
        have hp : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow (k - 1) 2 (by omega)
        omega
      have hprod : 2 ≤ 2 ^ k * q := Nat.mul_le_mul hpow2 hq
      omega
    omega

/-- The glide bound stated in Proposition 4: `G(2^k q - 1) ≥ 2k + 1`,
    i.e. the orbit has not dropped back to its start by step `2k`. -/
theorem glide_at_least_two_mul (k q : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    GlideAtLeast (2 ^ k * q - 1) (2 * k) := by
  intro t ht1 ht2
  exact collatz_iterate_gt_initial k q t hk hq ht1 ht2

/-- Proposition 4 (endpoint): after `2k` ordinary Collatz steps the value is
    `3^k * q - 1`. -/
theorem collatz_iterate_two_mul (k q : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    Nat.iterate collatz (2 * k) (2 ^ k * q - 1) = 3 ^ k * q - 1 := by
  rw [collatz_iterate_even k q k hk hq (by omega)]
  simp

end FuelLaw
end CollatzAdicBase
