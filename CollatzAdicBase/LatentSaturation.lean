import Init

/-!
# Latent saturation of Collatz-adic cycles

This file formalizes the exact lifting/saturation lemma used in the analysis of
the "latent cycle" problem of Paper 4.

A reduced rational with an odd denominator is represented by a pair
`(a, d) : ℕ × ℕ` with `a > 0`, `d > 0`, `d % 2 = 1` and `Nat.Coprime a d`.  The
reduced Collatz step is

* `(a, d) ↦ (a / 2, d)` when `a` is even,
* `(a, d) ↦ ((3a + d) / g, d / g)` with `g = gcd (3a + d) d` when `a` is odd.

Every nontrivial cycle has a denominator coprime to 3 (the 3-adic valuation of
the denominator never increases, and a cycle containing a 3-stripping odd step
could not close).  Its *home denominator* is therefore some `d'` with
`Nat.Coprime d' 3`.  The levels above the home denominator are `3^k * d'`, and
each odd step at level `k ≥ 1` strips exactly one factor of 3:

    ratStep (a, 3^k d') = (a + 3^(k-1) d', 3^(k-1) d').

After `k` such steps and `E` interleaved even (halving) steps the numerator `A`
at the home level satisfies `2^E * A = a + d' * t` for some `t`, hence
`2^E * A ≡ a (mod d')`.  Combined with the cycle equation
`Nat.Coprime a d → d ∣ 2^E - 3^M` this is the algebraic lifting map used to
determine `k_min(d')`.

No custom axioms and no `sorry` are used; the only imported module is `Init`.
-/

namespace CollatzAdicBase

namespace LatentSaturation

abbrev RatState := Nat × Nat

/-- A valid reduced rational state: positive numerator and denominator,
    odd denominator, and the two components coprime. -/
def Valid (s : RatState) : Prop :=
  0 < s.1 ∧ 0 < s.2 ∧ s.2 % 2 = 1 ∧ Nat.Coprime s.1 s.2

/-- The reduced Collatz step on rational states. -/
def ratStep (s : RatState) : RatState :=
  if s.1 % 2 = 0 then (s.1 / 2, s.2)
  else
    let g := Nat.gcd (3 * s.1 + s.2) s.2
    ((3 * s.1 + s.2) / g, s.2 / g)

theorem ratStep_even (a d : Nat) (h : a % 2 = 0) : ratStep (a, d) = (a / 2, d) := by
  simp [ratStep, h]

theorem ratStep_odd (a d : Nat) (h : a % 2 = 1) :
    ratStep (a, d) =
      ((3 * a + d) / Nat.gcd (3 * a + d) d, d / Nat.gcd (3 * a + d) d) := by
  simp [ratStep, h]

/-- `3^k d' = 3 * (3^(k-1) d')` for `k ≥ 1`. -/
theorem pow_three_factor (k d' : Nat) (hk : 1 ≤ k) :
    3 ^ k * d' = 3 * (3 ^ (k - 1) * d') := by
  have hp : 3 ^ k = 3 ^ (k - 1) * 3 := by
    have h : k = (k - 1) + 1 := by omega
    conv =>
      lhs
      rw [h]
    rw [Nat.pow_succ]
  rw [hp]
  ac_rfl

/-- **Exact gcd at a lifted level.**  If `a` is odd and coprime to `3^k d'`,
    then `gcd (3a + 3^k d') (3^k d') = 3`.  Consequently each odd step removes
    exactly one factor of 3 from the denominator. -/
theorem gcd_lift (k a d' : Nat) (hk : 1 ≤ k) (_hodd : a % 2 = 1)
    (hcop : Nat.Coprime a (3 ^ k * d')) :
    Nat.gcd (3 * a + 3 ^ k * d') (3 ^ k * d') = 3 := by
  let E := 3 ^ (k - 1) * d'
  have hD : 3 ^ k * d' = 3 * E := by
    dsimp [E]
    exact pow_three_factor k d' hk
  have hnum : 3 * a + 3 ^ k * d' = 3 * (a + E) := by
    rw [hD]
    omega
  have hgcd_a_E : Nat.gcd a E = 1 := by
    have h1 : Nat.gcd a E ∣ a := Nat.gcd_dvd_left a E
    have h2 : Nat.gcd a E ∣ 3 * E :=
      Nat.dvd_trans (Nat.dvd_mul_left (Nat.gcd a E) 3)
        (Nat.mul_dvd_mul_left 3 (Nat.gcd_dvd_right a E))
    have hdvd : Nat.gcd a E ∣ Nat.gcd a (3 * E) := Nat.dvd_gcd h1 h2
    have hcop' : Nat.gcd a (3 * E) = 1 := by
      rw [← hD]
      exact hcop.gcd_eq_one
    rw [hcop'] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  have hgcd_E : Nat.gcd (a + E) E = 1 := by
    have h := Nat.gcd_add_mul_left_left E a 1
    simpa using (h.trans hgcd_a_E)
  rw [hnum, hD, Nat.gcd_mul_left, hgcd_E]

/-- **Lifting lemma.**  The odd step at level `k ≥ 1` is exactly
    `(a, 3^k d') ↦ (a + 3^(k-1) d', 3^(k-1) d')`: one factor of 3 is stripped
    and the numerator is incremented by `3^(k-1) d'`. -/
theorem ratStep_lift (k a d' : Nat) (hk : 1 ≤ k) (hodd : a % 2 = 1)
    (hcop : Nat.Coprime a (3 ^ k * d')) :
    ratStep (a, 3 ^ k * d') = (a + 3 ^ (k - 1) * d', 3 ^ (k - 1) * d') := by
  rw [ratStep_odd a (3 ^ k * d') hodd]
  rw [gcd_lift k a d' hk hodd hcop]
  let E := 3 ^ (k - 1) * d'
  have hD : 3 ^ k * d' = 3 * E := by
    dsimp [E]
    exact pow_three_factor k d' hk
  have hnum : 3 * a + 3 ^ k * d' = 3 * (a + E) := by
    rw [hD]
    omega
  rw [hnum, hD]
  rw [Nat.mul_div_right (a + E) (by omega : 0 < 3)]
  rw [Nat.mul_div_right E (by omega : 0 < 3)]

/-- **Lifting congruence.**  If `2^E * A = a + d' * t`, then `2^E * A` and `a`
    are congruent modulo `d'`.  This is the congruence
    `2^E A ≡ a (mod d')` induced by the `k` odd denominator-stripping steps
    (with `E` interleaved halvings). -/
theorem lift_congruence (E a A d' t : Nat) (h : 2 ^ E * A = a + d' * t) :
    (2 ^ E * A) % d' = a % d' := by
  rw [h]
  simp [Nat.add_mod]

/-- **Cycle equation.**  If a cycle at denominator `d` with `E` halving steps
    and `M` odd steps satisfies `(2^E - 3^M) * a = d * t` and `a` is coprime to
    `d`, then `d ∣ 2^E - 3^M`. -/
theorem cycle_dvd_pow_sub (E M a d t : Nat) (hcop : Nat.Coprime a d)
    (h : (2 ^ E - 3 ^ M) * a = d * t) : d ∣ 2 ^ E - 3 ^ M := by
  have hdvd : d ∣ (2 ^ E - 3 ^ M) * a := by
    rw [h]
    exact Nat.dvd_mul_right d t
  exact hcop.symm.dvd_of_dvd_mul_right hdvd

/-- **Saturation, part 1.**  An even step leaves the denominator unchanged. -/
theorem den_even (a d : Nat) (h : a % 2 = 0) : (ratStep (a, d)).2 = d := by
  rw [ratStep_even a d h]

/-- **Saturation, part 2.**  The denominator after an odd step divides the
    old denominator. -/
theorem den_odd_dvd (a d : Nat) (h : a % 2 = 1) : (ratStep (a, d)).2 ∣ d := by
  rw [ratStep_odd a d h]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right (3 * a + d) d)

/-- **Saturation, part 3.**  A denominator coprime to 3 stays coprime to 3
    under every step.  Hence once the 3-part has been stripped, it never
    returns, and every cycle lives at a 3-free home denominator. -/
theorem three_free_preserved (a d : Nat) (_hcop : Nat.Coprime a d)
    (h3 : ¬ 3 ∣ d) : ¬ 3 ∣ (ratStep (a, d)).2 := by
  by_cases he : a % 2 = 0
  · rw [den_even a d he]
    exact h3
  · have he1 : a % 2 = 1 := by
      have hcases := Nat.mod_two_eq_zero_or_one a
      omega
    intro h3new
    have hdvd := den_odd_dvd a d he1
    rw [ratStep_odd a d he1] at h3new hdvd
    rcases h3new with ⟨c, hc⟩
    rcases hdvd with ⟨e, heq⟩
    apply h3
    refine ⟨c * e, ?_⟩
    rw [heq, hc]
    ac_rfl

/-- **Saturation, part 4.**  At a lifted level `k ≥ 1`, an odd step removes
    one factor of 3 from the denominator: the new denominator is exactly
    `3^(k-1) d'`. -/
theorem den_at_lifted_level (k a d' : Nat) (hk : 1 ≤ k) (hodd : a % 2 = 1)
    (hcop : Nat.Coprime a (3 ^ k * d')) :
    (ratStep (a, 3 ^ k * d')).2 = 3 ^ (k - 1) * d' := by
  rw [ratStep_lift k a d' hk hodd hcop]

/-- **Well-formedness.**  A valid state stays valid: positive numerator,
    positive odd denominator, and coprimality are preserved by both branch of
    the step. -/
theorem ratStep_valid {s : RatState} (hs : Valid s) : Valid (ratStep s) := by
  rcases s with ⟨a, d⟩
  rcases hs with ⟨ha, hd, hdodd, hcop⟩
  by_cases he : a % 2 = 0
  · rw [ratStep_even a d he]
    have hadvd : a / 2 ∣ a := by
      refine ⟨2, ?_⟩
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero he)).symm
    have hapos : 0 < a / 2 := Nat.div_pos (by omega : 2 ≤ a) (by omega : 0 < 2)
    refine ⟨hapos, hd, hdodd, ?_⟩
    have hcomp : Nat.gcd (a / 2) d ∣ a :=
      Nat.dvd_trans (Nat.gcd_dvd_left (a / 2) d) hadvd
    have hd1 : Nat.gcd (a / 2) d ∣ Nat.gcd a d :=
      Nat.dvd_gcd hcomp (Nat.gcd_dvd_right (a / 2) d)
    rw [hcop.gcd_eq_one] at hd1
    exact Nat.eq_one_of_dvd_one hd1
  · have he1 : a % 2 = 1 := by
      have hcases := Nat.mod_two_eq_zero_or_one a
      omega
    rw [ratStep_odd a d he1]
    let g := Nat.gcd (3 * a + d) d
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hd
    have hgd : g ∣ d := Nat.gcd_dvd_right (3 * a + d) d
    have hgn : g ∣ 3 * a + d := Nat.gcd_dvd_left (3 * a + d) d
    have hnpos : 0 < (3 * a + d) / g :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hgn) hgpos
    have hdpos' : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hgpos
    have hdodd' : (d / g) % 2 = 1 := by
      have hgodd : g % 2 = 1 := by
        have hcases := Nat.mod_two_eq_zero_or_one g
        rcases hcases with hg0 | hg1
        · have hgodddvd : g ∣ d := hgd
          rcases hgodddvd with ⟨m, hm⟩
          rcases Nat.dvd_of_mod_eq_zero hg0 with ⟨q, hq⟩
          have hd_even : d % 2 = 0 := Nat.mod_eq_zero_of_dvd ⟨q * m, by
            rw [hm, hq]
            ac_rfl⟩
          omega
        · exact hg1
      have hdmul : d = (d / g) * g := (Nat.div_mul_cancel hgd).symm
      have hcases := Nat.mod_two_eq_zero_or_one (d / g)
      rcases hcases with hq0 | hq1
      · rcases Nat.dvd_of_mod_eq_zero hq0 with ⟨q, hq⟩
        have hd_even : d % 2 = 0 := Nat.mod_eq_zero_of_dvd ⟨q * g, by
          rw [hdmul, hq]
          ac_rfl⟩
        omega
      · exact hq1
    refine ⟨hnpos, hdpos', hdodd', ?_⟩
    exact Nat.coprime_div_gcd_div_gcd hgpos

#print axioms gcd_lift
#print axioms ratStep_lift
#print axioms lift_congruence
#print axioms cycle_dvd_pow_sub
#print axioms den_at_lifted_level
#print axioms three_free_preserved
#print axioms ratStep_valid

end LatentSaturation
end CollatzAdicBase
