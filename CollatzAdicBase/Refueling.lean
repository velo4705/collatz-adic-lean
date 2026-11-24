import CollatzAdicBase.FuelLaw

namespace CollatzAdicBase

namespace Refueling

/-- The 2-adic valuation `v₂(n)` (with the convention `v₂(0) = 0`).
    For odd `n`, `τ(n) = v₂(n+1)` is the number of trailing 1-bits. -/
def v2 (n : Nat) : Nat :=
  if h0 : n = 0 then 0
  else if he : n % 2 = 0 then v2 (n / 2) + 1
  else 0
termination_by n
decreasing_by
  have hn : 0 < n := Nat.pos_of_ne_zero h0
  exact Nat.div_lt_self hn (by omega)

theorem v2_zero : v2 0 = 0 := by
  rw [v2]
  simp

theorem v2_of_odd {n : Nat} (h : n % 2 = 1) : v2 n = 0 := by
  rw [v2]
  have hn : n ≠ 0 := by omega
  simp [hn, h]

theorem v2_of_even {n : Nat} (hn : n ≠ 0) (h : n % 2 = 0) :
    v2 n = v2 (n / 2) + 1 := by
  rw [v2]
  simp [hn, h]

theorem three_pow_odd (k : Nat) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- `v₂(2^s · u) = s + v₂(u)` for `u ≥ 1`. -/
theorem v2_two_pow_mul (s u : Nat) (hu : 1 ≤ u) : v2 (2 ^ s * u) = s + v2 u := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hrew : 2 ^ Nat.succ s * u = 2 * (2 ^ s * u) := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hrew]
      have hne : 2 * (2 ^ s * u) ≠ 0 := by
        have hp : 0 < 2 ^ s := Nat.pow_pos (by omega : 0 < 2)
        have hpu : 0 < 2 ^ s * u := Nat.mul_pos hp (by omega)
        omega
      have hmod : (2 * (2 ^ s * u)) % 2 = 0 := by omega
      rw [v2_of_even hne hmod]
      rw [Nat.mul_div_right _ (by omega : 0 < 2)]
      rw [ih]
      omega

/-- `2^r ∣ n ↔ r ≤ v₂(n)` for `n ≥ 1`. -/
theorem two_pow_dvd_iff_le_v2 (n r : Nat) (hn : 1 ≤ n) :
    2 ^ r ∣ n ↔ r ≤ v2 n := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
      constructor
      · intro h
        rcases h with ⟨t, ht⟩
        have hpos_t : 1 ≤ t := by
          by_cases ht0 : t = 0
          · subst t
            simp at ht
            omega
          · omega
        have hEq : 2 ^ Nat.succ r * t = 2 * (2 ^ r * t) := by
          rw [Nat.pow_succ]
          ac_rfl
        have hn_even : n % 2 = 0 := by
          rw [ht, hEq]
          omega
        have hn_ne : n ≠ 0 := by omega
        have hv_n : v2 n = v2 (n / 2) + 1 := v2_of_even hn_ne hn_even
        have hhalf_eq : n / 2 = 2 ^ r * t := by
          rw [ht, hEq, Nat.mul_div_right _ (by omega : 0 < 2)]
        have hhalf_pos : 1 ≤ n / 2 := by omega
        have hle : r ≤ v2 (n / 2) := (ih (n / 2) hhalf_pos).mp ⟨t, hhalf_eq⟩
        rw [hv_n]
        omega
      · intro hle
        have hn_even : n % 2 = 0 := by
          by_cases he : n % 2 = 0
          · exact he
          · have hodd : n % 2 = 1 := by omega
            have hv0 : v2 n = 0 := v2_of_odd hodd
            omega
        have hn_ne : n ≠ 0 := by omega
        have hv_n : v2 n = v2 (n / 2) + 1 := v2_of_even hn_ne hn_even
        rw [hv_n] at hle
        have hn2 : 2 ≤ n := by omega
        have hhalf_pos : 1 ≤ n / 2 := Nat.div_pos hn2 (by omega)
        have hle' : r ≤ v2 (n / 2) := by omega
        rcases (ih (n / 2) hhalf_pos).mpr hle' with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        have hdvd2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn_even
        have hcancel : n / 2 * 2 = n := Nat.div_mul_cancel hdvd2
        rw [← hcancel, ht, Nat.pow_succ]
        ac_rfl

/-- Repeated halving: `collatz^s(2^s · u) = u`. -/
theorem iterate_collatz_halve_pow (s u : Nat) :
    Nat.iterate collatz s (2 ^ s * u) = u := by
  induction s with
  | zero => simp [Nat.iterate]
  | succ s ih =>
      change Nat.iterate collatz s (collatz (2 ^ Nat.succ s * u)) = u
      have hEq : 2 ^ Nat.succ s * u = 2 * (2 ^ s * u) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hcoll : collatz (2 ^ Nat.succ s * u) = 2 ^ s * u := by
        unfold collatz
        have hmod : (2 ^ Nat.succ s * u) % 2 = 0 := by
          rw [hEq]
          omega
        rw [hmod, hEq, Nat.mul_div_right _ (by omega : 0 < 2)]
        simp
      rw [hcoll]
      exact ih

/-- Fuel exhaustion: after `2k` Collatz steps, `3^k q - 1` has zero trailing
    ones when `q` is odd (because its successor `3^k q` is odd). -/
theorem fuel_exhausted (k q : Nat) (hqodd : q % 2 = 1) : v2 (3 ^ k * q) = 0 := by
  apply v2_of_odd
  rw [Nat.mul_mod, three_pow_odd, hqodd]

/-- The odd core `u` of a positive exhausted block is positive. -/
private theorem odd_core_pos (k q s u : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (hu : 3 ^ k * q = 2 ^ s * u + 1) : 1 ≤ u := by
  have h3 : 3 ≤ 3 ^ k := by
    have hk' : k = 1 + (k - 1) := by omega
    rw [hk', Nat.pow_add]
    have hp : 1 ≤ 3 ^ (k - 1) := Nat.one_le_pow (k - 1) 3 (by omega)
    omega
  have hprod : 3 ≤ 3 ^ k * q := by
    have hmul := Nat.mul_le_mul h3 hq
    simpa using hmul
  have hpu : 2 ≤ 2 ^ s * u := by omega
  by_cases hu0 : u = 0
  · subst u
    simp at hpu
  · omega

/-- After burning the initial `k`-bit fuel block (`2k` Collatz steps) and `s`
    further halvings, the orbit reaches the odd core `u = (3^k q - 1) / 2^s`. -/
theorem refuel_landing (k q s u : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (_hs : 1 ≤ s)
    (hu : 3 ^ k * q = 2 ^ s * u + 1) :
    Nat.iterate collatz (2 * k + s) (2 ^ k * q - 1) = u := by
  have hidx : 2 * k + s = s + 2 * k := by omega
  rw [hidx, Nat.iterate_add]
  rw [FuelLaw.collatz_iterate_two_mul k q hk hq]
  have hsub : 3 ^ k * q - 1 = 2 ^ s * u := by omega
  rw [hsub]
  exact iterate_collatz_halve_pow s u

/-- The odd core `u` is precisely the `2^s`-part of the exhausted block:
    `v₂(3^k q - 1) = s`. -/
theorem refuel_exhausts_fuel (k q s u : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (_hs : 1 ≤ s)
    (hu : 3 ^ k * q = 2 ^ s * u + 1) (huodd : u % 2 = 1) :
    v2 (3 ^ k * q - 1) = s := by
  have hsub : 3 ^ k * q - 1 = 2 ^ s * u := by omega
  rw [hsub, v2_two_pow_mul s u (odd_core_pos k q s u hk hq hu), v2_of_odd huodd]
  omega

/-- Algebraic shift underlying the refueling congruence:
    `2^(s+r) ∣ 3^k q + 2^s - 1  ↔  2^r ∣ u + 1`. -/
theorem refuel_divisibility_shift (k q s u r : Nat) (_hs : 1 ≤ s)
    (hu : 3 ^ k * q = 2 ^ s * u + 1) :
    2 ^ (s + r) ∣ 3 ^ k * q + 2 ^ s - 1 ↔ 2 ^ r ∣ u + 1 := by
  have hEq : 3 ^ k * q + 2 ^ s - 1 = 2 ^ s * (u + 1) := by
    rw [hu, Nat.mul_add]
    omega
  rw [hEq, Nat.pow_add]
  exact Nat.mul_dvd_mul_iff_left (Nat.pow_pos (by omega : 0 < 2))

/-- **Mid-flight refueling congruence theorem.** Burn an initial `k`-bit fuel
    block from `n = 2^k q - 1` (`q` odd, `k ≥ 1`).  Writing the exhausted value
    as `3^k q - 1 = 2^s u` (i.e. `3^k q = 2^s u + 1`) with `u` odd, the next odd landing `u` refills
    its trailing-ones reservoir by at least `r` bits exactly when

        `3^k q ≡ 1 - 2^s  (mod 2^(s+r))`,

    i.e. `2^(s+r) ∣ 3^k q + 2^s - 1`.  Equivalently `r ≤ v₂(u+1)`. -/
theorem refuel_congruence (k q s u r : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hu : 3 ^ k * q = 2 ^ s * u + 1) :
    r ≤ v2 (u + 1) ↔ 2 ^ (s + r) ∣ 3 ^ k * q + 2 ^ s - 1 := by
  exact Iff.trans
    (two_pow_dvd_iff_le_v2 (u + 1) r (by
      have hu1 := odd_core_pos k q s u hk hq hu
      omega)).symm
    (refuel_divisibility_shift k q s u r hs hu).symm

/-- The refueling criterion is a genuine congruence condition on `q`:
    it depends only on `q mod 2^(s+r)`. -/
theorem refuel_mod_invariant (k q q0 s r : Nat) (_hk : 1 ≤ k) (_hq : 1 ≤ q)
    (_hs : 1 ≤ s) (_hr : 1 ≤ r)
    (hmod : q % 2 ^ (s + r) = q0 % 2 ^ (s + r)) :
    2 ^ (s + r) ∣ 3 ^ k * q + 2 ^ s - 1 ↔
      2 ^ (s + r) ∣ 3 ^ k * q0 + 2 ^ s - 1 := by
  let M := 2 ^ (s + r)
  change q % M = q0 % M at hmod
  change M ∣ 3 ^ k * q + 2 ^ s - 1 ↔ M ∣ 3 ^ k * q0 + 2 ^ s - 1
  have hmulmod : (3 ^ k * q) % M = (3 ^ k * q0) % M := by
    calc
      (3 ^ k * q) % M = ((3 ^ k % M) * (q % M)) % M := Nat.mul_mod _ _ _
      _ = ((3 ^ k % M) * (q0 % M)) % M := by rw [hmod]
      _ = (3 ^ k * q0) % M := (Nat.mul_mod _ _ _).symm
  have haddmod : (3 ^ k * q + (2 ^ s - 1)) % M =
      (3 ^ k * q0 + (2 ^ s - 1)) % M := by
    calc
      (3 ^ k * q + (2 ^ s - 1)) % M =
          ((3 ^ k * q) % M + (2 ^ s - 1) % M) % M := Nat.add_mod _ _ _
      _ = ((3 ^ k * q0) % M + (2 ^ s - 1) % M) % M := by rw [hmulmod]
      _ = (3 ^ k * q0 + (2 ^ s - 1)) % M := (Nat.add_mod _ _ _).symm
  have hpow1 : 1 ≤ 2 ^ s := Nat.one_le_pow s 2 (by omega)
  have hl : 3 ^ k * q + 2 ^ s - 1 = 3 ^ k * q + (2 ^ s - 1) :=
    Nat.add_sub_assoc hpow1 (3 ^ k * q)
  have hr' : 3 ^ k * q0 + 2 ^ s - 1 = 3 ^ k * q0 + (2 ^ s - 1) :=
    Nat.add_sub_assoc hpow1 (3 ^ k * q0)
  have heqmod : (3 ^ k * q + 2 ^ s - 1) % M =
      (3 ^ k * q0 + 2 ^ s - 1) % M := by
    rw [hl, hr']
    exact haddmod
  constructor
  · intro h
    rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
    rwa [heqmod] at h
  · intro h
    rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
    rwa [← heqmod] at h

/-- Kernel-checked concrete witnesses from Section 6 of Paper 2. -/

-- n = 6,631,675: k = 2, q = 1,657,919, s = 1, u = 7,460,635, r = 2.
example : (3 ^ 2 * 1657919 + 2 ^ 1 - 1) % 2 ^ (1 + 2) = 0 := by decide
example : Nat.iterate collatz (2 * 2 + 1) (2 ^ 2 * 1657919 - 1) = 7460635 := by decide

-- The tau = 18 backbone: m = 43,841,695, k = 5, q = 1,370,053, s = 1,
-- u = 166,461,439.  The criterion is 3^5 q = -1 (mod 2^19), and the unique
-- residue class of q modulo 2^19 is q = 321,477.
example : (3 ^ 5 * 1370053 + 2 ^ 1 - 1) % 2 ^ (1 + 18) = 0 := by decide
example : (3 ^ 5 * 1370053) % 2 ^ (1 + 18) = 524287 := by decide
example : 1370053 % 2 ^ (1 + 18) = 321477 := by decide

end Refueling
end CollatzAdicBase
