import CollatzAdicBase.FuelLaw
import CollatzAdicBase.Refueling

set_option maxRecDepth 100000

/-!
# Stopping-time density over 2-adic residue classes (Paper 7)

This module attacks the second global barrier: multi-block trajectory drift and
finite stopping-time certificates over 2-adic residue classes.

Section 1 composes `FuelLaw` with `Refueling` into one exact two-block affine
identity connecting `fuel_burn` directly to `refuel_congruence`:

    2^(k+s) * u + 2^k = 3^k * (2^k*q - 1) + 3^k,

and derives the exact drift threshold `u < n ↔ 3^k*n + (3^k - 2^k) < 2^(k+s)*n`.

Section 2 proves explicit `iterate < n` drop bounds for the dominating residue
families `n ≡ 1 (mod 4)` and `n ≡ 3 (mod 16)` (5/8 of all odd classes).

Section 3 implements symbolic 2-adic residue-class backtracking: an affine
template `T^t(n) = (a*n+b)/2^e` is propagated along a residue class modulo
`2^K` and lifts to all members of the class.  A kernel-checked finite
computation certifies 109 of the 128 odd classes modulo `2^8 = 256`, giving
residue density `109/128` and survivor density `δ(8) = 19/128`.

No `sorry`, no `admit`, no custom axioms.
-/

namespace CollatzAdicBase

namespace StoppingTimeDensity

-- =========================================================================
-- Section 1 — exact two-block composition and drift
-- =========================================================================

/-- The exhausted fuel block: `3^k q - 1 = 2^s u`. -/
theorem two_block_exhaust (k q s u : Nat) (_hk : 1 ≤ k) (_hq : 1 ≤ q) (_hs : 1 ≤ s)
    (hu : 3 ^ k * q = 2 ^ s * u + 1) :
    2 ^ s * u = 3 ^ k * q - 1 := by
  omega

/-- `2^k q ≥ 2` for `k ≥ 1, q ≥ 1`. -/
private theorem two_pow_mul_ge_two (k q : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    2 ≤ 2 ^ k * q := by
  have hk' : k = 1 + (k - 1) := by omega
  rw [hk', Nat.pow_add]
  have hp : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow (k - 1) 2 (by omega)
  have hmul : 1 ≤ 2 ^ (k - 1) * q := by
    simpa using Nat.mul_le_mul hp hq
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hmul

/-- The exact two-block affine identity.  Writing `n = 2^k q - 1`, one
    burn + refuel cycle maps `n ↦ u` with

        2^(k+s) * u + 2^k = 3^k * n + 3^k. -/
theorem two_block_affine_plus (k q s u : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (_hs : 1 ≤ s)
    (hu : 3 ^ k * q = 2 ^ s * u + 1) :
    2 ^ (k + s) * u + 2 ^ k = 3 ^ k * (2 ^ k * q - 1) + 3 ^ k := by
  have h2kq : 1 ≤ 2 ^ k * q := Nat.le_trans (by omega : 1 ≤ 2) (two_pow_mul_ge_two k q hk hq)
  have hn : 2 ^ k * q - 1 + 1 = 2 ^ k * q := Nat.sub_add_cancel h2kq
  have hpadd : 2 ^ (k + s) = 2 ^ k * 2 ^ s := by rw [Nat.pow_add]
  calc
    2 ^ (k + s) * u + 2 ^ k = 2 ^ k * (2 ^ s * u) + 2 ^ k := by
      rw [hpadd, Nat.mul_assoc]
    _ = 2 ^ k * (2 ^ s * u + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ = 2 ^ k * (3 ^ k * q) := by rw [← hu]
    _ = 3 ^ k * (2 ^ k * q) := by ac_rfl
    _ = 3 ^ k * ((2 ^ k * q - 1) + 1) := by rw [hn]
    _ = 3 ^ k * (2 ^ k * q - 1) + 3 ^ k := by rw [Nat.mul_add, Nat.mul_one]

/-- `2^k ≤ 3^k`. -/
private theorem two_pow_le_three_pow (k : Nat) : 2 ^ k ≤ 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih (by omega)

/-- The two-block multiplier identity in subtraction form:

        2^(k+s) * u = 3^k * (2^k q - 1) + (3^k - 2^k). -/
theorem two_block_affine (k q s u : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hu : 3 ^ k * q = 2 ^ s * u + 1) :
    2 ^ (k + s) * u = 3 ^ k * (2 ^ k * q - 1) + (3 ^ k - 2 ^ k) := by
  have hplus := two_block_affine_plus k q s u hk hq hs hu
  have h3ge2 : 2 ^ k ≤ 3 ^ k := two_pow_le_three_pow k
  have hrewrite :
      3 ^ k * (2 ^ k * q - 1) + 3 ^ k =
        3 ^ k * (2 ^ k * q - 1) + (3 ^ k - 2 ^ k) + 2 ^ k := by
    omega
  rw [hrewrite] at hplus
  exact Nat.add_right_cancel hplus

/-- The exact composition: the orbit lands on `u` after `2k+s` steps, and the
    fuel identity feeds directly into the refueling congruence. -/
theorem two_block_composition (k q s u : Nat) (hk : 1 ≤ k) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hu : 3 ^ k * q = 2 ^ s * u + 1) :
    Nat.iterate collatz (2 * k + s) (2 ^ k * q - 1) = u ∧
      3 ^ k * q + 2 ^ s - 1 = 2 ^ s * (u + 1) := by
  constructor
  · exact Refueling.refuel_landing k q s u hk hq hs hu
  · rw [hu, Nat.mul_add]
    omega

/-- Connecting the composition to `refuel_congruence`: the same divisibility
    can be read on the burned block or on the affine image. -/
theorem two_block_refuel_congruence (k q s u r : Nat)
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hs : 1 ≤ s) (hu : 3 ^ k * q = 2 ^ s * u + 1) :
    r ≤ Refueling.v2 (u + 1) ↔ 2 ^ (s + r) ∣ 2 ^ s * (u + 1) := by
  rw [← (two_block_composition k q s u hk hq hs hu).2]
  exact Refueling.refuel_congruence k q s u r hk hq hs hu

/-- The exact logarithmic-drift threshold: the cycle drops iff the multiplier
    of the affine image is below `2^(k+s)`. -/
theorem two_block_drift_threshold (k q s u : Nat)
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hs : 1 ≤ s) (hu : 3 ^ k * q = 2 ^ s * u + 1) :
    u < 2 ^ k * q - 1 ↔
      3 ^ k * (2 ^ k * q - 1) + (3 ^ k - 2 ^ k) <
        2 ^ (k + s) * (2 ^ k * q - 1) := by
  have haff := two_block_affine k q s u hk hq hs hu
  constructor
  · intro hlt
    calc
      3 ^ k * (2 ^ k * q - 1) + (3 ^ k - 2 ^ k) = 2 ^ (k + s) * u := haff.symm
      _ < 2 ^ (k + s) * (2 ^ k * q - 1) :=
          Nat.mul_lt_mul_of_pos_left hlt (Nat.pow_pos (by omega))
  · intro hlt
    have hlt' : 2 ^ (k + s) * u < 2 ^ (k + s) * (2 ^ k * q - 1) := by
      calc
        2 ^ (k + s) * u = 3 ^ k * (2 ^ k * q - 1) + (3 ^ k - 2 ^ k) := haff
        _ < 2 ^ (k + s) * (2 ^ k * q - 1) := hlt
    exact (Nat.mul_lt_mul_left (Nat.pow_pos (by omega : 0 < 2))).mp hlt'

/-- A sufficient drift condition: if `3^k < 2^(k+s)` and `n` exceeds the
    additive constant, the two-block image is strictly smaller. -/
theorem two_block_drop_of_multiplier (k q s u : Nat)
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hs : 1 ≤ s) (hu : 3 ^ k * q = 2 ^ s * u + 1)
    (hbig : 3 ^ k < 2 ^ (k + s))
    (hlarge : 3 ^ k - 2 ^ k < (2 ^ (k + s) - 3 ^ k) * (2 ^ k * q - 1)) :
    u < 2 ^ k * q - 1 := by
  rw [two_block_drift_threshold k q s u hk hq hs hu]
  have hle : 3 ^ k ≤ 2 ^ (k + s) := Nat.le_of_lt hbig
  calc
    3 ^ k * (2 ^ k * q - 1) + (3 ^ k - 2 ^ k)
        < 3 ^ k * (2 ^ k * q - 1) + (2 ^ (k + s) - 3 ^ k) * (2 ^ k * q - 1) :=
          Nat.add_lt_add_left hlarge _
    _ = 2 ^ (k + s) * (2 ^ k * q - 1) := by
      rw [← Nat.add_mul]
      rw [Nat.add_sub_of_le hle]

-- =========================================================================
-- Section 2 — explicit drop bounds for the dominating residue families
-- =========================================================================

/-- Family `n ≡ 1 (mod 4)` (density 1/2 of odd classes): `G(n) = 3`. -/
theorem drop_one_mod_four (m : Nat) (hm : 1 ≤ m) :
    Nat.iterate collatz 3 (4 * m + 1) = 3 * m + 1 ∧
      3 * m + 1 < 4 * m + 1 := by
  have h1 : (4 * m + 1) % 2 = 1 := by omega
  have h2 : (12 * m + 4) % 2 = 0 := by omega
  have h3 : (6 * m + 2) % 2 = 0 := by omega
  have hd1 : (12 * m + 4) / 2 = 6 * m + 2 := by omega
  have hd2 : (6 * m + 2) / 2 = 3 * m + 1 := by omega
  have hs1 : collatz (4 * m + 1) = 12 * m + 4 := by
    rw [FuelLaw.collatz_of_odd (4 * m + 1) h1]
    omega
  have hs2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [FuelLaw.collatz_of_even (12 * m + 4) h2, hd1]
  have hs3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [FuelLaw.collatz_of_even (6 * m + 2) h3, hd2]
  constructor
  · simp [Nat.iterate, hs1, hs2, hs3]
  · omega

/-- Family `n ≡ 3 (mod 16)` (density 1/8 of odd classes): `G(n) = 6`. -/
theorem drop_three_mod_sixteen (m : Nat) :
    Nat.iterate collatz 6 (16 * m + 3) = 9 * m + 2 ∧
      9 * m + 2 < 16 * m + 3 := by
  have h1 : (16 * m + 3) % 2 = 1 := by omega
  have h2 : (48 * m + 10) % 2 = 0 := by omega
  have h3 : (24 * m + 5) % 2 = 1 := by omega
  have h4 : (72 * m + 16) % 2 = 0 := by omega
  have h5 : (36 * m + 8) % 2 = 0 := by omega
  have h6 : (18 * m + 4) % 2 = 0 := by omega
  have hd1 : (48 * m + 10) / 2 = 24 * m + 5 := by omega
  have hd2 : (72 * m + 16) / 2 = 36 * m + 8 := by omega
  have hd3 : (36 * m + 8) / 2 = 18 * m + 4 := by omega
  have hd4 : (18 * m + 4) / 2 = 9 * m + 2 := by omega
  have hs1 : collatz (16 * m + 3) = 48 * m + 10 := by
    rw [FuelLaw.collatz_of_odd (16 * m + 3) h1]
    omega
  have hs2 : collatz (48 * m + 10) = 24 * m + 5 := by
    rw [FuelLaw.collatz_of_even (48 * m + 10) h2, hd1]
  have hs3 : collatz (24 * m + 5) = 72 * m + 16 := by
    rw [FuelLaw.collatz_of_odd (24 * m + 5) h3]
    omega
  have hs4 : collatz (72 * m + 16) = 36 * m + 8 := by
    rw [FuelLaw.collatz_of_even (72 * m + 16) h4, hd2]
  have hs5 : collatz (36 * m + 8) = 18 * m + 4 := by
    rw [FuelLaw.collatz_of_even (36 * m + 8) h5, hd3]
  have hs6 : collatz (18 * m + 4) = 9 * m + 2 := by
    rw [FuelLaw.collatz_of_even (18 * m + 4) h6, hd4]
  constructor
  · simp [Nat.iterate, hs1, hs2, hs3, hs4, hs5, hs6]
  · omega

-- =========================================================================
-- Section 3 — affine residue templates and the K = 8 partition certificate
-- =========================================================================

/-- Denominator exponent of the affine template after t steps. -/
def affE (n : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => if (Nat.iterate collatz t n) % 2 = 0 then affE n t + 1 else affE n t

/-- Numerator slope of the affine template after t steps. -/
def affA (n : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => if (Nat.iterate collatz t n) % 2 = 0 then affA n t else 3 * affA n t

/-- Numerator constant of the affine template after t steps. -/
def affB (n : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => if (Nat.iterate collatz t n) % 2 = 0 then affB n t else 3 * affB n t + 2 ^ affE n t

/-- The affine invariant: `2^e * T^t(n) = a*n + b` with `a` odd. -/
theorem aff_spec (n t : Nat) :
    2 ^ affE n t * Nat.iterate collatz t n = affA n t * n + affB n t ∧
      affA n t % 2 = 1 := by
  induction t with
  | zero => simp [affA, affB, affE]
  | succ t ih =>
      rcases ih with ⟨hinv, haodd⟩
      by_cases hp : (Nat.iterate collatz t n) % 2 = 0
      · have hcoll : collatz (Nat.iterate collatz t n) = Nat.iterate collatz t n / 2 :=
          FuelLaw.collatz_of_even (Nat.iterate collatz t n) hp
        have hx : 2 * (Nat.iterate collatz t n / 2) = Nat.iterate collatz t n :=
          Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hp)
        simp [affA, affB, affE, hp]
        rw [Nat.iterate_succ_apply, hcoll, Nat.pow_succ, Nat.mul_assoc, hx, hinv]
        exact ⟨rfl, haodd⟩
      · have hp1 : (Nat.iterate collatz t n) % 2 = 1 := by omega
        have hcoll : collatz (Nat.iterate collatz t n) = 3 * Nat.iterate collatz t n + 1 :=
          FuelLaw.collatz_of_odd (Nat.iterate collatz t n) hp1
        simp [affA, affB, affE, hp]
        rw [Nat.iterate_succ_apply, hcoll]
        constructor
        · calc
            2 ^ affE n t * (3 * Nat.iterate collatz t n + 1)
                = 2 ^ affE n t * (3 * Nat.iterate collatz t n) + 2 ^ affE n t := by
                  rw [Nat.mul_add, Nat.mul_one]
            _ = 3 * (2 ^ affE n t * Nat.iterate collatz t n) + 2 ^ affE n t := by ac_rfl
            _ = 3 * (affA n t * n + affB n t) + 2 ^ affE n t := by rw [hinv]
            _ = 3 * affA n t * n + (3 * affB n t + 2 ^ affE n t) := by
                  rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
        · omega

/-- Equality of the first t parities. -/
def paritiesAgree (n r t : Nat) : Prop :=
  ∀ j, j < t → (Nat.iterate collatz j n) % 2 = (Nat.iterate collatz j r) % 2

/-- The affine coefficients depend only on the parity pattern. -/
theorem aff_eq_of_parities (n r t : Nat) (h : paritiesAgree n r t) :
    affA n t = affA r t ∧ affB n t = affB r t ∧ affE n t = affE r t := by
  induction t with
  | zero => simp [affA, affB, affE]
  | succ t ih =>
      have h' : paritiesAgree n r t := by
        intro j hj
        exact h j (by omega)
      rcases ih h' with ⟨hA, hB, hE⟩
      have hpar := h t (by omega)
      by_cases hp : (Nat.iterate collatz t r) % 2 = 0
      · have hpn : (Nat.iterate collatz t n) % 2 = 0 := by rwa [hpar]
        simp [affA, affB, affE, hp, hpn, hA, hB, hE]
      · have hp1 : (Nat.iterate collatz t r) % 2 = 1 := by omega
        have hp1n : (Nat.iterate collatz t n) % 2 = 1 := by rwa [hpar]
        simp [affA, affB, affE, hp1, hp1n, hA, hB, hE]

/-- If `n ≡ r (mod 2^K)` and the template never needs more than K bits, the
    two trajectories have the same first t parities. -/
theorem paritiesAgree_of_mod (n r K t : Nat) (_hK : 1 ≤ K)
    (hmod : n % 2 ^ K = r % 2 ^ K)
    (hdepth : ∀ j, j < t → affE r j + 1 ≤ K) :
    paritiesAgree n r t := by
  induction t with
  | zero => intro j hj; omega
  | succ t ih =>
      have hdepth_t : ∀ j, j < t → affE r j + 1 ≤ K := by
        intro j hj
        exact hdepth j (by omega)
      have iht := ih hdepth_t
      intro j hj
      by_cases hjt : j < t
      · exact iht j hjt
      · have hjeq : j = t := by omega
        subst j
        have hde := hdepth t (by omega)
        have heq := aff_eq_of_parities n r t iht
        rcases heq with ⟨hA, hB, hE⟩
        have hspecn := (aff_spec n t).1
        have hspecr := (aff_spec r t).1
        rw [← hA, ← hB, ← hE] at hspecr
        have hm : n % 2 ^ (affE r t + 1) = r % 2 ^ (affE r t + 1) := by
          have hdiv : 2 ^ (affE r t + 1) ∣ 2 ^ K := by
            refine ⟨2 ^ (K - (affE r t + 1)), ?_⟩
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [← Nat.mod_mod_of_dvd n hdiv, ← Nat.mod_mod_of_dvd r hdiv, hmod]
        rw [← hE] at hm
        have hcong : (affA n t * n + affB n t) % 2 ^ (affE n t + 1) =
            (affA n t * r + affB n t) % 2 ^ (affE n t + 1) := by
          let M := 2 ^ (affE n t + 1)
          change (affA n t * n + affB n t) % M = (affA n t * r + affB n t) % M
          change n % M = r % M at hm
          have hmul : (affA n t * n) % M = (affA n t * r) % M := by
            calc
              (affA n t * n) % M = ((affA n t % M) * (n % M)) % M := Nat.mul_mod _ _ _
              _ = ((affA n t % M) * (r % M)) % M := by rw [hm]
              _ = (affA n t * r) % M := (Nat.mul_mod _ _ _).symm
          calc
            (affA n t * n + affB n t) % M = ((affA n t * n) % M + affB n t % M) % M := Nat.add_mod _ _ _
            _ = ((affA n t * r) % M + affB n t % M) % M := by rw [hmul]
            _ = (affA n t * r + affB n t) % M := (Nat.add_mod _ _ _).symm
        have hx : (2 ^ affE n t * Nat.iterate collatz t n) % (2 ^ affE n t * 2) =
            (2 ^ affE n t * Nat.iterate collatz t r) % (2 ^ affE n t * 2) := by
          rw [hspecn, hspecr]
          rw [Nat.pow_succ] at hcong
          exact hcong
        have hx2 : 2 ^ affE n t * (Nat.iterate collatz t n % 2) =
            2 ^ affE n t * (Nat.iterate collatz t r % 2) := by
          simpa only [Nat.mul_mod_mul_left] using hx
        exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega : 0 < 2)) hx2

/-- A template certificate lifts to every member of its residue class. -/
theorem template_stop (n r K t a b e : Nat)
    (hmod : n % 2 ^ K = r % 2 ^ K)
    (hdata : affA r t = a ∧ affB r t = b ∧ affE r t = e)
    (hdepth : ∀ j, j < t → affE r j + 1 ≤ K)
    (hsmall : a < 2 ^ e)
    (hbound : b < (2 ^ e - a) * n) :
    Nat.iterate collatz t n < n := by
  have hK : 1 ≤ K := by
    by_cases ht : t = 0
    · subst t
      simp [affA, affB, affE] at hdata
      rcases hdata with ⟨rfl, rfl, rfl⟩
      simp at hsmall
    · have hd0 := hdepth 0 (by omega)
      simpa [affE] using hd0
  have hp := paritiesAgree_of_mod n r K t hK hmod hdepth
  have heq := aff_eq_of_parities n r t hp
  rcases heq with ⟨hA, hB, hE⟩
  have hspec := (aff_spec n t).1
  rw [hA, hB, hE] at hspec
  rw [hdata.1, hdata.2.1, hdata.2.2] at hspec
  have hsum : a * n + (2 ^ e - a) * n = 2 ^ e * n := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt hsmall)]
  have hlt : a * n + b < 2 ^ e * n := by
    rw [← hsum]
    exact Nat.add_lt_add_left hbound (a * n)
  rw [← hspec] at hlt
  exact (Nat.mul_lt_mul_left (Nat.pow_pos (by omega : 0 < 2))).mp hlt

/-- Greatest parity depth needed *before* any of the first t steps. -/
def maxDepth (r : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => max (maxDepth r t) (affE r t + 1)

/-- Every prefix depth is bounded by `maxDepth`. -/
theorem maxDepth_spec (r t j : Nat) (hj : j < t) :
    affE r j + 1 ≤ maxDepth r t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases hjt : j < t
      · exact Nat.le_trans (ih hjt) (Nat.le_max_left _ _)
      · have hjeq : j = t := by omega
        subst j
        exact Nat.le_max_right _ _

/-- The kernel-checkable certificate at `K = 8` (modulus 256): some template
    length `t ≤ 60` with all parity depths within 8 bits, final multiplier
    `a < 2^e`, and additive bound covering the least `n > 1` in the class. -/
def cert8 (r : Nat) : Bool :=
  (List.range 61).any (fun t =>
    decide (maxDepth r t ≤ 8 ∧
      affA r t < 2 ^ affE r t ∧
      affB r t < (2 ^ affE r t - affA r t) * (if r = 1 then 257 else r)))

/-- Every certified residue class modulo 256 has stopping time for all its
    members `n > 1`. -/
theorem cert8_stop (r n : Nat) (hr : r < 256) (hr_odd : r % 2 = 1)
    (hcert : cert8 r = true) (hmod : n % 256 = r % 256) (hn : 1 < n) :
    ∃ t, Nat.iterate collatz t n < n := by
  rw [cert8, List.any_eq_true] at hcert
  rcases hcert with ⟨t, _htmem, hcond⟩
  simp at hcond
  rcases hcond with ⟨hdepthmax, hsmall, hbnd⟩
  refine ⟨t, ?_⟩
  apply template_stop n r 8 t (affA r t) (affB r t) (affE r t) hmod
    ⟨rfl, rfl, rfl⟩
  · intro j hj
    exact Nat.le_trans (maxDepth_spec r t j hj) hdepthmax
  · exact hsmall
  · have hmin : (if r = 1 then 257 else r) ≤ n := by
      by_cases hr1 : r = 1
      · subst r
        change 257 ≤ n
        have hnmod : n % 256 = 1 := by simpa using hmod
        have hdecomp : 1 + 256 * (n / 256) = n := by
          have := Nat.mod_add_div n 256
          simpa [hnmod] using this
        have hkdiv : 1 ≤ n / 256 := by
          by_contra hz
          have hz0 : n / 256 = 0 := by omega
          rw [hz0] at hdecomp
          omega
        calc
          257 = 1 + 256 * 1 := by omega
          _ ≤ 1 + 256 * (n / 256) := Nat.add_le_add_left (Nat.mul_le_mul_left 256 hkdiv) 1
          _ = n := hdecomp
      · simp [hr1]
        by_contra hlt
        have hnlt : n < r := Nat.lt_of_not_ge hlt
        have hn256 : n < 256 := Nat.lt_trans hnlt hr
        have hmodn : n % 256 = n := Nat.mod_eq_of_lt hn256
        have hmodr : r % 256 = r := Nat.mod_eq_of_lt hr
        have hnr : n = r := by rw [hmodn, hmodr] at hmod; exact hmod
        rw [hnr] at hnlt
        omega
    exact Nat.lt_of_lt_of_le hbnd
      (Nat.mul_le_mul_left (2 ^ affE r t - affA r t) hmin)

/-- The explicit survivor set at `K = 8` (19 odd residues modulo 256). -/
def SURV8 : List Nat :=
  [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207,
   223, 231, 239, 251, 255]

/-- The kernel-checked residue partition at `K = 8`: exactly 109 of the 128
    odd residue classes are certified, so `δ(8) = 19/128`. -/
theorem k8_partition :
    ((List.range 256).filter (fun r => decide (r % 2 = 1 && cert8 r))).length = 109 ∧
      ((List.range 256).filter (fun r => decide (r % 2 = 1 && !cert8 r))).length = 19 ∧
      SURV8.length = 19 ∧
      (SURV8.all (fun r => decide (r < 256 && r % 2 = 1 && !cert8 r))) = true := by
  decide

/-- The certified count and density at `K = 8`. -/
theorem k8_density : 109 + 19 = 128 := by omega

-- Axiom audit for the new module.
#print axioms two_block_affine_plus
#print axioms two_block_affine
#print axioms two_block_composition
#print axioms two_block_refuel_congruence
#print axioms two_block_drift_threshold
#print axioms drop_one_mod_four
#print axioms drop_three_mod_sixteen
#print axioms template_stop
#print axioms cert8_stop
#print axioms k8_partition

end StoppingTimeDensity
end CollatzAdicBase
