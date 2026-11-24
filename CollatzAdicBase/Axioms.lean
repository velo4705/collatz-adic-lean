import CollatzAdicBase.FuelLaw
import CollatzAdicBase.RationalDescent
import CollatzAdicBase.Refueling
import CollatzAdicBase.AlternatingGlide
import CollatzAdicBase.LatentSaturation

-- Axiom audit: every theorem below should depend only on Lean's core axioms
-- (propext, Classical.choice, Quot.sound), with no sorryAx and no
-- project-specific axioms.  All five verified modules are audited here.

#print axioms CollatzAdicBase.FuelLaw.iterate_shortcut_formula
#print axioms CollatzAdicBase.FuelLaw.iterate_shortcut_odd
#print axioms CollatzAdicBase.FuelLaw.iterate_shortcut_strict_mono
#print axioms CollatzAdicBase.FuelLaw.collatz_iterate_gt_initial
#print axioms CollatzAdicBase.FuelLaw.collatz_iterate_two_mul
#print axioms CollatzAdicBase.FuelLaw.glide_at_least_two_mul

#print axioms CollatzAdicBase.lemma_2_1_stability
#print axioms CollatzAdicBase.lemma_2_2_one_three_per_odd_step
#print axioms CollatzAdicBase.lemma_2_3_forced_halving
#print axioms CollatzAdicBase.lemma_2_4_and_cor_2_5_three_free_cycles
#print axioms CollatzAdicBase.theorem_1_pure_three_power_descent
#print axioms CollatzAdicBase.verification_pure_three_power_k_le_six
#print axioms CollatzAdicBase.verification_all_reduced_small_k

#print axioms CollatzAdicBase.Refueling.two_pow_dvd_iff_le_v2
#print axioms CollatzAdicBase.Refueling.refuel_landing
#print axioms CollatzAdicBase.Refueling.refuel_exhausts_fuel
#print axioms CollatzAdicBase.Refueling.refuel_congruence
#print axioms CollatzAdicBase.Refueling.refuel_mod_invariant

#print axioms CollatzAdicBase.AlternatingGlide.three_dvd_alt
#print axioms CollatzAdicBase.AlternatingGlide.n_alt_glide_eq
#print axioms CollatzAdicBase.AlternatingGlide.alternating_bit_glide
#print axioms CollatzAdicBase.AlternatingGlide.lemma_three_k_zero

#print axioms CollatzAdicBase.LatentSaturation.gcd_lift
#print axioms CollatzAdicBase.LatentSaturation.ratStep_lift
#print axioms CollatzAdicBase.LatentSaturation.lift_congruence
#print axioms CollatzAdicBase.LatentSaturation.cycle_dvd_pow_sub
#print axioms CollatzAdicBase.LatentSaturation.den_at_lifted_level
#print axioms CollatzAdicBase.LatentSaturation.three_free_preserved
#print axioms CollatzAdicBase.LatentSaturation.ratStep_valid
