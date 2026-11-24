import CollatzAdicBase.FuelLaw
import CollatzAdicBase.AlternatingGlide
import CollatzAdicBase.LatentSaturation

-- Axiom audit: every theorem below should depend only on Lean's core axioms
-- (propext, Classical.choice, Quot.sound), with no sorryAx and no
-- project-specific axioms.

#print axioms CollatzAdicBase.FuelLaw.iterate_shortcut_formula
#print axioms CollatzAdicBase.FuelLaw.iterate_shortcut_odd
#print axioms CollatzAdicBase.FuelLaw.iterate_shortcut_strict_mono
#print axioms CollatzAdicBase.FuelLaw.collatz_iterate_gt_initial
#print axioms CollatzAdicBase.FuelLaw.collatz_iterate_two_mul
#print axioms CollatzAdicBase.FuelLaw.glide_at_least_two_mul
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
