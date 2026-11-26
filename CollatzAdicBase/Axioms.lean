import CollatzAdicBase.FuelLaw
import CollatzAdicBase.RationalDescent
import CollatzAdicBase.Refueling
import CollatzAdicBase.AlternatingGlide
import CollatzAdicBase.LatentSaturation
import CollatzAdicBase.CycleExclusion
import CollatzAdicBase.StoppingTimeDensity
import CollatzAdicBase.GlideMarkovChain
import CollatzAdicBase.SyracuseLogDrift
import CollatzAdicBase.SyracuseRenewal
import CollatzAdicBase.ExcursionTail
import CollatzAdicBase.LogDensityContraction

-- Axiom audit: every theorem below should depend only on Lean's core axioms
-- (propext, Classical.choice, Quot.sound), with no sorryAx and no
-- project-specific axioms.  All twelve verified modules and all 91 audited
-- declarations are covered here (90 printouts with core axioms, one axiom-free).

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

-- Cycle exclusion module (Paper 6)
#print axioms CollatzAdicBase.CycleExclusion.step_three_free
#print axioms CollatzAdicBase.CycleExclusion.denom_const_of_three_free
#print axioms CollatzAdicBase.CycleExclusion.cycleAcc_spec
#print axioms CollatzAdicBase.CycleExclusion.cycle_sum_identity
#print axioms CollatzAdicBase.CycleExclusion.cycle_dvd
#print axioms CollatzAdicBase.CycleExclusion.one_odd_step_le_denominator
#print axioms CollatzAdicBase.CycleExclusion.no_integer_cycles_M_le_six
#print axioms CollatzAdicBase.CycleExclusion.no_single_block_integer_cycles
#print axioms CollatzAdicBase.CycleExclusion.cycT_patterns_odd_M_le_six
#print axioms CollatzAdicBase.CycleExclusion.cycT_three_free

#print axioms CollatzAdicBase.StoppingTimeDensity.two_block_affine_plus
#print axioms CollatzAdicBase.StoppingTimeDensity.two_block_affine
#print axioms CollatzAdicBase.StoppingTimeDensity.two_block_composition
#print axioms CollatzAdicBase.StoppingTimeDensity.two_block_refuel_congruence
#print axioms CollatzAdicBase.StoppingTimeDensity.two_block_drift_threshold
#print axioms CollatzAdicBase.StoppingTimeDensity.drop_one_mod_four
#print axioms CollatzAdicBase.StoppingTimeDensity.drop_three_mod_sixteen
#print axioms CollatzAdicBase.StoppingTimeDensity.template_stop
#print axioms CollatzAdicBase.StoppingTimeDensity.cert8_stop
#print axioms CollatzAdicBase.StoppingTimeDensity.k8_partition

-- Glide Markov chain module (Paper 8)
#print axioms CollatzAdicBase.GlideMarkovChain.glide_identity
#print axioms CollatzAdicBase.GlideMarkovChain.glideC_bound
#print axioms CollatzAdicBase.GlideMarkovChain.glide_drop
#print axioms CollatzAdicBase.GlideMarkovChain.parityMap_injective_mod
#print axioms CollatzAdicBase.GlideMarkovChain.glideVal_child
#print axioms CollatzAdicBase.GlideMarkovChain.heavyCount_tilt
#print axioms CollatzAdicBase.GlideMarkovChain.heavyCount_exp
#print axioms CollatzAdicBase.GlideMarkovChain.survF_card_le_heavy
#print axioms CollatzAdicBase.GlideMarkovChain.odd_survivor_decay
#print axioms CollatzAdicBase.GlideMarkovChain.true_survivor_decay

-- Syracuse log-drift module (Paper 9)
#print axioms CollatzAdicBase.SyracuseLogDrift.syracuseStep_mul_pow_v2
#print axioms CollatzAdicBase.SyracuseLogDrift.syracuseStep_odd
#print axioms CollatzAdicBase.SyracuseLogDrift.syracuse_identity
#print axioms CollatzAdicBase.SyracuseLogDrift.valWitness
#print axioms CollatzAdicBase.SyracuseLogDrift.unique_val_residue
#print axioms CollatzAdicBase.SyracuseLogDrift.exactValF_card
#print axioms CollatzAdicBase.SyracuseLogDrift.cycle_min_upper_bound

-- Syracuse renewal module (Paper 10, v1.4.0)
#print axioms CollatzAdicBase.SyracuseRenewal.glideVal_eq_div_pow_of_v2
#print axioms CollatzAdicBase.SyracuseRenewal.glideW_v2_eq_one
#print axioms CollatzAdicBase.SyracuseRenewal.glide_at_acc_times
#print axioms CollatzAdicBase.SyracuseRenewal.glideW_sum_succ
#print axioms CollatzAdicBase.SyracuseRenewal.syracuseFail_subset_survivor
#print axioms CollatzAdicBase.SyracuseRenewal.syracuseFail_decay
#print axioms CollatzAdicBase.SyracuseRenewal.syracuseFail_rational_decay
#print axioms CollatzAdicBase.SyracuseRenewal.compCount_eq_choose
#print axioms CollatzAdicBase.SyracuseRenewal.mgfPartial_closed
#print axioms CollatzAdicBase.SyracuseRenewal.mgf_lambda_closed

-- Excursion tail module (Paper 11, Layer 6)
#print axioms CollatzAdicBase.ExcursionTail.syracuseOrbit_ratio_le
#print axioms CollatzAdicBase.ExcursionTail.excursionFailF_orbit_ge
#print axioms CollatzAdicBase.ExcursionTail.oneStep_inj
#print axioms CollatzAdicBase.ExcursionTail.valList_eq_of_modEq
#print axioms CollatzAdicBase.ExcursionTail.excursionFailF_tail_uniform

-- Log-density contraction module (Paper 12, Layer 7)
#print axioms CollatzAdicBase.LogDensityContraction.valList_eq_of_ValSeq
#print axioms CollatzAdicBase.LogDensityContraction.mem_syracuseFailF_iff_valList
#print axioms CollatzAdicBase.LogDensityContraction.not_mem_syracuseFailF_contracts
#print axioms CollatzAdicBase.LogDensityContraction.not_mem_excursionFailF_no_excursion
#print axioms CollatzAdicBase.LogDensityContraction.oddFin_card_ge
#print axioms CollatzAdicBase.LogDensityContraction.bounded_and_contracts_of_vals
#print axioms CollatzAdicBase.LogDensityContraction.goodTrajectory_card_lower
#print axioms CollatzAdicBase.LogDensityContraction.goodTrajectory_vals_of_residue
#print axioms CollatzAdicBase.LogDensityContraction.goodTrajectory_bounded_and_contracts
#print axioms CollatzAdicBase.LogDensityContraction.goodTrajectory_contracts_to_alpha
