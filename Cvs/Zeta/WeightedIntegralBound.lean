import Mathlib

/-!
# The weighted integral, bounded

A bound on `∫₁^∞ t^{−1/2}e^{−πt} dt`, by splitting at `t = 2` and taking `t^{−1/2}` at
each piece's left endpoint, and the zero-free height it gives.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex MeasureTheory

namespace Cvs.Zeta.WeightedIntegralBound

/-- `∫_{Ioi c} e^{−πt} dt = e^{−πc}/π`, at any base point. -/
theorem integral_exp_neg_pi_Ioi (c : ℝ) :
    (∫ t in Set.Ioi c, Real.exp (-(Real.pi * t))) = Real.exp (-(Real.pi * c)) / Real.pi := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h := MeasureTheory.integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) c hpi
  simp only [smul_eq_mul] at h
  rw [h, integral_exp_neg_Ioi]
  ring

theorem exp_neg_pi_integrableOn (c : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(Real.pi * t))) (Set.Ioi c) := by
  have h := exp_neg_integrableOn_Ioi c (b := Real.pi) Real.pi_pos
  simpa only [neg_mul] using h

/-- The weighted integrand is integrable: it is under `e^{−πt}`. -/
theorem weighted_integrableOn :
    IntegrableOn (fun t : ℝ => t ^ (-(1/2) : ℝ) * Real.exp (-(Real.pi * t)))
      (Set.Ioi (1:ℝ)) := by
  refine Integrable.mono (exp_neg_pi_integrableOn 1) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro t ht
      exact Or.inl (ne_of_gt (lt_trans zero_lt_one ht))
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) ≤ t := le_of_lt ht
    have htpos : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hpow : (t : ℝ) ^ (-(1/2) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    have hpos : (0:ℝ) ≤ (t : ℝ) ^ (-(1/2) : ℝ) := Real.rpow_nonneg htpos.le _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (Real.exp_pos _).le]
    nlinarith [Real.exp_pos (-(Real.pi * t))]

/-- `Ioi 1` splits at `2`. -/
theorem Ioi_one_split : Set.Ioi (1:ℝ) = Set.Ioc 1 2 ∪ Set.Ioi 2 := by
  ext x
  simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
  constructor
  · intro h
    by_cases h2 : 2 < x
    · exact Or.inr h2
    · exact Or.inl ⟨h, not_lt.mp h2⟩
  · rintro (⟨h, _⟩ | h)
    · exact h
    · linarith

theorem Ioc_Ioi_disjoint : Disjoint (Set.Ioc (1:ℝ) 2) (Set.Ioi 2) := by
  rw [Set.disjoint_left]
  rintro x ⟨_, hx2⟩ hx
  exact absurd hx (not_lt.mpr hx2)

end Cvs.Zeta.WeightedIntegralBound
