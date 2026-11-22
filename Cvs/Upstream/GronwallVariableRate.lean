import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Grönwall's inequality in integral form, with a variable rate

If `φ t ≤ C + ∫_{t₀}^t k φ` on `[t₀, t₁]` with `k ≥ 0`, `φ` and `k` continuous there, then
`φ t₁ ≤ C exp(∫_{t₀}^{t₁} k)`. The rate may be unbounded near an endpoint as long as it is continuous
on the closed interval where it is used.
-/

namespace Cvs.Upstream.GronwallVariableRate

open intervalIntegral Real Set

/-- **Integral Grönwall.** -/
theorem le_mul_exp_integral {φ k : ℝ → ℝ} {t₀ t₁ C : ℝ} (hle : t₀ ≤ t₁)
    (hφ : ContinuousOn φ (Icc t₀ t₁)) (hk : ContinuousOn k (Icc t₀ t₁))
    (hk0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ k t)
    (h : ∀ t ∈ Icc t₀ t₁, φ t ≤ C + ∫ s in t₀..t, k s * φ s) :
    φ t₁ ≤ C * exp (∫ s in t₀..t₁, k s) := by
  set Φ : ℝ → ℝ := fun t => ∫ s in t₀..t, k s * φ s with hΦ
  set K : ℝ → ℝ := fun t => ∫ s in t₀..t, k s with hK
  set Ψ : ℝ → ℝ := fun t => (C + Φ t) * exp (-K t) with hΨ
  have hI : uIcc t₀ t₁ = Icc t₀ t₁ := uIcc_of_le hle
  have hkφ : ContinuousOn (fun s => k s * φ s) (Icc t₀ t₁) := hk.mul hφ
  have hΦc : ContinuousOn Φ (Icc t₀ t₁) := by
    rw [← hI]; exact continuousOn_primitive_interval (by rw [hI]; exact hkφ.integrableOn_Icc)
  have hKc : ContinuousOn K (Icc t₀ t₁) := by
    rw [← hI]; exact continuousOn_primitive_interval (by rw [hI]; exact hk.integrableOn_Icc)
  have hΨc : ContinuousOn Ψ (Icc t₀ t₁) :=
    (continuousOn_const.add hΦc).mul (hKc.neg.rexp)
  -- derivatives in the interior
  have hderiv : ∀ t ∈ Ioo t₀ t₁, HasDerivAt Ψ
      ((k t * φ t) * exp (-K t) + (C + Φ t) * (exp (-K t) * -(k t))) t := by
    intro t ht
    have hsub : Icc t₀ t ⊆ Icc t₀ t₁ := Icc_subset_Icc_right ht.2.le
    have hnhds : Icc t₀ t₁ ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hΦd : HasDerivAt Φ (k t * φ t) t := by
      apply integral_hasDerivAt_right
      · exact (hkφ.mono hsub).intervalIntegrable_of_Icc ht.1.le
      · exact hkφ.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t |>.filter_mono
          (by rw [nhdsWithin_eq_nhds.mpr hnhds])
      · exact hkφ.continuousAt hnhds
    have hKd : HasDerivAt K (k t) t := by
      apply integral_hasDerivAt_right
      · exact (hk.mono hsub).intervalIntegrable_of_Icc ht.1.le
      · exact hk.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t |>.filter_mono
          (by rw [nhdsWithin_eq_nhds.mpr hnhds])
      · exact hk.continuousAt hnhds
    have := ((hasDerivAt_const t C).fun_add hΦd).fun_mul (hKd.neg.exp)
    simp only [Pi.neg_apply] at this
    refine this.congr_deriv ?_
    ring
  have hanti : AntitoneOn Ψ (Icc t₀ t₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁) hΨc
    · rw [interior_Icc]
      exact fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hderiv t ht).deriv]
      have hmem : t ∈ Icc t₀ t₁ := Ioo_subset_Icc_self ht
      have h1 := h t hmem
      have h2 := hk0 t hmem
      have he := (exp_pos (-K t)).le
      have : k t * (φ t - (C + Φ t)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 (by linarith)
      nlinarith [mul_nonpos_of_nonpos_of_nonneg this he]
  have hmem0 : t₀ ∈ Icc t₀ t₁ := left_mem_Icc.mpr hle
  have hmem1 : t₁ ∈ Icc t₀ t₁ := right_mem_Icc.mpr hle
  have hΨ1 := hanti hmem0 hmem1 hle
  have hΨ0 : Ψ t₀ = C := by simp [hΨ, hΦ, hK]
  rw [hΨ0] at hΨ1
  have hφ1 := h t₁ hmem1
  have hpos := exp_pos (K t₁)
  have key : C + Φ t₁ ≤ C * exp (K t₁) := by
    have : (C + Φ t₁) * exp (-K t₁) * exp (K t₁) ≤ C * exp (K t₁) :=
      mul_le_mul_of_nonneg_right hΨ1 hpos.le
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one] at this
  exact hφ1.trans key

end Cvs.Upstream.GronwallVariableRate
