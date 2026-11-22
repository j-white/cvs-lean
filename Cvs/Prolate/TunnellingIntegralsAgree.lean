import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.TunnellingExponentSharpPlunge
import Cvs.Prolate.TunnellingIntegralMargin
import Cvs.Route.Visibility.WindowChainCellFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The angular and the algebraic tunnelling integrals agree

The substitution `r = √2·sin(π/4 − φ/2)`, for which `1 − r² = sin φ` and `2 − r² = 2cos²(π/4 − φ/2)`, carries
`TunnellingIntegralMargin`'s angular integral `∫_α^{π/2} √(sin²φ − T) dφ` onto `ForbiddenZoneGrowth`'s `Z_T(sin α) = forbZ 1 T (sin α)` for every
`α ∈ [0, π/2]` and every `T`. Hence `TunnellingIntegralMargin`'s `W`, `Δ` equal `TunnellingExponentSharpPlunge`'s `W`, `Δ` for every `T`, `TunnellingFloorSumPlunge`'s level ratio is
`ProlateCellGramHalfUnit`'s at the rung `finOfSF j`, and `W(T) ≤ 1` for `T ≥ 0`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace Cvs.Prolate.TunnellingIntegralsAgree
open Cvs.ZeroCounting

/-- The substitution `r(φ) = √2·sin(π/4 − φ/2)`. -/
def subR (φ : ℝ) : ℝ := √2 * sin (π / 4 - φ / 2)

/-- `1 − r(φ)² = sin φ`. -/
theorem one_sub_subR_sq (φ : ℝ) : 1 - subR φ ^ 2 = sin φ := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hc : cos (2 * (π / 4 - φ / 2)) = sin φ := by
    rw [show 2 * (π / 4 - φ / 2) = π / 2 - φ by ring, cos_pi_div_two_sub]
  rw [cos_two_mul, cos_sq'] at hc
  unfold subR
  rw [mul_pow, h2]
  linarith

/-- `2 − r(φ)² = 2cos²(π/4 − φ/2)`. -/
theorem two_sub_subR_sq (φ : ℝ) : 2 - subR φ ^ 2 = 2 * cos (π / 4 - φ / 2) ^ 2 := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  unfold subR
  rw [mul_pow, h2]
  nlinarith [sin_sq_add_cos_sq (π / 4 - φ / 2)]

/-- **The substitution**: `∫_α^{π/2} √(sin²φ − T) dφ = Z_T(sin α)` for `0 ≤ α ≤ π/2`. -/
theorem integral_tunF_eq_forbZ (T : ℝ) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ π / 2) :
    ∫ φ in α..π / 2, Cvs.Prolate.TunnellingIntegralMargin.tunF T φ = Cvs.Prolate.ForbiddenZoneGrowth.forbZ 1 T (sin α) := by
  set g : ℝ → ℝ := fun r => 2 * √(Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T (1 - r ^ 2)) / √(2 - r ^ 2) with hg
  set f' : ℝ → ℝ := fun φ => -(√2 / 2 * cos (π / 4 - φ / 2)) with hf'
  have hderiv : ∀ φ ∈ uIcc α (π / 2), HasDerivAt subR (f' φ) φ := by
    intro φ _
    have h := ((hasDerivAt_id φ).div_const 2).const_sub (π / 4)
    have h' := (h.sin).const_mul √2
    refine (show HasDerivAt subR _ φ from h').congr_deriv ?_
    simp only [hf', id]
    ring
  have hcont' : ContinuousOn f' (uIcc α (π / 2)) := by
    rw [hf']; fun_prop
  have hθ : ∀ φ ∈ uIcc α (π / 2), 0 < cos (π / 4 - φ / 2) := by
    intro φ hφ
    rw [uIcc_of_le h1] at hφ
    exact cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hφ.2], by linarith [pi_pos, hφ.1]⟩
  have hgc : ContinuousOn g (subR '' uIcc α (π / 2)) := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ContinuousAt.continuousWithinAt ?_
    have hpos : 0 < √(2 - subR φ ^ 2) := by
      rw [two_sub_subR_sq]; exact sqrt_pos.mpr (by nlinarith [hθ φ hφ])
    simp only [hg]
    exact ((continuous_const.mul (by unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP; fun_prop)).continuousAt).div
      (by fun_prop) hpos.ne'
  have hsub := integral_comp_mul_deriv' hderiv hcont' hgc
  have hpt : ∀ φ ∈ uIcc α (π / 2), (g ∘ subR) φ * f' φ = -Cvs.Prolate.TunnellingIntegralMargin.tunF T φ := by
    intro φ hφ
    have hc := hθ φ hφ
    simp only [Function.comp, hg, hf', Cvs.Prolate.TunnellingIntegralMargin.tunF]
    rw [two_sub_subR_sq, one_sub_subR_sq, sqrt_mul (by norm_num), sqrt_sq hc.le]
    have hq : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP 1 T (sin φ) = sin φ ^ 2 - T := by unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP; ring
    rw [hq]
    have hs2 : 0 < √2 := by positivity
    generalize cos (π / 4 - φ / 2) = C at hc ⊢
    field_simp
  rw [integral_congr hpt, intervalIntegral.integral_neg] at hsub
  have hend : subR (π / 2) = 0 := by
    unfold subR; rw [show π / 4 - π / 2 / 2 = 0 by ring, sin_zero, mul_zero]
  have hstart : subR α = √(1 - sin α) := by
    rw [← one_sub_subR_sq α, sub_sub_cancel, sqrt_sq]
    unfold subR
    exact mul_nonneg (sqrt_nonneg _) (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos]))
  rw [hend, hstart, intervalIntegral.integral_symm 0 (√(1 - sin α))] at hsub
  unfold Cvs.Prolate.ForbiddenZoneGrowth.forbZ
  linarith

/-- **`W` bridged**: `TunnellingIntegralMargin`'s angular `W(T)` is `TunnellingExponentSharpPlunge`'s `Z_T(√T)`, for every `T`. -/
theorem tunW_eq (T : ℝ) : Cvs.Prolate.TunnellingIntegralMargin.tunW T = Cvs.Prolate.TunnellingExponentSharpPlunge.tunW T := by
  unfold Cvs.Prolate.TunnellingIntegralMargin.tunW Cvs.Prolate.TunnellingExponentSharpPlunge.tunW
  by_cases hT : T ≤ 1
  · have hs : √T ≤ 1 := by rw [← sqrt_one]; exact sqrt_le_sqrt hT
    rw [integral_tunF_eq_forbZ T (arcsin_nonneg.2 (sqrt_nonneg _)) (arcsin_le_pi_div_two _),
      sin_arcsin (by linarith [sqrt_nonneg T]) hs]
  · have hs : 1 ≤ √T := by rw [← sqrt_one]; exact sqrt_le_sqrt (by linarith)
    rw [arcsin_of_one_le hs, integral_same]
    unfold Cvs.Prolate.ForbiddenZoneGrowth.forbZ
    rw [sqrt_eq_zero'.2 (by linarith), integral_same]

/-- `TunnellingExponentSharpPlunge`'s gap `W − 2Δ` is the angular integral over `[π/3, π/2]`. -/
theorem tunGap_eq (T : ℝ) : Cvs.Prolate.TunnellingExponentSharpPlunge.tunGap T = ∫ φ in π / 3..π / 2, Cvs.Prolate.TunnellingIntegralMargin.tunF T φ := by
  rw [integral_tunF_eq_forbZ T (by positivity) (by linarith [pi_pos]), sin_pi_div_three]
  rfl

/-- **`Δ` bridged**: `TunnellingIntegralMargin`'s angular `Δ(T)` is `TunnellingExponentSharpPlunge`'s `Δ(T)`, for every `T`. -/
theorem tunD_eq (T : ℝ) : Cvs.Prolate.TunnellingIntegralMargin.tunD T = Cvs.Prolate.TunnellingExponentSharpPlunge.tunDelta T := by
  have h1 := Cvs.Prolate.TunnellingIntegralMargin.tunW_sub_two_tunD T
  have h2 := Cvs.Prolate.TunnellingExponentSharpPlunge.tunW_eq T
  rw [tunW_eq, ← tunGap_eq] at h1
  linarith

/-- `TunnellingFloorSumPlunge`'s rung level ratio is `ProlateCellGramHalfUnit`'s at the rung `finOfSF j`. -/
theorem tLev_eq {x : ℕ} (j : Cvs.Approximant.SpineSubspace.SF x) : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j = Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j) := rfl

/-- `W(T) ≤ 1` for `T ≥ 0`. -/
theorem tunW_le_one {T : ℝ} (hT : 0 ≤ T) : Cvs.Prolate.TunnellingIntegralMargin.tunW T ≤ 1 := by
  unfold Cvs.Prolate.TunnellingIntegralMargin.tunW
  have ha0 : 0 ≤ arcsin √T := arcsin_nonneg.2 (sqrt_nonneg _)
  have ha1 := arcsin_le_pi_div_two √T
  calc ∫ φ in arcsin √T..π / 2, Cvs.Prolate.TunnellingIntegralMargin.tunF T φ ≤ ∫ φ in arcsin √T..π / 2, sin φ := by
        refine integral_mono_on ha1 (Cvs.Prolate.TunnellingIntegralMargin.intervalIntegrable_tunF _ _ _)
          (continuous_sin.intervalIntegrable _ _) fun φ hφ => ?_
        have hs : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi (by linarith [hφ.1])
          (by linarith [hφ.2, pi_pos])
        unfold Cvs.Prolate.TunnellingIntegralMargin.tunF
        calc √(sin φ ^ 2 - T) ≤ √(sin φ ^ 2) := sqrt_le_sqrt (by linarith)
          _ = sin φ := sqrt_sq hs
    _ = cos (arcsin √T) := by rw [integral_sin, cos_pi_div_two, sub_zero]
    _ ≤ 1 := cos_le_one _

/-- `Δ(¾) = 0`. -/
theorem tunDelta_three_quarters : Cvs.Prolate.TunnellingExponentSharpPlunge.tunDelta (3 / 4) = 0 := by
  have h : √(3 / 4 : ℝ) = √3 / 2 := by
    rw [show (3 / 4 : ℝ) = 3 / 2 ^ 2 by norm_num, sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
      sqrt_sq (by norm_num)]
  unfold Cvs.Prolate.TunnellingExponentSharpPlunge.tunDelta
  rw [h, sub_self, zero_div]

end Cvs.Prolate.TunnellingIntegralsAgree

end
