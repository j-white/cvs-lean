import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly
import Cvs.Zeta.ExplicitFormula.EntireSummandHorizontals
import Cvs.Zeta.ExplicitFormula.PoleFactorVerticalIntegral
import Cvs.Zeta.ExplicitFormula.PoleTermSplit
import Cvs.Zeta.ExplicitFormula.ResidueAssembled

/-!
# The residue
-/

namespace Cvs.Detection

open Complex MeasureTheory Filter
open scoped Real Topology

theorem cast_two : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num

theorem cast_half : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring

/-- **The residue.** -/
theorem poleTwo_residue {h : ℂ → ℂ} (hd : Differentiable ℂ h) {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3) :
    (∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (2 + (y : ℝ) * I))
        - ∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)
      = ((2 * π : ℝ) : ℂ) * Cvs.Zeta.ofCritical h 1 := by
  have hbot : Tendsto (fun R : ℝ => -(R : ℝ)) atTop atBot := tendsto_neg_atTop_atBot
  have htop : Tendsto (fun R : ℝ => (R : ℝ)) atTop atTop := tendsto_id
  have hE := Cvs.Detection.differentiable_poleTwoEntire hd
  -- integrability on the two verticals
  have hi2 : Integrable (fun y : ℝ => Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (2 + (y : ℝ) * I)) := by
    have hh := Cvs.Zeta.ExplicitFormula.ResidueAssembled.integrable_poleTwo_line hd hA hdec (c := (2 : ℝ)) (by norm_num) le_rfl
      (by norm_num)
    simpa only [cast_two] using hh
  have hiH : Integrable (fun y : ℝ => Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)) := by
    have hh := Cvs.Zeta.ExplicitFormula.ResidueAssembled.integrable_poleTwo_line hd hA hdec (c := (1 / 2 : ℝ)) le_rfl (by norm_num)
      (by rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) from by ring, abs_neg]; norm_num)
    simpa only [cast_half] using hh
  have hR2 := MeasureTheory.intervalIntegral_tendsto_integral hi2 hbot htop
  have hRH := MeasureTheory.intervalIntegral_tendsto_integral hiH hbot htop
  -- the entire summand's verticals differ by its horizontals, which vanish
  have hid : ∀ R : ℝ,
      I • (∫ y in (-R : ℝ)..R, Cvs.Detection.poleTwoEntire h (2 + y * I))
        - I • (∫ y in (-R : ℝ)..R, Cvs.Detection.poleTwoEntire h (1 / 2 + y * I))
      = (∫ x : ℝ in (1 / 2 : ℝ)..2, Cvs.Detection.poleTwoEntire h (x + (R : ℝ) * I))
        - ∫ x : ℝ in (1 / 2 : ℝ)..2, Cvs.Detection.poleTwoEntire h (x + (-R : ℝ) * I) := by
    intro R
    have hh := Cvs.Zeta.ExplicitFormula.ResidueAssembled.rect_identity hE R
    linear_combination hh
  have hEsmul : Tendsto (fun R : ℝ =>
      I • (∫ y in (-R : ℝ)..R, Cvs.Detection.poleTwoEntire h (2 + y * I))
        - I • (∫ y in (-R : ℝ)..R, Cvs.Detection.poleTwoEntire h (1 / 2 + y * I)))
      atTop (𝓝 0) := by
    refine Tendsto.congr (fun R => (hid R).symm) ?_
    have hh := (Cvs.Zeta.ExplicitFormula.EntireSummandHorizontals.tendsto_horizontal hA hdec).sub (Cvs.Zeta.ExplicitFormula.EntireSummandHorizontals.tendsto_horizontal_neg hA hdec)
    rw [sub_zero] at hh
    exact hh
  have hEdiff : Tendsto (fun R : ℝ =>
      (∫ y in (-R : ℝ)..R, Cvs.Detection.poleTwoEntire h (2 + (y : ℝ) * I))
        - ∫ y in (-R : ℝ)..R, Cvs.Detection.poleTwoEntire h (1 / 2 + (y : ℝ) * I))
      atTop (𝓝 0) := by
    have hh := hEsmul.const_smul I⁻¹
    rw [smul_zero] at hh
    refine Tendsto.congr (fun R => ?_) hh
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul, one_smul]
  -- the pole summand: `PoleFactorVerticalIntegral` instantiated at the literal constants integral_split produces
  have hPpos := Cvs.Detection.tendsto_integral_inv_line_pos (a := (2 - 1 : ℝ)) (by norm_num)
  have hPneg := Cvs.Detection.tendsto_integral_inv_line_neg (a := (1 / 2 - 1 : ℝ)) (by norm_num)
  have hsplit : ∀ R : ℝ,
      (∫ y in (-R : ℝ)..R, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (2 + (y : ℝ) * I))
          - ∫ y in (-R : ℝ)..R, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)
        = ((∫ y in (-R : ℝ)..R, Cvs.Detection.poleTwoEntire h (2 + (y : ℝ) * I))
            - ∫ y in (-R : ℝ)..R, Cvs.Detection.poleTwoEntire h (1 / 2 + (y : ℝ) * I))
          + Cvs.Zeta.ofCritical h 1
            * ((∫ y in (-R : ℝ)..R, ((((2 - 1 : ℝ) : ℂ) + (y : ℝ) * I)⁻¹))
              - ∫ y in (-R : ℝ)..R, ((((1 / 2 - 1 : ℝ) : ℂ) + (y : ℝ) * I)⁻¹)) := by
    intro R
    have hA2 := Cvs.Zeta.ExplicitFormula.ResidueAssembled.integral_split hd (c := (2 : ℝ)) (by norm_num) R
    have hAH := Cvs.Zeta.ExplicitFormula.ResidueAssembled.integral_split hd (c := (1 / 2 : ℝ)) (by norm_num) R
    rw [cast_two] at hA2
    rw [cast_half] at hAH
    rw [hA2, hAH]
    ring
  have hlim1 : Tendsto (fun R : ℝ =>
      (∫ y in (-R : ℝ)..R, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (2 + (y : ℝ) * I))
        - ∫ y in (-R : ℝ)..R, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)) atTop
      (𝓝 ((∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (2 + (y : ℝ) * I))
        - ∫ y : ℝ, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I))) := hR2.sub hRH
  have hlim2 : Tendsto (fun R : ℝ =>
      (∫ y in (-R : ℝ)..R, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (2 + (y : ℝ) * I))
        - ∫ y in (-R : ℝ)..R, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (1 / 2 + (y : ℝ) * I)) atTop
      (𝓝 (0 + Cvs.Zeta.ofCritical h 1 * (((π : ℝ) : ℂ) - (-(π : ℝ) : ℂ)))) := by
    refine Tendsto.congr (fun R => (hsplit R).symm) ?_
    exact hEdiff.add ((hPpos.sub hPneg).const_mul _)
  rw [tendsto_nhds_unique hlim1 hlim2]
  push_cast
  ring

end Cvs.Detection
