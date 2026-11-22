import Mathlib
import Cvs.Zeta.CriticalParam
import Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly
import Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive
import Cvs.Zeta.ExplicitFormula.PoleTermSplit

/-!
# The residue, assembled

Every piece is in place.
-/

namespace Cvs.Zeta.ExplicitFormula.ResidueAssembled
open Cvs.Detection

open Complex MeasureTheory Filter
open scoped Real Topology

/-- The rectangle identity for an entire integrand — no side condition. -/
theorem rect_identity {E : ℂ → ℂ} (hE : Differentiable ℂ E) (R : ℝ) :
    ((∫ x : ℝ in (1 / 2 : ℝ)..2, E (x + (-R : ℝ) * I))
        - ∫ x : ℝ in (1 / 2 : ℝ)..2, E (x + (R : ℝ) * I))
      + I • (∫ y : ℝ in (-R : ℝ)..R, E (2 + y * I))
      - I • (∫ y : ℝ in (-R : ℝ)..R, E (1 / 2 + y * I)) = 0 := by
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    E ((1 / 2 : ℝ) - R * I) (2 + R * I) (by simpa using hE.differentiableOn)
  simpa using key

/-- The split, pointwise on a vertical `Re z = c` with `c ≠ 1`. -/
theorem poleTwo_split (h : ℂ → ℂ) {c : ℝ} (hc : c ≠ 1) (y : ℝ) :
    Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (((c : ℝ) : ℂ) + (y : ℝ) * I)
      = Cvs.Detection.poleTwoEntire h (((c : ℝ) : ℂ) + (y : ℝ) * I)
        + Cvs.Zeta.ofCritical h 1 * ((((c - 1 : ℝ) : ℂ) + (y : ℝ) * I)⁻¹) := by
  have hzne : ((c : ℝ) : ℂ) + (y : ℝ) * I ≠ 1 := by
    intro hz
    have hre : ((((c : ℝ) : ℂ) + (y : ℝ) * I)).re = c := by simp
    rw [hz] at hre
    simp at hre
    exact hc hre.symm
  have hsub : ((c : ℝ) : ℂ) + (y : ℝ) * I - 1 = (((c - 1 : ℝ) : ℂ) + (y : ℝ) * I) := by
    push_cast; ring
  rw [Cvs.Detection.poleTwo_decomp h hzne, hsub, div_eq_mul_inv]
  rfl

theorem continuous_poleLine {c : ℝ} (hc : c ≠ 1) :
    Continuous (fun y : ℝ => (((c - 1 : ℝ) : ℂ) + (y : ℝ) * I)⁻¹) := by
  refine Continuous.inv₀ (by fun_prop) fun y hz => ?_
  have hre : ((((c - 1 : ℝ) : ℂ) + (y : ℝ) * I)).re = c - 1 := by simp
  rw [hz] at hre
  simp at hre
  exact hc (by linarith)

/-- The split, integrated over `[−R, R]`. -/
theorem integral_split {h : ℂ → ℂ} (hd : Differentiable ℂ h) {c : ℝ} (hc : c ≠ 1) (R : ℝ) :
    (∫ y in (-R)..R, Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (((c : ℝ) : ℂ) + (y : ℝ) * I))
      = (∫ y in (-R)..R, Cvs.Detection.poleTwoEntire h (((c : ℝ) : ℂ) + (y : ℝ) * I))
        + Cvs.Zeta.ofCritical h 1
          * ∫ y in (-R)..R, ((((c - 1 : ℝ) : ℂ) + (y : ℝ) * I)⁻¹) := by
  have hcE : Continuous (fun y : ℝ => Cvs.Detection.poleTwoEntire h (((c : ℝ) : ℂ) + (y : ℝ) * I)) :=
    (Cvs.Detection.differentiable_poleTwoEntire hd).continuous.comp (by fun_prop)
  have hcP := continuous_poleLine hc
  have h1 : IntervalIntegrable
      (fun y : ℝ => Cvs.Detection.poleTwoEntire h (((c : ℝ) : ℂ) + (y : ℝ) * I)) volume (-R) R :=
    hcE.intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun y : ℝ => Cvs.Zeta.ofCritical h 1 * ((((c - 1 : ℝ) : ℂ) + (y : ℝ) * I)⁻¹))
      volume (-R) R := (hcP.const_smul (Cvs.Zeta.ofCritical h 1)).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr
      (g := fun y : ℝ => Cvs.Detection.poleTwoEntire h (((c : ℝ) : ℂ) + (y : ℝ) * I)
        + Cvs.Zeta.ofCritical h 1 * ((((c - 1 : ℝ) : ℂ) + (y : ℝ) * I)⁻¹))
      (fun y _ => poleTwo_split h hc y),
    intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]

/-- Integrability of `poleTwo` on a vertical whose distance to `z = 1` is at
least `½`. -/
theorem integrable_poleTwo_line {h : ℂ → ℂ} (hd : Differentiable ℂ h) {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖Cvs.Zeta.ofCritical h z‖ ≤ A / (1 + |z.im|) ^ 3)
    {c : ℝ} (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 2) (hfar : 1 / 2 ≤ |c - 1|) :
    Integrable (fun y : ℝ => Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (((c : ℝ) : ℂ) + (y : ℝ) * I)) := by
  have hcont : Continuous (fun y : ℝ => Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo h (((c : ℝ) : ℂ) + (y : ℝ) * I)) := by
    simp only [Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo]
    have hlin : Continuous (fun y : ℝ => ((c : ℝ) : ℂ) + (y : ℝ) * I - 1) := by fun_prop
    refine Continuous.mul (Continuous.div₀ (f := fun _ : ℝ => (1 : ℂ))
      (g := fun y : ℝ => ((c : ℝ) : ℂ) + (y : ℝ) * I - 1) continuous_const hlin fun y hz => ?_) ?_
    · have hre : ((((c : ℝ) : ℂ) + (y : ℝ) * I - 1)).re = c - 1 := by simp
      rw [hz] at hre
      simp at hre
      rw [← hre] at hfar
      norm_num at hfar
    · exact (Cvs.Zeta.differentiable_ofCritical hd).continuous.comp (by fun_prop)
  refine (integrable_inv_one_add_sq.const_mul (2 * A)).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have hre : ((((c : ℝ) : ℂ) + (y : ℝ) * I)).re = c := by simp
  have him : ((((c : ℝ) : ℂ) + (y : ℝ) * I)).im = y := by simp
  have hg := hdec (((c : ℝ) : ℂ) + (y : ℝ) * I) (by rw [hre]; linarith) (by rw [hre]; exact hc2)
  rw [him] at hg
  have hden : |c - 1| ≤ ‖((c : ℝ) : ℂ) + (y : ℝ) * I - 1‖ := by
    have h := Complex.abs_re_le_norm (((c : ℝ) : ℂ) + (y : ℝ) * I - 1)
    simpa using h
  have hdpos : (0 : ℝ) < ‖((c : ℝ) : ℂ) + (y : ℝ) * I - 1‖ := by linarith
  have hinv : ‖(1 : ℂ) / (((c : ℝ) : ℂ) + (y : ℝ) * I - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ hdpos]
    linarith
  rw [Cvs.Zeta.ExplicitFormula.AdmissibleTestAssembly.poleTwo, norm_mul, ← div_eq_mul_inv]
  have hstep : ‖(1 : ℂ) / (((c : ℝ) : ℂ) + (y : ℝ) * I - 1)‖
      * ‖Cvs.Zeta.ofCritical h (((c : ℝ) : ℂ) + (y : ℝ) * I)‖ ≤ 2 * (A / (1 + |y|) ^ 3) :=
    mul_le_mul hinv hg (norm_nonneg _) (by norm_num)
  refine hstep.trans ?_
  rw [show (2 : ℝ) * (A / (1 + |y|) ^ 3) = 2 * A / (1 + |y|) ^ 3 from by ring]
  gcongr
  exact Cvs.Zeta.ExplicitFormula.FirstPoleTermPositive.cube_ge y

end Cvs.Zeta.ExplicitFormula.ResidueAssembled
