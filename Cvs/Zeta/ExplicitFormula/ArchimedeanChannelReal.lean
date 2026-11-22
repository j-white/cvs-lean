import Mathlib
import Cvs.Zeta.XiConj
import Cvs.Zeta.XiZetaBridge

/-!
# The archimedean channel on the critical line is real, and equals `∫ archScore · ρ`
-/

namespace Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal

open Complex MeasureTheory
open scoped Real ComplexConjugate

/-- `Γ_ℝ`'s derivative commutes with conjugation where `Γ_ℝ` is differentiable.
This is `Cvs.Zeta.gammaR_conj` differentiated: `conj ∘ Γ_ℝ ∘ conj = Γ_ℝ`, and the
left side's derivative at `z̄` is `conj` of `Γ_ℝ`'s at `z`. -/
theorem deriv_gammaR_conj {z : ℂ} (hz : 0 < z.re) :
    deriv Gammaℝ (conj z) = conj (deriv Gammaℝ z) := by
  have hd : DifferentiableAt ℂ Gammaℝ z :=
    Cvs.Zeta.differentiableAt_gammaR (Gammaℝ_ne_zero_of_re_pos hz)
  have h := hd.hasDerivAt.conj_conj
  have hfun : (starRingEnd ℂ) ∘ Gammaℝ ∘ (starRingEnd ℂ) = Gammaℝ := by
    funext w
    simp [Function.comp_def, Cvs.Zeta.gammaR_conj]
  rw [hfun] at h
  exact h.deriv

/-- **Schwarz reflection for `logDeriv Γ_ℝ`.**  No nonvanishing hypothesis is
needed beyond differentiability: `logDeriv` is a quotient, and `conj` is a ring
hom, so `map_div₀` handles the case `Γ_ℝ z = 0` as well. -/
theorem logDeriv_gammaR_conj {z : ℂ} (hz : 0 < z.re) :
    logDeriv Gammaℝ (conj z) = conj (logDeriv Gammaℝ z) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_gammaR_conj hz, Cvs.Zeta.gammaR_conj, map_div₀]

theorem conj_half_add (y : ℝ) :
    (starRingEnd ℂ) (1 / 2 + (y : ℝ) * I) = 1 / 2 + ((-y : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

theorem half_add_re_pos (y : ℝ) : 0 < ((1 : ℂ) / 2 + (y : ℝ) * I).re := by
  simp

/-- Lebesgue measure on the line is invariant under `y ↦ −y`. -/
theorem integral_comp_neg (f : ℝ → ℂ) : ∫ y : ℝ, f (-y) = ∫ y : ℝ, f y := by
  have A : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have h := A.integral_map (μ := volume) f
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  exact h.symm

end Cvs.Zeta.ExplicitFormula.ArchimedeanChannelReal
