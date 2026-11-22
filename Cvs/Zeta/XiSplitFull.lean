import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiVertical
import Cvs.Zeta.XiVerticalFull
import Cvs.Zeta.XiVerticalSplit
import Cvs.Zeta.ZetaLowerBound

/-!
# The four-way split, on the whole line

`Cvs.Zeta.XiVerticalSplit` splits `∫ ξ'/ξ·φ` over `{y | 2 ≤ |y|}`; `Cvs.Zeta.XiFoldedSum` needs
it over all of `ℝ`.
-/

open Complex MeasureTheory

namespace Cvs.Zeta

/-- A bounded continuous factor against a cubically decaying test function is integrable on
the whole line.  `(1+|y|)³ ≥ (1+|y|)² ≥ 1 + y²` does the domination, landing on
`integrable_inv_one_add_sq`. -/
theorem integrable_vline_of_bounded {f φ : ℂ → ℂ} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfc : Continuous fun y : ℝ => f ((2 : ℂ) + y * I))
    (hb : ∀ y : ℝ, ‖f ((2 : ℂ) + y * I)‖ ≤ C)
    (hφc : Continuous φ) (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    Integrable fun y : ℝ => f ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I) := by
  have hpath : Continuous fun y : ℝ => ((2 : ℂ) + y * I) := by fun_prop
  have hdom : Integrable (fun y : ℝ => (C * A) * (1 + y ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hdom (hfc.mul (hφc.comp hpath)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have h2 : ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3 := hφ y
  have habs : (0 : ℝ) ≤ |y| := abs_nonneg y
  have hsq : (1 : ℝ) + y ^ 2 ≤ (1 + |y|) ^ 3 := by
    have hy : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    nlinarith [habs]
  have hle : A / (1 + |y|) ^ 3 ≤ A / (1 + y ^ 2) :=
    div_le_div_of_nonneg_left hA (by positivity) hsq
  rw [norm_mul]
  calc ‖f ((2 : ℂ) + y * I)‖ * ‖φ ((2 : ℂ) + y * I)‖
      ≤ C * (A / (1 + y ^ 2)) :=
        mul_le_mul (hb y) (h2.trans hle) (norm_nonneg _) hC
    _ = C * A * (1 + y ^ 2)⁻¹ := by rw [div_eq_mul_inv]; ring

/-! ### The three elementary summands, on the whole line -/

variable {φ : ℂ → ℂ} {A : ℝ}

theorem integrable_one_div_vline_full (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    Integrable fun y : ℝ => 1 / ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I) := by
  have hc : Continuous fun y : ℝ => (1 : ℂ) / ((2 : ℂ) + y * I) :=
    continuous_const.div₀ (by fun_prop) vline_ne_zero'
  refine integrable_vline_of_bounded (f := fun s : ℂ => 1 / s) (C := 1 / 2) hA (by norm_num)
    hc (fun y => ?_) hφc hφ
  have hns : (2 : ℝ) ≤ ‖(2 : ℂ) + y * I‖ := by
    have := Complex.abs_re_le_norm ((2 : ℂ) + y * I)
    simp only [Complex.add_re] at this
    simpa using le_trans (le_abs_self 2) (by simpa using this)
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le (by norm_num) hns

theorem integrable_one_div_sub_one_vline_full (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    Integrable fun y : ℝ => 1 / (((2 : ℂ) + y * I) - 1) * φ ((2 : ℂ) + y * I) := by
  have hc : Continuous fun y : ℝ => (1 : ℂ) / (((2 : ℂ) + y * I) - 1) :=
    continuous_const.div₀ (by fun_prop) fun y => sub_ne_zero.mpr (vline_ne_one y)
  refine integrable_vline_of_bounded (f := fun s : ℂ => 1 / (s - 1)) (C := 1) hA (by norm_num)
    hc (fun y => ?_) hφc hφ
  have hns : (1 : ℝ) ≤ ‖((2 : ℂ) + y * I) - 1‖ := by
    have := Complex.abs_re_le_norm (((2 : ℂ) + y * I) - 1)
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re] at this
    norm_num at this
    exact this
  rw [norm_div, norm_one, div_le_one (by linarith)]
  linarith

theorem integrable_logDeriv_riemannZeta_vline_full (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    Integrable fun y : ℝ =>
      logDeriv riemannZeta ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I) :=
  integrable_vline_of_bounded (f := logDeriv riemannZeta) (C := vonMangoldtSumTwo) hA
    vonMangoldtSumTwo_nonneg continuous_logDeriv_riemannZeta_vline
    (fun y => norm_logDeriv_riemannZeta_le_of_two_le_re (by simp)) hφc hφ

/-! ### The archimedean summand on the whole line -/

/-- The identity `ξ'/ξ = 1/s + 1/(s−1) + (Γ_ℝ)'/Γ_ℝ + ζ'/ζ` needs `Im s ≠ 0`, so on the line `Re s
= 2` it holds for every `y` except `y = 0`. -/
theorem archimedean_vline_ae (φ : ℂ → ℂ) :
    (fun y : ℝ => logDeriv Gammaℝ ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
      =ᵐ[volume] fun y : ℝ =>
        (logDeriv riemannXi ((2 : ℂ) + y * I) - 1 / ((2 : ℂ) + y * I)
          - 1 / (((2 : ℂ) + y * I) - 1) - logDeriv riemannZeta ((2 : ℂ) + y * I))
        * φ ((2 : ℂ) + y * I) := by
  have hae : ∀ᵐ y : ℝ, y ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hae] with y hy
  have him : (((2 : ℂ) + y * I)).im ≠ 0 := by simpa using hy
  rw [logDeriv_gammaR_eq him (riemannZeta_ne_zero_of_re_eq_two (by simp))]

/-- **The four-way split, on the whole line.** -/
theorem integral_vline_split_full (hA : 0 ≤ A) (hφc : Continuous φ)
    (hφ : ∀ y : ℝ, ‖φ ((2 : ℂ) + y * I)‖ ≤ A / (1 + |y|) ^ 3) :
    (∫ y : ℝ, logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
      = (∫ y : ℝ, 1 / ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
        + (∫ y : ℝ, 1 / (((2 : ℂ) + y * I) - 1) * φ ((2 : ℂ) + y * I))
        + (∫ y : ℝ, logDeriv Gammaℝ ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
        + (∫ y : ℝ, logDeriv riemannZeta ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)) := by
  have h2 := integrable_one_div_vline_full hA hφc hφ
  have h3 := integrable_one_div_sub_one_vline_full hA hφc hφ
  have h4 := integrable_logDeriv_riemannZeta_vline_full hA hφc hφ
  have hg : (∫ y : ℝ, logDeriv Gammaℝ ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I))
      = ∫ y : ℝ, (logDeriv riemannXi ((2 : ℂ) + y * I) - 1 / ((2 : ℂ) + y * I)
          - 1 / (((2 : ℂ) + y * I) - 1) - logDeriv riemannZeta ((2 : ℂ) + y * I))
        * φ ((2 : ℂ) + y * I) := integral_congr_ae (archimedean_vline_ae φ)
  rw [hg]
  have hexp : ∀ y : ℝ,
      (logDeriv riemannXi ((2 : ℂ) + y * I) - 1 / ((2 : ℂ) + y * I)
        - 1 / (((2 : ℂ) + y * I) - 1) - logDeriv riemannZeta ((2 : ℂ) + y * I))
        * φ ((2 : ℂ) + y * I)
      = logDeriv riemannXi ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)
        - (1 / ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)
          + 1 / (((2 : ℂ) + y * I) - 1) * φ ((2 : ℂ) + y * I)
          + logDeriv riemannZeta ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)) := by
    intro y; ring
  simp_rw [hexp]
  have h23 : Integrable (fun y : ℝ =>
      1 / ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)
        + 1 / (((2 : ℂ) + y * I) - 1) * φ ((2 : ℂ) + y * I)) := h2.add h3
  have h234 : Integrable (fun y : ℝ =>
      1 / ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)
        + 1 / (((2 : ℂ) + y * I) - 1) * φ ((2 : ℂ) + y * I)
        + logDeriv riemannZeta ((2 : ℂ) + y * I) * φ ((2 : ℂ) + y * I)) := h23.add h4
  rw [integral_sub (integrable_vline hA hφc hφ) h234, integral_add h23 h4,
    integral_add h2 h3]
  ring

end Cvs.Zeta
