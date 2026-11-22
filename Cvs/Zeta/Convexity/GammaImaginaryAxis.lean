import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

-- prose-lint-allow: R3 names what is absent (Stirling for Gamma on vertical lines) by name
/-!
# `‖Γ‖` on the imaginary axis, exactly; and a correction
-/

open Complex

namespace Cvs.ZetaGrowth

/-- **`‖Γ(it)‖² = π/(t·sinh(πt))`, exactly.**  Reflection at `z = it`, with
`Γ(1-it) = (-it)·Γ(-it)` and `Γ(-it) = conj Γ(it)`.  No Stirling. -/
theorem norm_Gamma_I_sq {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma ((t : ℂ) * I)‖ ^ 2 = Real.pi / (t * Real.sinh (Real.pi * t)) := by
  have htne : (t : ℂ) * I ≠ 0 := by
    refine mul_ne_zero ?_ I_ne_zero
    simpa using ne_of_gt ht
  have hneg : -((t : ℂ) * I) ≠ 0 := neg_ne_zero.mpr htne
  -- Γ(1-it) = (-it)·Γ(-it)
  have hrec : Complex.Gamma (1 - (t : ℂ) * I) = (-((t : ℂ) * I)) * Complex.Gamma (-((t : ℂ) * I)) := by
    have h := Complex.Gamma_add_one (-((t : ℂ) * I)) hneg
    rw [show -((t : ℂ) * I) + 1 = 1 - (t : ℂ) * I by ring] at h
    exact h
  -- Γ(-it) = conj Γ(it)
  have hconj : Complex.Gamma (-((t : ℂ) * I)) = (starRingEnd ℂ) (Complex.Gamma ((t : ℂ) * I)) := by
    rw [← Complex.Gamma_conj]
    congr 1
    apply Complex.ext <;> simp
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * I)
  rw [hrec, hconj] at hrefl
  -- the sine
  have hsin : Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * I)) = ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * I := by
    have harg : (Real.pi : ℂ) * ((t : ℂ) * I) = ((Real.pi * t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [harg, Complex.sin_mul_I, Complex.ofReal_sinh]
  rw [hsin] at hrefl
  -- Γ(it) * conj Γ(it) = ‖Γ(it)‖²
  have hmc : Complex.Gamma ((t : ℂ) * I) * (starRingEnd ℂ) (Complex.Gamma ((t : ℂ) * I))
      = ((‖Complex.Gamma ((t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hkey : (-((t : ℂ) * I)) * ((‖Complex.Gamma ((t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
      = (Real.pi : ℂ) / (((Real.sinh (Real.pi * t) : ℝ) : ℂ) * I) := by
    rw [← hmc]
    linear_combination hrefl
  -- take norms
  have hsinh : 0 < Real.sinh (Real.pi * t) := Real.sinh_pos_iff.mpr (by positivity)
  have hn : t * ‖Complex.Gamma ((t : ℂ) * I)‖ ^ 2 = Real.pi / Real.sinh (Real.pi * t) := by
    have h := congrArg (fun z : ℂ => ‖z‖) hkey
    simp only [norm_mul, norm_neg, norm_div, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hsinh, abs_of_pos Real.pi_pos,
      abs_of_nonneg (sq_nonneg (‖Complex.Gamma ((t : ℂ) * I)‖))] at h
    exact h
  field_simp at hn
  rw [show t * Real.pi = Real.pi * t by ring] at hn
  rw [eq_div_iff (by positivity)]
  linear_combination hn

theorem norm_Gammaℂ_I (t : ℝ) : ‖Gammaℂ ((t : ℂ) * I)‖ = 2 * ‖Complex.Gamma ((t : ℂ) * I)‖ := by
  rw [Gammaℂ_def, norm_mul, norm_mul]
  have h2pi : ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
  rw [h2pi, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  have hre : (-((t : ℂ) * I)).re = 0 := by simp
  rw [hre, Real.rpow_zero]
  norm_num

theorem norm_cos_I (t : ℝ) :
    ‖Complex.cos ((Real.pi : ℂ) * ((t : ℂ) * I) / 2)‖ = Real.cosh (Real.pi * t / 2) := by
  have harg : (Real.pi : ℂ) * ((t : ℂ) * I) / 2 = ((Real.pi * t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [harg, Complex.cos_mul_I, ← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _)]

/-- **The functional-equation factor on the imaginary axis, bounded exactly.**
‖Γ_ℝ(1-it)/Γ_ℝ(it)‖² = t·tanh(πt/2)/(2π) ≤ t/(2π) . -/
theorem norm_chi_sq_le {t : ℝ} (ht : 0 < t) :
    (‖Gammaℝ (1 - (t : ℂ) * I)‖ / ‖Gammaℝ ((t : ℂ) * I)‖) ^ 2 ≤ t / (2 * Real.pi) := by
  have hnm : ∀ n : ℕ, ((t : ℂ) * I) ≠ -(2 * n + 1) := by
    intro n hc
    have hre : ((t : ℂ) * I).re = (-(2 * (n : ℂ) + 1)).re := by rw [hc]
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hratio := Gammaℝ_div_Gammaℝ_one_sub hnm
  have hGne : Gammaℝ ((t : ℂ) * I) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have him : ((t : ℂ) * I).im = (-(2 * (n : ℂ))).im := by rw [hn]
    simp at him
    linarith
  have hG1ne : Gammaℝ (1 - (t : ℂ) * I) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    have him : (1 - (t : ℂ) * I).im = (-(2 * (n : ℂ))).im := by rw [hn]
    simp at him
    linarith
  -- the ratio in closed form
  have hnorms : ‖Gammaℝ ((t : ℂ) * I)‖ / ‖Gammaℝ (1 - (t : ℂ) * I)‖
      = 2 * ‖Complex.Gamma ((t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) := by
    rw [← norm_div, hratio, norm_mul, norm_Gammaℂ_I, norm_cos_I]
  have hGpos : 0 < ‖Complex.Gamma ((t : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero (fun n hc => by
      have him : ((t : ℂ) * I).im = (-(n : ℂ)).im := by rw [hc]
      simp at him
      linarith)
  have hcosh : 0 < Real.cosh (Real.pi * t / 2) := Real.cosh_pos _
  have hG1pos : 0 < ‖Gammaℝ (1 - (t : ℂ) * I)‖ := norm_pos_iff.mpr hG1ne
  have hGRpos : 0 < ‖Gammaℝ ((t : ℂ) * I)‖ := norm_pos_iff.mpr hGne
  -- invert
  have hinv : ‖Gammaℝ (1 - (t : ℂ) * I)‖ / ‖Gammaℝ ((t : ℂ) * I)‖
      = 1 / (2 * ‖Complex.Gamma ((t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2)) := by
    rw [← hnorms, one_div, inv_div]
  rw [hinv, div_pow, one_pow]
  -- the exact square
  have hsq := norm_Gamma_I_sq ht
  have hsinh2 : Real.sinh (Real.pi * t)
      = 2 * Real.sinh (Real.pi * t / 2) * Real.cosh (Real.pi * t / 2) := by
    rw [show Real.pi * t = 2 * (Real.pi * t / 2) by ring, Real.sinh_two_mul]
    ring_nf
  have hsc : Real.sinh (Real.pi * t / 2) ≤ Real.cosh (Real.pi * t / 2) :=
    le_of_lt (Real.sinh_lt_cosh _)
  have hden : (2 * ‖Complex.Gamma ((t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2)) ^ 2
      = 4 * (Real.pi / (t * Real.sinh (Real.pi * t))) * Real.cosh (Real.pi * t / 2) ^ 2 := by
    rw [mul_pow, mul_pow, hsq]; ring
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, hden, hsinh2]
  have hsinhpos : 0 < Real.sinh (Real.pi * t / 2) :=
    Real.sinh_pos_iff.mpr (by positivity)
  have hpi : 0 < Real.pi := Real.pi_pos
  field_simp
  nlinarith [hsc, hsinhpos, hcosh, ht, hpi, sq_nonneg (Real.cosh (Real.pi * t / 2))]

end Cvs.ZetaGrowth
