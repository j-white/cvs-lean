import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The `σ = -1/2` edge of the convexity bound, without Stirling
-/

open Complex

namespace Cvs.ArchScore

/-- The two `Γ`-arguments at `σ = -1/2` and `σ = 3/2` differ by exactly one. -/
theorem gammaArg_step (t : ℝ) :
    ((3 : ℂ) / 2 - (t : ℂ) * I) / 2 = (starRingEnd ℂ) (((-1 : ℂ) / 2 + (t : ℂ) * I) / 2 + 1) := by
  have hw : ((-1 : ℂ) / 2 + (t : ℂ) * I) / 2 + 1 = ((3 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hw, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast; ring

theorem arg_ne_zero (t : ℝ) : ((-1 : ℂ) / 2 + (t : ℂ) * I) / 2 ≠ 0 := by
  intro h
  have hre : (((-1 : ℂ) / 2 + (t : ℂ) * I) / 2).re = 0 := by rw [h]; simp
  simp at hre

/-- **The Gamma factors at the two edges differ by exactly `‖-1/4 + it/2‖`.**
Conjugation plus `Γ(z+1) = z·Γ(z)`; no asymptotics. -/
theorem norm_gamma_edges (t : ℝ) :
    ‖Complex.Gamma (((3 : ℂ) / 2 - (t : ℂ) * I) / 2)‖
      = ‖((-1 : ℂ) / 2 + (t : ℂ) * I) / 2‖
        * ‖Complex.Gamma (((-1 : ℂ) / 2 + (t : ℂ) * I) / 2)‖ := by
  rw [gammaArg_step, Complex.Gamma_conj, norm_conj,
    Complex.Gamma_add_one _ (arg_ne_zero t), norm_mul]

/-- The `π`-powers contribute exactly `π⁻¹`. -/
theorem norm_pi_cpow (z : ℂ) : ‖(Real.pi : ℂ) ^ z‖ = Real.pi ^ z.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]

/-- **The edge identity.** -/
theorem norm_gammaR_edges (t : ℝ) :
    ‖Gammaℝ ((3 : ℂ) / 2 - (t : ℂ) * I)‖
      = Real.pi⁻¹ * ‖((-1 : ℂ) / 2 + (t : ℂ) * I) / 2‖
        * ‖Gammaℝ ((-1 : ℂ) / 2 + (t : ℂ) * I)‖ := by
  rw [Gammaℝ_def, Gammaℝ_def, norm_mul, norm_mul, norm_pi_cpow, norm_pi_cpow,
    norm_gamma_edges]
  have h1 : (-((3 : ℂ) / 2 - (t : ℂ) * I) / 2).re = -(3 / 4) := by simp; ring
  have h2 : (-((-1 : ℂ) / 2 + (t : ℂ) * I) / 2).re = 1 / 4 := by simp; ring
  rw [h1, h2]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have : Real.pi ^ (-(3 / 4) : ℝ) = Real.pi⁻¹ * Real.pi ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_neg_one Real.pi, ← Real.rpow_add hpi]
    norm_num
  rw [this]
  ring

/-! ### The edge bound itself -/

theorem gammaR_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  push_neg
  intro n h
  rw [h] at hs
  simp at hs

/-- **The `σ = -1/2` edge, from the recurrence.**  `ζ` there is the bounded `σ = 3/2` value
times `π⁻¹‖(-1/2+it)/2‖`, which is linear in `|t|`. -/
theorem zeta_neg_half_eq (t : ℝ) (ht : t ≠ 0) :
    ‖riemannZeta ((-1 : ℂ) / 2 + (t : ℂ) * I)‖
      = Real.pi⁻¹ * ‖((-1 : ℂ) / 2 + (t : ℂ) * I) / 2‖
        * ‖riemannZeta ((3 : ℂ) / 2 - (t : ℂ) * I)‖ := by
  have hsne : ((-1 : ℂ) / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hr : ((-1 : ℂ) / 2 + (t : ℂ) * I).re = 0 := by rw [h]; simp
    simp at hr
  have h3ne : ((3 : ℂ) / 2 - (t : ℂ) * I) ≠ 0 := by
    intro h
    have hr : ((3 : ℂ) / 2 - (t : ℂ) * I).re = 0 := by rw [h]; simp
    simp at hr
  have hgs : Gammaℝ ((-1 : ℂ) / 2 + (t : ℂ) * I) ≠ 0 :=
    gammaR_ne_zero_of_im_ne_zero (by simpa using ht)
  -- functional equation, then `Λ = Γℝ·ζ` on the far edge
  have hfe : completedRiemannZeta ((-1 : ℂ) / 2 + (t : ℂ) * I)
      = completedRiemannZeta ((3 : ℂ) / 2 - (t : ℂ) * I) := by
    have hflip : ((-1 : ℂ) / 2 + (t : ℂ) * I) = 1 - ((3 : ℂ) / 2 - (t : ℂ) * I) := by ring
    rw [hflip, completedRiemannZeta_one_sub]
  have hsplit : completedRiemannZeta ((3 : ℂ) / 2 - (t : ℂ) * I)
      = Gammaℝ ((3 : ℂ) / 2 - (t : ℂ) * I) * riemannZeta ((3 : ℂ) / 2 - (t : ℂ) * I) := by
    have hg3 : Gammaℝ ((3 : ℂ) / 2 - (t : ℂ) * I) ≠ 0 :=
      gammaR_ne_zero_of_im_ne_zero (by simpa using neg_ne_zero.mpr ht)
    have hcancel : Gammaℝ ((3 : ℂ) / 2 - (t : ℂ) * I)
        * (completedRiemannZeta ((3 : ℂ) / 2 - (t : ℂ) * I)
          / Gammaℝ ((3 : ℂ) / 2 - (t : ℂ) * I))
        = completedRiemannZeta ((3 : ℂ) / 2 - (t : ℂ) * I) := by
      rw [← mul_div_assoc, mul_comm (Gammaℝ ((3 : ℂ) / 2 - (t : ℂ) * I)),
        mul_div_assoc, div_self hg3, mul_one]
    rw [riemannZeta_def_of_ne_zero h3ne, hcancel]
  rw [riemannZeta_def_of_ne_zero hsne, hfe, hsplit, norm_div, norm_mul,
    norm_gammaR_edges t]
  rw [mul_comm (Real.pi⁻¹ * ‖((-1 : ℂ) / 2 + (t : ℂ) * I) / 2‖)
    ‖Gammaℝ ((-1 : ℂ) / 2 + (t : ℂ) * I)‖]
  rw [mul_assoc, mul_comm ‖Gammaℝ ((-1 : ℂ) / 2 + (t : ℂ) * I)‖,
    mul_div_assoc, div_self (norm_ne_zero_iff.mpr hgs), mul_one]

end Cvs.ArchScore
