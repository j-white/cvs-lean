import Mathlib
import Cvs.Zeta.ThetaDecay

/- Vendored from rosetta/research/pathlaw/lean/Cvs.Zeta/ZetaRealSegment.lean. -/

set_option autoImplicit false

namespace Cvs.Zeta

open Complex MeasureTheory

/-! ### The theta kernel on `[1, ∞)`, with an explicit constant -/

/-- `evenKernel 0` is the Jacobi theta function on the imaginary axis. -/
theorem evenKernel_zero_eq_jacobiTheta (t : ℝ) :
    ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) = jacobiTheta (I * (t : ℂ)) := by
  have h := HurwitzZeta.evenKernel_def 0 t
  rw [jacobiTheta_eq_jacobiTheta₂]
  simpa using h

/-- **The kernel bound, with an explicit constant.**  On `t ≥ 1` the geometric
prefactor of `norm_jacobiTheta_sub_one_le` is at most `4`, and `e^{−πt} ≤ e^{−t}`
because `π > 1`. -/
theorem abs_evenKernel_zero_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    |HurwitzZeta.evenKernel 0 t - 1| ≤ 4 * Real.exp (-t) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have him : (0 : ℝ) < (I * (t : ℂ)).im := by simpa using htpos
  have hb := norm_jacobiTheta_sub_one_le him
  have him' : (I * (t : ℂ)).im = t := by simp
  rw [him'] at hb
  -- the norm on the left is the real absolute value
  have hnorm : ‖jacobiTheta (I * (t : ℂ)) - 1‖ = |HurwitzZeta.evenKernel 0 t - 1| := by
    rw [← evenKernel_zero_eq_jacobiTheta t]
    rw [show ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1
        = ((HurwitzZeta.evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.norm_real _
  rw [hnorm] at hb
  refine hb.trans ?_
  -- `e^{-π t} ≤ e^{-π} < 1/2`, so the prefactor `2/(1 - e^{-π t}) ≤ 4`
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hle : Real.exp (-(Real.pi * t)) ≤ Real.exp (-t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hhalf : Real.exp (-(Real.pi * t)) ≤ 1 / 2 := by
    have : Real.exp (-(Real.pi * t)) ≤ Real.exp (-1) := by
      refine Real.exp_le_exp.mpr ?_; nlinarith
    refine this.trans ?_
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hpos : (0 : ℝ) < 1 - Real.exp (-Real.pi * t) := by
    rw [show -Real.pi * t = -(Real.pi * t) by ring]; linarith
  have hpre : 2 / (1 - Real.exp (-Real.pi * t)) ≤ 4 := by
    rw [div_le_iff₀ hpos]
    rw [show -Real.pi * t = -(Real.pi * t) by ring] at *
    linarith
  calc 2 / (1 - Real.exp (-Real.pi * t)) * Real.exp (-Real.pi * t)
      ≤ 4 * Real.exp (-Real.pi * t) := by
        refine mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le
    _ ≤ 4 * Real.exp (-t) := by
        rw [show -Real.pi * t = -(Real.pi * t) by ring]
        linarith

/-- The cosine kernel at `0` is the same function. -/
theorem abs_cosKernel_zero_sub_one_le {t : ℝ} (ht : 1 ≤ t) :
    |HurwitzZeta.cosKernel 0 t - 1| ≤ 4 * Real.exp (-t) := by
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  exact abs_evenKernel_zero_sub_one_le ht

/-! ### The Mellin tails -/

/-- **A tail of `Λ₀`, bounded.**  For a non-positive real exponent the power
factor is at most `1` on `[1, ∞)`, so the whole tail is dominated by
`∫₁^∞ 4e^{−t} dt = 4/e`. -/
theorem norm_kernel_tail_le {e : ℂ} (he : e.re ≤ 0) (K : ℝ → ℝ)
    (hK : ∀ t : ℝ, 1 ≤ t → |K t - 1| ≤ 4 * Real.exp (-t)) :
    ‖∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ e • (((K t : ℝ) : ℂ) - 1)‖
      ≤ 4 * Real.exp (-1) := by
  have hint : IntegrableOn (fun t : ℝ => 4 * Real.exp (-t)) (Set.Ioi (1:ℝ)) := by
    have h := exp_neg_integrableOn_Ioi (1:ℝ) (b := 1) one_pos
    simp only [neg_mul, one_mul] at h
    exact h.const_mul 4
  refine (norm_integral_le_of_norm_le hint ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) ≤ t := le_of_lt ht
    have htpos : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    have hpow : (t : ℝ) ^ e.re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 he
    have hval : ‖((K t : ℝ) : ℂ) - 1‖ = |K t - 1| := by
      rw [show ((K t : ℝ) : ℂ) - 1 = ((K t - 1 : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_real _
    rw [hval]
    calc (t : ℝ) ^ e.re * |K t - 1| ≤ 1 * (4 * Real.exp (-t)) := by
          refine mul_le_mul hpow (hK t ht1) (abs_nonneg _) (by positivity)
      _ = 4 * Real.exp (-t) := by ring
  · rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]

/-! ### `Λ₀` is small on the strip -/

/-- **`‖Λ₀‖ ≤ 4/e` for every `s` in the closed strip.**  Both tails obey the same
bound, and Mathlib's `Λ₀` is their average. -/
theorem norm_completedRiemannZeta₀_le_of_re_mem {s : ℂ}
    (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ 4 * Real.exp (-1) := by
  rw [completedRiemannZeta₀_eq_Lambda0, Lambda0_zeta_eq_tails, norm_div]
  have hre : (s / 2).re = s.re / 2 := by simp
  have he1 : (s / 2 - 1).re ≤ 0 := by
    rw [Complex.sub_re, hre]; simp; linarith
  have he2 : ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1).re ≤ 0 := by
    rw [Complex.sub_re, Complex.sub_re, hre]
    simp
    linarith
  have hA := norm_kernel_tail_le he1 (HurwitzZeta.evenKernel 0)
    (fun t ht => abs_evenKernel_zero_sub_one_le ht)
  have hB := norm_kernel_tail_le he2 (HurwitzZeta.cosKernel 0)
    (fun t ht => abs_cosKernel_zero_sub_one_le ht)
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have htri := norm_add_le
    (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s / 2 - 1) •
      (((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1))
    (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1) •
      (((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1))
  have := htri.trans (add_le_add hA hB)
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

/-! ### The pole terms are large -/

/-- `1/s + 1/(1−s) = 1/(s(1−s)) ≥ 4` on `(0,1)`, since `s(1−s) ≤ ¼`.  The
inequality is `(2s−1)² ≥ 0`. -/
theorem four_le_norm_pole_terms {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    (4 : ℝ) ≤ ‖1 / (s : ℂ) + 1 / (1 - (s : ℂ))‖ := by
  have hs : (s : ℂ) ≠ 0 := by
    simpa using ne_of_gt h0
  have hs1 : (1 : ℂ) - (s : ℂ) ≠ 0 := by
    intro h
    have : (s : ℂ) = 1 := by linear_combination -h
    have : s = 1 := by exact_mod_cast this
    linarith
  have hcast : 1 / (s : ℂ) + 1 / (1 - (s : ℂ)) = ((1 / s + 1 / (1 - s) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hpos : (0 : ℝ) < 1 / s + 1 / (1 - s) := by
    have : (0:ℝ) < 1 - s := by linarith
    positivity
  rw [abs_of_pos hpos]
  have h1s : (0:ℝ) < 1 - s := by linarith
  rw [div_add_div _ _ (ne_of_gt h0) (ne_of_gt h1s), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * s - 1)]

/-! ### The conclusion -/

/-- **`ζ` has no zero on the real segment `(0,1)`.** A zero there would force `Λ₀(s) = 1/s +
1/(1−s)`, whose norm is at least `4`, while `Λ₀` is at most `4/e` on the whole strip. -/
theorem riemannZeta_ne_zero_of_mem_Ioo {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    riemannZeta (s : ℂ) ≠ 0 := by
  intro hz
  have hs0 : (s : ℂ) ≠ 0 := by simpa using ne_of_gt h0
  have hre : ((s : ℂ)).re = s := Complex.ofReal_re s
  -- `ζ = Λ / Γ_ℝ` and `Γ_ℝ ≠ 0`, so `Λ(s) = 0`
  have hG : Gammaℝ (s : ℂ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hre]; exact h0)
  have hL : completedRiemannZeta (s : ℂ) = 0 := by
    have h := riemannZeta_def_of_ne_zero hs0
    rw [hz] at h
    rcases div_eq_zero_iff.mp h.symm with h' | h'
    · exact h'
    · exact absurd h' hG
  -- hence `Λ₀(s) = 1/s + 1/(1-s)`
  have hsplit := completedRiemannZeta_eq (s : ℂ)
  rw [hL] at hsplit
  have hkey : completedRiemannZeta₀ (s : ℂ) = 1 / (s : ℂ) + 1 / (1 - (s : ℂ)) := by
    linear_combination -hsplit
  -- but `Λ₀` is small and the right-hand side is large
  have hsmall := norm_completedRiemannZeta₀_le_of_re_mem
    (s := (s : ℂ)) (by rw [hre]; linarith) (by rw [hre]; linarith)
  rw [hkey] at hsmall
  have hbig := four_le_norm_pole_terms h0 h1
  have he : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  linarith

/-! ### The residual, closed -/

end Cvs.Zeta
