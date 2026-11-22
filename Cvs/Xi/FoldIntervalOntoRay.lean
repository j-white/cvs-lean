import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Xi.InversionIntervalToRay
import Cvs.Xi.MellinSplitAtOne

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Folding the interval onto the ray

Inverting the variable turns the integral below one into one beyond it, and the pair's functional
equation replaces the modified function by its partner at the cost of a power. Collecting the three
powers leaves the partner's integrand at the reflected exponent.
-/

noncomputable section

open Set MeasureTheory Complex

namespace Cvs.Xi.FoldIntervalOntoRay

/-- **The three powers collect.** -/
theorem weight_eq {x : ℝ} (hx : 0 < x) (w : ℂ) (k : ℝ) :
    ((x ^ 2 : ℝ) : ℂ)⁻¹ * (((x : ℝ) : ℂ) ^ (w - 1))⁻¹ * ((x ^ k : ℝ) : ℂ)
      = ((x : ℝ) : ℂ) ^ ((k : ℂ) - w - 1) := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have h2 : ((x ^ 2 : ℝ) : ℂ) = ((x : ℝ) : ℂ) ^ (2 : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    push_cast
    ring
  have hk : ((x ^ k : ℝ) : ℂ) = ((x : ℝ) : ℂ) ^ (k : ℂ) := Complex.ofReal_cpow hx.le k
  rw [h2, hk, ← Complex.cpow_neg, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hx0,
    ← Complex.cpow_add _ _ hx0]
  congr 1
  ring

/-- **The integral below one, folded onto the ray beyond it.** -/
theorem integral_Ioo_eq (P : WeakFEPair ℂ) (w : ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • P.f_modif t)
      = P.ε • ∫ x in Ioi (1 : ℝ), ((x : ℝ) : ℂ) ^ ((P.k : ℂ) - w - 1) • P.g_modif x := by
  rw [Cvs.Xi.InversionIntervalToRay.integral_Ioo_eq_integral_Ioi_inv
      (fun t : ℝ => (t : ℂ) ^ (w - 1) • P.f_modif t), ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx0)
  have hfe : P.f_modif x⁻¹ = (P.ε * ((x ^ P.k : ℝ) : ℂ)) • P.g_modif x := by
    rw [← one_div]; exact P.hf_modif_FE x hx0
  have hinv : (((x⁻¹ : ℝ) : ℂ)) ^ (w - 1) = ((((x : ℝ) : ℂ)) ^ (w - 1))⁻¹ := by
    rw [Complex.ofReal_inv]
    exact Complex.inv_cpow_ofReal_nonneg hx0.le _
  rw [hfe, hinv]
  simp only [Complex.real_smul, smul_eq_mul]
  rw [← weight_eq hx0 w P.k]
  push_cast
  ring

/-- **`Λ₀` as a pair of integrals from one.** -/
theorem Λ₀_eq_integral_Ioi (P : WeakFEPair ℂ) (w : ℂ) :
    P.Λ₀ w = (P.ε • ∫ x in Ioi (1 : ℝ), ((x : ℝ) : ℂ) ^ ((P.k : ℂ) - w - 1) • P.g_modif x)
      + ∫ t in Ici (1 : ℝ), (t : ℂ) ^ (w - 1) • P.f_modif t := by
  rw [Cvs.Xi.MellinSplitAtOne.Λ₀_split P w, integral_Ioo_eq P w]

end Cvs.Xi.FoldIntervalOntoRay
