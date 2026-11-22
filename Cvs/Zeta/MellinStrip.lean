import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# Mellin transforms are bounded on vertical strips

The modulus of `mellin f s = ∫ x in Ioi 0, x^(s-1) • f x` never sees `Im s`: the weight `‖(x :
ℂ)^(s-1)‖` equals `x^(Re s - 1)` exactly.
-/

open MeasureTheory Set Complex Real

namespace Cvs.Zeta

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A Mellin transform's modulus is bounded by the Mellin transform of the modulus,
evaluated at `Re s`.  The right-hand side does not see `Im s` at all. -/
theorem norm_mellin_le (f : ℝ → E) (s : ℂ) :
    ‖mellin f s‖ ≤ ∫ x in Ioi (0 : ℝ), x ^ (s.re - 1) * ‖f x‖ := by
  rw [mellin]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  congr 2

/-- Convergence of the Mellin transform at a real point gives integrability of the
real majorant used in `norm_mellin_le`. -/
theorem integrableOn_rpow_mul_norm_of_mellinConvergent {f : ℝ → E} {σ : ℝ}
    (h : MellinConvergent f (σ : ℂ)) :
    IntegrableOn (fun x : ℝ => x ^ (σ - 1) * ‖f x‖) (Ioi 0) := by
  refine IntegrableOn.congr_fun (h.norm) (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  norm_num

/-- For `x > 0` and `a ≤ σ ≤ b`, the weight `x^(σ-1)` is dominated by the sum of the
two edge weights: below `1` the left edge wins, above `1` the right edge does. -/
theorem rpow_sub_one_le_add {a b σ x : ℝ} (hx : 0 < x) (ha : a ≤ σ) (hb : σ ≤ b) :
    x ^ (σ - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
  rcases le_or_gt x 1 with h1 | h1
  · have : x ^ (σ - 1) ≤ x ^ (a - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith)
    have hb' : (0 : ℝ) ≤ x ^ (b - 1) := Real.rpow_nonneg hx.le _
    linarith
  · have : x ^ (σ - 1) ≤ x ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have ha' : (0 : ℝ) ≤ x ^ (a - 1) := Real.rpow_nonneg hx.le _
    linarith

/-- **A Mellin transform is bounded on vertical strips**, by the sum of its two edge
majorants — a bound with no dependence on `Im s` whatsoever. -/
theorem norm_mellin_le_strip (f : ℝ → E) {a b : ℝ} {s : ℂ}
    (hia : MellinConvergent f (a : ℂ)) (hib : MellinConvergent f (b : ℂ))
    (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖mellin f s‖
      ≤ (∫ x in Ioi (0 : ℝ), x ^ (a - 1) * ‖f x‖)
        + ∫ x in Ioi (0 : ℝ), x ^ (b - 1) * ‖f x‖ := by
  have hA := integrableOn_rpow_mul_norm_of_mellinConvergent hia
  have hB := integrableOn_rpow_mul_norm_of_mellinConvergent hib
  refine (norm_mellin_le f s).trans ?_
  rw [← integral_add hA hB]
  refine integral_mono_of_nonneg ?_ (hA.add hB) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have := rpow_sub_one_le_add (a := a) (b := b) (σ := s.re) hx0 ha hb
    have hf : (0 : ℝ) ≤ ‖f x‖ := norm_nonneg _
    nlinarith [Real.rpow_nonneg hx0.le (a - 1), Real.rpow_nonneg hx0.le (b - 1)]

/-! ### Application to the entire part of a functional-equation pair -/

/-- **`Λ₀` of any weak FE-pair is bounded on every vertical strip** , uniformly in `Im s`. -/
theorem norm_Λ₀_le_strip (P : WeakFEPair E) {a b : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖P.Λ₀ s‖
      ≤ (∫ x in Ioi (0 : ℝ), x ^ (a - 1) * ‖P.f_modif x‖)
        + ∫ x in Ioi (0 : ℝ), x ^ (b - 1) * ‖P.f_modif x‖ := by
  have hc : ∀ σ : ℝ, MellinConvergent P.f_modif (σ : ℂ) := fun σ =>
    (P.isStrongFEPair_toStrongFEPair.hasMellin (σ : ℂ)).1
  have hΛ : P.Λ₀ s = mellin P.f_modif s := rfl
  rw [hΛ]
  exact norm_mellin_le_strip _ (hc a) (hc b) ha hb

end Cvs.Zeta
