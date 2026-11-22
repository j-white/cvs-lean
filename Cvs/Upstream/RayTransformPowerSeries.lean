import Mathlib
import Cvs.Prolate.Mellin.RayTransformEdgeSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ray transform of an even power series as a sum of simple fractions

If `F(e^{−is}) = Σ_j b_j e^{−2ijs}` with `Σ|b_j| < ∞`, then `T_F(w) = Σ_j b_j·i/(w − 2j − ½)`; if
`G(e^{−is}) = Σ_j b_j e^{i(2j + 1)s}`, then `T_G(w) = Σ_j b_j·i/(2j + ½ + w)`, for `Im w > 0`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)

namespace Cvs.Upstream.RayTransformPowerSeries
open Cvs.ZeroCounting

/-- `∫_0^∞ e^{i(w + κ)s} ds = i/(w + κ)` for `Im w > 0`. -/
theorem integral_exp_I (κ : ℝ) {w : ℂ} (hw : 0 < w.im) :
    ∫ s in Ioi (0 : ℝ), Complex.exp (I * (w + κ) * s) = I / (w + κ) := by
  have hre : (I * (w + κ)).re < 0 := by simp; linarith
  rw [integral_exp_mul_complex_Ioi hre 0]
  have hne : (w + κ : ℂ) ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  rw [Complex.I_sq]

/-- **A series of exponentials under the ray integral**:
`∫_0^∞ (Σ_j b_j e^{iκ_js}) e^{iws} ds = Σ_j b_j·i/(w + κ_j)`. -/
theorem hasSum_integral_series {b : ℕ → ℂ} (hb : Summable fun j => ‖b j‖) (κ : ℕ → ℝ) {w : ℂ} (hw : 0 < w.im)
    {f : ℝ → ℂ} (hf : ∀ s : ℝ, 0 < s → HasSum (fun j => b j * Complex.exp (I * κ j * s)) (f s)) :
    HasSum (fun j => b j * (I / (w + κ j))) (∫ s in Ioi (0 : ℝ), f s * Complex.exp (I * w * s)) := by
  have hterm : ∀ j : ℕ, ∫ s in Ioi (0 : ℝ), b j * Complex.exp (I * κ j * s) * Complex.exp (I * w * s)
      = b j * (I / (w + κ j)) := fun j => by
    rw [← integral_exp_I (κ j) hw, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
  simp_rw [← hterm]
  have hnorm : ∀ j : ℕ, ∀ s : ℝ, ‖b j * Complex.exp (I * κ j * s) * Complex.exp (I * w * s)‖
      = ‖b j‖ * Real.exp (-(w.im * s)) := fun j s => by
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    simp
  refine hasSum_integral_of_dominated_convergence (fun j s => ‖b j‖ * Real.exp (-(w.im * s))) ?_ ?_ ?_ ?_ ?_
  · intro j; exact (by fun_prop : Continuous fun s : ℝ =>
      b j * Complex.exp (I * κ j * s) * Complex.exp (I * w * s)).aestronglyMeasurable
  · intro j; exact Eventually.of_forall fun s => (hnorm j s).le
  · exact Eventually.of_forall fun s => hb.mul_right _
  · have : (fun s : ℝ => ∑' j, ‖b j‖ * Real.exp (-(w.im * s)))
        = fun s => (∑' j, ‖b j‖) * Real.exp (-(w.im * s)) := by
      funext s; rw [tsum_mul_right]
    rw [this]
    have := (exp_neg_integrableOn_Ioi 0 hw).const_mul (∑' j, ‖b j‖)
    refine Integrable.congr this (Eventually.of_forall fun s => ?_)
    simp only; ring_nf
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    exact (hf s hs).mul_right _

/-- `(e^{−is})^{2j} e^{−is/2} = e^{−i(2j + ½)s}`. -/
theorem circle_pow (s : ℝ) (j : ℕ) :
    Complex.exp (-(s * I)) ^ (2 * j) * Complex.exp (-(s * I / 2))
      = Complex.exp (I * ((-(2 * j + 1 / 2 : ℝ) : ℝ) : ℂ) * s) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring

/-- **The Mittag-Leffler form of the ray transform** of an even series: `T_F(w) = Σ_j b_j·i/(w − 2j − ½)`. -/
theorem hasSum_rayT {b : ℕ → ℂ} (hb : Summable fun j => ‖b j‖) {F : ℂ → ℂ}
    (hF : ∀ s : ℝ, HasSum (fun j => b j * Complex.exp (-(s * I)) ^ (2 * j)) (F (Complex.exp (-(s * I)))))
    {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun j => b j * (I / (w - (2 * j + 1 / 2)))) (rayT F w) := by
  have h := hasSum_integral_series hb (fun j => -(2 * j + 1 / 2 : ℝ)) hw
    (f := fun s => F (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2))) fun s _ => by
      have := (hF s).mul_right (Complex.exp (-(s * I / 2)))
      refine this.congr_fun fun j => ?_
      rw [mul_assoc (b j), circle_pow]
  have e1 : (fun j : ℕ => b j * (I / (w + ((-(2 * j + 1 / 2 : ℝ) : ℝ) : ℂ))))
      = fun j => b j * (I / (w - (2 * j + 1 / 2))) := by
    funext j; push_cast; ring_nf
  rw [e1] at h
  convert h using 1
  unfold rayT
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  congr 1; ring_nf

/-- **The reflected form**: if `G(e^{−is}) = Σ_j b_j e^{i(2j+1)s}`, then `T_G(w) = Σ_j b_j·i/(2j + ½ + w)`. -/
theorem hasSum_rayT_refl {b : ℕ → ℂ} (hb : Summable fun j => ‖b j‖) {G : ℂ → ℂ}
    (hG : ∀ s : ℝ, HasSum (fun j => b j * Complex.exp (s * I) ^ (2 * j + 1)) (G (Complex.exp (-(s * I)))))
    {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun j => b j * (I / (2 * j + 1 / 2 + w))) (rayT G w) := by
  have h := hasSum_integral_series hb (fun j => (2 * j + 1 / 2 : ℝ)) hw
    (f := fun s => G (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2))) fun s _ => by
      have := (hG s).mul_right (Complex.exp (-(s * I / 2)))
      refine this.congr_fun fun j => ?_
      rw [mul_assoc (b j), ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 2; push_cast; ring
  have e1 : (fun j : ℕ => b j * (I / (w + ((2 * j + 1 / 2 : ℝ) : ℂ))))
      = fun j => b j * (I / (2 * j + 1 / 2 + w)) := by
    funext j; push_cast; ring_nf
  rw [e1] at h
  convert h using 1
  unfold rayT
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  congr 1; ring_nf

end Cvs.Upstream.RayTransformPowerSeries

end
