import Mathlib
import Cvs.Route.Visibility.VisibilityLandauTransition

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The averaged exterior-column energy and its closed form

`∫_{u>1} (u² + x²)/(u² − x²)² du = 1/(1 − x²)` for `|x| < 1`, so the averaged column energy with weight one on
`I = [−½, ½]` and two on the lips `½ < |x| < ℓ` is `(2 artanh ℓ − artanh ½)/π²`: `Θ₀/2` at `ℓ = 3/5` and `Θ/2` at
`ℓ = 1/√3`; and the Laplace kernel `∫_{v>0} e^{−(u−t)v} dv = 1/(u − t)` with `∫_{t>0} e^{−qt}/(1 + t) dt ≤ 1/q`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace Cvs.Prolate.Hardy.AveragedColumnEnergy
open Cvs.ZeroCounting

/-! ### The exterior integral -/

theorem hasDerivAt_col {x u : ℝ} (h : u ^ 2 - x ^ 2 ≠ 0) :
    HasDerivAt (fun u => -u / (u ^ 2 - x ^ 2)) ((u ^ 2 + x ^ 2) / (u ^ 2 - x ^ 2) ^ 2) u := by
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2 - x ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).sub_const (x ^ 2)
  refine ((hasDerivAt_id' u).neg.div h1 h).congr_deriv ?_
  field_simp
  simp only [Pi.neg_apply]
  ring

theorem tendsto_col (x : ℝ) : Tendsto (fun u : ℝ => -u / (u ^ 2 - x ^ 2)) atTop (𝓝 0) := by
  have h0 : (1 : ℝ) - x ^ 2 * 0 ^ 2 ≠ 0 := by norm_num
  have hc : ContinuousAt (fun t : ℝ => -t * (1 - x ^ 2 * t ^ 2)⁻¹) 0 :=
    (continuous_neg.continuousAt).mul ((continuousAt_const.sub (continuousAt_const.mul
      (continuousAt_id.pow 2))).inv₀ h0)
  have ht := hc.tendsto.comp tendsto_inv_atTop_zero
  rw [show (-0 * (1 - x ^ 2 * 0 ^ 2)⁻¹ : ℝ) = 0 by simp] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (|x| + 1)] with u hu
  have hu0 : 0 < u := by linarith [abs_nonneg x]
  have hxu : x ^ 2 < u ^ 2 := by
    have : |x| < u := by linarith
    nlinarith [sq_abs x, abs_nonneg x]
  have hne : u ^ 2 - x ^ 2 ≠ 0 := by linarith
  simp only [Function.comp]
  field_simp

/-- **The exterior column integral** `∫_{u>1} (u² + x²)/(u² − x²)² du = 1/(1 − x²)` for `|x| < 1`. -/
theorem integral_col {x : ℝ} (hx : |x| < 1) :
    ∫ u in Ioi 1, (u ^ 2 + x ^ 2) / (u ^ 2 - x ^ 2) ^ 2 = 1 / (1 - x ^ 2) := by
  have hx2 : x ^ 2 < 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hpos : ∀ u ∈ Ici (1 : ℝ), 0 < u ^ 2 - x ^ 2 := fun u hu => by
    have : (1 : ℝ) ≤ u ^ 2 := by nlinarith [hu.out]
    linarith
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun u hu => hasDerivAt_col (hpos u hu).ne')
    (integrableOn_Ioi_deriv_of_nonneg' (fun u hu => hasDerivAt_col (hpos u hu).ne')
      (fun u hu => div_nonneg (by positivity) (sq_nonneg _)) (tendsto_col x)) (tendsto_col x)]
  have : (1 : ℝ) ^ 2 - x ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### The interior integral -/

/-- `artanh t = (log(1 + t) − log(1 − t))/2`. -/
def artanh (t : ℝ) : ℝ := (Real.log (1 + t) - Real.log (1 - t)) / 2

theorem hasDerivAt_artanh {t : ℝ} (h1 : -1 < t) (h2 : t < 1) : HasDerivAt artanh (1 / (1 - t ^ 2)) t := by
  have ha : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + t)) t := by
    have := ((hasDerivAt_id t).const_add 1).log (by simp; linarith)
    simpa using this
  have hb : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - t)) t := by
    have := ((hasDerivAt_id t).const_sub 1).log (by simp; linarith)
    simpa [neg_div] using this
  have h3 : 1 + t ≠ 0 := by linarith
  have h4 : 1 - t ≠ 0 := by linarith
  refine ((ha.sub hb).div_const 2).congr_deriv ?_
  rw [show 1 - t ^ 2 = (1 + t) * (1 - t) by ring]
  field_simp
  ring

/-- `∫_α^β dx/(1 − x²) = artanh β − artanh α` on `(−1, 1)`. -/
theorem integral_inv_one_sub_sq {α β : ℝ} (hα1 : -1 < α) (hα2 : α < 1) (hβ1 : -1 < β) (hβ2 : β < 1) :
    ∫ x in α..β, 1 / (1 - x ^ 2) = artanh β - artanh α := by
  have hmem : ∀ x ∈ uIcc α β, -1 < x ∧ x < 1 := by
    intro x hx
    rcases mem_uIcc.1 hx with h | h
    · exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · exact ⟨by linarith [h.1], by linarith [h.2]⟩
  refine integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_artanh (hmem x hx).1 (hmem x hx).2) ?_
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (f := fun _ => (1 : ℝ)) (g := fun x : ℝ => 1 - x ^ 2) continuousOn_const
    (continuousOn_const.sub (continuousOn_id.pow 2)) fun x hx => ?_
  have := hmem x hx
  have hx2 : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
  exact hx2

theorem artanh_neg (t : ℝ) : artanh (-t) = -artanh t := by
  unfold artanh; rw [sub_neg_eq_add, ← sub_eq_add_neg]; ring

/-! ### The averaged column energy -/

/-- The `u`-averaged square `ρ(x) = ∫_{u>1} (u² + x²)/(4π²(u² − x²)²) du` of the exterior sinc columns. -/
def colDensity (x : ℝ) : ℝ := ∫ u in Ioi 1, (u ^ 2 + x ^ 2) / (4 * π ^ 2 * (u ^ 2 - x ^ 2) ^ 2)

theorem colDensity_eq {x : ℝ} (hx : |x| < 1) : colDensity x = 1 / (4 * π ^ 2) * (1 / (1 - x ^ 2)) := by
  rw [← integral_col hx, colDensity, ← MeasureTheory.integral_const_mul]
  congr 1; ext u
  have : (4 * π ^ 2) ≠ 0 := by positivity
  field_simp

/-- The averaged extension energy `S_∞(ℓ) = 2(∫_I ρ + 2∫_{½<|x|<ℓ} ρ)`: one carrier on `I`, two on the lips. -/
def avgEnergy (ℓ : ℝ) : ℝ :=
  2 * ((∫ x in (-(1 / 2))..(1 / 2), colDensity x) +
    2 * ((∫ x in (1 / 2)..ℓ, colDensity x) + ∫ x in -ℓ..(-(1 / 2)), colDensity x))

theorem integral_colDensity {α β : ℝ} (hα1 : -1 < α) (hα2 : α < 1) (hβ1 : -1 < β) (hβ2 : β < 1) :
    ∫ x in α..β, colDensity x = 1 / (4 * π ^ 2) * (artanh β - artanh α) := by
  have hmem : ∀ x ∈ uIcc α β, |x| < 1 := by
    intro x hx
    rcases mem_uIcc.1 hx with h | h
    · exact abs_lt.2 ⟨by linarith [h.1], by linarith [h.2]⟩
    · exact abs_lt.2 ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [integral_congr (g := fun x => 1 / (4 * π ^ 2) * (1 / (1 - x ^ 2))) fun x hx => colDensity_eq (hmem x hx),
    intervalIntegral.integral_const_mul, integral_inv_one_sub_sq hα1 hα2 hβ1 hβ2]

/-- **The closed form** `S_∞(ℓ) = (2 artanh ℓ − artanh ½)/π²` for `½ ≤ ℓ < 1`. -/
theorem avgEnergy_eq {ℓ : ℝ} (h1 : 1 / 2 ≤ ℓ) (h2 : ℓ < 1) :
    avgEnergy ℓ = (2 * artanh ℓ - artanh (1 / 2)) / π ^ 2 := by
  unfold avgEnergy
  rw [integral_colDensity (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    integral_colDensity (by norm_num) (by norm_num) (by linarith) h2,
    integral_colDensity (by linarith) (by linarith) (by norm_num) (by norm_num), artanh_neg, artanh_neg]
  have : π ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem artanh_half : artanh (1 / 2) = Real.log 3 / 2 := by
  unfold artanh
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

/-- **At the fixed ellipse** `ℓ = 3/5`: `S_∞ = log(16/3)/(2π²) = Θ₀/2`. -/
theorem avgEnergy_three_fifths : avgEnergy (3 / 5) = Cvs.Route.Visibility.VisibilityLandauTransition.thetaCons / 2 := by
  rw [avgEnergy_eq (by norm_num) (by norm_num), artanh_half, Cvs.Route.Visibility.VisibilityLandauTransition.thetaCons]
  have ha : artanh (3 / 5) = Real.log 2 := by
    unfold artanh
    rw [show (1 : ℝ) + 3 / 5 = 8 / 5 by norm_num, show (1 : ℝ) - 3 / 5 = 2 / 5 by norm_num,
      ← Real.log_div (by norm_num) (by norm_num), show (8 / 5 : ℝ) / (2 / 5) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast; ring
  rw [ha, Real.log_div (by norm_num) (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  have : π ^ 2 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- **At the turning point** `ℓ = 1/√3`: `S_∞ = log((7 + 4√3)/3)/(2π²) = Θ/2`. -/
theorem avgEnergy_turn : avgEnergy (1 / √3) = Cvs.Route.Visibility.VisibilityLandauTransition.thetaSharp / 2 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs : (1 : ℝ) < √3 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2 : √3 < 2 := by nlinarith [Real.sqrt_nonneg 3]
  have hl1 : 1 / 2 ≤ 1 / √3 := by rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  have hl2 : 1 / √3 < 1 := by rw [div_lt_one (by linarith)]; exact hs
  rw [avgEnergy_eq hl1 hl2, artanh_half, Cvs.Route.Visibility.VisibilityLandauTransition.thetaSharp]
  have hp : 0 < 1 + 1 / √3 := by positivity
  have hm : 0 < 1 - 1 / √3 := by linarith
  have ha : 2 * artanh (1 / √3) = Real.log (2 + √3) := by
    unfold artanh
    rw [mul_div_cancel₀ _ two_ne_zero, ← Real.log_div hp.ne' hm.ne']
    congr 1
    have : √3 - 1 ≠ 0 := by linarith
    field_simp
    nlinarith
  rw [ha, Real.log_div (by positivity) (by norm_num)]
  have e : (7 + 4 * √3) = (2 + √3) ^ 2 := by nlinarith
  rw [e, Real.log_pow]
  have : π ^ 2 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-! ### The Laplace kernel of the odd cross term -/

/-- `∫_{v>0} e^{−(u−t)v} dv = 1/(u − t)` for `t < u`. -/
theorem integral_laplace {t u : ℝ} (h : t < u) : ∫ v in Ioi 0, Real.exp (-(u - t) * v) = 1 / (u - t) := by
  rw [integral_exp_mul_Ioi (by linarith : -(u - t) < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  have : u - t ≠ 0 := by linarith
  field_simp

end Cvs.Prolate.Hardy.AveragedColumnEnergy

end
