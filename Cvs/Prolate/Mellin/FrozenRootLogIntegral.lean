import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Cvs.Prolate.Mellin.FrozenRiccatiRoot

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The real part of the half-line integral of the frozen root's logarithm vanishes

`F(q) = log σ(q^{−2})` is analytic for `|q| > 3c`, `|F(q)| ≤ 6c²/|q|²` for `|q| ≥ 4c`, and `F(−q̄) = conj F(q)`.
Cauchy on the rectangles `[−X, X] × [−T, −g]` and `|F| ≤ 6c²/|q|²` give `∫_ℝ F(u − ig) du = 0` for `g ≥ 4c`;
the reflection `u ↦ −u` then gives `Re ∫_0^∞ F(u − ig) du = 0`.
-/

noncomputable section

open Real Set MeasureTheory Complex Filter Topology intervalIntegral
open scoped Interval
open Cvs.Prolate.Mellin.FrozenRiccatiRoot (hh norm_hh_le differentiableAt_hh hh_conj)

namespace Cvs.Prolate.Mellin.FrozenRootLogIntegral

/-- `F(q) = log σ(q^{−2})`. -/
def Fq (χ c : ℝ) (q : ℂ) : ℂ := hh χ c ((q ^ 2)⁻¹)

/-- `F` on the horizontal line `Im q = −T`. -/
def lineF (χ c T : ℝ) (u : ℝ) : ℂ := Fq χ c ((u : ℂ) + ((-T : ℝ) : ℂ) * I)

theorem c_sq_norm_inv (c : ℝ) (q : ℂ) : c ^ 2 * ‖(q ^ 2)⁻¹‖ = c ^ 2 / ‖q‖ ^ 2 := by
  rw [norm_inv, norm_pow, div_eq_mul_inv]

/-- `|F(q)| ≤ 6c²/|q|²` for `|q| ≥ 4c`, `c > 0`. -/
theorem norm_Fq_le {χ c : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) {q : ℂ} (hq : 4 * c ≤ ‖q‖) :
    ‖Fq χ c q‖ ≤ 6 * c ^ 2 / ‖q‖ ^ 2 := by
  have hq0 : 0 < ‖q‖ := by linarith
  have hw : c ^ 2 * ‖(q ^ 2)⁻¹‖ ≤ 1 / 8 := by
    rw [c_sq_norm_inv, div_le_iff₀ (by positivity)]; nlinarith
  have := norm_hh_le hχ hw
  rw [c_sq_norm_inv] at this
  unfold Fq; linarith [show 6 * (c ^ 2 / ‖q‖ ^ 2) = 6 * c ^ 2 / ‖q‖ ^ 2 by ring]

/-- `F` is analytic at every `q` with `|q| > 3c`. -/
theorem differentiableAt_Fq {χ c : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) {q : ℂ} (hq : 3 * c < ‖q‖) :
    DifferentiableAt ℂ (Fq χ c) q := by
  have hq0 : q ≠ 0 := fun h => by rw [h, norm_zero] at hq; linarith
  have hw : c ^ 2 * ‖(q ^ 2)⁻¹‖ < 1 / 8 := by
    rw [c_sq_norm_inv, div_lt_iff₀ (by positivity)]; nlinarith
  have hinv : DifferentiableAt ℂ (fun q : ℂ => (q ^ 2)⁻¹) q :=
    (differentiableAt_pow 2).inv (pow_ne_zero 2 hq0)
  exact DifferentiableAt.comp (f := fun q : ℂ => (q ^ 2)⁻¹) q (differentiableAt_hh hχ hw) hinv

/-- `|u − iT|² = u² + T²`. -/
theorem norm_line (u T : ℝ) : ‖(u : ℂ) + ((-T : ℝ) : ℂ) * I‖ ^ 2 = u ^ 2 + T ^ 2 := by
  rw [Complex.sq_norm, normSq_add_mul_I]; ring

/-- `T ≤ |u − iT|`. -/
theorem le_norm_line {u T : ℝ} : T ≤ ‖(u : ℂ) + ((-T : ℝ) : ℂ) * I‖ := by
  have h := norm_line u T
  have h0 := norm_nonneg ((u : ℂ) + ((-T : ℝ) : ℂ) * I)
  nlinarith [sq_nonneg u]

/-- **The reflection**: `F(−u − iT) = conj F(u − iT)`. -/
theorem lineF_neg {χ c T : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) (hT : 4 * c ≤ T) (u : ℝ) :
    lineF χ c T (-u) = (starRingEnd ℂ) (lineF χ c T u) := by
  have hT0 : 0 ≤ T := by linarith
  set q := (u : ℂ) + ((-T : ℝ) : ℂ) * I with hqd
  have hq : 4 * c ≤ ‖q‖ := hT.trans le_norm_line
  have hq0 : 0 < ‖q‖ := by linarith
  have hw : c ^ 2 * ‖(q ^ 2)⁻¹‖ < 1 / 8 := by
    rw [c_sq_norm_inv, div_lt_iff₀ (by positivity)]; nlinarith
  have e : (((-u : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ^ 2 = (starRingEnd ℂ) (q ^ 2) := by
    rw [hqd, map_pow, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  unfold lineF Fq
  rw [e, ← map_inv₀, hh_conj hχ hw]

/-- The line function is continuous for `T ≥ 4c`. -/
theorem continuous_lineF {χ c T : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) (hT : 4 * c ≤ T) :
    Continuous (lineF χ c T) := by
  have hT0 : 0 ≤ T := by linarith
  refine continuous_iff_continuousAt.2 fun u => ?_
  have hq : 3 * c < ‖(u : ℂ) + ((-T : ℝ) : ℂ) * I‖ := by linarith [le_norm_line (u := u) (T := T)]
  exact (differentiableAt_Fq hc hχ hq).continuousAt.comp (f := fun u : ℝ => (u : ℂ) + ((-T : ℝ) : ℂ) * I)
    (by fun_prop)

/-- `|F(u − iT)| ≤ 6c²/(u² + T²)` for `T ≥ 4c`. -/
theorem norm_lineF_le {χ c T : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) (hT : 4 * c ≤ T) (u : ℝ) :
    ‖lineF χ c T u‖ ≤ 6 * c ^ 2 / (u ^ 2 + T ^ 2) := by
  have hT0 : 0 ≤ T := by linarith
  have := norm_Fq_le hc hχ (hT.trans (le_norm_line (u := u) (T := T)))
  rw [norm_line] at this
  exact this

/-- The majorant `6c²/(u² + T²)` is integrable with integral `6πc²/T`. -/
theorem integral_majorant {c T : ℝ} (hT : 0 < T) :
    Integrable (fun u : ℝ => 6 * c ^ 2 / (u ^ 2 + T ^ 2))
      ∧ ∫ u : ℝ, 6 * c ^ 2 / (u ^ 2 + T ^ 2) = 6 * π * c ^ 2 / T := by
  have e : (fun u : ℝ => 6 * c ^ 2 / (u ^ 2 + T ^ 2)) = fun u => (6 * c ^ 2 / T ^ 2) * (1 + (u / T) ^ 2)⁻¹ := by
    funext u; field_simp; ring
  rw [e]
  refine ⟨(integrable_inv_one_add_sq.comp_div hT.ne').const_mul _, ?_⟩
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) T,
    integral_univ_inv_one_add_sq, abs_of_pos hT, smul_eq_mul]
  field_simp

theorem integrable_lineF {χ c T : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) (hT : 4 * c ≤ T) :
    Integrable (lineF χ c T) :=
  (integral_majorant (c := c) (by linarith)).1.mono' (continuous_lineF hc hχ hT).aestronglyMeasurable
    (Eventually.of_forall fun u => norm_lineF_le hc hχ hT u)

/-- **The line integral does not depend on the height**: `∫_ℝ F(u − iT) = ∫_ℝ F(u − ig)` for `T ≥ g ≥ 4c`. -/
theorem integral_lineF_eq {χ c g T : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) (hg : 4 * c ≤ g) (hgT : g ≤ T) :
    ∫ u, lineF χ c T u = ∫ u, lineF χ c g u := by
  have hT : 4 * c ≤ T := hg.trans hgT
  have hg0 : 0 < g := by linarith
  -- the rectangle identity at width `X`
  have hrect : ∀ X : ℝ, 0 < X → ‖(∫ u in (-X)..X, lineF χ c T u) - ∫ u in (-X)..X, lineF χ c g u‖
      ≤ 2 * (6 * c ^ 2 / X ^ 2 * (T - g)) := by
    intro X hX
    have hdiff : DifferentiableOn ℂ (Fq χ c) ([[(⟨-X, -T⟩ : ℂ).re, (⟨X, -g⟩ : ℂ).re]] ×ℂ
        [[(⟨-X, -T⟩ : ℂ).im, (⟨X, -g⟩ : ℂ).im]]) := by
      intro q hq
      rw [mem_reProdIm] at hq
      have him : q.im ≤ -g := by
        have := hq.2; simp only at this; rw [uIcc_of_le (by linarith)] at this; exact this.2
      have : g ≤ ‖q‖ := by
        have := Complex.abs_im_le_norm q; rw [abs_of_neg (by linarith)] at this; linarith
      exact (differentiableAt_Fq hc hχ (by linarith)).differentiableWithinAt
    have h := integral_boundary_rect_eq_zero_of_differentiableOn (Fq χ c) ⟨-X, -T⟩ ⟨X, -g⟩ hdiff
    simp only at h
    have hv : ∀ x : ℝ, |x| = X → ‖∫ y in (-T)..(-g), Fq χ c (x + y * I)‖ ≤ 6 * c ^ 2 / X ^ 2 * (T - g) := by
      intro x hx
      have hb : ∀ y ∈ Ι (-T) (-g), ‖Fq χ c (x + y * I)‖ ≤ 6 * c ^ 2 / X ^ 2 := by
        intro y hy
        rw [uIoc_of_le (by linarith)] at hy
        have hy1 : g ≤ |y| := by rw [abs_of_neg (by linarith [hy.2])]; linarith [hy.2]
        have hn : ‖(x : ℂ) + y * I‖ ^ 2 = x ^ 2 + y ^ 2 := by rw [Complex.sq_norm, normSq_add_mul_I]
        have hq4 : 4 * c ≤ ‖(x : ℂ) + y * I‖ := by
          have : |y| ≤ ‖(x : ℂ) + y * I‖ := by
            have := Complex.abs_im_le_norm ((x : ℂ) + y * I); simpa using this
          linarith
        refine (norm_Fq_le hc hχ hq4).trans ?_
        rw [hn]
        have hx2 : X ^ 2 = x ^ 2 := by rw [← hx, sq_abs]
        gcongr
        nlinarith [sq_nonneg y]
      have := norm_integral_le_of_norm_le_const hb
      rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ -g - -T), show -g - -T = T - g by ring] at this
    have hX : |X| = X := abs_of_pos hX
    have hXn : |-X| = X := by rw [abs_neg, hX]
    have e1 : (∫ u in (-X)..X, lineF χ c T u) = ∫ x in (-X)..X, Fq χ c (↑x + ↑(-T) * I) := rfl
    have e2 : (∫ u in (-X)..X, lineF χ c g u) = ∫ x in (-X)..X, Fq χ c (↑x + ↑(-g) * I) := rfl
    rw [e1, e2]
    have h3 := hv X hX
    have h4 := hv (-X) hXn
    have : (∫ x in (-X)..X, Fq χ c (↑x + ↑(-T) * I)) - ∫ x in (-X)..X, Fq χ c (↑x + ↑(-g) * I)
        = -(I • ∫ y in (-T)..(-g), Fq χ c (↑X + ↑y * I)) + I • ∫ y in (-T)..(-g), Fq χ c (↑(-X) + ↑y * I) := by
      linear_combination h
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul]
    push_cast at h4 ⊢
    linarith
  -- let the width go to infinity
  have hlim : Tendsto (fun X : ℝ => (∫ u in (-X)..X, lineF χ c T u) - ∫ u in (-X)..X, lineF χ c g u) atTop
      (𝓝 ((∫ u, lineF χ c T u) - ∫ u, lineF χ c g u)) :=
    (intervalIntegral_tendsto_integral (integrable_lineF hc hχ hT) tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral (integrable_lineF hc hχ hg) tendsto_neg_atTop_atBot tendsto_id)
  have hb0 : Tendsto (fun X : ℝ => 2 * (6 * c ^ 2 / X ^ 2 * (T - g))) atTop (𝓝 0) := by
    have : Tendsto (fun X : ℝ => X ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have h2 := (this.const_div_atTop (6 * c ^ 2)).mul_const (T - g)
    simpa using h2.const_mul 2
  have hn := hlim.norm
  have hle : ‖(∫ u, lineF χ c T u) - ∫ u, lineF χ c g u‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hn hb0 (eventually_gt_atTop 0 |>.mono fun X hX => hrect X hX)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- **The line integral vanishes**: `∫_ℝ F(u − ig) du = 0` for `g ≥ 4c`. -/
theorem integral_lineF_eq_zero {χ c g : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) (hg : 4 * c ≤ g) :
    ∫ u, lineF χ c g u = 0 := by
  have hg0 : 0 < g := by linarith
  have hbound : ∀ T, g ≤ T → ‖∫ u, lineF χ c g u‖ ≤ 6 * π * c ^ 2 / T := fun T hT => by
    rw [← integral_lineF_eq hc hχ hg hT]
    have hT0 : 0 < T := by linarith
    rw [← (integral_majorant (c := c) hT0).2]
    exact norm_integral_le_of_norm_le (integral_majorant hT0).1
      (Eventually.of_forall fun u => norm_lineF_le hc hχ (hg.trans hT) u)
  have ht : Tendsto (fun T : ℝ => 6 * π * c ^ 2 / T) atTop (𝓝 0) := tendsto_id.const_div_atTop _
  have hle : ‖∫ u, lineF χ c g u‖ ≤ 0 :=
    ge_of_tendsto ht (eventually_ge_atTop g |>.mono fun T hT => hbound T hT)
  exact norm_le_zero_iff.1 hle

/-- **The real part of the half-line integral vanishes**: `Re ∫_0^∞ F(u − ig) du = 0` for `g ≥ 4c`. -/
theorem re_integral_Ioi_lineF {χ c g : ℝ} (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) (hg : 4 * c ≤ g) :
    (∫ u in Ioi (0 : ℝ), lineF χ c g u).re = 0 := by
  have hI := integrable_lineF hc hχ hg
  have hsplit := integral_Iic_add_Ioi (b := 0) hI.integrableOn hI.integrableOn
  rw [integral_lineF_eq_zero hc hχ hg] at hsplit
  have hneg : ∫ u in Iic (0 : ℝ), lineF χ c g u = (starRingEnd ℂ) (∫ u in Ioi (0 : ℝ), lineF χ c g u) := by
    rw [← integral_conj]
    have := integral_comp_neg_Ioi (0 : ℝ) (lineF χ c g)
    rw [neg_zero] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact lineF_neg hc hχ hg u
  rw [hneg] at hsplit
  have := congrArg Complex.re hsplit
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
  linarith

end Cvs.Prolate.Mellin.FrozenRootLogIntegral

end
