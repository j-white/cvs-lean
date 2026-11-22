import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.Prolate.CosineTransformSecondOrder
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ModeEnergyArcsineLaw

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The endpoint mass of the rungs

`Y ∫_Y^∞ ψ_g² → (g(1) + g(−1))²/(2c²)` for `g ∈ C²[−1, 1]`, `Y arcsin(1/Y) → 1`, a uniform arcsine law at fixed `c`
forces `|L − a| ≤ b` at `Y = ∞`, and for `h₀, h₄, h₈`: `h_j(1)² / (c(1 − λ_j)) → 1`, with `c(1 − λ_j) > 0` eventually.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology

namespace Cvs.Prolate.RungEndpointMass
open Cvs.ZeroCounting

/-- `|∫_Y^∞ cos(2ct)/t²| ≤ 3/(2|c|Y²)`, by one integration by parts. -/
theorem abs_integral_cos_div_sq_le {c Y : ℝ} (hc : c ≠ 0) (hY : 0 < Y) :
    |∫ t in Ioi Y, cos (2 * c * t) / t ^ 2| ≤ 3 / (2 * |c| * Y ^ 2) := by
  have hc' : 0 < |c| := abs_pos.mpr hc
  have h2c : (2 * c) ≠ 0 := mul_ne_zero two_ne_zero hc
  have hpos : ∀ t ∈ Ioi Y, 0 < t := fun t ht => hY.trans ht
  have hu : ∀ t ∈ Ioi Y, HasDerivAt (fun t : ℝ => 1 / t ^ 2) (-2 / t ^ 3) t := fun t ht => by
    have ht0 : t ≠ 0 := (hpos t ht).ne'
    refine ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht0)).congr_deriv ?_
    norm_num; field_simp
  have hv : ∀ t ∈ Ioi Y, HasDerivAt (fun t => sin (2 * c * t) / (2 * c)) (cos (2 * c * t)) t := fun t _ => by
    refine ((((hasDerivAt_id t).const_mul (2 * c)).sin).div_const (2 * c)).congr_deriv ?_
    simp only [id, mul_one]; field_simp
  have hmeasIoi : ∀ {f : ℝ → ℝ}, ContinuousOn f (Ioi Y) → AEStronglyMeasurable f (volume.restrict (Ioi Y)) :=
    fun hf => hf.aestronglyMeasurable measurableSet_Ioi
  have hsq : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi Y) := Cvs.L2a.FullTailConvergence.integrableOn_one_div_sq hY
  have hcont_inv : ∀ n : ℕ, ContinuousOn (fun t : ℝ => 1 / t ^ n) (Ioi Y) := fun n =>
    continuousOn_const.div (continuous_pow n).continuousOn fun t ht => pow_ne_zero n (hpos t ht).ne'
  have huv' : IntegrableOn ((fun t : ℝ => 1 / t ^ 2) * fun t => cos (2 * c * t)) (Ioi Y) := by
    refine Integrable.mono' hsq (hmeasIoi ((hcont_inv 2).mul (by fun_prop : Continuous fun t => cos (2 * c * t)).continuousOn)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have := hpos t ht
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / t ^ 2)]
    exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)
  have hbound' : ∀ t ∈ Ioi Y, |-2 / t ^ 3 * (sin (2 * c * t) / (2 * c))| ≤ 1 / (|c| * Y) * (1 / t ^ 2) :=
    fun t ht => by
    have ht0 := hpos t ht
    have hYt : Y ≤ t := le_of_lt ht
    have hs := abs_sin_le_one (2 * c * t)
    rw [show -2 / t ^ 3 * (sin (2 * c * t) / (2 * c)) = -(sin (2 * c * t) * (1 / (c * t * t ^ 2))) by
      field_simp, abs_neg, abs_mul, abs_div, abs_one, abs_mul, abs_mul, abs_of_pos ht0,
      abs_of_pos (by positivity : 0 < t ^ 2)]
    calc |sin (2 * c * t)| * (1 / (|c| * t * t ^ 2)) ≤ 1 * (1 / (|c| * t * t ^ 2)) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
      _ ≤ 1 / (|c| * Y) * (1 / t ^ 2) := by
          rw [one_mul, div_mul_div_comm, one_mul]
          have hp : 0 < |c| * Y * t ^ 2 := mul_pos (mul_pos hc' hY) (pow_pos ht0 2)
          have hle : |c| * Y * t ^ 2 ≤ |c| * t * t ^ 2 := by gcongr
          exact one_div_le_one_div_of_le hp hle
  have hu'v : IntegrableOn ((fun t : ℝ => -2 / t ^ 3) * fun t => sin (2 * c * t) / (2 * c)) (Ioi Y) := by
    refine Integrable.mono' (hsq.const_mul (1 / (|c| * Y)))
      (hmeasIoi ((continuousOn_const.div (continuous_pow 3).continuousOn
        fun t ht => pow_ne_zero 3 (hpos t ht).ne').mul
          (by fun_prop : Continuous fun t => sin (2 * c * t) / (2 * c)).continuousOn)) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => by
      simpa only [Pi.mul_apply, Real.norm_eq_abs] using hbound' t ht)
  have hcontY : ContinuousAt ((fun t : ℝ => 1 / t ^ 2) * fun t => sin (2 * c * t) / (2 * c)) Y :=
    (continuousAt_const.div (continuous_pow 2).continuousAt (pow_ne_zero 2 hY.ne')).mul
      (by fun_prop : Continuous fun t => sin (2 * c * t) / (2 * c)).continuousAt
  have h_zero := hcontY.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi Y))
  have h_infty : Tendsto ((fun t : ℝ => 1 / t ^ 2) * fun t => sin (2 * c * t) / (2 * c)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => 1 / (2 * |c|) * (t ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop (two_ne_zero)).inv_tendsto_atTop.const_mul (1 / (2 * |c|))
    refine squeeze_zero_norm' ((eventually_gt_atTop 0).mono fun t ht => ?_) hlim
    have h2 : 0 < t ^ 2 := by positivity
    rw [Pi.mul_apply, Real.norm_eq_abs, show 1 / t ^ 2 * (sin (2 * c * t) / (2 * c)) =
      sin (2 * c * t) * (1 / (2 * c) * (t ^ 2)⁻¹) by field_simp, abs_mul, abs_mul, abs_div, abs_one, abs_mul,
      abs_two, abs_inv, abs_of_pos h2]
    exact mul_le_of_le_one_left (by positivity) (abs_sin_le_one _)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  have hlhs : ∫ t in Ioi Y, cos (2 * c * t) / t ^ 2 = ∫ t in Ioi Y, 1 / t ^ 2 * cos (2 * c * t) :=
    integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
  rw [hlhs, hibp]
  have h1 : |1 / Y ^ 2 * (sin (2 * c * Y) / (2 * c))| ≤ 1 / (2 * |c| * Y ^ 2) := by
    have h2 : 0 < Y ^ 2 := by positivity
    rw [show 1 / Y ^ 2 * (sin (2 * c * Y) / (2 * c)) =
      sin (2 * c * Y) * (1 / (2 * c * Y ^ 2)) by field_simp, abs_mul, abs_div, abs_one, abs_mul, abs_mul,
      abs_two, abs_of_pos h2]
    exact mul_le_of_le_one_left (by positivity) (abs_sin_le_one _)
  have h2 : |∫ t in Ioi Y, -2 / t ^ 3 * (sin (2 * c * t) / (2 * c))| ≤ 1 / (|c| * Y ^ 2) := by
    have := norm_integral_le_of_norm_le (hsq.const_mul (1 / (|c| * Y)))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs]; exact hbound' t ht))
    rw [integral_const_mul, Cvs.L2a.FullTailConvergence.integral_one_div_sq hY, Real.norm_eq_abs] at this
    calc _ ≤ 1 / (|c| * Y) * (1 / Y) := this
      _ = 1 / (|c| * Y ^ 2) := by field_simp
  simp only [Pi.mul_apply]
  calc |0 - 1 / Y ^ 2 * (sin (2 * c * Y) / (2 * c)) - ∫ t in Ioi Y, -2 / t ^ 3 * (sin (2 * c * t) / (2 * c))|
      ≤ |1 / Y ^ 2 * (sin (2 * c * Y) / (2 * c))| +
        |∫ t in Ioi Y, -2 / t ^ 3 * (sin (2 * c * t) / (2 * c))| := by
        rw [zero_sub, sub_eq_add_neg, ← abs_neg (1 / Y ^ 2 * (sin (2 * c * Y) / (2 * c)))]
        exact (abs_add_le _ _).trans (le_of_eq (by simp only [abs_neg]))
    _ ≤ 1 / (2 * |c| * Y ^ 2) + 1 / (|c| * Y ^ 2) := add_le_add h1 h2
    _ = 3 / (2 * |c| * Y ^ 2) := by field_simp; ring

/-- A continuous `f` with `|f| ≤ 1` has `f(t)/t²` integrable on `(Y, ∞)`, `Y > 0`. -/
theorem integrableOn_div_sq {f : ℝ → ℝ} {Y : ℝ} (hY : 0 < Y) (hf : Continuous f) (hf1 : ∀ t, |f t| ≤ 1) :
    IntegrableOn (fun t => f t / t ^ 2) (Ioi Y) := by
  refine Integrable.mono' (Cvs.L2a.FullTailConvergence.integrableOn_one_div_sq hY)
    ((hf.continuousOn.div (continuous_pow 2).continuousOn fun t ht =>
      pow_ne_zero 2 (hY.trans ht).ne').aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have h2 : 0 < t ^ 2 := pow_pos (hY.trans ht) 2
  rw [Real.norm_eq_abs, abs_div, abs_of_pos h2]
  exact div_le_div_of_nonneg_right (hf1 t) h2.le

/-- **The `sin²` average**: `Y ∫_Y^∞ sin²(ct)/t² → ½`. -/
theorem tendsto_mul_integral_sin_sq {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun Y : ℝ => Y * ∫ t in Ioi Y, sin (c * t) ^ 2 / t ^ 2) atTop (𝓝 (1 / 2)) := by
  have hc' : 0 < |c| := abs_pos.mpr hc
  have heq : ∀ Y : ℝ, 0 < Y → Y * ∫ t in Ioi Y, sin (c * t) ^ 2 / t ^ 2
      = 1 / 2 - Y / 2 * ∫ t in Ioi Y, cos (2 * c * t) / t ^ 2 := fun Y hY => by
    have hi1 := Cvs.L2a.FullTailConvergence.integrableOn_one_div_sq hY
    have hi2 := integrableOn_div_sq hY (by fun_prop : Continuous fun t => cos (2 * c * t))
      fun t => abs_cos_le_one _
    have e : ∫ t in Ioi Y, sin (c * t) ^ 2 / t ^ 2
        = ∫ t in Ioi Y, (1 / 2 * (1 / t ^ 2) - 1 / 2 * (cos (2 * c * t) / t ^ 2)) :=
      integral_congr_ae (Eventually.of_forall fun t => by
        simp only [sin_sq_eq_half_sub, show 2 * (c * t) = 2 * c * t by ring]; ring)
    rw [e, integral_sub (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
      Cvs.L2a.FullTailConvergence.integral_one_div_sq hY]
    field_simp
  have hR : Tendsto (fun Y : ℝ => Y / 2 * ∫ t in Ioi Y, cos (2 * c * t) / t ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun Y : ℝ => 3 / (4 * |c|) * Y⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (3 / (4 * |c|))
    refine squeeze_zero_norm' ((eventually_gt_atTop 0).mono fun Y hY => ?_) hlim
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < Y / 2)]
    calc Y / 2 * |∫ t in Ioi Y, cos (2 * c * t) / t ^ 2| ≤ Y / 2 * (3 / (2 * |c| * Y ^ 2)) :=
          mul_le_mul_of_nonneg_left (abs_integral_cos_div_sq_le hc hY) (by positivity)
      _ = 3 / (4 * |c|) * Y⁻¹ := by field_simp; ring
  have := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hR
  rw [sub_zero] at this
  exact this.congr' ((eventually_gt_atTop 0).mono fun Y hY => (heq Y hY).symm)

/-- **`Y arcsin(1/Y) → 1`**, the slope of `arcsin` at `0`. -/
theorem tendsto_mul_arcsin_inv : Tendsto (fun Y : ℝ => Y * arcsin (1 / Y)) atTop (𝓝 1) := by
  have hd : HasDerivAt arcsin 1 0 := by
    simpa using Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1) (by norm_num : (0 : ℝ) ≠ 1)
  have h := hd.tendsto_slope_zero_right.comp tendsto_inv_atTop_nhdsGT_zero
  refine h.congr' ((eventually_gt_atTop 0).mono fun Y hY => ?_)
  simp [Function.comp, arcsin_zero, smul_eq_mul, one_div]

/-- **Matching at `Y = ∞`**: a law `|T(Y) − a arcsin(1/Y)| ≤ b/Y` for all `Y ≥ 1`, together with
`Y T(Y) → L`, forces `|L − a| ≤ b`. -/
theorem abs_sub_le_of_arcsin_law {T : ℝ → ℝ} {a b L : ℝ}
    (hlaw : ∀ Y : ℝ, 1 ≤ Y → |T Y - a * arcsin (1 / Y)| ≤ b / Y)
    (hfar : Tendsto (fun Y => Y * T Y) atTop (𝓝 L)) : |L - a| ≤ b := by
  have ht : Tendsto (fun Y => |Y * T Y - a * (Y * arcsin (1 / Y))|) atTop (𝓝 |L - a * 1|) :=
    (hfar.sub (tendsto_mul_arcsin_inv.const_mul a)).abs
  rw [mul_one] at ht
  refine le_of_tendsto ht ((eventually_ge_atTop 1).mono fun Y hY1 => ?_)
  have hY : 0 < Y := one_pos.trans_le hY1
  calc |Y * T Y - a * (Y * arcsin (1 / Y))| = Y * |T Y - a * arcsin (1 / Y)| := by
        rw [← abs_of_pos hY, ← abs_mul, abs_of_pos hY]; ring_nf
    _ ≤ Y * (b / Y) := mul_le_mul_of_nonneg_left (hlaw Y hY1) hY.le
    _ = b := by field_simp

open Cvs.L2a.AngularProlateTailPositive in
/-- **The far field of the window**: for `g ∈ C²[−1, 1]` and `c > 0`,
`Y ∫_Y^∞ ψ_g² → (g(1) + g(−1))²/(2c²)`. -/
theorem tendsto_mul_integral_Ioi_psi_sq {c : ℝ} {g g₁ g₂ : ℝ → ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) :
    Tendsto (fun Y => Y * ∫ t in Ioi Y, psi c g t ^ 2) atTop (𝓝 ((g 1 + g (-1)) ^ 2 / (2 * c ^ 2))) := by
  set A := g 1 + g (-1)
  set B := |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|
  have hB : 0 ≤ B := add_nonneg (abs_nonneg _) (intervalIntegral.integral_nonneg (by norm_num)
    fun _ _ => abs_nonneg _)
  set K := B / c ^ 2 * (2 * |A| / c + B / c ^ 2)
  have hK : 0 ≤ K := by positivity
  have hψc : Continuous (psi c g) :=
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  -- the main term and the remainder, pointwise for `t ≥ 1`
  set sm : ℝ → ℝ := fun t => A * sin (c * t) / (c * t)
  have hsm_sq : ∀ t, 0 < t → sm t ^ 2 = A ^ 2 / c ^ 2 * (sin (c * t) ^ 2 / t ^ 2) := fun t ht => by
    simp only [sm]; field_simp
  have hrem : ∀ t, 1 ≤ t → |psi c g t ^ 2 - sm t ^ 2| ≤ K / t ^ 3 := fun t ht => by
    have ht0 : 0 < t := one_pos.trans_le ht
    have hct : 0 < c * t := mul_pos hc ht0
    have he : |psi c g t - sm t| ≤ B / (c * t) ^ 2 :=
      Cvs.Prolate.CosineTransformSecondOrder.psi_sub_le hg hg₁ hg₂c hct.ne'
    have hs : |sm t| ≤ |A| / (c * t) := by
      simp only [sm]
      rw [abs_div, abs_mul, abs_of_pos hct]
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)) hct.le
    have hfac : psi c g t ^ 2 - sm t ^ 2 = (psi c g t - sm t) * (2 * sm t + (psi c g t - sm t)) := by ring
    have h1t : 1 / t ≤ 1 := by rw [div_le_one ht0]; exact ht
    have h2 : |2 * sm t + (psi c g t - sm t)| ≤ (2 * |A| / c + B / c ^ 2) / t := by
      calc |2 * sm t + (psi c g t - sm t)| ≤ 2 * |sm t| + |psi c g t - sm t| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_two]
        _ ≤ 2 * (|A| / (c * t)) + B / (c * t) ^ 2 := by gcongr
        _ = (2 * |A| / c + B / c ^ 2 * (1 / t)) / t := by field_simp
        _ ≤ (2 * |A| / c + B / c ^ 2 * 1) / t := by gcongr
        _ = (2 * |A| / c + B / c ^ 2) / t := by rw [mul_one]
    rw [hfac, abs_mul]
    calc |psi c g t - sm t| * |2 * sm t + (psi c g t - sm t)|
        ≤ B / (c * t) ^ 2 * ((2 * |A| / c + B / c ^ 2) / t) :=
          mul_le_mul he h2 (abs_nonneg _) (by positivity)
      _ = K / t ^ 3 := by simp only [K]; field_simp
  -- integrability on `(Y, ∞)`, `Y ≥ 1`
  have hrem_int : ∀ Y : ℝ, 1 ≤ Y → IntegrableOn (fun t => psi c g t ^ 2 - sm t ^ 2) (Ioi Y) := fun Y hY => by
    have hY0 : 0 < Y := one_pos.trans_le hY
    refine Integrable.mono' ((Cvs.L2a.FullTailConvergence.integrableOn_one_div_sq hY0).const_mul K) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine (hψc.pow 2).continuousOn.sub (ContinuousOn.pow ?_ 2)
      exact ((continuous_const.mul (by fun_prop : Continuous fun t => sin (c * t))).continuousOn).div
        (by fun_prop : Continuous fun t => c * t).continuousOn fun t ht => (mul_pos hc (hY0.trans ht)).ne'
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht1 : 1 ≤ t := hY.trans (le_of_lt ht)
      have ht0 : 0 < t := one_pos.trans_le ht1
      rw [Real.norm_eq_abs]
      refine (hrem t ht1).trans ?_
      rw [show K / t ^ 3 = K * (1 / t ^ 2) * (1 / t) by field_simp]
      exact mul_le_of_le_one_right (by positivity) (by rw [div_le_one ht0]; exact ht1)
  have hsin_int : ∀ Y : ℝ, 0 < Y → IntegrableOn (fun t => sin (c * t) ^ 2 / t ^ 2) (Ioi Y) := fun Y hY =>
    integrableOn_div_sq hY (by fun_prop) fun t => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sin_sq_le_one _
  -- the decomposition
  have hdec : ∀ Y : ℝ, 1 ≤ Y → Y * ∫ t in Ioi Y, psi c g t ^ 2
      = A ^ 2 / c ^ 2 * (Y * ∫ t in Ioi Y, sin (c * t) ^ 2 / t ^ 2)
        + Y * ∫ t in Ioi Y, (psi c g t ^ 2 - sm t ^ 2) := fun Y hY => by
    have hY0 : 0 < Y := one_pos.trans_le hY
    have hsplit : ∫ t in Ioi Y, psi c g t ^ 2
        = ∫ t in Ioi Y, (A ^ 2 / c ^ 2 * (sin (c * t) ^ 2 / t ^ 2) + (psi c g t ^ 2 - sm t ^ 2)) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        rw [← hsm_sq t (hY0.trans ht)]; ring
    rw [hsplit, integral_add ((hsin_int Y hY0).const_mul _) (hrem_int Y hY), integral_const_mul]
    ring
  have hR : Tendsto (fun Y => Y * ∫ t in Ioi Y, (psi c g t ^ 2 - sm t ^ 2)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun Y : ℝ => K * Y⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul K
    refine squeeze_zero_norm' ((eventually_ge_atTop 1).mono fun Y hY => ?_) hlim
    have hY0 : 0 < Y := one_pos.trans_le hY
    have hb : ∀ t ∈ Ioi Y, ‖psi c g t ^ 2 - sm t ^ 2‖ ≤ K / Y * (1 / t ^ 2) := fun t ht => by
      have ht1 : 1 ≤ t := hY.trans (le_of_lt ht)
      have ht0 : 0 < t := one_pos.trans_le ht1
      rw [Real.norm_eq_abs]
      refine (hrem t ht1).trans ?_
      rw [show K / t ^ 3 = K * (1 / t ^ 2) * (1 / t) by field_simp,
        show K / Y * (1 / t ^ 2) = K * (1 / t ^ 2) * (1 / Y) by ring]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hY0 (le_of_lt ht)) (by positivity)
    have hI := norm_integral_le_of_norm_le
      ((Cvs.L2a.FullTailConvergence.integrableOn_one_div_sq hY0).const_mul (K / Y))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hb))
    rw [integral_const_mul, Cvs.L2a.FullTailConvergence.integral_one_div_sq hY0] at hI
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hY0]
    calc Y * ‖∫ t in Ioi Y, (psi c g t ^ 2 - sm t ^ 2)‖ ≤ Y * (K / Y * (1 / Y)) :=
          mul_le_mul_of_nonneg_left hI hY0.le
      _ = K * Y⁻¹ := by field_simp
  have hmain := ((tendsto_mul_integral_sin_sq hc.ne').const_mul (A ^ 2 / c ^ 2)).add hR
  rw [add_zero, show A ^ 2 / c ^ 2 * (1 / 2) = A ^ 2 / (2 * c ^ 2) by field_simp] at hmain
  exact hmain.congr' ((eventually_ge_atTop 1).mono fun Y hY => (hdec Y hY).symm)

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex in
/-- **The endpoint mass of `h₀`, `h₄`, `h₈`**: for every `η > 0`, eventually
`|h_j(1)² − c(1 − λ_j)| ≤ η c(1 − λ_j)`. -/
theorem abs_rung_one_sq_sub_le {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℝ in atTop, |rung c j 1 ^ 2 - c * (1 - lamR c j)| ≤ η * (c * (1 - lamR c j)) := by
  obtain ⟨K, hK⟩ := Cvs.Prolate.ModeEnergyArcsineLaw.hlev_even hj
  have hη' : 0 < 2 * η / π := by positivity
  filter_upwards [Cvs.Prolate.ModeEnergyArcsineLaw.arcsine_law_even hj hη', hK, eventually_gt_atTop 0]
    with c hlaw hlev hc
  obtain ⟨hg, hg₁, hg₂c, -, heven, -⟩ := rung_spec hlev.1
  have hfar := tendsto_mul_integral_Ioi_psi_sq hc hg hg₁ hg₂c
  rw [heven 1 ⟨by norm_num, le_rfl⟩] at hfar
  have hend := abs_sub_le_of_arcsin_law hlaw hfar
  have e : rung c j 1 ^ 2 - c * (1 - lamR c j)
      = c ^ 2 / 2 * ((rung c j 1 + rung c j 1) ^ 2 / (2 * c ^ 2) - 2 / c * (1 - lamR c j)) := by
    field_simp; ring
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < c ^ 2 / 2)]
  calc c ^ 2 / 2 * |(rung c j 1 + rung c j 1) ^ 2 / (2 * c ^ 2) - 2 / c * (1 - lamR c j)|
      ≤ c ^ 2 / 2 * (2 * η / π * (π / c * (1 - lamR c j))) :=
        mul_le_mul_of_nonneg_left hend (by positivity)
    _ = η * (c * (1 - lamR c j)) := by field_simp

open Cvs.Prolate.EvenRungsByIndex in
/-- **`c(1 − λ_j) > 0` eventually** for `h₀`, `h₄`, `h₈`, from `h_j(1) ≠ 0` and the endpoint mass. -/
theorem eventually_mul_one_sub_lamR_pos {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) :
    ∀ᶠ c : ℝ in atTop, 0 < c * (1 - lamR c j) := by
  obtain ⟨K, hK⟩ := Cvs.Prolate.ModeEnergyArcsineLaw.hlev_even hj
  filter_upwards [abs_rung_one_sq_sub_le hj one_pos, hK] with c h hlev
  have h1 : 0 < rung c j 1 ^ 2 := by
    have := rung_one_ne_zero hlev.1
    positivity
  have := (abs_le.mp h).2
  linarith

end Cvs.Prolate.RungEndpointMass

end
