import Mathlib
import Cvs.L2a.FullTailConvergence
import Cvs.Upstream.HolomorphicParamIntegralSine
import Cvs.Upstream.TrigMellinIntegralsContinuation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The per-mode exterior terms `M_k` and their bounds

For a `C¹` function `ψ` on `[1, ∞)` with `ψ, ψ′ ∈ L²(1, ∞)`, put `𝒜(ω) = 2∫₁^∞ ψ(t) sin(ωt)/t dt`,
`W(y₀, s) = ∫₁^∞ (ψ(t)/t) J(y₀t, s) dt` and `M_k(s) = 𝒜(kc)/(kc) + (2(s − 1)/(kc))W(kc, s)`. Then
`|𝒜| ≤ 2P`, `|𝒜(ω)| ≤ 2(|ψ(1)| + D + P/√3)/ω`, `‖W(y₀, s)‖ ≤ P/(√3(y₀ − |Im s| − 1))`, `W(y₀, ·)` is holomorphic on
`Re s < 3, |Im s| < y₀ − 2`, and `−2∫₁^∞ ψ(t)C(kct, s) dt = M_k(s)` for `Re s < 0` (`P`, `D` the `L²(1, ∞)` norms).
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Complex
open scoped ComplexConjugate
open Cvs.Upstream.TrigMellinIntegralsContinuation (cosM sinM)
open Cvs.Upstream.HolomorphicParamIntegralSine (jRot)

namespace Cvs.Prolate.Mellin.ModeExteriorTerms

variable {ψ ψ' : ℝ → ℝ}

/-- `𝒜(ω) = 2∫₁^∞ ψ(t) sin(ωt)/t dt`. -/
def aCoef (ψ : ℝ → ℝ) (ω : ℝ) : ℝ := 2 * ∫ t in Ioi (1 : ℝ), ψ t * (Real.sin (ω * t) / t)

/-- `W(y₀, s) = ∫₁^∞ (ψ(t)/t) J(y₀t, s) dt`. -/
def wInt (ψ : ℝ → ℝ) (y₀ : ℝ) (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), ((ψ t / t : ℝ) : ℂ) * jRot (y₀ * t) s

/-- `M_k(s) = 𝒜(kc)/(kc) + (2(s − 1)/(kc))W(kc, s)`. -/
def mTerm (ψ : ℝ → ℝ) (c : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ((aCoef ψ (k * c) / (k * c) : ℝ) : ℂ) + 2 * (s - 1) / (k * c) * wInt ψ (k * c) s

/-! ### Square integrability on `(1, ∞)` -/

theorem rpow_neg_two {t : ℝ} (ht : 0 < t) : t ^ (-2 : ℝ) = (1 / t) ^ 2 := by
  rw [Real.rpow_neg ht.le, Real.rpow_two, one_div, inv_pow]

theorem rpow_neg_four {t : ℝ} (ht : 0 < t) : t ^ (-4 : ℝ) = (1 / t ^ 2) ^ 2 := by
  rw [Real.rpow_neg ht.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div, inv_pow, ← pow_mul]

theorem integrableOn_inv_sq : IntegrableOn (fun t : ℝ => (1 / t) ^ 2) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).congr_fun
    (fun t ht => rpow_neg_two (lt_trans one_pos ht)) measurableSet_Ioi

theorem integral_inv_sq : ∫ t in Ioi (1 : ℝ), (1 / t) ^ 2 = 1 := by
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t ht => rpow_neg_two (lt_trans one_pos ht)),
    integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

theorem integrableOn_inv_pow_four : IntegrableOn (fun t : ℝ => (1 / t ^ 2) ^ 2) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) one_pos).congr_fun
    (fun t ht => rpow_neg_four (lt_trans one_pos ht)) measurableSet_Ioi

theorem integral_inv_pow_four : ∫ t in Ioi (1 : ℝ), (1 / t ^ 2) ^ 2 = 1 / 3 := by
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t ht => rpow_neg_four (lt_trans one_pos ht)),
    integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

/-- `|∫ f w| ≤ √(∫ f²)√(∫ w²)` when `f² ` and `w²` are integrable on `(1, ∞)`. -/
theorem abs_integral_mul_le {f w : ℝ → ℝ} (hfm : Measurable f) (hwm : Measurable w)
    (hf : IntegrableOn (fun t => f t ^ 2) (Ioi 1)) (hw : IntegrableOn (fun t => w t ^ 2) (Ioi 1)) :
    IntegrableOn (fun t => f t * w t) (Ioi 1)
      ∧ |∫ t in Ioi (1 : ℝ), f t * w t| ≤ √(∫ t in Ioi (1 : ℝ), f t ^ 2) * √(∫ t in Ioi (1 : ℝ), w t ^ 2) := by
  have hdom : IntegrableOn (fun t => (f t ^ 2 + w t ^ 2) / 2) (Ioi 1) := (hf.add hw).div_const 2
  have hfw : IntegrableOn (fun t => f t * w t) (Ioi 1) := by
    refine hdom.mono' ((hfm.mul hwm).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|f t| - |w t|), sq_abs (f t), sq_abs (w t)]
  exact ⟨hfw, Cvs.L2a.FullTailConvergence.abs_setIntegral_mul_le hf hw hfw⟩

/-! ### The coefficient `𝒜` -/

theorem integrableOn_sin_div_sq (ω : ℝ) : IntegrableOn (fun t : ℝ => (Real.sin (ω * t) / t) ^ 2) (Ioi 1) := by
  refine integrableOn_inv_sq.mono' ((by fun_prop : Measurable fun t : ℝ => (Real.sin (ω * t) / t) ^ 2)
    |>.aestronglyMeasurable) ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, one_div_pow]
  exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (by positivity)

theorem integral_sin_div_sq_le (ω : ℝ) : ∫ t in Ioi (1 : ℝ), (Real.sin (ω * t) / t) ^ 2 ≤ 1 := by
  refine (setIntegral_mono_on (integrableOn_sin_div_sq ω) integrableOn_inv_sq measurableSet_Ioi
    fun t ht => ?_).trans_eq integral_inv_sq
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [div_pow, one_div_pow]
  exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (by positivity)

/-- `|𝒜(ω)| ≤ 2P`, `P² = ∫₁^∞ ψ²`. -/
theorem abs_aCoef_le (hψm : Measurable ψ) (hψ2 : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1)) (ω : ℝ) :
    |aCoef ψ ω| ≤ 2 * √(∫ t in Ioi (1 : ℝ), ψ t ^ 2) := by
  obtain ⟨-, hcs⟩ := abs_integral_mul_le hψm (by fun_prop) hψ2 (integrableOn_sin_div_sq ω)
  unfold aCoef
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left (hcs.trans ?_) zero_le_two
  calc √(∫ t in Ioi (1 : ℝ), ψ t ^ 2) * √(∫ t in Ioi (1 : ℝ), (Real.sin (ω * t) / t) ^ 2)
      ≤ √(∫ t in Ioi (1 : ℝ), ψ t ^ 2) * 1 := by
        gcongr; exact Real.sqrt_le_one.mpr (integral_sin_div_sq_le ω)
    _ = _ := mul_one _

theorem integrableOn_cos_div_sq (ω : ℝ) : IntegrableOn (fun t : ℝ => (Real.cos (ω * t) / t) ^ 2) (Ioi 1) := by
  refine integrableOn_inv_sq.mono' ((by fun_prop : Measurable fun t : ℝ => (Real.cos (ω * t) / t) ^ 2)
    |>.aestronglyMeasurable) ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, one_div_pow]
  exact div_le_div_of_nonneg_right (Real.cos_sq_le_one _) (by positivity)

theorem integral_cos_div_sq_le (ω : ℝ) : ∫ t in Ioi (1 : ℝ), (Real.cos (ω * t) / t) ^ 2 ≤ 1 := by
  refine (setIntegral_mono_on (integrableOn_cos_div_sq ω) integrableOn_inv_sq measurableSet_Ioi
    fun t ht => ?_).trans_eq integral_inv_sq
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [div_pow, one_div_pow]
  exact div_le_div_of_nonneg_right (Real.cos_sq_le_one _) (by positivity)

theorem integrableOn_cos_div_pow_sq (ω : ℝ) :
    IntegrableOn (fun t : ℝ => (Real.cos (ω * t) / t ^ 2) ^ 2) (Ioi 1) := by
  refine integrableOn_inv_pow_four.mono' ((by fun_prop : Measurable fun t : ℝ => (Real.cos (ω * t) / t ^ 2) ^ 2)
    |>.aestronglyMeasurable) ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, one_div_pow]
  exact div_le_div_of_nonneg_right (Real.cos_sq_le_one _) (by positivity)

theorem integral_cos_div_pow_sq_le (ω : ℝ) : ∫ t in Ioi (1 : ℝ), (Real.cos (ω * t) / t ^ 2) ^ 2 ≤ 1 / 3 := by
  refine (setIntegral_mono_on (integrableOn_cos_div_pow_sq ω) integrableOn_inv_pow_four measurableSet_Ioi
    fun t ht => ?_).trans_eq integral_inv_pow_four
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [div_pow, one_div_pow]
  exact div_le_div_of_nonneg_right (Real.cos_sq_le_one _) (by positivity)

/-- **One integration by parts**: `|𝒜(ω)| ≤ 2(|ψ(1)| + D + P/√3)/ω` for `ω > 0`, `ψ` bounded and `C¹`,
`P² = ∫₁^∞ ψ²`, `D² = ∫₁^∞ ψ′²`. -/
theorem abs_aCoef_le_div (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ'c : Continuous ψ') {Mψ : ℝ}
    (hψb : ∀ t, |ψ t| ≤ Mψ) (hψ2 : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1))
    (hψ'2 : IntegrableOn (fun t => ψ' t ^ 2) (Ioi 1)) {ω : ℝ} (hω : 0 < ω) :
    |aCoef ψ ω| ≤ 2 * (|ψ 1| + √(∫ t in Ioi (1 : ℝ), ψ' t ^ 2) + √(∫ t in Ioi (1 : ℝ), ψ t ^ 2) / √3) / ω := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hψ t).continuousAt
  have hψm : Measurable ψ := hψc.measurable
  have hu : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun t => ψ t / t) (ψ' t / t - ψ t / t ^ 2) t := fun t ht => by
    have ht0 : (t : ℝ) ≠ 0 := (lt_trans one_pos ht).ne'
    have h := (hψ t).div (hasDerivAt_id t) ht0
    have e : (ψ' t * id t - ψ t * 1) / id t ^ 2 = ψ' t / t - ψ t / t ^ 2 := by
      simp only [id]; field_simp
    rw [e] at h; exact h
  have hv : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun t => -(Real.cos (ω * t) / ω)) (Real.sin (ω * t)) t := fun t _ => by
    have h := (((hasDerivAt_id t).const_mul ω).cos.div_const ω).neg
    have e : -(-Real.sin (ω * id t) * (ω * 1) / ω) = Real.sin (ω * t) := by
      simp only [id]; field_simp
    rw [e] at h; exact h
  obtain ⟨i1, -⟩ := abs_integral_mul_le hψm (by fun_prop) hψ2 (integrableOn_sin_div_sq ω)
  obtain ⟨i2, h2⟩ := abs_integral_mul_le hψ'c.measurable (by fun_prop) hψ'2 (integrableOn_cos_div_sq ω)
  obtain ⟨i3, h3⟩ := abs_integral_mul_le hψm (by fun_prop) hψ2 (integrableOn_cos_div_pow_sq ω)
  have huv' : IntegrableOn ((fun t => ψ t / t) * fun t => Real.sin (ω * t)) (Ioi 1) :=
    i1.congr_fun (fun t _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hu'v : IntegrableOn ((fun t => ψ' t / t - ψ t / t ^ 2) * fun t => -(Real.cos (ω * t) / ω)) (Ioi 1) :=
    IntegrableOn.congr_fun (((i2.sub i3).div_const (-ω)))
      (fun t _ => by simp only [Pi.mul_apply, Pi.sub_apply]; field_simp) measurableSet_Ioi
  have h0 : Tendsto ((fun t => ψ t / t) * fun t => -(Real.cos (ω * t) / ω)) (𝓝[>] 1)
      (𝓝 (ψ 1 / 1 * -(Real.cos (ω * 1) / ω))) := by
    have hc : ContinuousAt ((fun t => ψ t / t) * fun t => -(Real.cos (ω * t) / ω)) 1 :=
      ((hψc.continuousAt.div continuousAt_id one_ne_zero)).mul (by fun_prop)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto ((fun t => ψ t / t) * fun t => -(Real.cos (ω * t) / ω)) atTop (𝓝 0) := by
    have hb : ∀ t, 0 < t → ‖((fun t => ψ t / t) * fun t => -(Real.cos (ω * t) / ω)) t‖ ≤ Mψ / ω * t⁻¹ := by
      intro t ht
      simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_neg, abs_div, abs_of_pos ht, abs_of_pos hω]
      have := hψb t
      have hc := abs_cos_le_one (ω * t)
      have hM0 : 0 ≤ Mψ := (abs_nonneg _).trans this
      calc |ψ t| / t * (|Real.cos (ω * t)| / ω) ≤ Mψ / t * (1 / ω) := by gcongr
        _ = Mψ / ω * t⁻¹ := by ring
    have hlim : Tendsto (fun t : ℝ => Mψ / ω * t⁻¹) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.const_mul (Mψ / ω); rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with t ht using hb t ht
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  have e1 : ∫ t in Ioi (1 : ℝ), ψ t * (Real.sin (ω * t) / t)
      = ∫ t in Ioi (1 : ℝ), ψ t / t * Real.sin (ω * t) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  have e2 : ∫ t in Ioi (1 : ℝ), (ψ' t / t - ψ t / t ^ 2) * -(Real.cos (ω * t) / ω)
      = -(1 / ω) * ((∫ t in Ioi (1 : ℝ), ψ' t * (Real.cos (ω * t) / t))
          - ∫ t in Ioi (1 : ℝ), ψ t * (Real.cos (ω * t) / t ^ 2)) := by
    rw [← integral_sub i2 i3, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    field_simp
  unfold aCoef
  rw [e1, hibp, e2]
  have hP3 : √(∫ t in Ioi (1 : ℝ), (Real.cos (ω * t) / t ^ 2) ^ 2) ≤ 1 / √3 := by
    rw [show (1 : ℝ) / √3 = √(1 / 3) by rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (integral_cos_div_pow_sq_le ω)
  have hP1 : √(∫ t in Ioi (1 : ℝ), (Real.cos (ω * t) / t) ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (integral_cos_div_sq_le ω)
  set A := ∫ t in Ioi (1 : ℝ), ψ' t * (Real.cos (ω * t) / t)
  set B := ∫ t in Ioi (1 : ℝ), ψ t * (Real.cos (ω * t) / t ^ 2)
  have hA : |A| ≤ √(∫ t in Ioi (1 : ℝ), ψ' t ^ 2) :=
    h2.trans ((mul_le_mul_of_nonneg_left hP1 (Real.sqrt_nonneg _)).trans_eq (mul_one _))
  have hB : |B| ≤ √(∫ t in Ioi (1 : ℝ), ψ t ^ 2) / √3 :=
    h3.trans ((mul_le_mul_of_nonneg_left hP3 (Real.sqrt_nonneg _)).trans_eq (by ring))
  have hcos := abs_cos_le_one (ω * 1)
  rw [abs_mul, abs_two, show (0 : ℝ) - ψ 1 / 1 * -(Real.cos (ω * 1) / ω) - -(1 / ω) * (A - B)
      = (ψ 1 * Real.cos (ω * 1) + (A - B)) / ω by field_simp; ring, abs_div, abs_of_pos hω]
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hω.le) zero_le_two
  calc |ψ 1 * Real.cos (ω * 1) + (A - B)| ≤ |ψ 1| * 1 + (|A| + |B|) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ (abs_sub _ _))
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ ≤ _ := by linarith

/-! ### The integral `W` -/

theorem measurable_jRot (s : ℂ) : Measurable fun y : ℝ => jRot y s := by
  have hP : ∀ s' : ℂ, Measurable fun y : ℝ => Cvs.Upstream.HolomorphicParamIntegralSine.jPlus y s' := fun s' => by
    have hc : Continuous fun p : ℝ × ℝ => Cvs.Upstream.HolomorphicParamIntegralSine.rotF p.1 s' (1 + p.2 * I) := by
      refine continuous_iff_continuousAt.2 fun p => ?_
      unfold Cvs.Upstream.HolomorphicParamIntegralSine.rotF
      refine ContinuousAt.mul (by fun_prop) ?_
      exact ContinuousAt.comp (g := fun z : ℂ => z ^ (s' - 2)) (f := fun p : ℝ × ℝ => 1 + (p.2 : ℂ) * I)
        ((hasDerivAt_id _).cpow_const (Or.inl (by simp))).continuousAt (by fun_prop)
    have := (hc.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ))))
    unfold Cvs.Upstream.HolomorphicParamIntegralSine.jPlus
    exact measurable_const.mul this.measurable
  unfold jRot
  exact ((hP s).sub (Complex.continuous_conj.measurable.comp (hP (conj s)))).div_const _

/-- `‖W(y₀, s)‖ ≤ P/(√3(y₀ − |Im s| − 1))` for `Re s ≤ 3` and `|Im s| + 1 < y₀`. -/
theorem norm_wInt_le (hψm : Measurable ψ) (hψ2 : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1)) {y₀ : ℝ} {s : ℂ}
    (hs : s.re ≤ 3) (hy : |s.im| + 1 < y₀) :
    ‖wInt ψ y₀ s‖ ≤ √(∫ t in Ioi (1 : ℝ), ψ t ^ 2) / √3 / (y₀ - |s.im| - 1) := by
  set d := y₀ - |s.im| - 1 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have habs2 : IntegrableOn (fun t => |ψ t| ^ 2) (Ioi 1) := hψ2.congr_fun (fun t _ => (sq_abs _).symm)
    measurableSet_Ioi
  obtain ⟨hi, hcs⟩ := abs_integral_mul_le hψm.abs (by fun_prop) habs2 integrableOn_inv_pow_four
  have hbd : ∀ t ∈ Ioi (1 : ℝ), ‖((ψ t / t : ℝ) : ℂ) * jRot (y₀ * t) s‖ ≤ |ψ t| * (1 / t ^ 2) / d := by
    intro t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := lt_trans one_pos ht1
    have hy0 : 0 < y₀ := by linarith [abs_nonneg s.im]
    have hyt : y₀ ≤ y₀ * t := by nlinarith
    have hj := Cvs.Upstream.HolomorphicParamIntegralSine.norm_jRot_le (y := y₀ * t) hs (by linarith)
    have hden : t * d ≤ y₀ * t - |s.im| - 1 := by rw [hd]; nlinarith [abs_nonneg s.im]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    calc |ψ t| / t * ‖jRot (y₀ * t) s‖ ≤ |ψ t| / t * (1 / (t * d)) := by
          gcongr
          exact hj.trans (one_div_le_one_div_of_le (by positivity) hden)
      _ = |ψ t| * (1 / t ^ 2) / d := by field_simp
  have hint : IntegrableOn (fun t => |ψ t| * (1 / t ^ 2) / d) (Ioi 1) := hi.div_const d
  unfold wInt
  calc ‖∫ t in Ioi (1 : ℝ), ((ψ t / t : ℝ) : ℂ) * jRot (y₀ * t) s‖
      ≤ ∫ t in Ioi (1 : ℝ), |ψ t| * (1 / t ^ 2) / d :=
        norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbd))
    _ = (∫ t in Ioi (1 : ℝ), |ψ t| * (1 / t ^ 2)) / d := integral_div _ _
    _ ≤ (√(∫ t in Ioi (1 : ℝ), |ψ t| ^ 2) * √(∫ t in Ioi (1 : ℝ), (1 / t ^ 2) ^ 2)) / d := by
        gcongr; exact (le_abs_self _).trans hcs
    _ = √(∫ t in Ioi (1 : ℝ), ψ t ^ 2) / √3 / d := by
        have hsq : (∫ t in Ioi (1 : ℝ), |ψ t| ^ 2) = ∫ t in Ioi (1 : ℝ), ψ t ^ 2 :=
          setIntegral_congr_fun measurableSet_Ioi fun t _ => sq_abs _
        rw [integral_inv_pow_four, Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_one, hsq]
        ring

/-- `W(y₀, ·)` is holomorphic on `Re s < 3`, `|Im s| < y₀ − 2`, for bounded measurable `ψ`. -/
theorem differentiableOn_wInt (hψm : Measurable ψ) {Mψ : ℝ} (hψb : ∀ t, |ψ t| ≤ Mψ) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    DifferentiableOn ℂ (wInt ψ y₀) (Cvs.Upstream.HolomorphicParamIntegralSine.jRegion y₀) := by
  have hM0 : 0 ≤ Mψ := (abs_nonneg _).trans (hψb 0)
  refine Cvs.Upstream.HolomorphicParamIntegralSine.differentiableOn_integral (μ := volume.restrict (Ioi (1 : ℝ)))
    (Cvs.Upstream.HolomorphicParamIntegralSine.isOpen_jRegion y₀) (g := fun t => Mψ * (1 / t) ^ 2)
    (fun s _ => ((Complex.continuous_ofReal.measurable.comp (hψm.div measurable_id)).mul
      ((measurable_jRot s).comp (measurable_const.mul measurable_id))).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 1 < t) => ?_))
    (integrableOn_inv_sq.const_mul Mψ)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 1 < t) s hs => ?_))
  · have hsub : Cvs.Upstream.HolomorphicParamIntegralSine.jRegion y₀ ⊆ Cvs.Upstream.HolomorphicParamIntegralSine.jRegion (y₀ * t) := fun s hs =>
      ⟨hs.1, hs.2.trans_le (by nlinarith)⟩
    exact ((Cvs.Upstream.HolomorphicParamIntegralSine.differentiableOn_jRot (y₀ * t)).mono hsub).const_mul _
  · have ht0 : 0 < t := lt_trans one_pos ht
    have hs' : |s.im| < y₀ - 2 := hs.2
    have hj := Cvs.Upstream.HolomorphicParamIntegralSine.norm_jRot_le (y := y₀ * t) hs.1.le (by nlinarith)
    have hden : t ≤ y₀ * t - |s.im| - 1 := by nlinarith [abs_nonneg s.im]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    calc |ψ t| / t * ‖jRot (y₀ * t) s‖ ≤ Mψ / t * (1 / t) := by
          gcongr
          · exact hψb t
          · exact hj.trans (one_div_le_one_div_of_le ht0 hden)
      _ = Mψ * (1 / t) ^ 2 := by ring

/-! ### The per-mode identity -/

/-- **The per-mode term**: for `Re s < 0`, `−2∫₁^∞ ψ(t)C(kct, s) dt = M_k(s)`. -/
theorem neg_two_integral_cosM_eq (hψm : Measurable ψ) (hψ2 : IntegrableOn (fun t => ψ t ^ 2) (Ioi 1))
    {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : s.re < 0) :
    -2 * ∫ t in Ioi (1 : ℝ), ((ψ t : ℝ) : ℂ) * cosM (k * c * t) s = mTerm ψ c k s := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set y := (k : ℝ) * c with hy
  have hy0 : 0 < y := by positivity
  obtain ⟨i1, -⟩ := abs_integral_mul_le hψm (by fun_prop) hψ2 (integrableOn_sin_div_sq y)
  obtain ⟨i0, -⟩ := abs_integral_mul_le hψm.abs (by fun_prop : Measurable fun t : ℝ => 1 / t)
    (hψ2.congr_fun (fun t _ => (sq_abs _).symm) measurableSet_Ioi) integrableOn_inv_sq
  have i1c : IntegrableOn (fun t => ((ψ t * (Real.sin (y * t) / t) : ℝ) : ℂ)) (Ioi 1) := i1.ofReal
  have i2c : IntegrableOn (fun t => ((ψ t / t : ℝ) : ℂ) * jRot (y * t) s) (Ioi 1) := by
    refine (i0.div_const (1 - s.re)).mono'
      (((Complex.continuous_ofReal.measurable.comp (hψm.div measurable_id)).mul
        ((measurable_jRot s).comp (measurable_const.mul measurable_id))).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 1 < t) => ?_))
    have ht0 : 0 < t := lt_trans one_pos ht
    have hj : jRot (y * t) s = sinM (y * t) (s - 1) :=
      (Cvs.Upstream.HolomorphicParamIntegralSine.sinM_sub_one_eq_jRot (by positivity) (by linarith)).symm
    have hb := Cvs.Upstream.TrigMellinIntegralsContinuation.norm_sinM_le (s := s - 1) (by simp; linarith) (y * t)
    have hre : -(s - 1).re = 1 - s.re := by simp
    rw [hre, hj.symm] at hb
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    calc |ψ t| / t * ‖jRot (y * t) s‖ ≤ |ψ t| / t * (1 / (1 - s.re)) := by gcongr
      _ = |ψ t| * (1 / t) / (1 - s.re) := by ring
  have hpt : ∀ t ∈ Ioi (1 : ℝ), ((ψ t : ℝ) : ℂ) * cosM (y * t) s
      = -((1 / y : ℝ) : ℂ) * ((ψ t * (Real.sin (y * t) / t) : ℝ) : ℂ)
        - (s - 1) / y * (((ψ t / t : ℝ) : ℂ) * jRot (y * t) s) := by
    intro t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [Cvs.Upstream.TrigMellinIntegralsContinuation.cosM_eq hs (by positivity), Cvs.Upstream.HolomorphicParamIntegralSine.sinM_sub_one_eq_jRot (by positivity) (by linarith)]
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub (i1c.const_mul _) (i2c.const_mul _),
    integral_const_mul, integral_const_mul, integral_complex_ofReal]
  unfold mTerm aCoef wInt
  simp only [hy]
  push_cast
  field_simp
  ring

/-! ### The sums over modes -/

/-- `Σ_{n} 1/(n + K + 1)² ≤ 1/K` for `K ≥ 1`. -/
theorem tsum_inv_sq_shift_le {K : ℕ} (hK : 1 ≤ K) :
    ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + K + 1) ^ 2 ≤ 1 / (K : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun N => ?_
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have htel : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + K + 1) ^ 2
      ≤ 1 / (K : ℝ) - 1 / ((N : ℝ) + K) := by
    intro N
    induction N with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hm : (0 : ℝ) < (m : ℝ) + K := by positivity
      have hstep : (1 : ℝ) / ((m : ℝ) + K + 1) ^ 2 ≤ 1 / ((m : ℝ) + K) - 1 / ((m : ℝ) + K + 1) := by
        rw [div_sub_div _ _ hm.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      rw [show (m : ℝ) + 1 + K = m + K + 1 by ring]
      linarith
  have hpos : 0 ≤ 1 / ((N : ℝ) + K) := by positivity
  linarith [htel N]

/-- **The `𝒜`-sum with a logarithm**: for `P > 0`, `B ≥ 0`, `c > 0`,
`Σ_{k≥1} min(2P, B/(kc))/(kc) ≤ (2P/c)(2 + log(1 + B/(2cP)))`, the series being summable. -/
theorem tsum_min_le {P B c : ℝ} (hP : 0 < P) (hB : 0 ≤ B) (hc : 0 < c) :
    Summable (fun n : ℕ => min (2 * P) (B / (((n : ℝ) + 1) * c)) / (((n : ℝ) + 1) * c))
      ∧ ∑' n : ℕ, min (2 * P) (B / (((n : ℝ) + 1) * c)) / (((n : ℝ) + 1) * c)
        ≤ 2 * P / c * (2 + Real.log (1 + B / (2 * c * P))) := by
  set f : ℕ → ℝ := fun n => min (2 * P) (B / (((n : ℝ) + 1) * c)) / (((n : ℝ) + 1) * c) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => div_nonneg (le_min (by positivity) (by positivity)) (by positivity)
  have hfB : ∀ n, f n ≤ B / c ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := fun n => by
    simp only [hf]
    calc min (2 * P) (B / (((n : ℝ) + 1) * c)) / (((n : ℝ) + 1) * c)
        ≤ B / (((n : ℝ) + 1) * c) / (((n : ℝ) + 1) * c) := by gcongr; exact min_le_right _ _
      _ = B / c ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by field_simp
  have hsum2 : Summable fun n : ℕ => B / c ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    exact (this.mul_left (B / c ^ 2)).congr fun n => by push_cast; ring
  have hsum : Summable f := hsum2.of_nonneg_of_le hf0 hfB
  refine ⟨hsum, ?_⟩
  set K := ⌈B / (2 * c * P)⌉₊ with hK
  have hBc : 0 ≤ B / (2 * c * P) := by positivity
  have hlogK : Real.log K ≤ Real.log (1 + B / (2 * c * P)) := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (by linarith)
    · refine Real.log_le_log (by exact_mod_cast hpos) ?_
      have := Nat.ceil_lt_add_one (by positivity : 0 ≤ B / (2 * c * P))
      rw [← hK] at this; linarith
  have hlogK0 : 0 ≤ Real.log (1 + B / (2 * c * P)) := Real.log_nonneg (by linarith)
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · -- `B = 0`: every term vanishes
    have hB0 : B = 0 := by
      have := Nat.ceil_eq_zero.1 (hK ▸ hK0)
      have h2 : 0 ≤ B / (2 * c * P) := by positivity
      have h3 : B / (2 * c * P) = 0 := le_antisymm this h2
      rcases div_eq_zero_iff.1 h3 with h | h
      · exact h
      · exfalso; have : 0 < 2 * c * P := by positivity
        linarith
    have : ∀ n, f n = 0 := fun n => by
      show min (2 * P) (B / (((n : ℝ) + 1) * c)) / (((n : ℝ) + 1) * c) = 0
      rw [hB0, zero_div, min_eq_right (by positivity : (0 : ℝ) ≤ 2 * P), zero_div]
    rw [show f = fun _ => 0 from funext this, tsum_zero]
    positivity
  -- split at `K`
  rw [← hsum.sum_add_tsum_nat_add K]
  have h1 : ∑ n ∈ Finset.range K, f n ≤ 2 * P / c * (1 + Real.log K) := by
    have hH := harmonic_le_one_add_log K
    calc ∑ n ∈ Finset.range K, f n ≤ ∑ n ∈ Finset.range K, 2 * P / c * (1 / ((n : ℝ) + 1)) :=
          Finset.sum_le_sum fun n _ => by
            simp only [hf]
            calc min (2 * P) (B / (((n : ℝ) + 1) * c)) / (((n : ℝ) + 1) * c)
                ≤ 2 * P / (((n : ℝ) + 1) * c) := by gcongr; exact min_le_left _ _
              _ = 2 * P / c * (1 / ((n : ℝ) + 1)) := by field_simp
      _ = 2 * P / c * (harmonic K : ℝ) := by
          rw [← Finset.mul_sum]; congr 1
          simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ 2 * P / c * (1 + Real.log K) := by gcongr
  have h2 : ∑' n : ℕ, f (n + K) ≤ 2 * P / c := by
    have hle : ∀ n : ℕ, f (n + K) ≤ B / c ^ 2 * (1 / ((n : ℝ) + K + 1) ^ 2) := fun n => by
      have := hfB (n + K); push_cast at this; linarith
    have hs2 : Summable fun n : ℕ => B / c ^ 2 * (1 / ((n : ℝ) + K + 1) ^ 2) := by
      have := (summable_nat_add_iff K).2 hsum2
      exact this.congr fun n => by push_cast; ring
    calc ∑' n : ℕ, f (n + K) ≤ ∑' n : ℕ, B / c ^ 2 * (1 / ((n : ℝ) + K + 1) ^ 2) :=
          ((summable_nat_add_iff K).2 hsum).tsum_le_tsum hle hs2
      _ = B / c ^ 2 * ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + K + 1) ^ 2 := tsum_mul_left
      _ ≤ B / c ^ 2 * (1 / K) := mul_le_mul_of_nonneg_left (tsum_inv_sq_shift_le hKpos) (by positivity)
      _ ≤ 2 * P / c := by
          have hKge : B / (2 * c * P) ≤ K := Nat.le_ceil _
          have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
          rw [div_le_iff₀ (by positivity)] at hKge
          rw [mul_one_div, div_div, div_le_div_iff₀ (by positivity) hc]
          nlinarith
  calc ∑ n ∈ Finset.range K, f n + ∑' n : ℕ, f (n + K)
      ≤ 2 * P / c * (1 + Real.log K) + 2 * P / c := add_le_add h1 h2
    _ ≤ 2 * P / c * (2 + Real.log (1 + B / (2 * c * P))) := by
        have : 0 ≤ 2 * P / c := by positivity
        nlinarith

/-! ### Monotonicity of `P(C + log(1 + β/P))` -/

/-- `λ log(1 + b/λ) ≤ log(1 + b)` for `0 < λ ≤ 1`, `b ≥ 0` (Bernoulli). -/
theorem mul_log_one_add_div_le {l b : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (hb : 0 ≤ b) :
    l * Real.log (1 + b / l) ≤ Real.log (1 + b) := by
  have hB := one_add_mul_self_le_rpow_one_add (s := b) (by linarith) (p := 1 / l)
    (by rw [le_div_iff₀ hl0]; linarith)
  have h1 : Real.log (1 + b / l) ≤ 1 / l * Real.log (1 + b) := by
    rw [← Real.log_rpow (by linarith)]
    refine Real.log_le_log (by positivity) ?_
    calc 1 + b / l = 1 + 1 / l * b := by ring
      _ ≤ _ := hB
  calc l * Real.log (1 + b / l) ≤ l * (1 / l * Real.log (1 + b)) := mul_le_mul_of_nonneg_left h1 hl0.le
    _ = Real.log (1 + b) := by field_simp

/-- **Monotonicity**: `P(C + log(1 + β/P)) ≤ Q(C + log(1 + β′/Q))` for `0 < P ≤ Q`, `0 ≤ β ≤ β′`, `C ≥ 0`. -/
theorem mul_add_log_le {P Q β β' C : ℝ} (hP : 0 < P) (hPQ : P ≤ Q) (hβ : 0 ≤ β) (hββ' : β ≤ β') (hC : 0 ≤ C) :
    P * (C + Real.log (1 + β / P)) ≤ Q * (C + Real.log (1 + β' / Q)) := by
  have hQ : 0 < Q := hP.trans_le hPQ
  have h1 : P * Real.log (1 + β / P) ≤ Q * Real.log (1 + β / Q) := by
    have := mul_log_one_add_div_le (l := P / Q) (by positivity) ((div_le_one hQ).2 hPQ) (by positivity : 0 ≤ β / Q)
    have e : β / Q / (P / Q) = β / P := by field_simp
    rw [e] at this
    calc P * Real.log (1 + β / P) = Q * (P / Q * Real.log (1 + β / P)) := by field_simp
      _ ≤ Q * Real.log (1 + β / Q) := mul_le_mul_of_nonneg_left this hQ.le
  have h2 : Real.log (1 + β / Q) ≤ Real.log (1 + β' / Q) :=
    Real.log_le_log (by positivity) (by gcongr)
  nlinarith

end Cvs.Prolate.Mellin.ModeExteriorTerms

end
