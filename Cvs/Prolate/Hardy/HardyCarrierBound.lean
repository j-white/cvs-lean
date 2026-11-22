import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CarrierBoundBothColumns
import Cvs.Prolate.Hardy.CarrierNegativeFreqRate
import Cvs.Prolate.Hardy.CarrierNegativeFrequencies
import Cvs.Prolate.Hardy.CarrierUpperHalfPlane
import Cvs.Prolate.Hardy.ColumnTwoCarrierWave
import Cvs.Prolate.Hardy.ColumnWaveErrorBound
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.LipSymmetricPieces
import Cvs.Prolate.Hardy.ReflectedWaveSplit
import Cvs.Prolate.Hardy.SpectrumCosineHighpass
import Cvs.Upstream.FourierLpConjReflect
import Cvs.Upstream.HardyHalvesFourier
import Cvs.Upstream.HardyProjectionReal
import Cvs.Upstream.JordanArcIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The carrier bound (7) for `J_c`: `‖J_c Re(Ae^{icx})|_I‖ ≤ C·M`

For `A` holomorphic on `|z| ≤ 3/5` with `|A| ≤ M` on the ellipse `(3/5, √11/10)`, `J_c f = Re(e^{icx}A)1_I` plus
`Re[w(conj E − E)]` with `E = (1 − P₊)k − (1 − P₊)m`; the arc bound and `‖m‖ ≤ M/√5` give `C = 1 + 2(3/5)πκ + 2/√5`,
`κ = (δ₀ · 2π√11/10)^{−1/2}`, for every `c ≥ 1`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.Hardy.HardyCarrierBound
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.CentralResolventTrace (L2I)
open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R)
open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C posProj mulOp reLp ofRealLp ext0 wR wInvI hardyJ)
open Cvs.Upstream.FourierLpConjReflect (conjLp)
open Cvs.Prolate.Hardy.CarrierNegativeFrequencies (carH kC eta0)
open Cvs.Prolate.Hardy.LipSymmetricPieces (symS)
open Cvs.Prolate.Hardy.ColumnTwoCarrierWave (toL2)
open Cvs.Prolate.Hardy.CarrierBoundBothColumns (CarrierBound ellipse)

theorem mem_ellipse_real {x : ℝ} (hx : |x| ≤ 3 / 5) : (x : ℂ) ∈ ellipse (3 / 5) (√11 / 10) := by
  show ((x : ℂ).re / (3 / 5)) ^ 2 + ((x : ℂ).im / (√11 / 10)) ^ 2 ≤ 1
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_div]
  rw [zero_pow two_ne_zero, add_zero, div_pow, div_le_one (by norm_num)]
  nlinarith [sq_abs x, abs_nonneg x]

theorem mem_ellipse_arc (θ : ℝ) : (1 / 2 : ℂ) * Complex.cosh (eta0 + θ * Complex.I) ∈ ellipse (3 / 5) (√11 / 10) := by
  have hz := Cvs.Upstream.JordanArcIntegral.cosh_arc (1 / 2) eta0 θ
  rw [Cvs.Prolate.Hardy.CarrierNegativeFrequencies.cosh_eta0, Cvs.Prolate.Hardy.CarrierNegativeFrequencies.sinh_eta0] at hz
  have e : (1 / 2 : ℂ) * Complex.cosh (eta0 + θ * Complex.I) =
      ((3 / 5 * Real.cos θ : ℝ) : ℂ) + Complex.I * ((√11 / 10 * Real.sin θ : ℝ) : ℂ) := by
    push_cast at hz ⊢; linear_combination hz
  have hre : ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * Complex.I)).re = 3 / 5 * Real.cos θ := by
    rw [e]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]; ring
  have him : ((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * Complex.I)).im = √11 / 10 * Real.sin θ := by
    rw [e]; simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]; ring
  show (((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * Complex.I)).re / (3 / 5)) ^ 2 +
    (((1 / 2 : ℂ) * Complex.cosh (eta0 + θ * Complex.I)).im / (√11 / 10)) ^ 2 ≤ 1
  rw [hre, him]
  have hs : (0 : ℝ) < √11 / 10 := by positivity
  rw [show 3 / 5 * Real.cos θ / (3 / 5) = Real.cos θ by field_simp,
    show √11 / 10 * Real.sin θ / (√11 / 10) = Real.sin θ by field_simp]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem h_eq {c : ℝ} {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z) :
    toL2 (cI.indicator (carH c A)) = toL2 (kC c A) - toL2 ((symS (1 / 2) (3 / 5)).indicator (carH c A)) := by
  refine Lp.ext ?_
  filter_upwards [Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 (Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_cI_of c hA), Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 (Cvs.Prolate.Hardy.CarrierNegativeFreqRate.memLp_kC c hA),
    Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 (Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_symS_of c hA (a := 1 / 2) (b := 3 / 5) (by norm_num) le_rfl),
    Lp.coeFn_sub (toL2 (kC c A)) (toL2 ((symS (1 / 2) (3 / 5)).indicator (carH c A))),
    Cvs.Prolate.Hardy.SpectrumCosineHighpass.ae_ne (-(1 / 2))] with x h1 h2 h3 h4 hx
  rw [h1, h4, Pi.sub_apply, h2, h3, ← Cvs.Prolate.Hardy.LipSymmetricPieces.kC_sub_indicator c _ hx]
  ring

/-- `‖Re(w h)‖ ≤ M` where `w h = 1_I Ae^{icx}`. -/
theorem norm_re_w_h_le {c M : ℝ} (hc : 0 ≤ c) {A : ℂ → ℂ} (hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z)
    (hM : ∀ z ∈ ellipse (3 / 5) (√11 / 10), ‖A z‖ ≤ M) :
    ‖reLp (mulOp (wR (c / 2)) (toL2 (cI.indicator (carH c A))))‖ ≤ M := by
  have hb : 0 ≤ c / 2 := by positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using mem_ellipse_real (x := 0) (by norm_num)))
  set g : ℝ → ℝ := cI.indicator fun _ => M
  have hg : MemLp g 2 (volume : Measure ℝ) :=
    (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 (memLp_const M)
  have hle : ‖reLp (mulOp (wR (c / 2)) (toL2 (cI.indicator (carH c A))))‖ ≤ ‖hg.toLp g‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [Cvs.Prolate.Hardy.ReflectedWaveSplit.coeFn_reLp (mulOp (wR (c / 2)) (toL2 (cI.indicator (carH c A)))),
      Cvs.Upstream.HardyProjectionReal.coeFn_mulOp (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wR hb) (toL2 (cI.indicator (carH c A))),
      Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 (Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_cI_of c hA), hg.coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    simp only [g]
    by_cases hx : x ∈ cI
    · rw [indicator_of_mem hx, indicator_of_mem hx, Real.norm_eq_abs, Real.norm_of_nonneg hM0]
      have hxx : |x| ≤ 3 / 5 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      have e : wR (c / 2) x * carH c A x = A x * Complex.exp (Complex.I * ((c * x : ℝ) : ℂ)) := by
        unfold carH; field_simp [Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_ne_zero]; push_cast; ring_nf
      rw [e]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, mul_comm (Complex.I) _, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hM _ (mem_ellipse_real hxx)
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
  refine hle.trans ?_
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.nullMeasurableSet]
  have : (volume.restrict cI) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num
  rw [eLpNorm_const _ (by norm_num) (by rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]; norm_num), this]
  simp [Real.eNorm_of_nonneg hM0, ENNReal.toReal_ofReal hM0]

/-- The carrier-bound constant `C = 1 + 2(3/5)π(δ₀ · 2π√11/10)^{−1/2} + 2/√5`. -/
def cCar : ℝ := 1 + 2 * (3 / 5 * π * √(1 / ((√11 / 10 - 3 / 10) * (2 * π * (√11 / 10))))) + 2 * √(1 / 5)

/-- **The carrier bound (7)** for `J_c`, `c ≥ 1`. -/
theorem carrierBound_hardyJ {c : ℝ} (hc : 1 ≤ c) :
    CarrierBound c (Metric.closedBall 0 (3 / 5)) (ellipse (3 / 5) (√11 / 10)) cCar (hardyJ c) := by
  intro A M hAd hM f hf
  have hc0 : 0 < c := by linarith
  have hA : ∀ z : ℂ, ‖z‖ ≤ 3 / 5 → DifferentiableAt ℂ A z := fun z hz =>
    hAd z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using mem_ellipse_real (x := 0) (by norm_num)))
  have hb : 0 ≤ c / 2 := by positivity
  set h := toL2 (cI.indicator (carH c A))
  set k := toL2 (kC c A)
  set m := toL2 ((symS (1 / 2) (3 / 5)).indicator (carH c A))
  have hh : h = k - m - ((0 : L2C) + 0) - 0 := by simp only [h, k, m]; rw [h_eq hA]; abel
  have hsplit := Cvs.Prolate.Hardy.ReflectedWaveSplit.split h k m 0 0 0 hh
  simp only [map_zero, sub_zero, add_zero, sub_self] at hsplit
  have hJ := Cvs.Prolate.Hardy.ColumnTwoCarrierWave.hardyJ_eq_of hc0.le hA hf
  rw [hsplit, map_add, map_add] at hJ
  rw [hJ]
  -- the three pieces
  have t1 := norm_re_w_h_le hc0.le hA hM
  have t2 := Cvs.Prolate.Hardy.ReflectedWaveSplit.norm_reflect_le (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wR hb) (Cvs.Prolate.Hardy.CarrierUpperHalfPlane.norm_wR_le hb) (k - posProj k - (m - posProj m))
  have tk : ‖k - posProj k‖ ≤ M * (3 / 5) * π * √(1 / (c * (√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)))) := by
    have h2 := Cvs.Prolate.Hardy.CarrierNegativeFreqRate.norm_sub_posProj_kC_sq_le hc0 hA (fun θ _ => hM _ (mem_ellipse_arc θ)) (Cvs.Prolate.Hardy.CarrierNegativeFreqRate.memLp_kC c hA)
    rw [show k = (Cvs.Prolate.Hardy.CarrierNegativeFreqRate.memLp_kC c hA).toLp _ from Cvs.Prolate.Hardy.ColumnTwoCarrierWave.toL2_eq _]
    exact Cvs.Prolate.Hardy.ColumnWaveErrorBound.norm_le_of_sq_le (by positivity) h2
  have tm : ‖m - posProj m‖ ≤ M * √(2 * (3 / 5 - 1 / 2)) := by
    refine (Cvs.Upstream.HardyHalvesFourier.norm_sub_posProj_le m).trans ?_
    have hm := Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_symS_of c hA (a := 1 / 2) (b := 3 / 5) (by norm_num) le_rfl
    have h2 := Cvs.Prolate.Hardy.LipSymmetricPieces.norm_sq_symS_le (c := c) (a := 1 / 2) (b := 3 / 5) le_rfl (by norm_num) (A := A)
      (fun x hx => hM _ (mem_ellipse_real (by
        rcases hx with hx | hx
        · rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        · rw [abs_le]; constructor <;> linarith [hx.1, hx.2]))) hm
    rw [show m = hm.toLp _ from Cvs.Prolate.Hardy.ColumnTwoCarrierWave.toL2_eq _]
    exact Cvs.Prolate.Hardy.ColumnWaveErrorBound.norm_le_of_sq_le hM0 h2
  have hcmp : √(1 / (c * (√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)))) ≤
      √(1 / ((√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)))) := by
    refine Real.sqrt_le_sqrt (one_div_le_one_div_of_le (mul_pos Cvs.Prolate.Hardy.CarrierNegativeFreqRate.delta0_pos (by positivity)) ?_)
    have : 0 < (√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)) := mul_pos Cvs.Prolate.Hardy.CarrierNegativeFreqRate.delta0_pos (by positivity)
    rw [mul_assoc]; nlinarith
  have hE : ‖k - posProj k - (m - posProj m)‖ ≤ ‖k - posProj k‖ + ‖m - posProj m‖ := norm_sub_le _ _
  calc _ ≤ ‖reLp (mulOp (wR (c / 2)) h)‖ + ‖reLp (mulOp (wR (c / 2)) (conjLp (k - posProj k - (m - posProj m)) -
        (k - posProj k - (m - posProj m))))‖ := norm_add_le _ _
    _ ≤ M + 2 * (M * (3 / 5) * π * √(1 / ((√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)))) +
        M * √(2 * (3 / 5 - 1 / 2))) := by
        have := mul_le_mul_of_nonneg_left hcmp (show 0 ≤ M * (3 / 5) * π by positivity)
        nlinarith
    _ = cCar * M := by
        unfold cCar
        rw [show 2 * (3 / 5 - 1 / 2 : ℝ) = 1 / 5 by norm_num]
        ring

/-- The carrier bound holds eventually along `c = 2πx`. -/
theorem eventually_carrierBound :
    ∀ᶠ x : ℕ in Filter.atTop, CarrierBound (2 * π * x) (Metric.closedBall 0 (3 / 5)) (ellipse (3 / 5) (√11 / 10))
      cCar (hardyJ (2 * π * x)) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with x hx
  have : (1 : ℝ) ≤ x := by exact_mod_cast hx
  exact carrierBound_hardyJ (by nlinarith [Real.pi_gt_three])

end Cvs.Prolate.Hardy.HardyCarrierBound

end
