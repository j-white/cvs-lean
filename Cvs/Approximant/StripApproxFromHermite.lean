import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.QuarticHermiteWindowPhi
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.CosineCoefficientCompleteness
import Cvs.Finite.RecentredTransform
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowedModeSumDomain
import Cvs.Finite.WindowedPartialSumsConverge
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TopCornerConstants
import Cvs.Limit.CriticalStripOffAxes
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapStripLimit
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.Archimedean.LevyChannelSumSquares
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.EImageRadical
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhiDerivativesSignedSmall
import Cvs.Xi.PhiEvenExtension
import Cvs.Xi.PhiEvenRapidDecay
import Cvs.Xi.PhiTwiceDifferentiable
import Cvs.Xi.RiemannPhiContinuous
import Cvs.Xi.RiemannPhiEven
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.XiOffRealLine
import Cvs.Xi.XiValueAtOrigin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Strip approximability from closeness to the quartic Hermite profile

The cosine coefficients of `Φ(· − L/2)` are `O(L²/n²)`, so truncation at `N ≥ x^{1/4}` costs
`O(L³x^{−1/4})`. A profile `G_x` with `∫_{[0,1]}(G_x − b_x g_H)² ≤ Cx^{−3/2}`, `|b_x| ≥ b₀x^{1/4}`,
has test within `O(√(L H_x) x^{−1/4})` of `32 b_x x^{−3/4} Φ_L` relative to `b_x x^{−3/4}`; with
Cvs.Xi.XiOffRealLine the normalised truncated coefficient vectors are strip approximable.
-/

noncomputable section

open Real Set Filter MeasureTheory Matrix Topology Interval

namespace Cvs.Approximant.StripApproxFromHermite
open Cvs.ZeroCounting

open Cvs.Xi.RiemannPhiKernel (riemannPhi phiBoundConst)
open Cvs.Xi.PhiTwiceDifferentiable (riemannPhi1 riemannPhi2)
open Cvs.Finite.SymmetricModeSet (Idx mode negI coeff coeff_even)
open Cvs.L2a.TailLogScaleTest (logScale)

/-! ### The cosine coefficients of the recentred `Φ` -/

/-- `Φ` recentred on the window `(0, L]`. -/
def phiShift (L t : ℝ) : ℝ := riemannPhi (t - L / 2)

/-- The bound on `|Φ'|`. -/
def phi1Max : ℝ := Cvs.Xi.PhiDerivativesSignedSmall.phi1Const * exp (-(π / 4))

/-- The bound on `|Φ''|`. -/
def phi2Max : ℝ := Cvs.Xi.PhiDerivativesSignedSmall.phi2Const * exp (-(π / 4))

/-- `|Φ'| ≤ M₁` on the whole line. -/
theorem abs_riemannPhi1_le_max (u : ℝ) : |riemannPhi1 u| ≤ phi1Max := by
  have key : ∀ v : ℝ, 0 ≤ v → |riemannPhi1 v| ≤ phi1Max := fun v hv =>
    (Cvs.Xi.PhiDerivativesSignedSmall.abs_riemannPhi1_le hv).trans (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (exp_pos _).le (exp_le_one_iff.mpr (by linarith)))
      Cvs.Xi.PhiDerivativesSignedSmall.phi1Const_nonneg)
  rcases le_total 0 u with hu | hu
  · exact key u hu
  · have h := Cvs.Xi.PhiDerivativesSignedSmall.riemannPhi1_neg (-u)
    rw [neg_neg] at h
    rw [h, abs_neg]
    exact key (-u) (by linarith)

/-- `|Φ''| ≤ M₂` on the whole line. -/
theorem abs_riemannPhi2_le_max (u : ℝ) : |riemannPhi2 u| ≤ phi2Max := by
  have key : ∀ v : ℝ, 0 ≤ v → |riemannPhi2 v| ≤ phi2Max := fun v hv =>
    (Cvs.Xi.PhiDerivativesSignedSmall.abs_riemannPhi2_le hv).trans (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (exp_pos _).le (exp_le_one_iff.mpr (by linarith)))
      Cvs.Xi.PhiDerivativesSignedSmall.phi2Const_nonneg)
  rcases le_total 0 u with hu | hu
  · exact key u hu
  · have h := Cvs.Xi.PhiDerivativesSignedSmall.riemannPhi2_neg (-u)
    rw [neg_neg] at h
    rw [h]
    exact key (-u) (by linarith)

/-- `M₁ ≥ 0`. -/
theorem phi1Max_nonneg : 0 ≤ phi1Max := (abs_nonneg _).trans (abs_riemannPhi1_le_max 0)

/-- `M₂ ≥ 0`. -/
theorem phi2Max_nonneg : 0 ≤ phi2Max := (abs_nonneg _).trans (abs_riemannPhi2_le_max 0)

/-- **Two integrations by parts**: the `n`-th cosine coefficient of the recentred `Φ` is at most
`(2M₁ + L M₂) L/(2π² n²)`. -/
theorem abs_coef_phiShift_le {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : n ≠ 0) :
    |Cvs.Finite.WindowCosineBessel.coef L (phiShift L) n| ≤ (2 * phi1Max + L * phi2Max) * L / (2 * π ^ 2 * n ^ 2) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  set ω : ℝ := 2 * π * n / L with hω
  have hω0 : 0 < ω := by positivity
  have hωL : ω * L = 2 * π * n := by rw [hω]; field_simp
  have hsin : sin (ω * L) = 0 := by
    rw [hωL, show 2 * π * (n : ℝ) = ((2 * n : ℕ) : ℝ) * π by push_cast; ring]
    exact sin_nat_mul_pi _
  have hcos : cos (ω * L) = 1 := by
    rw [hωL, show 2 * π * (n : ℝ) = (n : ℝ) * (2 * π) by ring]
    exact cos_nat_mul_two_pi _
  set g := phiShift L
  set g1 : ℝ → ℝ := fun t => riemannPhi1 (t - L / 2)
  set g2 : ℝ → ℝ := fun t => riemannPhi2 (t - L / 2)
  have hg : ∀ t, HasDerivAt g (g1 t) t := fun t =>
    HasDerivAt.comp_sub_const t (L / 2) (Cvs.Xi.PhiTwiceDifferentiable.hasDerivAt_riemannPhi (t - L / 2))
  have hg1 : ∀ t, HasDerivAt g1 (g2 t) t := fun t =>
    HasDerivAt.comp_sub_const t (L / 2) (Cvs.Xi.PhiTwiceDifferentiable.hasDerivAt_riemannPhi1 (t - L / 2))
  have hc1 : Continuous g1 := Cvs.Xi.PhiDerivativesSignedSmall.continuous_riemannPhi1.comp (by fun_prop)
  have hc2 : Continuous g2 := Cvs.Xi.PhiDerivativesSignedSmall.continuous_riemannPhi2.comp (by fun_prop)
  have hsd : ∀ t, HasDerivAt (fun t => sin (ω * t) / ω) (cos (ω * t)) t := fun t => by
    have := ((hasDerivAt_id t).const_mul ω).sin.div_const ω
    simpa [mul_comm, hω0.ne'] using this
  have hcd : ∀ t, HasDerivAt (fun t => -cos (ω * t) / ω ^ 2) (sin (ω * t) / ω) t := fun t =>
    (((hasDerivAt_id' t).const_mul ω).cos.neg.div_const (ω ^ 2)).congr_deriv (by field_simp)
  -- first integration by parts
  have h1 : ∫ t in (0:ℝ)..L, g t * cos (ω * t) = -∫ t in (0:ℝ)..L, g1 t * (sin (ω * t) / ω) := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hg t) (fun t _ => hsd t)
      (hc1.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => cos (ω * t)).intervalIntegrable _ _)]
    simp [hsin]
  -- second integration by parts
  have h2 : ∫ t in (0:ℝ)..L, g1 t * (sin (ω * t) / ω)
      = (g1 0 - g1 L) / ω ^ 2 + (∫ t in (0:ℝ)..L, g2 t * cos (ω * t)) / ω ^ 2 := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hg1 t) (fun t _ => hcd t)
      (hc2.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => sin (ω * t) / ω).intervalIntegrable _ _)]
    have e : (fun t => g2 t * (-cos (ω * t) / ω ^ 2))
        = fun t => (-(1 / ω ^ 2)) * (g2 t * cos (ω * t)) := by
      funext t; ring
    rw [e, intervalIntegral.integral_const_mul, hcos]
    simp only [mul_zero, cos_zero]
    ring
  have hint : |∫ t in (0:ℝ)..L, g2 t * cos (ω * t)| ≤ L * phi2Max := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L)
      (f := fun t => g2 t * cos (ω * t)) (C := phi2Max) (fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _) |>.trans
          (abs_riemannPhi2_le_max _))
    simpa [Real.norm_eq_abs, abs_of_pos hL, mul_comm] using this
  have hbd : |∫ t in (0:ℝ)..L, g t * cos (ω * t)| ≤ (2 * phi1Max + L * phi2Max) / ω ^ 2 := by
    rw [h1, abs_neg, h2]
    have hω2 : 0 < ω ^ 2 := by positivity
    calc |(g1 0 - g1 L) / ω ^ 2 + (∫ t in (0:ℝ)..L, g2 t * cos (ω * t)) / ω ^ 2|
        ≤ |g1 0 - g1 L| / ω ^ 2 + |∫ t in (0:ℝ)..L, g2 t * cos (ω * t)| / ω ^ 2 := by
          rw [← abs_of_pos hω2, ← abs_div, ← abs_div, abs_of_pos hω2]
          exact abs_add_le _ _
      _ ≤ (2 * phi1Max) / ω ^ 2 + (L * phi2Max) / ω ^ 2 := by
          gcongr
          exact (abs_sub _ _).trans (by
            linarith [abs_riemannPhi1_le_max (0 - L / 2), abs_riemannPhi1_le_max (L - L / 2)])
      _ = (2 * phi1Max + L * phi2Max) / ω ^ 2 := by ring
  rw [Cvs.Finite.WindowCosineBessel.coef, if_neg hn, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / L)]
  calc 2 / L * |∫ x in (0:ℝ)..L, g x * cos (2 * π * n / L * x)|
      ≤ 2 / L * ((2 * phi1Max + L * phi2Max) / ω ^ 2) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = (2 * phi1Max + L * phi2Max) * L / (2 * π ^ 2 * n ^ 2) := by
        rw [hω]; field_simp

/-- The constant `(2M₁ + M₂)/(2π²)` of the coefficient decay. -/
def phiCoefConst : ℝ := (2 * phi1Max + phi2Max) / (2 * π ^ 2)

/-- For `L ≥ 1`, `|aₙ| ≤ K L²/n²`. -/
theorem abs_coef_phiShift_le_sq {L : ℝ} (hL : 1 ≤ L) {n : ℕ} (hn : n ≠ 0) :
    |Cvs.Finite.WindowCosineBessel.coef L (phiShift L) n| ≤ phiCoefConst * L ^ 2 / n ^ 2 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  refine (abs_coef_phiShift_le (by linarith) hn).trans ?_
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h1 : (2 * phi1Max + L * phi2Max) * L ≤ (2 * phi1Max + phi2Max) * L ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hLL phi1Max_nonneg, phi2Max_nonneg]
  rw [show phiCoefConst * L ^ 2 / n ^ 2 = (2 * phi1Max + phi2Max) * L ^ 2 / (2 * π ^ 2 * n ^ 2) by
    unfold phiCoefConst; field_simp]
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- The recentred `Φ` is continuous. -/
theorem continuous_phiShift (L : ℝ) : Continuous (phiShift L) :=
  Cvs.Xi.RiemannPhiContinuous.continuous_riemannPhi.comp (by fun_prop)

/-- The recentred `Φ` is symmetric about the centre of the window. -/
theorem phiShift_symm (L t : ℝ) : phiShift L (L - t) = phiShift L t := by
  unfold phiShift
  rw [show L - t - L / 2 = -(t - L / 2) by ring, Cvs.Xi.RiemannPhiEven.riemannPhi_neg]

/-- **The truncation rate of the recentred `Φ`**: for `L ≥ 1`,
`∫₀ᴸ (Φ_L − S_N Φ_L)² ≤ K² π² L⁵/(12 (N + 1)²)`. -/
theorem integral_sub_modeSum_phiShift_le {L : ℝ} (hL : 1 ≤ L) (N : ℕ) :
    ∫ t in (0:ℝ)..L, (phiShift L t - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L (Finset.range (N + 1))
        (Cvs.Finite.WindowCosineBessel.coef L (phiShift L)) t) ^ 2
      ≤ phiCoefConst ^ 2 * π ^ 2 * L ^ 5 / (12 * ((N : ℝ) + 1) ^ 2) := by
  have hL0 : 0 < L := by linarith
  set a := Cvs.Finite.WindowCosineBessel.coef L (phiShift L)
  set f : ℕ → ℝ := fun n => (if n = 0 then 2 else 1) * a n ^ 2 with hf
  have hS := Cvs.Finite.CosineCoefficientCompleteness.hasSum_coef_sq hL0 (continuous_phiShift L) (phiShift_symm L)
  have hsplit := hS.summable.sum_add_tsum_nat_add (N + 1)
  rw [hS.tsum_eq] at hsplit
  rw [Cvs.Finite.WindowCosineBessel.integral_sub_modeSum_sq hL0 (continuous_phiShift L)]
  have hI : ∫ x in (0:ℝ)..L, phiShift L x ^ 2
      = L / 2 * ((2 / L) * ∫ x in (0:ℝ)..L, phiShift L x ^ 2) := by
    field_simp
  rw [hI, ← hsplit]
  have hz : HasSum (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using h
  set K := phiCoefConst ^ 2 * L ^ 4 / ((N : ℝ) + 1) ^ 2
  have hK : 0 ≤ K := by positivity
  have hle : ∀ i : ℕ, f (i + (N + 1)) ≤ K * (1 / ((i : ℝ) + 1) ^ 2) := by
    intro i
    have hn : i + (N + 1) ≠ 0 := by omega
    simp only [hf, if_neg hn, one_mul]
    have hb := abs_coef_phiShift_le_sq hL hn
    have hc : 0 ≤ phiCoefConst * L ^ 2 / ((i + (N + 1) : ℕ) : ℝ) ^ 2 :=
      (abs_nonneg _).trans hb
    have hsq : a (i + (N + 1)) ^ 2
        ≤ (phiCoefConst * L ^ 2 / ((i + (N + 1) : ℕ) : ℝ) ^ 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    refine hsq.trans ?_
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hm : ((N : ℝ) + 1) * ((i : ℝ) + 1) ≤ ((i + (N + 1) : ℕ) : ℝ) ^ 2 := by
      push_cast; nlinarith
    rw [div_pow, show K * (1 / ((i : ℝ) + 1) ^ 2)
        = (phiCoefConst * L ^ 2) ^ 2 / (((N : ℝ) + 1) * ((i : ℝ) + 1)) ^ 2 by
      simp only [K]; field_simp]
    gcongr
  have hsumm : Summable fun i => f (i + (N + 1)) :=
    (summable_nat_add_iff (N + 1)).mpr hS.summable
  have htsum : ∑' i, f (i + (N + 1)) ≤ K * (π ^ 2 / 6) := by
    rw [← (hz.mul_left K).tsum_eq]
    exact hsumm.tsum_le_tsum hle (hz.mul_left K).summable
  have hnn : 0 ≤ L / 2 := by positivity
  calc L / 2 * (∑ i ∈ Finset.range (N + 1), f i + ∑' i, f (i + (N + 1)))
        - L / 2 * ∑ n ∈ Finset.range (N + 1), f n
      = L / 2 * ∑' i, f (i + (N + 1)) := by ring
    _ ≤ L / 2 * (K * (π ^ 2 / 6)) := mul_le_mul_of_nonneg_left htsum hnn
    _ = phiCoefConst ^ 2 * π ^ 2 * L ^ 5 / (12 * ((N : ℝ) + 1) ^ 2) := by
        simp only [K]; field_simp; ring

/-- The sup bound `C e^{−π}` on `|Φ|`. -/
def phiMax : ℝ := phiBoundConst * exp (-π)

/-- `|Φ| ≤ C e^{−π}` on the whole line. -/
theorem abs_riemannPhi_le_max (u : ℝ) : |riemannPhi u| ≤ phiMax := by
  have h := Cvs.Xi.PhiEvenRapidDecay.norm_phiEven_le u
  rw [Cvs.Xi.RiemannPhiEven.phiEven_eq, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right (Cvs.Xi.XiOffRealLine.phiBoundConst_mul_nonneg)
    (exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg u))))

/-- The recentred `Φ` is square integrable for any finite measure. -/
theorem memLp_phiShift (L : ℝ) {μ : Measure ℝ} [IsFiniteMeasure μ] : MemLp (phiShift L) 2 μ :=
  MemLp.of_bound (continuous_phiShift L).aestronglyMeasurable phiMax
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_riemannPhi_le_max _)

/-- The `Φ` window is square integrable. -/
theorem memLp_phiWindow (L : ℝ) : MemLp (Cvs.Xi.XiOffRealLine.phiWindow L) 2 volume := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) L)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  exact (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr (memLp_phiShift L)

/-- **Truncation on the transform side**: for `L ≥ 1` the truncated cosine series of the
recentred `Φ` has transform within `√(K²π²L⁵/(12(N+1)²)) √L e^{|Im z| L/2}` of the window's. -/
theorem norm_ctransform_phiShift_sub_le {L : ℝ} (hL : 1 ≤ L) (N : ℕ) (z : ℂ) :
    ‖Cvs.Route.GroundRouteJointGap.ctransform L N (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L (phiShift L))) z
        - Cvs.Finite.RecentredTransform.phase L z * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Xi.XiOffRealLine.phiWindow L)) z‖
      ≤ √(phiCoefConst ^ 2 * π ^ 2 * L ^ 5 / (12 * ((N : ℝ) + 1) ^ 2)) * √L
        * exp (|z.im| * L / 2) := by
  have hL0 : 0 < L := by linarith
  set ξ := coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L (phiShift L))
  have hsW : ∀ s ∉ Ioc (0:ℝ) L, Cvs.Xi.XiOffRealLine.phiWindow L s = 0 := fun s hs =>
    indicator_of_notMem hs _
  have hsM : ∀ s ∉ Ioc (0:ℝ) L, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) ξ s = 0 := fun s hs => by
    simp [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, hs]
  have h := Cvs.Route.GroundRouteJointGap.norm_phase_mul_sub_le hL0.le (Cvs.WeilForm.Archimedean.LevyChannelSumSquares.memLp_modeSum L (mode N) ξ)
    (memLp_phiWindow L) hsM hsW z
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)) (exp_pos _).le)
  rw [← Cvs.Finite.SymmetricModeSet.windowMode_eq_modeSum L N _ _ subset_rfl, Cvs.Finite.WindowedPartialSumsConverge.integral_sub_eq hL0 hsW]
  refine le_of_eq_of_le ?_ (integral_sub_modeSum_phiShift_le hL N)
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hL0.le] at ht
  rw [Cvs.Xi.XiOffRealLine.phiWindow, indicator_of_mem ht]
  unfold phiShift
  ring

/-! ### The test of a profile -/

/-- The test of a profile `F` at scale `x`: its window image at `1/x`, log-scaled and moved into
`(0, log x]`. -/
def kOf (x : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := fun s =>
  logScale (Cvs.Xi.EImageWindowPoisson.window (1 / x) F) (s - Real.log x)

/-- The test is subtractive in the profile. -/
theorem kOf_sub (x : ℝ) (F H : ℝ → ℝ) :
    kOf x (fun u => F u - H u) = fun s => kOf x F s - kOf x H s := by
  funext s
  simp only [kOf, logScale, Cvs.Xi.EImageWindowPoisson.window_sub]
  ring

/-- The test is homogeneous in the profile. -/
theorem kOf_smul (x t : ℝ) (F : ℝ → ℝ) :
    kOf x (fun u => t * F u) = fun s => t * kOf x F s := by
  funext s
  simp only [kOf, logScale, Cvs.Approximant.SpineSubspace.window_smul]
  ring

/-- The test of a profile continuous on `[0, 1]` is square integrable. -/
theorem memLp_kOf {x : ℝ} (hx : 0 < x) {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 1)) :
    MemLp (kOf x F) 2 volume := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hF
  have ha : 0 < 1 / x := one_div_pos.mpr hx
  have hmeas : Measurable (Cvs.Xi.EImageWindowPoisson.window (1 / x) F) :=
    (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hF).indicator measurableSet_Icc
  have hb : ∀ θ, |Cvs.Xi.EImageWindowPoisson.window (1 / x) F θ| ≤ M :=
    Cvs.Approximant.ConnesVectorRealScale.abs_window_le ha fun u hu => by simpa using hM u (Ioc_subset_Icc_self hu)
  have hL := (Cvs.WeilForm.EImageRadical.integrable_logScale_of_support hmeas hb ha
    (fun θ hθ => Cvs.Xi.EImageWindowPoisson.window_of_notMem F hθ)).2
  have e : kOf x F = fun s => logScale (Cvs.Xi.EImageWindowPoisson.window (1 / x) F) (s + -Real.log x) := by
    funext s; simp only [kOf, sub_eq_add_neg]
  rw [e]
  exact Cvs.WeilForm.CentredWindowTranslate.memLp_translate (-Real.log x) hL

/-- The quartic Hermite profile is continuous. -/
theorem continuous_gH (c : ℝ) : Continuous (Cvs.Approximant.QuarticHermiteWindowPhi.gH c) := by
  unfold Cvs.Approximant.QuarticHermiteWindowPhi.gH; fun_prop

/-- **The test against `b·32x^{−3/4}·Φ`**: for `x ≥ 4/π`, `β = 32 b x^{−3/4}` and `F` continuous
on `[0, 1]`, `∫₀^{log x}(k_F − βΦ_L)² ≤ 2H_⌊x⌋∫_{[0,1]}(F − b g_H)² + 2β²∫₀^{log x} T_x²`. -/
theorem integral_kOf_sub_phiShift_sq_le {x : ℝ} (hx : 4 / π ≤ x) (b : ℝ) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 1)) :
    ∫ t in (0:ℝ)..Real.log x,
        (kOf x F t - 32 * b * x ^ (-(3 / 4 : ℝ)) * phiShift (Real.log x) t) ^ 2
      ≤ 2 * (harmonic ⌊x⌋₊ : ℝ)
          * (∫ u in Icc (0 : ℝ) 1, (F u - b * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2)
        + 2 * (32 * b * x ^ (-(3 / 4 : ℝ))) ^ 2
          * ∫ t in (0:ℝ)..Real.log x, Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hx1 : 1 ≤ x := le_trans (by
    rw [le_div_iff₀ pi_pos]; linarith [pi_lt_four]) hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  set L := Real.log x
  set β := 32 * b * x ^ (-(3 / 4 : ℝ))
  set c := 2 * π * x
  set D : ℝ → ℝ := fun u => F u - b * Cvs.Approximant.QuarticHermiteWindowPhi.gH c u
  have hD : ContinuousOn D (Icc 0 1) :=
    hF.sub (continuous_const.mul (continuous_gH c)).continuousOn
  have hkD := memLp_kOf hx0 hD
  have hT := Cvs.Approximant.QuarticHermiteWindowPhi.memLp_tailX hx
  -- the test minus `βΦ_L` is the test of the difference minus `βT_x`
  have hae : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) L →
      (kOf x F t - β * phiShift L t) ^ 2 = (kOf x D t - β * Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t) ^ 2 := by
    filter_upwards [Cvs.Approximant.QuarticHermiteWindowPhi.logScale_window_gH_ae hx0] with t ht htI
    rw [uIoc_of_le hL] at htI
    have hsplit : kOf x F t = kOf x D t + b * kOf x (Cvs.Approximant.QuarticHermiteWindowPhi.gH c) t := by
      have h1 := congrFun (kOf_sub x F (fun u => b * Cvs.Approximant.QuarticHermiteWindowPhi.gH c u)) t
      rw [congrFun (kOf_smul x b (Cvs.Approximant.QuarticHermiteWindowPhi.gH c)) t] at h1
      simp only [D]
      rw [h1]; ring
    have hk : kOf x (Cvs.Approximant.QuarticHermiteWindowPhi.gH c) t
        = 32 * x ^ (-(3 / 4 : ℝ)) * (phiShift L t - Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t) := by
      have h2 : kOf x (Cvs.Approximant.QuarticHermiteWindowPhi.gH c) t
          = logScale (Cvs.Xi.EImageWindowPoisson.window (1 / x) (Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x))) (t - Real.log x) := rfl
      rw [h2, ht, Cvs.Xi.XiOffRealLine.phiWindow, indicator_of_mem htI, indicator_of_mem htI]
      rfl
    rw [hsplit, hk]
    ring
  rw [intervalIntegral.integral_congr_ae hae]
  have hi1 : IntervalIntegrable (fun t => (kOf x D t - β * Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t) ^ 2) volume 0 L :=
    (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL ((hkD.restrict _).sub (hT.const_mul β))).2
  have hi2 : IntervalIntegrable (fun t => kOf x D t ^ 2) volume 0 L :=
    (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL (hkD.restrict _)).2
  have hi3 : IntervalIntegrable (fun t => Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2) volume 0 L :=
    (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL hT).2
  calc ∫ t in (0:ℝ)..L, (kOf x D t - β * Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t) ^ 2
      ≤ ∫ t in (0:ℝ)..L, (2 * kOf x D t ^ 2 + 2 * β ^ 2 * Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2) :=
        intervalIntegral.integral_mono_on hL hi1
          ((hi2.const_mul 2).add (hi3.const_mul (2 * β ^ 2))) fun t _ => by
            nlinarith [sq_nonneg (kOf x D t + β * Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t)]
    _ = 2 * (∫ t in (0:ℝ)..L, kOf x D t ^ 2)
          + 2 * β ^ 2 * ∫ t in (0:ℝ)..L, Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2 := by
        rw [intervalIntegral.integral_add (hi2.const_mul 2) (hi3.const_mul _)]
        simp only [intervalIntegral.integral_const_mul]
    _ ≤ 2 * ((harmonic ⌊x⌋₊ : ℝ) * ∫ u in Icc (0 : ℝ) 1, D u ^ 2)
          + 2 * β ^ 2 * ∫ t in (0:ℝ)..L, Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2 := by
        have hk : ∫ t in (0:ℝ)..L, kOf x D t ^ 2
            ≤ (harmonic ⌊x⌋₊ : ℝ) * ∫ u in Icc (0 : ℝ) 1, D u ^ 2 := by
          rw [intervalIntegral.integral_of_le hL]
          refine (setIntegral_le_integral hkD.integrable_sq
            (Eventually.of_forall fun t => sq_nonneg _)).trans ?_
          exact Cvs.Approximant.ConnesVectorRealScale.integral_logScale_window_sq_le hx0 (hD.pow 2).integrableOn_Icc L
        linarith
    _ = _ := by rw [← mul_assoc]

/-! ### The normalised coefficient vector of a profile -/

/-- The even coefficient vector is homogeneous in the frequency coefficients. -/
theorem coeff_smul (N : ℕ) (s : Finset ℕ) (t : ℝ) (a : ℕ → ℝ) :
    coeff N s (fun n => t * a n) = t • coeff N s a := by
  funext i
  rcases i with _ | ⟨k, _⟩ <;> simp only [coeff, Pi.smul_apply, smul_eq_mul] <;> split_ifs <;>
    ring

/-- A vector normalised to unit length, or the zero mode when it vanishes. -/
def unitVec {N : ℕ} (ξ : Idx N → ℝ) : Idx N → ℝ :=
  if ξ ⬝ᵥ ξ = 0 then Pi.single none 1 else (√(ξ ⬝ᵥ ξ))⁻¹ • ξ

/-- Normalisation keeps an even vector even. -/
theorem unitVec_even {N : ℕ} {ξ : Idx N → ℝ} (hξ : ∀ i, ξ (negI N i) = ξ i) (i : Idx N) :
    unitVec ξ (negI N i) = unitVec ξ i := by
  unfold unitVec
  split_ifs
  · rcases i with _ | ⟨k, b⟩ <;> simp [negI]
  · simp only [Pi.smul_apply, hξ]

/-- The normalised vector is a unit vector. -/
theorem unitVec_dotProduct_self {N : ℕ} (ξ : Idx N → ℝ) : unitVec ξ ⬝ᵥ unitVec ξ = 1 := by
  unfold unitVec
  split_ifs with h
  · simp
  · have hq : 0 ≤ ξ ⬝ᵥ ξ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, ← mul_inv,
      Real.mul_self_sqrt hq, inv_mul_cancel₀ h]

/-- The cosine coefficients on `(0, log x]` of the test of the profile `G x`, on `Idx N`. -/
def profileCoef (G : ℝ → ℝ → ℝ) (x : ℝ) (N : ℕ) : Idx N → ℝ :=
  coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef (Real.log x) (kOf x (G x)))

/-- The normalised coefficient vector of the profile family `G` at truncation `N x`. -/
def profileVec (N : ℝ → ℕ) (G : ℝ → ℝ → ℝ) (x : ℝ) : Idx (N x) → ℝ :=
  unitVec (profileCoef G x (N x))

/-- Connes' vector is the normalised coefficient vector of the spine profile of `{1}`. -/
theorem connesVec_eq_profileVec (N : ℝ → ℕ) :
    Cvs.Approximant.ConnesVectorRealScale.connesVec N = profileVec N fun x => Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1 :=
  rfl

/-! ### The error at one scale -/

/-- The profile error `log x · x^a · Q/β²`, `β = 32 b x^{−3/4}` and
`Q = 2H_⌊x⌋∫_{[0,1]}(F − b g_H)² + 2β²∫₀^{log x} T_x²`. -/
def profileErr (x a b : ℝ) (F : ℝ → ℝ) : ℝ :=
  Real.log x * exp (a * Real.log x)
    * ((2 * (harmonic ⌊x⌋₊ : ℝ) * (∫ u in Icc (0 : ℝ) 1, (F u - b * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2)
      + 2 * (32 * b * x ^ (-(3 / 4 : ℝ))) ^ 2 * ∫ t in (0:ℝ)..Real.log x, Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2)
      / (32 * b * x ^ (-(3 / 4 : ℝ))) ^ 2)

/-- The truncation error `K²π² (log x)⁶ x^a/(12 (N + 1)²)`. -/
def truncErr (x a : ℝ) (N : ℕ) : ℝ :=
  phiCoefConst ^ 2 * π ^ 2 * Real.log x ^ 5 / (12 * ((N : ℝ) + 1) ^ 2) * Real.log x
    * exp (a * Real.log x)

/-- The window error `4 C e^{−π} e^{−(1−a) log x/2}/(1 − a)`. -/
def windowErr (x a : ℝ) : ℝ := 4 * phiMax * exp (-((1 - a) * (Real.log x / 2))) / (1 - a)

/-- `(2/|β|)√L √Q e^{aL/2} = 2√(L e^{aL} Q/β²)`. -/
theorem sqrt_combine {β L Q a : ℝ} (hβ : β ≠ 0) (hL : 0 ≤ L) :
    2 / |β| * √L * √Q * exp (a * L / 2) = 2 * √(L * exp (a * L) * (Q / β ^ 2)) := by
  rw [Real.sqrt_mul (mul_nonneg hL (exp_pos _).le), Real.sqrt_mul hL, ← Real.exp_half,
    Real.sqrt_div' _ (sq_nonneg β), Real.sqrt_sq_eq_abs]
  have : 0 < |β| := abs_pos.mpr hβ
  field_simp

/-- `2√R √L e^{aL/2} = 2√(R L e^{aL})`. -/
theorem sqrt_combine' {R L a : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) :
    2 * √R * √L * exp (a * L / 2) = 2 * √(R * L * exp (a * L)) := by
  rw [Real.sqrt_mul (mul_nonneg hR hL), Real.sqrt_mul hR, ← Real.exp_half]
  ring

/-- **The error at one scale.** For `x ≥ e`, `β = 32 b x^{−3/4} ≠ 0`, `F` continuous on `[0, 1]`
and `|Im z| ≤ a < 1`, `(2/β)` times the transform of the truncated coefficients of `k_F` is within
`2√(profileErr) + 2√(truncErr) + windowErr` of `Ξ(z)`. -/
theorem norm_two_div_mul_ctransform_sub_Xi_le {x a b β : ℝ} (hx : exp 1 ≤ x)
    (hβ : β = 32 * b * x ^ (-(3 / 4 : ℝ))) (hβ0 : β ≠ 0) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 1)) (N : ℕ) (ha : a < 1) {z : ℂ} (hz : |z.im| ≤ a) :
    ‖((2 / β : ℝ) : ℂ) * Cvs.Route.GroundRouteJointGap.ctransform (Real.log x) N
        (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef (Real.log x) (kOf x F))) z - Cvs.Limit.ZeroFreeApproximantsRH.Xi z‖
      ≤ 2 * √(profileErr x a b F) + 2 * √(truncErr x a N) + windowErr x a := by
  subst hβ
  set β := 32 * b * x ^ (-(3 / 4 : ℝ))
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) hx
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hL0 : 0 < Real.log x := by linarith
  have hx4 : 4 / π ≤ x := by
    refine le_trans ?_ hx
    have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    refine le_trans ?_ h2
    rw [div_le_iff₀ pi_pos]; linarith [pi_gt_three]
  set L := Real.log x
  set ξ := coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L (kOf x F))
  set ξΦ := coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L (phiShift L))
  set W := Cvs.Finite.RecentredTransform.phase L z * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Xi.XiOffRealLine.phiWindow L)) z
  set Q := 2 * (harmonic ⌊x⌋₊ : ℝ)
      * (∫ u in Icc (0 : ℝ) 1, (F u - b * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2)
    + 2 * β ^ 2 * ∫ t in (0:ℝ)..L, Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2
  have hkF : MemLp (kOf x F) 2 (volume.restrict (Ioc 0 L)) := (memLp_kOf hx0 hF).restrict _
  have hβΦ : MemLp (fun t => β * phiShift L t) 2 (volume.restrict (Ioc 0 L)) := by
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) L)) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    exact (memLp_phiShift L).const_mul β
  have hsm : coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L fun t => β * phiShift L t) = β • ξΦ := by
    rw [Cvs.Approximant.ConnesVectorRealScale.coef_smul, coeff_smul]
  have hsplit : ((2 / β : ℝ) : ℂ) * Cvs.Route.GroundRouteJointGap.ctransform L N ξ z - Cvs.Limit.ZeroFreeApproximantsRH.Xi z
      = ((2 / β : ℝ) : ℂ) * (Cvs.Route.GroundRouteJointGap.ctransform L N ξ z - Cvs.Route.GroundRouteJointGap.ctransform L N
          (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L fun t => β * phiShift L t)) z)
        + 2 * (Cvs.Route.GroundRouteJointGap.ctransform L N ξΦ z - W) + (2 * W - Cvs.Limit.ZeroFreeApproximantsRH.Xi z) := by
    rw [hsm, Cvs.Route.GroundRouteJointGap.ctransform_smul]
    have : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ0
    push_cast
    field_simp
    ring
  have hexp : exp (|z.im| * L / 2) ≤ exp (a * L / 2) :=
    exp_le_exp.mpr (by have := mul_le_mul_of_nonneg_right hz hL0.le; linarith)
  -- the profile term
  have h1 : ‖((2 / β : ℝ) : ℂ) * (Cvs.Route.GroundRouteJointGap.ctransform L N ξ z - Cvs.Route.GroundRouteJointGap.ctransform L N
        (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L fun t => β * phiShift L t)) z)‖
      ≤ 2 * √(profileErr x a b F) := by
    have hJ := integral_kOf_sub_phiShift_sq_le hx4 b hF
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two, profileErr,
      ← sqrt_combine hβ0 hL0.le]
    have hb := Cvs.Approximant.ConnesVectorRealScale.norm_ctransform_coef_sub_le hL0 N hkF hβΦ z
    calc 2 / |β| * ‖Cvs.Route.GroundRouteJointGap.ctransform L N ξ z - Cvs.Route.GroundRouteJointGap.ctransform L N
          (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L fun t => β * phiShift L t)) z‖
        ≤ 2 / |β| * (√L * √Q * exp (a * L / 2)) := by
          refine mul_le_mul_of_nonneg_left (hb.trans ?_) (by positivity)
          gcongr
      _ = _ := by ring
  -- the truncation term
  have h2 : ‖(2 : ℂ) * (Cvs.Route.GroundRouteJointGap.ctransform L N ξΦ z - W)‖ ≤ 2 * √(truncErr x a N) := by
    rw [norm_mul, Complex.norm_two, truncErr, ← sqrt_combine' (by positivity) hL0.le]
    have hb := norm_ctransform_phiShift_sub_le hL1 N z
    calc 2 * ‖Cvs.Route.GroundRouteJointGap.ctransform L N ξΦ z - W‖
        ≤ 2 * (√(phiCoefConst ^ 2 * π ^ 2 * L ^ 5 / (12 * ((N : ℝ) + 1) ^ 2)) * √L
          * exp (a * L / 2)) := by
          refine mul_le_mul_of_nonneg_left (hb.trans ?_) two_pos.le
          gcongr
      _ = _ := by ring
  -- the window term
  have h3 := Cvs.Xi.XiOffRealLine.norm_two_mul_phase_mul_sub_Xi_le hL0.le ha hz
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) ?_)
  simpa [phiMax, windowErr] using h3

/-! ### The size of the coefficient vector -/

/-- **The coefficient energy against a comparison**: `L‖ξ_g‖² ≤ 2∫₀ᴸ(g − h)² + 2∫₀ᴸ h²`. -/
theorem mul_dotProduct_coeff_le {L : ℝ} (hL : 0 < L) (N : ℕ) {g h : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 L))) (hh : MemLp h 2 (volume.restrict (Ioc 0 L))) :
    L * (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L g)
        ⬝ᵥ coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L g))
      ≤ 2 * (∫ t in (0:ℝ)..L, (g t - h t) ^ 2) + 2 * ∫ t in (0:ℝ)..L, h t ^ 2 := by
  rw [← Cvs.Route.GroundRouteJointGap.integral_modeSum_sq hL N (coeff_even N _ _)]
  refine (Cvs.Approximant.ConnesVectorRealScale.integral_modeSum_coeff_sq_le hL N hg).trans ?_
  have i1 := (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL.le hg).2
  have i2 : IntervalIntegrable (fun t => (g t - h t) ^ 2) volume 0 L :=
    (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL.le (hg.sub hh)).2
  have i3 := (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL.le hh).2
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (i2.const_mul 2) (i3.const_mul 2)]
  exact intervalIntegral.integral_mono_on hL.le i1 ((i2.const_mul 2).add (i3.const_mul 2))
    fun t _ => by nlinarith [sq_nonneg (g t - 2 * h t)]

/-- **The coefficient vector is of size `β`**: `‖ξ‖²/β² ≤ 2 profileErr(x, 0) + 2 (C e^{−π})²`. -/
theorem dotProduct_div_sq_le {x b : ℝ} (hx : exp 1 ≤ x) (hβ0 : 32 * b * x ^ (-(3 / 4 : ℝ)) ≠ 0)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 1)) (N : ℕ) :
    coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef (Real.log x) (kOf x F))
        ⬝ᵥ coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef (Real.log x) (kOf x F))
        / (32 * b * x ^ (-(3 / 4 : ℝ))) ^ 2
      ≤ 2 * profileErr x 0 b F + 2 * phiMax ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) hx
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hL0 : 0 < Real.log x := by linarith
  have hx4 : 4 / π ≤ x := by
    refine le_trans ?_ hx
    have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    refine le_trans ?_ h2
    rw [div_le_iff₀ pi_pos]; linarith [pi_gt_three]
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (Real.log x))) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hE := mul_dotProduct_coeff_le hL0 N ((memLp_kOf hx0 hF).restrict (Ioc 0 (Real.log x)))
    ((memLp_phiShift (Real.log x)).const_mul (32 * b * x ^ (-(3 / 4 : ℝ))))
  have hJ := integral_kOf_sub_phiShift_sq_le hx4 b hF
  set L := Real.log x
  set β := 32 * b * x ^ (-(3 / 4 : ℝ))
  set ξ := coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L (kOf x F))
  set Q := 2 * (harmonic ⌊x⌋₊ : ℝ)
      * (∫ u in Icc (0 : ℝ) 1, (F u - b * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2)
    + 2 * β ^ 2 * ∫ t in (0:ℝ)..L, Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2
  have hJ0 : 0 ≤ ∫ t in (0:ℝ)..L, (kOf x F t - β * phiShift L t) ^ 2 :=
    intervalIntegral.integral_nonneg hL0.le fun t _ => sq_nonneg _
  have hΦ : ∫ t in (0:ℝ)..L, (β * phiShift L t) ^ 2 ≤ L * (β ^ 2 * phiMax ^ 2) := by
    have h := intervalIntegral.integral_mono_on (f := fun t => (β * phiShift L t) ^ 2)
      (g := fun _ => β ^ 2 * phiMax ^ 2) hL0.le
      (Cvs.Approximant.ConnesVectorRealScale.intervalIntegrable_of_memLp hL0.le ((memLp_phiShift L).const_mul β)).2
      intervalIntegrable_const fun t _ => by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_riemannPhi_le_max _) 2) (sq_nonneg β)
    calc _ ≤ _ := h
      _ = L * (β ^ 2 * phiMax ^ 2) := by simp; ring
  have hQ0 : 0 ≤ Q / β ^ 2 := div_nonneg (hJ0.trans hJ) (sq_nonneg _)
  have hβ2 : 0 < β ^ 2 := by positivity
  have hP : profileErr x 0 b F = L * (Q / β ^ 2) := by
    show L * exp (0 * L) * (Q / β ^ 2) = _
    rw [zero_mul, exp_zero, mul_one]
  rw [hP]
  have hdot : ξ ⬝ᵥ ξ ≤ (2 * Q + 2 * (L * (β ^ 2 * phiMax ^ 2))) / L := by
    rw [le_div_iff₀ hL0, mul_comm]
    linarith
  calc ξ ⬝ᵥ ξ / β ^ 2 ≤ (2 * Q + 2 * (L * (β ^ 2 * phiMax ^ 2))) / L / β ^ 2 := by
        gcongr
    _ = 2 * (Q / β ^ 2) / L + 2 * phiMax ^ 2 := by field_simp
    _ ≤ 2 * (L * (Q / β ^ 2)) + 2 * phiMax ^ 2 := by
        have hL2 : 1 ≤ L * L := by nlinarith
        have : 2 * (Q / β ^ 2) / L ≤ 2 * (L * (Q / β ^ 2)) := by
          rw [div_le_iff₀ hL0]; nlinarith [mul_le_mul_of_nonneg_left hL2 hQ0]
        linarith

/-! ### The errors vanish below height `1/2` -/

/-- `(log x)^k x^p → 0` for `p < 0`. -/
theorem tendsto_log_pow_mul_exp (k : ℕ) {p : ℝ} (hp : p < 0) :
    Tendsto (fun x : ℝ => Real.log x ^ k * exp (p * Real.log x)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (neg_pos.mpr hp)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_natCast, div_eq_mul_inv, ← Real.rpow_neg hx.le, neg_neg, Real.rpow_def_of_pos hx,
    mul_comm (Real.log x)]

/-- The window error vanishes for `a < 1`. -/
theorem tendsto_windowErr {a : ℝ} (ha : a < 1) :
    Tendsto (fun x => windowErr x a) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => exp (-((1 - a) * (Real.log x / 2)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (Tendsto.const_mul_atTop (by linarith) (Real.tendsto_log_atTop.atTop_div_const two_pos)))
  have h2 := (h.const_mul (4 * phiMax)).div_const (1 - a)
  rw [mul_zero, zero_div] at h2
  exact h2

/-- `n ≥ x^{1/4}` gives `(n + 1)² ≥ √x`. -/
theorem exp_half_log_le_sq {x : ℝ} (hx : 0 < x) {n : ℝ} (hn : x ^ (1 / 4 : ℝ) ≤ n) :
    exp (Real.log x / 2) ≤ (n + 1) ^ 2 := by
  have h1 : x ^ (1 / 4 : ℝ) = exp (Real.log x / 4) := by
    rw [Real.rpow_def_of_pos hx]; ring_nf
  have h2 : exp (Real.log x / 2) = exp (Real.log x / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h2]
  rw [h1] at hn
  exact pow_le_pow_left₀ (exp_pos _).le (by linarith) 2

/-- The truncation error vanishes for `a < 1/2` once `N x ≥ x^{1/4}` eventually. -/
theorem tendsto_truncErr {a : ℝ} (ha : a < 1 / 2) {N : ℝ → ℕ}
    (hN : ∀ᶠ x in atTop, x ^ (1 / 4 : ℝ) ≤ N x) :
    Tendsto (fun x => truncErr x a (N x)) atTop (𝓝 0) := by
  have hlim := (tendsto_log_pow_mul_exp 6 (p := a - 1 / 2) (by linarith)).const_mul
    (phiCoefConst ^ 2 * π ^ 2 / 12)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have := Real.log_nonneg hx
    unfold truncErr; positivity
  · filter_upwards [eventually_ge_atTop 1, hN] with x hx hNx
    have hx0 : 0 < x := by linarith
    have hq := exp_half_log_le_sq hx0 hNx
    have e : exp ((a - 1 / 2) * Real.log x) = exp (a * Real.log x) / exp (Real.log x / 2) := by
      rw [← Real.exp_sub]; ring_nf
    have hL := Real.log_nonneg hx
    rw [e]
    unfold truncErr
    calc phiCoefConst ^ 2 * π ^ 2 * Real.log x ^ 5 / (12 * ((N x : ℝ) + 1) ^ 2) * Real.log x
          * exp (a * Real.log x)
        = phiCoefConst ^ 2 * π ^ 2 / 12 * (Real.log x ^ 6 * exp (a * Real.log x))
          / ((N x : ℝ) + 1) ^ 2 := by
          field_simp
      _ ≤ phiCoefConst ^ 2 * π ^ 2 / 12 * (Real.log x ^ 6 * exp (a * Real.log x))
          / exp (Real.log x / 2) := by
          gcongr
      _ = _ := by ring

/-- `H_⌊x⌋ ≤ 2 log x + 1` for `x ≥ 1`. -/
theorem harmonic_floor_le {x : ℝ} (hx : 1 ≤ x) : (harmonic ⌊x⌋₊ : ℝ) ≤ 2 * Real.log x + 1 := by
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := Nat.one_le_cast.mpr (Nat.floor_pos.mpr hx)
  have h2 : Real.log ⌊x⌋₊ ≤ Real.log x :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have h3 := harmonic_le_one_add_log ⌊x⌋₊
  have h4 := Real.log_nonneg hx
  linarith

/-- **The profile error vanishes**: if `|b_x| ≥ b₀ x^{1/4}` and
`∫_{[0,1]}(G_x − b_x g_H)² ≤ C x^{−3/2}` eventually, then `profileErr → 0` for `a < 1/2`. -/
theorem tendsto_profileErr {a : ℝ} (ha : a < 1 / 2) (G : ℝ → ℝ → ℝ) (b : ℝ → ℝ) {b₀ C : ℝ}
    (hb₀ : 0 < b₀) (hb : ∀ᶠ x in atTop, b₀ * x ^ (1 / 4 : ℝ) ≤ |b x|)
    (hclose : ∀ᶠ x in atTop, ∫ u in Icc (0 : ℝ) 1, (G x u - b x * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2
      ≤ C * x ^ (-(3 / 2 : ℝ))) :
    Tendsto (fun x => profileErr x a (b x) (G x)) atTop (𝓝 0) := by
  set A := 4 * π ^ 4 / (1 - exp (-π)) ^ 2
  have hlim1 := (tendsto_log_pow_mul_exp 2 (p := a - 1 / 2) (by linarith)).const_mul
    (3 * C / (512 * b₀ ^ 2))
  have hlim2 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (15 / 2) (2 * π)
    (by positivity)).const_mul (2 * A)
  have hlim := hlim1.add hlim2
  rw [mul_zero, mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have := Real.log_nonneg hx
    have hI : 0 ≤ ∫ u in Icc (0 : ℝ) 1, (G x u - b x * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2 :=
      setIntegral_nonneg measurableSet_Icc fun u _ => sq_nonneg _
    have hT : 0 ≤ ∫ t in (0:ℝ)..Real.log x, Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2 :=
      intervalIntegral.integral_nonneg this fun t _ => sq_nonneg _
    unfold profileErr
    exact mul_nonneg (mul_nonneg this (exp_pos _).le) (div_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg two_pos.le (Cvs.L2a.TopCornerConstants.harmonic_nonneg _)) hI)
      (mul_nonneg (by positivity) hT)) (sq_nonneg _))
  · filter_upwards [eventually_ge_atTop (exp 1), hb, hclose] with x hx hbx hIx
    have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) hx
    have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
    have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hx4 : 4 / π ≤ x := by
      refine le_trans ?_ hx
      have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
      refine le_trans ?_ h2
      rw [div_le_iff₀ pi_pos]; linarith [pi_gt_three]
    set L := Real.log x
    set I := ∫ u in Icc (0 : ℝ) 1, (G x u - b x * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2
    set T := ∫ t in (0:ℝ)..L, Cvs.Approximant.QuarticHermiteWindowPhi.tailX x t ^ 2
    set H := (harmonic ⌊x⌋₊ : ℝ)
    set β := 32 * b x * x ^ (-(3 / 4 : ℝ))
    have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Icc fun u _ => sq_nonneg _
    have hT0 : 0 ≤ T := intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _
    have hH0 : 0 ≤ H := Cvs.L2a.TopCornerConstants.harmonic_nonneg _
    have hH := harmonic_floor_le hx1
    have hTle := Cvs.Approximant.QuarticHermiteWindowPhi.integral_tailX_sq_le_rpow hx4
    have hr : ∀ q : ℝ, x ^ q = exp (q * L) := fun q => by
      rw [Real.rpow_def_of_pos hx0, mul_comm]
    rw [hr] at hbx hIx
    -- the lower bound on `β²`
    have hb2 : b₀ ^ 2 * exp (L / 2) ≤ b x ^ 2 := by
      have h0 : 0 ≤ b₀ * exp (1 / 4 * L) := by positivity
      calc b₀ ^ 2 * exp (L / 2) = (b₀ * exp (1 / 4 * L)) ^ 2 := by
            rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
        _ ≤ |b x| ^ 2 := pow_le_pow_left₀ h0 hbx 2
        _ = b x ^ 2 := sq_abs _
    have hβ2 : 1024 * b₀ ^ 2 * exp (-L) ≤ β ^ 2 := by
      have e1 : β ^ 2 = 1024 * b x ^ 2 * exp (-(3 / 2) * L) := by
        simp only [β, hr, mul_pow, ← Real.exp_nat_mul]
        push_cast; ring_nf
      have e2 : exp (-L) = exp (L / 2) * exp (-(3 / 2) * L) := by
        rw [← Real.exp_add]; ring_nf
      rw [e1, e2]
      have := exp_pos (-(3 / 2) * L)
      nlinarith
    have hβpos : 0 < β ^ 2 := lt_of_lt_of_le (by positivity) hβ2
    -- the profile part
    have hP : 2 * H * I / β ^ 2 ≤ 3 * C / (512 * b₀ ^ 2) * L * exp (-(1 / 2) * L) := by
      have hCx : 0 ≤ C * exp (-(3 / 2) * L) := hI0.trans hIx
      calc 2 * H * I / β ^ 2 ≤ 2 * (2 * L + 1) * (C * exp (-(3 / 2) * L)) / β ^ 2 := by
            gcongr
        _ ≤ 2 * (2 * L + 1) * (C * exp (-(3 / 2) * L)) / (1024 * b₀ ^ 2 * exp (-L)) := by
            gcongr
        _ ≤ 2 * (3 * L) * (C * exp (-(3 / 2) * L)) / (1024 * b₀ ^ 2 * exp (-L)) := by
            gcongr; linarith
        _ = 3 * C / (512 * b₀ ^ 2) * L * exp (-(1 / 2) * L) := by
            have e : exp (-(3 / 2) * L) = exp (-L) * exp (-(1 / 2) * L) := by
              rw [← Real.exp_add]; ring_nf
            rw [e]; field_simp; ring
    -- the tail part
    have hT2 : L * exp (a * L) * T ≤ A * (x ^ (15 / 2 : ℝ) * exp (-(2 * π) * x)) := by
      have hL0 : 0 ≤ L := by linarith
      have hLx : L ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
      have hex : exp (a * L) ≤ x := by
        calc exp (a * L) ≤ exp L := exp_le_exp.mpr (by nlinarith)
          _ = x := Real.exp_log hx0
      have e : x ^ (15 / 2 : ℝ) = x * x * x ^ (11 / 2 : ℝ) := by
        rw [show (15 / 2 : ℝ) = 1 + 1 + 11 / 2 by norm_num, Real.rpow_add hx0, Real.rpow_add hx0,
          Real.rpow_one]
      rw [e]
      calc L * exp (a * L) * T ≤ x * x * (A * x ^ (11 / 2 : ℝ) * exp (-(2 * π * x))) := by
            gcongr
        _ = _ := by rw [neg_mul]; ring
    calc profileErr x a (b x) (G x) = L * exp (a * L) * (2 * H * I / β ^ 2 + 2 * T) := by
          show L * exp (a * L) * ((2 * H * I + 2 * β ^ 2 * T) / β ^ 2) = _
          have hβ0 : β ≠ 0 := fun h => by simp [h] at hβpos
          have e : 2 * β ^ 2 * T / β ^ 2 = 2 * T := by field_simp
          rw [add_div, e]
      _ ≤ L * exp (a * L) * (3 * C / (512 * b₀ ^ 2) * L * exp (-(1 / 2) * L) + 2 * T) := by
          gcongr
      _ = 3 * C / (512 * b₀ ^ 2) * (L ^ 2 * exp ((a - 1 / 2) * L))
          + 2 * (L * exp (a * L) * T) := by
          rw [show (a - 1 / 2) * L = a * L + -(1 / 2) * L by ring, Real.exp_add]; ring
      _ ≤ _ := by linarith

/-! ### Strip approximability from profile closeness -/

/-- **Strip approximability from profile closeness**: profiles eventually continuous on `[0, 1]`
with `∫_{[0,1]}(G x − b x·g_H)² ≤ C x^{−3/2}`, `|b x| ≥ b₀ x^{1/4}`, give strip approximable
normalised coefficient vectors for every truncation with `N x ≥ x^{1/4}` eventually. -/
theorem stripApproximable_profileVec (N : ℝ → ℕ) (G : ℝ → ℝ → ℝ) (b : ℝ → ℝ) {b₀ C : ℝ}
    (hb₀ : 0 < b₀) (hGc : ∀ᶠ x in atTop, ContinuousOn (G x) (Icc 0 1))
    (hb : ∀ᶠ x in atTop, b₀ * x ^ (1 / 4 : ℝ) ≤ |b x|)
    (hclose : ∀ᶠ x in atTop, ∫ u in Icc (0 : ℝ) 1, (G x u - b x * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2
      ≤ C * x ^ (-(3 / 2 : ℝ)))
    (hN : ∀ᶠ x in atTop, x ^ (1 / 4 : ℝ) ≤ N x) :
    Cvs.Route.GroundRouteJointGap.StripApproximable N (profileVec N G) := by
  classical
  refine ⟨fun x i => unitVec_even (coeff_even _ _ _) i, fun x => unitVec_dotProduct_self _, ?_⟩
  set β : ℝ → ℝ := fun x => 32 * b x * x ^ (-(3 / 4 : ℝ)) with hβdef
  set ξ : ∀ x, Idx (N x) → ℝ := fun x => profileCoef G x (N x) with hξdef
  set err : ℝ → ℝ → ℝ := fun a x =>
    2 * √(profileErr x a (b x) (G x)) + 2 * √(truncErr x a (N x)) + windowErr x a
  have herr : ∀ a, a < 1 / 2 → Tendsto (err a) atTop (𝓝 0) := by
    intro a ha
    have h1 := ((Real.continuous_sqrt.tendsto 0).comp
      (tendsto_profileErr ha G b hb₀ hb hclose)).const_mul 2
    have h2 := ((Real.continuous_sqrt.tendsto 0).comp (tendsto_truncErr ha hN)).const_mul 2
    have h3 := tendsto_windowErr (a := a) (by linarith)
    have h := (h1.add h2).add h3
    simp only [Real.sqrt_zero, mul_zero, add_zero] at h
    exact h
  -- the estimate at every good scale
  have hest : ∀ᶠ x in atTop, β x ≠ 0 ∧ (∀ a < 1, ∀ z : ℂ, |z.im| ≤ a →
      ‖((2 / β x : ℝ) : ℂ) * Cvs.Route.GroundRouteJointGap.ctransform (Real.log x) (N x) (ξ x) z - Cvs.Limit.ZeroFreeApproximantsRH.Xi z‖
        ≤ err a x) ∧ ξ x ⬝ᵥ ξ x / β x ^ 2 ≤ 2 * profileErr x 0 (b x) (G x) + 2 * phiMax ^ 2 := by
    filter_upwards [eventually_ge_atTop (exp 1), hGc, hb] with x hx hc hbx
    have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) hx
    have hb0 : 0 < |b x| := lt_of_lt_of_le (by positivity) hbx
    have hβ : β x ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (abs_pos.mp hb0))
      (Real.rpow_pos_of_pos hx0 _).ne'
    exact ⟨hβ, fun a ha z hz => norm_two_div_mul_ctransform_sub_Xi_le hx rfl hβ hc (N x) ha hz,
      dotProduct_div_sq_le hx hβ hc (N x)⟩
  -- the coefficient vector is eventually nonzero, since `Ξ(0) ≠ 0`
  have hXi : 0 < ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ := norm_pos_iff.mpr fun h => by
    have := Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hne : ∀ᶠ x in atTop, ξ x ⬝ᵥ ξ x ≠ 0 := by
    filter_upwards [hest, (herr 0 (by norm_num)).eventually (gt_mem_nhds hXi)]
      with x ⟨_, h, _⟩ hlt h0
    have hz := h 0 (by norm_num) 0 (by simp)
    rw [dotProduct_self_eq_zero.mp h0, Cvs.Approximant.ConnesVectorRealScale.ctransform_zero, mul_zero, zero_sub,
      norm_neg] at hz
    linarith
  have hsmall : ∀ᶠ x in atTop, profileErr x 0 (b x) (G x) ≤ 1 :=
    (tendsto_profileErr (a := 0) (by norm_num) G b hb₀ hb hclose).eventually
      (ge_mem_nhds one_pos)
  -- the scale
  set S₀ : ℝ := 2 * √(2 + 2 * phiMax ^ 2)
  set s : ℝ → ℝ := fun x =>
    if ξ x ⬝ᵥ ξ x ≠ 0 ∧ β x ≠ 0 ∧ |2 * √(ξ x ⬝ᵥ ξ x) / β x| ≤ S₀
    then 2 * √(ξ x ⬝ᵥ ξ x) / β x else 1 with hsdef
  have hgood : ∀ᶠ x in atTop, ξ x ⬝ᵥ ξ x ≠ 0 ∧ β x ≠ 0 ∧ |2 * √(ξ x ⬝ᵥ ξ x) / β x| ≤ S₀ := by
    filter_upwards [hest, hne, hsmall] with x ⟨hβ, _, hq⟩ hn hp
    refine ⟨hn, hβ, ?_⟩
    rw [abs_div, abs_mul, abs_two, abs_of_nonneg (Real.sqrt_nonneg _), mul_div_assoc,
      ← Real.sqrt_sq_eq_abs, ← Real.sqrt_div' _ (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) two_pos.le
  refine ⟨s, max S₀ 1, fun x => ?_, fun x => ?_, ?_⟩
  · simp only [hsdef]
    split_ifs with h
    · exact div_ne_zero (mul_ne_zero two_ne_zero (Real.sqrt_ne_zero'.mpr
        (lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm h.1))))
        h.2.1
    · exact one_ne_zero
  · simp only [hsdef]
    split_ifs with h
    · exact h.2.2.trans (le_max_left _ _)
    · rw [abs_one]; exact le_max_right _ _
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Cvs.Limit.CriticalStripOffAxes.isOpen_criticalOffAxes]
  intro A hAs hA
  obtain ⟨a, -, ha, hAa⟩ := Cvs.Route.JointGapStripLimit.exists_abs_im_le_of_isCompact hA hAs
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hest, hgood, (herr a ha).eventually (gt_mem_nhds hε)]
    with x ⟨_, h, _⟩ hg hlt z hz
  have hs : s x = 2 * √(ξ x ⬝ᵥ ξ x) / β x := if_pos hg
  have hv : profileVec N G x = (√(ξ x ⬝ᵥ ξ x))⁻¹ • ξ x := if_neg hg.1
  have hq : (√(ξ x ⬝ᵥ ξ x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr
    (lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm hg.1)))
  have hβc : (β x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg.2.1
  rw [dist_comm, dist_eq_norm, hs, hv, Cvs.Route.GroundRouteJointGap.ctransform_smul]
  have e : ((2 * √(ξ x ⬝ᵥ ξ x) / β x : ℝ) : ℂ)
      * (((√(ξ x ⬝ᵥ ξ x))⁻¹ : ℝ) * Cvs.Route.GroundRouteJointGap.ctransform (Real.log x) (N x) (ξ x) z)
      = ((2 / β x : ℝ) : ℂ) * Cvs.Route.GroundRouteJointGap.ctransform (Real.log x) (N x) (ξ x) z := by
    push_cast
    field_simp
  rw [e]
  exact (h a (by linarith) z (hAa z hz)).trans_lt hlt

/-- **The explicit truncation threshold `N₀ x = ⌈x^{1/4}⌉`**: under the same closeness, every
truncation eventually at least `N₀` gives strip approximable normalised coefficient vectors. -/
theorem stripApproximable_profileVec_of_ceil_le (N : ℝ → ℕ) (G : ℝ → ℝ → ℝ) (b : ℝ → ℝ)
    {b₀ C : ℝ} (hb₀ : 0 < b₀) (hGc : ∀ᶠ x in atTop, ContinuousOn (G x) (Icc 0 1))
    (hb : ∀ᶠ x in atTop, b₀ * x ^ (1 / 4 : ℝ) ≤ |b x|)
    (hclose : ∀ᶠ x in atTop, ∫ u in Icc (0 : ℝ) 1, (G x u - b x * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2
      ≤ C * x ^ (-(3 / 2 : ℝ)))
    (hN : ∀ᶠ x in atTop, ⌈x ^ (1 / 4 : ℝ)⌉₊ ≤ N x) :
    Cvs.Route.GroundRouteJointGap.StripApproximable N (profileVec N G) :=
  stripApproximable_profileVec N G b hb₀ hGc hb hclose
    (hN.mono fun _ h => (Nat.le_ceil _).trans (by exact_mod_cast h))

end Cvs.Approximant.StripApproxFromHermite
