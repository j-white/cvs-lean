import Mathlib
import Cvs.Approximant.ConnesEndpointGeometry
import Cvs.Approximant.ConnesLowModeGeometry
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.RecentredTransform
import Cvs.Finite.RecentredTransformClosed
import Cvs.Finite.RecentredTransformEven
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Limit.OffAxesLimit
import Cvs.Route.GroundRouteJointGap
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Exact mass shifts and signed three-mode filters

The Connes endpoint-flat filter is zero-free off the axes. Linear one-cell shifts
produce the physical mass diagonal; paired complex-square channels have signed Gram determinants.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Real Matrix Finset Filter Set MeasureTheory
open scoped Topology
namespace Cvs.Approximant.ThreeModeMassShiftFilters
open Cvs.ZeroCounting
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Approximant.ConnesEndpointGeometry

/-- Signed coefficients of the polynomial with unsigned amplitudes `A, B, C`. -/
def profileCoeffs (N : ℕ) (A B C : ℝ) : Idx N → ℝ :=
  Cvs.Approximant.ConnesEndpointGeometry.threeMode N A (B/2) (C/2)

/-- The endpoint-flat rational numerator after removing the three frequency poles. -/
def affineNumerator (L A B : ℝ) (z : ℂ) : ℂ :=
  ((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)^2*
    (((-4*A-3*B : ℝ) : ℂ)*z^2+((4*A : ℝ) : ℂ)*
      ((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)^2)

theorem profileCoeffs_even (N : ℕ) (A B C : ℝ) (i : Idx N) :
    profileCoeffs N A B C (negI N i)=profileCoeffs N A B C i :=
  Cvs.Approximant.ConnesEndpointGeometry.threeMode_even _ _ _ _ _

theorem profileCoeffs_mass {N : ℕ} (hN : 2≤N) (A B C : ℝ) :
    profileCoeffs N A B C ⬝ᵥ profileCoeffs N A B C=A^2+B^2/2+C^2/2 := by
  rw [profileCoeffs,Cvs.Approximant.ConnesEndpointGeometry.threeMode_mass hN]
  ring

theorem profileCoeffs_endpoint {N : ℕ} (hN : 2≤N) (A B C : ℝ) :
    Cvs.Approximant.ConnesEndpointGeometry.endpoint N (profileCoeffs N A B C)=A+B+C := by
  rw [profileCoeffs,Cvs.Approximant.ConnesEndpointGeometry.threeMode_endpoint hN]
  ring

/-- The actual three-mode rational factor groups the two signed copies of each nonzero frequency. -/
theorem S_profileCoeffs {N : ℕ} (hN : 2≤N) (L A B C : ℝ) (z : ℂ) :
    Cvs.Finite.UniversalFunctionPairing.S L (mode N) (profileCoeffs N A B C) z=
      (A : ℂ)/(-z^2)+(B : ℂ)/(((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)^2-z^2)+
      (C : ℂ)/(4*((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)^2-z^2) := by
  obtain ⟨N,rfl⟩ : ∃ K,N=Nat.succ (Nat.succ K) := ⟨N-2,by omega⟩
  simp [Cvs.Finite.UniversalFunctionPairing.S,profileCoeffs,Cvs.Approximant.ConnesEndpointGeometry.threeMode,Fintype.sum_option,
    Fintype.sum_prod_type,Fin.sum_univ_succ,mode,Cvs.Approximant.ConnesEndpointGeometry.frequency]
  ring_nf

private theorem sq_im_ne_zero {z : ℂ} (hz : z∈Cvs.Limit.OffAxesLimit.offAxes) : (z^2).im≠0 :=
  fun h => Cvs.Limit.OffAxesLimit.notMem_offAxes_of_sq_im h hz

private theorem real_sub_sq_ne_zero (q : ℝ) {z : ℂ} (hz : z∈Cvs.Limit.OffAxesLimit.offAxes) :
    (q : ℂ)-z^2≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im] at hi
  exact sq_im_ne_zero hz (by linarith)

private theorem partial_fraction_flat (A B C q t : ℂ) (he : A+B+C=0)
    (ht : t≠0) (h1 : q-t≠0) (h2 : 4*q-t≠0) :
    A/(-t)+B/(q-t)+C/(4*q-t)=
      q*((-4*A-3*B)*t+4*A*q)/((-t)*(q-t)*(4*q-t)) := by
  have h2' : q*4-t≠0 := by simpa only [mul_comm] using h2
  field_simp [ht,h1,h2,h2']
  linear_combination t*(q-t)*he

/-- Endpoint cancellation reduces the actual rational numerator to a real affine function of `z²`. -/
theorem S_profileCoeffs_flat {L : ℝ} {N : ℕ} (hN : 2≤N)
    (A B C : ℝ) (he : A+B+C=0) {z : ℂ} (hz : z∈Cvs.Limit.OffAxesLimit.offAxes) :
    Cvs.Finite.UniversalFunctionPairing.S L (mode N) (profileCoeffs N A B C) z=
      affineNumerator L A B z/
        ((-z^2)*(((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)^2-z^2)*
          (4*((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)^2-z^2)) := by
  rw [S_profileCoeffs hN]
  have hz0 : z≠0 := by intro h; exact hz.1 (by simp [h])
  have hd1 : ((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)^2-z^2≠0 := by
    rw [←Complex.ofReal_pow]
    exact real_sub_sq_ne_zero ((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1)^2) hz
  have hd2 : 4*((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)^2-z^2≠0 := by
    rw [←Complex.ofReal_pow]
    change ((4 : ℝ) : ℂ)*((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1)^2 : ℝ)-z^2≠0
    rw [←Complex.ofReal_mul]
    exact real_sub_sq_ne_zero (4*(Cvs.Approximant.ConnesEndpointGeometry.frequency L 1)^2) hz
  have he' : (A : ℂ)+(B : ℂ)+(C : ℂ)=0 := by exact_mod_cast he
  simpa only [affineNumerator,Complex.ofReal_sub,Complex.ofReal_neg,
    Complex.ofReal_mul,Complex.ofReal_ofNat] using
    partial_fraction_flat (A : ℂ) (B : ℂ) (C : ℂ)
      (((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)^2) (z^2) he' (pow_ne_zero 2 hz0) hd1 hd2

/-- A nonzero endpoint-flat three-mode profile has a nonvanishing rational numerator off the axes. -/
theorem affineNumerator_ne_zero {L : ℝ} (hL : 0<L) (A B C : ℝ)
    (he : A+B+C=0) (hne : A≠0 ∨ B≠0 ∨ C≠0) {z : ℂ} (hz : z∈Cvs.Limit.OffAxesLimit.offAxes) :
    affineNumerator L A B z≠0 := by
  have hw : Cvs.Approximant.ConnesEndpointGeometry.frequency L 1≠0 := (Cvs.Approximant.ConnesEndpointGeometry.frequency_pos hL (by norm_num : 0<1)).ne'
  have hwc : ((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1 : ℝ) : ℂ)≠0 := by exact_mod_cast hw
  intro hn
  unfold affineNumerator at hn
  have hb := (mul_eq_zero.mp hn).resolve_left (pow_ne_zero 2 hwc)
  have hi := congrArg Complex.im hb
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,add_zero,←Complex.ofReal_pow,Complex.zero_im] at hi
  have hk : -4*A-3*B=0 := (mul_eq_zero.mp hi).resolve_right (sq_im_ne_zero hz)
  have ha : A=0 := by
    rw [hk,Complex.ofReal_zero,zero_mul,zero_add] at hb
    have hA : (4*A : ℝ)=0 := by
      have hAc := (mul_eq_zero.mp hb).resolve_right (pow_ne_zero 2 hwc)
      exact_mod_cast hAc
    linarith
  have hB : B=0 := by linarith
  have hC : C=0 := by linarith
  rcases hne with h | h | h <;> contradiction

/-- Every nonzero endpoint-flat three-mode rational factor is zero-free off the axes. -/
theorem S_profileCoeffs_ne_zero {L : ℝ} (hL : 0<L) {N : ℕ} (hN : 2≤N)
    (A B C : ℝ) (he : A+B+C=0) (hne : A≠0 ∨ B≠0 ∨ C≠0)
    {z : ℂ} (hz : z∈Cvs.Limit.OffAxesLimit.offAxes) :
    Cvs.Finite.UniversalFunctionPairing.S L (mode N) (profileCoeffs N A B C) z≠0 := by
  rw [S_profileCoeffs_flat hN A B C he hz]
  exact div_ne_zero (affineNumerator_ne_zero hL A B C he hne hz)
    (mul_ne_zero (mul_ne_zero (by simpa using real_sub_sq_ne_zero 0 hz)
      (by rw [←Complex.ofReal_pow]; exact real_sub_sq_ne_zero ((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1)^2) hz))
      (by rw [←Complex.ofReal_pow]
          change ((4 : ℝ) : ℂ)*((Cvs.Approximant.ConnesEndpointGeometry.frequency L 1)^2 : ℝ)-z^2≠0
          rw [←Complex.ofReal_mul]
          exact real_sub_sq_ne_zero (4*(Cvs.Approximant.ConnesEndpointGeometry.frequency L 1)^2) hz))

/-- The actual centered transform of a nonzero endpoint-flat three-mode profile cannot vanish off the axes. -/
theorem ctransform_profileCoeffs_ne_zero {L : ℝ} (hL : 0<L) {N : ℕ} (hN : 2≤N)
    (A B C : ℝ) (he : A+B+C=0) (hne : A≠0 ∨ B≠0 ∨ C≠0)
    {z : ℂ} (hz : z∈Cvs.Limit.OffAxesLimit.offAxes) :
    Cvs.Route.GroundRouteJointGap.ctransform L N (profileCoeffs N A B C) z≠0 := by
  have hsin : Complex.sin (z*(L : ℂ)/2)≠0 := by
    intro hs
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hi := congrArg Complex.im hk
    simp only [Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,Complex.intCast_im] at hi
    have hzL : z.im*L=0 := by simpa using hi
    exact hz.2 ((mul_eq_zero.mp hzL).resolve_right hL.ne')
  have hz0 : z≠0 := by intro h; exact hz.1 (by simp [h])
  unfold Cvs.Route.GroundRouteJointGap.ctransform Cvs.Finite.RecentredTransform.phase
  rw [Cvs.Finite.RecentredTransformClosed.centred_fourierLaplace_eq_sin hL (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) (profileCoeffs_even _ _ _ _) (fun i => Cvs.Finite.RecentredTransformEven.omega_add_ne_zero hz i)]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hz0) hsin)
    (S_profileCoeffs_ne_zero hL hN A B C he hne hz)

/-- The actual nonzero Connes endpoint-flat residual cannot annihilate any off-axis point. -/
theorem ctransform_flatVector_ne_zero {x : ℝ} (hx : 1<x) {N : ℕ} (hN : 2≤N)
    (hC : Cvs.Approximant.ConnesLowModeGeometry.coef x 1-2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0≠0) {z : ℂ} (hz : z∈Cvs.Limit.OffAxesLimit.offAxes) :
    Cvs.Route.GroundRouteJointGap.ctransform (log x) N (Cvs.Approximant.ConnesEndpointGeometry.flatVector x N) z≠0 := by
  apply ctransform_profileCoeffs_ne_zero (log_pos hx) hN
    (Cvs.Approximant.ConnesLowModeGeometry.coef x 2-Cvs.Approximant.ConnesLowModeGeometry.coef x 1)
    (2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0-Cvs.Approximant.ConnesLowModeGeometry.coef x 2)
    (Cvs.Approximant.ConnesLowModeGeometry.coef x 1-2*Cvs.Approximant.ConnesLowModeGeometry.coef x 0)
  · ring
  · exact Or.inr (Or.inr hC)
  · exact hz

/-- At all sufficiently large actual scales the Connes endpoint-flat residual is zero-free off the axes. -/
theorem eventually_ctransform_flatVector_ne_zero :
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,2≤N → ∀ z∈Cvs.Limit.OffAxesLimit.offAxes,
      Cvs.Route.GroundRouteJointGap.ctransform (log x) N (Cvs.Approximant.ConnesEndpointGeometry.flatVector x N) z≠0 := by
  filter_upwards [eventually_gt_atTop 1,Cvs.Approximant.ConnesLowModeGeometry.eventually_perpendicular_endpoint_ne_zero]
    with x hx hC N hN z hz
  exact ctransform_flatVector_ne_zero hx hN hC hz

private theorem sin_frequency_end {L : ℝ} (hL : 0<L) (n : ℕ) :
    Real.sin (frequency L n*L)=0 := by
  rw [frequency_mul_length hL]
  simpa using Cvs.Finite.CosineModeOverlap.sin_two_pi_int_sub (n:ℤ) 0

private theorem cos_frequency_end {L : ℝ} (hL : 0<L) (n : ℕ) :
    Real.cos (frequency L n*L)=1 := by
  rw [frequency_mul_length hL]
  simpa only [sub_zero, Real.cos_zero, mul_comm, mul_left_comm, mul_assoc] using
    Real.cos_nat_mul_two_pi_sub (0:ℝ) n

/-- The cosine convolution at the full window is its physical mass entry. -/
theorem cosineConv_end {L : ℝ} (hL : 0<L) (m n : ℕ) :
    cosineConv L m n L = if m=n then if m=0 then L else L/2 else 0 := by
  unfold cosineConv
  split_ifs <;> simp [sin_frequency_end hL, cos_frequency_end hL]

/-- The curvature matrix at the full window is diagonal and nonpositive. -/
theorem cosineCurvature_end {L : ℝ} (hL : 0<L) (m n : ℕ) :
    cosineCurvature L m n L = if m=n then -(frequency L m)^2*L/2 else 0 := by
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0
    · subst m
      simp [cosineCurvature, frequency]
    · simp [cosineCurvature, hm, sin_frequency_end hL, cos_frequency_end hL]
      ring
  · simp [cosineCurvature, hmn, sin_frequency_end hL]

/-- The linear one-cell function produces the physical cosine mass matrix. -/
theorem cosineVolterra_id {L : ℝ} (hL : 0<L) (m n : ℕ) :
    cosineVolterra L m n (fun t => t) =
      if m=n then if m=0 then L else L/2 else 0 := by
  rw [←cosineConv_end hL m n, cosineConv_eq_ramp_integral hL m n L]
  unfold cosineVolterra
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  ring

/-- Subtracting a linear one-cell function shifts exactly the physical mass diagonal. -/
theorem cosineVolterra_sub_linear {L : ℝ} (hL : 0<L) (m n : ℕ) (V : ℝ→ℝ)
    (hV : IntervalIntegrable (fun d => cosineCurvature L m n d*V (L-d)) volume 0 L)
    (μ : ℝ) :
    cosineVolterra L m n (fun t => V t-μ*t) = cosineVolterra L m n V -
      μ*(if m=n then if m=0 then L else L/2 else 0) := by
  have hi : IntervalIntegrable (fun d => μ*(cosineCurvature L m n d*(L-d))) volume 0 L :=
    (continuous_const.mul ((continuous_cosineCurvature L m n).mul
      (continuous_const.sub continuous_id))).intervalIntegrable 0 L
  rw [←cosineVolterra_id hL m n]
  unfold cosineVolterra
  have he : (fun d => cosineCurvature L m n d*(V (L-d)-μ*(L-d)))=
      (fun d => cosineCurvature L m n d*V (L-d)-μ*(cosineCurvature L m n d*(L-d))) := by
    funext d
    ring
  rw [he, intervalIntegral.integral_sub hV hi, intervalIntegral.integral_const_mul]
  ring

/-- The paired complex-square form has a nonpositive two-vector Gram determinant. -/
theorem paired_square_gram_det (c u v : ℂ) :
    (c*u^2).re*(c*v^2).re-(c*u*v).re^2 =
      -Complex.normSq c*((starRingEnd ℂ u*v).im)^2 := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

/-- Two real-independent evaluations give a strictly indefinite paired Gram. -/
theorem paired_square_gram_det_neg {c u v : ℂ} (hc : c≠0)
    (huv : (starRingEnd ℂ u*v).im≠0) :
    (c*u^2).re*(c*v^2).re-(c*u*v).re^2<0 := by
  rw [paired_square_gram_det]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Complex.normSq_pos.mpr hc))
    (sq_pos_of_ne_zero huv)

/-- Every nonconstant diagonal mode has strictly negative curvature at full separation. -/
theorem cosineCurvature_diag_end_neg {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 0 < m) :
    cosineCurvature L m m L < 0 := by
  rw [cosineCurvature_end hL, if_pos rfl]
  have hp : 0 < (frequency L m)^2 := sq_pos_of_pos (frequency_pos hL hm)
  nlinarith

end Cvs.Approximant.ThreeModeMassShiftFilters
