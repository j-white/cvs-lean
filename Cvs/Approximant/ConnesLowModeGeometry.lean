import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.QuarticHermiteWindowPhi
import Cvs.Approximant.SpineNearQuarticHermite
import Cvs.Approximant.StripApproxFromHermite
import Cvs.Finite.CoefficientsAreSamples
import Cvs.Finite.RecentredTransform
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TwoModeLowHeadDamping
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.MobiusReconstruction
import Cvs.Xi.XiValueAtOrigin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Connes low-mode geometry and unique arithmetic preimages

The first two Connes coefficients determine their perpendicular profile,
and finite Möbius inversion recovers the input on the sampled interval.
-/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace Cvs.Approximant.ConnesLowModeGeometry
open Cvs.ZeroCounting

/-- The actual unsigned cosine coefficients at a real scale. -/
def coef (x : ℝ) (n : ℕ) : ℝ := Cvs.Finite.WindowCosineBessel.coef (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) n

/-- The first centered grid sample has the negative half-coefficient phase. -/
theorem ctransform_first_evaluation {L : ℝ} (hL : 0<L) {N : ℕ} (hN : 0<N)
    (ξ : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) (hξ : ∀ i, ξ (Cvs.Finite.SymmetricModeSet.negI N i)=ξ i) :
    Cvs.Route.GroundRouteJointGap.ctransform L N ξ ((2*π/L : ℝ) : ℂ) =
      -((L : ℂ)*(ξ (some (⟨0,hN⟩,true)) : ℂ)) := by
  have hg := Cvs.Finite.CoefficientsAreSamples.centred_at_grid hL (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) (Cvs.Finite.SymmetricModeSet.mode_injective N) hξ (some (⟨0,hN⟩,true))
  simpa [Cvs.Route.GroundRouteJointGap.ctransform, Cvs.Finite.RecentredTransform.phase, Cvs.Finite.SymmetricModeSet.mode, Cvs.Finite.TruncationZeroFreeOffAxes.omega] using hg

/-- Either signed first Connes coordinate is half the unsigned coefficient. -/
theorem connesCoef_first (x : ℝ) {N : ℕ} (hN : 0<N) (b : Bool) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x N (some (⟨0,hN⟩,b))=coef x 1/2 := by
  simp [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, coef, hN]

private def beta (x : ℝ) : ℝ :=
  32*(Cvs.Approximant.SpineNearQuarticHermite.overlap (2*π*x))⁻¹*x ^ (-(3/4 : ℝ))

private def error (x : ℝ) : ℝ :=
  2*√(Cvs.Approximant.StripApproxFromHermite.profileErr x 0 ((Cvs.Approximant.SpineNearQuarticHermite.overlap (2*π*x))⁻¹)
      (Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1))+
    2*√(Cvs.Approximant.StripApproxFromHermite.truncErr x 0 (Cvs.Route.JointGapAtConnesVectors.connesThreshold x+1))+Cvs.Approximant.StripApproxFromHermite.windowErr x 0

private theorem eventually_beta_ne_zero : ∀ᶠ x : ℝ in atTop, beta x≠0 := by
  filter_upwards [eventually_ge_atTop 16] with x hx
  have hx0 : 0<x := by linarith
  have hb := Cvs.Approximant.SpineNearQuarticHermite.le_abs_inv_overlap hx
  have hb0 : 0 < |(Cvs.Approximant.SpineNearQuarticHermite.overlap (2*π*x))⁻¹| :=
    lt_of_lt_of_le (by positivity) hb
  exact mul_ne_zero (mul_ne_zero (by norm_num) (abs_pos.mp hb0))
    (rpow_pos_of_pos hx0 _).ne'

private theorem tendsto_error : Tendsto error atTop (𝓝 0) := by
  let G : ℝ → ℝ → ℝ := fun x => Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1
  let b : ℝ → ℝ := fun x => (Cvs.Approximant.SpineNearQuarticHermite.overlap (2*π*x))⁻¹
  have hb : ∀ᶠ x : ℝ in atTop, 1/20*x ^ (1/4 : ℝ) ≤ |b x| := by
    filter_upwards [eventually_ge_atTop 16] with x hx
    exact Cvs.Approximant.SpineNearQuarticHermite.le_abs_inv_overlap hx
  have hclose : ∀ᶠ x : ℝ in atTop,
      ∫ u in Icc (0 : ℝ) 1, (G x u-b x*Cvs.Approximant.QuarticHermiteWindowPhi.gH (2*π*x) u)^2
        ≤ 80217/4*x ^ (-(3/2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 16] with x hx
    exact Cvs.Approximant.SpineNearQuarticHermite.integral_spineG_sub_sq_le_rpow hx
  have hNr : ∀ᶠ x : ℝ in atTop,
      x ^ (1/4 : ℝ) ≤ (Cvs.Route.JointGapAtConnesVectors.connesThreshold x+1 : ℕ) := by
    exact Eventually.of_forall fun x => (Nat.le_ceil _).trans (by
      dsimp [Cvs.Route.JointGapAtConnesVectors.connesThreshold]
      norm_cast
      omega)
  have hp := Cvs.Approximant.StripApproxFromHermite.tendsto_profileErr (a := 0) (by norm_num) G b
    (b₀ := 1/20) (C := 80217/4) (by norm_num) hb hclose
  have ht := Cvs.Approximant.StripApproxFromHermite.tendsto_truncErr (a := 0) (by norm_num) hNr
  have hw := Cvs.Approximant.StripApproxFromHermite.tendsto_windowErr (a := 0) (by norm_num)
  have h1 := ((continuous_sqrt.tendsto 0).comp hp).const_mul 2
  have h2 := ((continuous_sqrt.tendsto 0).comp ht).const_mul 2
  change Tendsto (fun x => error x) atTop (𝓝 0)
  simpa only [error, G, b, Function.comp_apply, sqrt_zero, mul_zero, add_zero]
    using (h1.add h2).add hw

private theorem scaled_transform_tendsto (z : ℝ → ℝ)
    (hz : Tendsto z atTop (𝓝 0)) :
    Tendsto (fun x => ((2/beta x : ℝ) : ℂ)*Cvs.Route.GroundRouteJointGap.ctransform (log x)
      (Cvs.Route.JointGapAtConnesVectors.connesThreshold x+1) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x (Cvs.Route.JointGapAtConnesVectors.connesThreshold x+1))
      ((z x : ℝ) : ℂ)) atTop (𝓝 (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0)) := by
  have hest : ∀ᶠ x : ℝ in atTop,
      ‖((2/beta x : ℝ) : ℂ)*Cvs.Route.GroundRouteJointGap.ctransform (log x)
        (Cvs.Route.JointGapAtConnesVectors.connesThreshold x+1) (Cvs.Approximant.ConnesVectorRealScale.connesCoef x (Cvs.Route.JointGapAtConnesVectors.connesThreshold x+1))
        ((z x : ℝ) : ℂ)-Cvs.Limit.ZeroFreeApproximantsRH.Xi ((z x : ℝ) : ℂ)‖≤error x := by
    filter_upwards [eventually_ge_atTop (exp 1), eventually_beta_ne_zero] with x hx hβ
    have hc : ContinuousOn (Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1)
        (Icc 0 1) :=
      (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)
    exact Cvs.Approximant.StripApproxFromHermite.norm_two_div_mul_ctransform_sub_Xi_le hx rfl hβ hc _
      (a := 0) (by norm_num) (z := ((z x : ℝ) : ℂ)) (by simp)
  have he := squeeze_zero_norm' hest tendsto_error
  have hX := (Cvs.Limit.ZeroFreeApproximantsRH.differentiable_Xi.continuous.tendsto 0).comp
    (Complex.continuous_ofReal.tendsto 0 |>.comp hz)
  have h := he.add hX
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using h

private theorem tendsto_scaled_zero :
    Tendsto (fun x : ℝ => 2*log x*coef x 0/beta x) atTop
      (𝓝 (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0).re) := by
  have h := Complex.continuous_re.tendsto (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0) |>.comp
    (scaled_transform_tendsto (fun _ => 0) tendsto_const_nhds)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hL : 0<log x := log_pos ((one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx)
  simp only [Function.comp_apply, Complex.ofReal_zero]
  rw [Cvs.Approximant.ConnesCoefficientsNonvanishing.ctransform_zero_evaluation hL _ _ (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even _ _),
    Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none]
  simp only [Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, coef]
  ring

private theorem tendsto_scaled_first :
    Tendsto (fun x : ℝ => -(log x*coef x 1/beta x)) atTop
      (𝓝 (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0).re) := by
  have hω : Tendsto (fun x : ℝ => 2*π/log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := Complex.continuous_re.tendsto (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0) |>.comp
    (scaled_transform_tendsto (fun x => 2*π/log x) hω)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hL : 0<log x := log_pos ((one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx)
  simp only [Function.comp_apply]
  rw [ctransform_first_evaluation hL (Nat.zero_lt_succ _) _ (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even _ _),
    connesCoef_first]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, mul_zero, sub_zero]
  ring

/-- The actual first-to-constant cosine coefficient ratio tends to minus one. -/
theorem tendsto_first_ratio :
    Tendsto (fun x : ℝ => coef x 1/(2*coef x 0)) atTop (𝓝 (-1)) := by
  have hXi : (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0).re≠0 := ne_of_gt Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
  have h := (tendsto_scaled_first.div tendsto_scaled_zero hXi).neg
  simp only [div_self hXi] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (exp 1), eventually_beta_ne_zero,
    Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_connes_constantCoef_ne_zero] with x hx hβ ha
  have hL : log x≠0 := (log_pos
    ((one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx)).ne'
  have ha' : coef x 0≠0 := ha
  simp only [Pi.div_apply]
  field_simp [hβ, hL, ha']

/-- The actual first Connes cosine coefficient is eventually nonzero. -/
theorem eventually_first_ne_zero : ∀ᶠ x : ℝ in atTop, coef x 1≠0 := by
  filter_upwards [tendsto_first_ratio.eventually (gt_mem_nhds (by norm_num : (-1 : ℝ)<0))]
    with x hx hz
  simp only [hz, zero_div] at hx
  exact lt_irrefl 0 hx

/-- The actual two-mode perpendicular test normalized by its constant coefficient. -/
def perpendicularProfile (x s : ℝ) : ℝ :=
  Real.cos (2*π/log x*s)-coef x 1/(2*coef x 0)

/-- The normalized actual perpendicular test tends to zero at the window center. -/
theorem tendsto_perpendicular_center :
    Tendsto (fun x : ℝ => perpendicularProfile x (log x/2)) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (-1 : ℝ))).sub tendsto_first_ratio
  have hh : Tendsto (fun x : ℝ => (-1 : ℝ)-coef x 1/(2*coef x 0)) atTop (𝓝 0) := by
    simpa using h
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hL : log x≠0 := (log_pos
    ((one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx)).ne'
  have he : 2*π/log x*(log x/2)=π := by field_simp
  simp only [perpendicularProfile, he, Real.cos_pi]

/-- The normalized actual perpendicular test tends to two at either endpoint. -/
theorem tendsto_perpendicular_endpoint :
    Tendsto (fun x : ℝ => perpendicularProfile x 0) atTop (𝓝 2) := by
  have h : Tendsto (fun x : ℝ => 1-coef x 1/(2*coef x 0)) atTop (𝓝 2) := by
    convert ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_first_ratio) using 1
    norm_num
  simpa only [perpendicularProfile, mul_zero, Real.cos_zero] using h

/-- The two endpoint values of the normalized actual perpendicular test agree. -/
theorem perpendicular_endpoints {x : ℝ} (hx : 1<x) :
    perpendicularProfile x (log x)=perpendicularProfile x 0 := by
  have hL : log x≠0 := (log_pos hx).ne'
  have he : 2*π/log x*log x=2*π := by field_simp
  simp only [perpendicularProfile, he, mul_zero, Real.cos_zero, Real.cos_two_pi]

/-- The rescaled actual perpendicular profile has a constant shape error. -/
theorem perpendicular_rescaled_shape {x : ℝ} (hx : 1<x) (s : ℝ) :
    perpendicularProfile x (log x*s)-(1+Real.cos (2*π*s))=
      -(coef x 1/(2*coef x 0)+1) := by
  have hL : log x≠0 := (log_pos hx).ne'
  have he : 2*π/log x*(log x*s)=2*π*s := by field_simp
  rw [perpendicularProfile, he]
  ring

/-- The normalized two-mode coefficients are perpendicular to the actual Connes normal. -/
theorem perpendicular_coeff_orthogonal (x : ℝ) {N : ℕ} (hN : 0<N)
    (h0 : coef x 0≠0) :
    Cvs.WeilForm.TwoModeLowHeadDamping.twoMode N (-(coef x 1/(2*coef x 0))) (1/2) ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N=0 := by
  rw [Cvs.WeilForm.TwoModeLowHeadDamping.twoMode_pair hN, Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none,
    connesCoef_first x hN true, connesCoef_first x hN false]
  change -(coef x 1/(2*coef x 0))*coef x 0+(1/2)*(coef x 1/2+coef x 1/2)=0
  field_simp
  ring

/-- The unnormalized actual perpendicular test is eventually nonzero at its endpoints. -/
theorem eventually_perpendicular_endpoint_ne_zero :
    ∀ᶠ x : ℝ in atTop, coef x 1-2*coef x 0≠0 := by
  filter_upwards [tendsto_first_ratio.eventually (gt_mem_nhds (by norm_num : (-1 : ℝ)<1)),
    Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_connes_constantCoef_ne_zero] with x hx h0 hz
  have he : coef x 1=2*coef x 0 := sub_eq_zero.mp hz
  have h0' : coef x 0≠0 := h0
  rw [he, div_self (mul_ne_zero two_ne_zero h0')] at hx
  exact lt_irrefl 1 hx

open Finset
open scoped ArithmeticFunction.Moebius

open Cvs.Xi.EImageWindowPoisson (eimage window)
open Cvs.Xi.MobiusReconstruction (mobiusProfile)

private theorem triangular_sum_swap (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N/m), F m n)=
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N/n), F m n := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2,p.1⟩) (fun p => ⟨p.2,p.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m,n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hm1,hmN⟩,hn1,hnM⟩ := hp
    have hmn : n*m≤N := (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp hnM
    refine ⟨⟨hn1,?_⟩,hm1,?_⟩
    · nlinarith
    · exact (Nat.le_div_iff_mul_le (by omega : 0 < n)).mpr (by nlinarith)
  · rintro ⟨n,m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨hn1,hnN⟩,hm1,hmN⟩ := hp
    have hmn : m*n≤N := (Nat.le_div_iff_mul_le (by omega : 0 < n)).mp hmN
    refine ⟨⟨hm1,?_⟩,hn1,?_⟩
    · nlinarith
    · exact (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr (by nlinarith)
  · rintro ⟨m,n⟩ _
    rfl
  · rintro ⟨n,m⟩ _
    rfl
  · rintro ⟨m,n⟩ _
    rfl

/-- Möbius inversion recovers every sampled input from its full E-image. -/
theorem mobiusProfile_eimage {a u : ℝ} (ha : 0<a) (hu : 0<u) (hu1 : u≤1)
    (G : ℝ → ℝ) : mobiusProfile a (eimage a G) u=G u := by
  let N := ⌊1/u⌋₊
  have hN : 1≤N := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hu]
    linarith
  have hm0 : ∀ m ∈ Finset.Icc 1 N, (0 : ℝ) < m := by
    intro m hm
    exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hterm : ∀ m ∈ Finset.Icc 1 N,
      eimage a G (a/((m:ℝ)*u))/((m:ℝ)*u)=
        ∑ n ∈ Finset.Icc 1 (N/m), G ((m*n : ℕ)*u) := by
    intro m hm
    have hmpos := hm0 m hm
    have hfl : ⌊(a/((m:ℝ)*u))/a⌋₊=N/m := by
      rw [show (a/((m:ℝ)*u))/a=(1/u)/m by field_simp]
      exact Nat.floor_div_natCast _ _
    unfold eimage
    rw [hfl]
    have harg : ∀ n : ℕ, (n:ℝ)*a/(a/((m:ℝ)*u))=(m*n : ℕ)*u := by
      intro n
      push_cast
      field_simp
    simp only [harg]
    have hmul : a/(a/((m:ℝ)*u))=(m:ℝ)*u := by field_simp
    rw [hmul, mul_div_cancel_left₀ _ (mul_ne_zero hmpos.ne' hu.ne')]
  unfold mobiusProfile
  change (∑ m ∈ Finset.Icc 1 N, (μ m : ℝ)*
    (eimage a G (a/((m:ℝ)*u))/((m:ℝ)*u)))=G u
  have hsum : (∑ m ∈ Finset.Icc 1 N, (μ m : ℝ)*
      (eimage a G (a/((m:ℝ)*u))/((m:ℝ)*u)))=
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N/m),
        (μ m : ℝ)*G ((m*n : ℕ)*u) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [hterm m hm, Finset.mul_sum]
  rw [hsum]
  rw [triangular_sum_swap]
  rw [Cvs.Xi.MobiusReconstruction.sum_sigma_mul N (fun k => G ((k:ℝ)*u)) (fun m => (μ m : ℝ))]
  simp_rw [Cvs.Xi.MobiusReconstruction.sum_moebius_divisors]
  simp [hN]

/-- The actual finite window already determines its input on the sampled interval. -/
theorem mobiusProfile_window {a u : ℝ} (ha : 0<a) (hau : a≤u) (hu1 : u≤1)
    (G : ℝ → ℝ) : mobiusProfile a (window a G) u=G u := by
  have hu : 0<u := ha.trans_le hau
  rw [← mobiusProfile_eimage ha hu hu1 G]
  unfold mobiusProfile
  apply Finset.sum_congr rfl
  intro m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hmpos : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have hmu : (m:ℝ)*u≤1 := by
    have hmf : (m:ℝ)≤1/u := (Nat.le_floor_iff' (by
      have := (Finset.mem_Icc.mp hm).1
      omega : m≠0)).mp (Finset.mem_Icc.mp hm).2
    exact (le_div_iff₀ hu).mp hmf
  have hmem : a/((m:ℝ)*u)∈Icc a 1 := by
    constructor
    · rw [le_div_iff₀ (by positivity : (0:ℝ)<(m:ℝ)*u)]
      nlinarith
    · rw [div_le_one (by positivity : (0:ℝ)<(m:ℝ)*u)]
      nlinarith
  simp only [window, indicator_of_mem hmem]

/-- Two profiles with the same window coincide wherever that window samples them. -/
theorem profile_eq_of_window_eq {a : ℝ} (ha : 0<a) {G H : ℝ → ℝ}
    (h : window a G=window a H) {u : ℝ} (hu : u∈Icc a 1) : G u=H u := by
  rw [← mobiusProfile_window ha hu.1 hu.2 G,
    ← mobiusProfile_window ha hu.1 hu.2 H, h]

/-- Every exact window preimage is its Möbius reconstruction on the sampled interval. -/
theorem profile_eq_mobius_of_window_eq {a : ℝ} (ha : 0<a) {G v : ℝ → ℝ}
    (h : window a G=v) {u : ℝ} (hu : u∈Icc a 1) : G u=mobiusProfile a v u := by
  rw [← mobiusProfile_window ha hu.1 hu.2 G, h]

end Cvs.Approximant.ConnesLowModeGeometry
