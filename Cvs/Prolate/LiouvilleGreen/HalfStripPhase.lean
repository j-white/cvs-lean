import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Cvs.Prolate.LiouvilleGreen.ComplexSymbols
import Cvs.Upstream.HalfStripRayIntegrals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Liouville–Green phase `Φ_T` on the half-strip

`Φ_T(z) = Φ₀(z) − Φ₀(0)`, `Φ₀(z) = z − i∫_0^∞ (Φ′(z + is) − 1) ds`, is holomorphic on `U_a` with `Φ_T′ = Φ′`,
real on the real segment, `Im Φ_T` increases upward, and `Im Φ_T(x + iy) ≥ κy` when `|x| ≤ L`, `κ² = (T − L²)/(1 − L²)`.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral
open Complex (I)
open Cvs.Upstream.HalfStripRayIntegrals (strip RayBound rayInt)
open Cvs.Prolate.LiouvilleGreen.ComplexSymbols

namespace Cvs.Prolate.LiouvilleGreen.HalfStripPhase

/-- `Φ′ − 1`. -/
def gm (T : ℝ) (z : ℂ) : ℂ := phiD T z - 1

/-- `Φ₀(z) = z − i∫_0^∞ (Φ′(z + is) − 1) ds`. -/
def Phi0 (T : ℝ) (z : ℂ) : ℂ := z - I * rayInt (gm T) z

/-- **The Liouville–Green phase** `Φ_T = Φ₀ − Φ₀(0)`. -/
def Phi (T : ℝ) (z : ℂ) : ℂ := Phi0 T z - Phi0 T 0

variable {a T : ℝ}

theorem differentiableOn_gm (hT : a ^ 2 < T) (hT1 : T ≤ 1) : DifferentiableOn ℂ (gm T) (strip a) :=
  (differentiableOn_phiD hT hT1).sub_const 1

/-- `Φ_T′ = Φ′`. -/
theorem hasDerivAt_Phi (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) :
    HasDerivAt (Phi T) (phiD T z) z := by
  have hm : 0 < T - a ^ 2 := by linarith
  have hm1 : T - a ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have h := Cvs.Upstream.HalfStripRayIntegrals.hasDerivAt_rayInt (differentiableOn_gm hT hT1) hm hm1 (by linarith)
    (rayBound_phiD_sub_one hT hT1) hz
  have h2 := (((hasDerivAt_id z).sub (h.const_mul I)).sub_const (Phi0 T 0))
  refine h2.congr_deriv ?_
  simp only [gm]
  rw [← mul_assoc, Complex.I_mul_I]; ring

theorem Phi_zero (T : ℝ) : Phi T 0 = 0 := sub_self _

theorem differentiableOn_Phi (hT : a ^ 2 < T) (hT1 : T ≤ 1) : DifferentiableOn ℂ (Phi T) (strip a) :=
  fun _ hz => (hasDerivAt_Phi hT hT1 hz).differentiableAt.differentiableWithinAt

theorem hasDerivAt_ray (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => Phi T (z + t * I)) (phiD T (z + t * I) * I) t := by
  have h1 := hasDerivAt_Phi hT hT1 (Cvs.Upstream.HalfStripRayIntegrals.add_mem_strip hz ht)
  have h2 : HasDerivAt (fun s : ℝ => z + (s : ℂ) * I) I t := by
    simpa using ((hasDerivAt_id (t : ℂ)).comp_ofReal (z := t)).mul_const I |>.const_add z
  exact h1.comp t h2

theorem continuousOn_phiD_ray (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) :
    ContinuousOn (fun t : ℝ => phiD T (z + t * I)) (Ici 0) :=
  (differentiableOn_phiD hT hT1).continuousOn.comp (by fun_prop) fun _ ht => Cvs.Upstream.HalfStripRayIntegrals.add_mem_strip hz ht

/-- **The vertical increment** `Φ_T(z + is) − Φ_T(z) = i∫_0^s Φ′(z + it) dt`. -/
theorem Phi_vert (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) {s : ℝ} (hs : 0 ≤ s) :
    Phi T (z + s * I) - Phi T z = I * ∫ t in (0 : ℝ)..s, phiD T (z + t * I) := by
  have hu : uIcc 0 s = Icc 0 s := uIcc_of_le hs
  have hd : ∀ t ∈ uIcc (0 : ℝ) s, HasDerivAt (fun t : ℝ => Phi T (z + t * I)) (phiD T (z + t * I) * I) t :=
    fun t ht => hasDerivAt_ray hT hT1 hz (by rw [hu] at ht; exact ht.1)
  have hc : ContinuousOn (fun t : ℝ => phiD T (z + t * I) * I) (uIcc 0 s) := by
    rw [hu]; exact ((continuousOn_phiD_ray hT hT1 hz).mono Icc_subset_Ici_self).mul continuousOn_const
  have h := integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  rw [← h, intervalIntegral.integral_mul_const, mul_comm]

/-- `Im Φ_T(z + is) − Im Φ_T(z) = ∫_0^s Re Φ′(z + it) dt`. -/
theorem im_Phi_vert (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) {s : ℝ} (hs : 0 ≤ s) :
    (Phi T (z + s * I)).im - (Phi T z).im = ∫ t in (0 : ℝ)..s, (phiD T (z + t * I)).re := by
  have h := congrArg Complex.im (Phi_vert hT hT1 hz hs)
  rw [Complex.sub_im, Complex.I_mul_im] at h
  rw [h]
  have hc : ContinuousOn (fun t : ℝ => phiD T (z + t * I)) (uIcc 0 s) := by
    rw [uIcc_of_le hs]; exact (continuousOn_phiD_ray hT hT1 hz).mono Icc_subset_Ici_self
  exact (Complex.reCLM.intervalIntegral_comp_comm hc.intervalIntegrable).symm

/-- `Im Φ_T` increases upward. -/
theorem im_Phi_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) {s : ℝ} (hs : 0 ≤ s) :
    (Phi T z).im ≤ (Phi T (z + s * I)).im := by
  have h := im_Phi_vert hT hT1 hz hs
  have : 0 ≤ ∫ t in (0 : ℝ)..s, (phiD T (z + t * I)).re :=
    intervalIntegral.integral_nonneg hs fun t _ => re_phiD_nonneg T _
  linarith

/-- **`Φ_T` is real on the real segment.** -/
theorem im_Phi_ofReal (hT : a ^ 2 < T) (hT1 : T ≤ 1) {t : ℝ} (ht : |t| < a) : (Phi T t).im = 0 := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg _) ht
  have hmem : ∀ u ∈ uIcc (0 : ℝ) t, |u| < a := fun u hu => by
    have : |u| ≤ |t| := by
      rcases Set.mem_uIcc.1 hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
    exact this.trans_lt ht
  have hd : ∀ u ∈ uIcc (0 : ℝ) t, HasDerivAt (fun u : ℝ => Phi T u) (phiD T u) u := fun u hu =>
    (hasDerivAt_Phi hT hT1 (show (u : ℂ) ∈ strip a from ⟨by simpa using hmem u hu, by simp⟩)).comp_ofReal
  have hr : ∀ u ∈ uIcc (0 : ℝ) t, phiD T u = (√((T - u ^ 2) / (1 - u ^ 2)) : ℝ) := fun u hu =>
    phiD_ofReal hT hT1 (hmem u hu)
  have hc : ContinuousOn (fun u : ℝ => phiD T u) (uIcc 0 t) :=
    (differentiableOn_phiD hT hT1).continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun v hv => show (v : ℂ) ∈ strip a from ⟨by simpa using hmem v hv, by simp⟩)
  have h := integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  have e : (∫ u in (0 : ℝ)..t, phiD T u) = ((∫ u in (0 : ℝ)..t, √((T - u ^ 2) / (1 - u ^ 2)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun u hu => hr u hu
  rw [e] at h
  have h0 : Phi T ((0 : ℝ) : ℂ) = 0 := by simpa using Phi_zero T
  rw [h0, sub_zero] at h
  rw [← h, Complex.ofReal_im]

/-- **The upward margin** `Im Φ_T(x + iy) ≥ κy` for `|x| ≤ L < a`, `y ≥ 0`, `κ = √((T − L²)/(1 − L²))`. -/
theorem im_Phi_ge (hT : a ^ 2 < T) (hT1 : T ≤ 1) {L x y : ℝ} (hL : L < a) (hx : |x| ≤ L) (hy : 0 ≤ y) :
    √((T - L ^ 2) / (1 - L ^ 2)) * y ≤ (Phi T (x + y * I)).im := by
  have ha1 : a ^ 2 < 1 := lt_of_lt_of_le hT hT1
  have hL0 : 0 ≤ L := (abs_nonneg x).trans hx
  have hL1 : L ^ 2 < 1 := by nlinarith
  have hxs : (x : ℂ) ∈ strip a := ⟨by simpa using hx.trans_lt hL, by simp⟩
  have h := im_Phi_vert hT hT1 hxs hy
  rw [im_Phi_ofReal hT hT1 (hx.trans_lt hL), sub_zero] at h
  rw [h]
  have hκ : ∀ t ∈ Icc (0 : ℝ) y, √((T - L ^ 2) / (1 - L ^ 2)) ≤ (phiD T (x + t * I)).re := by
    intro t ht
    have hmem : (x : ℂ) + t * I ∈ strip a := Cvs.Upstream.HalfStripRayIntegrals.add_mem_strip hxs ht.1
    have hre : ((x : ℂ) + t * I).re ^ 2 ≤ L ^ 2 := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    exact (Real.sqrt_le_sqrt (re_pp_ge hT1 hL1 hre)).trans (sqrt_re_pp_le (pp_mem_slitPlane hT hT1 hmem))
  have hc : ContinuousOn (fun t : ℝ => (phiD T (x + t * I)).re) (Icc 0 y) :=
    Complex.continuous_re.comp_continuousOn ((continuousOn_phiD_ray hT hT1 hxs).mono Icc_subset_Ici_self)
  calc √((T - L ^ 2) / (1 - L ^ 2)) * y = ∫ t in (0 : ℝ)..y, √((T - L ^ 2) / (1 - L ^ 2)) := by
        rw [intervalIntegral.integral_const]; simp [smul_eq_mul, mul_comm]
    _ ≤ ∫ t in (0 : ℝ)..y, (phiD T (x + t * I)).re :=
        intervalIntegral.integral_mono_on hy intervalIntegrable_const (hc.intervalIntegrable_of_Icc hy) hκ

/-- **The lower bound** `Im Φ_T ≥ −√(1 + (1 − T)/m)` on `U_a`. -/
theorem im_Phi_ge_neg (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) :
    -√(1 + (1 - T) / (T - a ^ 2)) ≤ (Phi T z).im := by
  have hR : 0 ≤ √(1 + (1 - T) / (T - a ^ 2)) := Real.sqrt_nonneg _
  have hxs : (z.re : ℂ) ∈ strip a := ⟨by simpa using hz.1, by simp⟩
  have h0 := im_Phi_ofReal hT hT1 hz.1
  rcases le_or_gt 0 z.im with hy | hy
  · have h := im_Phi_le hT hT1 hxs hy
    rw [Complex.re_add_im, h0] at h
    linarith
  · have hs : 0 ≤ -z.im := by linarith
    have h := im_Phi_vert hT hT1 hz hs
    have e : z + ((-z.im : ℝ) : ℂ) * I = (z.re : ℂ) := by
      apply Complex.ext <;> simp
    rw [e, h0] at h
    have hb : ∀ t ∈ Icc (0 : ℝ) (-z.im), (phiD T (z + t * I)).re ≤ √(1 + (1 - T) / (T - a ^ 2)) := by
      intro t ht
      have hmem := Cvs.Upstream.HalfStripRayIntegrals.add_mem_strip hz ht.1
      have h1 := norm_phiD_sq_le hT hT1 hmem
      calc (phiD T (z + t * I)).re ≤ ‖phiD T (z + t * I)‖ := Complex.re_le_norm _
        _ = √(‖phiD T (z + t * I)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ √(1 + (1 - T) / (T - a ^ 2)) := Real.sqrt_le_sqrt h1
    have hc : ContinuousOn (fun t : ℝ => (phiD T (z + t * I)).re) (Icc 0 (-z.im)) :=
      Complex.continuous_re.comp_continuousOn ((continuousOn_phiD_ray hT hT1 hz).mono Icc_subset_Ici_self)
    have hI : ∫ t in (0 : ℝ)..(-z.im), (phiD T (z + t * I)).re ≤
        ∫ t in (0 : ℝ)..(-z.im), √(1 + (1 - T) / (T - a ^ 2)) :=
      intervalIntegral.integral_mono_on hs (hc.intervalIntegrable_of_Icc hs) intervalIntegrable_const hb
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hI
    have hz1 : -z.im < 1 := by linarith [hz.2]
    nlinarith

end Cvs.Prolate.LiouvilleGreen.HalfStripPhase

end
