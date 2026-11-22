import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Cvs.Prolate.LiouvilleGreen.ComplexSymbols
import Cvs.Prolate.LiouvilleGreen.HalfStripPhase
import Cvs.Upstream.HalfStripRayIntegrals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Volterra equation of the recessive Liouville–Green solution

`ε = 𝒱ε`, `𝒱f(z) = (1/2c)∫_0^∞ (1 − e^{2ic(Φ_T(z + is) − Φ_T(z))}) r(z + is)(1 + f(z + is)) ds`, has a
holomorphic solution on `U_a` with `|ε| ≤ q/(1 − q)`, `q = V/c < 1`, `V = K_rπ/√m`, and
`ε′ = iΦ′e^{−2icΦ_T}∫_0^∞ e^{2icΦ_T}r(1 + ε)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open Complex (I)
open Cvs.Upstream.HalfStripRayIntegrals (strip RayBound rayInt)
open Cvs.Prolate.LiouvilleGreen.ComplexSymbols
open Cvs.Prolate.LiouvilleGreen.HalfStripPhase

namespace Cvs.Prolate.LiouvilleGreen.RecessiveVolterra

/-- The error-control constant `V = K_rπ/√m`, `m = T − a²`. -/
def vV (a T : ℝ) : ℝ := kR T (T - a ^ 2) * (π / √(T - a ^ 2))

/-- The crude growth constant `e^{2c√(1 + (1 − T)/m)}` of `e^{2icΦ_T}` on `U_a`. -/
def eC (a T c : ℝ) : ℝ := Real.exp (2 * c * √(1 + (1 - T) / (T - a ^ 2)))

/-- `e^{2icΦ_T}`. -/
def eph (c T : ℝ) (w : ℂ) : ℂ := Complex.exp (2 * I * c * Phi T w)

/-- `e^{−2icΦ_T}`. -/
def emph (c T : ℝ) (w : ℂ) : ℂ := Complex.exp (-(2 * I * c * Phi T w))

/-- The Volterra kernel `1 − e^{2ic(Φ_T(z + is) − Φ_T(z))}`. -/
def kern (c T : ℝ) (z : ℂ) (s : ℝ) : ℂ := 1 - Complex.exp (2 * I * c * (Phi T (z + s * I) - Phi T z))

/-- The forcing `r(1 + f)`. -/
def resid (T : ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ := rr T w * (1 + f w)

/-- **The Volterra operator** `𝒱f(z) = (1/2c)∫_0^∞ k(z, s) r(z + is)(1 + f(z + is)) ds`. -/
def vop (c T : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (2 * c)) * ∫ s in Ioi (0 : ℝ), kern c T z s * resid T f (z + s * I)

/-- `f` holomorphic on `U_a` and bounded by `B` there. -/
def Good (a : ℝ) (f : ℂ → ℂ) (B : ℝ) : Prop := DifferentiableOn ℂ f (strip a) ∧ ∀ z ∈ strip a, ‖f z‖ ≤ B

section

variable {a T c : ℝ}

theorem eph_mul_emph (c T : ℝ) (w : ℂ) : eph c T w * emph c T w = 1 := by
  unfold eph emph; rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem exp_kern (c T : ℝ) (z : ℂ) (s : ℝ) :
    Complex.exp (2 * I * c * (Phi T (z + s * I) - Phi T z)) = eph c T (z + s * I) * emph c T z := by
  unfold eph emph; rw [← Complex.exp_add]; ring_nf

theorem re_two_I_mul (c : ℝ) (w : ℂ) : (2 * I * c * w).re = -(2 * c * w.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_eph_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 ≤ c) {w : ℂ} (hw : w ∈ strip a) :
    ‖eph c T w‖ ≤ eC a T c := by
  unfold eph eC
  rw [Complex.norm_exp, re_two_I_mul]
  refine Real.exp_le_exp.2 ?_
  have := im_Phi_ge_neg hT hT1 hw
  nlinarith

theorem norm_kern_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 ≤ c) {z : ℂ} (hz : z ∈ strip a) {s : ℝ}
    (hs : 0 ≤ s) : ‖kern c T z s‖ ≤ 2 := by
  unfold kern
  have h1 : ‖Complex.exp (2 * I * c * (Phi T (z + s * I) - Phi T z))‖ ≤ 1 := by
    rw [Complex.norm_exp, re_two_I_mul, Complex.sub_im, Real.exp_le_one_iff]
    have := im_Phi_le hT hT1 hz hs
    nlinarith
  calc _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (2 * I * c * (Phi T (z + s * I) - Phi T z))‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

theorem hm (hT : a ^ 2 < T) : 0 < T - a ^ 2 := by linarith

theorem hm1 (hT1 : T ≤ 1) : T - a ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]

theorem kR_nonneg (hT : a ^ 2 < T) (hT1 : T ≤ 1) : 0 ≤ kR T (T - a ^ 2) := by
  have h0 : 0 ≤ T := le_trans (sq_nonneg a) hT.le
  unfold kR
  have := mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - T)
  have := hm hT
  positivity

theorem vV_nonneg (hT : a ^ 2 < T) (hT1 : T ≤ 1) : 0 ≤ vV a T :=
  mul_nonneg (kR_nonneg hT hT1) (div_nonneg Real.pi_pos.le (Real.sqrt_nonneg _))

theorem differentiableOn_resid (hT : a ^ 2 < T) (hT1 : T ≤ 1) {f : ℂ → ℂ} {B : ℝ} (hf : Good a f B) :
    DifferentiableOn ℂ (resid T f) (strip a) :=
  (differentiableOn_rr hT hT1).mul ((differentiableOn_const 1).add hf.1)

theorem rayBound_resid (hT : a ^ 2 < T) (hT1 : T ≤ 1) {f : ℂ → ℂ} {B : ℝ} (hf : Good a f B) :
    RayBound a (T - a ^ 2) (kR T (T - a ^ 2) * (1 + B)) (resid T f) := by
  intro z hz
  have h1 := Cvs.Prolate.LiouvilleGreen.ComplexSymbols.rayBound_rr (le_trans (sq_nonneg a) hT.le) hT hT1 z hz
  have h2 : ‖1 + f z‖ ≤ 1 + B := (norm_add_le _ _).trans (by rw [norm_one]; linarith [hf.2 z hz])
  have hD : 0 < T - a ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.im]
  unfold resid
  rw [norm_mul, mul_div_right_comm]
  exact mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg (kR_nonneg hT hT1) hD.le)

theorem differentiableOn_eph (hT : a ^ 2 < T) (hT1 : T ≤ 1) : DifferentiableOn ℂ (eph c T) (strip a) :=
  ((differentiableOn_Phi hT hT1).const_mul _).cexp

theorem rayBound_eph_resid (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 ≤ c) {f : ℂ → ℂ} {B : ℝ}
    (hf : Good a f B) :
    RayBound a (T - a ^ 2) (eC a T c * (kR T (T - a ^ 2) * (1 + B))) (fun w => eph c T w * resid T f w) := by
  intro z hz
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul (norm_eph_le hT hT1 hc hz) (rayBound_resid hT hT1 hf z hz) (norm_nonneg _)
    (Real.exp_pos _).le

theorem B_nonneg {f : ℂ → ℂ} {B : ℝ} (hf : Good a f B) (ha : 0 < a) : 0 ≤ B :=
  (norm_nonneg _).trans (hf.2 0 ⟨by simpa using ha, by simp⟩)

/-- The integrand of `𝒱f` is integrable along the ray. -/
theorem integrableOn_vop (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 ≤ c) {f : ℂ → ℂ} {B : ℝ}
    (hf : Good a f B) {z : ℂ} (hz : z ∈ strip a) :
    IntegrableOn (fun s : ℝ => kern c T z s * resid T f (z + s * I)) (Ioi 0) := by
  have hR := Cvs.Upstream.HalfStripRayIntegrals.integrableOn_ray (differentiableOn_resid hT hT1 hf) (hm hT) (rayBound_resid hT hT1 hf) hz
  have hE := Cvs.Upstream.HalfStripRayIntegrals.integrableOn_ray (G := fun w => eph c T w * resid T f w)
    ((differentiableOn_eph hT hT1).mul (differentiableOn_resid hT hT1 hf)) (hm hT)
    (rayBound_eph_resid hT hT1 hc hf) hz
  have := hR.sub (hE.mul_const (emph c T z))
  refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, kern, exp_kern]; ring

/-- **The split form** `𝒱f = (1/2c)(F₁ − e^{−2icΦ_T}F₂)`. -/
theorem vop_eq (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 ≤ c) {f : ℂ → ℂ} {B : ℝ} (hf : Good a f B) {z : ℂ}
    (hz : z ∈ strip a) :
    vop c T f z = (1 / (2 * c)) *
      (rayInt (resid T f) z - emph c T z * rayInt (fun w => eph c T w * resid T f w) z) := by
  have hR := Cvs.Upstream.HalfStripRayIntegrals.integrableOn_ray (differentiableOn_resid hT hT1 hf) (hm hT) (rayBound_resid hT hT1 hf) hz
  have hE := Cvs.Upstream.HalfStripRayIntegrals.integrableOn_ray (G := fun w => eph c T w * resid T f w)
    ((differentiableOn_eph hT hT1).mul (differentiableOn_resid hT hT1 hf)) (hm hT)
    (rayBound_eph_resid hT hT1 hc hf) hz
  unfold vop rayInt
  congr 1
  rw [← integral_const_mul, ← integral_sub hR (hE.const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [kern, exp_kern]; ring

/-- `e^{−2icΦ_T}` has derivative `−2icΦ′e^{−2icΦ_T}`. -/
theorem hasDerivAt_emph (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) :
    HasDerivAt (emph c T) (emph c T z * (-(2 * I * c * phiD T z))) z :=
  (((hasDerivAt_Phi hT hT1 hz).const_mul (2 * I * c)).neg).cexp

/-- **The derivative of `𝒱f`**: `iΦ′e^{−2icΦ_T}F₂`. -/
theorem hasDerivAt_vop (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {f : ℂ → ℂ} {B : ℝ} (hf : Good a f B)
    {z : ℂ} (hz : z ∈ strip a) :
    HasDerivAt (vop c T f)
      (I * phiD T z * emph c T z * rayInt (fun w => eph c T w * resid T f w) z) z := by
  have hB := B_nonneg hf (lt_of_le_of_lt (abs_nonneg _) hz.1)
  have hK := kR_nonneg hT hT1
  have h1 := Cvs.Upstream.HalfStripRayIntegrals.hasDerivAt_rayInt (differentiableOn_resid hT hT1 hf) (hm hT) (hm1 hT1) (by positivity)
    (rayBound_resid hT hT1 hf) hz
  have h2 := Cvs.Upstream.HalfStripRayIntegrals.hasDerivAt_rayInt (G := fun w => eph c T w * resid T f w)
    ((differentiableOn_eph hT hT1).mul (differentiableOn_resid hT hT1 hf)) (hm hT) (hm1 hT1)
    (by unfold eC; positivity) (rayBound_eph_resid hT hT1 hc.le hf) hz
  have h3 := ((h1.sub ((hasDerivAt_emph (c := c) hT hT1 hz).mul h2)).const_mul ((1 : ℂ) / (2 * c)))
  have hev : (fun w => (1 / (2 * c)) * (rayInt (resid T f) w - emph c T w *
      rayInt (fun w => eph c T w * resid T f w) w)) =ᶠ[𝓝 z] vop c T f := by
    filter_upwards [(Cvs.Upstream.HalfStripRayIntegrals.isOpen_strip a).mem_nhds hz] with w hw
    exact (vop_eq hT hT1 hc.le hf hw).symm
  refine (h3.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  have he := eph_mul_emph c T z
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp
  linear_combination (-resid T f z) * he

/-- `|𝒱f| ≤ (V/c)(1 + B)` on `U_a`. -/
theorem norm_vop_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {f : ℂ → ℂ} {B : ℝ} (hf : Good a f B)
    {z : ℂ} (hz : z ∈ strip a) : ‖vop c T f z‖ ≤ vV a T / c * (1 + B) := by
  have hB := B_nonneg hf (lt_of_le_of_lt (abs_nonneg _) hz.1)
  have hK := kR_nonneg hT hT1
  have hmaj : IntegrableOn (fun s : ℝ => 2 * (kR T (T - a ^ 2) * (1 + B)) *
      (1 / (T - a ^ 2 + (z.im + s) ^ 2))) (Ioi 0) := (Cvs.Upstream.HalfStripRayIntegrals.integrableOn_shift (hm hT) z.im).const_mul _
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ‖kern c T z s * resid T f (z + s * I)‖ ≤
      2 * (kR T (T - a ^ 2) * (1 + B)) * (1 / (T - a ^ 2 + (z.im + s) ^ 2)) := by
    intro s hs
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (norm_kern_le hT hT1 hc.le hz (le_of_lt hs))
      (Cvs.Upstream.HalfStripRayIntegrals.norm_ray_le (rayBound_resid hT hT1 hf) hz (le_of_lt hs)) (norm_nonneg _) (by norm_num)
  unfold vop
  rw [norm_mul, show ‖(1 / (2 * c) : ℂ)‖ = 1 / (2 * c) by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]; norm_num]
  have hI : ‖∫ s in Ioi (0 : ℝ), kern c T z s * resid T f (z + s * I)‖ ≤
      2 * (kR T (T - a ^ 2) * (1 + B)) * (π / √(T - a ^ 2)) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (setIntegral_mono_on (integrableOn_vop hT hT1 hc.le hf hz).norm hmaj measurableSet_Ioi hpt).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (Cvs.Upstream.HalfStripRayIntegrals.integral_shift_le (hm hT) z.im) (by positivity)
  calc 1 / (2 * c) * ‖∫ s in Ioi (0 : ℝ), kern c T z s * resid T f (z + s * I)‖ ≤
        1 / (2 * c) * (2 * (kR T (T - a ^ 2) * (1 + B)) * (π / √(T - a ^ 2))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = vV a T / c * (1 + B) := by unfold vV; field_simp

/-- **The contraction**: `|𝒱f − 𝒱g| ≤ (V/c)δ` when `|f − g| ≤ δ` on `U_a`. -/
theorem norm_vop_sub_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {f g : ℂ → ℂ} {B B' δ : ℝ}
    (hf : Good a f B) (hg : Good a g B') (hδ : ∀ w ∈ strip a, ‖f w - g w‖ ≤ δ) {z : ℂ} (hz : z ∈ strip a) :
    ‖vop c T f z - vop c T g z‖ ≤ vV a T / c * δ := by
  have hK := kR_nonneg hT hT1
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ z hz)
  have hmaj : IntegrableOn (fun s : ℝ => 2 * (kR T (T - a ^ 2) * δ) *
      (1 / (T - a ^ 2 + (z.im + s) ^ 2))) (Ioi 0) := (Cvs.Upstream.HalfStripRayIntegrals.integrableOn_shift (hm hT) z.im).const_mul _
  have hdiff : ∀ s ∈ Ioi (0 : ℝ), kern c T z s * resid T f (z + s * I) - kern c T z s * resid T g (z + s * I) =
      kern c T z s * (rr T (z + s * I) * (f (z + s * I) - g (z + s * I))) := fun s _ => by
    unfold resid; ring
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ‖kern c T z s * (rr T (z + s * I) * (f (z + s * I) - g (z + s * I)))‖ ≤
      2 * (kR T (T - a ^ 2) * δ) * (1 / (T - a ^ 2 + (z.im + s) ^ 2)) := by
    intro s hs
    have hw := Cvs.Upstream.HalfStripRayIntegrals.add_mem_strip hz (le_of_lt hs)
    have h1 := Cvs.Prolate.LiouvilleGreen.ComplexSymbols.rayBound_rr (le_trans (sq_nonneg a) hT.le) hT hT1 _ hw
    have hw' : (z + s * I).im = z.im + s := by simp
    rw [hw'] at h1
    rw [norm_mul, norm_mul, mul_assoc]
    refine mul_le_mul (norm_kern_le hT hT1 hc.le hz (le_of_lt hs)) ?_ (by positivity) (by norm_num)
    calc ‖rr T (z + s * I)‖ * ‖f (z + s * I) - g (z + s * I)‖ ≤
          kR T (T - a ^ 2) / (T - a ^ 2 + (z.im + s) ^ 2) * δ :=
          mul_le_mul h1 (hδ _ hw) (norm_nonneg _) (div_nonneg hK (by nlinarith [hm hT, sq_nonneg (z.im + s)]))
      _ = kR T (T - a ^ 2) * δ * (1 / (T - a ^ 2 + (z.im + s) ^ 2)) := by ring
  unfold vop
  rw [← mul_sub, ← integral_sub (integrableOn_vop hT hT1 hc.le hf hz) (integrableOn_vop hT hT1 hc.le hg hz),
    setIntegral_congr_fun measurableSet_Ioi hdiff, norm_mul, show ‖(1 / (2 * c) : ℂ)‖ = 1 / (2 * c) by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]; norm_num]
  have hint : IntegrableOn (fun s : ℝ => kern c T z s * (rr T (z + s * I) * (f (z + s * I) - g (z + s * I))))
      (Ioi 0) := by
    refine ((integrableOn_vop hT hT1 hc.le hf hz).sub (integrableOn_vop hT hT1 hc.le hg hz)).congr_fun ?_
      measurableSet_Ioi
    intro s hs; exact hdiff s hs
  have hI : ‖∫ s in Ioi (0 : ℝ), kern c T z s * (rr T (z + s * I) * (f (z + s * I) - g (z + s * I)))‖ ≤
      2 * (kR T (T - a ^ 2) * δ) * (π / √(T - a ^ 2)) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (setIntegral_mono_on hint.norm hmaj measurableSet_Ioi hpt).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (Cvs.Upstream.HalfStripRayIntegrals.integral_shift_le (hm hT) z.im) (by positivity)
  calc _ ≤ 1 / (2 * c) * (2 * (kR T (T - a ^ 2) * δ) * (π / √(T - a ^ 2))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = vV a T / c * δ := by unfold vV; field_simp

/-- `𝒱` maps `Good B` into `Good ((V/c)(1 + B))`. -/
theorem good_vop (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {f : ℂ → ℂ} {B : ℝ} (hf : Good a f B) :
    Good a (vop c T f) (vV a T / c * (1 + B)) :=
  ⟨fun _ hz => (hasDerivAt_vop hT hT1 hc hf hz).differentiableAt.differentiableWithinAt,
    fun _ hz => norm_vop_le hT hT1 hc hf hz⟩

/-! ### The Picard iteration -/

/-- The Picard iterates `ε₀ = 0`, `ε_{n+1} = 𝒱ε_n`. -/
def it (c T : ℝ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | n + 1 => vop c T (it c T n)

theorem good_it (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) (hq : vV a T / c < 1) (n : ℕ) :
    Good a (it c T n) (vV a T / c / (1 - vV a T / c)) := by
  have hq0 : 0 ≤ vV a T / c := div_nonneg (vV_nonneg hT hT1) hc.le
  have hB0 : 0 ≤ vV a T / c / (1 - vV a T / c) := div_nonneg hq0 (by linarith)
  induction n with
  | zero => exact ⟨differentiableOn_const 0, fun _ _ => by simp [it]; exact hB0⟩
  | succ n ih =>
    refine ⟨(good_vop hT hT1 hc ih).1, fun z hz => (norm_vop_le hT hT1 hc ih hz).trans (le_of_eq ?_)⟩
    have h1q : 1 - vV a T / c ≠ 0 := by linarith
    generalize vV a T / c = q at h1q ⊢
    field_simp
    ring

theorem norm_it_succ_sub_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) (hq : vV a T / c < 1)
    (n : ℕ) : ∀ z ∈ strip a, ‖it c T (n + 1) z - it c T n z‖ ≤ (vV a T / c) ^ (n + 1) := by
  induction n with
  | zero =>
    intro z hz
    simp only [it, zero_add, pow_one]
    rw [sub_zero]
    refine (norm_vop_le hT hT1 hc (B := 0) ⟨differentiableOn_const 0, fun _ _ => by simp⟩ hz).trans ?_
    rw [add_zero, mul_one]
  | succ n ih =>
    intro z hz
    have h := norm_vop_sub_le hT hT1 hc (good_it hT hT1 hc hq (n + 1)) (good_it hT hT1 hc hq n) ih hz
    show ‖vop c T (it c T (n + 1)) z - vop c T (it c T n) z‖ ≤ _
    refine h.trans (le_of_eq ?_)
    ring

/-- The iterates converge uniformly on `U_a`. -/
theorem tendstoUniformlyOn_it (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) (hq : vV a T / c < 1) :
    TendstoUniformlyOn (fun N z => it c T N z) (fun z => ∑' n, (it c T (n + 1) z - it c T n z)) atTop
      (strip a) := by
  have hq0 : 0 ≤ vV a T / c := div_nonneg (vV_nonneg hT hT1) hc.le
  have hs : Summable fun n : ℕ => (vV a T / c) ^ (n + 1) :=
    (summable_geometric_of_lt_one hq0 hq).mul_left _ |>.congr fun n => (pow_succ' _ n).symm
  have h := tendstoUniformlyOn_tsum_nat hs (s := strip a) (f := fun n z => it c T (n + 1) z - it c T n z)
    fun n z hz => norm_it_succ_sub_le hT hT1 hc hq n z hz
  refine h.congr (Eventually.of_forall fun N z _ => ?_)
  simp only
  rw [Finset.sum_range_sub (fun n => it c T n z)]
  show it c T N z - 0 = it c T N z
  rw [sub_zero]

/-- **The Volterra solution**: a holomorphic `ε` on `U_a` with `ε = 𝒱ε` and `|ε| ≤ q/(1 − q)`. -/
theorem exists_eps (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) (hq : vV a T / c < 1) :
    ∃ ε : ℂ → ℂ, Good a ε (vV a T / c / (1 - vV a T / c)) ∧ ∀ z ∈ strip a, ε z = vop c T ε z := by
  set ε : ℂ → ℂ := fun z => ∑' n, (it c T (n + 1) z - it c T n z)
  have hU := tendstoUniformlyOn_it hT hT1 hc hq
  have hgood : Good a ε (vV a T / c / (1 - vV a T / c)) := by
    refine ⟨TendstoLocallyUniformlyOn.differentiableOn hU.tendstoLocallyUniformlyOn
      (Eventually.of_forall fun n => (good_it hT hT1 hc hq n).1) (Cvs.Upstream.HalfStripRayIntegrals.isOpen_strip a), fun z hz => ?_⟩
    exact le_of_tendsto ((hU.tendsto_at hz).norm) (Eventually.of_forall fun n => (good_it hT hT1 hc hq n).2 z hz)
  refine ⟨ε, hgood, fun z hz => ?_⟩
  have h1 : Tendsto (fun n => it c T (n + 1) z) atTop (𝓝 (ε z)) :=
    (hU.tendsto_at hz).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => it c T (n + 1) z) atTop (𝓝 (vop c T ε z)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    have hq1 : 0 < vV a T / c + 1 := by have := div_nonneg (vV_nonneg hT hT1) hc.le; linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hU (δ / (vV a T / c + 1))
      (by positivity))
    refine ⟨N, fun n hn => ?_⟩
    have hd : ∀ w ∈ strip a, ‖ε w - it c T n w‖ ≤ δ / (vV a T / c + 1) := fun w hw => by
      have := hN n hn w hw; rw [dist_eq_norm] at this; exact this.le
    have := norm_vop_sub_le hT hT1 hc hgood (good_it hT hT1 hc hq n) hd hz
    rw [dist_eq_norm, norm_sub_rev]
    show ‖vop c T ε z - vop c T (it c T n) z‖ < δ
    refine this.trans_lt ?_
    have hq0 := div_nonneg (vV_nonneg hT hT1) hc.le
    rw [mul_div_assoc', div_lt_iff₀ hq1]
    nlinarith
  exact tendsto_nhds_unique h1 h2

/-! ### The derivative of the solution -/

/-- The flux `J = i∫_0^∞ e^{2icΦ_T}r(1 + ε)` along the ray. -/
def flux (c T : ℝ) (ε : ℂ → ℂ) (z : ℂ) : ℂ := I * rayInt (fun w => eph c T w * resid T ε w) z

/-- **`ε′ = Φ′e^{−2icΦ_T}J`**. -/
theorem hasDerivAt_eps (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {ε : ℂ → ℂ} {B : ℝ} (hε : Good a ε B)
    (hfix : ∀ z ∈ strip a, ε z = vop c T ε z) {z : ℂ} (hz : z ∈ strip a) :
    HasDerivAt ε (phiD T z * emph c T z * flux c T ε z) z := by
  have h := hasDerivAt_vop hT hT1 hc hε hz
  have hev : vop c T ε =ᶠ[𝓝 z] ε := by
    filter_upwards [(Cvs.Upstream.HalfStripRayIntegrals.isOpen_strip a).mem_nhds hz] with w hw using (hfix w hw).symm
  refine (h.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  unfold flux; ring

/-- **`J′ = −e^{2icΦ_T}r(1 + ε)`**. -/
theorem hasDerivAt_flux (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {ε : ℂ → ℂ} {B : ℝ} (hε : Good a ε B)
    {z : ℂ} (hz : z ∈ strip a) :
    HasDerivAt (flux c T ε) (-(eph c T z * resid T ε z)) z := by
  have hB := B_nonneg hε (lt_of_le_of_lt (abs_nonneg _) hz.1)
  have hK := kR_nonneg hT hT1
  have h2 := Cvs.Upstream.HalfStripRayIntegrals.hasDerivAt_rayInt (G := fun w => eph c T w * resid T ε w)
    ((differentiableOn_eph hT hT1).mul (differentiableOn_resid hT hT1 hε)) (hm hT) (hm1 hT1)
    (by unfold eC; positivity) (rayBound_eph_resid hT hT1 hc.le hε) hz
  refine (h2.const_mul I).congr_deriv ?_
  rw [← mul_assoc, Complex.I_mul_I]; ring

/-- `|e^{−2icΦ_T}J| ≤ V(1 + B)` on `U_a`. -/
theorem norm_emph_flux_le (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {ε : ℂ → ℂ} {B : ℝ} (hε : Good a ε B)
    {z : ℂ} (hz : z ∈ strip a) : ‖emph c T z * flux c T ε z‖ ≤ vV a T * (1 + B) := by
  have hB := B_nonneg hε (lt_of_le_of_lt (abs_nonneg _) hz.1)
  have hK := kR_nonneg hT hT1
  have hE := Cvs.Upstream.HalfStripRayIntegrals.integrableOn_ray (G := fun w => eph c T w * resid T ε w)
    ((differentiableOn_eph hT hT1).mul (differentiableOn_resid hT hT1 hε)) (hm hT)
    (rayBound_eph_resid hT hT1 hc.le hε) hz
  have hmaj : IntegrableOn (fun s : ℝ => kR T (T - a ^ 2) * (1 + B) *
      (1 / (T - a ^ 2 + (z.im + s) ^ 2))) (Ioi 0) := (Cvs.Upstream.HalfStripRayIntegrals.integrableOn_shift (hm hT) z.im).const_mul _
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ‖emph c T z * (eph c T (z + s * I) * resid T ε (z + s * I))‖ ≤
      kR T (T - a ^ 2) * (1 + B) * (1 / (T - a ^ 2 + (z.im + s) ^ 2)) := by
    intro s hs
    have h1 : ‖emph c T z * eph c T (z + s * I)‖ ≤ 1 := by
      rw [mul_comm, ← exp_kern, Complex.norm_exp, re_two_I_mul, Complex.sub_im, Real.exp_le_one_iff]
      have := im_Phi_le hT hT1 hz (le_of_lt hs)
      nlinarith
    rw [← mul_assoc, norm_mul]
    calc _ ≤ 1 * (kR T (T - a ^ 2) * (1 + B) * (1 / (T - a ^ 2 + (z.im + s) ^ 2))) :=
          mul_le_mul h1 (Cvs.Upstream.HalfStripRayIntegrals.norm_ray_le (rayBound_resid hT hT1 hε) hz (le_of_lt hs)) (norm_nonneg _)
            zero_le_one
      _ = _ := one_mul _
  unfold flux rayInt
  rw [mul_left_comm, norm_mul, Complex.norm_I, one_mul, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (setIntegral_mono_on (hE.const_mul (emph c T z)).norm hmaj measurableSet_Ioi hpt).trans ?_
  rw [integral_const_mul]
  calc kR T (T - a ^ 2) * (1 + B) * ∫ s in Ioi (0 : ℝ), 1 / (T - a ^ 2 + (z.im + s) ^ 2) ≤
        kR T (T - a ^ 2) * (1 + B) * (π / √(T - a ^ 2)) :=
        mul_le_mul_of_nonneg_left (Cvs.Upstream.HalfStripRayIntegrals.integral_shift_le (hm hT) z.im) (by positivity)
    _ = vV a T * (1 + B) := by unfold vV; ring

end

end Cvs.Prolate.LiouvilleGreen.RecessiveVolterra

end
