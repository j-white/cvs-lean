import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.Route.Visibility.SpinePairingExteriorTransform
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.Edge.DeepJointShare
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.StepA.OneZeroParitySectors
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.WindowTransformExterior
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The transplant applied: the angle from the exterior data, and `P_{U_D}U_ρ` for high zeros

On `Ω = {s/2 < Re w < 5/2, |Im w| < Y}` a `Transplant` constant `K` turns the data built from the continuation `F`
of `X + aG(0)/(2(1 − s))` into `θ_x(D) ≤ (3K/2 + K_p/4)√E` when `‖F‖², (aG(0))² ≤ E‖r‖²` (caseinf-attack Theorem 4
(b)–(f)), and the transform of `U_ρ` into `‖P_{U_D}U_ρ‖ ≤ 4K x^{|δ_ρ|/2}/|γ_ρ|` for `|γ_ρ| ≥ 2Y` (Theorem 4′). The
bound on `F` also gives `‖Φ_σ‖ ≤ 2x^{|δ_σ|/2}(1 + 1/(1 − 2|δ_σ|))√E‖r‖` (Corollary 5′).
-/

noncomputable section

open Real MeasureTheory Filter Set
open scoped InnerProductSpace ComplexConjugate
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.StepA.Edge.FiniteTopCorrectedClosing (USpan)
open Cvs.StepA.OneZeroParitySectors (ue ve)
open Cvs.StepA.Edge.WindowCoshTransformDuality (coshT wR emb Transplant)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.WindowTransformExterior (ext)
open Cvs.Route.Visibility.SpinePairingExteriorTransform (extComb)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.StepA.Edge.TransplantAngleHighZeros
open Cvs.ZeroCounting

/-! ### The rectangle and the data box -/

/-- The transplant rectangle `Ω = {s/2 < Re w < 5/2, |Im w| < Y}`. -/
def rect (s Y : ℝ) : Set ℂ := {w | s / 2 < w.re ∧ w.re < 5 / 2 ∧ |w.im| < Y}

/-- The data box `{−2 < Re s < 3, |Im s| < Y}`. -/
def sbox (Y : ℝ) : Set ℂ := {s | -2 < s.re ∧ s.re < 3 ∧ |s.im| < Y}

theorem isOpen_sbox (Y : ℝ) : IsOpen (sbox Y) := by
  change IsOpen ({s : ℂ | -2 < s.re} ∩ ({s : ℂ | s.re < 3} ∩ {s : ℂ | |s.im| < Y}))
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))

theorem half_add_mem_sbox {s Y : ℝ} (hs : 0 ≤ s) {w : ℂ} (hw : w ∈ rect s Y) : 1 / 2 + w ∈ sbox Y := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

theorem half_sub_mem_sbox {s Y : ℝ} (hs : 0 ≤ s) {w : ℂ} (hw : w ∈ rect s Y) : 1 / 2 - w ∈ sbox Y := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

/-! ### Complex powers of `x` -/

theorem natCast_cpow_mul_neg {x : ℕ} (hx : (0 : ℝ) < x) (w : ℂ) :
    (x : ℂ) ^ (w / 2) * (x : ℂ) ^ (-(w / 2)) = 1 := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [← Complex.cpow_add _ _ hx0, add_neg_cancel, Complex.cpow_zero]

theorem norm_natCast_cpow {x : ℕ} (hx : (0 : ℝ) < x) (w : ℂ) : ‖(x : ℂ) ^ w‖ = (x : ℝ) ^ w.re := by
  rw [show (x : ℂ) = ((x : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hx]

theorem natCast_cpow_conj {x : ℕ} (w : ℂ) : (x : ℂ) ^ (conj w) = conj ((x : ℂ) ^ w) := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne), Complex.conj_natCast]

/-! ### The transform of `U_ρ` in closed form -/

/-- `∫_{−L/2}^{L/2} cosh(at) dt = 2 sinh(aL/2)/a` for `a ≠ 0`. -/
theorem integral_cosh_mul (L : ℝ) {a : ℂ} (ha : a ≠ 0) :
    ∫ t in -(L / 2)..L / 2, Complex.cosh (a * t) = 2 * Complex.sinh (a * (L / 2 : ℝ)) / a := by
  have h1 := integral_exp_mul_complex (a := -(L / 2)) (b := L / 2) ha
  have h2 := integral_exp_mul_complex (a := -(L / 2)) (b := L / 2) (neg_ne_zero.2 ha)
  have hi1 : IntervalIntegrable (fun t : ℝ => Complex.exp (a * t)) volume (-(L / 2)) (L / 2) :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hi2 : IntervalIntegrable (fun t : ℝ => Complex.exp (-a * t)) volume (-(L / 2)) (L / 2) :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have e : (fun t : ℝ => Complex.cosh (a * t))
      = fun t : ℝ => (Complex.exp (a * t) + Complex.exp (-a * t)) / 2 := by
    ext t; rw [Complex.cosh, neg_mul]
  rw [e, intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2, h1, h2, Complex.sinh]
  push_cast
  field_simp
  ring_nf

/-- `‖sinh u‖ ≤ e^{|Re u|}`. -/
theorem norm_sinh_le (u : ℂ) : ‖Complex.sinh u‖ ≤ Real.exp |u.re| := by
  rw [Complex.sinh, norm_div, Complex.norm_two]
  have h1 : ‖Complex.exp u - Complex.exp (-u)‖ ≤ Real.exp u.re + Real.exp (-u.re) := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
  have h2 : Real.exp u.re ≤ Real.exp |u.re| := Real.exp_le_exp.2 (le_abs_self _)
  have h3 : Real.exp (-u.re) ≤ Real.exp |u.re| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith [div_le_div_of_nonneg_right h1 (by norm_num : (0:ℝ) ≤ 2)]

/-- `ue_z(t) cosh(wt)` as four `cosh`s at `iz ± w`, `iz̄ ± w`. -/
theorem ue_mul_cosh (z w : ℂ) (t : ℝ) :
    (ue z t : ℂ) * Complex.cosh (w * t)
      = (Complex.cosh ((Complex.I * z + w) * t) + Complex.cosh ((Complex.I * z - w) * t)
        + Complex.cosh ((Complex.I * conj z + w) * t) + Complex.cosh ((Complex.I * conj z - w) * t)) / 4 := by
  have hz := Cvs.StepA.Edge.WindowCoshTransformDuality.cosh_I_mul z t
  have hz' := Cvs.StepA.Edge.WindowCoshTransformDuality.cosh_I_mul (conj z) t
  have hu : ue (conj z) t = ue z t := by simp [ue, Real.cosh_neg]
  have hv : ve (conj z) t = -ve z t := by simp [ve, Real.sinh_neg]
  rw [hu, hv] at hz'
  have hue : (ue z t : ℂ) = (Complex.cosh (Complex.I * z * t) + Complex.cosh (Complex.I * conj z * t)) / 2 := by
    rw [hz, hz']; push_cast; ring
  rw [hue]
  simp only [add_mul, sub_mul, Complex.cosh_add, Complex.cosh_sub]
  ring

/-- `2 sinh(aL/2)/a`. -/
def shc (L : ℝ) (a : ℂ) : ℂ := 2 * Complex.sinh (a * (L / 2 : ℝ)) / a

/-- The closed form of `F_{U_z}(w)`: `¼ Σ shc(iz ± w) + shc(iz̄ ± w)`. -/
def ueClosed (L : ℝ) (z w : ℂ) : ℂ :=
  (shc L (Complex.I * z + w) + shc L (Complex.I * z - w) + shc L (Complex.I * conj z + w)
    + shc L (Complex.I * conj z - w)) / 4

/-- The four exponents are nonzero when `|Im w| < |Re z|`. -/
theorem ne_zero_of_im_lt {z w : ℂ} (h : |w.im| < |z.re|) :
    Complex.I * z + w ≠ 0 ∧ Complex.I * z - w ≠ 0 ∧ Complex.I * conj z + w ≠ 0 ∧ Complex.I * conj z - w ≠ 0 := by
  have hp : 0 < |z.re + w.im| := by
    have := abs_sub_abs_le_abs_sub z.re (-w.im); rw [abs_neg, sub_neg_eq_add] at this; linarith
  have hm : 0 < |z.re - w.im| := by have := abs_sub_abs_le_abs_sub z.re w.im; linarith
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩ <;> have h' := congrArg Complex.im h0 <;>
    simp at h' <;> first
    | (rw [show z.re + w.im = 0 by linarith] at hp; simp at hp)
    | (rw [show z.re - w.im = 0 by linarith] at hm; simp at hm)

/-- **The `U` transform in closed form**: `∫ ue_z(t) cosh(wt) dt = ueClosed(L, z, w)` when `|Im w| < |Re z|`. -/
theorem integral_ue_mul_cosh (L : ℝ) {z w : ℂ} (h : |w.im| < |z.re|) :
    ∫ t in -(L / 2)..L / 2, (ue z t : ℂ) * Complex.cosh (w * t) = ueClosed L z w := by
  obtain ⟨h1, h2, h3, h4⟩ := ne_zero_of_im_lt h
  have hi : ∀ a : ℂ, IntervalIntegrable (fun t : ℝ => Complex.cosh (a * t)) volume (-(L / 2)) (L / 2) :=
    fun a => Continuous.intervalIntegrable (by fun_prop) _ _
  simp_rw [ue_mul_cosh]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add ((hi _).add (hi _) |>.add (hi _)) (hi _),
    intervalIntegral.integral_add ((hi _).add (hi _)) (hi _), intervalIntegral.integral_add (hi _) (hi _),
    integral_cosh_mul L h1, integral_cosh_mul L h2, integral_cosh_mul L h3, integral_cosh_mul L h4]
  rfl

/-- `‖shc(L, a)‖ ≤ 2e^{|Re a|L/2}/‖a‖` for `L ≥ 0`. -/
theorem norm_shc_le {L : ℝ} (hL : 0 ≤ L) (a : ℂ) : ‖shc L a‖ ≤ 2 * Real.exp (|a.re| * (L / 2)) / ‖a‖ := by
  unfold shc
  rw [norm_div, norm_mul, Complex.norm_two]
  have h := norm_sinh_le (a * (L / 2 : ℝ))
  have hre : (a * ((L / 2 : ℝ) : ℂ)).re = a.re * (L / 2) := by simp
  rw [hre, abs_mul, abs_of_nonneg (by linarith : 0 ≤ L / 2)] at h
  exact div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)

/-- One exponent: `|Re a| ≤ A` and `|Re z|/2 ≤ |Im a|` give `‖shc(L, a)‖ ≤ 4e^{AL/2}/|Re z|`. -/
theorem norm_shc_le_of {L A : ℝ} (hL : 0 ≤ L) {a z : ℂ} (hz : 0 < |z.re|) (hA : |a.re| ≤ A)
    (him : |z.re| / 2 ≤ |a.im|) : ‖shc L a‖ ≤ 4 * Real.exp (A * (L / 2)) / |z.re| := by
  refine (norm_shc_le hL a).trans ?_
  have hn : |z.re| / 2 ≤ ‖a‖ := him.trans (Complex.abs_im_le_norm a)
  have he : Real.exp (|a.re| * (L / 2)) ≤ Real.exp (A * (L / 2)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hA (by linarith))
  have hpos : 0 < |z.re| / 2 := by linarith
  calc 2 * Real.exp (|a.re| * (L / 2)) / ‖a‖ ≤ 2 * Real.exp (A * (L / 2)) / (|z.re| / 2) :=
        div_le_div₀ (by positivity) (by linarith) hpos hn
    _ = 4 * Real.exp (A * (L / 2)) / |z.re| := by field_simp; ring

/-- **The size of the `U` transform**: for `|Im w| ≤ |Re z|/2`, `Re z ≠ 0`, `L ≥ 0`,
`‖ueClosed(L, z, w)‖ ≤ 4e^{(|Im z| + |Re w|)L/2}/|Re z|`. -/
theorem norm_ueClosed_le {L : ℝ} (hL : 0 ≤ L) {z w : ℂ} (hz : 0 < |z.re|) (hw : |w.im| ≤ |z.re| / 2) :
    ‖ueClosed L z w‖ ≤ 4 * Real.exp ((|z.im| + |w.re|) * (L / 2)) / |z.re| := by
  set M := 4 * Real.exp ((|z.im| + |w.re|) * (L / 2)) / |z.re|
  have hre : ∀ a : ℂ, (a = Complex.I * z + w ∨ a = Complex.I * z - w ∨ a = Complex.I * conj z + w
      ∨ a = Complex.I * conj z - w) → ‖shc L a‖ ≤ M := by
    intro a ha
    refine norm_shc_le_of hL hz ?_ ?_
    · rcases ha with rfl | rfl | rfl | rfl <;> simp <;>
        first
        | (have := abs_add_le (-z.im) w.re; rw [abs_neg] at this; linarith)
        | (have := abs_sub (-z.im) w.re; rw [abs_neg] at this; linarith)
        | (have := abs_add_le z.im w.re; linarith)
        | (have := abs_sub z.im w.re; linarith)
    · have h1 := abs_sub_abs_le_abs_sub z.re w.im
      have h2 := abs_sub_abs_le_abs_sub z.re (-w.im)
      rw [abs_neg, sub_neg_eq_add] at h2
      rcases ha with rfl | rfl | rfl | rfl <;> simp <;> linarith
  unfold ueClosed
  rw [norm_div, Complex.norm_ofNat]
  have h : ‖shc L (Complex.I * z + w) + shc L (Complex.I * z - w) + shc L (Complex.I * conj z + w)
      + shc L (Complex.I * conj z - w)‖ ≤ ‖shc L (Complex.I * z + w)‖ + ‖shc L (Complex.I * z - w)‖
        + ‖shc L (Complex.I * conj z + w)‖ + ‖shc L (Complex.I * conj z - w)‖ := norm_add₄_le
  have := hre _ (Or.inl rfl)
  have := hre _ (Or.inr (Or.inl rfl))
  have := hre _ (Or.inr (Or.inr (Or.inl rfl)))
  have := hre _ (Or.inr (Or.inr (Or.inr rfl)))
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  linarith

/-- `w ↦ shc(L, c + w)` and `w ↦ shc(L, c − w)` are differentiable where the exponent is nonzero. -/
theorem differentiableAt_shc (L : ℝ) {a : ℂ → ℂ} {w : ℂ} (ha : DifferentiableAt ℂ a w) (h0 : a w ≠ 0) :
    DifferentiableAt ℂ (fun w => shc L (a w)) w := by
  unfold shc
  exact ((Complex.differentiable_sinh.differentiableAt.comp w (ha.mul_const _)).const_mul _).div ha h0

/-- **The closed form is holomorphic** where `|Im w| < |Re z|`. -/
theorem differentiableOn_ueClosed (L : ℝ) (z : ℂ) :
    DifferentiableOn ℂ (ueClosed L z) {w | |w.im| < |z.re|} := by
  intro w hw
  obtain ⟨h1, h2, h3, h4⟩ := ne_zero_of_im_lt (z := z) (w := w) hw
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold ueClosed
  refine ((((differentiableAt_shc L ?_ h1).add (differentiableAt_shc L ?_ h2)).add
    (differentiableAt_shc L ?_ h3)).add (differentiableAt_shc L ?_ h4)).div_const _ <;> fun_prop

/-- `F_{U_z}(w) = ∫ ue_z(t) cosh(wt) dt` for the window class of `U_z`. -/
theorem coshT_emb_ueVec {x : ℕ} (hx0 : (0 : ℝ) < x) (z w : ℂ) :
    coshT x (emb x (ueVec hx0 z)) w
      = ∫ t in -(Real.log x / 2)..Real.log x / 2, (ue z t : ℂ) * Complex.cosh (w * t) := by
  have hL := Real.log_natCast_nonneg x
  unfold coshT
  refine intervalIntegral.integral_congr_ae ?_
  have hshift := (measurePreserving_add_right (volume : Measure ℝ) (Real.log x / 2)).quasiMeasurePreserving.ae_eq_comp
    (Cvs.Route.Visibility.VisibilityClosingStep.coe_ueVec_ae hx0 z)
  filter_upwards [hshift, (Set.countable_singleton (Real.log x / 2)).ae_notMem volume] with t h1 ht hmem
  have ht : t ≠ Real.log x / 2 := ht
  rw [Set.uIoc_of_le (by linarith)] at hmem
  have hm : t + Real.log x / 2 ∈ Set.Ico 0 (Real.log x) :=
    ⟨by linarith [hmem.1], by linarith [lt_of_le_of_ne hmem.2 ht]⟩
  have e : Cvs.StepA.Edge.WindowCoshTransformDuality.rep x (emb x (ueVec hx0 z)) t = ue z t := by
    have h1' : Cvs.StepA.Edge.WindowCoshTransformDuality.rep x (emb x (ueVec hx0 z)) t
        = (Set.Ico 0 (Real.log x)).indicator (Cvs.Route.Visibility.VisibilityClosingStep.ueProf x z) (t + Real.log x / 2) := h1
    rw [h1', Set.indicator_of_mem hm, Cvs.Route.Visibility.VisibilityClosingStep.ueProf, add_sub_cancel_right]
  rw [e]

/-- **Theorem 4′ for a high zero**: with `Transplant x (w(D)) Ω Ω K K_p` on `Ω = rect s Y`, `s ≥ 0`,
`2Y ≤ |γ_ρ|`, `Y > 0`: `‖P_{U_D}U_ρ‖ ≤ K·4x^{|δ_ρ|/2}/|γ_ρ|`. -/
theorem norm_proj_ueVec_le {x : ℕ} (hx0 : (0 : ℝ) < x) {D : Finset nonTrivialZeroSet} {s Y K Kp : ℝ} (hs : 0 ≤ s)
    (hT : Transplant x (wR '' (D : Set nonTrivialZeroSet)) (rect s Y) (rect s Y) K Kp)
    (ρ : nonTrivialZeroSet) (hY : 0 < Y) (hγ : 2 * Y ≤ |(ρ : ℂ).im|) :
    ‖(USpan hx0 D).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖
      ≤ K * (4 * (x : ℝ) ^ (|Cvs.GaussKernel.del ρ| / 2) / |(ρ : ℂ).im|) := by
  set L := Real.log x with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg x
  set z := Cvs.ZeroCounting.zPoint ρ
  have hzre : z.re = (ρ : ℂ).im := Cvs.ZeroCounting.zPoint_re ρ
  have hzim : |z.im| = |Cvs.GaussKernel.del ρ| := by
    rw [Cvs.ZeroCounting.zPoint_im, abs_neg]; rfl
  have hγpos : 0 < |z.re| := by rw [hzre]; linarith
  set U := ueVec hx0 z
  set d : ℂ → ℂ := fun w => (x : ℂ) ^ (-(w / 2)) * coshT x (emb x U) w with hd
  have hinΩ : ∀ w ∈ rect s Y, |w.im| ≤ |z.re| / 2 := fun w hw => by
    rw [hzre]; linarith [hw.2.2]
  have hcl : ∀ w ∈ rect s Y, coshT x (emb x U) w = ueClosed L z w := fun w hw => by
    rw [coshT_emb_ueVec, integral_ue_mul_cosh]
    linarith [hinΩ w hw]
  have hdiff : DifferentiableOn ℂ d (rect s Y) := by
    have h1 : DifferentiableOn ℂ (fun w => (x : ℂ) ^ (-(w / 2)) * ueClosed L z w) (rect s Y) := by
      refine DifferentiableOn.mul ?_ ((differentiableOn_ueClosed L z).mono fun w hw => ?_)
      · intro w _
        exact (DifferentiableAt.const_cpow (by fun_prop)
          (Or.inl (by exact_mod_cast hx0.ne'))).differentiableWithinAt
      · show |w.im| < |z.re|
        linarith [hinΩ w hw]
    exact h1.congr fun w hw => by simp only [hd, hcl w hw]
  have hconj : ∀ w ∈ rect s Y, d (conj w) = conj (d w) := fun w _ => by
    simp only [hd]
    rw [map_mul, ← natCast_cpow_conj, Cvs.StepA.Edge.WindowCoshTransformDuality.coshT_conj]
    congr 2
    simp [map_neg, map_div₀, map_ofNat]
  set M := 4 * (x : ℝ) ^ (|Cvs.GaussKernel.del ρ| / 2) / |(ρ : ℂ).im| with hM
  have hbound : ∀ w ∈ rect s Y, ‖d w‖ ≤ M := fun w hw => by
    have hre : 0 < w.re := by linarith [hw.1]
    simp only [hd]
    rw [norm_mul, norm_natCast_cpow hx0, hcl w hw]
    have h := norm_ueClosed_le hL hγpos (hinΩ w hw)
    rw [hzim, abs_of_pos hre, hzre] at h
    have hneg : (-(w / 2)).re = -(w.re / 2) := by simp
    rw [hneg]
    have hexp : Real.exp (L * -(w.re / 2)) * Real.exp ((|Cvs.GaussKernel.del ρ| + w.re) * (L / 2))
        = Real.exp (L * (|Cvs.GaussKernel.del ρ| / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e1 : (x : ℝ) ^ (-(w.re / 2)) * (4 * Real.exp ((|Cvs.GaussKernel.del ρ| + w.re) * (L / 2)) / |(ρ : ℂ).im|)
        = M := by
      rw [hM, Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0, ← hLdef, ← hexp]
      ring
    rw [← e1]
    exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx0.le _)
  obtain ⟨v, hv, hvn⟩ := hT d M 0 hdiff hconj hbound
  rw [abs_zero, mul_zero, add_zero] at hvn
  refine (Cvs.StepA.Edge.WindowCoshTransformDuality.norm_proj_USpan_le hx0 U v fun ρ' hρ' => ?_).trans hvn
  have hw := hv (wR ρ') ⟨ρ', hρ', rfl⟩
  rw [Complex.ofReal_zero, zero_div, add_zero, hd, ← mul_assoc, natCast_cpow_mul_neg hx0, one_mul] at hw
  rw [hw, ← Cvs.StepA.Edge.WindowCoshTransformDuality.inner_emb_ueVec_eq_re hx0 (emb x U) ρ', LinearIsometry.inner_map_map]

/-! ### The exterior data -/

/-- `|δ_ρ| < ½` for a nontrivial zero. -/
theorem abs_del_lt_half (ρ : nonTrivialZeroSet) : |Cvs.GaussKernel.del ρ| < 1 / 2 := by
  obtain ⟨-, h0, h1⟩ := ρ.2
  rw [abs_lt]; constructor <;> simp only [Cvs.GaussKernel.del] <;> linarith

/-- `Φ_ρ = x^{w/2}X(½ + w) + x^{−w/2}X(½ − w)` at `w = w_ρ`. -/
theorem extComb_eq_wR (x : ℕ) (G : ℝ → ℝ) (ρ : nonTrivialZeroSet) :
    extComb x G ρ = (x : ℂ) ^ (wR ρ / 2) * mellinR (ext (1 / x) G) (1 / 2 + wR ρ)
      + (x : ℂ) ^ (-(wR ρ / 2)) * mellinR (ext (1 / x) G) (1 / 2 - wR ρ) := by
  unfold extComb wR
  split_ifs
  · congr 3 <;> ring
  · rw [add_comm]; congr 3 <;> ring

/-- `½ ± w_ρ` lie in the data box of height `Y` when `|γ_ρ| < Y`, with real part below `1`. -/
theorem half_pm_wR_mem {ρ : nonTrivialZeroSet} {Y : ℝ} (hY : |(ρ : ℂ).im| < Y) :
    (1 / 2 + wR ρ ∈ sbox Y ∧ (1 / 2 + wR ρ).re < 1) ∧ (1 / 2 - wR ρ ∈ sbox Y ∧ (1 / 2 - wR ρ).re < 1) := by
  have hre := Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re ρ
  have him := Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im ρ
  have h1 := abs_del_lt_half ρ
  have h0 := abs_nonneg (Cvs.GaussKernel.del ρ)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩ <;> simp only [Complex.add_re, Complex.sub_re,
    Complex.add_im, Complex.sub_im, hre] <;> norm_num <;> linarith

/-- **The data identity**: with `F(½ ± w) = X(½ ± w) + g/(2(1 − (½ ± w)))`,
`x^{w/2}(d(w) − (g/4)/(w − ½)) = −½(x^{w/2}X(½ + w) + x^{−w/2}X(½ − w))`. -/
theorem data_identity {x : ℕ} (hx0 : (0 : ℝ) < x) (X F : ℂ → ℂ) (g : ℂ) {w : ℂ} (h1 : (1 : ℂ) / 2 - w ≠ 0)
    (hF1 : F (1 / 2 + w) = X (1 / 2 + w) + g / (2 * (1 - (1 / 2 + w))))
    (hF2 : F (1 / 2 - w) = X (1 / 2 - w) + g / (2 * (1 - (1 / 2 - w)))) :
    (x : ℂ) ^ (w / 2) * ((-(1 / 2) * F (1 / 2 + w)
        - 1 / 2 * (x : ℂ) ^ (-w) * (F (1 / 2 - w) - g / (2 * (1 / 2 + w)))) + -(g / 4) / (w - 1 / 2))
      = -(1 / 2) * ((x : ℂ) ^ (w / 2) * X (1 / 2 + w) + (x : ℂ) ^ (-(w / 2)) * X (1 / 2 - w)) := by
  have hx : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hc : (x : ℂ) ^ (-(w / 2)) = (x : ℂ) ^ (w / 2) * (x : ℂ) ^ (-w) := by
    rw [← Complex.cpow_add _ _ hx]; congr 1; ring
  have e1 : (1 : ℂ) - (1 / 2 + w) = 1 / 2 - w := by ring
  have e2 : (1 : ℂ) - (1 / 2 - w) = 1 / 2 + w := by ring
  have h3 : w - 1 / 2 ≠ 0 := fun h => h1 (by linear_combination -h)
  have hz : -(1 / 2) * (g / (2 * (1 / 2 - w))) + -(g / 4) / (w - 1 / 2) = 0 := by
    rw [show w - 1 / 2 = -(1 / 2 - w) by ring]
    field_simp
    ring
  rw [hF1, hF2, e1, e2, hc]
  linear_combination (x : ℂ) ^ (w / 2) * hz

/-- The value `aG(0) = x⁻¹G_a(0)` at `x`. -/
abbrev g0 (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ := 1 / (x : ℝ) * Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a 0

/-- **The exterior data at `x` with constant `E`**: `(aG(0))² ≤ E‖r_a‖²`, and a conjugate-symmetric holomorphic
`F` on the box of height `x` equal to `X + aG(0)/(2(1 − s))` for `Re s < 1`, with `‖F‖² ≤ E‖r_a‖²` there. -/
def ExtData (x : ℕ) (E : ℝ) : Prop :=
  ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, g0 x a ^ 2 ≤ E * Cvs.Route.Visibility.ExteriorFactorMTwo.rNorm x a ^ 2 ∧
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (sbox x) ∧ (∀ s ∈ sbox x, F (conj s) = conj (F s)) ∧
      (∀ s ∈ sbox x, s.re < 1 →
        F s = mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) s + (g0 x a : ℂ) / (2 * (1 - s))) ∧
      ∀ s ∈ sbox x, ‖F s‖ ^ 2 ≤ E * Cvs.Route.Visibility.ExteriorFactorMTwo.rNorm x a ^ 2

/-- **The angle from the exterior data** (caseinf-attack Theorem 4 (b)–(f)): with `Transplant` on `Ω = rect s Y`,
`0 < s`, `Y ≤ x`, `|γ_ρ| < x` on `D`, and `ExtData x E`, `θ_x(D) ≤ (3K/2 + K_p/4)√E`. -/
theorem angle_le_of_extData {x : ℕ} (hx : 80 ≤ 2 * π * x) (hx0 : (0 : ℝ) < x) {D : Finset nonTrivialZeroSet}
    {s Y K Kp E : ℝ} (hs : 0 < s) (hYx : Y ≤ x)
    (hT : Transplant x (wR '' (D : Set nonTrivialZeroSet)) (rect s Y) (rect s Y) K Kp) (hK : 0 ≤ K)
    (hKp : 0 ≤ Kp) (hD : ∀ ρ ∈ D, |(ρ : ℂ).im| < x) (hdat : ExtData x E) :
    Cvs.StepA.Edge.DeepJointShare.angle hx0 D ≤ (3 / 2 * K + Kp / 4) * √E := by
  refine Cvs.StepA.Edge.WindowCoshTransformDuality.angle_le_of_interp hx0 (by positivity) fun r hr => ?_
  obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
  set R := Cvs.Route.Visibility.ExteriorFactorMTwo.rNorm x a with hR
  have hR0 : 0 ≤ R := norm_nonneg _
  obtain ⟨hg, F, hFd, hFc, hFf, hFb⟩ := hdat a
  set g := g0 x a
  have hFn : ∀ s ∈ sbox x, ‖F s‖ ≤ √E * R := fun s hs => Cvs.Route.Visibility.ExteriorFactorMTwo.norm_le_sqrt_mul hR0 (hFb s hs)
  have hgn : |g| ≤ √E * R := by
    have := Cvs.Route.Visibility.ExteriorFactorMTwo.norm_le_sqrt_mul (y := (g : ℂ)) hR0 (by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; exact hg)
    rwa [Complex.norm_real, Real.norm_eq_abs] at this
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  set d : ℂ → ℂ := fun w => -(1 / 2) * F (1 / 2 + w)
    - 1 / 2 * (x : ℂ) ^ (-w) * (F (1 / 2 - w) - (g : ℂ) / (2 * (1 / 2 + w))) with hd
  have hYs : ∀ w ∈ rect s Y, 1 / 2 + w ∈ sbox x ∧ 1 / 2 - w ∈ sbox x := fun w hw => by
    have hw' : w ∈ rect s x := ⟨hw.1, hw.2.1, hw.2.2.trans_le hYx⟩
    exact ⟨half_add_mem_sbox hs.le hw', half_sub_mem_sbox hs.le hw'⟩
  have hne : ∀ w ∈ rect s Y, (1 : ℂ) / 2 + w ≠ 0 := fun w hw h0 => by
    have := congrArg Complex.re h0; simp at this; linarith [hw.1]
  have hdiff : DifferentiableOn ℂ d (rect s Y) := by
    intro w hw
    obtain ⟨h1, h2⟩ := hYs w hw
    have hF1 : DifferentiableAt ℂ (fun w => F (1 / 2 + w)) w :=
      (hFd.differentiableAt ((isOpen_sbox x).mem_nhds h1)).comp w (by fun_prop)
    have hF2 : DifferentiableAt ℂ (fun w => F (1 / 2 - w)) w :=
      (hFd.differentiableAt ((isOpen_sbox x).mem_nhds h2)).comp w (by fun_prop)
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ (-w)) w :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl hx0')
    have hdiv : DifferentiableAt ℂ (fun w : ℂ => (g : ℂ) / (2 * (1 / 2 + w))) w :=
      have hden : DifferentiableAt ℂ (fun w : ℂ => 2 * (1 / 2 + w)) w := by fun_prop
      DifferentiableAt.div (c := fun _ : ℂ => (g : ℂ)) (d := fun w : ℂ => 2 * (1 / 2 + w))
        (differentiableAt_const _) hden (mul_ne_zero two_ne_zero (hne w hw))
    exact ((hF1.const_mul (-(1 / 2))).sub ((hpow.const_mul (1 / 2)).mul (hF2.sub hdiv))).differentiableWithinAt
  have hconj : ∀ w ∈ rect s Y, d (conj w) = conj (d w) := fun w hw => by
    obtain ⟨h1, h2⟩ := hYs w hw
    have e1 : (1 : ℂ) / 2 + conj w = conj (1 / 2 + w) := by simp [map_add, map_ofNat]
    have e2 : (1 : ℂ) / 2 - conj w = conj (1 / 2 - w) := by simp [map_sub, map_ofNat]
    have e3 : (x : ℂ) ^ (-conj w) = conj ((x : ℂ) ^ (-w)) := by rw [← map_neg, natCast_cpow_conj]
    simp only [hd]
    rw [e1, e2, e3, hFc _ h1, hFc _ h2]
    simp [map_sub, map_mul, map_div₀, map_neg, Complex.conj_ofReal, map_ofNat]
  have hx1 : (1 : ℝ) ≤ x := by
    have : 0 < x := by exact_mod_cast hx0
    exact_mod_cast this
  have hbound : ∀ w ∈ rect s Y, ‖d w‖ ≤ 3 / 2 * √E * R := fun w hw => by
    obtain ⟨h1, h2⟩ := hYs w hw
    have hre : 0 < w.re := by linarith [hw.1]
    have hpw : ‖(x : ℂ) ^ (-w)‖ ≤ 1 := by
      rw [norm_natCast_cpow hx0, Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hden : 1 ≤ ‖(2 : ℂ) * (1 / 2 + w)‖ := by
      rw [norm_mul, Complex.norm_two]
      have := Complex.re_le_norm (1 / 2 + w)
      simp at this
      linarith
    have hgd : ‖(g : ℂ) / (2 * (1 / 2 + w))‖ ≤ |g| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_self (abs_nonneg _) hden
    have hA := hFn _ h1
    have hB := hFn _ h2
    have hsub : ‖F (1 / 2 - w) - (g : ℂ) / (2 * (1 / 2 + w))‖ ≤ 2 * (√E * R) :=
      (norm_sub_le _ _).trans (by linarith)
    simp only [hd]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_neg]
    norm_num
    have hp0 := norm_nonneg ((x : ℂ) ^ (-w))
    have hs0 := norm_nonneg (F (1 / 2 - w) - (g : ℂ) / (2 * (1 / 2 + w)))
    nlinarith [mul_le_mul hpw hsub hs0 zero_le_one]
  obtain ⟨v, hv, hvn⟩ := hT d (3 / 2 * √E * R) (-(g / 4)) hdiff hconj hbound
  refine ⟨v, fun ρ hρ => ?_, ?_⟩
  · have hw := hv (wR ρ) ⟨ρ, hρ, rfl⟩
    obtain ⟨⟨hm1, hr1⟩, ⟨hm2, hr2⟩⟩ := half_pm_wR_mem (hD ρ hρ)
    have hre := Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re ρ
    have hδ := abs_del_lt_half ρ
    have hn1 : (1 : ℂ) / 2 - wR ρ ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp [hre] at this; linarith
    have hid := data_identity hx0 (mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))) F (g : ℂ) hn1
      (hFf _ hm1 hr1) (hFf _ hm2 hr2)
    rw [show (((-(g / 4) : ℝ)) : ℂ) = -((g : ℂ) / 4) by push_cast; ring] at hw
    simp only [hd] at hw
    rw [hw, hid, ← extComb_eq_wR, Cvs.Route.Visibility.ShareBesselFromExtPairing.inner_evenPart_spineMap_ueVec hx hx0 a ρ]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im]
    norm_num
    ring
  · refine hvn.trans ?_
    have hc : |(-(g / 4))| ≤ √E * R / 4 := by rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith
    have hE0 : 0 ≤ √E * R := mul_nonneg (Real.sqrt_nonneg _) hR0
    nlinarith [mul_le_mul_of_nonneg_left hc hKp]

/-- **The pairing from the exterior data** (caseinf-attack Corollary 5′): with `ExtData x E`, `E ≥ 0`, and
`|γ_σ| < x`, `‖Φ_σ(a)‖ ≤ 2·x^{|δ_σ|/2}(1 + 1/(1 − 2|δ_σ|))√E·‖r_a‖`. -/
theorem norm_extComb_le_of_extData {x : ℕ} (hx0 : (0 : ℝ) < x) {E : ℝ} (hdat : ExtData x E)
    {σ : nonTrivialZeroSet} (hσ : |(σ : ℂ).im| < x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ‖extComb x (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) σ‖
      ≤ 2 * ((x : ℝ) ^ (|Cvs.GaussKernel.del σ| / 2) * (1 + 1 / (1 - 2 * |Cvs.GaussKernel.del σ|)) * √E)
        * Cvs.Route.Visibility.ExteriorFactorMTwo.rNorm x a := by
  set R := Cvs.Route.Visibility.ExteriorFactorMTwo.rNorm x a
  have hR0 : 0 ≤ R := norm_nonneg _
  obtain ⟨hg, F, -, -, hFf, hFb⟩ := hdat a
  set g := g0 x a
  have hFn : ∀ s ∈ sbox x, ‖F s‖ ≤ √E * R := fun s hs => Cvs.Route.Visibility.ExteriorFactorMTwo.norm_le_sqrt_mul hR0 (hFb s hs)
  have hgn : |g| ≤ √E * R := by
    have := Cvs.Route.Visibility.ExteriorFactorMTwo.norm_le_sqrt_mul (y := (g : ℂ)) hR0 (by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; exact hg)
    rwa [Complex.norm_real, Real.norm_eq_abs] at this
  have hx1 : (1 : ℝ) ≤ x := by
    have : 0 < x := by exact_mod_cast hx0
    exact_mod_cast this
  set δ := |Cvs.GaussKernel.del σ|
  have hδ : δ < 1 / 2 := abs_del_lt_half σ
  have hδ0 : 0 ≤ δ := abs_nonneg _
  have hpos : 0 < 1 - 2 * δ := by linarith
  have hre := Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re σ
  obtain ⟨⟨hm1, hr1⟩, ⟨hm2, hr2⟩⟩ := half_pm_wR_mem hσ
  set X := mellinR (ext (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))
  set w := wR σ
  have hXb : ∀ s ∈ sbox x, s.re < 1 → 1 - 2 * δ ≤ ‖(2 : ℂ) * (1 - s)‖ → ‖X s‖ ≤ (1 + 1 / (1 - 2 * δ)) * (√E * R) := by
    intro s hs hr hden
    have hX : X s = F s - (g : ℂ) / (2 * (1 - s)) := by rw [hFf s hs hr]; ring
    rw [hX]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |g| / ‖(2 : ℂ) * (1 - s)‖ ≤ √E * R / (1 - 2 * δ) :=
      div_le_div₀ (by positivity) hgn hpos hden
    have := hFn s hs
    have e : (1 + 1 / (1 - 2 * δ)) * (√E * R) = √E * R + √E * R / (1 - 2 * δ) := by ring
    linarith
  have hd1 : 1 - 2 * δ ≤ ‖(2 : ℂ) * (1 - (1 / 2 + w))‖ := by
    rw [norm_mul, Complex.norm_two]
    have := Complex.re_le_norm (1 - (1 / 2 + w))
    simp [hre] at this
    linarith
  have hd2 : 1 - 2 * δ ≤ ‖(2 : ℂ) * (1 - (1 / 2 - w))‖ := by
    rw [norm_mul, Complex.norm_two]
    have := Complex.re_le_norm (1 - (1 / 2 - w))
    simp [hre] at this
    linarith
  have hX1 := hXb _ hm1 hr1 hd1
  have hX2 := hXb _ hm2 hr2 hd2
  have hp1 : ‖(x : ℂ) ^ (w / 2)‖ = (x : ℝ) ^ (δ / 2) := by
    rw [norm_natCast_cpow hx0]; congr 1; simp [hre, w]; rfl
  have hp2 : ‖(x : ℂ) ^ (-(w / 2))‖ ≤ (x : ℝ) ^ (δ / 2) := by
    rw [norm_natCast_cpow hx0]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    simp [hre, w]; linarith
  rw [extComb_eq_wR]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hκ : 0 ≤ (1 + 1 / (1 - 2 * δ)) * (√E * R) := by positivity
  have hxδ : 0 ≤ (x : ℝ) ^ (δ / 2) := Real.rpow_nonneg hx0.le _
  have t1 := mul_le_mul hp1.le hX1 (norm_nonneg _) hxδ
  have t2 := mul_le_mul hp2 hX2 (norm_nonneg _) hxδ
  nlinarith

end Cvs.StepA.Edge.TransplantAngleHighZeros

end
