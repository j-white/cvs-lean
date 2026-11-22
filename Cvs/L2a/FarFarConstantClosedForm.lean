import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ChebyshevRampBound
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarFarProfileClosedForm
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.RampIntegrals
import Cvs.L2a.RampOnePieceBounds
import Cvs.L2a.RampTwoPieceBounds
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `C_η` in closed form

`‖w b₁‖² ≤ π²J₁ + 8πν₂J₂ + 16ν₂²J₃` with `Jᵢ = qᵢ + κᵢ√5 Λ` over `ℚ(√5)` (Chebyshev on `[3/2, 2]`, exact primitives),
`‖w bᵢ‖ ≤ √(2/3) Kᵢ` for `i = 2, 3, 4` from `|bᵢ| ≤ Kᵢ/y`, and Cvs.L2a.ChebyshevRampBound–`RampTwoPieceBounds`'s `νᵢ`. `FarFarBound`'s `farFar_le` then holds
with `C_η = (2/π)(β₁ + β₂/c + β₃/c² + β₄/c³)²` closed, whose limit is `2πJ₁ + 16ν₂J₂ + (32/π)ν₂²J₃`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.FarIntegrationByParts Cvs.L2a.FarFarBound Cvs.L2a.RampIntegrals Cvs.L2a.FarFarProfileClosedForm Cvs.L2a.ChebyshevRampBound Cvs.L2a.RampOnePieceBounds Cvs.L2a.RampTwoPieceBounds

namespace Cvs.L2a.FarFarConstantClosedForm

/-! ### Primitives over `ℚ(√5)` -/

/-- The primitive family `(Ay + By³ + Cy⁵)/(5y² − 9)³ + κ√5 log((√5y − 3)/(√5y + 3))`. -/
def primE (A B C κ y : ℝ) : ℝ :=
  (A * y + B * y ^ 3 + C * y ^ 5) / (5 * y ^ 2 - 9) ^ 3 + κ * √5 * Real.log ((√5 * y - 3) / (√5 * y + 3))

/-- `√5 y > 3` for `y ≥ 3/2`. -/
theorem sqrt_five_mul_sub_pos {y : ℝ} (hy : 3 / 2 ≤ y) : 0 < √5 * y - 3 := by
  have h : (2 : ℝ) < √5 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  nlinarith

/-- `(log((√5y − 3)/(√5y + 3)))′ = 6√5/(5y² − 9)` for `y ≥ 3/2`. -/
theorem hasDerivAt_log_ratio {y : ℝ} (hy : 3 / 2 ≤ y) :
    HasDerivAt (fun y => Real.log ((√5 * y - 3) / (√5 * y + 3))) (6 * √5 / (5 * y ^ 2 - 9)) y := by
  have h1 := sqrt_five_mul_sub_pos hy
  have hy0 : 0 ≤ y := by linarith
  have h2 : 0 < √5 * y + 3 := by positivity
  have hu : HasDerivAt (fun y => √5 * y - 3) (√5) y := by
    simpa using ((hasDerivAt_id y).const_mul (√5)).sub_const 3
  have hv : HasDerivAt (fun y => √5 * y + 3) (√5) y := by
    simpa using ((hasDerivAt_id y).const_mul (√5)).add_const 3
  have := (hu.div hv h2.ne').log (div_pos h1 h2).ne'
  simp only [Pi.div_apply] at this
  refine this.congr_deriv ?_
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hE : 5 * y ^ 2 - 9 = (√5 * y - 3) * (√5 * y + 3) := by linear_combination (-y ^ 2) * h5
  rw [hE]
  field_simp
  ring

/-- The derivative of `primE` on `y ≥ 3/2`. -/
theorem hasDerivAt_primE (A B C κ : ℝ) {y : ℝ} (hy : 3 / 2 ≤ y) :
    HasDerivAt (primE A B C κ) (((A + 3 * B * y ^ 2 + 5 * C * y ^ 4) * (5 * y ^ 2 - 9)
      - 30 * y * (A * y + B * y ^ 3 + C * y ^ 5) + 30 * κ * (5 * y ^ 2 - 9) ^ 3) / (5 * y ^ 2 - 9) ^ 4) y := by
  have hE : 0 < 5 * y ^ 2 - 9 := by nlinarith
  have hN : HasDerivAt (fun y => A * y + B * y ^ 3 + C * y ^ 5) (A + 3 * B * y ^ 2 + 5 * C * y ^ 4) y := by
    have := (((hasDerivAt_id y).const_mul A).add ((hasDerivAt_pow 3 y).const_mul B)).add
      ((hasDerivAt_pow 5 y).const_mul C)
    refine this.congr_deriv ?_
    push_cast; ring
  have hD : HasDerivAt (fun y => (5 * y ^ 2 - 9) ^ 3) (3 * (5 * y ^ 2 - 9) ^ 2 * (10 * y)) y := by
    have := (((hasDerivAt_pow 2 y).const_mul 5).sub_const 9).pow 3
    refine this.congr_deriv ?_
    push_cast; ring
  have := (hN.div hD (by positivity)).add ((hasDerivAt_log_ratio hy).const_mul (κ * √5))
  refine this.congr_deriv ?_
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  rw [show κ * √5 * (6 * √5 / (5 * y ^ 2 - 9)) = 30 * κ / (5 * y ^ 2 - 9) by
    rw [show κ * √5 * (6 * √5 / (5 * y ^ 2 - 9)) = 6 * κ * (√5 * √5) / (5 * y ^ 2 - 9) by ring, h5]; ring]
  field_simp
  ring

/-- `(Ay + By³ + Cy⁵)/(5y² − 9)³ → 0` as `y → ∞` (substitute `t = 1/y`). -/
theorem tendsto_ratE (A B C : ℝ) :
    Tendsto (fun y => (A * y + B * y ^ 3 + C * y ^ 5) / (5 * y ^ 2 - 9) ^ 3) atTop (𝓝 0) := by
  set q : ℝ → ℝ := fun t => (A * t ^ 5 + B * t ^ 3 + C * t) / (5 - 9 * t ^ 2) ^ 3 with hq
  have hc : ContinuousAt q 0 := by
    have hn : ContinuousAt (fun t : ℝ => A * t ^ 5 + B * t ^ 3 + C * t) 0 := by fun_prop
    have hd : ContinuousAt (fun t : ℝ => (5 - 9 * t ^ 2) ^ 3) 0 := by fun_prop
    have h0 : ((5 : ℝ) - 9 * 0 ^ 2) ^ 3 ≠ 0 := by norm_num
    exact hn.div₀ hd h0
  have h := hc.tendsto.comp tendsto_inv_atTop_zero
  have h0 : q 0 = 0 := by simp [hq]
  rw [h0] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
  have hy0 : y ≠ 0 := by positivity
  have hE : 0 < 5 * y ^ 2 - 9 := by nlinarith
  simp only [Function.comp_apply, hq]
  have h' : (5 : ℝ) - 9 * y⁻¹ ^ 2 = (5 * y ^ 2 - 9) / y ^ 2 := by field_simp
  rw [h', div_eq_div_iff (by positivity) (by positivity)]
  field_simp

/-- `log((√5y − 3)/(√5y + 3)) → 0` as `y → ∞`. -/
theorem tendsto_log_ratio : Tendsto (fun y : ℝ => Real.log ((√5 * y - 3) / (√5 * y + 3))) atTop (𝓝 0) := by
  have h5 : 0 < √5 := by positivity
  have h1 : Tendsto (fun y : ℝ => (√5 * y - 3) / (√5 * y + 3)) atTop (𝓝 1) := by
    have hlin : Tendsto (fun y : ℝ => √5 * y + 3) atTop atTop :=
      tendsto_atTop_add_const_right _ 3 (Tendsto.const_mul_atTop h5 tendsto_id)
    have : Tendsto (fun y : ℝ => 1 - 6 / (√5 * y + 3)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hlin)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have : 0 < √5 * y + 3 := by positivity
    field_simp
    ring
  have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  rwa [Real.log_one] at this

/-- `primE → 0` as `y → ∞`. -/
theorem tendsto_primE (A B C κ : ℝ) : Tendsto (primE A B C κ) atTop (𝓝 0) := by
  have := (tendsto_ratE A B C).add (tendsto_log_ratio.const_mul (κ * √5))
  rw [mul_zero, add_zero] at this
  exact this

/-- `(2√5 − 3)/(2√5 + 3) = 11/(29 + 12√5)`, so its log is `−log((29 + 12√5)/11)`. -/
theorem log_ratio_two : Real.log ((√5 * 2 - 3) / (√5 * 2 + 3)) = -Real.log ((29 + 12 * √5) / 11) := by
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 < √5 * 2 + 3 := by positivity
  have hq : 0 < 29 + 12 * √5 := by positivity
  rw [← Real.log_inv, inv_div]
  congr 1
  rw [div_eq_div_iff hp.ne' hq.ne']
  linear_combination (24 : ℝ) * h5

/-- `(3√5/2 − 3)/(3√5/2 + 3) = 1/(9 + 4√5)`, so its log is `−log(9 + 4√5)`. -/
theorem log_ratio_three_halves :
    Real.log ((√5 * (3 / 2) - 3) / (√5 * (3 / 2) + 3)) = -Real.log (9 + 4 * √5) := by
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 < √5 * (3 / 2) + 3 := by positivity
  have hq : 0 < 9 + 4 * √5 := by positivity
  rw [← Real.log_inv, ← one_div]
  congr 1
  rw [div_eq_div_iff hp.ne' hq.ne']
  linear_combination (6 : ℝ) * h5

/-- `Λ = (5/8) log((29 + 12√5)/11) + (3/8) log(9 + 4√5)`, the log part of the one-piece bound. -/
def lamL : ℝ := 5 / 8 * Real.log ((29 + 12 * √5) / 11) + 3 / 8 * Real.log (9 + 4 * √5)

/-- `Λ ≥ 0`. -/
theorem lamL_nonneg : 0 ≤ lamL := by
  have h5 : 0 ≤ √5 := Real.sqrt_nonneg 5
  unfold lamL
  have h1 : 0 ≤ Real.log ((29 + 12 * √5) / 11) := Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have h2 : 0 ≤ Real.log (9 + 4 * √5) := Real.log_nonneg (by linarith)
  positivity

/-- **The one-piece bound in `y`**: `f² = w²g`, `g` nonincreasing and continuous on `[3/2, 2]`, `g ≥ 0` beyond `2`
and `primE′ = g` on `[3/2, ∞)` give `‖f‖² ≤ −(5/8) primE 2 − (3/8) primE (3/2)`, evaluated. -/
theorem nN_sq_le_primE {f g : ℝ → ℝ} {A B C κ : ℝ} (hf : MemLp f 2 (volume.restrict (Ioi (3 / 2))))
    (hfg : ∀ x, 3 / 2 < x → f x ^ 2 = wF x ^ 2 * g x) (hg : AntitoneOn g (Icc (3 / 2) 2))
    (hgc : ContinuousOn g (Icc (3 / 2) 2)) (hg0 : ∀ x, 2 < x → 0 ≤ g x)
    (hG : ∀ y, 3 / 2 ≤ y → HasDerivAt (primE A B C κ) (g y) y) :
    nN f ^ 2 ≤ -(5 / 8) * ((2 * A + 8 * B + 32 * C) / 1331)
      - 3 / 8 * ((3 / 2 * A + 27 / 8 * B + 243 / 32 * C) * (64 / 729)) + κ * √5 * lamL := by
  have hI : uIcc (3 / 2 : ℝ) 2 = Icc (3 / 2) 2 := uIcc_of_le (by norm_num)
  have hmid : ∫ x in (3 / 2 : ℝ)..2, g x = primE A B C κ 2 - primE A B C κ (3 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hG x (by rw [hI] at hx; exact hx.1)) ((hI ▸ hgc).intervalIntegrable)
  have htail : ∫ x in Ioi (2 : ℝ), g x = 0 - primE A B C κ 2 :=
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun x hx => hG x (by linarith [mem_Ici.mp hx]))
      (fun x hx => hg0 x hx) (tendsto_primE A B C κ)
  have h := integral_wF_sq_mul_le hg hgc
  rw [nN_sq_eq_split hf hfg, htail]
  rw [hmid] at h
  have e : -(5 / 8) * primE A B C κ 2 - 3 / 8 * primE A B C κ (3 / 2)
      = -(5 / 8) * ((2 * A + 8 * B + 32 * C) / 1331)
        - 3 / 8 * ((3 / 2 * A + 27 / 8 * B + 243 / 32 * C) * (64 / 729)) + κ * √5 * lamL := by
    unfold primE lamL
    rw [log_ratio_two, log_ratio_three_halves]
    ring
  linarith

/-! ### `β₁`: the leading coefficient, exactly -/

/-- `J₁ = 10/11 + (√5/12)Λ`, the one-piece value of `∫ w² y²/D²`. -/
def jJ₁ : ℝ := 10 / 11 + 1 / 12 * √5 * lamL

/-- `J₂ = 7045/4356 + (2√5/27)Λ`, the one-piece value of `∫ w² y²Y/D³`. -/
def jJ₂ : ℝ := 7045 / 4356 + 2 / 27 * √5 * lamL

/-- `J₃ = 976450/323433 + (65√5/972)Λ`, the one-piece value of `∫ w² y²Y²/D⁴`. -/
def jJ₃ : ℝ := 976450 / 323433 + 65 / 972 * √5 * lamL

/-- `J₁, J₂, J₃ ≥ 0`. -/
theorem jJ_nonneg : 0 ≤ jJ₁ ∧ 0 ≤ jJ₂ ∧ 0 ≤ jJ₃ := by
  have := lamL_nonneg
  unfold jJ₁ jJ₂ jJ₃
  exact ⟨by positivity, by positivity, by positivity⟩

/-- `b₁ = (y/D)(π + 4ν Y/D)`. -/
theorem bI₁_eq (ν y : ℝ) :
    bI₁ ν y = y / (y ^ 2 - 9 / 5) * (π + 4 * ν * ((y ^ 2 - 1) / (y ^ 2 - 9 / 5))) := by
  unfold bI₁; simp only [div_eq_mul_inv, ← inv_pow]; ring

/-- `b₁² ` is nonincreasing on `[3/2, 2]` for `ν ≥ 0`. -/
theorem bI₁_sq_antitoneOn {ν : ℝ} (hν : 0 ≤ ν) : AntitoneOn (fun y => bI₁ ν y ^ 2) (Icc (3 / 2) 2) := by
  intro s hs t ht hst
  simp only
  have hs0 : 0 < s := by linarith [hs.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hDs : 0 < s ^ 2 - 9 / 5 := by nlinarith [hs.1]
  have hDt : 0 < t ^ 2 - 9 / 5 := by nlinarith [ht.1]
  have hYt : 0 < t ^ 2 - 1 := by nlinarith [ht.1]
  have hu : t / (t ^ 2 - 9 / 5) ≤ s / (s ^ 2 - 9 / 5) := by
    rw [div_le_div_iff₀ hDt hDs]
    nlinarith [mul_nonneg (sub_nonneg.2 hst) (by positivity : (0 : ℝ) ≤ s * t + 9 / 5)]
  have hv : (t ^ 2 - 1) / (t ^ 2 - 9 / 5) ≤ (s ^ 2 - 1) / (s ^ 2 - 9 / 5) := by
    rw [div_le_div_iff₀ hDt hDs]
    nlinarith [mul_le_mul hst hst hs0.le ht0.le]
  have hut : 0 ≤ t / (t ^ 2 - 9 / 5) := by positivity
  have hvt : 0 ≤ (t ^ 2 - 1) / (t ^ 2 - 9 / 5) := by positivity
  have hbt : 0 ≤ bI₁ ν t := by rw [bI₁_eq]; have := pi_pos; positivity
  have hb : bI₁ ν t ≤ bI₁ ν s := by
    rw [bI₁_eq, bI₁_eq]
    have := pi_pos
    exact mul_le_mul hu (by gcongr) (by positivity) (hut.trans hu)
  exact pow_le_pow_left₀ hbt hb 2

/-- `b₁²` is continuous on `[3/2, 2]`. -/
theorem bI₁_sq_continuousOn (ν : ℝ) : ContinuousOn (fun y => bI₁ ν y ^ 2) (Icc (3 / 2) 2) := by
  refine ContinuousOn.pow ?_ 2
  have hD : ∀ y ∈ Icc (3 / 2 : ℝ) 2, y ^ 2 - 9 / 5 ≠ 0 := fun y hy => by nlinarith [hy.1]
  have h1 : ContinuousOn (fun y : ℝ => π * y) (Icc (3 / 2) 2) := by fun_prop
  have h2 : ContinuousOn (fun y : ℝ => y ^ 2 - 9 / 5) (Icc (3 / 2) 2) := by fun_prop
  have h3 : ContinuousOn (fun y : ℝ => 4 * ν * y * (y ^ 2 - 1)) (Icc (3 / 2) 2) := by fun_prop
  have h4 : ContinuousOn (fun y : ℝ => (y ^ 2 - 9 / 5) ^ 2) (Icc (3 / 2) 2) := by fun_prop
  exact (h1.div₀ h2 hD).add (h3.div₀ h4 fun y hy => pow_ne_zero 2 (hD y hy))

/-- The primitive of `b₁²`: `π²G₁ + 8πνG₂ + 16ν²G₃` as one `primE`. -/
theorem hasDerivAt_primE_bI₁ (ν : ℝ) {y : ℝ} (hy : 3 / 2 ≤ y) :
    HasDerivAt (primE (π ^ 2 * (-405 / 2) + 8 * π * ν * (-180) + 16 * ν ^ 2 * (-325 / 2))
      (π ^ 2 * 225 + 8 * π * ν * 225 + 16 * ν ^ 2 * (5875 / 27))
      (π ^ 2 * (-125 / 2) + 8 * π * ν * (-625 / 9) + 16 * ν ^ 2 * (-12125 / 162))
      (π ^ 2 * (1 / 12) + 8 * π * ν * (2 / 27) + 16 * ν ^ 2 * (65 / 972))) (bI₁ ν y ^ 2) y := by
  refine (hasDerivAt_primE _ _ _ _ hy).congr_deriv ?_
  have hE : 0 < 5 * y ^ 2 - 9 := by nlinarith
  have hD : y ^ 2 - 9 / 5 ≠ 0 := by nlinarith
  unfold bI₁
  field_simp
  ring

/-- **`β₁²`**: `‖w b₁‖² ≤ π²J₁ + 8πνJ₂ + 16ν²J₃` for every `ν ≥ 0`. -/
theorem nN_wF_mul_bI₁_sq_le {ν : ℝ} (hν : 0 ≤ ν) :
    nN (fun y => wF y * bI₁ ν y) ^ 2 ≤ π ^ 2 * jJ₁ + 8 * π * ν * jJ₂ + 16 * ν ^ 2 * jJ₃ := by
  have hmem : MemLp (fun y => wF y * bI₁ ν y) 2 (volume.restrict (Ioi (3 / 2))) :=
    memLp_wF_mul (by unfold bI₁; fun_prop) fun y hy => abs_bI₁_le hy
  have h := nN_sq_le_primE (g := fun y => bI₁ ν y ^ 2) hmem (fun x _ => by ring) (bI₁_sq_antitoneOn hν)
    (bI₁_sq_continuousOn ν) (fun x _ => sq_nonneg _) (fun y hy => hasDerivAt_primE_bI₁ ν hy)
  refine h.trans (le_of_eq ?_)
  unfold jJ₁ jJ₂ jJ₃
  ring

/-! ### `β₂, β₃, β₄`: the `1/y` majorants -/

/-- `‖1/y‖_{L²(3/2, ∞)} = √(2/3)`. -/
theorem nN_one_div : nN (fun y => 1 / y) = √(2 / 3) := by
  unfold nN
  congr 1
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun y => -y⁻¹) (fun y hy => ?_) (fun y _ => sq_nonneg _)
    (by simpa using tendsto_inv_atTop_zero.neg)]
  · norm_num
  · have hy0 : y ≠ 0 := by have := mem_Ici.mp hy; positivity
    refine (hasDerivAt_inv hy0).neg.congr_deriv ?_
    field_simp

/-- `|b| ≤ K/y` on `(3/2, ∞)` gives `‖w b‖ ≤ √(2/3) K`. -/
theorem nN_wF_mul_le_of_abs_le {b : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (h : ∀ y, 3 / 2 < y → |b y| ≤ K / y) :
    nN (fun y => wF y * b y) ≤ √(2 / 3) * K := by
  have hm : MemLp (fun y : ℝ => 1 / y) 2 (volume.restrict (Ioi (3 / 2))) :=
    memLp_of_le_inv (C := 1) (by fun_prop) fun y hy => by
      have : (0 : ℝ) < y := by linarith
      rw [abs_of_pos (by positivity)]
  have := nN_mono (f := fun y => wF y * b y) (g := fun y => K * (1 / y)) (fun y hy => ?_) (hm.const_mul K)
  · rw [nN_const_mul hK, nN_one_div] at this; linarith
  · obtain ⟨h0, h1, -, -⟩ := wF_bounds y
    rw [abs_mul, abs_of_nonneg h0, mul_one_div]
    exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans (h y hy)

/-! ### The closed constants -/

/-- `ν₂ = √(13/30 + (5/32) log 3 + (3/32) log 5)` (Cvs.L2a.ChebyshevRampBound). -/
def νB₂ : ℝ := √(13 / 30 + 5 / 32 * Real.log 3 + 3 / 32 * Real.log 5)

/-- `ν₃ = √(82747/324000 − (5/256) log 3 − (3/256) log 5)` (Cvs.L2a.RampOnePieceBounds). -/
def νB₃ : ℝ := √(82747 / 324000 - 5 / 256 * Real.log 3 - 3 / 256 * Real.log 5)

/-- `ν₄ = √(13/30 − (5/32) log 3 − (3/32) log 5)` (Cvs.L2a.RampOnePieceBounds). -/
def νB₄ : ℝ := √(13 / 30 - 5 / 32 * Real.log 3 - 3 / 32 * Real.log 5)

/-- `ν₅ = π√(1937/10890 + (1/8) log(15/11))` (Cvs.L2a.RampTwoPieceBounds). -/
def νB₅ : ℝ := π * √(1937 / 10890 + 1 / 8 * Real.log (15 / 11))

/-- `ν₆ = π√(1277/10890 − (1/8) log(15/11))` (Cvs.L2a.RampTwoPieceBounds). -/
def νB₆ : ℝ := π * √(1277 / 10890 - 1 / 8 * Real.log (15 / 11))

/-- `ν₇ = √(72127/324000 − (25/256) log 3 − (15/256) log 5)` (Cvs.L2a.RampOnePieceBounds). -/
def νB₇ : ℝ := √(72127 / 324000 - 25 / 256 * Real.log 3 - 15 / 256 * Real.log 5)

/-- `β₁ = √(π²J₁ + 8πν₂J₂ + 16ν₂²J₃)`. -/
def βB₁ : ℝ := √(π ^ 2 * jJ₁ + 8 * π * νB₂ * jJ₂ + 16 * νB₂ ^ 2 * jJ₃)

/-- `β₂ = √(2/3)·(2000/3)ν₃`. -/
def βB₂ : ℝ := √(2 / 3) * (2000 / 3 * νB₃)

/-- `β₃ = √(2/3)·(10(6ν₅² + 2ν₆² + π⁴)/(9π) + (400/9)ν₆ + 5(4ν₃ + 4ν₅ + 2ν₄ + 4ν₄)²/(2ν₂))`. -/
def βB₃ : ℝ := √(2 / 3) * (10 * (6 * νB₅ ^ 2 + 2 * νB₆ ^ 2 + π ^ 4) / (9 * π) + 400 / 9 * νB₆
  + 5 * (4 * νB₃ + 4 * νB₅ + 2 * νB₄ + 4 * νB₄) ^ 2 / (2 * νB₂))

/-- `β₄ = √(2/3)·(8000/27)ν₇`. -/
def βB₄ : ℝ := √(2 / 3) * (8000 / 27 * νB₇)

/-- The closed far-far constant `C_η(c) = (2/π)(β₁ + β₂/c + β₃/c² + β₄/c³)²`. -/
def cEtaClosed (c : ℝ) : ℝ := cEtaSym βB₁ βB₂ βB₃ βB₄ c

/-- The six `νᵢ` are nonnegative and `ν₂ > 0`. -/
theorem νB_facts : 0 < νB₂ ∧ 0 ≤ νB₃ ∧ 0 ≤ νB₄ ∧ 0 ≤ νB₅ ∧ 0 ≤ νB₆ ∧ 0 ≤ νB₇ := by
  refine ⟨nN_xP₂_pos.trans_le nN_xP₂_le, Real.sqrt_nonneg _, Real.sqrt_nonneg _,
    mul_nonneg pi_pos.le (Real.sqrt_nonneg _), mul_nonneg pi_pos.le (Real.sqrt_nonneg _), Real.sqrt_nonneg _⟩

/-- The four `βᵢ` bound `‖w bᵢ‖` at the closed `νᵢ`. -/
theorem nN_wF_mul_bI_le :
    nN (fun y => wF y * bI₁ νB₂ y) ≤ βB₁ ∧ nN (fun y => wF y * bI₂ νB₃ y) ≤ βB₂
      ∧ nN (fun y => wF y * bI₃ νB₂ νB₃ νB₄ νB₅ νB₆ y) ≤ βB₃ ∧ nN (fun y => wF y * bI₄ νB₇ y) ≤ βB₄ := by
  obtain ⟨h2, h3, h4, h5, h6, h7⟩ := νB_facts
  refine ⟨Real.le_sqrt_of_sq_le (nN_wF_mul_bI₁_sq_le h2.le), ?_, ?_, ?_⟩
  · exact nN_wF_mul_le_of_abs_le (by positivity) fun y hy => by
      have := abs_bI₂_le (ν₃ := νB₃) hy; rwa [abs_of_nonneg h3] at this
  · refine nN_wF_mul_le_of_abs_le (by have := pi_pos; positivity) fun y hy => ?_
    have := abs_bI₃_le (ν₃ := νB₃) (ν₄ := νB₄) (ν₅ := νB₅) (ν₆ := νB₆) h2 hy
    rwa [abs_of_nonneg h6, abs_of_nonneg h4, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * νB₃ + 4 * νB₅ + 2 * νB₄)] at this
  · exact nN_wF_mul_le_of_abs_le (by positivity) fun y hy => by
      have := abs_bI₄_le (ν₇ := νB₇) hy; rwa [abs_of_nonneg h7] at this

open Cvs.L2a.AngularProlateTailPositive Cvs.Upstream.CosineTransformHalfLine in
/-- **The far-far bound, closed**: for `c ≥ 1` and any finite rung family,
`‖wK(wΦ)‖² ≤ (C_η(c)/c) ∫_{Ioi 1} Φ²` with `C_η = cEtaClosed` explicit. -/
theorem farFar_le_closed {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 1 ≤ c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) :
    ∫ y in Ioi 1, ‖(wF y : ℂ)
        * calK c ((Ioi 1).indicator fun x => ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ cEtaClosed c / c * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  obtain ⟨hβ₁, hβ₂, hβ₃, hβ₄⟩ := nN_wF_mul_bI_le
  exact farFar_le_sym a hg hg₁ hg₂c hang hc hχ hχ0 hχc nN_xP₂_le nN_xP₃_le nN_xP₄_le nN_xP₅_le nN_xP₆_le
    nN_xP₇_le hβ₁ hβ₂ hβ₃ hβ₄

/-- The four `βᵢ` are nonnegative. -/
theorem βB_nonneg : 0 ≤ βB₁ ∧ 0 ≤ βB₂ ∧ 0 ≤ βB₃ ∧ 0 ≤ βB₄ := by
  obtain ⟨h2, h3, h4, h5, h6, h7⟩ := νB_facts
  have := pi_pos
  unfold βB₁ βB₂ βB₃ βB₄
  exact ⟨Real.sqrt_nonneg _, by positivity, by positivity, by positivity⟩

/-- `C_η` is nonincreasing on `c > 0`. -/
theorem cEtaClosed_antitoneOn : AntitoneOn cEtaClosed (Ioi 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := βB_nonneg
  exact cEtaSym_antitoneOn h1 h2 h3 h4

open Cvs.L2a.AngularProlateTailPositive Cvs.Upstream.CosineTransformHalfLine in
/-- **Uniform in `c ≥ c₀`**: the far-far bound with the constant frozen at `c₀ ≥ 1`. -/
theorem farFar_le_closed_of_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c c₀ : ℝ} {χ : ι → ℝ}
    (a : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hχ : Function.Injective χ) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) :
    ∫ y in Ioi 1, ‖(wF y : ℂ)
        * calK c ((Ioi 1).indicator fun x => ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ cEtaClosed c₀ / c * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  have h := farFar_le_closed a hg hg₁ hg₂c hang (hc₀.trans hc) hχ hχ0 hχc
  have hmon : cEtaClosed c ≤ cEtaClosed c₀ :=
    cEtaClosed_antitoneOn (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) hc
  have hP : 0 ≤ ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hP)
  exact div_le_div_of_nonneg_right hmon (by linarith)

end Cvs.L2a.FarFarConstantClosedForm

end
