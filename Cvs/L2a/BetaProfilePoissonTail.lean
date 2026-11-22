import Mathlib
import Cvs.Finite.OneModeCertificate
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.CosineTransformSecondOrder
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.Zeta.Digamma
import Cvs.Zeta.Digamma.DigammaQuarterConstant
import Cvs.Zeta.DigammaCriticalAsymptotic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The profile `β = (1 − y²)³(1 − 9y²)` and its Poisson tail `T_β`

`β` clamped to `[−1, 1]` is `C²(ℝ)`, `psi c (a⁻¹β(·/a)) = psi (ca) β`, `Ψ = psi (2π) β` is `O(ξ⁻⁴)`, and
`F_∞(Ψ) = T_β` on `θ > 1`, `C¹` with `T_β' = −T_γ/θ`, `γ = (yβ)'`; `Π₊(Ψ) = ½(49/24 − log 2π)`, `Π₋(Ψ) = 59/630`.
`‖T⁺‖`, `‖log θ·T⁺‖`, `V₀`, `V_{1/2}`, `C_L1` and `C_A` (from `ρ_{T⁺} ≤ V_{1/2}²/(2π(t² + ¼))`) get closed-form and
rational bounds.
-/

namespace Cvs.L2a.BetaProfilePoissonTail

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.FullTailConvergence Cvs.L2a.FullTailPoleChannel

/-! ### Clamped profiles -/

/-- The clamp `max (−1) (min y 1)` of `y` onto `[−1, 1]`. -/
def clamp (y : ℝ) : ℝ := max (-1) (min y 1)

theorem clamp_of_mem {y : ℝ} (h : y ∈ Icc (-1 : ℝ) 1) : clamp y = y := by
  unfold clamp; rw [min_eq_left h.2, max_eq_right h.1]

theorem clamp_of_one_le {y : ℝ} (h : 1 ≤ y) : clamp y = 1 := by
  unfold clamp; rw [min_eq_right h]; norm_num

theorem clamp_of_le_neg_one {y : ℝ} (h : y ≤ -1) : clamp y = -1 := by
  unfold clamp; rw [min_eq_left (by linarith)]; exact max_eq_left h

theorem continuous_clamp : Continuous clamp := by unfold clamp; fun_prop

theorem clamp_neg (y : ℝ) : clamp (-y) = -clamp y := by
  rcases le_or_gt 1 y with h | h
  · rw [clamp_of_le_neg_one (by linarith), clamp_of_one_le h]
  rcases le_or_gt y (-1) with h' | h'
  · rw [clamp_of_one_le (by linarith), clamp_of_le_neg_one h']; norm_num
  rw [clamp_of_mem ⟨by linarith, by linarith⟩, clamp_of_mem ⟨h'.le, h.le⟩]

/-- A derivative is the union of its left and right one-sided derivatives. -/
theorem hasDerivAt_of_Iic_Ici {f : ℝ → ℝ} {d x : ℝ} (hl : HasDerivWithinAt f d (Iic x) x)
    (hr : HasDerivWithinAt f d (Ici x) x) : HasDerivAt f d x := by
  have h := hl.union hr
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h

/-- **Clamping keeps a derivative** whose value vanishes at `±1`: `(p ∘ clamp)' = p' ∘ clamp`. -/
theorem hasDerivAt_comp_clamp {p p' : ℝ → ℝ} (hp : ∀ y, HasDerivAt p (p' y) y) (h1 : p' 1 = 0)
    (hm1 : p' (-1) = 0) (y : ℝ) : HasDerivAt (fun y => p (clamp y)) (p' (clamp y)) y := by
  have hconst : ∀ (a : ℝ) (s : Set ℝ), HasDerivWithinAt (fun _ : ℝ => p a) 0 s y :=
    fun a s => hasDerivWithinAt_const _ _ _
  rcases lt_trichotomy y 1 with hy1 | rfl | hy1
  · rcases lt_trichotomy y (-1) with hym | rfl | hym
    · rw [clamp_of_le_neg_one hym.le, hm1]
      refine (hasDerivAt_const y (p (-1))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hym] with z hz
      rw [clamp_of_le_neg_one (le_of_lt hz)]
    · rw [clamp_of_le_neg_one le_rfl, hm1]
      refine hasDerivAt_of_Iic_Ici ?_ ?_
      · refine (hconst (-1) _).congr_of_eventuallyEq ?_ (by rw [clamp_of_le_neg_one le_rfl])
        filter_upwards [self_mem_nhdsWithin] with z hz
        rw [clamp_of_le_neg_one hz]
      · have h := (hp (-1)).hasDerivWithinAt (s := Ici (-1))
        rw [hm1] at h
        refine h.congr_of_eventuallyEq ?_ (by rw [clamp_of_le_neg_one le_rfl])
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hy1)] with z hz hz'
        rw [clamp_of_mem ⟨hz, le_of_lt hz'⟩]
    · rw [clamp_of_mem ⟨hym.le, hy1.le⟩]
      refine (hp y).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hym hy1] with z hz
      rw [clamp_of_mem ⟨hz.1.le, hz.2.le⟩]
  · rw [clamp_of_one_le le_rfl, h1]
    refine hasDerivAt_of_Iic_Ici ?_ ?_
    · have h := (hp 1).hasDerivWithinAt (s := Iic 1)
      rw [h1] at h
      refine h.congr_of_eventuallyEq ?_ (by rw [clamp_of_one_le le_rfl])
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds (show (-1 : ℝ) < 1 by norm_num))]
        with z hz hz'
      rw [clamp_of_mem ⟨le_of_lt hz', hz⟩]
    · refine (hconst 1 _).congr_of_eventuallyEq ?_ (by rw [clamp_of_one_le le_rfl])
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [clamp_of_one_le hz]
  · rw [clamp_of_one_le hy1.le, h1]
    refine (hasDerivAt_const y (p 1)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy1] with z hz
    rw [clamp_of_one_le (le_of_lt hz)]

/-! ### The polynomial `(1 − y²)³(1 − 9y²)` and its derivatives -/

/-- `(1 − y²)³(1 − 9y²) = 1 − 12y² + 30y⁴ − 28y⁶ + 9y⁸`. -/
def betaPoly (y : ℝ) : ℝ := 1 - 12 * y ^ 2 + 30 * y ^ 4 - 28 * y ^ 6 + 9 * y ^ 8

/-- The first derivative of `betaPoly`. -/
def betaPoly1 (y : ℝ) : ℝ := -24 * y + 120 * y ^ 3 - 168 * y ^ 5 + 72 * y ^ 7

/-- The second derivative of `betaPoly`. -/
def betaPoly2 (y : ℝ) : ℝ := -24 + 360 * y ^ 2 - 840 * y ^ 4 + 504 * y ^ 6

/-- The third derivative of `betaPoly`. -/
def betaPoly3 (y : ℝ) : ℝ := 720 * y - 3360 * y ^ 3 + 3024 * y ^ 5

/-- The fourth derivative of `betaPoly`. -/
def betaPoly4 (y : ℝ) : ℝ := 720 - 10080 * y ^ 2 + 15120 * y ^ 4

/-- The primitive `B(x) = x(1 − x²)⁴` of `betaPoly`. -/
def bigBPoly (x : ℝ) : ℝ := x * (1 - x ^ 2) ^ 4

theorem betaPoly_eq (y : ℝ) : betaPoly y = (1 - y ^ 2) ^ 3 * (1 - 9 * y ^ 2) := by unfold betaPoly; ring

theorem hasDerivAt_mono (a : ℝ) (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => a * y ^ (n + 1)) (a * ((n + 1 : ℕ) : ℝ) * y ^ n) y := by
  have h := (hasDerivAt_pow (n + 1) y).const_mul a
  simpa [mul_assoc] using h

theorem hasDerivAt_betaPoly (y : ℝ) : HasDerivAt betaPoly (betaPoly1 y) y := by
  have h := ((((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_mono 12 1 y)).add (hasDerivAt_mono 30 3 y)).sub
    (hasDerivAt_mono 28 5 y)).add (hasDerivAt_mono 9 7 y)
  refine (h.congr_deriv (by simp only [betaPoly1]; push_cast; ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun z => ?_)
  simp only [betaPoly, Pi.add_apply, Pi.sub_apply]; try ring

theorem hasDerivAt_betaPoly1 (y : ℝ) : HasDerivAt betaPoly1 (betaPoly2 y) y := by
  have h := (((hasDerivAt_mono (-24) 0 y).add (hasDerivAt_mono 120 2 y)).sub (hasDerivAt_mono 168 4 y)).add
    (hasDerivAt_mono 72 6 y)
  refine (h.congr_deriv (by simp only [betaPoly2]; push_cast; ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun z => ?_)
  simp only [betaPoly1, Pi.add_apply, Pi.sub_apply]; try ring

theorem hasDerivAt_betaPoly2 (y : ℝ) : HasDerivAt betaPoly2 (betaPoly3 y) y := by
  have h := ((((hasDerivAt_const y (-24 : ℝ)).add (hasDerivAt_mono 360 1 y)).sub (hasDerivAt_mono 840 3 y)).add
    (hasDerivAt_mono 504 5 y))
  refine (h.congr_deriv (by simp only [betaPoly3]; push_cast; ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun z => ?_)
  simp only [betaPoly2, Pi.add_apply, Pi.sub_apply]; try ring

theorem hasDerivAt_betaPoly3 (y : ℝ) : HasDerivAt betaPoly3 (betaPoly4 y) y := by
  have h := ((hasDerivAt_mono 720 0 y).sub (hasDerivAt_mono 3360 2 y)).add (hasDerivAt_mono 3024 4 y)
  refine (h.congr_deriv (by simp only [betaPoly4]; push_cast; ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun z => ?_)
  simp only [betaPoly3, Pi.add_apply, Pi.sub_apply]; try ring

theorem hasDerivAt_bigBPoly (x : ℝ) : HasDerivAt bigBPoly (betaPoly x) x := by
  have h := ((hasDerivAt_id x).mul (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).pow 4))
  refine (h.congr_deriv (by simp only [betaPoly, Pi.sub_apply, Pi.pow_apply, id]; push_cast; ring))
    |>.congr_of_eventuallyEq
    (Eventually.of_forall fun z => ?_)
  simp only [bigBPoly, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id]

/-! ### The profile `β` -/

/-- **The profile** `β = betaPoly ∘ clamp`: `(1 − y²)³(1 − 9y²)` on `[−1, 1]`, `0` outside. -/
def beta (y : ℝ) : ℝ := betaPoly (clamp y)

/-- `β' = betaPoly1 ∘ clamp`. -/
def beta1 (y : ℝ) : ℝ := betaPoly1 (clamp y)

/-- `β'' = betaPoly2 ∘ clamp`. -/
def beta2 (y : ℝ) : ℝ := betaPoly2 (clamp y)

/-- The primitive `B = bigBPoly ∘ clamp` of `β`, with `B = 0` off `(−1, 1)`. -/
def bigB (x : ℝ) : ℝ := bigBPoly (clamp x)

theorem hasDerivAt_beta (y : ℝ) : HasDerivAt beta (beta1 y) y :=
  hasDerivAt_comp_clamp hasDerivAt_betaPoly (by norm_num [betaPoly1]) (by norm_num [betaPoly1]) y

theorem hasDerivAt_beta1 (y : ℝ) : HasDerivAt beta1 (beta2 y) y :=
  hasDerivAt_comp_clamp hasDerivAt_betaPoly1 (by norm_num [betaPoly2]) (by norm_num [betaPoly2]) y

theorem hasDerivAt_bigB (x : ℝ) : HasDerivAt bigB (beta x) x :=
  hasDerivAt_comp_clamp hasDerivAt_bigBPoly (by norm_num [betaPoly]) (by norm_num [betaPoly]) x

theorem continuous_beta : Continuous beta := by unfold beta betaPoly; have := continuous_clamp; fun_prop
theorem continuous_beta1 : Continuous beta1 := by unfold beta1 betaPoly1; have := continuous_clamp; fun_prop
theorem continuous_beta2 : Continuous beta2 := by unfold beta2 betaPoly2; have := continuous_clamp; fun_prop

theorem deriv_beta : deriv beta = beta1 := funext fun y => (hasDerivAt_beta y).deriv
theorem deriv_beta1 : deriv beta1 = beta2 := funext fun y => (hasDerivAt_beta1 y).deriv

/-- **`β ∈ C²(ℝ)`.** -/
theorem contDiff_beta : ContDiff ℝ 2 beta := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv, deriv_beta]
  refine ⟨fun y => (hasDerivAt_beta y).differentiableAt, by simp, ?_⟩
  rw [contDiff_one_iff_deriv, deriv_beta1]
  exact ⟨fun y => (hasDerivAt_beta1 y).differentiableAt, continuous_beta2⟩

theorem beta_of_mem {y : ℝ} (h : y ∈ Icc (-1 : ℝ) 1) : beta y = betaPoly y := by rw [beta, clamp_of_mem h]

theorem beta_of_one_le_abs {y : ℝ} (h : 1 ≤ |y|) : beta y = 0 := by
  rcases le_abs'.mp h with h | h
  · rw [beta, clamp_of_le_neg_one h]; norm_num [betaPoly]
  · rw [beta, clamp_of_one_le h]; norm_num [betaPoly]

theorem beta1_of_one_le_abs {y : ℝ} (h : 1 ≤ |y|) : beta1 y = 0 := by
  rcases le_abs'.mp h with h | h
  · rw [beta1, clamp_of_le_neg_one h]; norm_num [betaPoly1]
  · rw [beta1, clamp_of_one_le h]; norm_num [betaPoly1]

theorem beta_zero : beta 0 = 1 := by rw [beta_of_mem ⟨by norm_num, by norm_num⟩]; norm_num [betaPoly]

theorem beta_neg (y : ℝ) : beta (-y) = beta y := by unfold beta; rw [clamp_neg]; unfold betaPoly; ring

theorem bigB_of_one_le {x : ℝ} (h : 1 ≤ x) : bigB x = 0 := by
  rw [bigB, clamp_of_one_le h]; norm_num [bigBPoly]

theorem bigB_of_mem {x : ℝ} (h : x ∈ Icc (-1 : ℝ) 1) : bigB x = bigBPoly x := by rw [bigB, clamp_of_mem h]

/-- `∫_{−1}^{1} p = P(1) − P(−1)` for a primitive `P` of `p`. -/
theorem integral_of_prim {P p : ℝ → ℝ} (hP : ∀ y, HasDerivAt P (p y) y) (hp : Continuous p) :
    ∫ s in (-1 : ℝ)..1, p s = P 1 - P (-1) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hP y) (hp.intervalIntegrable _ _)

/-- **`∫β = 0`.** -/
theorem integral_beta : ∫ s in (-1 : ℝ)..1, beta s = 0 := by
  rw [integral_of_prim hasDerivAt_bigB continuous_beta]
  rw [bigB_of_one_le le_rfl, bigB_of_mem ⟨le_rfl, by norm_num⟩]; norm_num [bigBPoly]

/-! ### Rescaling and the transform `Ψ = psi (2π) β` -/

/-- **Rescaling**: `psi c (a⁻¹β(·/a)) = psi (ca) β` for `0 < a ≤ 1`. -/
theorem psi_comp_div {c a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (ξ : ℝ) :
    psi c (fun s => a⁻¹ * beta (s / a)) ξ = psi (c * a) beta ξ := by
  unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
  set f : ℝ → ℝ := fun t => a⁻¹ * beta t * cos (c * a * ξ * t) with hf
  have e : (fun s => a⁻¹ * beta (s / a) * cos (c * ξ * s)) = fun s => f (s / a) := by
    funext s; simp only [hf]; rw [show c * a * ξ * (s / a) = c * ξ * s by field_simp]
  have hcont : Continuous fun t => beta t * cos (c * a * ξ * t) := by
    have := continuous_beta; fun_prop
  have hfa : (fun t => a * f t) = fun t => beta t * cos (c * a * ξ * t) := by
    funext t; simp only [hf]; field_simp
  rw [e, intervalIntegral.integral_comp_div f ha.ne', smul_eq_mul, ← intervalIntegral.integral_const_mul, hfa]
  have ha' : 1 ≤ 1 / a := by rw [le_div_iff₀ ha]; linarith
  have hz1 : ∫ t in (-1 / a)..(-1), beta t * cos (c * a * ξ * t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_, intervalIntegral.integral_zero]
    rw [uIcc_of_le (by rw [neg_div]; linarith)] at ht
    simp only
    rw [beta_of_one_le_abs (by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]), zero_mul]
  have hz2 : ∫ t in (1 : ℝ)..(1 / a), beta t * cos (c * a * ξ * t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_, intervalIntegral.integral_zero]
    rw [uIcc_of_le ha'] at ht
    simp only
    rw [beta_of_one_le_abs (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1), zero_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -1) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := -1) (b := 1) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _), hz1, hz2, zero_add, add_zero]

/-- **The transform** `Ψ = psi (2π) β`, the profile at scale `c = 2π`. -/
noncomputable def Psi : ℝ → ℝ := psi (2 * π) beta

/-- `psi c (a⁻¹β(·/a)) = Ψ` with `a = 2π/c`, for `c ≥ 2π`. -/
theorem psi_comp_div_eq_Psi {c : ℝ} (hc : 2 * π ≤ c) :
    psi c (fun s => (2 * π / c)⁻¹ * beta (s / (2 * π / c))) = Psi := by
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  funext ξ
  rw [psi_comp_div (by positivity) (by rw [div_le_one hc0]; exact hc), Psi, mul_div_cancel₀ _ hc0.ne']

theorem hasDerivAt_beta_on : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt beta (beta1 s) s := fun s _ => hasDerivAt_beta s
theorem hasDerivAt_beta1_on : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt beta1 (beta2 s) s := fun s _ => hasDerivAt_beta1 s
theorem continuousOn_beta2 : ContinuousOn beta2 (uIcc (-1) 1) := continuous_beta2.continuousOn

theorem beta1_one : beta1 1 = 0 := beta1_of_one_le_abs (by norm_num)
theorem beta1_neg_one : beta1 (-1) = 0 := beta1_of_one_le_abs (by norm_num)
theorem beta_one : beta 1 = 0 := beta_of_one_le_abs (by norm_num)
theorem beta_neg_one : beta (-1) = 0 := beta_of_one_le_abs (by norm_num)

/-- The fourth-order constant `K_Ψ = |β‴(1) − β‴(−1)| + ∫|β⁗|`. -/
noncomputable def KPsi : ℝ := |betaPoly3 1 - betaPoly3 (-1)| + ∫ s in (-1 : ℝ)..1, |betaPoly4 s|

/-- **Four integrations by parts**: `Ψ(ξ) = −((β‴(1) − β‴(−1)) cos 2πξ − ∫β⁗ cos(2πξs))/(2πξ)⁴`. -/
theorem Psi_eq {ξ : ℝ} (hξ : ξ ≠ 0) :
    Psi ξ = -((betaPoly3 1 - betaPoly3 (-1)) * cos (2 * π * ξ)
      - ∫ s in (-1 : ℝ)..1, betaPoly4 s * cos (2 * π * ξ * s)) / (2 * π * ξ) ^ 4 := by
  have hcξ : 2 * π * ξ ≠ 0 := mul_ne_zero (by positivity) hξ
  have h1 := Cvs.Prolate.CosineTransformSecondOrder.psi_eq hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2 hcξ
  have h2 := Cvs.Prolate.CosineTransformSecondOrder.psi_eq (fun s _ => hasDerivAt_betaPoly2 s) (fun s _ => hasDerivAt_betaPoly3 s)
    (by unfold betaPoly4; fun_prop : Continuous betaPoly4).continuousOn hcξ
  have e : ∫ s in (-1 : ℝ)..1, beta2 s * cos (2 * π * ξ * s) = psi (2 * π) betaPoly2 ξ := by
    unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [beta2, clamp_of_mem hs]
  rw [Psi, h1, e, h2, beta_one, beta_neg_one, beta1_one, beta1_neg_one]
  have h21 : betaPoly2 1 = 0 := by norm_num [betaPoly2]
  have h2m : betaPoly2 (-1) = 0 := by norm_num [betaPoly2]
  rw [h21, h2m]
  field_simp
  ring

theorem KPsi_nonneg : 0 ≤ KPsi :=
  add_nonneg (abs_nonneg _) (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _)

/-- **`Ψ = O(ξ⁻⁴)`**: `|Ψ(ξ)| ≤ K_Ψ/(2πξ)⁴`. -/
theorem abs_Psi_le {ξ : ℝ} (hξ : ξ ≠ 0) : |Psi ξ| ≤ KPsi / (2 * π * ξ) ^ 4 := by
  rw [Psi_eq hξ, abs_div, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * π * ξ) ^ 4)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  · refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans
      (intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun s _ => ?_)
    · exact (by unfold betaPoly4; fun_prop :
        Continuous fun s => |betaPoly4 s * cos (2 * π * ξ * s)|).intervalIntegrable _ _
    · exact (by unfold betaPoly4; fun_prop : Continuous fun s => |betaPoly4 s|).intervalIntegrable _ _
    · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

/-! ### The Poisson tail of a profile -/

/-- The Poisson tail of `f` cut at `N` modes: `f(0)/(2θ) + Σ_{n<N} f((n+1)/θ)/θ`. -/
noncomputable def profTailN (f : ℝ → ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  f 0 / (2 * θ) + ∑ n ∈ Finset.range N, f ((n + 1) / θ) / θ

/-- **The Poisson tail** `T_f(θ) = (1/2θ)[f(0) + 2Σ_{1≤n≤θ} f(n/θ)]`. -/
noncomputable def profTail (f : ℝ → ℝ) (θ : ℝ) : ℝ := profTailN f ⌊θ⌋₊ θ

variable {f f₁ f₂ : ℝ → ℝ}

/-- Modes past `θ` add nothing when `f` vanishes off `(−1, 1)`. -/
theorem profTailN_eq (hf : ∀ y, 1 ≤ |y| → f y = 0) {θ : ℝ} (hθ : 0 < θ) {N : ℕ} (hN : ⌊θ⌋₊ ≤ N) :
    profTailN f N θ = profTail f θ := by
  unfold profTail profTailN
  rw [← Finset.sum_range_add_sum_Ico _ hN, Finset.sum_eq_zero (s := Finset.Ico _ _) fun n hn => ?_, add_zero]
  have hn := (Finset.mem_Ico.mp hn).1
  have h1 : θ < (n : ℝ) + 1 :=
    (Nat.lt_floor_add_one θ).trans_le (by exact_mod_cast Nat.add_le_add_right hn 1)
  rw [hf _ (by rw [abs_of_pos (by positivity), le_div_iff₀ hθ]; linarith), zero_div]

theorem profTail_eventuallyEq (hf : ∀ y, 1 ≤ |y| → f y = 0) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :
    profTail f =ᶠ[𝓝 θ₀] profTailN f (⌊θ₀⌋₊ + 1) := by
  filter_upwards [Ioo_mem_nhds hθ₀ (Nat.lt_floor_add_one θ₀)] with θ hθ
  refine (profTailN_eq hf hθ.1 ?_).symm
  have := (Nat.floor_lt hθ.1.le).mpr (by push_cast; exact hθ.2 : θ < ((⌊θ₀⌋₊ + 1 : ℕ) : ℝ))
  omega

theorem continuousAt_profTailN (hfc : Continuous f) (N : ℕ) {θ : ℝ} (hθ : θ ≠ 0) :
    ContinuousAt (profTailN f N) θ := by
  have h2 : 2 * θ ≠ 0 := mul_ne_zero two_ne_zero hθ
  unfold profTailN
  fun_prop (disch := assumption)

theorem continuousOn_profTail (hf : ∀ y, 1 ≤ |y| → f y = 0) (hfc : Continuous f) :
    ContinuousOn (profTail f) (Ioi 0) := fun _ hθ =>
  ((continuousAt_profTailN hfc _ (ne_of_gt hθ)).congr (profTail_eventuallyEq hf hθ).symm).continuousWithinAt

/-- A symmetric sum of an even function over `[−k, k]`. -/
theorem sum_Icc_neg_eq {G : ℤ → ℝ} (hG : ∀ n, G (-n) = G n) (k : ℕ) :
    ∑ n ∈ Finset.Icc (-(k : ℤ)) k, G n = G 0 + 2 * ∑ n ∈ Finset.range k, G ((n : ℤ) + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)
        = insert (-((k : ℤ) + 1)) (insert ((k : ℤ) + 1) (Finset.Icc (-(k : ℤ)) k)) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih, Finset.sum_range_succ, hG]
    ring

/-- `|psi (2π) f (ξ)| ≤ C₁/(2πξ)²` when `f(1) + f(−1) = 0`. -/
theorem abs_psi_le_of_edge (hf : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f₁ (f₂ s) s) (hf₂c : ContinuousOn f₂ (uIcc (-1) 1))
    (hA : f 1 + f (-1) = 0) {ξ : ℝ} (hξ : 0 < ξ) :
    |psi (2 * π) f ξ| ≤ (|f₁ 1 - f₁ (-1)| + ∫ s in (-1 : ℝ)..1, |f₂ s|) / (2 * π * ξ) ^ 2 := by
  have h := Cvs.Prolate.CosineTransformSecondOrder.psi_sub_le hf hf₁ hf₂c (c := 2 * π) (ξ := ξ) (by positivity)
  rwa [hA, zero_mul, zero_div, sub_zero] at h

theorem abs_psi_mode_le (hf : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f₁ (f₂ s) s) (hf₂c : ContinuousOn f₂ (uIcc (-1) 1))
    (hA : f 1 + f (-1) = 0) (m : ℕ) {θ : ℝ} (hθ : 1 ≤ θ) :
    |psi (2 * π) f (((m : ℝ) + 1) * θ)|
      ≤ (|f₁ 1 - f₁ (-1)| + ∫ s in (-1 : ℝ)..1, |f₂ s|) / (2 * π) ^ 2 * (1 / ((m : ℝ) + 1) ^ 2) := by
  have hC : 0 ≤ |f₁ 1 - f₁ (-1)| + ∫ s in (-1 : ℝ)..1, |f₂ s| := C1_nonneg f₁ f₂
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := m.cast_nonneg (α := ℝ); linarith
  refine (abs_psi_le_of_edge hf hf₁ hf₂c hA (by positivity)).trans ?_
  rw [div_mul_div_comm, mul_one]
  refine div_le_div_of_nonneg_left hC (by positivity) ?_
  have : ((m : ℝ) + 1) ^ 2 ≤ ((m + 1) * θ) ^ 2 := by
    gcongr; nlinarith
  calc (2 * π) ^ 2 * ((m : ℝ) + 1) ^ 2 ≤ (2 * π) ^ 2 * (((m : ℝ) + 1) * θ) ^ 2 := by gcongr
    _ = (2 * π * (((m : ℝ) + 1) * θ)) ^ 2 := by ring

theorem summable_inv_succ_sq : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  exact_mod_cast this

/-- **The full tail is the sum of the modes** when `f(1) + f(−1) = 0`. -/
theorem hasSum_fullTail (hf : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f₁ (f₂ s) s) (hf₂c : ContinuousOn f₂ (uIcc (-1) 1))
    (hA : f 1 + f (-1) = 0) {θ : ℝ} (hθ : 1 < θ) :
    HasSum (fun m : ℕ => psi (2 * π) f (((m : ℝ) + 1) * θ)) (fullTail (psi (2 * π) f) θ) := by
  have hs : Summable fun m : ℕ => psi (2 * π) f (((m : ℝ) + 1) * θ) :=
    Summable.of_norm_bounded (summable_inv_succ_sq.mul_left _) fun m => by
      rw [Real.norm_eq_abs]; exact abs_psi_mode_le hf hf₁ hf₂c hA m hθ.le
  have hp := tendsto_partial hf hf₁ hf₂c (by positivity : (0 : ℝ) < 2 * π) hθ
  have ht := hs.hasSum.tendsto_sum_nat
  have e : ∑' m : ℕ, psi (2 * π) f (((m : ℝ) + 1) * θ) = fullTail (psi (2 * π) f) θ := by
    refine tendsto_nhds_unique (ht.congr fun M => ?_) hp
    rw [sum_Icc_eq_sum_range (fun m : ℕ => psi (2 * π) f (m * θ))]
    push_cast; rfl
  rw [← e]; exact hs.hasSum

/-- The full tail is continuous on `(1, ∞)` when `f(1) + f(−1) = 0`. -/
theorem continuousOn_fullTail (hf : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f₁ (f₂ s) s) (hf₂c : ContinuousOn f₂ (uIcc (-1) 1))
    (hA : f 1 + f (-1) = 0) : ContinuousOn (fullTail (psi (2 * π) f)) (Ioi 1) := by
  have hψ : Continuous (psi (2 * π) f) :=
    (contDiff_psi (fun s hs => (hf s hs).continuousAt.continuousWithinAt) _).continuous
  have hG : Continuous fun θ : ℝ => ∑' m : ℕ, psi (2 * π) f (((m : ℝ) + 1) * max θ 1) :=
    continuous_tsum (fun m => by fun_prop) (summable_inv_succ_sq.mul_left _) fun m θ => by
      rw [Real.norm_eq_abs]; exact abs_psi_mode_le hf hf₁ hf₂c hA m (le_max_right θ 1)
  refine hG.continuousOn.congr fun θ hθ => ?_
  show _ = ∑' m : ℕ, psi (2 * π) f (((m : ℝ) + 1) * max θ 1)
  rw [max_eq_left (le_of_lt hθ)]
  exact (hasSum_fullTail hf hf₁ hf₂c hA hθ).tsum_eq.symm

/-- Off the integers, Poisson summation (Cvs.L2a.FullTailConvergence) gives `F_∞ = T_f`. -/
theorem fullTail_eq_profTail_of_floor_lt (hf : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f₁ (f₂ s) s) (hf₂c : ContinuousOn f₂ (uIcc (-1) 1))
    (heven : ∀ y, f (-y) = f y) (hint : ∫ s in (-1 : ℝ)..1, f s = 0) {θ : ℝ} (hθ : 1 < θ)
    (hfl : (⌊θ⌋₊ : ℝ) < θ) : fullTail (psi (2 * π) f) θ = profTail f θ := by
  have hθ0 : 0 < θ := by linarith
  have e : 2 * π * θ / (2 * π) = θ := by field_simp
  rw [fullTail_eq_poissonPiece hf hf₁ hf₂c (by positivity) hθ (k := ⌊θ⌋₊) (by rw [e]; exact hfl)
    (by rw [e]; exact Nat.lt_floor_add_one θ)]
  unfold poissonPiece profTail profTailN
  set G : ℤ → ℝ := fun n => f (2 * π * n / (2 * π * θ)) with hGd
  have hG : ∀ n, G (-n) = G n := fun n => by
    simp only [hGd, Int.cast_neg, mul_neg, neg_div, heven]
  rw [sum_Icc_neg_eq hG, hint]
  have h0 : G 0 = f 0 := by simp [hGd]
  have hs : ∀ n : ℕ, G ((n : ℤ) + 1) = f (((n : ℝ) + 1) / θ) := fun n => by
    simp only [hGd]; push_cast; congr 1; field_simp
  rw [h0, Finset.sum_congr rfl fun n _ => hs n, ← Finset.sum_div]
  field_simp
  ring

/-- **Poisson summation for a profile**: `F_∞(psi (2π) f) = T_f` on `θ > 1`, for `f` even, `C²` on
`[−1, 1]`, vanishing off `(−1, 1)`, with `∫f = 0`. -/
theorem fullTail_eq_profTail (hf : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt f₁ (f₂ s) s) (hf₂c : ContinuousOn f₂ (uIcc (-1) 1))
    (hfc : Continuous f) (hzero : ∀ y, 1 ≤ |y| → f y = 0) (heven : ∀ y, f (-y) = f y)
    (hint : ∫ s in (-1 : ℝ)..1, f s = 0) {θ : ℝ} (hθ : 1 < θ) :
    fullTail (psi (2 * π) f) θ = profTail f θ := by
  have hA : f 1 + f (-1) = 0 := by rw [hzero 1 (by norm_num), hzero (-1) (by norm_num), add_zero]
  have hev : fullTail (psi (2 * π) f) =ᶠ[𝓝[>] θ] profTail f := by
    filter_upwards [Ioo_mem_nhdsGT (Nat.lt_floor_add_one θ)] with t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hk : ⌊t⌋₊ = ⌊θ⌋₊ := by
      rw [Nat.floor_eq_iff ht0]
      exact ⟨(Nat.floor_le (by linarith)).trans ht.1.le, ht.2⟩
    exact fullTail_eq_profTail_of_floor_lt hf hf₁ hf₂c heven hint (by linarith [ht.1])
      (by rw [hk]; exact (Nat.floor_le (by linarith)).trans_lt ht.1)
  have h1 := ((continuousOn_fullTail hf hf₁ hf₂c hA).continuousAt (Ioi_mem_nhds hθ)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi θ))
  have h2 := ((continuousOn_profTail hzero hfc).continuousAt
    (Ioi_mem_nhds (by linarith : (0 : ℝ) < θ))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi θ))
  exact tendsto_nhds_unique (h1.congr' hev) h2

/-! ### `T_β` and its decay -/

/-- **`T_β`**, the Poisson tail of `β`. -/
noncomputable def Tb : ℝ → ℝ := profTail beta

theorem beta_edge : beta 1 + beta (-1) = 0 := by rw [beta_one, beta_neg_one, add_zero]

/-- **`F_∞(Ψ) = T_β`** on `θ > 1`. -/
theorem fullTail_Psi {θ : ℝ} (hθ : 1 < θ) : fullTail Psi θ = Tb θ :=
  fullTail_eq_profTail hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2 continuous_beta
    (fun _ hy => beta_of_one_le_abs hy) beta_neg integral_beta hθ

theorem hasSum_inv_succ_pow_four : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 4) (π ^ 4 / 90) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero] at h
  exact_mod_cast h

theorem abs_Psi_mode_le (m : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    |Psi (((m : ℝ) + 1) * θ)| ≤ KPsi / (2 * π * θ) ^ 4 * (1 / ((m : ℝ) + 1) ^ 4) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine (abs_Psi_le (by positivity)).trans (le_of_eq ?_)
  field_simp

/-- **`T⁺ = O(θ⁻⁴)`**: `|F_∞(Ψ)(θ)| ≤ K_Ψ/(1440 θ⁴)` on `θ > 1`. -/
theorem abs_fullTail_Psi_le {θ : ℝ} (hθ : 1 < θ) : |fullTail Psi θ| ≤ KPsi / (1440 * θ ^ 4) := by
  have hθ0 : 0 < θ := by linarith
  have hs : HasSum (fun m : ℕ => Psi (((m : ℝ) + 1) * θ)) (fullTail Psi θ) :=
    hasSum_fullTail hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2 beta_edge hθ
  have hb := hasSum_inv_succ_pow_four.mul_left (KPsi / (2 * π * θ) ^ 4)
  have e : KPsi / (2 * π * θ) ^ 4 * (π ^ 4 / 90) = KPsi / (1440 * θ ^ 4) := by field_simp; ring
  rw [← e, abs_le]
  constructor
  · have := hasSum_le (fun m => neg_le_of_abs_le (abs_Psi_mode_le m hθ0)) hb.neg hs
    linarith
  · exact hasSum_le (fun m => le_of_abs_le (abs_Psi_mode_le m hθ0)) hs hb

/-- `|T_β(θ)| ≤ K_Ψ/(1440 θ⁴)` on `θ > 1`. -/
theorem abs_Tb_le {θ : ℝ} (hθ : 1 < θ) : |Tb θ| ≤ KPsi / (1440 * θ ^ 4) :=
  fullTail_Psi hθ ▸ abs_fullTail_Psi_le hθ

/-! ### `L²` facts for `T⁺` -/

/-- `∫_{(1,∞)} θ⁻ⁿ = 1/(n − 1)` for `n ≥ 2`, with integrability. -/
theorem integrableOn_inv_pow {n : ℕ} (hn : 2 ≤ n) : IntegrableOn (fun θ : ℝ => 1 / θ ^ n) (Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -(n : ℝ)) (by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith) one_pos).congr_fun (fun θ hθ => ?_) measurableSet_Ioi
  have hθ : (0 : ℝ) < θ := lt_trans one_pos hθ
  show θ ^ (-(n : ℝ)) = 1 / θ ^ n
  rw [rpow_neg hθ.le, rpow_natCast, one_div]

theorem integral_inv_pow {n : ℕ} (hn : 2 ≤ n) : ∫ θ in Ioi (1 : ℝ), 1 / θ ^ n = 1 / ((n : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun θ : ℝ => θ ^ (-(n : ℝ))) fun θ hθ => by
    have hθ : (0 : ℝ) < θ := lt_trans one_pos hθ
    simp only
    rw [rpow_neg hθ.le, rpow_natCast, one_div], integral_Ioi_rpow_of_lt (by linarith) one_pos, one_rpow]
  rw [show -(n : ℝ) + 1 = -((n : ℝ) - 1) by ring, div_neg, neg_div, neg_neg]

theorem measurable_fullTail_Psi : Measurable (fullTail Psi) :=
  measurable_fullTail hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2 (by positivity)

/-- A profile bounded by `K/θⁿ` on `(1, ∞)`, `n ≥ 2`, is integrable there, with integral at most `K/(n − 1)`. -/
theorem integrableOn_of_le_inv_pow {F : ℝ → ℝ} (hF : AEStronglyMeasurable F (volume.restrict (Ioi 1)))
    {K : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hb : ∀ θ, 1 < θ → |F θ| ≤ K / θ ^ n) :
    IntegrableOn F (Ioi 1) ∧ ∫ θ in Ioi 1, F θ ≤ K / ((n : ℝ) - 1) := by
  have hi : IntegrableOn (fun θ : ℝ => K * (1 / θ ^ n)) (Ioi 1) := (integrableOn_inv_pow hn).const_mul K
  have hK : ∀ θ ∈ Ioi (1 : ℝ), K / θ ^ n = K * (1 / θ ^ n) := fun θ _ => by ring
  have hFi : IntegrableOn F (Ioi 1) := by
    refine hi.mono' hF ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun θ hθ => ?_))
    rw [Real.norm_eq_abs, ← hK θ hθ]; exact hb θ hθ
  refine ⟨hFi, (setIntegral_mono_on hFi hi measurableSet_Ioi fun θ hθ => ?_).trans ?_⟩
  · rw [← hK θ hθ]; exact (le_abs_self _).trans (hb θ hθ)
  · rw [integral_const_mul, integral_inv_pow hn]; apply le_of_eq; ring

/-- **`‖T⁺‖² ≤ K_Ψ²/(1440²·7)`**, with `T⁺² ∈ L¹(1, ∞)`. -/
theorem fullTail_Psi_sq :
    IntegrableOn (fun θ => fullTail Psi θ ^ 2) (Ioi 1)
      ∧ ∫ θ in Ioi 1, fullTail Psi θ ^ 2 ≤ (KPsi / 1440) ^ 2 / 7 := by
  have h := integrableOn_of_le_inv_pow (F := fun θ => fullTail Psi θ ^ 2) (K := (KPsi / 1440) ^ 2) (n := 8)
    (measurable_fullTail_Psi.pow_const 2).aestronglyMeasurable (by norm_num) fun θ hθ => by
      have hb := abs_fullTail_Psi_le hθ
      have hθ0 : 0 < θ := by linarith
      rw [abs_pow, show (KPsi / 1440) ^ 2 / θ ^ 8 = (KPsi / (1440 * θ ^ 4)) ^ 2 by field_simp]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  norm_num at h ⊢
  exact h

/-- **`‖log θ · T⁺‖² ≤ K_Ψ²/(1440²·5)`**, with `(log θ · T⁺)² ∈ L¹(1, ∞)`. -/
theorem log_fullTail_Psi_sq :
    IntegrableOn (fun θ => (Real.log θ * fullTail Psi θ) ^ 2) (Ioi 1)
      ∧ ∫ θ in Ioi 1, (Real.log θ * fullTail Psi θ) ^ 2 ≤ (KPsi / 1440) ^ 2 / 5 := by
  have h := integrableOn_of_le_inv_pow (F := fun θ => (Real.log θ * fullTail Psi θ) ^ 2)
    (K := (KPsi / 1440) ^ 2) (n := 6)
    ((Real.measurable_log.mul measurable_fullTail_Psi).pow_const 2).aestronglyMeasurable
    (by norm_num) fun θ hθ => by
      have hb := abs_fullTail_Psi_le hθ
      have hθ0 : 0 < θ := by linarith
      have hl0 : 0 ≤ Real.log θ := Real.log_nonneg hθ.le
      have hl : Real.log θ ≤ θ := (Real.log_le_sub_one_of_pos hθ0).trans (by linarith)
      rw [abs_pow, abs_mul, abs_of_nonneg hl0,
        show (KPsi / 1440) ^ 2 / θ ^ 6 = (θ * (KPsi / (1440 * θ ^ 4))) ^ 2 by field_simp]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul hl hb (abs_nonneg _) hθ0.le) 2
  norm_num at h ⊢
  exact h

/-- The log-scale `T⁺` is in `L²` and `L¹` (Cvs.L2a.FullTailConvergence). -/
theorem memLp_logScale_fullTail_Psi :
    MemLp (Cvs.L2a.TailLogScaleTest.logScale (fullTail Psi)) 2 volume
      ∧ Integrable (Cvs.L2a.TailLogScaleTest.logScale (fullTail Psi)) volume :=
  memLp_logScale_fullTail hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2 (by positivity)

/-! ### Power sums and the finite-`N` integrals -/

theorem sum_succ_pow_two (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ 2 = (N : ℝ) ^ 3 / 3 + (N : ℝ) ^ 2 / 2 + N / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_succ_pow_four (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ 4
      = (N : ℝ) ^ 5 / 5 + (N : ℝ) ^ 4 / 2 + (N : ℝ) ^ 3 / 3 - N / 30 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_succ_pow_six (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ 6
      = (N : ℝ) ^ 7 / 7 + (N : ℝ) ^ 6 / 2 + (N : ℝ) ^ 5 / 2 - (N : ℝ) ^ 3 / 6 + N / 42 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_succ_pow_eight (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ 8
      = (N : ℝ) ^ 9 / 9 + (N : ℝ) ^ 8 / 2 + 2 * (N : ℝ) ^ 7 / 3 - 7 * (N : ℝ) ^ 5 / 15
        + 2 * (N : ℝ) ^ 3 / 9 - N / 30 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- On `(0, N]`, `T_β` is the `N`-mode tail. -/
theorem Tb_eq_profTailN {N : ℕ} {θ : ℝ} (hθ : 0 < θ) (hθN : θ ≤ N) : Tb θ = profTailN beta N θ :=
  (profTailN_eq (fun _ hy => beta_of_one_le_abs hy) hθ (Nat.floor_le_of_le hθN)).symm

theorem hasDerivAt_const_div (m : ℝ) {θ : ℝ} (hθ : θ ≠ 0) :
    HasDerivAt (fun θ : ℝ => m / θ) (-(m / θ ^ 2)) θ := by
  have h := (hasDerivAt_const θ m).div (hasDerivAt_id' θ) hθ
  refine h.congr_deriv ?_
  ring

/-- On `[1, N]`, the integral of `F_∞(Ψ)` against `w` is that of the `N`-mode tail. -/
theorem integral_fullTail_Psi_eq {N : ℕ} (hN : 1 ≤ N) (w : ℝ → ℝ) :
    ∫ θ in (1 : ℝ)..N, fullTail Psi θ * w θ = ∫ θ in (1 : ℝ)..N, profTailN beta N θ * w θ := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun θ hθ => ?_)
  rw [uIoc_of_le hN'] at hθ
  rw [fullTail_Psi hθ.1, Tb_eq_profTailN (by linarith [hθ.1]) hθ.2]

theorem continuousOn_profTailN_beta (N : ℕ) : ContinuousOn (profTailN beta N) (Ioi 0) := fun _ hθ =>
  (continuousAt_profTailN continuous_beta N (ne_of_gt hθ)).continuousWithinAt

theorem tendsto_const_div_pow (C : ℝ) {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun N : ℕ => C / (N : ℝ) ^ k) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hk).comp tendsto_natCast_atTop_atTop)

/-! ### `Π₋(Ψ) = 59/630` -/

/-- **The `N`-mode `Π₋` integral, exactly**: `∫_1^N T_β/θ = 59/630 − 8/(63N⁶) + 1/(30N⁸)`. -/
theorem integral_fullTail_Psi_div_interval {N : ℕ} (hN : 1 ≤ N) :
    ∫ θ in (1 : ℝ)..N, fullTail Psi θ / θ = 59 / 630 - 8 / (63 * (N : ℝ) ^ 6) + 1 / (30 * (N : ℝ) ^ 8) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  simp_rw [div_eq_mul_inv (fullTail Psi _)]
  rw [integral_fullTail_Psi_eq hN]
  set F : ℝ → ℝ := fun θ => -1 / 2 * θ⁻¹ - ∑ n ∈ Finset.range N, bigB (((n : ℝ) + 1) / θ) / ((n : ℝ) + 1)
    with hFd
  have hF : ∀ θ ∈ uIcc (1 : ℝ) N, HasDerivAt F (profTailN beta N θ * θ⁻¹) θ := by
    intro θ hθ
    rw [uIcc_of_le hN'] at hθ
    have hθ0 : θ ≠ 0 := by linarith [hθ.1]
    have h1 := (hasDerivAt_inv hθ0).const_mul (-1 / 2)
    have h2 := HasDerivAt.fun_sum (u := Finset.range N) (x := θ)
      (A := fun n θ => bigB (((n : ℝ) + 1) / θ) / ((n : ℝ) + 1))
      (A' := fun n => beta (((n : ℝ) + 1) / θ) * (-((((n : ℝ) + 1)) / θ ^ 2)) / ((n : ℝ) + 1))
      fun n _ => ((hasDerivAt_bigB _).comp θ (hasDerivAt_const_div _ hθ0)).div_const _
    refine (h1.sub h2).congr_deriv ?_
    unfold profTailN
    rw [beta_zero, add_mul, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun n _ => ?_
      have : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
  have hsub : uIcc (1 : ℝ) N ⊆ Ioi 0 := fun θ hθ => by
    rw [uIcc_of_le hN'] at hθ; exact lt_of_lt_of_le one_pos hθ.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (ContinuousOn.intervalIntegrable
    (((continuousOn_profTailN_beta N).mono hsub).mul (continuousOn_inv₀.mono fun θ hθ => ne_of_gt (hsub hθ))))]
  have h1 : ∑ n ∈ Finset.range N, bigB (((n : ℝ) + 1) / 1) / ((n : ℝ) + 1) = 0 :=
    Finset.sum_eq_zero fun n _ => by
      rw [div_one, bigB_of_one_le (by have := n.cast_nonneg (α := ℝ); linarith), zero_div]
  have hterm : ∀ n ∈ Finset.range N, bigB (((n : ℝ) + 1) / N) / ((n : ℝ) + 1)
      = 1 / N - 4 / (N : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 + 6 / (N : ℝ) ^ 5 * ((n : ℝ) + 1) ^ 4
        - 4 / (N : ℝ) ^ 7 * ((n : ℝ) + 1) ^ 6 + 1 / (N : ℝ) ^ 9 * ((n : ℝ) + 1) ^ 8 := by
    intro n hn
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hn
    rw [bigB_of_mem ⟨by rw [le_div_iff₀ hN0]; linarith [n.cast_nonneg (α := ℝ)],
      by rw [div_le_one hN0]; exact hn'⟩]
    unfold bigBPoly
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  simp only [hFd]
  rw [Finset.sum_congr rfl hterm, h1]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, sum_succ_pow_two, sum_succ_pow_four, sum_succ_pow_six, sum_succ_pow_eight]
  field_simp
  ring

/-- **`Π₋(Ψ) = ∫_{(1,∞)} T⁺/θ = 59/630`.** -/
theorem piMinus_Psi : ∫ θ in Ioi 1, fullTail Psi θ / θ = 59 / 630 := by
  have hi := (integrableOn_of_le_inv_pow (F := fun θ => fullTail Psi θ / θ) (K := KPsi / 1440) (n := 5)
    (measurable_fullTail_Psi.div measurable_id).aestronglyMeasurable (by norm_num) fun θ hθ => by
      have hθ0 : 0 < θ := by linarith
      rw [abs_div, abs_of_pos hθ0, div_le_iff₀ hθ0,
        show KPsi / 1440 / θ ^ 5 * θ = KPsi / (1440 * θ ^ 4) by field_simp]
      exact abs_fullTail_Psi_le hθ).1
  have hlim := intervalIntegral_tendsto_integral_Ioi 1 hi tendsto_natCast_atTop_atTop
  have hcf : Tendsto (fun N : ℕ => 59 / 630 - 8 / (63 * (N : ℝ) ^ 6) + 1 / (30 * (N : ℝ) ^ 8)) atTop
      (𝓝 (59 / 630)) := by
    have h := (tendsto_const_nhds (x := (59 / 630 : ℝ))).sub (tendsto_const_div_pow (8 / 63) (k := 6) (by norm_num))
      |>.add (tendsto_const_div_pow (1 / 30) (k := 8) (by norm_num))
    rw [sub_zero, add_zero] at h
    refine h.congr fun N => ?_
    rw [div_div, div_div]
  refine tendsto_nhds_unique hlim (hcf.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (integral_fullTail_Psi_div_interval hN).symm

/-! ### `Π₊(Ψ) = ½(49/24 − log 2π)` -/

/-- `q(v) = −6v² + (15/2)v⁴ − (14/3)v⁶ + (9/8)v⁸`. -/
noncomputable def qPoly (v : ℝ) : ℝ := -6 * v ^ 2 + 15 / 2 * v ^ 4 - 14 / 3 * v ^ 6 + 9 / 8 * v ^ 8

/-- `log v + q(v)`, a primitive of `β(v)/v` on `(0, 1]`. -/
noncomputable def logPrim (v : ℝ) : ℝ := Real.log v + qPoly v

theorem hasDerivAt_logPrim {v : ℝ} (hv : 0 < v) : HasDerivAt logPrim (betaPoly v / v) v := by
  have h := (Real.hasDerivAt_log hv.ne').add ((((hasDerivAt_mono (-6) 1 v).add (hasDerivAt_mono (15 / 2) 3 v)).sub
    (hasDerivAt_mono (14 / 3) 5 v)).add (hasDerivAt_mono (9 / 8) 7 v))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  · unfold betaPoly; field_simp; push_cast; ring
  · simp only [logPrim, qPoly, Pi.add_apply, Pi.sub_apply]; try ring

/-- **Capping keeps a derivative** whose value vanishes at `1`: `(p ∘ min · 1)' = p' ∘ min · 1` on `(0, ∞)`. -/
theorem hasDerivAt_comp_min_one {p p' : ℝ → ℝ} (hp : ∀ y, 0 < y → HasDerivAt p (p' y) y) (h1 : p' 1 = 0)
    {y : ℝ} (hy : 0 < y) : HasDerivAt (fun y => p (min y 1)) (p' (min y 1)) y := by
  rcases lt_trichotomy y 1 with hy1 | rfl | hy1
  · rw [min_eq_left hy1.le]
    refine (hp y hy).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hy1] with z hz
    rw [min_eq_left (le_of_lt hz)]
  · rw [min_self, h1]
    refine hasDerivAt_of_Iic_Ici ?_ ?_
    · have h := (hp 1 one_pos).hasDerivWithinAt (s := Iic 1)
      rw [h1] at h
      refine h.congr_of_eventuallyEq ?_ (by rw [min_self])
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [min_eq_left hz]
    · refine (hasDerivWithinAt_const (1 : ℝ) _ (p 1)).congr_of_eventuallyEq ?_ (by rw [min_self])
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [min_eq_right hz]
  · rw [min_eq_right hy1.le, h1]
    refine (hasDerivAt_const y (p 1)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy1] with z hz
    rw [min_eq_right (le_of_lt hz)]

theorem betaPoly_min_div {u : ℝ} (hu : 0 < u) : betaPoly (min u 1) / min u 1 = beta u / u := by
  rcases le_or_gt u 1 with h | h
  · rw [min_eq_left h, beta_of_mem ⟨by linarith, h⟩]
  · rw [min_eq_right h.le, beta_of_one_le_abs (by rw [abs_of_pos hu]; exact h.le)]; norm_num [betaPoly]

/-- **The `N`-mode `Π₊` integral, exactly**: `∫_1^N T_β = 49/48 − ½ log 2 − log s_N + 1/(12N) − 1/(360N³)
− 5/(36N⁵) + 3/(80N⁷)`, with `s_N` Stirling's sequence. -/
theorem integral_fullTail_Psi_interval {N : ℕ} (hN : 1 ≤ N) :
    ∫ θ in (1 : ℝ)..N, fullTail Psi θ
      = 49 / 48 - Real.log 2 / 2 - Real.log (Stirling.stirlingSeq N)
        + (1 / (12 * (N : ℝ)) - 1 / (360 * (N : ℝ) ^ 3) - 5 / (36 * (N : ℝ) ^ 5) + 3 / (80 * (N : ℝ) ^ 7)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have e := integral_fullTail_Psi_eq hN (fun _ => 1)
  simp only [mul_one] at e
  rw [e]
  set F : ℝ → ℝ := fun θ => 1 / 2 * Real.log θ
    - ∑ n ∈ Finset.range N, logPrim (min (((n : ℝ) + 1) / θ) 1) with hFd
  have hsub : uIcc (1 : ℝ) N ⊆ Ioi 0 := fun θ hθ => by
    rw [uIcc_of_le hN'] at hθ; exact lt_of_lt_of_le one_pos hθ.1
  have hF : ∀ θ ∈ uIcc (1 : ℝ) N, HasDerivAt F (profTailN beta N θ) θ := by
    intro θ hθ
    have hθ0 : 0 < θ := hsub hθ
    have h1 := (Real.hasDerivAt_log hθ0.ne').const_mul (1 / 2)
    have h2 := HasDerivAt.fun_sum (u := Finset.range N) (x := θ)
      (A := fun n θ => logPrim (min (((n : ℝ) + 1) / θ) 1))
      (A' := fun n => betaPoly (min (((n : ℝ) + 1) / θ) 1) / min (((n : ℝ) + 1) / θ) 1
        * (-((((n : ℝ) + 1)) / θ ^ 2)))
      fun n _ => (hasDerivAt_comp_min_one (fun v hv => hasDerivAt_logPrim hv) (by norm_num [betaPoly])
        (by positivity)).comp θ (hasDerivAt_const_div _ hθ0.ne')
    refine (h1.sub h2).congr_deriv ?_
    unfold profTailN
    rw [beta_zero, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun n _ => ?_
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [betaPoly_min_div (by positivity)]
      field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (ContinuousOn.intervalIntegrable ((continuousOn_profTailN_beta N).mono hsub))]
  have hone : ∀ n ∈ Finset.range N, logPrim (min (((n : ℝ) + 1) / 1) 1) = -49 / 24 := fun n _ => by
    rw [div_one, min_eq_right (by have := n.cast_nonneg (α := ℝ); linarith)]
    norm_num [logPrim, qPoly]
  have hterm : ∀ n ∈ Finset.range N, logPrim (min (((n : ℝ) + 1) / N) 1)
      = (Real.log ((n : ℝ) + 1) - Real.log N) + (-6 / (N : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2
        + 15 / 2 / (N : ℝ) ^ 4 * ((n : ℝ) + 1) ^ 4 - 14 / 3 / (N : ℝ) ^ 6 * ((n : ℝ) + 1) ^ 6
        + 9 / 8 / (N : ℝ) ^ 8 * ((n : ℝ) + 1) ^ 8) := by
    intro n hn
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [min_eq_left (by rw [div_le_one hN0]; exact hn'), logPrim, Real.log_div hn0.ne' hN0.ne']
    congr 1
    unfold qPoly
    field_simp
  have hfact : Real.log (Nat.factorial N : ℝ) = ∑ n ∈ Finset.range N, Real.log ((n : ℝ) + 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod,
      Real.log_prod (fun n _ => by positivity)]
    push_cast; rfl
  have hstir := Stirling.log_stirlingSeq_formula N
  rw [Real.log_mul (by norm_num) hN0.ne', Real.log_div hN0.ne' (exp_pos 1).ne', Real.log_exp, hfact] at hstir
  simp only [hFd]
  rw [Finset.sum_congr rfl hone, Finset.sum_congr rfl hterm, hstir, Real.log_one]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, sum_succ_pow_two, sum_succ_pow_four, sum_succ_pow_six, sum_succ_pow_eight]
  field_simp
  ring

/-- **`∫_{(1,∞)} T⁺ = ½(49/24 − log 2π)`.** -/
theorem integral_fullTail_Psi : ∫ θ in Ioi 1, fullTail Psi θ = 49 / 48 - Real.log (2 * π) / 2 := by
  have hi := (integrableOn_of_le_inv_pow (F := fullTail Psi) (K := KPsi / 1440) (n := 4)
    measurable_fullTail_Psi.aestronglyMeasurable (by norm_num) fun θ hθ => by
      rw [div_div]; exact abs_fullTail_Psi_le hθ).1
  have hlim := intervalIntegral_tendsto_integral_Ioi 1 hi tendsto_natCast_atTop_atTop
  have hs := (Stirling.tendsto_stirlingSeq_sqrt_pi).log (by positivity)
  have hR : Tendsto (fun N : ℕ => 1 / (12 * (N : ℝ)) - 1 / (360 * (N : ℝ) ^ 3) - 5 / (36 * (N : ℝ) ^ 5)
      + 3 / (80 * (N : ℝ) ^ 7)) atTop (𝓝 0) := by
    have h := (((tendsto_const_div_pow (1 / 12) (k := 1) one_ne_zero).sub
      (tendsto_const_div_pow (1 / 360) (k := 3) (by norm_num))).sub
      (tendsto_const_div_pow (5 / 36) (k := 5) (by norm_num))).add
      (tendsto_const_div_pow (3 / 80) (k := 7) (by norm_num))
    rw [sub_zero, sub_zero, add_zero] at h
    exact h.congr fun N => by ring
  have hcf := ((tendsto_const_nhds (x := 49 / 48 - Real.log 2 / 2)).sub hs).add hR
  rw [add_zero, Real.log_sqrt pi_pos.le] at hcf
  rw [Real.log_mul (by norm_num) pi_pos.ne', show 49 / 48 - (Real.log 2 + Real.log π) / 2
    = 49 / 48 - Real.log 2 / 2 - Real.log π / 2 by ring]
  refine tendsto_nhds_unique hlim (hcf.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (integral_fullTail_Psi_interval hN).symm

/-- `|F_X(Ψ)(θ)| ≤ K_Ψ/(1440 θ⁴)` on `θ > 1`, uniformly in `X`. -/
theorem abs_posTail_Psi_le (X : ℝ) {θ : ℝ} (hθ : 1 < θ) :
    |posTail Psi X θ| ≤ KPsi / 1440 * (1 / θ ^ 4) := by
  have hθ0 : 0 < θ := by linarith
  rcases lt_or_ge X θ with hX | hX
  · rw [posTail_of_gt _ hX, abs_zero]; have := KPsi_nonneg; positivity
  rw [posTail_eq_partial _ hθ hX]
  have hterm : ∀ m ∈ Finset.Icc 1 ⌊X / θ⌋₊, |Psi (m * θ)| ≤ KPsi / (2 * π * θ) ^ 4 * (1 / (m : ℝ) ^ 4) :=
    fun m hm => by
      have hm : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      refine (abs_Psi_le (by positivity)).trans (le_of_eq ?_)
      field_simp
  have hz : ∑ m ∈ Finset.Icc 1 ⌊X / θ⌋₊, 1 / (m : ℝ) ^ 4 ≤ π ^ 4 / 90 :=
    sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_four
  calc |∑ m ∈ Finset.Icc 1 ⌊X / θ⌋₊, Psi (m * θ)|
      ≤ ∑ m ∈ Finset.Icc 1 ⌊X / θ⌋₊, KPsi / (2 * π * θ) ^ 4 * (1 / (m : ℝ) ^ 4) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ ≤ KPsi / (2 * π * θ) ^ 4 * (π ^ 4 / 90) := by
        rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hz (by have := KPsi_nonneg; positivity)
    _ = KPsi / 1440 * (1 / θ ^ 4) := by field_simp; ring

theorem tendsto_posTail_Psi {θ : ℝ} (hθ : 1 < θ) :
    Tendsto (fun X => posTail Psi X θ) atTop (𝓝 (fullTail Psi θ)) := by
  have hp := tendsto_partial hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2
    (by positivity : (0 : ℝ) < 2 * π) hθ
  have hfl : Tendsto (fun X : ℝ => ⌊X / θ⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const (by linarith))
  refine (hp.comp hfl).congr' ?_
  filter_upwards [eventually_ge_atTop θ] with X hX
  exact (posTail_eq_partial _ hθ hX).symm

/-- **`Π₊(Ψ) = ½(49/24 − log 2π)`.** -/
theorem piPlus_Psi : piPlus Psi = 49 / 48 - Real.log (2 * π) / 2 := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set K := 2 * |beta 1 + beta (-1)| + (|beta1 1 - beta1 (-1)| + ∫ s in (-1 : ℝ)..1, |beta2 s|) with hKd
  have hu : Tendsto (fun X : ℝ => K / (2 * π) ^ 2 * (3 + Real.log X) / X) atTop (𝓝 0) := by
    have h3 : Tendsto (fun X : ℝ => 3 / X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hl : Tendsto (fun X : ℝ => Real.log X / X) atTop (𝓝 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa only [pow_one, one_mul, add_zero] using this
    have := (h3.add hl).const_mul (K / (2 * π) ^ 2)
    rw [add_zero, mul_zero] at this
    refine this.congr fun X => ?_
    ring
  have h1 : Tendsto (fun X : ℝ => ∫ θ in Ioi 1, posTail Psi X θ) atTop (𝓝 (piPlus Psi)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) ?_ hu
    filter_upwards [eventually_ge_atTop 1] with X hX
    rw [Real.norm_eq_abs]
    exact abs_integral_posTail_sub_le hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2 h2π hX
  have h2 : Tendsto (fun X : ℝ => ∫ θ in Ioi 1, posTail Psi X θ) atTop
      (𝓝 (∫ θ in Ioi 1, fullTail Psi θ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun θ => KPsi / 1440 * (1 / θ ^ 4))
      (Eventually.of_forall fun X => (measurable_posTail_psi hasDerivAt_beta_on (2 * π) X).aestronglyMeasurable)
      (Eventually.of_forall fun X => (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun θ hθ => by rw [Real.norm_eq_abs]; exact abs_posTail_Psi_le X hθ))
      ((integrableOn_inv_pow (n := 4) (by norm_num)).const_mul _)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun θ hθ => tendsto_posTail_Psi hθ))
  rw [tendsto_nhds_unique h1 h2, integral_fullTail_Psi]

/-! ### `γ = (yβ)'` and the derivative of `T_β` -/

/-- The fifth derivative of `betaPoly`. -/
def betaPoly5 (y : ℝ) : ℝ := -20160 * y + 60480 * y ^ 3

theorem hasDerivAt_betaPoly4 (y : ℝ) : HasDerivAt betaPoly4 (betaPoly5 y) y := by
  have h := ((hasDerivAt_const y (720 : ℝ)).sub (hasDerivAt_mono 10080 1 y)).add (hasDerivAt_mono 15120 3 y)
  refine (h.congr_deriv (by simp only [betaPoly5]; push_cast; ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun z => ?_)
  simp only [betaPoly4, Pi.add_apply, Pi.sub_apply]; try ring

/-- `(yβ)' = β + yβ'` on `[−1, 1]`. -/
def gammaPoly (y : ℝ) : ℝ := betaPoly y + y * betaPoly1 y

/-- The first derivative of `gammaPoly`. -/
def gammaPoly1 (y : ℝ) : ℝ := 2 * betaPoly1 y + y * betaPoly2 y

/-- The second derivative of `gammaPoly`. -/
def gammaPoly2 (y : ℝ) : ℝ := 3 * betaPoly2 y + y * betaPoly3 y

/-- The third derivative of `gammaPoly`. -/
def gammaPoly3 (y : ℝ) : ℝ := 4 * betaPoly3 y + y * betaPoly4 y

/-- The fourth derivative of `gammaPoly`. -/
def gammaPoly4 (y : ℝ) : ℝ := 5 * betaPoly4 y + y * betaPoly5 y

theorem hasDerivAt_shift {p p₁ p₂ : ℝ → ℝ} {k : ℝ} (hp : ∀ y, HasDerivAt p (p₁ y) y)
    (hp₁ : ∀ y, HasDerivAt p₁ (p₂ y) y) (y : ℝ) :
    HasDerivAt (fun y => k * p y + y * p₁ y) ((k + 1) * p₁ y + y * p₂ y) y := by
  have h := ((hp y).const_mul k).add ((hasDerivAt_id' y).mul (hp₁ y))
  exact h.congr_deriv (by ring)

theorem hasDerivAt_gammaPoly (y : ℝ) : HasDerivAt gammaPoly (gammaPoly1 y) y := by
  have h := hasDerivAt_shift (k := 1) hasDerivAt_betaPoly hasDerivAt_betaPoly1 y
  simp only [one_mul] at h
  exact h.congr_deriv (by unfold gammaPoly1; ring)

theorem hasDerivAt_gammaPoly1 (y : ℝ) : HasDerivAt gammaPoly1 (gammaPoly2 y) y :=
  (hasDerivAt_shift (k := 2) hasDerivAt_betaPoly1 hasDerivAt_betaPoly2 y).congr_deriv (by unfold gammaPoly2; ring)

theorem hasDerivAt_gammaPoly2 (y : ℝ) : HasDerivAt gammaPoly2 (gammaPoly3 y) y :=
  (hasDerivAt_shift (k := 3) hasDerivAt_betaPoly2 hasDerivAt_betaPoly3 y).congr_deriv (by unfold gammaPoly3; ring)

theorem hasDerivAt_gammaPoly3 (y : ℝ) : HasDerivAt gammaPoly3 (gammaPoly4 y) y :=
  (hasDerivAt_shift (k := 4) hasDerivAt_betaPoly3 hasDerivAt_betaPoly4 y).congr_deriv (by unfold gammaPoly4; ring)

/-- **The profile `γ = (yβ)' = β + yβ'`**, which governs `T_β'`. -/
def gamma (y : ℝ) : ℝ := beta y + y * beta1 y

theorem beta1_neg (y : ℝ) : beta1 (-y) = -beta1 y := by unfold beta1; rw [clamp_neg]; unfold betaPoly1; ring

theorem gamma_eq (y : ℝ) : gamma y = gammaPoly (clamp y) := by
  by_cases h : y ∈ Icc (-1 : ℝ) 1
  · rw [clamp_of_mem h, gamma, beta, beta1, clamp_of_mem h, gammaPoly]
  · have hy : 1 ≤ |y| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h.le
    rw [gamma, beta_of_one_le_abs hy, beta1_of_one_le_abs hy, mul_zero, add_zero]
    rcases le_abs'.mp hy with h' | h'
    · rw [clamp_of_le_neg_one h']; norm_num [gammaPoly, betaPoly, betaPoly1]
    · rw [clamp_of_one_le h']; norm_num [gammaPoly, betaPoly, betaPoly1]

theorem hasDerivAt_gamma (y : ℝ) : HasDerivAt gamma (gammaPoly1 (clamp y)) y := by
  rw [show gamma = fun y => gammaPoly (clamp y) from funext gamma_eq]
  exact hasDerivAt_comp_clamp hasDerivAt_gammaPoly (by norm_num [gammaPoly1, betaPoly1, betaPoly2])
    (by norm_num [gammaPoly1, betaPoly1, betaPoly2]) y

theorem hasDerivAt_gamma_on : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gamma (gammaPoly1 s) s := fun s hs => by
  have h := hasDerivAt_gamma s
  rwa [clamp_of_mem (by rwa [uIcc_of_le (by norm_num)] at hs)] at h

theorem continuous_gamma : Continuous gamma := by
  unfold gamma; have := continuous_beta; have := continuous_beta1; fun_prop

theorem gamma_of_one_le_abs {y : ℝ} (h : 1 ≤ |y|) : gamma y = 0 := by
  rw [gamma, beta_of_one_le_abs h, beta1_of_one_le_abs h, mul_zero, add_zero]

theorem gamma_neg (y : ℝ) : gamma (-y) = gamma y := by rw [gamma, gamma, beta_neg, beta1_neg]; ring

theorem gamma_zero : gamma 0 = 1 := by rw [gamma, beta_zero, zero_mul, add_zero]

theorem integral_gamma : ∫ s in (-1 : ℝ)..1, gamma s = 0 := by
  have hP : ∀ y, HasDerivAt (fun y => y * beta y) (gamma y) y := fun y =>
    ((hasDerivAt_id' y).mul (hasDerivAt_beta y)).congr_deriv (by unfold gamma; ring)
  rw [integral_of_prim hP continuous_gamma, beta_one, beta_neg_one]; ring

/-- **`T_γ = F_∞(psi (2π) γ)`** on `θ > 1`. -/
theorem fullTail_psi_gamma {θ : ℝ} (hθ : 1 < θ) : fullTail (psi (2 * π) gamma) θ = profTail gamma θ :=
  fullTail_eq_profTail hasDerivAt_gamma_on (fun s _ => hasDerivAt_gammaPoly1 s)
    (by unfold gammaPoly2 betaPoly2 betaPoly3; fun_prop : Continuous gammaPoly2).continuousOn continuous_gamma
    (fun _ hy => gamma_of_one_le_abs hy) gamma_neg integral_gamma hθ

/-- `T_β' = −T_γ/θ` for the `N`-mode tails. -/
theorem hasDerivAt_profTailN_beta (N : ℕ) {θ : ℝ} (hθ : θ ≠ 0) :
    HasDerivAt (profTailN beta N) (-(1 / θ) * profTailN gamma N θ) θ := by
  have h1 := (hasDerivAt_const θ (beta 0)).div ((hasDerivAt_id' θ).const_mul 2) (mul_ne_zero two_ne_zero hθ)
  have h2 := HasDerivAt.fun_sum (u := Finset.range N) (x := θ)
    (A := fun n θ => beta (((n : ℝ) + 1) / θ) / θ)
    (A' := fun n => (beta1 (((n : ℝ) + 1) / θ) * (-((((n : ℝ) + 1)) / θ ^ 2)) * θ
      - beta (((n : ℝ) + 1) / θ) * 1) / θ ^ 2)
    fun n _ => ((hasDerivAt_beta _).comp θ (hasDerivAt_const_div _ hθ)).div (hasDerivAt_id' θ) hθ
  refine (h1.add h2).congr_deriv ?_
  unfold profTailN
  rw [mul_add, Finset.mul_sum, gamma_zero, beta_zero]
  congr 1
  · field_simp; ring
  · refine Finset.sum_congr rfl fun n _ => ?_
    unfold gamma
    field_simp
    ring

/-- **`T_β` is `C¹` on `(0, ∞)`**, with `T_β'(θ) = −T_γ(θ)/θ`. -/
theorem hasDerivAt_Tb {θ : ℝ} (hθ : 0 < θ) : HasDerivAt Tb (-(1 / θ) * profTail gamma θ) θ := by
  have h := (hasDerivAt_profTailN_beta (⌊θ⌋₊ + 1) hθ.ne').congr_of_eventuallyEq
    (profTail_eventuallyEq (fun _ hy => beta_of_one_le_abs hy) hθ)
  rwa [profTailN_eq (fun _ hy => gamma_of_one_le_abs hy) hθ (Nat.le_succ _)] at h

theorem continuousOn_deriv_Tb : ContinuousOn (fun θ => -(1 / θ) * profTail gamma θ) (Ioi 0) :=
  ((continuousOn_const.div continuousOn_id fun _ hθ => ne_of_gt hθ).neg).mul
    (continuousOn_profTail (fun _ hy => gamma_of_one_le_abs hy) continuous_gamma)

/-! ### `T⁺ = F_∞(Ψ)` is `C¹` on `(1, ∞)` -/

/-! ### Exact polynomial integrals and the Cauchy–Schwarz bound for `∫|p|` -/

/-- The polynomial with coefficient list `l`, lowest degree first. -/
noncomputable def polyL (l : List ℝ) (s : ℝ) : ℝ := ∑ k ∈ Finset.range l.length, l.getD k 0 * s ^ k

theorem integral_polyL (l : List ℝ) (a b : ℝ) :
    ∫ s in a..b, polyL l s
      = ∑ k ∈ Finset.range l.length, l.getD k 0 * ((b ^ (k + 1) - a ^ (k + 1)) / (k + 1)) := by
  unfold polyL
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun s : ℝ => l.getD k 0 * s ^ k).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]

/-- **Cauchy–Schwarz on `[−1, 1]`**: `∫|p| ≤ √(2∫p²)` for continuous `p`. -/
theorem integral_abs_le_sqrt {p : ℝ → ℝ} (hp : Continuous p) :
    ∫ s in (-1 : ℝ)..1, |p s| ≤ √(2 * ∫ s in (-1 : ℝ)..1, p s ^ 2) := by
  set I := ∫ s in (-1 : ℝ)..1, p s ^ 2 with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
  have key : ∀ t : ℝ, 0 < t → ∫ s in (-1 : ℝ)..1, |p s| ≤ I / (2 * t) + t := by
    intro t ht
    have hm : ∫ s in (-1 : ℝ)..1, |p s| ≤ ∫ s in (-1 : ℝ)..1, (p s ^ 2 / (2 * t) + t / 2) :=
      intervalIntegral.integral_mono_on (by norm_num) (hp.abs.intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun s _ => by
          rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (|p s| - t), sq_abs (p s), abs_nonneg (p s)]
    rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous fun s => p s ^ 2 / (2 * t)).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_div, intervalIntegral.integral_const] at hm
    simp only [smul_eq_mul] at hm
    linarith
  rcases hI0.lt_or_eq with hpos | hzero
  · have hs : 0 < √(I / 2) := Real.sqrt_pos.mpr (by positivity)
    refine (key _ hs).trans (le_of_eq ?_)
    have h2 : √(I / 2) * √(I / 2) = I / 2 := Real.mul_self_sqrt (by positivity)
    have h4 : √(2 * I) = 2 * √(I / 2) := by
      rw [show 2 * I = 2 ^ 2 * (I / 2) by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [h4]; field_simp; nlinarith [h2]
  · rw [← hzero, mul_zero, Real.sqrt_zero]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key ε hε
    rw [← hzero, zero_div, zero_add] at this
    linarith

theorem integral_betaPoly4_sq : ∫ s in (-1 : ℝ)..1, betaPoly4 s ^ 2 = 4423680 := by
  have e : (fun s : ℝ => betaPoly4 s ^ 2)
      = polyL [518400, 0, -14515200, 0, 123379200, 0, -304819200, 0, 228614400] := by
    funext s; simp [polyL, Finset.sum_range_succ, betaPoly4]; ring
  rw [e, integral_polyL]; simp [Finset.sum_range_succ]; norm_num

theorem integral_gammaPoly4_sq : ∫ s in (-1 : ℝ)..1, gammaPoly4 s ^ 2 = 698941440 := by
  have e : (fun s : ℝ => gammaPoly4 s ^ 2)
      = polyL [12960000, 0, -508032000, 0, 5958489600, 0, -19203609600, 0, 18517766400] := by
    funext s; simp [polyL, Finset.sum_range_succ, gammaPoly4, betaPoly4, betaPoly5]; ring
  rw [e, integral_polyL]; simp [Finset.sum_range_succ]; norm_num

theorem integral_betaPoly2_sq : ∫ s in (-1 : ℝ)..1, betaPoly2 s ^ 2 = 65536 / 143 := by
  have e : (fun s : ℝ => betaPoly2 s ^ 2)
      = polyL [576, 0, -17280, 0, 169920, 0, -628992, 0, 1068480, 0, -846720, 0, 254016] := by
    funext s; simp [polyL, Finset.sum_range_succ, betaPoly2]; ring
  rw [e, integral_polyL]; simp [Finset.sum_range_succ]; norm_num

/-- `∫|β⁗| ≤ √(2·4423680)`. -/
theorem integral_abs_betaPoly4_le : ∫ s in (-1 : ℝ)..1, |betaPoly4 s| ≤ √8847360 := by
  have h := integral_abs_le_sqrt (p := betaPoly4) (by unfold betaPoly4; fun_prop)
  rw [integral_betaPoly4_sq] at h; norm_num at h; exact h

/-- **`K_Ψ ≤ 768 + √8847360`**, the exact boundary jump `|β‴(1) − β‴(−1)| = 768` plus Cauchy–Schwarz. -/
theorem KPsi_le : KPsi ≤ 768 + √8847360 := by
  have h := integral_abs_betaPoly4_le
  unfold KPsi; norm_num [betaPoly3]; linarith

/-- **The rational bound** `K_Ψ/1440 ≤ 13/5`, so `|T⁺(θ)| ≤ (13/5)/θ⁴`. -/
theorem KPsi_div_le : KPsi / 1440 ≤ 13 / 5 := by
  have hs : √8847360 ≤ 2975 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have := KPsi_le; rw [div_le_iff₀ (by norm_num)]; linarith

/-! ### `T⁺` on `(1, 2]` and the sharpened `L²` bounds -/

/-- On `(0, 2]` only the mode `n = 1` survives: `T_f(θ) = (f(0) + 2f(1/θ))/(2θ)`. -/
theorem profTail_eq_of_le_two (hf : ∀ y, 1 ≤ |y| → f y = 0) {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ ≤ 2) :
    profTail f θ = (f 0 + 2 * f (1 / θ)) / (2 * θ) := by
  rw [← profTailN_eq hf hθ (N := 2) (Nat.floor_le_of_le (by norm_num; exact hθ2))]
  unfold profTailN
  have h2 : f ((((1 : ℕ) : ℝ) + 1) / θ) = 0 := hf _ (by
    rw [abs_of_pos (by positivity), le_div_iff₀ hθ]; norm_num; linarith)
  rw [Finset.sum_range_succ, Finset.sum_range_one, h2]
  norm_num
  field_simp

/-- On `(0, 2]`, `T_β(θ) = (1 + 2β(1/θ))/(2θ)`. -/
theorem Tb_eq_of_le_two {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ ≤ 2) : Tb θ = (1 + 2 * beta (1 / θ)) / (2 * θ) := by
  rw [Tb, profTail_eq_of_le_two (fun _ hy => beta_of_one_le_abs hy) hθ hθ2, beta_zero]

/-- `−1 ≤ β ≤ 0` on `[1/2, 1]`. -/
theorem beta_mem_of_half_le {v : ℝ} (h1 : 1 / 2 ≤ v) (h2 : v ≤ 1) : -1 ≤ beta v ∧ beta v ≤ 0 := by
  rw [beta_of_mem ⟨by linarith, h2⟩, betaPoly_eq]
  have hu : 1 / 4 ≤ v ^ 2 := by nlinarith
  have hu1 : v ^ 2 ≤ 1 := by nlinarith
  set u := v ^ 2
  have ha : 0 ≤ 1 - u := by linarith
  constructor
  · nlinarith [mul_nonneg (mul_nonneg ha ha) (sq_nonneg (3 * u - 1)), mul_nonneg ha (sq_nonneg (3 * u - 1)),
      sq_nonneg (3 * u - 1), mul_nonneg ha (mul_nonneg ha ha)]
  · exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha 3) (by linarith)

/-- **`|T⁺(θ)| ≤ 1/(2θ)` on `(1, 2]`.** -/
theorem abs_fullTail_Psi_le_of_le_two {θ : ℝ} (hθ : 1 < θ) (hθ2 : θ ≤ 2) : |fullTail Psi θ| ≤ 1 / (2 * θ) := by
  have hθ0 : 0 < θ := by linarith
  rw [fullTail_Psi hθ, Tb_eq_of_le_two hθ0 hθ2, abs_div, abs_of_pos (by positivity : 0 < 2 * θ)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hv1 : 1 / 2 ≤ 1 / θ := by rw [div_le_div_iff₀ (by norm_num) hθ0]; linarith
  have hv2 : 1 / θ ≤ 1 := by rw [div_le_one hθ0]; linarith
  obtain ⟨hl, hu⟩ := beta_mem_of_half_le hv1 hv2
  rw [abs_le]; constructor <;> linarith

/-- `∫_{(a,∞)} θ⁻ⁿ = 1/((n − 1)aⁿ⁻¹)` for `a > 0`, `n ≥ 2`, with integrability. -/
theorem integrableOn_Ioi_inv_pow {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (fun θ : ℝ => 1 / θ ^ n) (Ioi a) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -(n : ℝ)) (by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith) ha).congr_fun (fun θ hθ => ?_) measurableSet_Ioi
  have hθ : (0 : ℝ) < θ := lt_trans ha hθ
  show θ ^ (-(n : ℝ)) = 1 / θ ^ n
  rw [rpow_neg hθ.le, rpow_natCast, one_div]

theorem integral_Ioi_inv_pow {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) :
    ∫ θ in Ioi a, 1 / θ ^ n = 1 / (((n : ℝ) - 1) * a ^ (n - 1)) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun θ : ℝ => θ ^ (-(n : ℝ))) fun θ hθ => by
    have hθ : (0 : ℝ) < θ := lt_trans ha hθ
    simp only
    rw [rpow_neg hθ.le, rpow_natCast, one_div], integral_Ioi_rpow_of_lt (by linarith) ha]
  rw [show -(n : ℝ) + 1 = -((n : ℝ) - 1) by ring, rpow_neg ha.le,
    show (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) by rw [Nat.cast_sub (by omega)]; norm_num, rpow_natCast]
  field_simp

/-- **Split at `a`**: an integral over `(b, ∞)` is at most the majorants' integrals over `(b, a]` and `(a, ∞)`. -/
theorem setIntegral_Ioi_le_split {F f g : ℝ → ℝ} {b a : ℝ} (hba : b ≤ a) (hF : IntegrableOn F (Ioi b))
    (hf : IntegrableOn f (Ioc b a)) (hg : IntegrableOn g (Ioi a)) (h1 : ∀ θ ∈ Ioc b a, F θ ≤ f θ)
    (h2 : ∀ θ ∈ Ioi a, F θ ≤ g θ) :
    ∫ θ in Ioi b, F θ ≤ (∫ θ in b..a, f θ) + ∫ θ in Ioi a, g θ := by
  rw [← Ioc_union_Ioi_eq_Ioi hba, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hF.mono_set Ioc_subset_Ioi_self) (hF.mono_set (Ioi_subset_Ioi hba)), intervalIntegral.integral_of_le hba]
  exact add_le_add (setIntegral_mono_on (hF.mono_set Ioc_subset_Ioi_self) hf measurableSet_Ioc h1)
    (setIntegral_mono_on (hF.mono_set (Ioi_subset_Ioi hba)) hg measurableSet_Ioi h2)

theorem integral_inv_sq_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ θ in a..b, 1 / θ ^ 2 = 1 / a - 1 / b := by
  have hd : ∀ θ ∈ uIcc a b, HasDerivAt (fun θ : ℝ => -(1 / θ)) (1 / θ ^ 2) θ := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ
    exact (hasDerivAt_const_div 1 (by linarith [hθ.1] : θ ≠ 0)).neg.congr_deriv (neg_neg _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · ring
  · exact (continuousOn_const.div (continuousOn_pow 2) fun θ hθ => by
      rw [uIcc_of_le hab] at hθ; exact pow_ne_zero 2 (by linarith [hθ.1])).intervalIntegrable

/-- **`‖T⁺‖² ≤ 1/8 + (K_Ψ/1440)²/896`**: the exact `(1, 2]` profile and the `θ⁻⁴` envelope beyond. -/
theorem integral_fullTail_Psi_sq_le :
    ∫ θ in Ioi 1, fullTail Psi θ ^ 2 ≤ 1 / 8 + (KPsi / 1440) ^ 2 / 896 := by
  have h := setIntegral_Ioi_le_split (a := 2) (f := fun θ => 1 / 4 * (1 / θ ^ 2))
    (g := fun θ => (KPsi / 1440) ^ 2 * (1 / θ ^ 8)) (by norm_num) fullTail_Psi_sq.1
    ((continuousOn_const.mul (continuousOn_const.div (continuousOn_pow 2) fun θ hθ =>
      pow_ne_zero 2 (by linarith [hθ.1]))).integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self)
    ((integrableOn_Ioi_inv_pow two_pos (by norm_num)).const_mul _)
    (fun θ hθ => by
      have hθ0 : 0 < θ := by linarith [hθ.1]
      have hb := abs_fullTail_Psi_le_of_le_two hθ.1 hθ.2
      rw [← sq_abs]
      calc |fullTail Psi θ| ^ 2 ≤ (1 / (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = 1 / 4 * (1 / θ ^ 2) := by field_simp; ring)
    (fun θ (hθ : 2 < θ) => by
      have hθ0 : 0 < θ := by linarith
      have hb := abs_fullTail_Psi_le (by linarith : 1 < θ)
      rw [← sq_abs]
      calc |fullTail Psi θ| ^ 2 ≤ (KPsi / (1440 * θ ^ 4)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = (KPsi / 1440) ^ 2 * (1 / θ ^ 8) := by field_simp)
  rw [intervalIntegral.integral_const_mul, integral_inv_sq_interval one_pos (by norm_num),
    integral_const_mul, integral_Ioi_inv_pow two_pos (by norm_num)] at h
  norm_num at h; linarith

/-- **The rational bound** `‖T⁺‖² ≤ 133/1000`. -/
theorem integral_fullTail_Psi_sq_le_rat : ∫ θ in Ioi 1, fullTail Psi θ ^ 2 ≤ 133 / 1000 := by
  have h := integral_fullTail_Psi_sq_le
  have hK := KPsi_div_le
  have hK0 : 0 ≤ KPsi / 1440 := by have := KPsi_nonneg; positivity
  have : (KPsi / 1440) ^ 2 ≤ (13 / 5) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  linarith

/-- **`‖log θ · T⁺‖² ≤ 3/8 − (log 2)/2 + (K_Ψ/1440)²·29/13440`**, using `log θ ≤ θ − 1`. -/
theorem integral_log_fullTail_Psi_sq_le :
    ∫ θ in Ioi 1, (Real.log θ * fullTail Psi θ) ^ 2
      ≤ 3 / 8 - Real.log 2 / 2 + (KPsi / 1440) ^ 2 * (29 / 13440) := by
  have hc1 : ContinuousOn (fun θ : ℝ => 1 / 4 * (1 - 2 * (1 / θ) + 1 / θ ^ 2)) (Icc 1 2) :=
    continuousOn_const.mul ((continuousOn_const.sub (continuousOn_const.mul
      (continuousOn_const.div continuousOn_id fun θ hθ => (show (0 : ℝ) < θ by linarith [hθ.1]).ne'))).add
      (continuousOn_const.div (continuousOn_pow 2) fun θ hθ => pow_ne_zero 2 (by linarith [hθ.1])))
  have i6 := integrableOn_Ioi_inv_pow (n := 6) two_pos (by norm_num)
  have i7 := integrableOn_Ioi_inv_pow (n := 7) two_pos (by norm_num)
  have i8 := integrableOn_Ioi_inv_pow (n := 8) two_pos (by norm_num)
  have i67 : IntegrableOn (fun θ : ℝ => 1 / θ ^ 6 - 2 * (1 / θ ^ 7)) (Ioi 2) := i6.sub (i7.const_mul 2)
  have i678 : IntegrableOn (fun θ : ℝ => 1 / θ ^ 6 - 2 * (1 / θ ^ 7) + 1 / θ ^ 8) (Ioi 2) := i67.add i8
  have h := setIntegral_Ioi_le_split (a := 2) (f := fun θ => 1 / 4 * (1 - 2 * (1 / θ) + 1 / θ ^ 2))
    (g := fun θ => (KPsi / 1440) ^ 2 * (1 / θ ^ 6 - 2 * (1 / θ ^ 7) + 1 / θ ^ 8)) (by norm_num)
    log_fullTail_Psi_sq.1 (hc1.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self)
    (i678.const_mul _)
    (fun θ hθ => by
      have hθ0 : 0 < θ := by linarith [hθ.1]
      have hb := abs_fullTail_Psi_le_of_le_two hθ.1 hθ.2
      have hl0 : 0 ≤ Real.log θ := Real.log_nonneg hθ.1.le
      have hl : Real.log θ ≤ θ - 1 := Real.log_le_sub_one_of_pos hθ0
      rw [← sq_abs, abs_mul, abs_of_nonneg hl0]
      calc (Real.log θ * |fullTail Psi θ|) ^ 2 ≤ ((θ - 1) * (1 / (2 * θ))) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul hl hb (abs_nonneg _) (by linarith [hθ.1])) 2
        _ = 1 / 4 * (1 - 2 * (1 / θ) + 1 / θ ^ 2) := by field_simp; ring)
    (fun θ (hθ : 2 < θ) => by
      have hθ0 : 0 < θ := by linarith
      have hb := abs_fullTail_Psi_le (by linarith : 1 < θ)
      have hl0 : 0 ≤ Real.log θ := Real.log_nonneg (by linarith)
      have hl : Real.log θ ≤ θ - 1 := Real.log_le_sub_one_of_pos hθ0
      rw [← sq_abs, abs_mul, abs_of_nonneg hl0]
      calc (Real.log θ * |fullTail Psi θ|) ^ 2 ≤ ((θ - 1) * (KPsi / (1440 * θ ^ 4))) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul hl hb (abs_nonneg _) (by linarith)) 2
        _ = (KPsi / 1440) ^ 2 * (1 / θ ^ 6 - 2 * (1 / θ ^ 7) + 1 / θ ^ 8) := by field_simp; ring)
  have e1 : ∫ θ in (1 : ℝ)..2, 1 / 4 * (1 - 2 * (1 / θ) + 1 / θ ^ 2) = 1 / 4 * (3 / 2 - 2 * Real.log 2) := by
    have hi : IntervalIntegrable (fun θ : ℝ => 1 / θ) volume 1 2 :=
      (continuousOn_const.div continuousOn_id fun θ hθ => by
        rw [uIcc_of_le (by norm_num)] at hθ; exact (show (0 : ℝ) < θ by linarith [hθ.1]).ne').intervalIntegrable
    have hi2 : IntervalIntegrable (fun θ : ℝ => 1 / θ ^ 2) volume 1 2 :=
      (continuousOn_const.div (continuousOn_pow 2) fun θ hθ => by
        rw [uIcc_of_le (by norm_num)] at hθ; exact pow_ne_zero 2 (by linarith [hθ.1])).intervalIntegrable
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (intervalIntegrable_const.sub
      (hi.const_mul 2)) hi2, intervalIntegral.integral_sub intervalIntegrable_const (hi.const_mul 2),
      intervalIntegral.integral_const_mul, integral_one_div_of_pos one_pos two_pos,
      integral_inv_sq_interval one_pos (by norm_num), intervalIntegral.integral_const]
    norm_num; ring
  have e2 : ∫ θ in Ioi (2 : ℝ), (KPsi / 1440) ^ 2 * (1 / θ ^ 6 - 2 * (1 / θ ^ 7) + 1 / θ ^ 8)
      = (KPsi / 1440) ^ 2 * (29 / 13440) := by
    rw [integral_const_mul, integral_add i67 i8, integral_sub i6 (i7.const_mul 2),
      integral_const_mul, integral_Ioi_inv_pow two_pos (by norm_num), integral_Ioi_inv_pow two_pos (by norm_num),
      integral_Ioi_inv_pow two_pos (by norm_num)]
    norm_num
  rw [e1, e2] at h
  linarith

/-- **The rational bound** `‖log θ · T⁺‖² ≤ 11/250`. -/
theorem integral_log_fullTail_Psi_sq_le_rat : ∫ θ in Ioi 1, (Real.log θ * fullTail Psi θ) ^ 2 ≤ 11 / 250 := by
  have h := integral_log_fullTail_Psi_sq_le
  have hK0 : 0 ≤ KPsi / 1440 := by have := KPsi_nonneg; positivity
  have : (KPsi / 1440) ^ 2 ≤ (13 / 5) ^ 2 := pow_le_pow_left₀ hK0 KPsi_div_le 2
  have := Real.log_two_gt_d9
  linarith

/-! ### Decay of `T_β' = −T_γ/θ` and the variation functionals -/

/-- `A_γ = |γ''(1) + γ''(−1)|/(2π)³`, the `ξ⁻³` constant of `psi (2π) γ`. -/
noncomputable def Agam : ℝ := |gammaPoly2 1 + gammaPoly2 (-1)| / (2 * π) ^ 3

/-- `B_γ = (|γ‴(1) − γ‴(−1)| + ∫|γ⁗|)/(2π)⁴`, the `ξ⁻⁴` constant of `psi (2π) γ`. -/
noncomputable def Bgam : ℝ :=
  (|gammaPoly3 1 - gammaPoly3 (-1)| + ∫ s in (-1 : ℝ)..1, |gammaPoly4 s|) / (2 * π) ^ 4

theorem Agam_nonneg : 0 ≤ Agam := by unfold Agam; positivity

theorem Bgam_nonneg : 0 ≤ Bgam := by
  unfold Bgam
  have := intervalIntegral.integral_nonneg (μ := volume) (a := (-1 : ℝ)) (b := 1) (f := fun s => |gammaPoly4 s|)
    (by norm_num) fun _ _ => abs_nonneg _
  positivity

/-- **`|psi (2π) γ (ξ)| ≤ A_γ/ξ³ + B_γ/ξ⁴`** for `ξ > 0`, since `γ(±1) = 0` and `γ'(1) = γ'(−1)`. -/
theorem abs_psi_gamma_le {ξ : ℝ} (hξ : 0 < ξ) : |psi (2 * π) gamma ξ| ≤ Agam / ξ ^ 3 + Bgam / ξ ^ 4 := by
  have hcξ : 2 * π * ξ ≠ 0 := by positivity
  have h4c : Continuous gammaPoly4 := by unfold gammaPoly4 betaPoly4 betaPoly5; fun_prop
  have h2c : Continuous gammaPoly2 := by unfold gammaPoly2 betaPoly2 betaPoly3; fun_prop
  have h1 := Cvs.Prolate.CosineTransformSecondOrder.psi_eq hasDerivAt_gamma_on (fun s _ => hasDerivAt_gammaPoly1 s)
    h2c.continuousOn hcξ
  have hb := Cvs.Prolate.CosineTransformSecondOrder.psi_sub_le (fun s _ => hasDerivAt_gammaPoly2 s)
    (fun s _ => hasDerivAt_gammaPoly3 s) h4c.continuousOn hcξ
  have e : ∫ s in (-1 : ℝ)..1, gammaPoly2 s * cos (2 * π * ξ * s) = psi (2 * π) gammaPoly2 ξ := rfl
  rw [h1, gamma_of_one_le_abs (by norm_num), gamma_of_one_le_abs (by norm_num), e]
  have hg1 : gammaPoly1 1 - gammaPoly1 (-1) = 0 := by norm_num [gammaPoly1, betaPoly1, betaPoly2]
  rw [hg1]
  simp only [add_zero, zero_mul, zero_div, zero_sub, abs_neg, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π * ξ) ^ 2)]
  set A := gammaPoly2 1 + gammaPoly2 (-1)
  set C := |gammaPoly3 1 - gammaPoly3 (-1)| + ∫ s in (-1 : ℝ)..1, |gammaPoly4 s|
  have hs : |A * sin (2 * π * ξ) / (2 * π * ξ)| ≤ |A| / (2 * π * ξ) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * π * ξ)]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)) (by positivity)
  have hp : |psi (2 * π) gammaPoly2 ξ| ≤ |A| / (2 * π * ξ) + C / (2 * π * ξ) ^ 2 := by
    have := abs_sub_abs_le_abs_sub (psi (2 * π) gammaPoly2 ξ) (A * sin (2 * π * ξ) / (2 * π * ξ))
    linarith
  calc |psi (2 * π) gammaPoly2 ξ| / (2 * π * ξ) ^ 2
      ≤ (|A| / (2 * π * ξ) + C / (2 * π * ξ) ^ 2) / (2 * π * ξ) ^ 2 :=
        div_le_div_of_nonneg_right hp (by positivity)
    _ = Agam / ξ ^ 3 + Bgam / ξ ^ 4 := by unfold Agam Bgam; field_simp; ring

theorem hasSum_inv_succ_sq : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero] at h
  exact_mod_cast h

/-- **`T_γ = O(θ⁻³)`**: `|T_γ(θ)| ≤ A_γ(π²/6)/θ³ + B_γ(π⁴/90)/θ⁴` on `θ > 1`. -/
theorem abs_profTail_gamma_le {θ : ℝ} (hθ : 1 < θ) :
    |profTail gamma θ| ≤ Agam * (π ^ 2 / 6) / θ ^ 3 + Bgam * (π ^ 4 / 90) / θ ^ 4 := by
  have hθ0 : 0 < θ := by linarith
  have hA : gamma 1 + gamma (-1) = 0 := by
    rw [gamma_of_one_le_abs (by norm_num), gamma_of_one_le_abs (by norm_num), add_zero]
  have hs := hasSum_fullTail hasDerivAt_gamma_on (fun s _ => hasDerivAt_gammaPoly1 s)
    (by unfold gammaPoly2 betaPoly2 betaPoly3; fun_prop : Continuous gammaPoly2).continuousOn hA hθ
  rw [fullTail_psi_gamma hθ] at hs
  have hterm : ∀ m : ℕ, |psi (2 * π) gamma (((m : ℝ) + 1) * θ)|
      ≤ Agam / θ ^ 3 * (1 / ((m : ℝ) + 1) ^ 2) + Bgam / θ ^ 4 * (1 / ((m : ℝ) + 1) ^ 4) := fun m => by
    have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := m.cast_nonneg (α := ℝ); linarith
    refine (abs_psi_gamma_le (by positivity)).trans (add_le_add ?_ (le_of_eq (by field_simp)))
    rw [mul_pow, div_mul_div_comm, mul_one]
    refine div_le_div_of_nonneg_left Agam_nonneg (by positivity) ?_
    have hpow : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 3 := pow_le_pow_right₀ hm (by norm_num)
    nlinarith [pow_pos hθ0 3]
  have hb := (hasSum_inv_succ_sq.mul_left (Agam / θ ^ 3)).add (hasSum_inv_succ_pow_four.mul_left (Bgam / θ ^ 4))
  rw [show Agam * (π ^ 2 / 6) / θ ^ 3 + Bgam * (π ^ 4 / 90) / θ ^ 4
      = Agam / θ ^ 3 * (π ^ 2 / 6) + Bgam / θ ^ 4 * (π ^ 4 / 90) by ring, abs_le]
  constructor
  · have := hasSum_le (fun m => neg_le_of_abs_le (hterm m)) hb.neg hs
    linarith
  · exact hasSum_le (fun m => le_of_abs_le (hterm m)) hs hb

/-- `A_γ(π²/6) = 16/π`. -/
theorem Agam_mul_eq : Agam * (π ^ 2 / 6) = 16 / π := by
  unfold Agam; norm_num [gammaPoly2, betaPoly2, betaPoly3]; field_simp; ring

/-- `B_γ(π⁴/90) = (14592 + ∫|γ⁗|)/1440`. -/
theorem Bgam_mul_eq : Bgam * (π ^ 4 / 90) = (14592 + ∫ s in (-1 : ℝ)..1, |gammaPoly4 s|) / 1440 := by
  unfold Bgam; norm_num [gammaPoly3, betaPoly3, betaPoly4]; field_simp; ring

/-- **`T_β' = O(θ⁻⁴)`**: `|T_β'(θ)| ≤ (16/π)/θ⁴ + B_γ(π⁴/90)/θ⁵` on `θ > 1`. -/
theorem abs_deriv_Tb_le {θ : ℝ} (hθ : 1 < θ) :
    |-(1 / θ) * profTail gamma θ| ≤ 16 / π / θ ^ 4 + Bgam * (π ^ 4 / 90) / θ ^ 5 := by
  have hθ0 : 0 < θ := by linarith
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / θ), ← Agam_mul_eq]
  calc 1 / θ * |profTail gamma θ| ≤ 1 / θ * (Agam * (π ^ 2 / 6) / θ ^ 3 + Bgam * (π ^ 4 / 90) / θ ^ 4) :=
        mul_le_mul_of_nonneg_left (abs_profTail_gamma_le hθ) (by positivity)
    _ = Agam * (π ^ 2 / 6) / θ ^ 4 + Bgam * (π ^ 4 / 90) / θ ^ 5 := by field_simp

/-- `|1 + 2γ(v)| ≤ 43/10` on `[1/2, 1]`, from `γ = w²(48 − 128w + 81w²)`, `w = 1 − v²`. -/
theorem abs_one_add_two_gamma_le {v : ℝ} (h1 : 1 / 2 ≤ v) (h2 : v ≤ 1) : |1 + 2 * gamma v| ≤ 43 / 10 := by
  rw [gamma_eq, clamp_of_mem ⟨by linarith, h2⟩]
  have e : gammaPoly v = (1 - v ^ 2) ^ 2 * (48 - 128 * (1 - v ^ 2) + 81 * (1 - v ^ 2) ^ 2) := by
    unfold gammaPoly betaPoly betaPoly1; ring
  have hw0 : 0 ≤ 1 - v ^ 2 := by nlinarith
  have hw1 : 1 - v ^ 2 ≤ 3 / 4 := by nlinarith
  rw [e]
  set w := 1 - v ^ 2
  have hup : w ^ 2 * (48 - 128 * w + 81 * w ^ 2) ≤ 33 / 20 := by
    nlinarith [sq_nonneg (w - 1 / 3), sq_nonneg (w - 0.4), mul_nonneg hw0 (sub_nonneg.2 hw1),
      mul_nonneg (mul_nonneg hw0 hw0) (sub_nonneg.2 hw1), sq_nonneg (w ^ 2 - w / 2)]
  have hlo : -53 / 20 ≤ w ^ 2 * (48 - 128 * w + 81 * w ^ 2) := by
    nlinarith [sq_nonneg (w - 1 / 3), mul_nonneg hw0 (sub_nonneg.2 hw1),
      mul_nonneg (mul_nonneg hw0 hw0) (sub_nonneg.2 hw1), sq_nonneg (w ^ 2 - w / 2),
      sq_nonneg (9 * w ^ 2 - 64 / 9 * w)]
  rw [abs_le]; constructor <;> linarith

/-- **`|T_β'(θ)| ≤ (43/20)/θ²` on `(1, 2]`.** -/
theorem abs_deriv_Tb_le_of_le_two {θ : ℝ} (hθ : 1 < θ) (hθ2 : θ ≤ 2) :
    |-(1 / θ) * profTail gamma θ| ≤ 43 / 20 / θ ^ 2 := by
  have hθ0 : 0 < θ := by linarith
  rw [profTail_eq_of_le_two (fun _ hy => gamma_of_one_le_abs hy) hθ0 hθ2, gamma_zero, abs_mul, abs_neg,
    abs_of_pos (by positivity : 0 < 1 / θ), abs_div, abs_of_pos (by positivity : 0 < 2 * θ)]
  have hv1 : 1 / 2 ≤ 1 / θ := by rw [div_le_div_iff₀ (by norm_num) hθ0]; linarith
  have hv2 : 1 / θ ≤ 1 := by rw [div_le_one hθ0]; linarith
  have h := abs_one_add_two_gamma_le hv1 hv2
  calc 1 / θ * (|1 + 2 * gamma (1 / θ)| / (2 * θ)) ≤ 1 / θ * (43 / 10 / (2 * θ)) := by gcongr
    _ = 43 / 20 / θ ^ 2 := by field_simp; ring

theorem continuousOn_deriv_Tb_Ioi_one : ContinuousOn (fun θ => -(1 / θ) * profTail gamma θ) (Ioi 1) :=
  continuousOn_deriv_Tb.mono fun _ hθ => mem_Ioi.mpr (lt_trans one_pos hθ)

theorem abs_deriv_Tb_le_inv_pow {θ : ℝ} (hθ : 1 < θ) :
    |-(1 / θ) * profTail gamma θ| ≤ (16 / π + Bgam * (π ^ 4 / 90)) / θ ^ 4 := by
  have hθ0 : 0 < θ := by linarith
  have hB := Bgam_nonneg
  have h5 : Bgam * (π ^ 4 / 90) / θ ^ 5 ≤ Bgam * (π ^ 4 / 90) / θ ^ 4 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hθ.le (by norm_num))
  have := abs_deriv_Tb_le hθ
  rw [add_div]; linarith

/-- **`V₀ = ∫_{(1,∞)} |T_β'| ≤ 43/40 + 2/(3π) + B_γ(π⁴/90)/64`**, with `T_β' ∈ L¹(1, ∞)`. -/
theorem V0_le :
    IntegrableOn (fun θ => |-(1 / θ) * profTail gamma θ|) (Ioi 1)
      ∧ ∫ θ in Ioi 1, |-(1 / θ) * profTail gamma θ| ≤ 43 / 40 + 2 / (3 * π) + Bgam * (π ^ 4 / 90) / 64 := by
  have hi := (integrableOn_of_le_inv_pow (F := fun θ => |-(1 / θ) * profTail gamma θ|) (n := 4)
    (K := 16 / π + Bgam * (π ^ 4 / 90))
    (continuousOn_deriv_Tb_Ioi_one.abs.aestronglyMeasurable measurableSet_Ioi) (by norm_num)
    fun θ hθ => by rw [abs_abs]; exact abs_deriv_Tb_le_inv_pow hθ).1
  refine ⟨hi, ?_⟩
  have i4 := integrableOn_Ioi_inv_pow (n := 4) two_pos (by norm_num)
  have i5 := integrableOn_Ioi_inv_pow (n := 5) two_pos (by norm_num)
  have ig : IntegrableOn (fun θ : ℝ => 16 / π * (1 / θ ^ 4) + Bgam * (π ^ 4 / 90) * (1 / θ ^ 5)) (Ioi 2) :=
    (i4.const_mul (16 / π)).add (i5.const_mul (Bgam * (π ^ 4 / 90)))
  have h := setIntegral_Ioi_le_split (a := 2) (f := fun θ => 43 / 20 * (1 / θ ^ 2))
    (g := fun θ => 16 / π * (1 / θ ^ 4) + Bgam * (π ^ 4 / 90) * (1 / θ ^ 5)) (by norm_num) hi
    ((continuousOn_const.mul (continuousOn_const.div (continuousOn_pow 2) fun θ hθ =>
      pow_ne_zero 2 (by linarith [hθ.1]))).integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self)
    ig
    (fun θ hθ => (abs_deriv_Tb_le_of_le_two hθ.1 hθ.2).trans (le_of_eq (by ring)))
    (fun θ (hθ : 2 < θ) => (abs_deriv_Tb_le (by linarith)).trans (le_of_eq (by ring)))
  rw [intervalIntegral.integral_const_mul, integral_inv_sq_interval one_pos (by norm_num),
    integral_add (i4.const_mul (16 / π)) (i5.const_mul (Bgam * (π ^ 4 / 90))), integral_const_mul,
    integral_const_mul,
    integral_Ioi_inv_pow two_pos (by norm_num), integral_Ioi_inv_pow two_pos (by norm_num)] at h
  have hπ := pi_pos
  refine h.trans (le_of_eq ?_)
  field_simp; ring

/-- **`∫_{(1,∞)} |T_β'| θ^{1/2} ≤ (43/40)(log 2 + 1/2) + (2/π + B_γ(π⁴/90)/24)/√2`**, the integral in `V_{1/2}`. -/
theorem V_half_le :
    IntegrableOn (fun θ => |-(1 / θ) * profTail gamma θ| * √θ) (Ioi 1)
      ∧ ∫ θ in Ioi 1, |-(1 / θ) * profTail gamma θ| * √θ
        ≤ 43 / 40 * (Real.log 2 + 1 / 2) + (2 / π + Bgam * (π ^ 4 / 90) / 24) / √2 := by
  have hc : ContinuousOn (fun θ => |-(1 / θ) * profTail gamma θ| * √θ) (Ioi 1) :=
    continuousOn_deriv_Tb_Ioi_one.abs.mul continuous_sqrt.continuousOn
  have hi := (integrableOn_of_le_inv_pow (F := fun θ => |-(1 / θ) * profTail gamma θ| * √θ) (n := 3)
    (K := 16 / π + Bgam * (π ^ 4 / 90)) (hc.aestronglyMeasurable measurableSet_Ioi)
    (by norm_num) fun θ hθ => by
      have hθ0 : 0 < θ := by linarith
      have hs : √θ ≤ θ := Real.sqrt_le_iff.mpr ⟨hθ0.le, by nlinarith⟩
      have hK : 0 ≤ 16 / π + Bgam * (π ^ 4 / 90) := by have := Bgam_nonneg; have := pi_pos; positivity
      rw [abs_mul, abs_abs, abs_of_nonneg (Real.sqrt_nonneg θ)]
      calc |-(1 / θ) * profTail gamma θ| * √θ ≤ (16 / π + Bgam * (π ^ 4 / 90)) / θ ^ 4 * θ :=
            mul_le_mul (abs_deriv_Tb_le_inv_pow hθ) hs (Real.sqrt_nonneg θ) (by positivity)
        _ = (16 / π + Bgam * (π ^ 4 / 90)) / θ ^ 3 := by field_simp).1
  refine ⟨hi, ?_⟩
  have i3 := integrableOn_Ioi_inv_pow (n := 3) two_pos (by norm_num)
  have i4 := integrableOn_Ioi_inv_pow (n := 4) two_pos (by norm_num)
  have hs2 : 0 < √2 := by positivity
  have ig : IntegrableOn (fun θ : ℝ => 16 / π / √2 * (1 / θ ^ 3) + Bgam * (π ^ 4 / 90) / √2 * (1 / θ ^ 4))
      (Ioi 2) := (i3.const_mul (16 / π / √2)).add (i4.const_mul (Bgam * (π ^ 4 / 90) / √2))
  have h := setIntegral_Ioi_le_split (a := 2) (f := fun θ => 43 / 40 * (1 / θ ^ 2 + 1 / θ))
    (g := fun θ => 16 / π / √2 * (1 / θ ^ 3) + Bgam * (π ^ 4 / 90) / √2 * (1 / θ ^ 4)) (by norm_num) hi
    ((continuousOn_const.mul ((continuousOn_const.div (continuousOn_pow 2) fun θ hθ =>
      pow_ne_zero 2 (by linarith [hθ.1])).add (continuousOn_const.div continuousOn_id
      fun θ hθ => (show (0 : ℝ) < θ by linarith [hθ.1]).ne'))).integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self)
    ig
    (fun θ hθ => by
      have hθ0 : 0 < θ := by linarith [hθ.1]
      have hs : √θ ≤ (1 + θ) / 2 := by
        rw [Real.sqrt_le_left]; · nlinarith [sq_nonneg (θ - 1)]
        positivity
      calc |-(1 / θ) * profTail gamma θ| * √θ ≤ 43 / 20 / θ ^ 2 * ((1 + θ) / 2) :=
            mul_le_mul (abs_deriv_Tb_le_of_le_two hθ.1 hθ.2) hs (Real.sqrt_nonneg θ) (by positivity)
        _ = 43 / 40 * (1 / θ ^ 2 + 1 / θ) := by field_simp; ring)
    (fun θ (hθ : 2 < θ) => by
      have hθ0 : 0 < θ := by linarith
      have hs : √θ ≤ θ / √2 := by
        rw [le_div_iff₀ hs2, ← Real.sqrt_mul hθ0.le]
        exact Real.sqrt_le_iff.mpr ⟨hθ0.le, by nlinarith⟩
      have hK : 0 ≤ 16 / π / θ ^ 4 + Bgam * (π ^ 4 / 90) / θ ^ 5 := by
        have := Bgam_nonneg; have := pi_pos; positivity
      calc |-(1 / θ) * profTail gamma θ| * √θ ≤ (16 / π / θ ^ 4 + Bgam * (π ^ 4 / 90) / θ ^ 5) * (θ / √2) :=
            mul_le_mul (abs_deriv_Tb_le (by linarith)) hs (Real.sqrt_nonneg θ) hK
        _ = 16 / π / √2 * (1 / θ ^ 3) + Bgam * (π ^ 4 / 90) / √2 * (1 / θ ^ 4) := by field_simp)
  have e1 : ∫ θ in (1 : ℝ)..2, 43 / 40 * (1 / θ ^ 2 + 1 / θ) = 43 / 40 * (1 / 2 + Real.log 2) := by
    have hi1 : IntervalIntegrable (fun θ : ℝ => 1 / θ) volume 1 2 :=
      (continuousOn_const.div continuousOn_id fun θ hθ => by
        rw [uIcc_of_le (by norm_num)] at hθ; exact (show (0 : ℝ) < θ by linarith [hθ.1]).ne').intervalIntegrable
    have hi2 : IntervalIntegrable (fun θ : ℝ => 1 / θ ^ 2) volume 1 2 :=
      (continuousOn_const.div (continuousOn_pow 2) fun θ hθ => by
        rw [uIcc_of_le (by norm_num)] at hθ; exact pow_ne_zero 2 (by linarith [hθ.1])).intervalIntegrable
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi2 hi1,
      integral_inv_sq_interval one_pos (by norm_num), integral_one_div_of_pos one_pos two_pos]
    norm_num
  rw [e1, integral_add (i3.const_mul (16 / π / √2)) (i4.const_mul (Bgam * (π ^ 4 / 90) / √2)),
    integral_const_mul, integral_const_mul,
    integral_Ioi_inv_pow two_pos (by norm_num), integral_Ioi_inv_pow two_pos (by norm_num)] at h
  refine h.trans (le_of_eq ?_)
  have hπ := pi_pos
  field_simp; ring

/-- `∫|γ⁗| ≤ √(2·698941440)`. -/
theorem integral_abs_gammaPoly4_le : ∫ s in (-1 : ℝ)..1, |gammaPoly4 s| ≤ √1397882880 := by
  have h := integral_abs_le_sqrt (p := gammaPoly4) (by unfold gammaPoly4 betaPoly4 betaPoly5; fun_prop)
  rw [integral_gammaPoly4_sq] at h; norm_num at h; exact h

/-- **The rational bound** `B_γ(π⁴/90) ≤ 51981/1440`. -/
theorem Bgam_mul_le : Bgam * (π ^ 4 / 90) ≤ 51981 / 1440 := by
  have hs : √1397882880 ≤ 37389 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [Bgam_mul_eq]
  have := integral_abs_gammaPoly4_le
  rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith

/-- **The rational bound** `V₀ ≤ 93/50`. -/
theorem V0_le_rat : ∫ θ in Ioi 1, |-(1 / θ) * profTail gamma θ| ≤ 93 / 50 := by
  have h := V0_le.2
  have hB := Bgam_mul_le
  have hπ : 2 / (3 * π) ≤ 2 / (3 * 3.141592) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [pi_gt_d6])
  linarith

/-- **The rational bound** `∫_{(1,∞)} |T_β'| θ^{1/2} ≤ 14/5`, so `V_{1/2} ≤ 33/10`. -/
theorem V_half_le_rat : ∫ θ in Ioi 1, |-(1 / θ) * profTail gamma θ| * √θ ≤ 14 / 5 := by
  have h := V_half_le.2
  have hB := Bgam_mul_le
  have hπ : 2 / π ≤ 2 / 3.141592 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [pi_gt_d6])
  have hl := Real.log_two_lt_d9
  have hs2 : 1 / √2 ≤ 70711 / 100000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hB0 := Bgam_nonneg
  have hX : (2 / π + Bgam * (π ^ 4 / 90) / 24) / √2 ≤ (2 / 3.141592 + 51981 / 1440 / 24) * (70711 / 100000) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hs2 (by positivity) (by positivity)
  linarith

/-! ### `C_L1`: the position-truncation rate of `T⁺` -/

/-- `C₁(β) = ∫|β''|`, the second-order constant of `Ψ` in `FullTailConvergence`'s rate. -/
noncomputable def C1beta : ℝ := ∫ s in (-1 : ℝ)..1, |beta2 s|

theorem C1beta_nonneg : 0 ≤ C1beta :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _

/-- **`K1b(2π, 0, C₁(β)) = C₁(β)²(1/(2π⁴) + 1/576)`**, since `β(±1) = β'(±1) = 0`. -/
theorem K1b_Psi_eq :
    K1b (2 * π) (beta 1 + beta (-1)) (|beta1 1 - beta1 (-1)| + ∫ s in (-1 : ℝ)..1, |beta2 s|)
      = C1beta ^ 2 * (1 / (2 * π ^ 4) + 1 / 576) := by
  rw [beta_edge, beta1_one, beta1_neg_one, sub_zero, abs_zero, zero_add]
  unfold K1b BG C1beta
  have hπ := pi_pos
  simp only [abs_zero, mul_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    zero_add]
  field_simp
  ring

/-- **`‖posTail(Ψ, k) − T⁺‖ ≤ C₁(β)√(1/(2π⁴) + 1/576) · k^{−1/4}`** for `k ≥ 1` (`FullTailConvergence`'s `L²` rate). -/
theorem norm_posTail_sub_fullTail_Psi_le {k : ℝ} (hk : 1 ≤ k) :
    √(∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2)
      ≤ C1beta * √(1 / (2 * π ^ 4) + 1 / 576) * k ^ (-(1 / 4 : ℝ)) := by
  have hk0 : 0 < k := by linarith
  have h := integral_sub_sq_le hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2
    (by positivity : (0 : ℝ) < 2 * π) hk
  have h2 := K1_le (by positivity : (0 : ℝ) < 2 * π) (beta 1 + beta (-1))
    (|beta1 1 - beta1 (-1)| + ∫ s in (-1 : ℝ)..1, |beta2 s|) hk
  rw [K1b_Psi_eq] at h2
  have hs : √k = (k ^ (-(1 / 4 : ℝ))) ^ (-2 : ℝ) := by
    rw [← rpow_mul hk0.le, Real.sqrt_eq_rpow]; norm_num
  have hq : 0 < k ^ (-(1 / 4 : ℝ)) := rpow_pos_of_pos hk0 _
  have hsq : √k = 1 / (k ^ (-(1 / 4 : ℝ))) ^ 2 := by
    rw [hs, rpow_neg hq.le, rpow_two]; exact (one_div _).symm
  refine (Real.sqrt_le_sqrt (h.trans h2)).trans (le_of_eq ?_)
  rw [hsq, div_div_eq_mul_div, div_one, Real.sqrt_mul (by have := C1beta_nonneg; positivity),
    Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq C1beta_nonneg]

/-- `C_L1 = ∫_{(1,∞)} ‖T⁺ − posTail(Ψ, k)‖ dk/k`. -/
noncomputable def CL1 : ℝ := ∫ k in Ioi 1, √(∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2) / k

/-- **`C_L1 ≤ 4 C₁(β)√(1/(2π⁴) + 1/576)`**, from `∫_1^∞ k^{−5/4} = 4`. -/
theorem CL1_le : CL1 ≤ 4 * (C1beta * √(1 / (2 * π ^ 4) + 1 / 576)) := by
  set c := C1beta * √(1 / (2 * π ^ 4) + 1 / 576) with hc
  have hc0 : 0 ≤ c := by have := C1beta_nonneg; positivity
  have hmaj : IntegrableOn (fun k : ℝ => c * k ^ (-(5 / 4 : ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul c
  have hint : ∫ k in Ioi (1 : ℝ), c * k ^ (-(5 / 4 : ℝ)) = 4 * c := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos, one_rpow]; norm_num; ring
  unfold CL1
  by_cases hI : IntegrableOn (fun k => √(∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2) / k) (Ioi 1)
  · rw [← hint]
    refine setIntegral_mono_on hI hmaj measurableSet_Ioi fun k (hk : 1 < k) => ?_
    have hk0 : 0 < k := by linarith
    have h := norm_posTail_sub_fullTail_Psi_le hk.le
    rw [← hc] at h
    calc √(∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2) / k ≤ c * k ^ (-(1 / 4 : ℝ)) / k :=
          div_le_div_of_nonneg_right h hk0.le
      _ = c * k ^ (-(5 / 4 : ℝ)) := by
          rw [mul_div_assoc, show -(5 / 4 : ℝ) = -(1 / 4) + -1 by norm_num, rpow_add hk0, rpow_neg_one]
          ring
  · rw [integral_undef hI]; positivity

/-- `C₁(β) ≤ √(2·65536/143)`. -/
theorem C1beta_le : C1beta ≤ √(131072 / 143) := by
  have h := integral_abs_le_sqrt (p := betaPoly2) (by unfold betaPoly2; fun_prop)
  rw [integral_betaPoly2_sq] at h
  have e : C1beta = ∫ s in (-1 : ℝ)..1, |betaPoly2 s| := by
    unfold C1beta
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [beta2, clamp_of_mem hs]
  rw [e]; norm_num at h ⊢; exact h

/-- **The rational bound** `C_L1 ≤ 101/10`. -/
theorem CL1_le_rat : CL1 ≤ 101 / 10 := by
  have h := CL1_le
  have hC : C1beta ≤ 3028 / 100 := C1beta_le.trans (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  have hπ4 : (3.141592 : ℝ) ^ 4 ≤ π ^ 4 := pow_le_pow_left₀ (by norm_num) pi_gt_d6.le 4
  have hq : 1 / (2 * π ^ 4) + 1 / 576 ≤ (829 / 10000) ^ 2 := by
    have : 1 / (2 * π ^ 4) ≤ 1 / (2 * 3.141592 ^ 4) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    norm_num at this ⊢; linarith
  have hs : √(1 / (2 * π ^ 4) + 1 / 576) ≤ 829 / 10000 := Real.sqrt_le_iff.mpr ⟨by norm_num, hq⟩
  have h0 := C1beta_nonneg
  have := mul_le_mul hC hs (Real.sqrt_nonneg _) (by norm_num)
  linarith

/-! ### The spectral density of `T⁺` -/

open Cvs.Prolate.Mellin.MellinKernelSturmLiouville in
/-- The Mellin primitives `(−u/(t² + ¼), −ũ/(t² + ¼))` of the kernels `y_t` and `ỹ_t`. -/
noncomputable def mellinPrim (t : ℝ) (θ : ℝ) : ℝ × ℝ := (-(ku t θ / (t ^ 2 + 1 / 4)), -(kus t θ / (t ^ 2 + 1 / 4)))

open Cvs.Prolate.Mellin.MellinKernelSturmLiouville in
theorem hasDerivAt_mellinPrim_fst (t θ : ℝ) (hθ : 0 < θ) :
    HasDerivAt (fun θ => (mellinPrim t θ).1) (ky t θ) θ := by
  have h := ((hasDerivAt_ku (ξ := t) hθ).div_const (t ^ 2 + 1 / 4)).neg
  refine h.congr_deriv ?_
  field_simp

open Cvs.Prolate.Mellin.MellinKernelSturmLiouville in
theorem hasDerivAt_mellinPrim_snd (t θ : ℝ) (hθ : 0 < θ) :
    HasDerivAt (fun θ => (mellinPrim t θ).2) (kys t θ) θ := by
  have h := ((hasDerivAt_kus (ξ := t) hθ).div_const (t ^ 2 + 1 / 4)).neg
  refine h.congr_deriv ?_
  field_simp

open Cvs.Prolate.Mellin.MellinKernelSturmLiouville in
/-- **`P_c² + P_s² = θ/(t² + ¼)`.** -/
theorem mellinPrim_sq (t : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    (mellinPrim t θ).1 ^ 2 + (mellinPrim t θ).2 ^ 2 = θ / (t ^ 2 + 1 / 4) := by
  unfold mellinPrim ku kus
  have hs := sin_sq_add_cos_sq (t * Real.log θ)
  have hq := Real.sq_sqrt hθ
  field_simp
  linear_combination 4 * (4 * t ^ 2 + 1) * √θ ^ 2 * hs + 4 * (4 * t ^ 2 + 1) * hq

/-- `|P_c u + P_s w| ≤ √θ/√(t² + ¼)` for a unit vector `(u, w)`. -/
theorem abs_mellinPrim_comb_le (t : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) {u w : ℝ} (huw : u ^ 2 + w ^ 2 = 1) :
    |(mellinPrim t θ).1 * u + (mellinPrim t θ).2 * w| ≤ √θ / √(t ^ 2 + 1 / 4) := by
  rw [← Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ t ^ 2 + 1 / 4), ← mellinPrim_sq t hθ]
  apply Real.abs_le_sqrt
  set a := (mellinPrim t θ).1; set b := (mellinPrim t θ).2
  nlinarith [sq_nonneg (a * w - b * u)]

theorem continuousOn_mellinPrim_fst (t : ℝ) : ContinuousOn (fun θ => (mellinPrim t θ).1) (Ioi 0) :=
  fun _ hθ => (hasDerivAt_mellinPrim_fst t _ hθ).continuousAt.continuousWithinAt

theorem continuousOn_mellinPrim_snd (t : ℝ) : ContinuousOn (fun θ => (mellinPrim t θ).2) (Ioi 0) :=
  fun _ hθ => (hasDerivAt_mellinPrim_snd t _ hθ).continuousAt.continuousWithinAt

/-- A Mellin primitive is `O(θ)` on `(1, ∞)`: `|P| ≤ 2θ`. -/
theorem abs_mellinPrim_le (t : ℝ) {θ : ℝ} (hθ : 1 < θ) :
    |(mellinPrim t θ).1| ≤ 2 * θ ∧ |(mellinPrim t θ).2| ≤ 2 * θ := by
  have hθ0 : 0 ≤ θ := by linarith
  have hd : √θ / √(t ^ 2 + 1 / 4) ≤ 2 * θ := by
    have hq : (1 / 2 : ℝ) ≤ √(t ^ 2 + 1 / 4) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg t])
    have hs : √θ ≤ θ := Real.sqrt_le_iff.mpr ⟨hθ0, by nlinarith⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.sqrt_nonneg θ]
  exact ⟨by simpa using (abs_mellinPrim_comb_le t hθ0 (u := 1) (w := 0) (by norm_num)).trans hd,
    by simpa using (abs_mellinPrim_comb_le t hθ0 (u := 0) (w := 1) (by norm_num)).trans hd⟩

theorem Tb_one : Tb 1 = 1 / 2 := by
  unfold Tb profTail profTailN
  norm_num [beta_one, beta_zero]

theorem continuousOn_Tb : ContinuousOn Tb (Ioi 0) :=
  fun _ hθ => (hasDerivAt_Tb hθ).continuousAt.continuousWithinAt

/-- `T_β' · v ∈ L¹(1, ∞)` for continuous `v` with `|v| ≤ 2θ`. -/
theorem integrableOn_deriv_Tb_mul {v : ℝ → ℝ} (hvc : ContinuousOn v (Ioi 0))
    (hvb : ∀ θ, 1 < θ → |v θ| ≤ 2 * θ) : IntegrableOn (fun θ => -(1 / θ) * profTail gamma θ * v θ) (Ioi 1) := by
  have hT := Bgam_nonneg
  have hπ := pi_pos
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := fun _ hθ => mem_Ioi.mpr (lt_trans one_pos hθ)
  refine (integrableOn_of_le_inv_pow (n := 3) (K := 2 * (16 / π + Bgam * (π ^ 4 / 90)))
    ((continuousOn_deriv_Tb_Ioi_one.mul (hvc.mono hsub)).aestronglyMeasurable measurableSet_Ioi) (by norm_num)
    fun θ hθ => ?_).1
  have hθ0 : 0 < θ := by linarith
  show |-(1 / θ) * profTail gamma θ * v θ| ≤ _
  rw [abs_mul]
  calc |-(1 / θ) * profTail gamma θ| * |v θ| ≤ (16 / π + Bgam * (π ^ 4 / 90)) / θ ^ 4 * (2 * θ) :=
        mul_le_mul (abs_deriv_Tb_le_inv_pow hθ) (hvb θ hθ) (abs_nonneg _) (by positivity)
    _ = 2 * (16 / π + Bgam * (π ^ 4 / 90)) / θ ^ 3 := by field_simp

/-- **Integration by parts against a primitive** `v` of `w`: `∫ T_β w = −T_β(1)v(1) − ∫ T_β' v` on `(1, ∞)`. -/
theorem integral_Tb_mul_eq {v w : ℝ → ℝ} (hv : ∀ θ, 0 < θ → HasDerivAt v (w θ) θ)
    (hvb : ∀ θ, 1 < θ → |v θ| ≤ 2 * θ) (hwb : ∀ θ, 1 < θ → |w θ| ≤ 1) (hwc : ContinuousOn w (Ioi 0)) :
    ∫ θ in Ioi 1, Tb θ * w θ = -(Tb 1 * v 1) - ∫ θ in Ioi 1, -(1 / θ) * profTail gamma θ * v θ := by
  have hK := KPsi_nonneg
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := fun _ hθ => mem_Ioi.mpr (lt_trans one_pos hθ)
  have hvc : ContinuousOn v (Ioi 0) := fun θ hθ => (hv θ hθ).continuousAt.continuousWithinAt
  have huv : IntegrableOn (fun θ => Tb θ * w θ) (Ioi 1) :=
    (integrableOn_of_le_inv_pow (n := 4) (K := KPsi / 1440)
      (((continuousOn_Tb.mul hwc).mono hsub).aestronglyMeasurable measurableSet_Ioi) (by norm_num)
      fun θ hθ => by
        show |Tb θ * w θ| ≤ _
        rw [abs_mul]
        calc |Tb θ| * |w θ| ≤ KPsi / (1440 * θ ^ 4) * 1 :=
              mul_le_mul (abs_Tb_le hθ) (hwb θ hθ) (abs_nonneg _) (by positivity)
          _ = KPsi / 1440 / θ ^ 4 := by field_simp).1
  have h0 : Tendsto (Tb * v) (𝓝[>] 1) (𝓝 (Tb 1 * v 1)) :=
    ((continuousOn_Tb.mul hvc).continuousAt (Ioi_mem_nhds one_pos)).tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (Tb * v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun θ : ℝ => 2 * (KPsi / 1440) / θ ^ 3) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 1] with θ hθ
    have hθ0 : 0 < θ := by linarith
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    calc |Tb θ| * |v θ| ≤ KPsi / (1440 * θ ^ 4) * (2 * θ) :=
          mul_le_mul (abs_Tb_le hθ) (hvb θ hθ) (abs_nonneg _) (by positivity)
      _ = 2 * (KPsi / 1440) / θ ^ 3 := by field_simp
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (u := Tb) (v := v) (u' := fun θ => -(1 / θ) * profTail gamma θ)
    (v' := w) (fun θ (hθ : θ ∈ Ioi 1) => hasDerivAt_Tb (lt_trans one_pos hθ)) (fun θ (hθ : θ ∈ Ioi 1) => hv θ (lt_trans one_pos hθ))
    huv (integrableOn_deriv_Tb_mul hvc hvb) h0 hinf
  rw [h]; ring

/-- `V_{1/2} = |T⁺(1⁺)| + ∫_{(1,∞)} |T_β'| θ^{1/2} = 1/2 + ∫_{(1,∞)} |T_β'| θ^{1/2}`. -/
noncomputable def VHalf : ℝ := 1 / 2 + ∫ θ in Ioi 1, |-(1 / θ) * profTail gamma θ| * √θ

theorem VHalf_nonneg : 0 ≤ VHalf := by
  unfold VHalf
  have : 0 ≤ ∫ θ in Ioi 1, |-(1 / θ) * profTail gamma θ| * √θ :=
    setIntegral_nonneg measurableSet_Ioi fun θ _ => by positivity
  positivity

/-- **The rational bound** `V_{1/2} ≤ 33/10`. -/
theorem VHalf_le_rat : VHalf ≤ 33 / 10 := by unfold VHalf; linarith [V_half_le_rat]

open Cvs.Prolate.Mellin.MellinKernelSturmLiouville in
/-- **The spectral density of `T⁺` is `O(1/(t² + ¼))`**: `ρ(t) ≤ V_{1/2}²/(2π(t² + ¼))`. -/
theorem specDensity_fullTail_Psi_le (t : ℝ) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.L2a.TailLogScaleTest.logScale (fullTail Psi)) t
      ≤ VHalf ^ 2 / (2 * π * (t ^ 2 + 1 / 4)) := by
  have hF : ∀ θ ≤ 1, fullTail Psi θ = 0 := fun θ hθ => by simp [fullTail, not_lt.mpr hθ]
  have hcongr : ∀ w : ℝ → ℝ, ∫ θ in Ioi 1, fullTail Psi θ * w θ = ∫ θ in Ioi 1, Tb θ * w θ := fun w =>
    setIntegral_congr_fun measurableSet_Ioi fun θ hθ => by rw [fullTail_Psi hθ]
  have hkyb : ∀ θ, 1 < θ → |ky t θ| ≤ 1 := fun θ hθ => by
    unfold ky
    have hs : 1 ≤ √θ := Real.one_le_sqrt.mpr hθ.le
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < √θ), div_le_one (by linarith)]
    exact (abs_cos_le_one _).trans hs
  have hkysb : ∀ θ, 1 < θ → |kys t θ| ≤ 1 := fun θ hθ => by
    unfold kys
    have hs : 1 ≤ √θ := Real.one_le_sqrt.mpr hθ.le
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < √θ), div_le_one (by linarith)]
    exact (abs_sin_le_one _).trans hs
  have hkyc : ContinuousOn (ky t) (Ioi 0) := fun θ hθ => (hasDerivAt_ky hθ).continuousAt.continuousWithinAt
  have hkysc : ContinuousOn (kys t) (Ioi 0) := fun θ hθ => (hasDerivAt_kys hθ).continuousAt.continuousWithinAt
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := fun _ hθ => mem_Ioi.mpr (lt_trans one_pos hθ)
  have hint : ∀ w : ℝ → ℝ, ContinuousOn w (Ioi 0) → (∀ θ, 1 < θ → |w θ| ≤ 1) →
      IntegrableOn (fun θ => fullTail Psi θ * w θ) (Ioi 1) := fun w hwc hwb => by
    have hK := KPsi_nonneg
    refine (integrableOn_of_le_inv_pow (n := 4) (K := KPsi / 1440)
      ?_ (by norm_num) fun θ hθ => ?_).1
    · refine (((continuousOn_Tb.mul hwc).mono hsub).congr fun θ hθ => ?_).aestronglyMeasurable measurableSet_Ioi
      simp only [Pi.mul_apply, fullTail_Psi hθ]
    · rw [abs_mul]
      calc |fullTail Psi θ| * |w θ| ≤ KPsi / (1440 * θ ^ 4) * 1 :=
            mul_le_mul (abs_fullTail_Psi_le hθ) (hwb θ hθ) (abs_nonneg _) (by positivity)
        _ = KPsi / 1440 / θ ^ 4 := by field_simp
  rw [Cvs.L2a.TailLogScaleTest.specDensity_eq _ hF t (hint _ hkyc hkyb) (hint _ hkysc hkysb), hcongr, hcongr,
    integral_Tb_mul_eq (hasDerivAt_mellinPrim_fst t) (fun θ hθ => (abs_mellinPrim_le t hθ).1) hkyb hkyc,
    integral_Tb_mul_eq (hasDerivAt_mellinPrim_snd t) (fun θ hθ => (abs_mellinPrim_le t hθ).2) hkysb hkysc]
  have iP1 := integrableOn_deriv_Tb_mul (continuousOn_mellinPrim_fst t) (fun θ hθ => (abs_mellinPrim_le t hθ).1)
  have iP2 := integrableOn_deriv_Tb_mul (continuousOn_mellinPrim_snd t) (fun θ hθ => (abs_mellinPrim_le t hθ).2)
  set D := fun θ : ℝ => -(1 / θ) * profTail gamma θ with hD
  set a := -(Tb 1 * (mellinPrim t 1).1) - ∫ θ in Ioi 1, D θ * (mellinPrim t θ).1
  set b := -(Tb 1 * (mellinPrim t 1).2) - ∫ θ in Ioi 1, D θ * (mellinPrim t θ).2
  set q := t ^ 2 + 1 / 4 with hqd
  have hq : 0 < q := by positivity
  have hsq : 0 < √q := Real.sqrt_pos.mpr hq
  have hπ := pi_pos
  have hr : √(a ^ 2 + b ^ 2) ≤ VHalf / √q := by
    rcases (Real.sqrt_nonneg (a ^ 2 + b ^ 2)).lt_or_eq with hr0 | hr0
    · set r := √(a ^ 2 + b ^ 2)
      have hrr : r * r = a ^ 2 + b ^ 2 := Real.mul_self_sqrt (by positivity)
      set u := a / r; set w := b / r
      have huw : u ^ 2 + w ^ 2 = 1 := by
        simp only [u, w, div_pow]; rw [← add_div, ← hrr]; field_simp
      have hrab : r = a * u + b * w := by
        simp only [u, w]; field_simp; rw [← hrr]; ring
      have hlin : (∫ θ in Ioi 1, D θ * (mellinPrim t θ).1) * u + (∫ θ in Ioi 1, D θ * (mellinPrim t θ).2) * w
          = ∫ θ in Ioi 1, D θ * ((mellinPrim t θ).1 * u + (mellinPrim t θ).2 * w) := by
        rw [← integral_mul_const, ← integral_mul_const, ← integral_add (iP1.mul_const u) (iP2.mul_const w)]
        refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
        ring
      have iC : IntegrableOn (fun θ => D θ * ((mellinPrim t θ).1 * u + (mellinPrim t θ).2 * w)) (Ioi 1) :=
        IntegrableOn.congr_fun (f := fun θ => D θ * (mellinPrim t θ).1 * u + D θ * (mellinPrim t θ).2 * w)
          ((iP1.mul_const u).add (iP2.mul_const w)) (fun θ _ => by ring) measurableSet_Ioi
      have iV : IntegrableOn (fun θ => |D θ| * √θ / √q) (Ioi 1) := V_half_le.1.div_const _
      have hI : |∫ θ in Ioi 1, D θ * ((mellinPrim t θ).1 * u + (mellinPrim t θ).2 * w)|
          ≤ (∫ θ in Ioi 1, |D θ| * √θ) / √q := by
        refine (abs_integral_le_integral_abs).trans ?_
        rw [← integral_div]
        refine setIntegral_mono_on iC.abs iV measurableSet_Ioi fun θ (hθ : 1 < θ) => ?_
        rw [abs_mul, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (abs_mellinPrim_comb_le t (by linarith) huw) (abs_nonneg _)
      have hB := abs_mellinPrim_comb_le t zero_le_one huw
      rw [Real.sqrt_one] at hB
      have hexp : a * u + b * w = -(Tb 1 * ((mellinPrim t 1).1 * u + (mellinPrim t 1).2 * w))
          - ((∫ θ in Ioi 1, D θ * (mellinPrim t θ).1) * u + (∫ θ in Ioi 1, D θ * (mellinPrim t θ).2) * w) := by
        simp only [a, b]; ring
      rw [hlin] at hexp
      have h1 : -(Tb 1 * ((mellinPrim t 1).1 * u + (mellinPrim t 1).2 * w)) ≤ 1 / 2 * (1 / √q) := by
        rw [Tb_one]
        have := neg_abs_le ((mellinPrim t 1).1 * u + (mellinPrim t 1).2 * w)
        have := abs_le.mp hB
        nlinarith
      have h2 := neg_abs_le (∫ θ in Ioi 1, D θ * ((mellinPrim t θ).1 * u + (mellinPrim t θ).2 * w))
      rw [hrab, hexp]
      unfold VHalf
      rw [add_div, div_eq_mul_one_div (1 / 2)]
      linarith
    · rw [← hr0]; exact div_nonneg VHalf_nonneg hsq.le
  have hsq2 : a ^ 2 + b ^ 2 ≤ (VHalf / √q) ^ 2 := by
    rw [← Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + b ^ 2)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hr 2
  rw [div_pow, Real.sq_sqrt hq.le] at hsq2
  calc (a ^ 2 + b ^ 2) / (2 * π) ≤ VHalf ^ 2 / q / (2 * π) := div_le_div_of_nonneg_right hsq2 (by positivity)
    _ = VHalf ^ 2 / (2 * π * q) := by field_simp

/-! ### `C_A`: the archimedean functional of `T⁺` -/

open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)

/-- An even function integrable on `(0, ∞)` is integrable on `ℝ`. -/
theorem integrable_of_even {G : ℝ → ℝ} (hGm : AEStronglyMeasurable G volume) (hG : ∀ t, G (-t) = G t)
    (h : IntegrableOn G (Ioi 0)) : Integrable G := by
  have hH : Integrable (indicator (Ici 0) G) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (f := G)).mpr h).integrable_indicator measurableSet_Ici
  refine Integrable.mono' (hH.abs.add (hH.comp_neg.abs)) hGm (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  rcases le_total 0 t with ht | ht
  · rw [indicator_of_mem (show t ∈ Ici 0 from ht)]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · rw [indicator_of_mem (show -t ∈ Ici 0 from mem_Ici.mpr (by linarith)), hG]
    exact le_add_of_nonneg_left (abs_nonneg _)

/-- The archimedean bound `c₀ = 5.37228` from `ψ(¼) − log π ≥ −5.37228`. -/
theorem abs_archSymbol_le_of_abs_le {t : ℝ} (ht : |t| ≤ 1024) : |archSymbol t| ≤ 537228 / 100000 := by
  have hlo := (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.archSymbol_min_at_zero t).trans' (Cvs.Finite.OneModeCertificate.archSymbol_zero_bounds.1)
  have hmono := Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (t₀ := t) (t₁ := 1024) (by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2)
  have hd := abs_le.mp (DigammaAsym.abs_re_digamma_sub_log_le 1024 (by norm_num))
  have hl : Real.log (1024 / 2) = 9 * Real.log 2 := by
    rw [show (1024 / 2 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_lt_d9
  have hπ := Cvs.Moments.log_pi_bounds.1
  have hup : archSymbol 1024 ≤ 537228 / 100000 := by unfold archSymbol; rw [hl] at hd; linarith [hd.2]
  rw [abs_le]; constructor <;> linarith

/-- `|archSymbol t| ≤ log(|t|/2)` for `|t| ≥ 1024`. -/
theorem abs_archSymbol_le_log {t : ℝ} (ht : 1024 ≤ |t|) : |archSymbol t| ≤ Real.log (|t| / 2) := by
  have hlo := (Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.archSymbol_min_at_zero t).trans' (Cvs.Finite.OneModeCertificate.archSymbol_zero_bounds.1)
  have heq : archSymbol t = archSymbol |t| :=
    le_antisymm (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (by rw [sq_abs]))
      (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (by rw [sq_abs]))
  have hd := abs_le.mp (DigammaAsym.abs_re_digamma_sub_log_le |t| (by linarith))
  have hπ := Cvs.Moments.log_pi_bounds.1
  have h57 : 57 / |t| ≤ 57 / 1024 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht
  have hlog : 9 * Real.log 2 ≤ Real.log (|t| / 2) :=
    calc 9 * Real.log 2 = Real.log (2 ^ 9) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log (|t| / 2) := Real.log_le_log (by norm_num) (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hup : archSymbol t ≤ Real.log (|t| / 2) := by rw [heq]; unfold archSymbol; linarith [hd.2]
  rw [abs_le]; constructor <;> linarith

theorem archSymbol_neg (t : ℝ) : archSymbol (-t) = archSymbol t :=
  le_antisymm (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (by rw [neg_sq]))
    (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (by rw [neg_sq]))

theorem continuous_archSymbol_sq_div : Continuous fun t : ℝ => archSymbol t ^ 2 / (t ^ 2 + 1 / 4) :=
  (Cvs.WeilForm.Archimedean.ArchFormIntegrable.continuous_archSymbol.pow 2).div (by fun_prop) fun t => by positivity

/-- On `(1024, ∞)`, `a(t)²/(t² + ¼) ≤ (16/√2) t^{−3/2}`, from `log y ≤ 4y^{1/4}`. -/
theorem archSymbol_sq_div_le_tail {t : ℝ} (ht : 1024 < t) :
    archSymbol t ^ 2 / (t ^ 2 + 1 / 4) ≤ 16 / √2 * t ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h := abs_archSymbol_le_log (t := t) (by rw [abs_of_pos ht0]; exact ht.le)
  rw [abs_of_pos ht0] at h
  have hl0 : 0 ≤ Real.log (t / 2) := Real.log_nonneg (by linarith)
  have hl := Real.log_le_rpow_div (x := t / 2) (ε := 1 / 4) (by positivity) (by norm_num)
  have hsq : archSymbol t ^ 2 ≤ (4 * (t / 2) ^ (1 / 4 : ℝ)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h.trans (by linarith)) 2
  have e1 : (4 * (t / 2) ^ (1 / 4 : ℝ)) ^ 2 = 16 / √2 * t ^ (1 / 2 : ℝ) := by
    rw [mul_pow, ← rpow_natCast ((t / 2) ^ (1 / 4 : ℝ)) 2, ← rpow_mul (by positivity),
      div_rpow ht0.le (by norm_num), Real.sqrt_eq_rpow]
    norm_num; ring
  have e2 : t ^ (1 / 2 : ℝ) / t ^ 2 = t ^ (-(3 / 2 : ℝ)) := by
    rw [← rpow_natCast t 2, ← rpow_sub ht0]; norm_num
  calc archSymbol t ^ 2 / (t ^ 2 + 1 / 4) ≤ 16 / √2 * t ^ (1 / 2 : ℝ) / t ^ 2 := by
        rw [← e1]
        exact div_le_div₀ (by positivity) hsq (by positivity) (by linarith)
    _ = 16 / √2 * t ^ (-(3 / 2 : ℝ)) := by rw [mul_div_assoc, e2]

/-- `∫_ℝ 1/(t² + ¼) = 2π`. -/
theorem integral_inv_sq_add_quarter : ∫ t : ℝ, 1 / (t ^ 2 + 1 / 4) = 2 * π := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) 2
  rw [integral_univ_inv_one_add_sq] at h
  have e : (fun t : ℝ => 1 / (t ^ 2 + 1 / 4)) = fun t => 4 * (1 + (2 * t) ^ 2)⁻¹ := by
    funext t; field_simp; ring
  rw [e, integral_const_mul, h]; norm_num; ring

theorem integrable_inv_sq_add_quarter : Integrable fun t : ℝ => 1 / (t ^ 2 + 1 / 4) := by
  have e : (fun t : ℝ => 1 / (t ^ 2 + 1 / 4)) = fun t => 4 * (1 + (2 * t) ^ 2)⁻¹ := by
    funext t; field_simp; ring
  rw [e]
  exact (integrable_inv_one_add_sq.comp_mul_left' (two_ne_zero)).const_mul 4

/-- `M_a = ∫_ℝ a(t)²/(t² + ¼)`, the archimedean mass against the `T⁺` majorant. -/
noncomputable def archMaj : ℝ := ∫ t, archSymbol t ^ 2 / (t ^ 2 + 1 / 4)

/-- **`a(t)²/(t² + ¼) ∈ L¹(ℝ)`, and `M_a ≤ 2π c₀² + √2`** with `c₀ = 5.37228`. -/
theorem archMaj_le :
    Integrable (fun t : ℝ => archSymbol t ^ 2 / (t ^ 2 + 1 / 4))
      ∧ archMaj ≤ 2 * π * (537228 / 100000) ^ 2 + √2 := by
  set G := fun t : ℝ => archSymbol t ^ 2 / (t ^ 2 + 1 / 4) with hGd
  have hG : ∀ t, G (-t) = G t := fun t => by
    simp only [hGd, neg_sq, archSymbol_neg]
  have hGnn : ∀ t, 0 ≤ G t := fun t => by simp only [hGd]; positivity
  have hq := integrable_inv_sq_add_quarter
  have htail : IntegrableOn (fun t : ℝ => 16 / √2 * t ^ (-(3 / 2 : ℝ))) (Ioi 1024) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
  have hbound : ∀ t ∈ Ioi (0 : ℝ), G t ≤ (537228 / 100000) ^ 2 * (1 / (t ^ 2 + 1 / 4))
      + indicator (Ioi 1024) (fun t => 16 / √2 * t ^ (-(3 / 2 : ℝ))) t := fun t (ht : 0 < t) => by
    rcases le_or_gt t 1024 with h | h
    · rw [indicator_of_notMem (show t ∉ Ioi 1024 from not_lt.mpr h), add_zero]
      have ha := abs_archSymbol_le_of_abs_le (t := t) (by rw [abs_of_pos ht]; exact h)
      simp only [hGd]
      rw [mul_one_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
    · rw [indicator_of_mem (show t ∈ Ioi 1024 from h)]
      have := archSymbol_sq_div_le_tail h
      have : 0 ≤ (537228 / 100000 : ℝ) ^ 2 * (1 / (t ^ 2 + 1 / 4)) := by positivity
      simp only [hGd]; linarith
  have hmaj : Integrable fun t : ℝ => (537228 / 100000 : ℝ) ^ 2 * (1 / (t ^ 2 + 1 / 4))
      + indicator (Ioi 1024) (fun t => 16 / √2 * t ^ (-(3 / 2 : ℝ))) t :=
    (hq.const_mul _).add (htail.integrable_indicator measurableSet_Ioi)
  have hGi0 : IntegrableOn G (Ioi 0) :=
    Integrable.mono' hmaj.integrableOn (continuous_archSymbol_sq_div.aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGnn t)]; exact hbound t ht))
  have hGi := integrable_of_even continuous_archSymbol_sq_div.aestronglyMeasurable hG hGi0
  refine ⟨hGi, ?_⟩
  have hhalf : ∫ t in Ioi (0 : ℝ), 1 / (t ^ 2 + 1 / 4) = π := by
    have h := integral_comp_abs (f := fun t : ℝ => 1 / (t ^ 2 + 1 / 4))
    simp only [sq_abs] at h
    rw [integral_inv_sq_add_quarter] at h; linarith
  have hevenI : archMaj = 2 * ∫ t in Ioi (0 : ℝ), G t := by
    rw [← integral_comp_abs]; unfold archMaj
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    rcases le_total 0 t with ht | ht
    · simp only [abs_of_nonneg ht, hGd]
    · simp only [abs_of_nonpos ht, hGd, neg_sq, archSymbol_neg]
  have hle : ∫ t in Ioi (0 : ℝ), G t ≤ ∫ t in Ioi (0 : ℝ), ((537228 / 100000 : ℝ) ^ 2 * (1 / (t ^ 2 + 1 / 4))
      + indicator (Ioi 1024) (fun t => 16 / √2 * t ^ (-(3 / 2 : ℝ))) t) :=
    setIntegral_mono_on hGi0 hmaj.integrableOn measurableSet_Ioi hbound
  rw [integral_add (hq.const_mul _).integrableOn (htail.integrable_indicator measurableSet_Ioi).integrableOn,
    integral_const_mul, hhalf, setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi 1024 = Ioi 1024 by ext; simp only [mem_inter_iff, mem_Ioi]; constructor <;> intro h
      <;> [exact h.2; exact ⟨by linarith, h⟩],
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)] at hle
  have h32 : (1024 : ℝ) ^ (-(3 / 2 : ℝ) + 1) = 1 / 32 := by
    rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num, rpow_neg (by norm_num), ← Real.sqrt_eq_rpow,
      show (1024 : ℝ) = 32 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
  rw [h32] at hle
  have hs2 : 16 / √2 * (-(1 / 32) / (-(3 / 2) + 1)) = 1 / √2 := by field_simp; norm_num
  rw [hs2] at hle
  have hsq : 2 * (1 / √2) = √2 := by
    field_simp; rw [Real.sq_sqrt (by norm_num)]
  rw [hevenI]; nlinarith [hsq]

/-- **`C_A = (∫ a(t)² ρ_{T⁺}(t) dt)^{1/2}`**, the archimedean functional of `T⁺`. -/
noncomputable def CA : ℝ :=
  √(∫ t, archSymbol t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.L2a.TailLogScaleTest.logScale (fullTail Psi)) t)

/-- **`a² ρ_{T⁺} ∈ L¹(ℝ)` and `C_A² ≤ (V_{1/2}²/2π) M_a`.** -/
theorem CA_sq_le :
    Integrable (fun t => archSymbol t ^ 2
        * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.L2a.TailLogScaleTest.logScale (fullTail Psi)) t)
      ∧ ∫ t, archSymbol t ^ 2
          * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.L2a.TailLogScaleTest.logScale (fullTail Psi)) t
        ≤ VHalf ^ 2 / (2 * π) * archMaj := by
  obtain ⟨h2, h1⟩ := memLp_logScale_fullTail_Psi
  have hρ := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1
  have hA := archMaj_le.1
  have hπ := pi_pos
  have hmaj : Integrable fun t : ℝ => VHalf ^ 2 / (2 * π) * (archSymbol t ^ 2 / (t ^ 2 + 1 / 4)) :=
    hA.const_mul _
  have hpt : ∀ t, archSymbol t ^ 2
      * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.L2a.TailLogScaleTest.logScale (fullTail Psi)) t
      ≤ VHalf ^ 2 / (2 * π) * (archSymbol t ^ 2 / (t ^ 2 + 1 / 4)) := fun t => by
    have h := specDensity_fullTail_Psi_le t
    calc archSymbol t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.L2a.TailLogScaleTest.logScale (fullTail Psi)) t
        ≤ archSymbol t ^ 2 * (VHalf ^ 2 / (2 * π * (t ^ 2 + 1 / 4))) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = VHalf ^ 2 / (2 * π) * (archSymbol t ^ 2 / (t ^ 2 + 1 / 4)) := by field_simp
  have hi : Integrable (fun t => archSymbol t ^ 2
      * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.L2a.TailLogScaleTest.logScale (fullTail Psi)) t) :=
    hmaj.mono' ((Cvs.WeilForm.Archimedean.ArchFormIntegrable.continuous_archSymbol.pow 2).aestronglyMeasurable.mul
      hρ.aestronglyMeasurable) (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
          (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ _))]
        exact hpt t)
  refine ⟨hi, ?_⟩
  rw [archMaj, ← integral_const_mul]
  exact integral_mono hi hmaj hpt

/-- **The rational bound** `C_A ≤ 179/10`. -/
theorem CA_le_rat : CA ≤ 179 / 10 := by
  have h := CA_sq_le.2
  have hM := archMaj_le.2
  have hV := VHalf_le_rat
  have hV0 := VHalf_nonneg
  have hπ := pi_pos
  have hπ3 := pi_gt_three
  have hs2 : √2 ≤ 1415 / 1000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hX : VHalf ^ 2 / (2 * π) * archMaj ≤ (33 / 10) ^ 2 * ((537228 / 100000) ^ 2 + 1415 / 1000 / 6) := by
    have hM' : archMaj / (2 * π) ≤ (537228 / 100000) ^ 2 + 1415 / 1000 / 6 := by
      rw [div_le_iff₀ (by positivity)]
      have : √2 ≤ 1415 / 1000 / 6 * (2 * π) := by nlinarith
      nlinarith
    have hM0 : 0 ≤ archMaj := integral_nonneg fun t => by positivity
    calc VHalf ^ 2 / (2 * π) * archMaj = VHalf ^ 2 * (archMaj / (2 * π)) := by ring
      _ ≤ (33 / 10) ^ 2 * ((537228 / 100000) ^ 2 + 1415 / 1000 / 6) :=
        mul_le_mul (pow_le_pow_left₀ hV0 hV 2) hM' (by positivity) (by positivity)
  unfold CA
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩

/-! ### The functionals at a glance -/

/-- `0.101 ≤ Π₊(Ψ) ≤ 0.102`. -/
theorem piPlus_Psi_bounds : 101 / 1000 ≤ piPlus Psi ∧ piPlus Psi ≤ 102 / 1000 := by
  rw [piPlus_Psi, Real.log_mul two_ne_zero pi_ne_zero]
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have hπ := Cvs.Moments.log_pi_bounds
  constructor <;> linarith [hπ.1, hπ.2]

end Cvs.L2a.BetaProfilePoissonTail
