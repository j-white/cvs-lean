import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungDecayBeyondEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far integration-by-parts identity

For `y ≥ 3/2`, a rung `ψ = psi c g` (Cvs.L2a.AngularProlateTailPositive, Cvs.Prolate.Gram.RungGramFloorAtInfinity) and the ramp `w = sin²(π(x − 3/2))` on `[3/2, 2]`, `1` after,
`B′ + eψR = wψe` exactly, with `e = e^{icxy}`, `Q = c²(x² − 1)(y² − 1) − (c² − χ) − 2icxy`, `G = w/Q` and
`R = (pG′)′ + 2icy pG′`. Hence `∫_{3/2}^T wψe = B(T) + ∫_{3/2}^T eψR`, and `∫_{3/2}^T wψe → ∫_{3/2}^∞ eψR`.
-/

namespace Cvs.L2a.FarIntegrationByParts

open Real Set Filter Topology MeasureTheory intervalIntegral Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.RungDecayBeyondEdge

/-! ### The ramp -/

/-- The clamp of `x` to `[3/2, 2]`. -/
noncomputable def clampW (x : ℝ) : ℝ := max (3 / 2) (min x 2)

/-- The ramp `w = sin²(π(x − 3/2))` on `[3/2, 2]`, `0` before and `1` after. -/
noncomputable def wF (x : ℝ) : ℝ := Real.sin (π * (clampW x - 3 / 2)) ^ 2

/-- The derivative of the ramp, `π sin(2π(x − 3/2))` on `[3/2, 2]` and `0` outside. -/
noncomputable def wF₁ (x : ℝ) : ℝ := π * Real.sin (2 * π * (clampW x - 3 / 2))

/-- The second derivative of the ramp on `(3/2, 2) ∪ (2, ∞)`. -/
noncomputable def wF₂ (x : ℝ) : ℝ := if x ≤ 2 then 2 * π ^ 2 * Real.cos (2 * π * (x - 3 / 2)) else 0

/-- The ramp and its derivative are continuous. -/
theorem continuous_wF : Continuous wF ∧ Continuous wF₁ := by
  unfold wF wF₁ clampW; constructor <;> fun_prop

/-- On `[2, ∞)` the ramp is `1` and its derivative is `0`. -/
theorem wF_of_two_le {x : ℝ} (hx : 2 ≤ x) : wF x = 1 ∧ wF₁ x = 0 := by
  have h : clampW x = 2 := by unfold clampW; rw [min_eq_right hx]; norm_num
  unfold wF wF₁; rw [h]
  constructor
  · rw [show π * (2 - 3 / 2 : ℝ) = π / 2 by ring, Real.sin_pi_div_two]; norm_num
  · rw [show 2 * π * (2 - 3 / 2 : ℝ) = π by ring, Real.sin_pi]; ring

/-- At `3/2` the ramp and its derivative vanish. -/
theorem wF_three_halves : wF (3 / 2) = 0 ∧ wF₁ (3 / 2) = 0 := by
  have h : clampW (3 / 2) = 3 / 2 := by unfold clampW; norm_num
  unfold wF wF₁; rw [h]; simp

/-- The ramp's derivatives on `(3/2, 2) ∪ (2, ∞)`. -/
theorem hasDerivAt_wF {x : ℝ} (hx : 3 / 2 < x) (hx2 : x ≠ 2) :
    HasDerivAt wF (wF₁ x) x ∧ HasDerivAt wF₁ (wF₂ x) x := by
  rcases lt_or_gt_of_ne hx2 with hlt | hgt
  · have hev : clampW =ᶠ[𝓝 x] id := by
      filter_upwards [Ioo_mem_nhds hx hlt] with z hz
      unfold clampW; rw [min_eq_left hz.2.le, max_eq_right hz.1.le]; rfl
    have hcl : ∀ z ∈ Ioo (3 / 2 : ℝ) 2, clampW z = z := fun z hz => by
      unfold clampW; rw [min_eq_left hz.2.le, max_eq_right hz.1.le]
    have hx' : clampW x = x := hcl x ⟨hx, hlt⟩
    constructor
    · have h1 : HasDerivAt (fun z => Real.sin (π * (z - 3 / 2)) ^ 2) (wF₁ x) x := by
        have := (((hasDerivAt_id x).sub_const (3 / 2)).const_mul π).sin.pow 2
        refine this.congr_deriv ?_
        unfold wF₁; rw [hx']
        rw [show 2 * π * (x - 3 / 2) = 2 * (π * (x - 3 / 2)) by ring, Real.sin_two_mul]
        simp; ring
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      unfold wF; rw [hz]; rfl
    · have h1 : HasDerivAt (fun z => π * Real.sin (2 * π * (z - 3 / 2))) (wF₂ x) x := by
        have := ((((hasDerivAt_id x).sub_const (3 / 2)).const_mul (2 * π)).sin).const_mul π
        refine this.congr_deriv ?_
        unfold wF₂; rw [if_pos hlt.le]; simp; ring
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      unfold wF₁; rw [hz]; rfl
  · have hev : ∀ᶠ z in 𝓝 x, 2 < z := Ioi_mem_nhds hgt
    constructor
    · have h1 : HasDerivAt (fun _ => (1 : ℝ)) (wF₁ x) x := by
        rw [(wF_of_two_le hgt.le).2]; exact hasDerivAt_const x 1
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      exact (wF_of_two_le hz.le).1
    · have h1 : HasDerivAt (fun _ => (0 : ℝ)) (wF₂ x) x := by
        unfold wF₂; rw [if_neg (not_le.mpr hgt)]; exact hasDerivAt_const x 0
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      exact (wF_of_two_le hz.le).2

/-! ### The quotient `G = w/Q` and the remainder `R` -/

/-- `Q(x) = c²(x² − 1)(y² − 1) − (c² − χ) − 2icxy`. -/
noncomputable def qQ (c χ y x : ℝ) : ℂ :=
  ((c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) - (c ^ 2 - χ) : ℝ) : ℂ) - ((2 * c * x * y : ℝ) : ℂ) * I

/-- `Q′(x) = 2c²x(y² − 1) − 2icy`. -/
noncomputable def qQ₁ (c y x : ℝ) : ℂ := ((2 * c ^ 2 * x * (y ^ 2 - 1) : ℝ) : ℂ) - ((2 * c * y : ℝ) : ℂ) * I

/-- `Q″ = 2c²(y² − 1)`. -/
noncomputable def qQ₂ (c y : ℝ) : ℂ := ((2 * c ^ 2 * (y ^ 2 - 1) : ℝ) : ℂ)

/-- `G = w/Q`. -/
noncomputable def gW (w : ℝ → ℝ) (c χ y x : ℝ) : ℂ := (w x : ℂ) / qQ c χ y x

/-- `G′ = (w′Q − wQ′)/Q²`. -/
noncomputable def gW₁ (w w₁ : ℝ → ℝ) (c χ y x : ℝ) : ℂ :=
  ((w₁ x : ℂ) * qQ c χ y x - (w x : ℂ) * qQ₁ c y x) / qQ c χ y x ^ 2

/-- `G″ = ((w″Q − wQ″)Q − 2(w′Q − wQ′)Q′)/Q³`. -/
noncomputable def gW₂ (w w₁ w₂ : ℝ → ℝ) (c χ y x : ℝ) : ℂ :=
  (((w₂ x : ℂ) * qQ c χ y x - (w x : ℂ) * qQ₂ c y) * qQ c χ y x
    - 2 * ((w₁ x : ℂ) * qQ c χ y x - (w x : ℂ) * qQ₁ c y x) * qQ₁ c y x) / qQ c χ y x ^ 3

/-- `R = (pG′)′ + 2icy pG′ = 2xG′ + pG″ + 2icy pG′`. -/
noncomputable def rR (w w₁ w₂ : ℝ → ℝ) (c χ y x : ℝ) : ℂ :=
  2 * (x : ℂ) * gW₁ w w₁ c χ y x + ((pP x : ℝ) : ℂ) * gW₂ w w₁ w₂ c χ y x
    + 2 * I * ((c * y : ℝ) : ℂ) * ((pP x : ℝ) : ℂ) * gW₁ w w₁ c χ y x

/-- The phase `e = e^{icxy}`. -/
noncomputable def eF (c y x : ℝ) : ℂ := cexp (((c * y * x : ℝ) : ℂ) * I)

/-- The boundary term `B = e(Gu − p(G′ + icyG)ψ)`, with `u = pψ′`. -/
noncomputable def bB (w w₁ : ℝ → ℝ) (c χ : ℝ) (g : ℝ → ℝ) (y x : ℝ) : ℂ :=
  eF c y x * (gW w c χ y x * (rungU c g x : ℂ)
    - ((pP x : ℝ) : ℂ) * (gW₁ w w₁ c χ y x + I * ((c * y : ℝ) : ℂ) * gW w c χ y x) * (psi c g x : ℂ))

/-- The real part of `Q`. -/
theorem qQ_re (c χ y x : ℝ) : (qQ c χ y x).re = c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) - (c ^ 2 - χ) := by
  simp only [qQ, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

/-- `Q ≠ 0` for `x, y ≥ 3/2`. -/
theorem qQ_ne_zero {c χ y x : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hx : 3 / 2 ≤ x) (hy : 3 / 2 ≤ y) :
    qQ c χ y x ≠ 0 := by
  intro h
  have h1 := qQ_re c χ y x
  rw [h, Complex.zero_re] at h1
  have hx2 : 5 / 4 ≤ x ^ 2 - 1 := by nlinarith
  have hy2 : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have : 25 / 16 ≤ (x ^ 2 - 1) * (y ^ 2 - 1) := by nlinarith
  nlinarith [sq_pos_of_pos hc]

/-- `|Q| ≥ (c²(y² − 1)/2)·x²` for `x ≥ 2`, `y ≥ 3/2`. -/
theorem norm_qQ_ge {c χ y x : ℝ} (hχ : 0 ≤ χ) (hx : 2 ≤ x) (hy : 3 / 2 ≤ y) :
    c ^ 2 * (y ^ 2 - 1) / 2 * x ^ 2 ≤ ‖qQ c χ y x‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [qQ_re]
  have hy2 : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have hx2 : 1 ≤ x ^ 2 / 2 - 1 := by nlinarith
  have : 1 ≤ (y ^ 2 - 1) * (x ^ 2 / 2 - 1) := by nlinarith
  nlinarith [sq_nonneg c]

/-- `|Q′| ≤ (2c²(y² − 1) + 2cy)·x` for `x ≥ 1`. -/
theorem norm_qQ₁_le {c y x : ℝ} (hc : 0 < c) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    ‖qQ₁ c y x‖ ≤ (2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y) * x := by
  unfold qQ₁
  have hy2 : 0 ≤ y ^ 2 - 1 := by nlinarith
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg c, mul_pos hc (by linarith : (0:ℝ) < y)]

/-- `Q′` is the derivative of `Q`. -/
theorem hasDerivAt_qQ (c χ y x : ℝ) : HasDerivAt (qQ c χ y) (qQ₁ c y x) x := by
  have ha : HasDerivAt (fun x : ℝ => c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) - (c ^ 2 - χ))
      (2 * c ^ 2 * x * (y ^ 2 - 1)) x := by
    have := ((((hasDerivAt_pow 2 x).sub_const 1).const_mul (c ^ 2)).mul_const (y ^ 2 - 1)).sub_const (c ^ 2 - χ)
    refine this.congr_deriv ?_; push_cast; ring
  have hb : HasDerivAt (fun x : ℝ => 2 * c * x * y) (2 * c * y) x := by
    have := ((hasDerivAt_id x).const_mul (2 * c)).mul_const y
    refine this.congr_deriv ?_; simp
  exact (ha.ofReal_comp.sub (hb.ofReal_comp.mul_const I))

/-- `Q″` is the derivative of `Q′`. -/
theorem hasDerivAt_qQ₁ (c y x : ℝ) : HasDerivAt (qQ₁ c y) (qQ₂ c y) x := by
  have ha : HasDerivAt (fun x : ℝ => 2 * c ^ 2 * x * (y ^ 2 - 1)) (2 * c ^ 2 * (y ^ 2 - 1)) x := by
    have := ((hasDerivAt_id x).const_mul (2 * c ^ 2)).mul_const (y ^ 2 - 1)
    refine this.congr_deriv ?_; simp
  have := ha.ofReal_comp.sub ((hasDerivAt_const x (((2 * c * y : ℝ) : ℂ))).mul_const I)
  unfold qQ₁ qQ₂; refine this.congr_deriv ?_; simp

/-- `G′` is the derivative of `G` where `w` is differentiable and `Q ≠ 0`. -/
theorem hasDerivAt_gW {w w₁ : ℝ → ℝ} {c χ y x : ℝ} (hw : HasDerivAt w (w₁ x) x) (hQ : qQ c χ y x ≠ 0) :
    HasDerivAt (gW w c χ y) (gW₁ w w₁ c χ y x) x :=
  hw.ofReal_comp.div (hasDerivAt_qQ c χ y x) hQ

/-- `G″` is the derivative of `G′` where `w′` is differentiable and `Q ≠ 0`. -/
theorem hasDerivAt_gW₁ {w w₁ w₂ : ℝ → ℝ} {c χ y x : ℝ} (hw : HasDerivAt w (w₁ x) x)
    (hw₁ : HasDerivAt w₁ (w₂ x) x) (hQ : qQ c χ y x ≠ 0) :
    HasDerivAt (gW₁ w w₁ c χ y) (gW₂ w w₁ w₂ c χ y x) x := by
  have hN := (hw₁.ofReal_comp.mul (hasDerivAt_qQ c χ y x)).sub (hw.ofReal_comp.mul (hasDerivAt_qQ₁ c y x))
  have := hN.div ((hasDerivAt_qQ c χ y x).pow 2) (pow_ne_zero 2 hQ)
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  unfold gW₂; field_simp; ring

/-- The phase is differentiable with `e′ = icy e`. -/
theorem hasDerivAt_eF (c y x : ℝ) : HasDerivAt (eF c y) (((c * y : ℝ) : ℂ) * I * eF c y x) x := by
  have := ((((hasDerivAt_id x).const_mul (c * y)).ofReal_comp).mul_const I).cexp
  unfold eF; refine this.congr_deriv ?_; simp; ring

/-! ### The exact identity -/

/-- **The exact identity** `B′ + eψR = wψe` at any `x > 1` where `w, w′` are differentiable and `Q ≠ 0`. -/
theorem hasDerivAt_bB {g g₁ g₂ w w₁ w₂ : ℝ → ℝ} {c χ y x : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hx : 1 < x) (hw : HasDerivAt w (w₁ x) x) (hw₁ : HasDerivAt w₁ (w₂ x) x) (hQ : qQ c χ y x ≠ 0) :
    HasDerivAt (bB w w₁ c χ g y)
      ((w x : ℂ) * (psi c g x : ℂ) * eF c y x - eF c y x * (psi c g x : ℂ) * rR w w₁ w₂ c χ y x) x := by
  obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  have hψ' := (hψ x hx).ofReal_comp
  have hu' := (hu x).ofReal_comp
  have hp' : HasDerivAt (fun x : ℝ => ((pP x : ℝ) : ℂ)) (((2 * x : ℝ)) : ℂ) x := by
    have := (hasDerivAt_pow 2 x).sub_const 1
    exact (this.congr_deriv (by push_cast; ring)).ofReal_comp
  have hG := hasDerivAt_gW (c := c) (χ := χ) (y := y) hw hQ
  have hG₁ := hasDerivAt_gW₁ (c := c) (χ := χ) (y := y) hw hw₁ hQ
  have := (hasDerivAt_eF c y x).mul ((hG.mul hu').sub
    ((hp'.mul (hG₁.add (hG.const_mul (I * ((c * y : ℝ) : ℂ))))).mul hψ'))
  refine this.congr_deriv ?_
  have hp0 : ((pP x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pP_pos hx).ne'
  have hd : ((pP x : ℝ) : ℂ) * ((rungU c g x / pP x : ℝ) : ℂ) = (rungU c g x : ℂ) := by
    push_cast; field_simp
  have hwQ : (w x : ℂ) = qQ c χ y x * gW w c χ y x := by unfold gW; field_simp
  have hQe : qQ c χ y x = (c : ℂ) ^ 2 * ((x : ℂ) ^ 2 - 1) * ((y : ℂ) ^ 2 - 1) - ((c : ℂ) ^ 2 - χ)
      - 2 * (c : ℂ) * x * y * I := by unfold qQ; push_cast; ring
  unfold rR
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  set G := gW w c χ y x
  set G₁ := gW₁ w w₁ c χ y x
  set G₂ := gW₂ w w₁ w₂ c χ y x
  set e := eF c y x
  set ψ := (psi c g x : ℂ)
  set u := (rungU c g x : ℂ)
  set ψd := ((rungU c g x / pP x : ℝ) : ℂ)
  set Q := qQ c χ y x
  unfold pP at hd ⊢; unfold qP
  push_cast at hd ⊢
  linear_combination (-(e * (G₁ + I * (c * y) * G))) * hd - (ψ * e) * hwQ - (e * G * ψ) * hQe
    - ((c * y) ^ 2 * ((x : ℂ) ^ 2 - 1) * e * G * ψ) * I_sq

/-! ### Continuity -/

/-- `Q` and `Q′` are continuous. -/
theorem continuous_qQ (c χ y : ℝ) : Continuous (qQ c χ y) ∧ Continuous (qQ₁ c y) :=
  ⟨continuous_iff_continuousAt.2 fun x => (hasDerivAt_qQ c χ y x).continuousAt,
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_qQ₁ c y x).continuousAt⟩

/-- `G`, `G′` and `R` are continuous where `Q ≠ 0`, for continuous `w, w′, w″`. -/
theorem continuousAt_gW_rR {w w₁ w₂ : ℝ → ℝ} {c χ y x : ℝ} (hw : Continuous w) (hw₁ : Continuous w₁)
    (hw₂ : Continuous w₂) (hQ : qQ c χ y x ≠ 0) :
    ContinuousAt (gW w c χ y) x ∧ ContinuousAt (gW₁ w w₁ c χ y) x ∧ ContinuousAt (rR w w₁ w₂ c χ y) x := by
  obtain ⟨hQc, hQ₁c⟩ := continuous_qQ c χ y
  have cw := (continuous_ofReal.comp hw).continuousAt (x := x)
  have cw₁ := (continuous_ofReal.comp hw₁).continuousAt (x := x)
  have cw₂ := (continuous_ofReal.comp hw₂).continuousAt (x := x)
  have cQ := hQc.continuousAt (x := x)
  have cQ₁ := hQ₁c.continuousAt (x := x)
  have hG : ContinuousAt (gW w c χ y) x := cw.div cQ hQ
  have hG₁ : ContinuousAt (gW₁ w w₁ c χ y) x :=
    ((cw₁.mul cQ).sub (cw.mul cQ₁)).div (cQ.pow 2) (pow_ne_zero 2 hQ)
  have hG₂ : ContinuousAt (gW₂ w w₁ w₂ c χ y) x :=
    ((((cw₂.mul cQ).sub (cw.mul continuousAt_const)).mul cQ).sub
      ((continuousAt_const.mul ((cw₁.mul cQ).sub (cw.mul cQ₁))).mul cQ₁)).div (cQ.pow 3) (pow_ne_zero 3 hQ)
  refine ⟨hG, hG₁, ?_⟩
  have hp : ContinuousAt (fun x : ℝ => ((pP x : ℝ) : ℂ)) x := by unfold pP; fun_prop
  have hx : ContinuousAt (fun x : ℝ => (x : ℂ)) x := by fun_prop
  exact ((continuousAt_const.mul hx).mul hG₁).add (hp.mul hG₂) |>.add ((continuousAt_const.mul hp).mul hG₁)

/-- The phase is continuous with modulus one. -/
theorem continuous_eF (c y : ℝ) : Continuous (eF c y) ∧ ∀ x, ‖eF c y x‖ = 1 :=
  ⟨by unfold eF; fun_prop, fun x => by unfold eF; exact Complex.norm_exp_ofReal_mul_I _⟩

/-! ### Decay on `[2, ∞)` -/

/-- The scalar bound behind `|R| ≲ 1/x`. -/
theorem rR_aux {x m A p k E F κ : ℝ} (hx : 1 ≤ x) (hk : 0 < k) (hm : k * x ^ 2 ≤ m) (hA0 : 0 ≤ A)
    (hA : A ≤ E * x) (hp : p ≤ x ^ 2) (hF : 0 ≤ F) (hκ : 0 ≤ κ) :
    2 * x * (A / m ^ 2) + p * ((F * m + 2 * A ^ 2) / m ^ 3) + 2 * κ * p * (A / m ^ 2)
      ≤ ((2 * E + F) / k ^ 2 + 2 * E ^ 2 / k ^ 3 + 2 * κ * E / k ^ 2) / x := by
  have hx0 : 0 < x := by linarith
  have hkx : 0 < k * x ^ 2 := by positivity
  have hm0 : 0 < m := lt_of_lt_of_le hkx hm
  have hE : 0 ≤ E := le_of_not_gt fun h => by nlinarith
  have hm2 : (k * x ^ 2) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hkx.le hm 2
  have hm3 : (k * x ^ 2) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ hkx.le hm 3
  have h1 : A / m ^ 2 ≤ E * x / (k * x ^ 2) ^ 2 := div_le_div₀ (by positivity) hA (by positivity) hm2
  have h2 : F / m ^ 2 ≤ F / (k * x ^ 2) ^ 2 := div_le_div_of_nonneg_left hF (by positivity) hm2
  have h3 : A ^ 2 / m ^ 3 ≤ (E * x) ^ 2 / (k * x ^ 2) ^ 3 :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ hA0 hA 2) (by positivity) hm3
  have e1 : (F * m + 2 * A ^ 2) / m ^ 3 = F / m ^ 2 + 2 * (A ^ 2 / m ^ 3) := by field_simp
  have hG2 : 0 ≤ F / m ^ 2 + 2 * (A ^ 2 / m ^ 3) := by positivity
  have hxx : x ≤ x ^ 2 := by nlinarith
  calc 2 * x * (A / m ^ 2) + p * ((F * m + 2 * A ^ 2) / m ^ 3) + 2 * κ * p * (A / m ^ 2)
      ≤ 2 * x * (E * x / (k * x ^ 2) ^ 2) + x ^ 2 * (F / (k * x ^ 2) ^ 2 + 2 * ((E * x) ^ 2 / (k * x ^ 2) ^ 3))
          + 2 * κ * x ^ 2 * (E * x / (k * x ^ 2) ^ 2) := by
        rw [e1]
        have := mul_le_mul hp (add_le_add h2 (mul_le_mul_of_nonneg_left h3 (by norm_num))) hG2 (by positivity)
        have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * x)
        have h5 := mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 2 * κ)) h1
          (by positivity) (by positivity)
        linarith
    _ = ((2 * E + F) / k ^ 2 + 2 * E ^ 2 / k ^ 3) / x ^ 2 + 2 * κ * E / k ^ 2 / x := by
        field_simp; ring
    _ ≤ ((2 * E + F) / k ^ 2 + 2 * E ^ 2 / k ^ 3) / x + 2 * κ * E / k ^ 2 / x := by
        gcongr
    _ = ((2 * E + F) / k ^ 2 + 2 * E ^ 2 / k ^ 3 + 2 * κ * E / k ^ 2) / x := by ring

/-- The scalar bound behind `|B| ≲ 1/x`. -/
theorem bB_aux {x m A p k E κ U Ψ u ψ : ℝ} (hx : 1 ≤ x) (hk : 0 < k) (hm : k * x ^ 2 ≤ m) (hA0 : 0 ≤ A)
    (hA : A ≤ E * x) (hp : p ≤ x ^ 2) (hκ : 0 ≤ κ) (hu0 : 0 ≤ u) (hu : u ≤ U * x)
    (hψ0 : 0 ≤ ψ) (hψ : ψ ≤ Ψ / x) :
    (1 / m) * u + p * (A / m ^ 2 + κ * (1 / m)) * ψ ≤ (U / k + E * Ψ / k ^ 2 + κ * Ψ / k) / x := by
  have hx0 : 0 < x := by linarith
  have hkx : 0 < k * x ^ 2 := by positivity
  have hm0 : 0 < m := lt_of_lt_of_le hkx hm
  have hE : 0 ≤ E := le_of_not_gt fun h => by nlinarith
  have hΨ : 0 ≤ Ψ := le_of_not_gt fun h => by
    have := div_neg_of_neg_of_pos h hx0
    linarith [hψ0.trans hψ]
  have hm2 : (k * x ^ 2) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hkx.le hm 2
  have h1 : A / m ^ 2 ≤ E * x / (k * x ^ 2) ^ 2 := div_le_div₀ (by positivity) hA (by positivity) hm2
  have h0 : 1 / m ≤ 1 / (k * x ^ 2) := one_div_le_one_div_of_le hkx hm
  have hxx : x ≤ x ^ 2 := by nlinarith
  calc (1 / m) * u + p * (A / m ^ 2 + κ * (1 / m)) * ψ
      ≤ (1 / (k * x ^ 2)) * (U * x) + x ^ 2 * (E * x / (k * x ^ 2) ^ 2 + κ * (1 / (k * x ^ 2))) * (Ψ / x) := by
        have ha := mul_le_mul h0 hu hu0 (by positivity)
        have hb : A / m ^ 2 + κ * (1 / m) ≤ E * x / (k * x ^ 2) ^ 2 + κ * (1 / (k * x ^ 2)) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h0 hκ)
        have hc := mul_le_mul (mul_le_mul hp hb (by positivity) (by positivity)) hψ hψ0 (by positivity)
        linarith
    _ = (U / k + κ * Ψ / k) / x + E * Ψ / k ^ 2 / x ^ 2 := by field_simp; ring
    _ ≤ (U / k + κ * Ψ / k) / x + E * Ψ / k ^ 2 / x := by gcongr
    _ = (U / k + E * Ψ / k ^ 2 + κ * Ψ / k) / x := by ring

/-- With the constant ramp, `|R| ≲ 1/x` on `[2, ∞)`. -/
theorem norm_rR_one_le {c χ y : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hy : 3 / 2 ≤ y) :
    ∃ K, ∀ x, 2 ≤ x → ‖rR (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x‖ ≤ K / x := by
  refine ⟨(2 * (2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y) + 2 * c ^ 2 * (y ^ 2 - 1)) / (c ^ 2 * (y ^ 2 - 1) / 2) ^ 2
    + 2 * (2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y) ^ 2 / (c ^ 2 * (y ^ 2 - 1) / 2) ^ 3
    + 2 * (c * y) * (2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y) / (c ^ 2 * (y ^ 2 - 1) / 2) ^ 2, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hy2 : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have hk : 0 < c ^ 2 * (y ^ 2 - 1) / 2 := by positivity
  have hm := norm_qQ_ge (c := c) hχ hx hy
  have hA := norm_qQ₁_le hc (x := x) (by linarith) (by linarith : (1 : ℝ) ≤ y)
  have hF : ‖qQ₂ c y‖ = 2 * c ^ 2 * (y ^ 2 - 1) := by
    unfold qQ₂; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp0 : 0 ≤ pP x := (pP_pos (by linarith)).le
  have hp : pP x ≤ x ^ 2 := by unfold pP; linarith
  set Q := qQ c χ y x
  set Q₁ := qQ₁ c y x
  have hQ0 : Q ≠ 0 := qQ_ne_zero hc hχ (by linarith) hy
  have hG₁ : ‖gW₁ (fun _ => 1) (fun _ => 0) c χ y x‖ = ‖Q₁‖ / ‖Q‖ ^ 2 := by
    simp [gW₁, Q, Q₁, norm_pow]
  have hG₂ : ‖gW₂ (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x‖
      ≤ (2 * c ^ 2 * (y ^ 2 - 1) * ‖Q‖ + 2 * ‖Q₁‖ ^ 2) / ‖Q‖ ^ 3 := by
    unfold gW₂
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, zero_sub]
    rw [norm_div, norm_pow]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_neg, hF, norm_mul, norm_mul, norm_neg, Complex.norm_two]
    nlinarith [norm_nonneg Q₁]
  have hR : ‖rR (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x‖
      ≤ 2 * x * ‖gW₁ (fun _ => 1) (fun _ => 0) c χ y x‖
        + pP x * ‖gW₂ (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x‖
        + 2 * (c * y) * pP x * ‖gW₁ (fun _ => 1) (fun _ => 0) c χ y x‖ := by
    unfold rR
    refine (norm_add₃_le).trans (le_of_eq ?_)
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, Complex.norm_two,
      abs_of_nonneg hx0.le, abs_of_nonneg hp0, abs_of_pos hc, abs_of_pos (by linarith : (0 : ℝ) < y)]
    ring
  refine hR.trans ?_
  rw [hG₁]
  refine le_trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hG₂ hp0)) le_rfl) ?_
  exact rR_aux (by linarith) hk hm (norm_nonneg _) hA hp (by positivity) (by positivity)

/-- With the constant ramp, the boundary term decays: `|B| ≲ 1/x` on `[2, ∞)`. -/
theorem norm_bB_one_le {g g₁ g₂ : ℝ → ℝ} {c χ y : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c) (hχ : 0 ≤ χ) (hy : 3 / 2 ≤ y) :
    ∃ K, ∀ x, 2 ≤ x → ‖bB (fun _ => 1) (fun _ => 0) c χ g y x‖ ≤ K / x := by
  set Ψ := |g 1 + g (-1)| / c + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / c ^ 2
  set U := 2 * |g 1 + g (-1)| + (|g 1 + g₁ 1 + (g (-1) - g₁ (-1))| + ∫ s in (-1 : ℝ)..1, 2 * |g₁ s| + |g₂ s|) / c
  set k := c ^ 2 * (y ^ 2 - 1) / 2
  set E := 2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y
  refine ⟨U / k + E * Ψ / k ^ 2 + (c * y) * Ψ / k, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hy2 : 5 / 4 ≤ y ^ 2 - 1 := by nlinarith
  have hk : 0 < k := by positivity
  have hm := norm_qQ_ge (c := c) hχ hx hy
  have hA := norm_qQ₁_le hc (x := x) (by linarith) (by linarith : (1 : ℝ) ≤ y)
  have hp0 : 0 ≤ pP x := (pP_pos (by linarith)).le
  have hp : pP x ≤ x ^ 2 := by unfold pP; linarith
  have hψ := abs_psi_le hg hg₁ hg₂c hc (ξ := x) (by linarith)
  have hu := abs_rungU_le hg hg₁ hg₂c hc (ξ := x) (by linarith)
  set Q := qQ c χ y x
  set Q₁ := qQ₁ c y x
  have hG : ‖gW (fun _ => 1) c χ y x‖ = 1 / ‖Q‖ := by simp [gW, Q]
  have hG₁ : ‖gW₁ (fun _ => 1) (fun _ => 0) c χ y x‖ = ‖Q₁‖ / ‖Q‖ ^ 2 := by
    simp [gW₁, Q, Q₁, norm_pow]
  have hcy : 0 ≤ c * y := by have : 0 < y := by linarith
                             positivity
  have hB : ‖bB (fun _ => 1) (fun _ => 0) c χ g y x‖
      ≤ ‖gW (fun _ => 1) c χ y x‖ * |rungU c g x|
        + pP x * (‖gW₁ (fun _ => 1) (fun _ => 0) c χ y x‖ + (c * y) * ‖gW (fun _ => 1) c χ y x‖)
          * |psi c g x| := by
    unfold bB
    rw [norm_mul, (continuous_eF c y).2, one_mul]
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    gcongr
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul, abs_of_pos hc,
      abs_of_pos (by linarith : (0 : ℝ) < y), le_refl]
  refine hB.trans ?_
  rw [hG, hG₁]
  exact bB_aux (by linarith) hk hm (norm_nonneg _) hA hp hcy (abs_nonneg _) hu (abs_nonneg _) hψ

/-! ### The ramp's remainder and the far identity -/

/-- On `[2, ∞)` the ramp's boundary term is the constant ramp's. -/
theorem bB_wF_eq_of_two_le {c χ y x : ℝ} {g : ℝ → ℝ} (hx : 2 ≤ x) :
    bB wF wF₁ c χ g y x = bB (fun _ => 1) (fun _ => 0) c χ g y x := by
  unfold bB gW gW₁; rw [(wF_of_two_le hx).1, (wF_of_two_le hx).2]

/-- On `(2, ∞)` the ramp's remainder is the constant ramp's. -/
theorem rR_wF_eq_of_two_lt {c χ y x : ℝ} (hx : 2 < x) :
    rR wF wF₁ wF₂ c χ y x = rR (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x := by
  unfold rR gW₁ gW₂ wF₂; rw [(wF_of_two_le hx.le).1, (wF_of_two_le hx.le).2, if_neg (not_le.mpr hx)]

/-- On `(−∞, 2]` the ramp's remainder uses the smooth second derivative `2π² cos(2π(x − 3/2))`. -/
theorem rR_wF_eq_of_le_two {c χ y x : ℝ} (hx : x ≤ 2) :
    rR wF wF₁ wF₂ c χ y x = rR wF wF₁ (fun x => 2 * π ^ 2 * Real.cos (2 * π * (x - 3 / 2))) c χ y x := by
  unfold rR gW₂ wF₂; rw [if_pos hx]

/-- **`eψR` is integrable on `(3/2, ∞)`.** -/
theorem integrableOn_eψR {g g₁ g₂ : ℝ → ℝ} {c χ y : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hy : 3 / 2 ≤ y) :
    IntegrableOn (fun x => eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x) (Ioi (3 / 2)) := by
  obtain ⟨-, -, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have heψ : Continuous (fun x => eF c y x * (psi c g x : ℂ)) :=
    (continuous_eF c y).1.mul (continuous_ofReal.comp hψc)
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (3 / 2 : ℝ) ≤ 2)]
  refine IntegrableOn.union ?_ ?_
  · have h1 : ContinuousOn (fun x => eF c y x * (psi c g x : ℂ)
        * rR wF wF₁ (fun x => 2 * π ^ 2 * Real.cos (2 * π * (x - 3 / 2))) c χ y x) (Icc (3 / 2) 2) :=
      fun x hx => (heψ.continuousAt.mul (continuousAt_gW_rR continuous_wF.1 continuous_wF.2 (by fun_prop)
        (qQ_ne_zero hc hχ hx.1 hy)).2.2).continuousWithinAt
    have h2 : ContinuousOn (fun x => eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x) (Icc (3 / 2) 2) :=
      h1.congr fun x hx => by simp only [rR_wF_eq_of_le_two hx.2]
    exact h2.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · obtain ⟨K, hK⟩ := norm_rR_one_le hc hχ hy
    have h1 : ContinuousOn (fun x => eF c y x * (psi c g x : ℂ)
        * rR (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x) (Ioi 2) :=
      fun x hx => (heψ.continuousAt.mul (continuousAt_gW_rR continuous_const continuous_const continuous_const
        (qQ_ne_zero hc hχ (by linarith [mem_Ioi.mp hx]) hy)).2.2).continuousWithinAt
    have h2 : ContinuousOn (fun x => eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x) (Ioi 2) :=
      h1.congr fun x hx => by simp only [rR_wF_eq_of_two_lt (mem_Ioi.mp hx)]
    set Ψ := |g 1 + g (-1)| / c + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / c ^ 2
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 2)).const_mul (Ψ * K)) (h2.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx2 : 2 < x := hx
    have hx0 : 0 < x := by linarith
    have hψ := abs_psi_le hg hg₁ hg₂c hc (ξ := x) (by linarith)
    have hR := hK x hx2.le
    rw [rR_wF_eq_of_two_lt hx2, norm_mul, norm_mul, (continuous_eF c y).2, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.rpow_neg hx0.le, Real.rpow_two]
    calc |psi c g x| * ‖rR (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y x‖ ≤ (Ψ / x) * (K / x) :=
          mul_le_mul hψ hR (norm_nonneg _) ((abs_nonneg _).trans hψ)
      _ = Ψ * K * (x ^ 2)⁻¹ := by field_simp

/-- **The far identity on `[3/2, T]`**: `∫_{3/2}^T wψe = B(T) + ∫_{3/2}^T eψR`. -/
theorem ibp_far_Icc {g g₁ g₂ : ℝ → ℝ} {c χ y T : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hy : 3 / 2 ≤ y) (hT : 3 / 2 ≤ T) :
    ∫ x in (3 / 2 : ℝ)..T, (wF x : ℂ) * (psi c g x : ℂ) * eF c y x
      = bB wF wF₁ c χ g y T + ∫ x in (3 / 2 : ℝ)..T, eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x := by
  obtain ⟨-, -, hψc, huc⟩ := rung_system hg hg₁ hg₂c hang
  have hR : IntervalIntegrable (fun x => eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x) volume (3 / 2) T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
      ((integrableOn_eψR hg hg₁ hg₂c hang hc hχ hy).mono_set Ioc_subset_Ioi_self)
  have hL : IntervalIntegrable (fun x => (wF x : ℂ) * (psi c g x : ℂ) * eF c y x) volume (3 / 2) T :=
    (((continuous_ofReal.comp continuous_wF.1).mul (continuous_ofReal.comp hψc)).mul
      (continuous_eF c y).1).intervalIntegrable _ _
  have hB0 : bB wF wF₁ c χ g y (3 / 2) = 0 := by
    unfold bB gW gW₁; rw [wF_three_halves.1, wF_three_halves.2]; simp
  have hp : Continuous (fun x : ℝ => ((pP x : ℝ) : ℂ)) := by unfold pP; fun_prop
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le (bB wF wF₁ c χ g y)
    (fun x => (wF x : ℂ) * (psi c g x : ℂ) * eF c y x - eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x)
    hT (countable_singleton 2) ?_ ?_ (hL.sub hR)
  · rw [intervalIntegral.integral_sub hL hR, hB0, sub_zero] at hftc
    linear_combination hftc
  · intro x hx
    have h := continuousAt_gW_rR (w₂ := fun _ => 0) continuous_wF.1 continuous_wF.2 continuous_const
      (qQ_ne_zero hc hχ hx.1 hy)
    unfold bB
    exact ((continuous_eF c y).1.continuousAt.mul ((h.1.mul (continuous_ofReal.comp huc).continuousAt).sub
      ((hp.continuousAt.mul (h.2.1.add (continuousAt_const.mul h.1))).mul
        (continuous_ofReal.comp hψc).continuousAt))).continuousWithinAt
  · intro x hx
    have hx1 : 3 / 2 < x := hx.1.1
    have hx2 : x ≠ 2 := hx.2
    obtain ⟨hw, hw₁⟩ := hasDerivAt_wF hx1 hx2
    exact hasDerivAt_bB hg hg₁ hg₂c hang (by linarith) hw hw₁ (qQ_ne_zero hc hχ hx1.le hy)

/-- **The far integration-by-parts identity**: for `y ≥ 3/2`, `∫_{3/2}^T wψe^{icxy} dx → ∫_{3/2}^∞ e^{icxy}ψR dx`
as `T → ∞`, the right side converging absolutely. -/
theorem ibp_far {g g₁ g₂ : ℝ → ℝ} {c χ y : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 ≤ χ) (hy : 3 / 2 ≤ y) :
    IntegrableOn (fun x => eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x) (Ioi (3 / 2))
      ∧ Tendsto (fun T => ∫ x in (3 / 2 : ℝ)..T, (wF x : ℂ) * (psi c g x : ℂ) * eF c y x) atTop
          (𝓝 (∫ x in Ioi (3 / 2 : ℝ), eF c y x * (psi c g x : ℂ) * rR wF wF₁ wF₂ c χ y x)) := by
  have hI := integrableOn_eψR hg hg₁ hg₂c hang hc hχ hy
  refine ⟨hI, ?_⟩
  obtain ⟨K, hK⟩ := norm_bB_one_le hg hg₁ hg₂c hc hχ hy
  have hB : Tendsto (fun T => bB wF wF₁ c χ g y T) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T : ℝ => K / T) ?_ (tendsto_const_nhds.div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop 2] with T hT
    rw [bB_wF_eq_of_two_le hT]; exact hK T hT
  have h := hB.add (intervalIntegral_tendsto_integral_Ioi (3 / 2) hI tendsto_id)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (3 / 2)] with T hT
  exact (ibp_far_Icc hg hg₁ hg₂c hang hc hχ hy hT).symm

end Cvs.L2a.FarIntegrationByParts
