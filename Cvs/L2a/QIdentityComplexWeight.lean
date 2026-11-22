import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityRealWeight
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Q-identity with a complex `C²` weight, and its atoms

For a complex weight `w` with derivatives `w₁, w₂` on `[α, β] ⊆ (1, ∞)` and `c, y > 0`: `∫_α^β wψe = ∫_α^β eψR + [B]_α^β`
with `G = w/Q`, `R = (pG′)′ + 2icy pG′ = A₁/Q + A₂/Q² + A₃/Q³`, `A₁ = (2x + 2icyp)w′ + pw″`,
`A₂ = −((2x + 2icyp)Q′ + pQ″)w − 2pQ′w′`, `A₃ = 2pQ′²w`; the atoms and `R` are bounded term by term.
-/

namespace Cvs.L2a.QIdentityComplexWeight

open Real Set Filter Topology MeasureTheory intervalIntegral Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts

/-! ### The complex-weight quotient, remainder and boundary term -/

/-- `G = w/Q` for a complex weight `w`. -/
noncomputable def gWc (w : ℝ → ℂ) (c χ y x : ℝ) : ℂ := w x / qQ c χ y x

/-- `G′ = (w′Q − wQ′)/Q²`. -/
noncomputable def gWc₁ (w w₁ : ℝ → ℂ) (c χ y x : ℝ) : ℂ :=
  (w₁ x * qQ c χ y x - w x * qQ₁ c y x) / qQ c χ y x ^ 2

/-- `G″ = ((w″Q − wQ″)Q − 2(w′Q − wQ′)Q′)/Q³`. -/
noncomputable def gWc₂ (w w₁ w₂ : ℝ → ℂ) (c χ y x : ℝ) : ℂ :=
  ((w₂ x * qQ c χ y x - w x * qQ₂ c y) * qQ c χ y x
    - 2 * (w₁ x * qQ c χ y x - w x * qQ₁ c y x) * qQ₁ c y x) / qQ c χ y x ^ 3

/-- `R = (pG′)′ + 2icy pG′ = 2xG′ + pG″ + 2icy pG′`. -/
noncomputable def rRc (w w₁ w₂ : ℝ → ℂ) (c χ y x : ℝ) : ℂ :=
  2 * (x : ℂ) * gWc₁ w w₁ c χ y x + ((pP x : ℝ) : ℂ) * gWc₂ w w₁ w₂ c χ y x
    + 2 * I * ((c * y : ℝ) : ℂ) * ((pP x : ℝ) : ℂ) * gWc₁ w w₁ c χ y x

/-- The boundary term `B = e(Gu − p(G′ + icyG)ψ)`, with `u = pψ′`. -/
noncomputable def bBc (w w₁ : ℝ → ℂ) (c χ : ℝ) (g : ℝ → ℝ) (y x : ℝ) : ℂ :=
  eF c y x * (gWc w c χ y x * (rungU c g x : ℂ)
    - ((pP x : ℝ) : ℂ) * (gWc₁ w w₁ c χ y x + I * ((c * y : ℝ) : ℂ) * gWc w c χ y x) * (psi c g x : ℂ))

/-! ### Real weights recover Cvs.L2a.FarIntegrationByParts -/

/-! ### Derivatives -/

/-- `G′` is the derivative of `G` where `w` is differentiable and `Q ≠ 0`. -/
theorem hasDerivAt_gWc {w w₁ : ℝ → ℂ} {c χ y x : ℝ} (hw : HasDerivAt w (w₁ x) x) (hQ : qQ c χ y x ≠ 0) :
    HasDerivAt (gWc w c χ y) (gWc₁ w w₁ c χ y x) x :=
  hw.div (hasDerivAt_qQ c χ y x) hQ

/-- `G″` is the derivative of `G′` where `w, w′` are differentiable and `Q ≠ 0`. -/
theorem hasDerivAt_gWc₁ {w w₁ w₂ : ℝ → ℂ} {c χ y x : ℝ} (hw : HasDerivAt w (w₁ x) x)
    (hw₁ : HasDerivAt w₁ (w₂ x) x) (hQ : qQ c χ y x ≠ 0) :
    HasDerivAt (gWc₁ w w₁ c χ y) (gWc₂ w w₁ w₂ c χ y x) x := by
  have hN := (hw₁.mul (hasDerivAt_qQ c χ y x)).sub (hw.mul (hasDerivAt_qQ₁ c y x))
  have := hN.div ((hasDerivAt_qQ c χ y x).pow 2) (pow_ne_zero 2 hQ)
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  unfold gWc₂; field_simp; ring

/-- **The exact identity** `B′ + eψR = wψe` at any `x > 1` where `w, w′` are differentiable and `Q ≠ 0`. -/
theorem hasDerivAt_bBc {g g₁ g₂ : ℝ → ℝ} {w w₁ w₂ : ℝ → ℂ} {c χ y x : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hx : 1 < x) (hw : HasDerivAt w (w₁ x) x) (hw₁ : HasDerivAt w₁ (w₂ x) x) (hQ : qQ c χ y x ≠ 0) :
    HasDerivAt (bBc w w₁ c χ g y)
      (w x * (psi c g x : ℂ) * eF c y x - eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x) x := by
  obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  have hψ' := (hψ x hx).ofReal_comp
  have hu' := (hu x).ofReal_comp
  have hp' : HasDerivAt (fun x : ℝ => ((pP x : ℝ) : ℂ)) (((2 * x : ℝ)) : ℂ) x := by
    have := (hasDerivAt_pow 2 x).sub_const 1
    exact (this.congr_deriv (by push_cast; ring)).ofReal_comp
  have hG := hasDerivAt_gWc (c := c) (χ := χ) (y := y) hw hQ
  have hG₁ := hasDerivAt_gWc₁ (c := c) (χ := χ) (y := y) hw hw₁ hQ
  have := (hasDerivAt_eF c y x).mul ((hG.mul hu').sub
    ((hp'.mul (hG₁.add (hG.const_mul (I * ((c * y : ℝ) : ℂ))))).mul hψ'))
  refine this.congr_deriv ?_
  have hp0 : ((pP x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pP_pos hx).ne'
  have hd : ((pP x : ℝ) : ℂ) * ((rungU c g x / pP x : ℝ) : ℂ) = (rungU c g x : ℂ) := by
    push_cast; field_simp
  have hwQ : w x = qQ c χ y x * gWc w c χ y x := by unfold gWc; field_simp
  have hQe : qQ c χ y x = (c : ℂ) ^ 2 * ((x : ℂ) ^ 2 - 1) * ((y : ℂ) ^ 2 - 1) - ((c : ℂ) ^ 2 - χ)
      - 2 * (c : ℂ) * x * y * I := by unfold qQ; push_cast; ring
  unfold rRc
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  set G := gWc w c χ y x
  set G₁ := gWc₁ w w₁ c χ y x
  set G₂ := gWc₂ w w₁ w₂ c χ y x
  set e := eF c y x
  set ψ := (psi c g x : ℂ)
  set u := (rungU c g x : ℂ)
  set ψd := ((rungU c g x / pP x : ℝ) : ℂ)
  set Q := qQ c χ y x
  unfold pP at hd ⊢; unfold qP
  push_cast at hd ⊢
  linear_combination (-(e * (G₁ + I * (c * y) * G))) * hd - (ψ * e) * hwQ - (e * G * ψ) * hQe
    - ((c * y) ^ 2 * ((x : ℂ) ^ 2 - 1) * e * G * ψ) * I_sq

/-! ### The identity on `[α, β]` -/

/-- `G`, `G′` and `R` are continuous on `s` where `Q ≠ 0`, for `w, w′, w″` continuous on `s`. -/
theorem continuousOn_gWc_rRc {w w₁ w₂ : ℝ → ℂ} {c χ y : ℝ} {s : Set ℝ} (hw : ContinuousOn w s)
    (hw₁ : ContinuousOn w₁ s) (hw₂ : ContinuousOn w₂ s) (hQ : ∀ x ∈ s, qQ c χ y x ≠ 0) :
    ContinuousOn (gWc w c χ y) s ∧ ContinuousOn (gWc₁ w w₁ c χ y) s ∧ ContinuousOn (rRc w w₁ w₂ c χ y) s := by
  obtain ⟨hQc, hQ₁c⟩ := continuous_qQ c χ y
  have cQ := hQc.continuousOn (s := s)
  have cQ₁ := hQ₁c.continuousOn (s := s)
  have hG : ContinuousOn (gWc w c χ y) s := hw.div cQ hQ
  have hG₁ : ContinuousOn (gWc₁ w w₁ c χ y) s :=
    ((hw₁.mul cQ).sub (hw.mul cQ₁)).div (cQ.pow 2) fun x hx => pow_ne_zero 2 (hQ x hx)
  have hG₂ : ContinuousOn (gWc₂ w w₁ w₂ c χ y) s :=
    ((((hw₂.mul cQ).sub (hw.mul continuousOn_const)).mul cQ).sub
      ((continuousOn_const.mul ((hw₁.mul cQ).sub (hw.mul cQ₁))).mul cQ₁)).div (cQ.pow 3)
      fun x hx => pow_ne_zero 3 (hQ x hx)
  refine ⟨hG, hG₁, ?_⟩
  have hp : ContinuousOn (fun x : ℝ => ((pP x : ℝ) : ℂ)) s :=
    (by unfold pP; fun_prop : Continuous fun x : ℝ => ((pP x : ℝ) : ℂ)).continuousOn
  have hx : ContinuousOn (fun x : ℝ => (x : ℂ)) s := continuous_ofReal.continuousOn
  exact ((continuousOn_const.mul hx).mul hG₁).add (hp.mul hG₂) |>.add ((continuousOn_const.mul hp).mul hG₁)

/-- **The Q-identity on `[α, β] ⊆ (1, ∞)` for a complex `C²` weight**: `∫_α^β wψe = ∫_α^β eψR + [B]_α^β`,
`e = e^{icxy}`, `G = w/Q`, `R = (pG′)′ + 2icy pG′`. -/
theorem ibpC_Icc {g g₁ g₂ : ℝ → ℝ} {w w₁ w₂ : ℝ → ℂ} {c χ y α β : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hy : 0 < y) (hα : 1 < α) (hαβ : α ≤ β)
    (hw : ∀ x ∈ Icc α β, HasDerivAt w (w₁ x) x) (hw₁ : ∀ x ∈ Icc α β, HasDerivAt w₁ (w₂ x) x)
    (hw₂ : ContinuousOn w₂ (Icc α β)) :
    ∫ x in α..β, w x * (psi c g x : ℂ) * eF c y x
      = (∫ x in α..β, eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x)
        + (bBc w w₁ c χ g y β - bBc w w₁ c χ g y α) := by
  obtain ⟨-, -, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hI : uIcc α β = Icc α β := uIcc_of_le hαβ
  have hQ : ∀ x ∈ Icc α β, qQ c χ y x ≠ 0 := fun x hx =>
    Cvs.L2a.QIdentityRealWeight.qQ_ne_zero_of_pos hc (by linarith [hx.1]) hy
  have hwc : ContinuousOn w (Icc α β) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hw₁c : ContinuousOn w₁ (Icc α β) := fun x hx => (hw₁ x hx).continuousAt.continuousWithinAt
  have hL : IntervalIntegrable (fun x => w x * (psi c g x : ℂ) * eF c y x) volume α β :=
    ((hwc.mul (continuous_ofReal.comp hψc).continuousOn).mul
      (continuous_eF c y).1.continuousOn).intervalIntegrable_of_Icc hαβ
  have hR : IntervalIntegrable (fun x => eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x) volume α β :=
    (((continuous_eF c y).1.continuousOn.mul (continuous_ofReal.comp hψc).continuousOn).mul
      (continuousOn_gWc_rRc hwc hw₁c hw₂ hQ).2.2).intervalIntegrable_of_Icc hαβ
  have hderiv : ∀ x ∈ uIcc α β, HasDerivAt (bBc w w₁ c χ g y)
      ((fun x => w x * (psi c g x : ℂ) * eF c y x
        - eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x) x) x := by
    intro x hx
    rw [hI] at hx
    exact hasDerivAt_bBc hg hg₁ hg₂c hang (by linarith [hx.1]) (hw x hx) (hw₁ x hx) (hQ x hx)
  have hftc := integral_eq_sub_of_hasDerivAt hderiv (hL.sub hR)
  rw [intervalIntegral.integral_sub hL hR] at hftc
  linear_combination hftc

/-- `B` vanishes at a point where `w` and `w′` vanish. -/
theorem bBc_eq_zero {w w₁ : ℝ → ℂ} {c χ y x : ℝ} {g : ℝ → ℝ} (h0 : w x = 0) (h1 : w₁ x = 0) :
    bBc w w₁ c χ g y x = 0 := by
  unfold bBc gWc gWc₁; rw [h0, h1]; simp

/-! ### The atoms -/

/-- `2x + 2icy p`, the coefficient of `G′` in `R = 2xG′ + pG″ + 2icy pG′`. -/
noncomputable def kK (c y x : ℝ) : ℂ := 2 * (x : ℂ) + 2 * I * ((c * y : ℝ) : ℂ) * ((pP x : ℝ) : ℂ)

/-- The first atom `A₁ = (2x + 2icyp)w′ + pw″`. -/
noncomputable def aC₁ (w₁ w₂ : ℝ → ℂ) (c y x : ℝ) : ℂ := kK c y x * w₁ x + ((pP x : ℝ) : ℂ) * w₂ x

/-- The second atom `A₂ = −((2x + 2icyp)Q′ + pQ″)w − 2pQ′w′`. -/
noncomputable def aC₂ (w w₁ : ℝ → ℂ) (c y x : ℝ) : ℂ :=
  -((kK c y x * qQ₁ c y x + ((pP x : ℝ) : ℂ) * qQ₂ c y) * w x) - 2 * ((pP x : ℝ) : ℂ) * qQ₁ c y x * w₁ x

/-- The third atom `A₃ = 2pQ′²w`. -/
noncomputable def aC₃ (w : ℝ → ℂ) (c y x : ℝ) : ℂ := 2 * ((pP x : ℝ) : ℂ) * qQ₁ c y x ^ 2 * w x

/-- **`R = A₁/Q + A₂/Q² + A₃/Q³`** wherever `Q ≠ 0`, for any complex weight. -/
theorem rRc_eq {w w₁ w₂ : ℝ → ℂ} {c χ y x : ℝ} (hQ : qQ c χ y x ≠ 0) :
    rRc w w₁ w₂ c χ y x
      = aC₁ w₁ w₂ c y x / qQ c χ y x + aC₂ w w₁ c y x / qQ c χ y x ^ 2 + aC₃ w c y x / qQ c χ y x ^ 3 := by
  unfold rRc gWc₁ gWc₂ aC₁ aC₂ aC₃ kK
  field_simp
  ring

/-! ### Atom bounds -/

/-- `|2x + 2icyp| ≤ 2x + 2cyp` for `x ≥ 1`, `c, y ≥ 0`. -/
theorem norm_kK_le {c y x : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y) (hx : 1 ≤ x) :
    ‖kK c y x‖ ≤ 2 * x + 2 * (c * y) * pP x := by
  have hp : 0 ≤ pP x := by unfold pP; nlinarith
  unfold kK
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (mul_nonneg hc hy), abs_of_nonneg hp]
  norm_num

/-- `|Q″| = 2c²(y² − 1)` for `y ≥ 1`. -/
theorem norm_qQ₂_eq {c y : ℝ} (hy : 1 ≤ y) : ‖qQ₂ c y‖ = 2 * c ^ 2 * (y ^ 2 - 1) := by
  unfold qQ₂
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  have : 0 ≤ y ^ 2 - 1 := by nlinarith
  positivity

/-- `|Q| ≥ |c²(x² − 1)(y² − 1) − (c² − χ)|` from `Re Q`. -/
theorem norm_qQ_ge_re (c χ y x : ℝ) : |c ^ 2 * (x ^ 2 - 1) * (y ^ 2 - 1) - (c ^ 2 - χ)| ≤ ‖qQ c χ y x‖ := by
  rw [← qQ_re]; exact Complex.abs_re_le_norm _

/-- `|A₁| ≤ (2x + 2cyp)|w′| + p|w″|`. -/
theorem norm_aC₁_le {w₁ w₂ : ℝ → ℂ} {c y x : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y) (hx : 1 ≤ x) :
    ‖aC₁ w₁ w₂ c y x‖ ≤ (2 * x + 2 * (c * y) * pP x) * ‖w₁ x‖ + pP x * ‖w₂ x‖ := by
  have hp : 0 ≤ pP x := by unfold pP; nlinarith
  unfold aC₁
  refine (norm_add_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (norm_kK_le hc hy hx) (norm_nonneg _)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]

/-- `|A₂| ≤ ((2x + 2cyp)|Q′| + p|Q″|)|w| + 2p|Q′||w′|`. -/
theorem norm_aC₂_le {w w₁ : ℝ → ℂ} {c y x : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y) (hx : 1 ≤ x) :
    ‖aC₂ w w₁ c y x‖ ≤ ((2 * x + 2 * (c * y) * pP x) * ‖qQ₁ c y x‖ + pP x * ‖qQ₂ c y‖) * ‖w x‖
      + 2 * pP x * ‖qQ₁ c y x‖ * ‖w₁ x‖ := by
  have hp : 0 ≤ pP x := by unfold pP; nlinarith
  have hpn : ‖((pP x : ℝ) : ℂ)‖ = pP x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  unfold aC₂
  refine (norm_sub_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
  · rw [norm_neg, norm_mul]
    refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add ?_ (le_of_eq ?_))) (norm_nonneg _)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (norm_kK_le hc hy hx) (norm_nonneg _)
    · rw [norm_mul, hpn]
  · rw [norm_mul, norm_mul, norm_mul, hpn]; norm_num

/-- `|A₃| = 2p|Q′|²|w|`. -/
theorem norm_aC₃_eq {w : ℝ → ℂ} {c y x : ℝ} (hx : 1 ≤ x) :
    ‖aC₃ w c y x‖ = 2 * pP x * ‖qQ₁ c y x‖ ^ 2 * ‖w x‖ := by
  have hp : 0 ≤ pP x := by unfold pP; nlinarith
  unfold aC₃
  rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  norm_num

/-- **`|R| ≤ |A₁|/|Q| + |A₂|/|Q|² + |A₃|/|Q|³`** wherever `Q ≠ 0`. -/
theorem norm_rRc_le {w w₁ w₂ : ℝ → ℂ} {c χ y x : ℝ} (hQ : qQ c χ y x ≠ 0) :
    ‖rRc w w₁ w₂ c χ y x‖ ≤ ‖aC₁ w₁ w₂ c y x‖ / ‖qQ c χ y x‖ + ‖aC₂ w w₁ c y x‖ / ‖qQ c χ y x‖ ^ 2
      + ‖aC₃ w c y x‖ / ‖qQ c χ y x‖ ^ 3 := by
  rw [rRc_eq hQ]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (le_of_eq ?_)) (le_of_eq ?_))
  · rw [norm_div, norm_div, norm_pow]
  · rw [norm_div, norm_pow]

end Cvs.L2a.QIdentityComplexWeight
