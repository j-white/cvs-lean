import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.PlaneCorrelationL2
import Cvs.Route.CoreSchurForm
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.OneCellBoxWindowForm
import Cvs.Route.OneCellCriterion
import Cvs.Route.OneCellLaplaceTransform
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.StepAFromTwoGaps
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.Mollify.AeSymmetryEnough
import Cvs.WeilForm.NestedWindowsMonotoneBottom
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowSetNonempty

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Reflection-even window positivity is RH

The box `1_(0,l]` has `‖1_(0,l]‖² = l` and window form `G(l)` (Cvs.Route.OneCellBoxWindowForm). Centred in `(0, log x]` by `NestedWindowsMonotoneBottom`'s
embedding it is reflection-even with the same norm and form value, so `μ‖w‖² ≤ Q_x(w)` on even classes at `x`
gives `μ·l ≤ G(l)` for `0 < l ≤ log x`. With Cvs.Route.OneCellCriterion: RH is `Q_x ≥ −ε‖·‖²` on even classes at arbitrarily
large `x` for every `ε > 0`, and also `Q_x ≥ 0` on even classes at infinitely many `x`.
-/

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.WeilForm.ReflectionEvenPositivityRH
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.Route.OneCellLaplaceTransform (G)

/-- The reflection-even classes of the form domain at `L = log x`. -/
abbrev Ev (x : ℕ) : Submodule ℝ (Dom x) := Cvs.StepA.StepAFromTwoGaps.evenSub (Real.log_natCast_nonneg x)

/-! ### The box as a form-domain class -/

/-- The box `1_(0,l]` as a form-domain class at `L = l`. -/
def boxD {l : ℝ} (hl : 0 < l) : Cvs.WeilForm.FormDomain.formDomain hl.le :=
  Cvs.Approximant.SpineSubspace.ofFun hl.le (Cvs.WeilForm.WindowSetNonempty.memLp_flat l) (ae_of_all _ (Cvs.WeilForm.WindowSetNonempty.support_flat l))
    (Cvs.WeilForm.WindowSetNonempty.integrableOn_levy_flat hl)

/-- The class `boxD` is a.e. the box. -/
theorem coe_boxD_ae {l : ℝ} (hl : 0 < l) :
    (((boxD hl : Cvs.WeilForm.FormDomain.formDomain hl.le) : Cvs.WeilForm.WeilFormOnWindowL2.window l) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] Cvs.WeilForm.WindowSetNonempty.flat l :=
  Cvs.Approximant.SpineSubspace.coe_ofFun_ae hl.le _ _ _

/-- The box is reflection-even: `reflD (1_(0,l]) = 1_(0,l]`. -/
theorem reflD_boxD {l : ℝ} (hl : 0 < l) : Cvs.WeilForm.WindowReflectionSymmetry.reflD hl.le (boxD hl) = boxD hl := by
  apply Subtype.ext; apply Subtype.ext
  show Cvs.WeilForm.WindowReflectionSymmetry.refl l ((boxD hl : Cvs.WeilForm.WeilFormOnWindowL2.window l) : Lp ℝ 2 (volume : Measure ℝ))
    = ((boxD hl : Cvs.WeilForm.WeilFormOnWindowL2.window l) : Lp ℝ 2 (volume : Measure ℝ))
  apply Lp.ext
  have h2 := (Measure.measurePreserving_sub_left volume l).quasiMeasurePreserving.ae_eq_comp
    (coe_boxD_ae hl)
  filter_upwards [Cvs.WeilForm.WindowReflectionSymmetry.refl_ae l _, h2, coe_boxD_ae hl, Cvs.WeilForm.Mollify.AeSymmetryEnough.flat_even_ae hl] with s h1 h2 h3 h4
  rw [h1, h3]
  simp only [Function.comp_apply] at h2
  rw [h2]
  exact h4

/-- `‖1_(0,l]‖² = l`. -/
theorem norm_sq_boxD {l : ℝ} (hl : 0 < l) : ‖boxD hl‖ ^ 2 = l := by
  have h : ‖boxD hl‖ = ‖((boxD hl : Cvs.WeilForm.WeilFormOnWindowL2.window l) : Lp ℝ 2 (volume : Measure ℝ))‖ := rfl
  rw [h, Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
  have hae : (fun s => (((boxD hl : Cvs.WeilForm.WeilFormOnWindowL2.window l) : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ) s ^ 2)
      =ᵐ[volume] fun s => Cvs.WeilForm.WindowSetNonempty.flat l s ^ 2 :=
    (coe_boxD_ae hl).mono fun s hs => by simp only [hs]
  rw [integral_congr_ae hae]
  exact Cvs.WeilForm.WindowSetNonempty.integral_flat_sq hl.le

/-- **The window form of the box is `G(l)`**, for every complete `(P, R)`: `e^l ≤ P`, `l ≤ R log 2`. -/
theorem Q_boxD {l : ℝ} (hl : 0 < l) {P R : ℕ} (hP : Real.exp l ≤ P) (hR : l ≤ R * Real.log 2) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hl.le P R (boxD hl) = G l := by
  rw [boxD, Cvs.Approximant.SpineSubspace.Q_ofFun]
  exact Cvs.Route.OneCellBoxWindowForm.weilForm_flat_eq hl hP hR

/-! ### The centred box at scale `x` -/

/-- `0 < l ≤ log x` forces `2 ≤ x`. -/
theorem two_le_of_le_log {l : ℝ} (hl : 0 < l) {x : ℕ} (hlx : l ≤ Real.log x) : 2 ≤ x := by
  by_contra h
  push Not at h
  have h1 : (x : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 h
  have := Real.log_nonpos (Nat.cast_nonneg x) h1
  linarith

/-- The box `1_(0,l]` translated to the centre of `(0, log x]`, `l ≤ log x`. -/
def cboxD {l : ℝ} (hl : 0 < l) {x : ℕ} (hlx : l ≤ Real.log x) : Dom x :=
  Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD hl.le (Real.log_natCast_nonneg x) hlx (boxD hl)

/-- The centred box is reflection-even. -/
theorem cboxD_mem_Ev {l : ℝ} (hl : 0 < l) {x : ℕ} (hlx : l ≤ Real.log x) : cboxD hl hlx ∈ Ev x := by
  show Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) (cboxD hl hlx) = cboxD hl hlx
  rw [cboxD, Cvs.WeilForm.NestedWindowsMonotoneBottom.reflD_embedD, reflD_boxD]

/-- `‖centred box‖² = l`. -/
theorem norm_sq_cboxD {l : ℝ} (hl : 0 < l) {x : ℕ} (hlx : l ≤ Real.log x) :
    ‖cboxD hl hlx‖ ^ 2 = l := by
  have h : ‖cboxD hl hlx‖ = ‖boxD hl‖ := Cvs.WeilForm.NestedWindowsMonotoneBottom.norm_embed hl.le hlx (boxD hl)
  rw [h, norm_sq_boxD]

/-- **The window form of the centred box is `G(l)`**: `Q_x(centred 1_(0,l]) = G(l)` for `0 < l ≤ log x`. -/
theorem Q_cboxD {l : ℝ} (hl : 0 < l) {x : ℕ} (hlx : l ≤ Real.log x) : Qx x (cboxD hl hlx) = G l := by
  obtain ⟨-, hP, hR⟩ := Cvs.Approximant.SpineSubspace.sizes x (two_le_of_le_log hl hlx)
  have hP' : Real.exp l ≤ x := (Real.exp_le_exp.2 hlx).trans hP
  have hR' : l ≤ (Nat.clog 2 x : ℝ) * Real.log 2 := hlx.trans hR
  have h : Qx x (cboxD hl hlx) = Cvs.WeilForm.InfimumAttainedSphere.Q hl.le x (Nat.clog 2 x) (boxD hl) :=
    Cvs.WeilForm.NestedWindowsMonotoneBottom.weilQW_embed hl.le hlx le_rfl le_rfl hP' hR' (boxD hl)
  rw [h, Q_boxD hl hP' hR']

/-! ### Even floors bound the one-cell function -/

/-- **An even floor at `x` bounds `G` below on `(0, log x]`**: `μ‖w‖² ≤ Q_x(w)` for every reflection-even
`w` gives `μ·l ≤ G(l)` for `0 < l ≤ log x`. -/
theorem mul_le_G_of_evenFloor {x : ℕ} {μ : ℝ} (h : ∀ w ∈ Ev x, μ * ‖w‖ ^ 2 ≤ Qx x w) {l : ℝ}
    (hl : 0 < l) (hlx : l ≤ Real.log x) : μ * l ≤ G l := by
  have h1 := h _ (cboxD_mem_Ev hl hlx)
  rwa [norm_sq_cboxD, Q_cboxD] at h1

/-- **Even positivity at `x` gives `G ≥ 0` on `(0, log x]`.** -/
theorem G_nonneg_of_evenPos {x : ℕ} (h : ∀ w ∈ Ev x, 0 ≤ Qx x w) {l : ℝ} (hl : 0 < l)
    (hlx : l ≤ Real.log x) : 0 ≤ G l := by
  have h1 := mul_le_G_of_evenFloor (μ := 0) (fun w hw => by simpa using h w hw) hl hlx
  simpa using h1

/-! ### RH -/

/-- `x₀ = ⌈e^l⌉₊ ≤ x` gives `l ≤ log x`. -/
theorem le_log_of_ceil_exp_le {l : ℝ} {x : ℕ} (hx : ⌈Real.exp l⌉₊ ≤ x) : l ≤ Real.log x := by
  have h1 : Real.exp l ≤ x := (Nat.le_ceil _).trans (by exact_mod_cast hx)
  exact (Real.le_log_iff_exp_le ((Real.exp_pos l).trans_le h1)).2 h1

/-- **Even window positivity at infinitely many `x` gives RH.** -/
theorem rh_of_frequently_evenWindowPos (h : ∃ᶠ x : ℕ in atTop, ∀ w ∈ Ev x, 0 ≤ Qx x w) :
    RiemannHypothesis := by
  refine Cvs.Route.OneCellCriterion.riemannHypothesis_of_G_nonneg fun l hl => ?_
  obtain ⟨x, hx, hx0⟩ := (h.and_eventually (eventually_ge_atTop ⌈Real.exp l⌉₊)).exists
  exact G_nonneg_of_evenPos hx hl (le_log_of_ceil_exp_le hx0)

/-- **RH is even window positivity at infinitely many `x`.** -/
theorem rh_iff_frequently_evenWindowPos :
    RiemannHypothesis ↔ ∃ᶠ x : ℕ in atTop, ∀ w ∈ Ev x, 0 ≤ Qx x w :=
  ⟨fun hRH => (eventually_ge_atTop 2).frequently.mono fun x hx w _ => Cvs.Route.CoreSchurForm.nonneg_of_rh hRH x hx w,
    rh_of_frequently_evenWindowPos⟩

end Cvs.WeilForm.ReflectionEvenPositivityRH
