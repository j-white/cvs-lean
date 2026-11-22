import Mathlib
import Cvs.Route.L1GapCeilingRH
import Cvs.Route.L1GapParametricRH
import Cvs.WeilForm.ApproxWindowPositivityRH
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.HatFunctionWindow
import Cvs.WeilForm.HatInFormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.NestedWindowsMonotoneBottom
import Cvs.WeilForm.PrimeShiftOperator
import Cvs.WeilForm.SimpleGroundEvenOrOdd
import Cvs.WeilForm.TwoIndependentClasses
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `L1GapL` with `L ≥ 0` gives RH

The tent and the even part of the half-width tent span a plane of even classes at every scale; its orthogonal
basis embeds isometrically, evenly and with unchanged Weil value into every larger window, so a constant `M`
bounds both Rayleigh quotients for all `x ≥ 2` and Cvs.Route.L1GapCeilingRH applies with `M = O(1)`.
-/

noncomputable section

open MeasureTheory Real Filter Topology
open scoped InnerProductSpace

namespace Cvs.Route.L1GapNonnegRH
open Cvs.ZeroCounting

open Cvs.ZeroCounting

/-- The tent is even. -/
theorem reflD_hatD {L : ℝ} (hL : 0 < L) : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL.le (Cvs.WeilForm.HatInFormDomain.hatD hL) = Cvs.WeilForm.HatInFormDomain.hatD hL := by
  apply Subtype.ext; apply Subtype.ext
  show Cvs.WeilForm.WindowReflectionSymmetry.refl L ((Cvs.WeilForm.HatFunctionWindow.hatW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
    = ((Cvs.WeilForm.HatFunctionWindow.hatW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
  apply Lp.ext
  have h2 := (Measure.measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp
    (Cvs.WeilForm.HatFunctionWindow.hatW_ae L)
  filter_upwards [Cvs.WeilForm.WindowReflectionSymmetry.refl_ae L _, h2, Cvs.WeilForm.HatFunctionWindow.hatW_ae L] with s h1 h2 h3
  rw [h1, h3]
  simp only [Function.comp_apply] at h2 ⊢
  rw [h2]
  unfold Cvs.WeilForm.HatFunctionWindow.hat
  rw [show L - (L - s) = s by ring, min_comm]

/-- The even part of the half-width tent is `s ↦ (h(s) + h(L − s))/2` almost everywhere, `h` the half-width tent. -/
theorem evenPart_hatSmallD_ae {L : ℝ} (hL : 0 < L) :
    ((Cvs.WeilForm.EvenOddSplitForm.evenPart hL.le (Cvs.WeilForm.TwoIndependentClasses.hatSmallD hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun s => 1 / 2 * (Cvs.WeilForm.HatFunctionWindow.hat (L / 2) s + Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L - s)) := by
  have hcoe : ((Cvs.WeilForm.EvenOddSplitForm.evenPart hL.le (Cvs.WeilForm.TwoIndependentClasses.hatSmallD hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      = (1 / 2 : ℝ) • (((Cvs.WeilForm.TwoIndependentClasses.hatSmallW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        + Cvs.WeilForm.WindowReflectionSymmetry.refl L ((Cvs.WeilForm.TwoIndependentClasses.hatSmallW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))) := rfl
  rw [hcoe]
  have h6 := (Measure.measurePreserving_sub_left volume L).quasiMeasurePreserving.ae_eq_comp
    (Cvs.WeilForm.TwoIndependentClasses.hatSmallW_ae L)
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (((Cvs.WeilForm.TwoIndependentClasses.hatSmallW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
      Lp ℝ 2 (volume : Measure ℝ)) + Cvs.WeilForm.WindowReflectionSymmetry.refl L ((Cvs.WeilForm.TwoIndependentClasses.hatSmallW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
        Lp ℝ 2 (volume : Measure ℝ))),
    Lp.coeFn_add ((Cvs.WeilForm.TwoIndependentClasses.hatSmallW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      (Cvs.WeilForm.WindowReflectionSymmetry.refl L ((Cvs.WeilForm.TwoIndependentClasses.hatSmallW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))),
    Cvs.WeilForm.WindowReflectionSymmetry.refl_ae L ((Cvs.WeilForm.TwoIndependentClasses.hatSmallW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)),
    Cvs.WeilForm.TwoIndependentClasses.hatSmallW_ae L, h6] with s h1 h3 h4 h5 h6
  simp only [Function.comp_apply] at h6
  rw [h1, Pi.smul_apply, h3, Pi.add_apply, h4, h5, h6, smul_eq_mul]

/-- The even part of the half-width tent is not a multiple of the tent. -/
theorem evenPart_hatSmallD_ne_smul {L : ℝ} (hL : 0 < L) (c : ℝ) :
    Cvs.WeilForm.EvenOddSplitForm.evenPart hL.le (Cvs.WeilForm.TwoIndependentClasses.hatSmallD hL) ≠ c • Cvs.WeilForm.HatInFormDomain.hatD hL := by
  intro h
  have hLp : ((Cvs.WeilForm.EvenOddSplitForm.evenPart hL.le (Cvs.WeilForm.TwoIndependentClasses.hatSmallD hL) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      = c • ((Cvs.WeilForm.HatFunctionWindow.hatW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) := by
    have := congrArg (fun φ : Cvs.WeilForm.FormDomain.formDomain hL.le =>
      ((φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))) h
    simp only [Submodule.coe_smul] at this
    exact this
  have hae : (fun s => 1 / 2 * (Cvs.WeilForm.HatFunctionWindow.hat (L / 2) s + Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L - s)))
      =ᵐ[volume] fun s => c * Cvs.WeilForm.HatFunctionWindow.hat L s := by
    have h1 := evenPart_hatSmallD_ae hL
    rw [hLp] at h1
    filter_upwards [h1, Lp.coeFn_smul c ((Cvs.WeilForm.HatFunctionWindow.hatW L : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)),
      Cvs.WeilForm.HatFunctionWindow.hatW_ae L] with s hs1 hs2 hs3
    rw [← hs1, hs2, Pi.smul_apply, hs3, smul_eq_mul]
  have heq : (fun s => 1 / 2 * (Cvs.WeilForm.HatFunctionWindow.hat (L / 2) s + Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L - s)))
      = fun s => c * Cvs.WeilForm.HatFunctionWindow.hat L s := (Continuous.ae_eq_iff_eq (volume : Measure ℝ)
    (continuous_const.mul ((Cvs.WeilForm.HatFunctionWindow.continuous_hat _).add
      ((Cvs.WeilForm.HatFunctionWindow.continuous_hat _).comp (continuous_const.sub continuous_id))))
    (continuous_const.mul (Cvs.WeilForm.HatFunctionWindow.continuous_hat L))).mp hae
  have e1 : Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L / 2) = 0 := by
    unfold Cvs.WeilForm.HatFunctionWindow.hat; rw [show L / 2 - L / 2 = (0 : ℝ) by ring, min_eq_right (by linarith), max_self]
  have e2 : Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L - L / 2) = 0 := by rw [show L - L / 2 = L / 2 by ring]; exact e1
  have e3 : Cvs.WeilForm.HatFunctionWindow.hat L (L / 2) = L / 2 := Cvs.WeilForm.HatFunctionWindow.hat_half hL.le
  have e4 : Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L / 4) = L / 4 := by
    unfold Cvs.WeilForm.HatFunctionWindow.hat; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  have e5 : Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L - L / 4) = 0 := by
    unfold Cvs.WeilForm.HatFunctionWindow.hat; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  have e6 : Cvs.WeilForm.HatFunctionWindow.hat L (L / 4) = L / 4 := by
    unfold Cvs.WeilForm.HatFunctionWindow.hat; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  have hmid : 1 / 2 * (Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L / 2) + Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L - L / 2))
      = c * Cvs.WeilForm.HatFunctionWindow.hat L (L / 2) := congrFun heq (L / 2)
  have hq : 1 / 2 * (Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L / 4) + Cvs.WeilForm.HatFunctionWindow.hat (L / 2) (L - L / 4))
      = c * Cvs.WeilForm.HatFunctionWindow.hat L (L / 4) := congrFun heq (L / 4)
  rw [e1, e2, e3] at hmid
  rw [e4, e5, e6] at hq
  have hc : c = 0 := by
    have h0 : c * (L / 2) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · linarith
  rw [hc] at hq
  linarith

/-- **Two orthogonal nonzero even classes** in the form domain of every nondegenerate window. -/
theorem exists_even_pair_pos {L : ℝ} (hL0 : 0 ≤ L) (hL : 0 < L) :
    ∃ a b : Cvs.WeilForm.FormDomain.formDomain hL0, Cvs.WeilForm.WindowReflectionSymmetry.reflD hL0 a = a ∧ Cvs.WeilForm.WindowReflectionSymmetry.reflD hL0 b = b ∧
      ⟪a, b⟫_ℝ = 0 ∧ a ≠ 0 ∧ b ≠ 0 := by
  set a : Cvs.WeilForm.FormDomain.formDomain hL0 := Cvs.WeilForm.HatInFormDomain.hatD hL with had
  set b0 : Cvs.WeilForm.FormDomain.formDomain hL0 := Cvs.WeilForm.EvenOddSplitForm.evenPart hL0 (Cvs.WeilForm.TwoIndependentClasses.hatSmallD hL) with hb0d
  have ha : a ≠ 0 := Cvs.WeilForm.HatInFormDomain.hatD_ne_zero hL
  have hae : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL0 a = a := reflD_hatD hL
  have hb0e : Cvs.WeilForm.WindowReflectionSymmetry.reflD hL0 b0 = b0 := Cvs.WeilForm.EvenOddSplitForm.reflD_evenPart _ _
  have hn : ‖a‖ ≠ 0 := by simpa using ha
  refine ⟨a, b0 - (⟪a, b0⟫_ℝ / ‖a‖ ^ 2) • a, hae, ?_, ?_, ha, ?_⟩
  · rw [Cvs.WeilForm.EvenOddSplitForm.reflD_sub, Cvs.WeilForm.SimpleGroundEvenOrOdd.reflD_smul, hae, hb0e]
  · rw [Cvs.WeilForm.TwoIndependentClasses.inner_coe, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, ← Cvs.WeilForm.TwoIndependentClasses.inner_coe]
    have hnorm : ‖((a : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))‖ = ‖a‖ := rfl
    rw [hnorm]
    field_simp
    ring
  · intro h0
    exact evenPart_hatSmallD_ne_smul hL _ (sub_eq_zero.mp h0)

/-- The window embedding preserves inner products. -/
theorem inner_embedD {L L' : ℝ} (hL : 0 ≤ L) (hL' : 0 ≤ L') (hLL : L ≤ L')
    (a b : Cvs.WeilForm.FormDomain.formDomain hL) :
    ⟪Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD hL hL' hLL a, Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD hL hL' hLL b⟫_ℝ = ⟪a, b⟫_ℝ := by
  rw [Cvs.WeilForm.TwoIndependentClasses.inner_coe, Cvs.WeilForm.TwoIndependentClasses.inner_coe]
  show ⟪((Cvs.WeilForm.NestedWindowsMonotoneBottom.embed L L' a : Cvs.WeilForm.WeilFormOnWindowL2.window L') : Lp ℝ 2 (volume : Measure ℝ)),
      ((Cvs.WeilForm.NestedWindowsMonotoneBottom.embed L L' b : Cvs.WeilForm.WeilFormOnWindowL2.window L') : Lp ℝ 2 (volume : Measure ℝ))⟫_ℝ = _
  rw [Cvs.WeilForm.NestedWindowsMonotoneBottom.embed_coe hL hLL, Cvs.WeilForm.NestedWindowsMonotoneBottom.embed_coe hL hLL]
  have h1 := norm_add_sq_real
    (Cvs.WeilForm.PrimeShiftOperator.transLp (Cvs.WeilForm.NestedWindowsMonotoneBottom.shift L L') ((a : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
    (Cvs.WeilForm.PrimeShiftOperator.transLp (Cvs.WeilForm.NestedWindowsMonotoneBottom.shift L L') ((b : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)))
  have h2 := norm_add_sq_real ((a : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
    ((b : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
  rw [← Cvs.WeilForm.PrimeShiftOperator.transLp_add, Cvs.WeilForm.PrimeShiftOperator.norm_transLp, Cvs.WeilForm.PrimeShiftOperator.norm_transLp, Cvs.WeilForm.PrimeShiftOperator.norm_transLp] at h1
  linarith

/-- **A fixed orthogonal even pair with bounded Rayleigh quotients at every scale `x ≥ 2`.** -/
theorem exists_even_pair : ∃ M : ℝ, ∀ᶠ x : ℕ in atTop,
    ∃ a b : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) a = a ∧ Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) b = b ∧
      ⟪a, b⟫_ℝ = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
      Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) a ≤ M * ‖a‖ ^ 2 ∧
      Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) b ≤ M * ‖b‖ ^ 2 := by
  have hL2 : 0 < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨a, b, hae, hbe, hab, ha, hb⟩ := exists_even_pair_pos (Real.log_natCast_nonneg 2) hL2
  set Q₀ := Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg 2) 2 (Nat.clog 2 2) with hQ₀
  refine ⟨max (Q₀ a / ‖a‖ ^ 2) (Q₀ b / ‖b‖ ^ 2), ?_⟩
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hLL := Cvs.WeilForm.ApproxWindowPositivityRH.log_le_log_nat le_rfl hx
  have hnorm : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg 2),
      ‖Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD (Real.log_natCast_nonneg 2) (Real.log_natCast_nonneg x) hLL φ‖ = ‖φ‖ :=
    fun φ => Cvs.WeilForm.NestedWindowsMonotoneBottom.norm_embed (Real.log_natCast_nonneg 2) hLL φ
  have hne : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg 2), φ ≠ 0 →
      Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD (Real.log_natCast_nonneg 2) (Real.log_natCast_nonneg x) hLL φ ≠ 0 := by
    intro φ hφ h0
    have h1 : ‖φ‖ = 0 := by
      rw [← hnorm φ, h0]
      simp
    exact hφ (by simpa using h1)
  have hQ : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg 2), φ ≠ 0 → ∀ M : ℝ, Q₀ φ / ‖φ‖ ^ 2 ≤ M →
      Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD (Real.log_natCast_nonneg 2) (Real.log_natCast_nonneg x) hLL φ)
        ≤ M * ‖Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD (Real.log_natCast_nonneg 2) (Real.log_natCast_nonneg x) hLL φ‖ ^ 2 := by
    intro φ hφ M hM
    rw [Cvs.WeilForm.ApproxWindowPositivityRH.Q_embedD le_rfl hx, hnorm]
    have hp : 0 < ‖φ‖ ^ 2 := by exact pow_pos (by simpa using hφ) 2
    rwa [div_le_iff₀ hp] at hM
  refine ⟨Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD _ _ hLL a, Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD _ _ hLL b, ?_, ?_, ?_, hne a ha, hne b hb,
    hQ a ha _ (le_max_left _ _), hQ b hb _ (le_max_right _ _)⟩
  · rw [Cvs.WeilForm.NestedWindowsMonotoneBottom.reflD_embedD, hae]
  · rw [Cvs.WeilForm.NestedWindowsMonotoneBottom.reflD_embedD, hbe]
  · rw [inner_embedD, hab]

/-- **RH from `L1GapL` at infinitely many integers `x`**, for any bound `L` that is eventually nonnegative. -/
theorem riemannHypothesis_of_L1GapL_nearPos {L : ℕ → ℝ} (hL0 : ∀ᶠ x : ℕ in atTop, 0 ≤ L x)
    (h : ∃ᶠ x : ℕ in atTop, Cvs.Route.L1GapParametricRH.L1GapL L x) : RiemannHypothesis := by
  obtain ⟨M, hM⟩ := exists_even_pair
  refine Cvs.Route.L1GapCeilingRH.riemannHypothesis_of_L1GapL_of_pair (M := fun _ => M) hL0 hM ?_ h
  have hK : Tendsto (fun x : ℕ => √(x : ℝ) * Real.log x) atTop atTop := by
    refine Tendsto.atTop_mul_atTop₀ ?_ ?_
    · exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop hK

end Cvs.Route.L1GapNonnegRH
