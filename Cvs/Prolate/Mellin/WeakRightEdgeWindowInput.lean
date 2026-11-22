import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.Envelope.RungProfileEdgePlunge
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.RungTransformUnitCircle
import Cvs.Prolate.Mellin.RungUnitCircleLaw
import Cvs.Prolate.Mellin.RungWindowLawCircleEdge
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.MOnePrimeTopDepth
import Cvs.Route.Visibility.WindowLaplaceUPairing
import Cvs.Route.Visibility.WindowLogEnergyCellFloor

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window input from the weak right-edge law `g‖B‖ ≤ W(x)(1 − λ_{4j})^{1/4}`

With `G = 1`, `C₁ = 4e⁶E_j` and `C₂ = W(1 − λ)^{1/4}√x`, `RungWindowLawRightEdge`'s fixed-scale bound and `E_j² ≤ P x (1 − λ)^{3/4}`
give `WinTailProfile 0`, so hV holds with the weak law in place of `EdgeLawSum`, which implies it.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Prolate.Mellin.RungTransformUnitCircle (Aw Bw)
open Cvs.Prolate.Mellin.RungWindowLawCircleEdge (subPoly_max winQ fixed_rhs_eq)

namespace Cvs.Prolate.Mellin.WeakRightEdgeWindowInput
open Cvs.ZeroCounting

/-- **The weak right-edge law**: some subpolynomial `W` has, at all large `x`, for every rung, `|σ| ≤ 1` and
`g ≥ 8πx`, `g‖B(σ + ig)‖ ≤ W(x)(1 − λ_{4j})^{1/4}`. -/
def WeakEdgeLaw : Prop :=
  ∃ W : ℕ → ℝ, SubPoly W ∧ ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, ∀ σ : ℝ, |σ| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g →
    g * ‖Bw x j (σ + g * I)‖ ≤ W x * (1 - lamR (2 * π * x) (2 * (j : ℕ))) ^ (1 / 4 : ℝ)

/-- `(ω^{1/4})² = ω^{1/2}`. -/
theorem rpow_quarter_sq {ω : ℝ} (hω : 0 ≤ ω) : (ω ^ (1 / 4 : ℝ)) ^ 2 = ω ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hω]; norm_num

/-- `ω^{3/4} ≤ ω^{1/2}` on `[0, 1]`. -/
theorem rpow_three_quarter_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) : ω ^ (3 / 4 : ℝ) ≤ ω ^ (1 / 2 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_ge' hω0 hω1 (by norm_num) (by norm_num)

/-- `E/√x ≤ (1 + P)ω^{1/4}` from `E² ≤ P·x·ω^{3/4}`, `0 ≤ ω ≤ 1`. -/
theorem div_sqrt_le {x E P ω : ℝ} (hx0 : 0 < x) (hE : 0 ≤ E) (hP : 0 ≤ P) (hω0 : 0 ≤ ω)
    (hω1 : ω ≤ 1) (h : E ^ 2 ≤ P * x * ω ^ (3 / 4 : ℝ)) : E / √x ≤ (1 + P) * ω ^ (1 / 4 : ℝ) := by
  have hs : 0 < √x := Real.sqrt_pos.2 hx0
  have hr0 : 0 ≤ ω ^ (1 / 4 : ℝ) := Real.rpow_nonneg hω0 _
  have hh0 : 0 ≤ ω ^ (1 / 2 : ℝ) := Real.rpow_nonneg hω0 _
  rw [div_le_iff₀ hs]
  have hsq : E ^ 2 ≤ ((1 + P) * ω ^ (1 / 4 : ℝ) * √x) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hx0.le, rpow_quarter_sq hω0]
    calc E ^ 2 ≤ P * x * ω ^ (3 / 4 : ℝ) := h
      _ ≤ P * x * ω ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (rpow_three_quarter_le hω0 hω1) (by positivity)
      _ ≤ (1 + P) ^ 2 * ω ^ (1 / 2 : ℝ) * x := by
          have h1 : P ≤ (1 + P) ^ 2 := by nlinarith
          have h2 : 0 ≤ ω ^ (1 / 2 : ℝ) * x := by positivity
          nlinarith
  exact (pow_le_pow_iff_left₀ hE (by positivity) two_ne_zero).1 hsq

/-- `0 ≤ P(x)` for `RungProfileEdgePlunge`'s edge factor. -/
theorem edgeP_nonneg (x : ℕ) : 0 ≤ Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x := by
  unfold Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP Cvs.Prolate.Envelope.RungProfileEdgePlunge.depthQ
  have hK := Cvs.Prolate.Envelope.RungProfileEdgePlunge.one_le_K₁
  have hl : 0 ≤ Real.log (Cvs.Prolate.Envelope.RungProfileEdgePlunge.K₁ * (2 * π * x)) := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp
    · have hx : (1 : ℝ) ≤ x := by exact_mod_cast h
      have h2 : (1 : ℝ) ≤ 2 * π * x := by nlinarith [Real.pi_gt_three]
      exact Real.log_nonneg (by nlinarith)
  positivity

/-- **The per-rung window log-tail law at exponent `½` from the weak right-edge law**. -/
theorem winTailProfile_zero_of_weakEdgeLaw (hW : WeakEdgeLaw) : Cvs.Route.Visibility.WindowLogEnergyCellFloor.WinTailProfile 0 := by
  obtain ⟨W, hWs, hW⟩ := hW
  set W' : ℕ → ℝ := fun x => max (W x) 0 with hW'
  have hW's : SubPoly W' := subPoly_max hWs
  set C₁ : ℝ := 4 * Real.exp 6 with hC₁
  refine ⟨fun x => Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x * winQ C₁ 0 (Real.log x) + 2 / π * W' x ^ 2, ?_, ?_⟩
  · have hL : SubPoly fun x : ℕ => 1 + Real.log x := (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 1).add Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log
    have hL0 : ∀ᶠ x : ℕ in atTop, 0 ≤ 1 + Real.log x :=
      Eventually.of_forall fun x => by have := Real.log_natCast_nonneg x; linarith
    have h1 : SubPoly fun x : ℕ => 1 / (2 * π) + (1 + Real.log x) / (8 * π ^ 2) := by
      refine (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).add ?_
      have := (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (1 / (8 * π ^ 2))).mul hL (Eventually.of_forall fun _ => by positivity) hL0
      simpa [div_eq_inv_mul, mul_comm] using this
    have hQ : SubPoly fun x : ℕ => winQ C₁ 0 (Real.log x) := by
      unfold winQ
      refine ((((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (8 * C₁ ^ 2)).mul hL
        (Eventually.of_forall fun _ => by positivity) hL0).mul h1
        (Eventually.of_forall fun x => by have := Real.log_natCast_nonneg x; positivity)
        (Eventually.of_forall fun x => by have := Real.log_natCast_nonneg x; positivity)).add
        (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (2 / π * 0 ^ 2))).mono (Eventually.of_forall fun x => le_of_eq (by ring))
    have hQ0 : ∀ x : ℕ, 0 ≤ winQ C₁ 0 (Real.log x) := fun x => by
      unfold winQ; have := Real.log_natCast_nonneg x; positivity
    have hW2 : SubPoly fun x => W' x ^ 2 := by
      have := hW's.mul hW's (Eventually.of_forall fun _ => le_max_right _ _)
        (Eventually.of_forall fun _ => le_max_right _ _)
      simpa [sq] using this
    exact (Cvs.Prolate.Envelope.RungProfileEdgePlunge.subPoly_edgeP.mul hQ (Eventually.of_forall edgeP_nonneg) (Eventually.of_forall hQ0)).add
      ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const (2 / π)).mul hW2 (Eventually.of_forall fun _ => by positivity)
        (Eventually.of_forall fun _ => sq_nonneg _))
  · filter_upwards [hW, Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE_sq_le, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hWx hEx hx σ hσ j
    have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
    have hσ' : |-σ| ≤ 1 := by rwa [abs_neg]
    have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
    have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj).1
    have hc0 : (0 : ℝ) < 2 * π * x := by positivity
    have hl1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 h1
    have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj
    set ω := 1 - lamR (2 * π * x) (2 * (j : ℕ)) with hωd
    have hω0 : 0 ≤ ω := by rw [hωd]; linarith
    have hω1 : ω ≤ 1 := by rw [hωd]; linarith
    have hE0 := Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE_nonneg x j
    set E := Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j with hEd
    set C₂ : ℝ := W' x * ω ^ (1 / 4 : ℝ) * √(x : ℝ) with hC₂
    have hs : 0 < √(x : ℝ) := Real.sqrt_pos.2 hx0
    have upA : ∀ s : ℝ, |s| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g → g * ‖Aw x j (s + g * I)‖ ≤ C₁ * E * |(1 : ℝ)| :=
      fun s hs' g hg => by rw [abs_one, mul_one]; exact Cvs.Prolate.Mellin.RungUnitCircleLaw.g_norm_Aw_le hx hj hs' hg
    have upB : ∀ s : ℝ, |s| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g →
        g * ‖Bw x j (s + g * I)‖ ≤ C₂ * |(1 : ℝ)| / √(x : ℝ) := fun s hs' g hg => by
      rw [abs_one, mul_one, hC₂, mul_div_assoc, div_self hs.ne', mul_one]
      refine (hWx j s hs' g hg).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hω0 _)
    obtain ⟨hI, hle⟩ := Cvs.Prolate.Mellin.RungWindowLawRightEdge.winTail_le_fixed hx j σ (upA σ hσ) (upB σ hσ) (upA (-σ) hσ') (upB (-σ) hσ')
    refine ⟨hI, hle.trans ?_⟩
    rw [fixed_rhs_eq hx0]
    have hE2 : E ^ 2 ≤ Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x * x * ω ^ (1 / 2 : ℝ) :=
      (hEx j hj).trans (mul_le_mul_of_nonneg_left (rpow_three_quarter_le hω0 hω1)
        (mul_nonneg (edgeP_nonneg x) hx0.le))
    have hxs : 0 ≤ (x : ℝ) ^ |σ| := Real.rpow_nonneg hx0.le _
    have hh0 : 0 ≤ ω ^ (1 / 2 : ℝ) := Real.rpow_nonneg hω0 _
    have hC₂sq : C₂ ^ 2 = W' x ^ 2 * ω ^ (1 / 2 : ℝ) * x := by
      rw [hC₂, mul_pow, mul_pow, rpow_quarter_sq hω0, Real.sq_sqrt hx0.le]
    have hQ : winQ (C₁ * E) C₂ (Real.log x)
        ≤ x * ω ^ (1 / 2 : ℝ) * (Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x * winQ C₁ 0 (Real.log x) + 2 / π * W' x ^ 2) := by
      unfold winQ
      rw [hC₂sq]
      have hL : 0 ≤ 1 + Real.log x := by have := Real.log_natCast_nonneg x; linarith
      have hA : 0 ≤ 8 * (1 + Real.log x) * (1 / (2 * π) + (1 + Real.log x) / (8 * π ^ 2)) := by positivity
      have hC1 : 0 ≤ C₁ ^ 2 := sq_nonneg _
      calc 8 * (C₁ * E) ^ 2 * (1 + Real.log x) * (1 / (2 * π) + (1 + Real.log x) / (8 * π ^ 2))
            + 2 / π * (W' x ^ 2 * ω ^ (1 / 2 : ℝ) * x)
          = C₁ ^ 2 * (8 * (1 + Real.log x) * (1 / (2 * π) + (1 + Real.log x) / (8 * π ^ 2))) * E ^ 2
            + 2 / π * (W' x ^ 2 * ω ^ (1 / 2 : ℝ) * x) := by ring
        _ ≤ C₁ ^ 2 * (8 * (1 + Real.log x) * (1 / (2 * π) + (1 + Real.log x) / (8 * π ^ 2)))
              * (Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x * x * ω ^ (1 / 2 : ℝ))
            + 2 / π * (W' x ^ 2 * ω ^ (1 / 2 : ℝ) * x) := by gcongr
        _ = _ := by ring
    have hone : ω ^ (1 / 2 + 0 : ℝ) = ω ^ (1 / 2 : ℝ) := by norm_num
    rw [hone, one_pow, mul_one]
    calc (x : ℝ) ^ |σ| / x ^ 2 * winQ (C₁ * E) C₂ (Real.log x)
        ≤ (x : ℝ) ^ |σ| / x ^ 2 * (x * ω ^ (1 / 2 : ℝ)
            * (Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x * winQ C₁ 0 (Real.log x) + 2 / π * W' x ^ 2)) := by gcongr
      _ = (Cvs.Prolate.Envelope.RungProfileEdgePlunge.edgeP x * winQ C₁ 0 (Real.log x) + 2 / π * W' x ^ 2) * (x : ℝ) ^ |σ| * (1 / x)
            * ω ^ (1 / 2 : ℝ) := by field_simp

/-- **The window input from the weak right-edge law**. -/
theorem winInput_of_weakEdgeLaw (hW : WeakEdgeLaw) :
    (∃ ν < 1, Cvs.Route.Visibility.MOnePrimeTopDepth.WinLogReg ν) ∨ ∃ η' ≥ 0, Cvs.Route.Visibility.WindowLogEnergyCellFloor.WinTailProfile η' :=
  Or.inr ⟨0, le_rfl, winTailProfile_zero_of_weakEdgeLaw hW⟩

end Cvs.Prolate.Mellin.WeakRightEdgeWindowInput

end
