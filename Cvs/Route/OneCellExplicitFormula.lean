import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.Route.DilationLatticeCriterion
import Cvs.Route.NestedBoxFrequenciesReal
import Cvs.Route.OneCellBoxWindowForm
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.ConcreteTestIdentification
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.WindowSetNonempty
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.FirstZeroHeightBound
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The explicit formula for the one-cell function
`G(L) = ∑_ρ m_ρ Re[4 sin²(z_ρ L/2)/z_ρ²]`, `z_ρ = zPoint ρ`: the box is the constant cosine mode, so `ZeroSideGramMatrix`'s
zero side applies, Cvs.Route.OneCellBoxWindowForm evaluates its Weil form as `G(L)`, and Cvs.Finite.UniversalFunctionPairing its square transform; `z_ρ ≠ 0` because
`ξ` has no zero with `|Im| ≤ 5.5` (Cvs.Zeta.FirstZeroHeightBound). With Cvs.Route.NestedBoxFrequenciesReal: RH ↔ every frequency is real, unconditionally.
-/

noncomputable section

open Real

namespace Cvs.Route.OneCellExplicitFormula
open Cvs.ZeroCounting

open Cvs.Route.OneCellLaplaceTransform (G)

/-- No zero's point vanishes: `Re zPoint ρ = Im ρ` and `|Im ρ| > 5.5`. -/
theorem zPoint_ne_zero (ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet) : Cvs.ZeroCounting.zPoint ρ ≠ 0 := by
  obtain ⟨hz, h0, h1⟩ := ρ.2
  have hne1 : (ρ : ℂ) ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hξ : Cvs.Zeta.riemannXi (ρ : ℂ) = 0 := (Cvs.Zeta.riemannXi_eq_zero_iff_riemannZeta h0 hne1).2 hz
  have him := Cvs.Zeta.FirstZeroHeightBound.abs_im_gt_of_riemannXi_eq_zero hξ
  intro hzero
  have hre : (Cvs.ZeroCounting.zPoint ρ).re = ((ρ : ℂ)).im := Cvs.Finite.ZeroSideGramMatrix.zPoint_re ρ
  rw [hzero, Complex.zero_re] at hre
  rw [← hre, abs_zero] at him
  linarith

/-- The constant mode. -/
def mode0 : Unit → ℤ := fun _ => 0
def xi1 : Unit → ℝ := fun _ => 1

theorem modeSum_eq_flat (L : ℝ) : Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L mode0 xi1 = Cvs.WeilForm.WindowSetNonempty.flat L := by
  funext y
  unfold Cvs.Finite.TruncationZeroFreeOffAxes.modeSum Cvs.WeilForm.WindowSetNonempty.flat
  by_cases hy : y ∈ Set.Ioc (0:ℝ) L
  · simp [hy, mode0, xi1, Cvs.Finite.TruncationZeroFreeOffAxes.omega]
  · simp [hy]

/-- The box's square transform at a nonzero point: `4 sin²(zL/2)/z²`. -/
theorem sqTransform_box {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z ≠ 0) :
    Cvs.Detection.sqTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode0 xi1)) z
      = 4 * (Complex.sin (z * L / 2) ^ 2 / z ^ 2) := by
  have hgen : ∀ k, ((2 * π * mode0 k / L : ℝ) : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    intro k; simp [mode0]; exact hz
  rw [Cvs.Finite.UniversalFunctionPairing.sqTransform_cosPoly_eq hL mode0 xi1 hgen]
  unfold Cvs.Finite.UniversalFunctionPairing.S
  simp only [mode0, xi1, Finset.univ_unique, Finset.sum_singleton, Int.cast_zero, mul_zero, zero_div,
    Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub, Complex.ofReal_one]
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  rw [show (L : ℂ) * z / 2 = z * L / 2 by ring]
  field_simp

/-- **The explicit formula for the one-cell function**, unconditionally. -/
theorem zeroSideG : Cvs.Route.NestedBoxFrequenciesReal.ZeroSideG := by
  intro L hL
  rcases hL.lt_or_eq with hL | hL
  · have hP := Cvs.WeilForm.ConcreteTestIdentification.le_ceil_exp L
    have hR := Cvs.WeilForm.ConcreteTestIdentification.le_ceil_log L
    rw [← Cvs.Route.OneCellBoxWindowForm.weilForm_flat_eq hL hP hR, ← modeSum_eq_flat]
    have hinv : Function.Involutive (id : Unit → Unit) := fun _ => rfl
    rw [← Cvs.Finite.ZeroSideGramMatrix.zeroSide_modeSum hL mode0 hinv (fun _ => by simp [mode0]) (fun _ => rfl) 0 0]
    unfold Cvs.ZeroCounting.kernelZeroSide
    refine tsum_congr fun ρ => ?_
    rw [sqTransform_box hL (zPoint_ne_zero ρ)]
  · subst hL
    rw [Cvs.Route.DilationLatticeCriterion.G_zero]
    symm
    refine (tsum_congr fun ρ => ?_).trans tsum_zero
    simp

/-- **RH is the reality of the frequencies**, unconditionally. -/
theorem rh_iff_frequenciesReal : RiemannHypothesis ↔ Cvs.Route.NestedBoxFrequenciesReal.FrequenciesReal :=
  Cvs.Route.NestedBoxFrequenciesReal.rh_iff_frequenciesReal zeroSideG

end Cvs.Route.OneCellExplicitFormula
