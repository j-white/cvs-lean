import Mathlib
import Cvs.Finite.EvenBilinearZeroSide
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.TopQuadruple
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The parity sectors around the top quadruple, one scale
At one `(L, N)`, `L·vᵀ M_L v` on each sector is `W` times the pairing at `z_σ`, plus the zeros off the
line outside `quad σ`, plus the zeros on the line. An even rest bound `E_e` gives `W·lamE − E_e ≤ evLam`;
with an odd rest bound `E_o`, `0 ≤ E_e + E_o` and `W·trialBound + E_o + onLineBound < W·lamE − E_e`,
`OddAbove` fails. With finitely many zeros off the line both rests are finite sums of `lamE`, `lamOTop`.
-/

noncomputable section

open Real MeasureTheory Matrix

namespace Cvs.StepA.QuadrupleParitySectors
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI mode_injective negI_involutive mode_negI)
open Cvs.StepA.OneZeroParitySectors (ue ve)
open Cvs.StepA.TopQuadruple (offLine quad quadWeight pairE pairO)

/-! ### Splitting a sum over the zeros -/

/-! ### The rest of the zero set, in each sector -/

/-- For `L > 0` and every `ξ`, `m_ρ · pairE L N ξ (z_ρ)` is summable over the zeros. -/
theorem summable_pairE {L : ℝ} (hL : 0 < L) (N : ℕ) (ξ : Idx N → ℝ) :
    Summable fun ρ : nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := by
  refine (Cvs.Finite.EvenBilinearZeroSide.summable_zeroSide_cosPoly hL (mode N) ξ).congr fun ρ => ?_
  have hcont : Continuous fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) :=
    (Cvs.Finite.EvenSectorZeroSide.continuous_cosPoly L (mode N) ξ).comp (continuous_add_const _)
  have e := Cvs.StepA.OneZeroParitySectors.re_sqTransform_of_even L
    (g := fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2))
    (hcont.intervalIntegrable _ _) (Cvs.StepA.OneZeroParitySectors.cosPoly_centred_neg hL.ne' (mode N) ξ)
    (Cvs.ZeroCounting.zPoint ρ)
  have hfun : (fun s => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (s - L / 2 + L / 2))
      = Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ := by
    funext s; rw [sub_add_cancel]
  simp only [hfun] at e
  rw [e]
  rfl

/-- For `L > 0` and every `o`, `m_ρ · pairO L N o (z_ρ)` is summable over the zeros. -/
theorem summable_pairO {L : ℝ} (hL : 0 < L) (N : ℕ) (o : Idx N → ℝ) :
    Summable fun ρ : nonTrivialZeroSet =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * pairO L N o (Cvs.ZeroCounting.zPoint ρ) := by
  refine (Cvs.Finite.ParitySectorDefect.summable_zeroSide_sine hL (mode N) o).congr fun ρ => ?_
  have hcont : Continuous fun t => Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2) :=
    (Cvs.Finite.OddSectorZeroSide.continuous_sinePoly L (mode N) o).comp (continuous_add_const _)
  have e := Cvs.StepA.OneZeroParitySectors.re_sqTransform_of_odd L
    (g := fun t => Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (t + L / 2))
    (hcont.intervalIntegrable _ _) (Cvs.StepA.OneZeroParitySectors.sinePoly_centred_neg hL.ne' (mode N) o)
    (Cvs.ZeroCounting.zPoint ρ)
  have hfun : (fun s => Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o (s - L / 2 + L / 2))
      = Cvs.Finite.OddSectorZeroSide.sinePoly L (mode N) o := by
    funext s; rw [sub_add_cancel]
  simp only [hfun] at e
  rw [e]
  rfl

/-! ### Each sector split around the quadruple -/

/-! ### The odd sector from above -/

/-! ### The even sector from below -/

/-! ### The pointwise criterion -/

/-! ### Finitely many zeros off the line -/

end Cvs.StepA.QuadrupleParitySectors
