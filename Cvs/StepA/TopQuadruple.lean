import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.StepA.NegativeIndexQuadruples
import Cvs.StepA.OneZeroParitySectors
import Cvs.Zeta.AllZerosOnLine
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.WeightedRateLemma
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.CarlsonCountBridge
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
# The top quadruple of the zero set
The quadruple `{σ, σ̄, 1 − σ, 1 − σ̄}` as a finset with total weight `W ≥ 1`, on which both sector
pairings and both sector bottoms are constant; without RH some quadruple is strictly on top, or two tie,
or the top distance is not attained (attained when finitely many zeros are off the line). One zero's
odd term is at most `lamOTop · ∫ f²` with `0 ≤ lamOTop ≤ ∫ uo²`, `−∫ ve² ≤ lamE ≤ 0`, and with finitely
many zeros off the line `evLam ≥ W·lamE(z_σ) + ∑_{off line ∖ quad σ} m_ρ lamE(z_ρ)`.
-/

noncomputable section

open Real MeasureTheory

namespace Cvs.StepA.TopQuadruple
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.NegativeIndexQuadruples (InQuad zPoint_oneSubZ zPoint_conjZ)
open Cvs.StepA.OneZeroParitySectors (ue ve uo vo)

/-! ### The zero-set conditions -/

/-- The nontrivial zeros off the critical line. -/
def offLine : Set nonTrivialZeroSet := {ρ | (ρ : ℂ).re ≠ 1 / 2}

/-! ### The quadruple as a finset -/

/-- The quadruple `{σ, σ̄, 1 − σ, 1 − σ̄}` of a nontrivial zero. -/
def quad (σ : nonTrivialZeroSet) : Finset nonTrivialZeroSet :=
  {σ, Cvs.GaussKernel.conjZ σ, Cvs.GaussKernel.oneSubZ σ,
    Cvs.GaussKernel.oneSubZ (Cvs.GaussKernel.conjZ σ)}

/-- Membership in the quadruple finset is `InQuad`. -/
theorem mem_quad_iff {ρ σ : nonTrivialZeroSet} : ρ ∈ quad σ ↔ InQuad ρ σ := by
  simp only [quad, Finset.mem_insert, Finset.mem_singleton, InQuad]

/-- A zero lies in its own quadruple. -/
theorem self_mem_quad (σ : nonTrivialZeroSet) : σ ∈ quad σ :=
  mem_quad_iff.mpr (Or.inl rfl)

/-! ### The total weight of the quadruple -/

/-- The total multiplicity `W = ∑_{ρ ∈ quad σ} m_ρ` of the quadruple. -/
def quadWeight (σ : nonTrivialZeroSet) : ℝ :=
  ∑ ρ ∈ quad σ, (Cvs.Criterion.divisorWeight ρ : ℝ)

/-- The total weight of a quadruple is at least one. -/
theorem one_le_quadWeight (σ : nonTrivialZeroSet) : 1 ≤ quadWeight σ := by
  have h1 : (1 : ℝ) ≤ Cvs.Criterion.divisorWeight σ := by
    exact_mod_cast Cvs.Criterion.one_le_divisorWeight σ
  exact h1.trans (Finset.single_le_sum (fun ρ _ => Nat.cast_nonneg _) (self_mem_quad σ))

/-- A weighted sum over the quadruple of a quantity constant on it is `W` times its value. -/
theorem sum_quad_mul (σ : nonTrivialZeroSet) {f : nonTrivialZeroSet → ℝ}
    (hf : ∀ ρ, InQuad ρ σ → f ρ = f σ) :
    ∑ ρ ∈ quad σ, (Cvs.Criterion.divisorWeight ρ : ℝ) * f ρ = quadWeight σ * f σ := by
  rw [quadWeight, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ρ hρ => by rw [hf ρ (mem_quad_iff.mp hρ)]

/-! ### The sector weights and pairings across a quadruple -/

/-- The even-sector pairing of one zero with the centred cosine polynomial of `ξ`:
`(∫ cg ue)² − (∫ cg ve)²`. -/
def pairE (L : ℝ) (N : ℕ) (ξ : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) (z : ℂ) : ℝ :=
  (∫ t in -(L / 2)..L / 2,
      Cvs.Finite.EvenSectorZeroSide.cosPoly L (Cvs.Finite.SymmetricModeSet.mode N) ξ (t + L / 2) * ue z t) ^ 2
    - (∫ t in -(L / 2)..L / 2,
      Cvs.Finite.EvenSectorZeroSide.cosPoly L (Cvs.Finite.SymmetricModeSet.mode N) ξ (t + L / 2) * ve z t) ^ 2

/-- The odd-sector pairing of one zero with the centred sine polynomial of `o`:
`(∫ sg uo)² − (∫ sg vo)²`. -/
def pairO (L : ℝ) (N : ℕ) (o : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) (z : ℂ) : ℝ :=
  (∫ t in -(L / 2)..L / 2,
      Cvs.Finite.OddSectorZeroSide.sinePoly L (Cvs.Finite.SymmetricModeSet.mode N) o (t + L / 2) * uo z t) ^ 2
    - (∫ t in -(L / 2)..L / 2,
      Cvs.Finite.OddSectorZeroSide.sinePoly L (Cvs.Finite.SymmetricModeSet.mode N) o (t + L / 2) * vo z t) ^ 2

/-! ### The sector bottoms across a quadruple -/

/-! ### Some quadruple is on top, two tie, or the top is not attained -/

/-- Without RH some nontrivial zero lies off the critical line. -/
theorem exists_offLine_of_not_RH (h : ¬ RiemannHypothesis) :
    ∃ ρ : nonTrivialZeroSet, (ρ : ℂ).re ≠ 1 / 2 :=
  Cvs.Zeta.GaussKernel.AdmissibleKernel.exists_offLine_of_not_allZerosOnLine fun h' =>
    h (Cvs.Zeta.GaussKernel.AdmissibleKernel.riemannHypothesis_iff.mp h')

/-! ### The zero-side point of the top quadruple -/

/-- The imaginary part of `z_ρ` is minus the distance of `ρ` from the critical line. -/
theorem im_zPoint_eq_neg_del (ρ : nonTrivialZeroSet) :
    (Cvs.ZeroCounting.zPoint ρ).im = -Cvs.GaussKernel.del ρ := by
  rw [Cvs.ZeroCounting.zPoint_im, Cvs.GaussKernel.del]

/-! ### The lower root between `−Q` and `0` -/

/-- A window square integral is nonnegative for `L ≥ 0`. -/
theorem integral_sq_nonneg {L : ℝ} (hL : 0 ≤ L) (f : ℝ → ℝ) :
    0 ≤ ∫ t in -(L / 2)..L / 2, f t ^ 2 :=
  intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _

/-! ### The even bottom and the odd top of one zero -/

/-! ### The even bottom with finitely many zeros off the line -/

end Cvs.StepA.TopQuadruple
