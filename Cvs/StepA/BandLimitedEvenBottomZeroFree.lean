import Mathlib
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.SymmetricModeSet
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TopSetCriterion
import Cvs.StepA.TopQuadruple
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiStripZetaHalfPlane
import Cvs.Zeta.ZeroSetsAgree
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band-limited even bottom from a zero-free half-plane

If every zero of `ξ` has real part at most `θ`, every zero is within `θ − 1/2` of the critical line, so the
envelope of the zeros off the line is `o(e^{δL})` for each `δ > θ − 1/2` (Cvs.StepA.RestEnvelopeSmall). With Cvs.StepA.Edge.TopSetCriterion at the empty band, the
even bottom of the window's `N(L)`-mode block, `N(L) = O(L)`, is then at least `−ε e^{δL}` for large `L`, for every
`ε > 0`; at `θ = 7/8` this holds for every `δ > 3/8`.
-/

noncomputable section

open Real Filter Topology Asymptotics

namespace Cvs.StepA.BandLimitedEvenBottomZeroFree
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.TopQuadruple (offLine)
open Cvs.StepA.Edge.TopSetCriterion (bandBotE bandRayE restE)
open Cvs.Zeta.XiStripZetaHalfPlane (ZetaFreeAbove)

/-- **Every zero within `θ − 1/2` of the line**: if every zero of `ξ` has real part at most `θ`, every
nontrivial zero has `|Re ρ − 1/2| ≤ θ − 1/2`. -/
theorem abs_del_le {θ : ℝ} (h : ∀ ρ : ℂ, Cvs.Zeta.riemannXi ρ = 0 → ρ.re ≤ θ) (ρ : nonTrivialZeroSet) :
    |Cvs.GaussKernel.del ρ| ≤ θ - 1 / 2 := by
  have hξ := Cvs.Zeta.ZeroIndex.riemannXi_apply_eq_zero ρ
  have h1 := h _ hξ
  have h2 := Cvs.Zeta.XiStripZetaHalfPlane.one_sub_le_re h hξ
  rw [Cvs.GaussKernel.del, abs_le]
  constructor <;> linarith

/-- The even band bottom of the empty set of zeros is nonnegative. -/
theorem bandBotE_empty_nonneg (L : ℝ) (N : ℕ) : 0 ≤ bandBotE L N ∅ := by
  refine Real.sInf_nonneg fun r hr => ?_
  obtain ⟨ξ, -, -, rfl⟩ := hr
  simp

/-- **The even bottom against all the zeros off the line**: for `L > 0`,
`−∑'_{off line} m_ρ envE(L, N, z_ρ) ≤ evLam`. -/
theorem neg_restE_le_evLam {L : ℝ} (hL : 0 < L) (N : ℕ) :
    -restE L N ∅ ≤ Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  have h := Cvs.StepA.Edge.TopSetCriterion.evLam_ge_band hL N (Set.empty_subset offLine)
  linarith [bandBotE_empty_nonneg L N]

end Cvs.StepA.BandLimitedEvenBottomZeroFree
