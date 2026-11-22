import Mathlib
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Case ∞ split: a finite top set exists iff some off-line band is finite

A finite top set exists iff some off-line zero has finitely many zeros at least as deep, so the
`DepthToZero` hypothesis of Cvs.StepA.Edge.CorrectedPairingUSums/Cvs.Route.Visibility.ShareBesselFromExtPairing weakens to `TopAttained`; its failure is exactly `NoTop`,
off RH every off-line zero has infinitely many zeros at least as deep.
-/

noncomputable section

open Filter
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop)

namespace Cvs.StepA.Edge.FiniteTopIffFiniteBand
open Cvs.ZeroCounting

/-- The zeros at least as far from the critical line as `ρ₀`. -/
def deepBand (ρ₀ : nonTrivialZeroSet) : Set nonTrivialZeroSet :=
  {ρ | |Cvs.GaussKernel.del ρ₀| ≤ |Cvs.GaussKernel.del ρ|}

/-- **A finite top set exists iff some off-line zero has finitely many zeros at least as deep.** -/
theorem exists_finiteTop_iff :
    (∃ (S : Finset nonTrivialZeroSet) (δ : ℝ), FiniteTop S δ) ↔
      ∃ ρ₀ : nonTrivialZeroSet, Cvs.GaussKernel.del ρ₀ ≠ 0 ∧ (deepBand ρ₀).Finite := by
  classical
  constructor
  · rintro ⟨S, δ, hδ, ⟨σ, hσ⟩, hS, hout⟩
    refine ⟨σ, fun h0 => ?_, S.finite_toSet.subset fun ρ hρ => ?_⟩
    · have := hS σ hσ
      rw [h0, abs_zero] at this
      linarith
    · by_contra hn
      have h1 := hout ρ hn
      have h2 : |Cvs.GaussKernel.del σ| ≤ |Cvs.GaussKernel.del ρ| := hρ
      rw [hS σ hσ] at h2
      linarith
  · rintro ⟨ρ₀, h₀, hfin⟩
    have hε : 0 < |Cvs.GaussKernel.del ρ₀| := abs_pos.mpr h₀
    have hne : hfin.toFinset.Nonempty :=
      ⟨ρ₀, hfin.mem_toFinset.mpr (show |Cvs.GaussKernel.del ρ₀| ≤ |Cvs.GaussKernel.del ρ₀| from le_rfl)⟩
    obtain ⟨σ, hσ, hmax⟩ := hfin.toFinset.exists_max_image (fun ρ => |Cvs.GaussKernel.del ρ|) hne
    have hσε : |Cvs.GaussKernel.del ρ₀| ≤ |Cvs.GaussKernel.del σ| := hfin.mem_toFinset.mp hσ
    refine ⟨hfin.toFinset.filter fun ρ => |Cvs.GaussKernel.del ρ| = |Cvs.GaussKernel.del σ|,
      |Cvs.GaussKernel.del σ|, lt_of_lt_of_le hε hσε, ⟨σ, Finset.mem_filter.mpr ⟨hσ, rfl⟩⟩,
      fun ρ hρ => (Finset.mem_filter.mp hρ).2, fun ρ hρ => ?_⟩
    by_cases hin : ρ ∈ hfin.toFinset
    · exact lt_of_le_of_ne (hmax ρ hin) fun heq => hρ (Finset.mem_filter.mpr ⟨hin, heq⟩)
    · have : ¬ |Cvs.GaussKernel.del ρ₀| ≤ |Cvs.GaussKernel.del ρ| := fun h' =>
        hin (hfin.mem_toFinset.mpr h')
      exact (not_le.mp this).trans_le hσε

/-- Off RH, a finite top set exists (distinct from `Cvs.StepA.TopQuadruple.TopAttained`, which only asks for a deepest zero). -/
def TopAttained : Prop :=
  ¬ RiemannHypothesis → ∃ (S : Finset nonTrivialZeroSet) (δ : ℝ), FiniteTop S δ

/-- RH fails and every off-line zero has infinitely many zeros at least as deep. -/
def NoTop : Prop :=
  ¬ RiemannHypothesis ∧
    ∀ ρ₀ : nonTrivialZeroSet, Cvs.GaussKernel.del ρ₀ ≠ 0 → (deepBand ρ₀).Infinite

/-- `TopAttained` fails exactly in `NoTop`. -/
theorem not_topAttained_iff : ¬ TopAttained ↔ NoTop := by
  unfold TopAttained NoTop
  rw [exists_finiteTop_iff]
  constructor
  · intro h
    by_contra hc
    refine h fun hRH => ?_
    by_contra hn
    exact hc ⟨hRH, fun ρ₀ h₀ hfin => hn ⟨ρ₀, h₀, hfin⟩⟩
  · rintro ⟨hRH, hinf⟩ h
    obtain ⟨ρ₀, h₀, hfin⟩ := h hRH
    exact hinf ρ₀ h₀ hfin

/-! ### The deep-orthogonal bound, for any (possibly infinite) set of zeros -/

end Cvs.StepA.Edge.FiniteTopIffFiniteBand

end
