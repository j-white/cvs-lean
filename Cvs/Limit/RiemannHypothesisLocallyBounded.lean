import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.OffAxisSpineChosenConstants
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Upstream.MontelPlane

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# RH from local boundedness of the recentred family

Local boundedness of the normalised recentred transforms gives the Riemann Hypothesis, once every
subsequential limit is assumed to vanish wherever `Ξ` does off the coordinate axes: the spine
quantifies over the window lengths and truncations, so the subsequence such a family admits may be
handed back to it.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Set Filter

namespace Cvs.Limit.RiemannHypothesisLocallyBounded
open Cvs.ZeroCounting

/-- **RH from boundedness and a subsequential limit that sees the off-axis zeros of `Ξ`**, on the
recentred normalised family. -/
theorem riemannHypothesis_of_bdd_sees {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ) {w₀ : ℂ}
    (hw₀ : w₀ ∈ Cvs.Limit.OffAxesLimit.offAxes)
    (hbd : ∀ r : ℝ, ∃ M : ℝ, ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ r →
      ‖Cvs.Limit.OffAxisSpineChosenConstants.cnorm (P n) (R n) (hL n) (N n) w₀
        * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z‖ ≤ M)
    (hSees : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ f : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun k z => Cvs.Limit.OffAxisSpineChosenConstants.cnorm (P (φ k)) (R (φ k)) (hL (φ k)) (N (φ k)) w₀
          * Cvs.Finite.RecentredTransform.cgtransform (P (φ k)) (R (φ k)) (hL (φ k)) (N (φ k)) z)
        f atTop Cvs.Limit.OffAxesLimit.offAxes →
      ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, Cvs.Limit.ZeroFreeApproximantsRH.Xi z = 0 → f z = 0) :
    RiemannHypothesis := by
  have hd : ∀ n : ℕ, Differentiable ℂ (fun z =>
      Cvs.Limit.OffAxisSpineChosenConstants.cnorm (P n) (R n) (hL n) (N n) w₀
        * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z) :=
    fun n => (differentiable_const _).mul
      (Cvs.Finite.RecentredTransform.differentiable_cgtransform (P n) (R n) (hL n) (N n))
  obtain ⟨φ, f, hφ, hconv⟩ :=
    Cvs.Upstream.MontelPlane.exists_subseq_tendstoLocallyUniformlyOn hd hbd
  have hconv' := hconv.mono (subset_univ Cvs.Limit.OffAxesLimit.offAxes)
  exact Cvs.Limit.OffAxisSpineChosenConstants.riemannHypothesis_of_ground_centred_offAxes_conv
    (L := L ∘ φ) (fun k => hL (φ k)) (P ∘ φ) (R ∘ φ) (N ∘ φ) f hw₀ hconv'
    (hSees φ hφ f hconv')

end Cvs.Limit.RiemannHypothesisLocallyBounded
