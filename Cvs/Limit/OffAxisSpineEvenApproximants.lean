import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The off-axis spine with evenness carried by the approximants

A locally uniform limit of functions even on a set closed under negation is even there, so the
recentred spine off the axes takes the evenness of its limit from `Cvs.Finite.RecentredTransformEven` rather than as a
hypothesis, leaving the conjugation symmetry the only condition on the limit's shape.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Limit.OffAxisSpineEvenApproximants


/-- **A locally uniform limit of even functions is even**, on a set closed under negation. -/
theorem eq_neg_of_tendsto {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (hconv : TendstoLocallyUniformlyOn F f atTop s)
    (hs : ∀ z ∈ s, -z ∈ s) (hF : ∀ n, ∀ z ∈ s, F n (-z) = F n z)
    {z : ℂ} (hz : z ∈ s) : f (-z) = f z := by
  have h1 := hconv.tendsto_at (hs z hz)
  have h2 := hconv.tendsto_at hz
  have heq : (fun n => F n (-z)) = fun n => F n z := funext fun n => hF n z hz
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end Cvs.Limit.OffAxisSpineEvenApproximants
