import Mathlib
import Cvs.Prolate.CrossRungPhasePair

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A window pair in Prüfer form, as an interval integral

The window `{k/m′ ≤ θ < k/m} ∩ (1, b]` of Cvs.L2a.TailEdgeFarSplit is almost everywhere the interval from `max 1 (k/m′)` to
`min b (k/m)`, so its integral is an interval integral; on it a rung pair in Prüfer form is the amplitude product
against the difference and the sum phase, and any bounds `Ed`, `Es` on the two oscillatory integrals bound the
window pair by `Ed + Es`: the envelope `E(i, j, m, m′)` of an earlier result is a difference-phase bound plus a sum-phase bound.
-/

namespace Cvs.Prolate.PruferWindowPair

open Real Set MeasureTheory intervalIntegral
open Cvs.Prolate.CrossRungPhasePair

/-- **A rung pair in Prüfer form on an interval**: with `ψᵢ = Aᵢ cos Θᵢ`, `ψⱼ = Aⱼ cos Θⱼ` on the relevant ranges,
bounds `Ed`, `Es` on the amplitude product against the difference and the sum phase bound the pair by `Ed + Es`. -/
theorem pair_interval_le {ψi ψj Ai Aj Θi Θj : ℝ → ℝ} {m m' p q Ed Es : ℝ} (hpq : p ≤ q)
    (hi : ∀ t ∈ Icc p q, ψi (m * t) = Ai (m * t) * Real.cos (Θi (m * t)))
    (hj : ∀ t ∈ Icc p q, ψj (m' * t) = Aj (m' * t) * Real.cos (Θj (m' * t)))
    (hId : IntervalIntegrable
      (fun t => Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) - Θj (m' * t))) volume p q)
    (hIs : IntervalIntegrable
      (fun t => Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) + Θj (m' * t))) volume p q)
    (hd : |∫ t in p..q, Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) - Θj (m' * t))| ≤ Ed)
    (hs : |∫ t in p..q, Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) + Θj (m' * t))| ≤ Es) :
    |∫ t in p..q, ψi (m * t) * ψj (m' * t)| ≤ Ed + Es := by
  have e : ∫ t in p..q, ψi (m * t) * ψj (m' * t)
      = (∫ t in p..q, Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) - Θj (m' * t)))
        + ∫ t in p..q, Ai (m * t) * Aj (m' * t) / 2 * Real.cos (Θi (m * t) + Θj (m' * t)) := by
    rw [← integral_add hId hIs]
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hpq] at ht
    simp only
    rw [hi t ht, hj t ht, mul_mul_mul_comm, cos_mul_cos]
    ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add hd hs)

end Cvs.Prolate.PruferWindowPair
