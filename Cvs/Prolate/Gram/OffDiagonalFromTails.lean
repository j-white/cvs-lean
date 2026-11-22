import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Cvs.Prolate.LiouvilleGreen.LayerWindowSplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# An off-diagonal Gram entry from the two tails

If `|∫_1^t ψ_iψ_j| ≤ K/t` for all large `t` (orthogonality on `(1, ∞)` at any rate, Cvs.Prolate.RungOrthogonalityAtInfinity) and the tails obey
`∫_T^t ψ_i² ≤ τ_i` for `t ≥ T`, then `|∫_1^T ψ_iψ_j| ≤ √(τ_iτ_j)`: the cross mass on `[1, T]` is minus the cross
mass beyond `T`, so it is charged to the tails and the rate constant `K` drops out.
-/

namespace Cvs.Prolate.Gram.OffDiagonalFromTails

open Real Set MeasureTheory intervalIntegral Filter Topology Cvs.Prolate.LiouvilleGreen.LayerWindowSplit

/-- **The off-diagonal entry from the tails.** -/
theorem abs_integral_le_tails {ψi ψj : ℝ → ℝ} {T K τi τj : ℝ} (hT : 1 ≤ T)
    (hci : ContinuousOn ψi (Ici 1)) (hcj : ContinuousOn ψj (Ici 1))
    (hcross : ∀ t, T ≤ t → |∫ ξ in (1 : ℝ)..t, ψi ξ * ψj ξ| ≤ K / t)
    (hτi : ∀ t, T ≤ t → ∫ ξ in T..t, ψi ξ ^ 2 ≤ τi) (hτj : ∀ t, T ≤ t → ∫ ξ in T..t, ψj ξ ^ 2 ≤ τj) :
    |∫ ξ in (1 : ℝ)..T, ψi ξ * ψj ξ| ≤ √(τi * τj) := by
  have hτi0 : 0 ≤ τi := le_trans (by simp) (hτi T le_rfl)
  -- for every `t ≥ T`, the entry is within `K/t` of `√(τ_iτ_j)`
  have hstep : ∀ t, T ≤ t → |∫ ξ in (1 : ℝ)..T, ψi ξ * ψj ξ| ≤ K / t + √(τi * τj) := fun t ht => by
    have h1t : (1 : ℝ) ≤ t := hT.trans ht
    have hci' : ContinuousOn ψi (Icc 1 t) := hci.mono Icc_subset_Ici_self
    have hcj' : ContinuousOn ψj (Icc 1 t) := hcj.mono Icc_subset_Ici_self
    have i1 : IntervalIntegrable (fun ξ => ψi ξ * ψj ξ) volume 1 T :=
      ((hci'.mul hcj').mono (Icc_subset_Icc le_rfl ht)).intervalIntegrable_of_Icc hT
    have i2 : IntervalIntegrable (fun ξ => ψi ξ * ψj ξ) volume T t :=
      ((hci'.mul hcj').mono (Icc_subset_Icc hT le_rfl)).intervalIntegrable_of_Icc ht
    have hsplit := intervalIntegral.integral_add_adjacent_intervals i1 i2
    have hcs := abs_integral_mul_le ht (hci'.mono (Icc_subset_Icc hT le_rfl)) (hcj'.mono (Icc_subset_Icc hT le_rfl))
    have htail : √(∫ ξ in T..t, ψi ξ ^ 2) * √(∫ ξ in T..t, ψj ξ ^ 2) ≤ √(τi * τj) := by
      rw [← Real.sqrt_mul (intervalIntegral.integral_nonneg ht fun ξ _ => sq_nonneg _)]
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (hτi t ht) (hτj t ht) (intervalIntegral.integral_nonneg ht fun ξ _ => sq_nonneg _) hτi0
    have hx := hcross t ht
    have e : ∫ ξ in (1 : ℝ)..T, ψi ξ * ψj ξ = (∫ ξ in (1 : ℝ)..t, ψi ξ * ψj ξ) - ∫ ξ in T..t, ψi ξ * ψj ξ := by
      linarith
    rw [e]
    calc |(∫ ξ in (1 : ℝ)..t, ψi ξ * ψj ξ) - ∫ ξ in T..t, ψi ξ * ψj ξ|
        ≤ |∫ ξ in (1 : ℝ)..t, ψi ξ * ψj ξ| + |∫ ξ in T..t, ψi ξ * ψj ξ| := abs_sub _ _
      _ ≤ K / t + √(τi * τj) := add_le_add hx (hcs.trans htail)
  -- let `t → ∞`
  have hlim : Tendsto (fun t : ℝ => K / t + √(τi * τj)) atTop (𝓝 (0 + √(τi * τj))) :=
    (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
  rw [zero_add] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨T, hstep⟩)

end Cvs.Prolate.Gram.OffDiagonalFromTails
