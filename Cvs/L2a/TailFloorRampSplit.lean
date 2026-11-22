import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The smooth split of the tail: the floor with a ramp

For `ψ + T` with a ramp `η` (`η = 1` on `[θ₀, b]`) and `s > 0`, pointwise
`(ψ + T)² ≥ ψ² + 2ηψT − s(1 − η)²ψ² − T²/s` by `2xy ≥ −sx² − y²/s` on `x = (1 − η)ψ`, `y = T`, and
`(ψ + T)² ≥ ψ² + 2ψT` where `η = 1`, so `∫₁ᵇ (ψ + T)² ≥ ∫ ψ² − s ∫ (1 − η)²ψ² − (1/s) ∫₁^{θ₀} T² + 2 ∫ ηψT`:
the tail floor whose cross term carries the weight `η`, vanishing where the cut is.
-/

namespace Cvs.L2a.TailFloorRampSplit

open Real Set intervalIntegral

/-- **Pointwise, on the edge**: `ψ² + 2ηψT − s(1 − η)²ψ² − T²/s ≤ (ψ + T)²` for `s > 0`. -/
theorem sq_add_ge_edge {ψ T η s : ℝ} (hs : 0 < s) :
    ψ ^ 2 + 2 * (η * (ψ * T)) - s * ((1 - η) ^ 2 * ψ ^ 2) - 1 / s * T ^ 2 ≤ (ψ + T) ^ 2 := by
  have h0 : 0 ≤ (s * ((1 - η) * ψ) + T) ^ 2 / s := div_nonneg (sq_nonneg _) hs.le
  have e : (s * ((1 - η) * ψ) + T) ^ 2 / s
      = s * ((1 - η) ^ 2 * ψ ^ 2) + 2 * ((1 - η) * ψ * T) + 1 / s * T ^ 2 := by
    field_simp
    ring
  nlinarith [sq_nonneg T]

/-- **Pointwise, on the bulk**: `ψ² + 2ηψT − s(1 − η)²ψ² ≤ (ψ + T)²` when `η = 1`, `s ≥ 0`. -/
theorem sq_add_ge_bulk {ψ T η s : ℝ} (hη : η = 1) :
    ψ ^ 2 + 2 * (η * (ψ * T)) - s * ((1 - η) ^ 2 * ψ ^ 2) ≤ (ψ + T) ^ 2 := by
  subst hη; nlinarith [sq_nonneg T]

/-- **The smooth split of the tail**: on `[1, b]` with `1 ≤ θ₀ ≤ b`, `η` continuous with `η = 1` on `[θ₀, b]`, and
`ψ`, `T` continuous, `∫₁ᵇ ψ² − s ∫₁ᵇ (1 − η)²ψ² − (1/s) ∫₁^{θ₀} T² + 2 ∫₁ᵇ ηψT ≤ ∫₁ᵇ (ψ + T)²`. -/
theorem tail_floor_ramp {ψ T η : ℝ → ℝ} {θ₀ b s : ℝ} (h1 : 1 ≤ θ₀) (hb : θ₀ ≤ b) (hs : 0 < s)
    (hψ : ContinuousOn ψ (Icc 1 b)) (hT : ContinuousOn T (Icc 1 b)) (hηc : ContinuousOn η (Icc 1 b))
    (hη1 : ∀ θ ∈ Icc θ₀ b, η θ = 1) :
    (∫ θ in (1 : ℝ)..b, ψ θ ^ 2) - s * (∫ θ in (1 : ℝ)..b, (1 - η θ) ^ 2 * ψ θ ^ 2)
        - 1 / s * (∫ θ in (1 : ℝ)..θ₀, T θ ^ 2) + 2 * (∫ θ in (1 : ℝ)..b, η θ * (ψ θ * T θ))
      ≤ ∫ θ in (1 : ℝ)..b, (ψ θ + T θ) ^ 2 := by
  have h1b : (1 : ℝ) ≤ b := h1.trans hb
  have hsub1 : uIcc 1 θ₀ ⊆ uIcc 1 b := uIcc_subset_uIcc_left (by rw [uIcc_of_le h1b]; exact ⟨h1, hb⟩)
  have hsub2 : uIcc θ₀ b ⊆ uIcc 1 b := uIcc_subset_uIcc_right (by rw [uIcc_of_le h1b]; exact ⟨h1, hb⟩)
  have hI1 : IntervalIntegrable (fun θ => ψ θ ^ 2) MeasureTheory.volume 1 b := (hψ.pow 2).intervalIntegrable_of_Icc h1b
  have hI2 : IntervalIntegrable (fun θ => (1 - η θ) ^ 2 * ψ θ ^ 2) MeasureTheory.volume 1 b :=
    (((continuousOn_const.sub hηc).pow 2).mul (hψ.pow 2)).intervalIntegrable_of_Icc h1b
  have hI3 : IntervalIntegrable (fun θ => η θ * (ψ θ * T θ)) MeasureTheory.volume 1 b :=
    (hηc.mul (hψ.mul hT)).intervalIntegrable_of_Icc h1b
  have hI4 : IntervalIntegrable (fun θ => (ψ θ + T θ) ^ 2) MeasureTheory.volume 1 b :=
    ((hψ.add hT).pow 2).intervalIntegrable_of_Icc h1b
  have hIT : IntervalIntegrable (fun θ => T θ ^ 2) MeasureTheory.volume 1 b := (hT.pow 2).intervalIntegrable_of_Icc h1b
  -- the edge piece `[1, θ₀]`
  have hedge : ∫ θ in (1 : ℝ)..θ₀, (ψ θ ^ 2 + 2 * (η θ * (ψ θ * T θ)) - s * ((1 - η θ) ^ 2 * ψ θ ^ 2) - 1 / s * T θ ^ 2)
      ≤ ∫ θ in (1 : ℝ)..θ₀, (ψ θ + T θ) ^ 2 := by
    refine integral_mono_on h1 ?_ (hI4.mono_set hsub1) fun θ _ => sq_add_ge_edge hs
    exact (((hI1.mono_set hsub1).add ((hI3.mono_set hsub1).const_mul 2)).sub ((hI2.mono_set hsub1).const_mul s)).sub
      ((hIT.mono_set hsub1).const_mul (1 / s))
  -- the bulk piece `[θ₀, b]`
  have hbulk : ∫ θ in θ₀..b, (ψ θ ^ 2 + 2 * (η θ * (ψ θ * T θ)) - s * ((1 - η θ) ^ 2 * ψ θ ^ 2))
      ≤ ∫ θ in θ₀..b, (ψ θ + T θ) ^ 2 := by
    refine integral_mono_on hb ?_ (hI4.mono_set hsub2) fun θ hθ => sq_add_ge_bulk (hη1 θ hθ)
    exact ((hI1.mono_set hsub2).add ((hI3.mono_set hsub2).const_mul 2)).sub ((hI2.mono_set hsub2).const_mul s)
  rw [integral_sub (((hI1.mono_set hsub1).add ((hI3.mono_set hsub1).const_mul 2)).sub ((hI2.mono_set hsub1).const_mul s))
    ((hIT.mono_set hsub1).const_mul (1 / s)),
    integral_sub ((hI1.mono_set hsub1).add ((hI3.mono_set hsub1).const_mul 2)) ((hI2.mono_set hsub1).const_mul s),
    integral_add (hI1.mono_set hsub1) ((hI3.mono_set hsub1).const_mul 2), integral_const_mul, integral_const_mul,
    integral_const_mul] at hedge
  rw [integral_sub ((hI1.mono_set hsub2).add ((hI3.mono_set hsub2).const_mul 2)) ((hI2.mono_set hsub2).const_mul s),
    integral_add (hI1.mono_set hsub2) ((hI3.mono_set hsub2).const_mul 2), integral_const_mul,
    integral_const_mul] at hbulk
  have e1 := integral_add_adjacent_intervals (hI1.mono_set hsub1) (hI1.mono_set hsub2)
  have e2 := integral_add_adjacent_intervals (hI2.mono_set hsub1) (hI2.mono_set hsub2)
  have e3 := integral_add_adjacent_intervals (hI3.mono_set hsub1) (hI3.mono_set hsub2)
  have e4 := integral_add_adjacent_intervals (hI4.mono_set hsub1) (hI4.mono_set hsub2)
  rw [← e1, ← e2, ← e3, ← e4]
  have hm := mul_add s (∫ x in (1 : ℝ)..θ₀, (1 - η x) ^ 2 * ψ x ^ 2) (∫ x in θ₀..b, (1 - η x) ^ 2 * ψ x ^ 2)
  linarith

end Cvs.L2a.TailFloorRampSplit
