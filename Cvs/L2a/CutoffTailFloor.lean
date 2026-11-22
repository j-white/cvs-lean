import Mathlib
import Cvs.L2a.PlateauSummedDiagonal
import Cvs.L2a.TailFloorRampSplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail floor of the cutoff route: diagonal exact, cross terms as weighted pair integrals

For `T₂ = Σ_{m=2}^{M} G(m·)`, a ramp `η` (`η = 1` on `[θ₀, b]`) and a plateau `σ` (`0 ≤ σ ≤ 1`, `σ = 1` on `[1, θ₀]`,
`σ = 0` outside `(19/20, 3/2)`), the smooth split (Cvs.L2a.TailFloorRampSplit) and the plateau diagonal (Cvs.L2a.PlateauSummedDiagonal) give
`∫₁ᵇ (G + T₂)² ≥ ∫₁ᵇ G² − s∫₁ᵇ (1 − η)²G² − (1/s)[(5/6)∫_{19/10}^{3M/2} G² + Σ_{m≠m'} ∫ σ G(m·)G(m'·)]
+ 2Σ_{m=2}^{M} ∫₁ᵇ η G G(m·)`: the tail floor with only weighted cross-mode pair integrals left.
-/

namespace Cvs.L2a.CutoffTailFloor

open Real Set Finset intervalIntegral

/-- The square of a weighted finite sum integrates as the double sum of weighted products. -/
theorem integral_weighted_sq_sum {σ : ℝ → ℝ} {F : ℕ → ℝ → ℝ} {L R : ℝ} (S : Finset ℕ) (hσc : Continuous σ)
    (hF : ∀ m ∈ S, Continuous (F m)) :
    ∫ θ in L..R, σ θ * (∑ m ∈ S, F m θ) ^ 2 = ∑ m ∈ S, ∑ m' ∈ S, ∫ θ in L..R, σ θ * (F m θ * F m' θ) := by
  have e : (fun θ => σ θ * (∑ m ∈ S, F m θ) ^ 2) = fun θ => ∑ m ∈ S, ∑ m' ∈ S, σ θ * (F m θ * F m' θ) := by
    funext θ
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum]
  rw [e]
  have hI : ∀ m ∈ S, ∀ m' ∈ S, IntervalIntegrable (fun θ => σ θ * (F m θ * F m' θ)) MeasureTheory.volume L R :=
    fun m hm m' hm' => (hσc.mul ((hF m hm).mul (hF m' hm'))).intervalIntegrable L R
  have hI' : ∀ m ∈ S, IntervalIntegrable (fun θ => ∑ m' ∈ S, σ θ * (F m θ * F m' θ)) MeasureTheory.volume L R :=
    fun m hm => by
      have h := IntervalIntegrable.sum S fun m' hm' => hI m hm m' hm'
      simpa only [Finset.sum_fn] using h
  rw [integral_finsetSum hI']
  apply Finset.sum_congr rfl; intro m hm
  rw [integral_finsetSum fun m' hm' => hI m hm m' hm']

/-- The weighted product of `G` with the tail is the sum of the weighted pair integrals. -/
theorem integral_weighted_tail {η G : ℝ → ℝ} {L R : ℝ} {M : ℕ} (hηc : Continuous η) (hGc : Continuous G) :
    ∫ θ in L..R, η θ * (G θ * ∑ m ∈ Finset.Icc 2 M, G (m * θ))
      = ∑ m ∈ Finset.Icc 2 M, ∫ θ in L..R, η θ * (G θ * G (m * θ)) := by
  have e : (fun θ => η θ * (G θ * ∑ m ∈ Finset.Icc 2 M, G (m * θ)))
      = fun θ => ∑ m ∈ Finset.Icc 2 M, η θ * (G θ * G (m * θ)) := by
    funext θ; rw [Finset.mul_sum, Finset.mul_sum]
  rw [e]
  exact integral_finsetSum fun m _ =>
    (hηc.mul (hGc.mul (hGc.comp (continuous_const.mul continuous_id)))).intervalIntegrable L R

/-- The diagonal of the plateau-weighted tail square is at most `(5/6)∫_{19/10}^{3M/2} G²`, and the square itself
is the diagonal plus the off-diagonal pairs. -/
theorem plateau_tail_sq_le {σ G : ℝ → ℝ} {M : ℕ} (hM : 2 ≤ M) (hσc : Continuous σ) (hGc : Continuous G)
    (hσ1 : ∀ θ, σ θ ≤ 1) (hσ0 : ∀ θ, θ ≤ 19 / 20 ∨ 3 / 2 ≤ θ → σ θ = 0) :
    ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2
      ≤ 5 / 6 * (∫ u in (19 / 10 : ℝ)..(3 * M / 2), G u ^ 2)
        + ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
            (if m = m' then 0 else ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (G (m * θ) * G (m' * θ))) := by
  rw [integral_weighted_sq_sum (F := fun m θ => G (m * θ)) (Finset.Icc 2 M) hσc
    fun m _ => hGc.comp (continuous_const.mul continuous_id)]
  have hdiag := Cvs.L2a.PlateauSummedDiagonal.sum_dilate_sq_le (σ := σ) (G := G) hσc hGc hσ1 hσ0 hM
    (L := 19 / 20) (R := 3 / 2) le_rfl le_rfl
  -- split each inner sum into its diagonal term and the rest
  have e : ∀ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M, ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (G (m * θ) * G (m' * θ))
      = (∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * G (m * θ) ^ 2)
        + ∑ m' ∈ Finset.Icc 2 M,
            (if m = m' then 0 else ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (G (m * θ) * G (m' * θ))) := by
    intro m hm
    have := Finset.sum_erase_add (Finset.Icc 2 M)
      (fun m' => ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (G (m * θ) * G (m' * θ))) hm
    rw [← this]
    have e2 : ∑ m' ∈ Finset.Icc 2 M,
        (if m = m' then 0 else ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (G (m * θ) * G (m' * θ)))
        = ∑ m' ∈ (Finset.Icc 2 M).erase m, ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (G (m * θ) * G (m' * θ)) := by
      rw [← Finset.sum_erase_add _ _ hm, if_pos rfl, add_zero]
      apply Finset.sum_congr rfl; intro m' hm'
      rw [if_neg (Finset.ne_of_mem_erase hm').symm]
    rw [e2]
    have e3 : ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (G (m * θ) * G (m * θ))
        = ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * G (m * θ) ^ 2 := by
      congr 1; funext θ; ring
    rw [e3]; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
  linarith

/-- **The tail floor of the cutoff route.** With `T₂ = Σ_{m=2}^{M} G(m·)`, `1 ≤ θ₀ ≤ 3/2`, `θ₀ ≤ b`, `s > 0`,
`η` continuous with `η = 1` on `[θ₀, b]`, and `σ` continuous with `0 ≤ σ ≤ 1`, `σ = 1` on `[1, θ₀]`, `σ = 0` outside
`(19/20, 3/2)`: the split with the diagonal exact and the cross terms as weighted pair integrals. -/
theorem tail_floor_cutoff {G η σ : ℝ → ℝ} {θ₀ b s : ℝ} {M : ℕ} (hM : 2 ≤ M) (h1 : 1 ≤ θ₀) (hθ₀ : θ₀ ≤ 3 / 2)
    (hb : θ₀ ≤ b) (hs : 0 < s) (hGc : Continuous G) (hηc : Continuous η) (hη1 : ∀ θ ∈ Icc θ₀ b, η θ = 1)
    (hσc : Continuous σ) (hσnn : ∀ θ, 0 ≤ σ θ) (hσ1 : ∀ θ, σ θ ≤ 1) (hσp : ∀ θ ∈ Icc 1 θ₀, σ θ = 1)
    (hσ0 : ∀ θ, θ ≤ 19 / 20 ∨ 3 / 2 ≤ θ → σ θ = 0) :
    (∫ θ in (1 : ℝ)..b, G θ ^ 2) - s * (∫ θ in (1 : ℝ)..b, (1 - η θ) ^ 2 * G θ ^ 2)
        - 1 / s * (5 / 6 * (∫ u in (19 / 10 : ℝ)..(3 * M / 2), G u ^ 2)
            + ∑ m ∈ Finset.Icc 2 M, ∑ m' ∈ Finset.Icc 2 M,
              (if m = m' then 0 else ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (G (m * θ) * G (m' * θ))))
        + 2 * ∑ m ∈ Finset.Icc 2 M, ∫ θ in (1 : ℝ)..b, η θ * (G θ * G (m * θ))
      ≤ ∫ θ in (1 : ℝ)..b, (G θ + ∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2 := by
  have hTc : Continuous fun θ => ∑ m ∈ Finset.Icc 2 M, G (m * θ) :=
    continuous_finsetSum _ fun m _ => hGc.comp (continuous_const.mul continuous_id)
  have hsplit := Cvs.L2a.TailFloorRampSplit.tail_floor_ramp (ψ := G) (T := fun θ => ∑ m ∈ Finset.Icc 2 M, G (m * θ))
    (η := η) h1 hb hs hGc.continuousOn hTc.continuousOn hηc.continuousOn hη1
  -- the edge square of the tail under the plateau
  have hT2 : ∫ θ in (1 : ℝ)..θ₀, (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2
      ≤ ∫ θ in (19 / 20 : ℝ)..(3 / 2), σ θ * (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2 := by
    have hF : Continuous fun θ => σ θ * (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2 := hσc.mul (hTc.pow 2)
    have hnn : ∀ θ, 0 ≤ σ θ * (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2 := fun θ =>
      mul_nonneg (hσnn θ) (sq_nonneg _)
    have hI : ∀ a b : ℝ, IntervalIntegrable (fun θ => σ θ * (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2)
        MeasureTheory.volume a b := fun a b => hF.intervalIntegrable a b
    have e : ∫ θ in (1 : ℝ)..θ₀, (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2
        = ∫ θ in (1 : ℝ)..θ₀, σ θ * (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ hθ => ?_)
      rw [uIoc_of_le h1] at hθ
      rw [hσp θ ⟨hθ.1.le, hθ.2⟩, one_mul]
    rw [e, ← integral_add_adjacent_intervals (hI (19 / 20) 1) (hI 1 (3 / 2)),
      ← integral_add_adjacent_intervals (hI 1 θ₀) (hI θ₀ (3 / 2))]
    have z1 : 0 ≤ ∫ θ in (19 / 20 : ℝ)..1, σ θ * (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2 :=
      integral_nonneg (by norm_num) fun θ _ => hnn θ
    have z2 : 0 ≤ ∫ θ in θ₀..(3 / 2), σ θ * (∑ m ∈ Finset.Icc 2 M, G (m * θ)) ^ 2 :=
      integral_nonneg hθ₀ fun θ _ => hnn θ
    linarith
  have hplat := plateau_tail_sq_le (σ := σ) (G := G) hM hσc hGc hσ1 hσ0
  have hcross := integral_weighted_tail (η := η) (G := G) (L := 1) (R := b) (M := M) hηc hGc
  have hs' : 0 ≤ 1 / s := by positivity
  have := mul_le_mul_of_nonneg_left (hT2.trans hplat) hs'
  rw [hcross] at hsplit
  linarith

end Cvs.L2a.CutoffTailFloor
