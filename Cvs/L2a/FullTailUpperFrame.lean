import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.L1CutLevelExponent
import Cvs.L2a.L1FullTailWinfBound
import Cvs.L2a.L1WindowFromFloor
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanTailHighMass
import Cvs.Prolate.AngularBesselInequality

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The upper frame of the full tail: `N ≤ C(ℓ)·Σ bᵢ²(π/c)(1 − λᵢ)`

`N ≤ 2N_k + 6K₁(k)` from `FullTailConvergence`'s `L²` rate, `N_k ≤ (1 + log k)J(1 + 8 log k)P` (Cvs.L2a.RungSpanTailHighMass), and at the level
`k = max(1, ((K₁ᵦ + P)/P)²)` the rate costs `6P`; `L1CutLevelExponent`'s endpoint floor puts `log k ≤ 3πc + 2 log((K₁ᵦ + P)/V)`.
With `AngularBesselInequality`'s `∫₁^∞ψᵢ² = (π/c)(1 − λᵢ)`, the full tail is `(1 − λ)`-small up to the symbolic factor.
-/

noncomputable section

open Real Set MeasureTheory
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.FullTailConvergence (fullTail K1)

namespace Cvs.L2a.FullTailUpperFrame

/-- **One level step**: `|N_k − N| ≤ 2√(N K) + K`, `N, K ≥ 0` give `N ≤ 2N_k + 6K`. -/
theorem le_of_abs_sub {N Nk K : ℝ} (hN : 0 ≤ N) (hK : 0 ≤ K) (h : |Nk - N| ≤ 2 * √(N * K) + K) :
    N ≤ 2 * Nk + 6 * K := by
  have h1 : N - Nk ≤ 2 * √(N * K) + K := by
    have := neg_abs_le (Nk - N)
    linarith
  have h2 : 2 * √(N * K) ≤ N / 2 + 2 * K := by
    rw [Real.sqrt_mul hN]
    nlinarith [sq_nonneg (√N - 2 * √K), Real.sq_sqrt hN, Real.sq_sqrt hK]
  linarith

/-- The frame factor `C(ℓ) = 2(1 + ℓ)J(1 + 8ℓ) + 6`. -/
def frameC (J ℓ : ℝ) : ℝ := 2 * (1 + ℓ) * (J * (1 + 8 * ℓ)) + 6

theorem frameC_nonneg {J ℓ : ℝ} (hJ : 0 ≤ J) (hℓ : 0 ≤ ℓ) : 0 ≤ frameC J ℓ := by
  unfold frameC; positivity

variable {ι : Type} [Fintype ι]

/-- `K₁ᵦ ≥ 0` for the span. -/
theorem K1bS_nonneg (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1)) (hc0 : 0 < c) :
    0 ≤ Cvs.L2a.L1FullTailWinfBound.K1bS c a g g₁ g₂ := by
  have hG := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span a hg
  have hG₁ := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span a hg₁
  have hG₂ := Cvs.L2a.FullTailFloorLimit.continuousOn_span a hg₂c
  have h := (Cvs.L2a.FullTailConvergence.integral_sub_sq_le hG hG₁ hG₂ hc0 (le_refl (1 : ℝ))).trans
    (Cvs.L2a.FullTailConvergence.K1_le hc0 _ _ (le_refl (1 : ℝ)))
  rw [Real.sqrt_one, div_one] at h
  exact (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _).trans h

/-- **The full tail at a level**: `N ≤ 2(1 + log k)J(1 + 8 log k)P + 6K₁ᵦk^{−1/2}` for `k ≥ 1`. -/
theorem tailN_le_level (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (hM : ∀ i, ∀ X : ℝ, 2 ≤ X → 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) {k : ℝ} (hk : 1 ≤ k) :
    Cvs.L2a.L1WindowFromFloor.tailN c a g
      ≤ 2 * ((1 + Real.log k) * ((Fintype.card ι : ℝ) * (1 + 8 * Real.log k)
          * ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2))
        + 6 * (Cvs.L2a.L1FullTailWinfBound.K1bS c a g g₁ g₂ * k ^ (-(1 / 2) : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hspan : (fun ξ => ∑ i, a i * psi c (g i) ξ) = psi c (fun t => ∑ i, a i * g i t) :=
    Cvs.L2a.FullTailFloorLimit.span_eq a hg c
  have hG := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span a hg
  have hG₁ := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span a hg₁
  have hG₂ := Cvs.L2a.FullTailFloorLimit.continuousOn_span a hg₂c
  have habs := Cvs.L2a.FullTailConvergence.abs_N_sub_le hG hG₁ hG₂ hc0 hk
  have hK1 : 0 ≤ K1 c ((fun t => ∑ i, a i * g i t) 1 + (fun t => ∑ i, a i * g i t) (-1))
      (|(fun t => ∑ i, a i * g₁ i t) 1 - (fun t => ∑ i, a i * g₁ i t) (-1)|
        + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, a i * g₂ i t) s|) k :=
    (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _).trans
      (Cvs.L2a.FullTailConvergence.integral_sub_sq_le hG hG₁ hG₂ hc0 hk)
  have hKle := Cvs.L2a.FullTailConvergence.K1_le hc0
    ((fun t => ∑ i, a i * g i t) 1 + (fun t => ∑ i, a i * g i t) (-1))
    (|(fun t => ∑ i, a i * g₁ i t) 1 - (fun t => ∑ i, a i * g₁ i t) (-1)|
      + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, a i * g₂ i t) s|) hk
  have hN0 : 0 ≤ ∫ θ in Ioi 1, fullTail (psi c fun t => ∑ i, a i * g i t) θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hstep := le_of_abs_sub hN0 hK1 habs
  have hNk := Cvs.L2a.RungSpanTailHighMass.integral_posTail_sq_le a hg hg₁ hg₂c hang hc hχ0 hχc hM hk
  rw [hspan] at hNk
  have hr : Cvs.L2a.L1FullTailWinfBound.K1bS c a g g₁ g₂ * k ^ (-(1 / 2) : ℝ)
      = Cvs.L2a.L1FullTailWinfBound.K1bS c a g g₁ g₂ / √k := by
    rw [rpow_neg hk0.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  unfold Cvs.L2a.L1WindowFromFloor.tailN
  rw [hspan, hr]
  unfold Cvs.L2a.L1FullTailWinfBound.K1bS
  linarith

/-- **The upper frame of the full tail**: for the rung span with some `bᵢ ≠ 0`, at `c ≥ 80`,
`N ≤ C(ℓ)·Σ bᵢ²(π/c)(1 − λᵢ)`, `ℓ = max(0, 3πc + 2 log((K₁ᵦ + P)/V))`, `P = Σ bᵢ²∫₁^∞ψᵢ²`, `V = Σ bᵢ²|μᵢ|³/(64c)`. -/
theorem tailN_le_frame (b : ι → ℝ) {h h₁ h₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s) (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1)
    (hμ0 : ∀ i, μ i ≠ 0) (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hM : ∀ i, ∀ X : ℝ, 2 ≤ X → 0 < ∫ t in (1 : ℝ)..X, psi c (h i) t ^ 2) (hb : ∃ i, b i ≠ 0) :
    Cvs.L2a.L1WindowFromFloor.tailN c b h
      ≤ frameC (Fintype.card ι)
          (max 0 (3 * π * c + 2 * Real.log ((Cvs.L2a.L1FullTailWinfBound.K1bS c b h h₁ h₂
              + ∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (h i) t ^ 2) / Cvs.L2a.L1WindowFromFloor.endV c 1 b μ)))
        * ∑ i, b i ^ 2 * (π / c * (1 - (μ i * √(c / (2 * π))) ^ 2)) := by
  have hc0 : 0 < c := by linarith
  set P := ∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (h i) t ^ 2 with hPd
  set Kb := Cvs.L2a.L1FullTailWinfBound.K1bS c b h h₁ h₂ with hKbd
  set V := Cvs.L2a.L1WindowFromFloor.endV c 1 b μ with hVd
  set J : ℝ := (Fintype.card ι : ℝ) with hJd
  have hKb := K1bS_nonneg b hg hg₁ hg₂c hc0
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  -- the mass is the `(1 − λ)` sum
  have hmass : P = ∑ i, b i ^ 2 * (π / c * (1 - (μ i * √(c / (2 * π))) ^ 2)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Cvs.Prolate.AngularBesselInequality.mass_eq hc0
      (fun s hs => (hg i s (by rw [uIcc_of_le (by norm_num)]; exact hs)).continuousAt.continuousWithinAt)
      (heven i) (hμ i) (hnorm i)]
  rw [← hmass]
  -- the endpoint floor
  obtain ⟨i₀, hi₀⟩ := hb
  have hV : 0 < V := by
    rw [hVd]; unfold Cvs.L2a.L1WindowFromFloor.endV
    refine div_pos (by
      rw [one_mul]
      exact lt_of_lt_of_le (mul_pos (pow_pos (abs_pos.mpr hi₀) 2) (pow_pos (abs_pos.mpr (hμ0 i₀)) 3))
        (by
          rw [sq_abs]
          exact Finset.single_le_sum (f := fun i => b i ^ 2 * |μ i| ^ 3)
            (fun i _ => mul_nonneg (sq_nonneg _) (pow_nonneg (abs_nonneg _) 3)) (Finset.mem_univ i₀)))
      (by positivity)
  have hfl : exp (-(3 * π * c / 2)) * V ≤ P := by
    have := Cvs.L2a.L1CutLevelExponent.tail_ge_endpoint b hg hg₁ hg₂c hang (by linarith) hχ0
      (fun i => (hχc i).le) heven hnorm hμ0 hμ zero_le_one (le_of_eq (one_mul P))
    simpa [hVd, Cvs.L2a.L1WindowFromFloor.endV] using this
  have hP : 0 < P := lt_of_lt_of_le (by positivity) hfl
  -- the level
  set k := Cvs.L2a.L1FullTailWinfBound.cutK (Kb + P) P with hkd
  have hk1 : 1 ≤ k := le_max_left _ _
  have hk0 : 0 < k := by linarith
  have hlk : Real.log k ≤ 3 * π * c + 2 * Real.log ((Kb + P) / V) := by
    have := Cvs.L2a.L1CutLevelExponent.log_cutK_le hP hV (show P ≤ Kb + P by linarith) hfl
    linarith
  have hlk0 : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hrate : Kb * k ^ (-(1 / 2) : ℝ) ≤ P := by
    have h := (Cvs.L2a.L1FullTailWinfBound.cutK_rpow_le (by linarith : 0 < Kb + P) hP).1
    calc Kb * k ^ (-(1 / 2) : ℝ) ≤ Kb * (P / (Kb + P)) := mul_le_mul_of_nonneg_left h hKb
      _ ≤ P := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
  have hstep := tailN_le_level b hg hg₁ hg₂c hang hc hχ0 hχc hM hk1
  set ℓ := max 0 (3 * π * c + 2 * Real.log ((Kb + P) / V))
  replace hlk : Real.log k ≤ ℓ := hlk.trans (le_max_right _ _)
  have hpoly : (1 + Real.log k) * (J * (1 + 8 * Real.log k)) ≤ (1 + ℓ) * (J * (1 + 8 * ℓ)) := by
    have h1 : 1 + Real.log k ≤ 1 + ℓ := by linarith
    have h2 : J * (1 + 8 * Real.log k) ≤ J * (1 + 8 * ℓ) := mul_le_mul_of_nonneg_left (by linarith) hJ0
    exact mul_le_mul h1 h2 (by positivity) (by linarith)
  have hP0 := hP.le
  unfold frameC
  rw [← hJd] at hstep
  nlinarith [mul_le_mul_of_nonneg_right hpoly hP0]

end Cvs.L2a.FullTailUpperFrame
