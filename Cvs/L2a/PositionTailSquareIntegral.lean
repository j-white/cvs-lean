import Mathlib
import Cvs.L2a.PositionTailEdgeRow
import Cvs.L2a.PositionTailPairIntegrals
import Cvs.L2a.PositionTruncatedTail
import Cvs.Upstream.OffDiagonalHarmonicSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The square integral of the position-truncated tail

For a radial solution with the hypotheses of Cvs.L2a.PositionTailEdgeRow and `X ≥ 1`,
`∫_{(1,∞)} F² ≤ ∫_1^X ψ² + (π²/6)B² + 2(π²/6)·rowC + 8·(14/3)BD/c² + (16/9)(π²/6)²B²`,
where `F` is the position-truncated tail of `ψ`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.PositionTailSquareIntegral

open Cvs.L2a.PositionTruncatedTail (posTail pairI)

/-- The partial sums of `1/n²` over `[2, N]` are at most `π²/6`. -/
lemma sum_inv_sq_le (N : ℕ) : ∑ a ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2 ≤ π ^ 2 / 6 :=
  sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two

/-- **The square integral of the position-truncated tail** is bounded by the near integral plus the
summed edge-row, diagonal and far off-diagonal bounds. -/
theorem integral_posTail_sq_le {ψ v v' : ℝ → ℝ} {c χ A A₁ B D κ X : ℝ} (hψ : ∀ ξ, HasDerivAt ψ (v ξ) ξ)
    (hv : ∀ ξ, HasDerivAt v (v' ξ) ξ) (hvc : Continuous v')
    (hode : ∀ ξ, (ξ ^ 2 - 1) * v' ξ + 2 * ξ * v ξ + (c ^ 2 * ξ ^ 2 - χ) * ψ ξ = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hq : ∀ ξ, 2 ≤ ξ → κ * c ^ 2 * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 - χ)
    (hA : ∀ θ ∈ Icc (1 : ℝ) 2, |ψ θ| ≤ A) (hA₁ : ∫ θ in (1 : ℝ)..2, |v θ| ≤ A₁) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hψB : ∀ ξ, 2 ≤ ξ → |ψ ξ| ≤ B / ξ) (hvD : ∀ ξ, 2 ≤ ξ → |v ξ| ≤ D / ξ) (hX : 1 ≤ X) :
    ∫ θ in Ioi 1, posTail ψ X θ ^ 2
      ≤ (∫ θ in (1 : ℝ)..X, ψ θ ^ 2) + π ^ 2 / 6 * B ^ 2
        + 2 * (π ^ 2 / 6) * Cvs.L2a.PositionTailEdgeRow.rowC c A A₁ B D κ
        + 8 * (14 / 3 * (B * D) / c ^ 2) + 16 / 9 * (π ^ 2 / 6) ^ 2 * B ^ 2 := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun ξ => (hψ ξ).continuousAt
  set N := ⌊X⌋₊ with hN
  set R := Cvs.L2a.PositionTailEdgeRow.rowC c A A₁ B D κ with hR
  set K := 14 / 3 * (B * D) / c ^ 2 with hK
  set P : ℕ → ℕ → ℝ := fun a m => pairI ψ X a m with hP
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hNX : (N : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 1 ⟨le_rfl, by norm_num⟩)
  have hA₁0 : 0 ≤ A₁ :=
    le_trans (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _) hA₁
  have hR0 : 0 ≤ R := by rw [hR]; unfold Cvs.L2a.PositionTailEdgeRow.rowC; positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  -- the upper limit of each pair integral is at least 1
  have hb : ∀ a m : ℕ, 1 ≤ a → a ≤ N → 1 ≤ m → m ≤ N → 1 ≤ X / ((max a m : ℕ) : ℝ) := by
    intro a m ha haN hm hmN
    have hpos : (0 : ℝ) < ((max a m : ℕ) : ℝ) := by
      have : 1 ≤ max a m := le_trans ha (le_max_left _ _)
      exact_mod_cast this
    have hle : ((max a m : ℕ) : ℝ) ≤ X := le_trans (by exact_mod_cast max_le haN hmN) hNX
    rw [le_div_iff₀ hpos]; linarith
  -- the pairing formula
  have hkey : ∫ θ in Ioi 1, posTail ψ X θ ^ 2 = ∑ a ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, P a m := by
    have h := Cvs.L2a.PositionTruncatedTail.integral_posTail_mul_dilate ψ hX hψc.continuousOn (k := 1) le_rfl
    simp only [Nat.cast_one, one_mul] at h
    rw [Finset.filter_true_of_mem fun m hm => (Finset.mem_Icc.mp hm).2] at h
    simp only [sq]; exact h
  have split : ∀ F : ℕ → ℝ, ∑ a ∈ Finset.Icc 1 N, F a = F 1 + ∑ a ∈ Finset.Icc 2 N, F a := by
    intro F
    have : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by ext x; simp; omega
    rw [this, Finset.sum_insert (by simp)]
  -- the (1,1) pair
  have h11 : P 1 1 = ∫ θ in (1 : ℝ)..X, ψ θ ^ 2 := by
    simp only [hP, pairI, max_self, Nat.cast_one, div_one, one_mul, sq]
  -- the edge rows
  have hrow : ∀ m ∈ Finset.Icc 2 N, |P 1 m| ≤ R * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    have h := Cvs.L2a.PositionTailEdgeRow.abs_integral_row_le (m := (m : ℝ)) hψ hv hvc hode hc hχ0 hχ
      (by exact_mod_cast hm'.1) (hb 1 m le_rfl hN1 (by omega) hm'.2) hκ hκ1 hq hA hA₁ hB hD hψB hvD
    simp only [hP, pairI, Nat.cast_one, one_mul]
    rw [mul_one_div]; exact h
  have hcol : ∀ a ∈ Finset.Icc 2 N, |P a 1| ≤ R * (1 / (a : ℝ) ^ 2) := by
    intro a ha
    have h := hrow a ha
    simp only [hP, pairI, Nat.cast_one, one_mul] at h ⊢
    rw [max_comm]
    simp_rw [mul_comm (ψ (a * _)) (ψ _)]
    exact h
  -- the diagonal
  have hdiag : ∀ a ∈ Finset.Icc 2 N, P a a ≤ B ^ 2 * (1 / (a : ℝ) ^ 2) := by
    intro a ha
    have ha' := Finset.mem_Icc.mp ha
    have h := Cvs.L2a.PositionTailPairIntegrals.integral_diag_le (a := (a : ℝ)) (by exact_mod_cast ha'.1)
      (hb a a (by omega) ha'.2 (by omega) ha'.2) hψc hψB
    rw [max_self] at h
    simp only [hP, pairI, max_self, ← sq]
    rw [mul_one_div]; exact h
  -- the far off-diagonal pairs
  have hfar : ∀ a ∈ Finset.Icc 2 N, ∀ m ∈ (Finset.Icc 2 N).erase a,
      P a m ≤ K * (1 / ((a : ℝ) * m * |(a : ℝ) - m|)) + 16 / 9 * B ^ 2 * (1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2)) := by
    intro a ha m hm
    have ha' := Finset.mem_Icc.mp ha
    have hmne := (Finset.mem_erase.mp hm).1
    have hm' := Finset.mem_Icc.mp (Finset.mem_erase.mp hm).2
    have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha'.1
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm'.1
    have h := Cvs.L2a.PositionTailPairIntegrals.abs_integral_far_le (a := (a : ℝ)) (m := (m : ℝ)) hψ hv hvc hode hc hχ0 hχ
      ha2 hm2 (by exact_mod_cast (Ne.symm hmne)) (hb a m (by omega) ha'.2 (by omega) hm'.2) hB hD hψB hvD
    have e1 : 14 / 3 * (B * D) / (c ^ 2 * ((a : ℝ) * m * |(a : ℝ) - m|))
        = K * (1 / ((a : ℝ) * m * |(a : ℝ) - m|)) := by rw [hK, mul_one_div, div_div]
    have e2 : B ^ 2 / ((a : ℝ) ^ 3 * (m : ℝ) ^ 3) ≤ B ^ 2 * (1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2)) := by
      rw [one_div_mul_one_div, mul_one_div]
      apply div_le_div_of_nonneg_left (sq_nonneg B) (by positivity)
      have h1 : (a : ℝ) ^ 2 ≤ (a : ℝ) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have h2 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hle := le_trans (le_abs_self _) h
    simp only [hP, pairI]
    rw [e1] at hle
    nlinarith
  -- summing each family
  have Z := sum_inv_sq_le N
  have Z0 : 0 ≤ ∑ a ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have S1 : ∑ m ∈ Finset.Icc 2 N, P 1 m ≤ R * (π ^ 2 / 6) := by
    calc _ ≤ ∑ m ∈ Finset.Icc 2 N, R * (1 / (m : ℝ) ^ 2) :=
          Finset.sum_le_sum fun m hm => le_trans (le_abs_self _) (hrow m hm)
      _ = R * ∑ m ∈ Finset.Icc 2 N, 1 / (m : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left Z hR0
  have S2 : ∑ a ∈ Finset.Icc 2 N, P a 1 ≤ R * (π ^ 2 / 6) := by
    calc _ ≤ ∑ a ∈ Finset.Icc 2 N, R * (1 / (a : ℝ) ^ 2) :=
          Finset.sum_le_sum fun a ha => le_trans (le_abs_self _) (hcol a ha)
      _ = R * ∑ a ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left Z hR0
  have S3 : ∑ a ∈ Finset.Icc 2 N, P a a ≤ B ^ 2 * (π ^ 2 / 6) := by
    calc _ ≤ ∑ a ∈ Finset.Icc 2 N, B ^ 2 * (1 / (a : ℝ) ^ 2) := Finset.sum_le_sum hdiag
      _ = B ^ 2 * ∑ a ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left Z (sq_nonneg B)
  have W : ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, 1 / ((a : ℝ) * m * |(a : ℝ) - m|) ≤ 8 := by
    refine le_trans ?_ (Cvs.Upstream.OffDiagonalHarmonicSum.offDiag_sum_le N)
    calc _ ≤ ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 1 N).filter (· ≠ a),
          1 / ((a : ℝ) * m * |(a : ℝ) - m|) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun _ _ _ => by positivity
          intro m hm
          simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_filter] at hm ⊢
          omega
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ =>
            Finset.sum_nonneg fun _ _ => by positivity
          intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  have V : ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, 1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2)
      ≤ (π ^ 2 / 6) ^ 2 := by
    calc _ ≤ ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => by positivity
      _ = (∑ a ∈ Finset.Icc 2 N, 1 / (a : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 2 N, 1 / (m : ℝ) ^ 2 :=
          (Finset.sum_mul_sum _ _ _ _).symm
      _ ≤ _ := by rw [sq]; exact mul_le_mul Z Z Z0 (by positivity)
  have S4 : ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, P a m
      ≤ K * 8 + 16 / 9 * B ^ 2 * (π ^ 2 / 6) ^ 2 := by
    calc _ ≤ ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a,
          (K * (1 / ((a : ℝ) * m * |(a : ℝ) - m|)) + 16 / 9 * B ^ 2 * (1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2))) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun m hm => hfar a ha m hm
      _ = K * (∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, 1 / ((a : ℝ) * m * |(a : ℝ) - m|))
          + 16 / 9 * B ^ 2 * (∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a,
              1 / (a : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2)) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left W hK0)
          (mul_le_mul_of_nonneg_left V (by positivity))
  -- assemble
  have hdec : ∑ a ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, P a m
      = P 1 1 + ∑ m ∈ Finset.Icc 2 N, P 1 m + ∑ a ∈ Finset.Icc 2 N, P a 1
        + ∑ a ∈ Finset.Icc 2 N, P a a + ∑ a ∈ Finset.Icc 2 N, ∑ m ∈ (Finset.Icc 2 N).erase a, P a m := by
    rw [split, split (P 1)]
    have : ∀ a ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N, P a m
        = P a 1 + (P a a + ∑ m ∈ (Finset.Icc 2 N).erase a, P a m) := fun a ha => by
      rw [split (P a), Finset.add_sum_erase _ _ ha]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  rw [hkey, hdec, h11]
  nlinarith [S1, S2, S3, S4]

end Cvs.L2a.PositionTailSquareIntegral
