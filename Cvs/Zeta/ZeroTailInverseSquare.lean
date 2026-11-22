import Mathlib
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.DyadicTailZeroSide
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The zeros above `T` against `1/γ²` weigh at most `16 log(4T)/T`

Summing `Cvs.Zeta.ZeroCounting.DyadicTailZeroSide`'s dyadic count `8·2^jT log(2^{j+1}T)` against `1/(2^jT)²` over every block gives, for
`9 + e ≤ 2T`, `Σ_{|γ| > T} m_ρ/γ² ≤ (8/T) Σ_j 2^{−j}(log 2T + j log 2) ≤ 16 log(4T)/T`, which tends to `0`.
-/

noncomputable section

open Real Filter Topology Cvs.Zeta.Explicit.Venue

namespace Cvs.Zeta.ZeroTailInverseSquare

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

/-- The tail bound `16 log(4T)/T`. -/
def tailBound (T : ℝ) : ℝ := 16 * Real.log (4 * T) / T

/-- `Σ_{j<n} 8·2^jT log(2·2^jT)/(2^jT)² ≤ 16 log(4T)/T` for `T ≥ 1/2`. -/
theorem dyadic_sum_le {T : ℝ} (hT : 1 / 2 ≤ T) (n : ℕ) :
    ∑ j ∈ Finset.range n, 1 / ((2 : ℝ) ^ j * T) ^ 2 * (8 * ((2 : ℝ) ^ j * T) * Real.log (2 * ((2 : ℝ) ^ j * T)))
      ≤ tailBound T := by
  have hT0 : 0 < T := by linarith
  have hl2T : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hterm : ∀ j : ℕ, 1 / ((2 : ℝ) ^ j * T) ^ 2 * (8 * ((2 : ℝ) ^ j * T) * Real.log (2 * ((2 : ℝ) ^ j * T)))
      = 8 / T * (Real.log (2 * T) * (1 / 2 : ℝ) ^ j + Real.log 2 * ((j : ℝ) * (1 / 2 : ℝ) ^ j)) := by
    intro j
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have hlog : Real.log (2 * ((2 : ℝ) ^ j * T)) = Real.log (2 * T) + j * Real.log 2 := by
      rw [show 2 * ((2 : ℝ) ^ j * T) = (2 * T) * 2 ^ j by ring, Real.log_mul (by positivity) h2j.ne',
        Real.log_pow]
    rw [hlog, one_div_pow]
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hg : ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j ≤ 2 := sum_geometric_two_le n
  have hm : ∑ j ∈ Finset.range n, (j : ℝ) * (1 / 2 : ℝ) ^ j ≤ 2 := by
    have hs := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / 2)
      (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)
    have h := hs.summable.sum_le_tsum (Finset.range n) (fun j _ => by positivity)
    rw [hs.tsum_eq] at h
    norm_num at h ⊢
    exact h
  have hlog4 : Real.log (4 * T) = Real.log (2 * T) + Real.log 2 := by
    rw [show 4 * T = (2 * T) * 2 by ring, Real.log_mul (by positivity) (by norm_num)]
  rw [tailBound, hlog4]
  calc 8 / T * (Real.log (2 * T) * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j
        + Real.log 2 * ∑ j ∈ Finset.range n, (j : ℝ) * (1 / 2 : ℝ) ^ j)
      ≤ 8 / T * (Real.log (2 * T) * 2 + Real.log 2 * 2) := by gcongr
    _ = 16 * (Real.log (2 * T) + Real.log 2) / T := by ring

/-- **Every finite set of zeros above `T` weighs at most `16 log(4T)/T`** against `m_ρ/γ²`, for `9 + e ≤ 2T`. -/
theorem sum_le_tailBound {T : ℝ} (hT : 9 + Real.exp 1 ≤ 2 * T)
    (F : Finset {ρ : nonTrivialZeroSet // T < |(ρ : ℂ).im|}) :
    ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ) / (((ρ : nonTrivialZeroSet) : ℂ)).im ^ 2
      ≤ tailBound T := by
  classical
  have he := Real.exp_pos 1
  have hT0 : 0 < T := by linarith
  -- a dyadic height above every member of `F`
  set B : ℝ := ∑ ρ ∈ F, |(((ρ : nonTrivialZeroSet) : ℂ)).im|
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / T) (by norm_num : (1 : ℝ) < 2)
  have hB : ∀ ρ ∈ F, |(((ρ : nonTrivialZeroSet) : ℂ)).im| ≤ 2 ^ n * T := fun ρ hρ => by
    have h1 := Finset.single_le_sum (f := fun ρ : {ρ : nonTrivialZeroSet // T < |(ρ : ℂ).im|} =>
      |(((ρ : nonTrivialZeroSet) : ℂ)).im|) (fun _ _ => abs_nonneg _) hρ
    rw [div_lt_iff₀ hT0] at hn
    exact h1.trans hn.le
  set S : Finset nonTrivialZeroSet := (nontrivialZetaZeroWindowFinset ((2 : ℝ) ^ n * T) \
    nontrivialZetaZeroWindowFinset T).map Cvs.Criterion.zeroEquiv.toEmbedding
  set g : nonTrivialZeroSet → ℝ := fun ρ => (Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / |Cvs.GaussKernel.gam ρ| ^ 2)
  have hsub : F.map (Function.Embedding.subtype _) ⊆ S := by
    intro ρ hρ
    obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_map.mp hρ
    refine Finset.mem_map.mpr ⟨Cvs.Criterion.zeroEquiv.symm ρ', ?_, by simp⟩
    have hv : (nontrivialZetaZeroValue (Cvs.Criterion.zeroEquiv.symm ρ')).im
        = (((ρ' : nonTrivialZeroSet) : ℂ)).im := by
      rw [← Cvs.Criterion.coe_zeroEquiv, Equiv.apply_symm_apply]
    rw [Finset.mem_sdiff, mem_nontrivialZetaZeroWindowFinset, mem_nontrivialZetaZeroWindowFinset, hv]
    exact ⟨hB ρ' hρ', not_le.mpr ρ'.2⟩
  have hg0 : ∀ ρ, 0 ≤ g ρ := fun ρ => by positivity
  calc ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ) / (((ρ : nonTrivialZeroSet) : ℂ)).im ^ 2
      = ∑ ρ ∈ F.map (Function.Embedding.subtype _), g ρ := by
        rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        simp only [g, Function.Embedding.coe_subtype, Cvs.GaussKernel.gam, sq_abs]; ring
    _ ≤ ∑ ρ ∈ S, g ρ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun ρ _ _ => hg0 ρ
    _ ≤ ∑ j ∈ Finset.range n, 1 / ((2 : ℝ) ^ j * T) ^ 2
          * (8 * ((2 : ℝ) ^ j * T) * Real.log (2 * ((2 : ℝ) ^ j * T))) :=
        Cvs.Zeta.ZeroCounting.DyadicTailZeroSide.tail_le_zeroSet (f := fun t => 1 / t ^ 2) hT
          (fun a b ha hab => one_div_le_one_div_of_le (pow_pos (by linarith) 2) (pow_le_pow_left₀ (by linarith) hab 2))
          (fun t _ => by positivity) n
    _ ≤ tailBound T := dyadic_sum_le (by linarith) n

/-- **The zeros above `T` against `1/γ²`**: for `9 + e ≤ 2T`, `ρ ↦ m_ρ/γ²` is summable over `|γ| > T` and
`Σ_{|γ| > T} m_ρ/γ² ≤ 16 log(4T)/T`. -/
theorem tsum_le_tailBound {T : ℝ} (hT : 9 + Real.exp 1 ≤ 2 * T) :
    Summable (fun ρ : {ρ : nonTrivialZeroSet // T < |(ρ : ℂ).im|} =>
        (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ) / (((ρ : nonTrivialZeroSet) : ℂ)).im ^ 2)
      ∧ ∑' ρ : {ρ : nonTrivialZeroSet // T < |(ρ : ℂ).im|},
        (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ) / (((ρ : nonTrivialZeroSet) : ℂ)).im ^ 2
      ≤ tailBound T :=
  have h0 : 0 ≤ fun ρ : {ρ : nonTrivialZeroSet // T < |(ρ : ℂ).im|} =>
      (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ) / (((ρ : nonTrivialZeroSet) : ℂ)).im ^ 2 :=
    fun ρ => by positivity
  ⟨summable_of_sum_le h0 (sum_le_tailBound hT), Real.tsum_le_of_sum_le h0 (sum_le_tailBound hT)⟩

end Cvs.Zeta.ZeroTailInverseSquare
