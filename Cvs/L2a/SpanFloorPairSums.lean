import Mathlib
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.TailFloorFromPairNodes
import Cvs.L2a.TreeBoundInverseScaling

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pair sums of the span floor are `K/c + Λ`

At `χ̄ = c²χ̂`, `χ_max = c²χ̂_m`, spread `c²Ŝ`, `μ_i = c μ̂_i` and rung sums `c q₁`, `c³ q₂`, the pair sums of the span
floor (Cvs.L2a.SpanTailFloorMassSum) are at most `K/c + Λ`, with `K` the symmetrised unit level sums over the mode pairs and the first
pairs (Cvs.L2a.TreeBoundInverseScaling) and `Λ` the `c`-free leaves and boundary terms.
-/

namespace Cvs.L2a.SpanFloorPairSums

open Real Finset Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.TreeBoundInverseScaling

theorem Tsym_le {T T' : ℕ → ℕ → ℝ} {m m' : ℕ} (hne : m ≠ m') (h : m < m' → T m m' ≤ T' m m')
    (h' : m' < m → T m' m ≤ T' m' m) : Tsym T m m' ≤ Tsym T' m m' := by
  unfold Tsym
  by_cases hlt : m < m'
  · simp only [hlt, if_true]; exact h hlt
  · have : m' < m := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
    simp only [hlt, if_false]; exact h' this

theorem Tsym_add (X Y : ℕ → ℕ → ℝ) (m m' : ℕ) :
    Tsym (fun m m' => X m m' + Y m m') m m' = Tsym X m m' + Tsym Y m m' := by
  unfold Tsym; split_ifs <;> rfl

theorem Tsym_div (X : ℕ → ℕ → ℝ) (c : ℝ) (m m' : ℕ) :
    Tsym (fun m m' => X m m' / c) m m' = Tsym X m m' / c := by
  unfold Tsym; split_ifs <;> rfl

/-- The `c`-free coefficient of `1/c` in the pair sums: the unit level sums. -/
noncomputable def Kpair (s χh χm Sh h h₂ hη b ε δ μ₁ μ₂ c₀ : ℝ) (M N : ℕ) : ℝ :=
  1 / s * ∑ m ∈ Icc 2 M, ∑ m' ∈ Icc 2 M,
      (if m = m' then 0 else Tsym (fun m m' => Lm m m' χh χm Sh h h₂ ε δ μ₁ μ₂ c₀ N) m m')
    + 2 * ∑ m ∈ Icc 2 M, Lf m χh χm Sh h hη b ε δ μ₁ μ₂ c₀ N

/-- The `c`-free remainder of the pair sums: the leaves and the boundary terms. -/
noncomputable def Λpair (s χm b q₁ q₂ : ℝ) (M N : ℕ) : ℝ :=
  1 / s * ∑ m ∈ Icc 2 M, ∑ m' ∈ Icc 2 M,
      (if m = m' then 0 else Tsym (fun m m' : ℕ => ρm m m' χm ^ N * ((1 / (m : ℝ) + 1 / m') / 2)) m m')
    + 2 * ∑ m ∈ Icc 2 M,
        (Bd 1 m b q₁ q₂ * ∑ j ∈ range N, ρf m χm ^ j + ρf m χm ^ N * ((1 / 1 + 1 / (m : ℝ)) / 2))

set_option maxHeartbeats 800000 in
/-- **The pair sums are `K/c + Λ`.** -/
theorem pair_sums_le {c c₀ s χh χm Sh h h₂ hη b ε δ μ₁ μ₂ Qψ Qu q₁ q₂ : ℝ} {M N : ℕ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c)
    (hs : 0 < s)
    (hχm : 0 ≤ χm) (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hq : ∀ m : ℝ, 1 ≤ m → 0 ≤ m ^ 2 - χh / (19 / 20 - h) ^ 2)
    (hq' : ∀ m : ℝ, 1 ≤ m → 0 ≤ m ^ 2 - χh / (4 / 3 - h) ^ 2)
    (hQψ : Qψ = c * q₁) (hQu : Qu = c ^ 3 * q₂) :
    1 / s * ∑ m ∈ Icc 2 M, ∑ m' ∈ Icc 2 M,
        (if m = m' then 0
          else Tsym (fun m m' => Tm c m m' (c ^ 2 * χh) (c ^ 2 * χm) (c ^ 2 * Sh) h h₂ ε δ (c * μ₁) (c * μ₂) N) m m')
      + 2 * ∑ m ∈ Icc 2 M, Tf c m (c ^ 2 * χh) (c ^ 2 * χm) (c ^ 2 * Sh) h hη b ε δ (c * μ₁) (c * μ₂) Qψ Qu N
      ≤ Kpair s χh χm Sh h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c + Λpair s χm b q₁ q₂ M N := by
  subst hQψ hQu
  have hs' : 0 ≤ 1 / s := by positivity
  have hmem : ∀ n ∈ Icc 2 M, (2 : ℝ) ≤ n := fun n hn => by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
  have hstep : ∀ n n' : ℕ, n < n' → (n : ℝ) + 1 ≤ n' := fun n n' h => by exact_mod_cast h
  -- the mode pairs, termwise
  have key : ∀ m ∈ Icc 2 M, ∀ m' ∈ Icc 2 M,
      (if m = m' then 0
          else Tsym (fun m m' => Tm c m m' (c ^ 2 * χh) (c ^ 2 * χm) (c ^ 2 * Sh) h h₂ ε δ (c * μ₁) (c * μ₂) N) m m')
        ≤ (if m = m' then 0 else Tsym (fun m m' => Lm m m' χh χm Sh h h₂ ε δ μ₁ μ₂ c₀ N) m m') / c
          + (if m = m' then 0 else Tsym (fun m m' : ℕ => ρm m m' χm ^ N * ((1 / (m : ℝ) + 1 / m') / 2)) m m') := by
    intro m hm m' hm'
    by_cases hmm : m = m'
    · simp [hmm]
    · simp only [hmm, if_false]
      rw [← Tsym_div, ← Tsym_add]
      refine Tsym_le hmm (fun hlt => ?_) (fun hlt => ?_)
      · exact Tm_scale hc₀ hc (hmem m hm) (hstep m m' hlt) hχm hε hε2 hδ hμ₁ hμ₂ (hq _ (by linarith [hmem m hm]))
          (hq _ (by linarith [hmem m' hm'])) N
      · exact Tm_scale hc₀ hc (hmem m' hm') (hstep m' m hlt) hχm hε hε2 hδ hμ₁ hμ₂ (hq _ (by linarith [hmem m' hm']))
          (hq _ (by linarith [hmem m hm])) N
  -- the first pairs, termwise
  have key2 : ∀ m ∈ Icc 2 M, Tf c m (c ^ 2 * χh) (c ^ 2 * χm) (c ^ 2 * Sh) h hη b ε δ (c * μ₁) (c * μ₂) (c * q₁) (c ^ 3 * q₂) N
      ≤ Lf m χh χm Sh h hη b ε δ μ₁ μ₂ c₀ N / c
        + (Bd 1 m b q₁ q₂ * ∑ j ∈ range N, ρf m χm ^ j + ρf m χm ^ N * ((1 / 1 + 1 / (m : ℝ)) / 2)) := by
    intro m hm
    exact (Tf_scale hc₀ hc (hmem m hm) hχm hε hε2 hδ hμ₁ hμ₂ (hq' 1 le_rfl) (hq' _ (by linarith [hmem m hm])) N).trans
      (le_of_eq (add_assoc _ _ _))
  calc _ ≤ 1 / s * ∑ m ∈ Icc 2 M, ∑ m' ∈ Icc 2 M,
          ((if m = m' then 0 else Tsym (fun m m' => Lm m m' χh χm Sh h h₂ ε δ μ₁ μ₂ c₀ N) m m') / c
            + (if m = m' then 0
                else Tsym (fun m m' : ℕ => ρm m m' χm ^ N * ((1 / (m : ℝ) + 1 / m') / 2)) m m'))
        + 2 * ∑ m ∈ Icc 2 M, (Lf m χh χm Sh h hη b ε δ μ₁ μ₂ c₀ N / c
            + (Bd 1 m b q₁ q₂ * ∑ j ∈ range N, ρf m χm ^ j + ρf m χm ^ N * ((1 / 1 + 1 / (m : ℝ)) / 2))) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun m' hm' => key m hm m' hm') hs'
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum key2) (by norm_num)
    _ = _ := by
        unfold Kpair Λpair
        simp only [Finset.sum_add_distrib, ← Finset.sum_div]
        ring

end Cvs.L2a.SpanFloorPairSums
