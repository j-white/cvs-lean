import Mathlib
import Cvs.L2a.CutoffFactorSupNorms
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.HierarchyFactorDecay
import Cvs.L2a.HierarchyNodeWeight
import Cvs.L2a.TreeConstantScaling
import Cvs.L2a.TreeStepModePair

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The explicit tree bounds scale like `1/c`

With `χ̄ = c²χ̂`, `χ_max = c²χ̂_m`, spread `c²Ŝ`, `μ_i = c μ̂_i` and rung sums `c q₁`, `c³ q₂`: the depth ratios `ρ`
are `c`-free, and the project bound of a mode pair is at most the unit level sum over `c` plus the `c`-free leaf,
`T_m ≤ L_m/c + ρ^N (1/m₁ + 1/m₂)/2`; for a pair `(1, m)`, `T_f ≤ L_f/c + B_d Σ_{j<N} ρ^j + ρ^N (1 + 1/m)/2`.
-/

namespace Cvs.L2a.TreeBoundInverseScaling

open Real Finset Cvs.L2a.HierarchyNodeWeight Cvs.L2a.TreeStepModePair Cvs.L2a.TreeConstantSupBounds Cvs.L2a.CutoffFactorSupNorms Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.HierarchyFactorDecay Cvs.L2a.TreeConstantScaling

/-- The `c`-free depth ratio of a mode pair. -/
noncomputable def ρm (m₁ m₂ χm : ℝ) : ℝ :=
  m₂ ^ 2 * κ₁m 1 (m₁ ^ 2) (m₂ ^ 2) * χm + m₁ ^ 2 * κ₂m 1 (m₁ ^ 2) (m₂ ^ 2) * χm
/-- The `c`-free depth ratio of a pair `(1, m)`. -/
noncomputable def ρf (m χm : ℝ) : ℝ := m ^ 2 * κ₁f 1 (m ^ 2) * χm + 1 * κ₂f 1 (m ^ 2) * χm

/-- The unit level sum of a mode pair (`c = 1`, `μ = μ̂`, the majorant `A` at `c₀`). -/
noncomputable def Lm (m₁ m₂ χh χm Sh h h₂ ε δ μ₁ μ₂ c₀ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ range N, ρm m₁ m₂ χm ^ j
    * Ecost m₁ m₂ μ₁ μ₂ (Real.pi / h₂) (κ₁m 1 (m₁ ^ 2) (m₂ ^ 2)) (κ₂m 1 (m₁ ^ 2) (m₂ ^ 2))
        (κ₁'m 1 (m₁ ^ 2) (m₂ ^ 2)) (κ₂'m 1 (m₁ ^ 2) (m₂ ^ 2))
        (Cvs.L2a.ExplicitTreeBoundPlateau.Cf 1 m₂ (Real.pi / h₂) (a₁ 1 (m₁ ^ 2) (m₂ ^ 2) (19 / 20)) (a₁' 1 (m₁ ^ 2) (m₂ ^ 2) (19 / 20)) (19 / 20))
        (Cvs.L2a.ExplicitTreeBoundPlateau.Cf 1 m₁ (Real.pi / h₂) (a₂ 1 (m₁ ^ 2) (m₂ ^ 2) (19 / 20)) (a₂' 1 (m₁ ^ 2) (m₂ ^ 2) (19 / 20)) (19 / 20))
        (Vc m₁ ε δ (Ac 1 m₁ χh h (19 / 20 - h) / c₀ ^ 2) (Bconst 1 m₁ χh (19 / 20 - h)) Sh)
        (Vc m₂ ε δ (Ac 1 m₂ χh h (19 / 20 - h) / c₀ ^ 2) (Bconst 1 m₂ χh (19 / 20 - h)) Sh) j j

/-- The unit level sum of a pair `(1, m)` without its boundary term (the majorant `A` at `c₀`). -/
noncomputable def Lf (m χh χm Sh h hη b ε δ μ₁ μ₂ c₀ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ range N, ρf m χm ^ j
    * Ecost 1 m μ₁ μ₂ (Real.pi / (2 * hη)) (κ₁f 1 (m ^ 2)) (κ₂f 1 (m ^ 2)) (κ₁'f 1 (m ^ 2)) (κ₂'f 1 (m ^ 2))
        (Cvs.L2a.ExplicitTreeBoundPlateau.Cf 1 m (Real.pi / (2 * hη)) (a₁ 1 1 (m ^ 2) (4 / 3)) (a₁' 1 1 (m ^ 2) (4 / 3)) (4 / 3))
        (Cvs.L2a.ExplicitTreeBoundPlateau.Cf 1 1 (Real.pi / (2 * hη)) (a₂ 1 1 (m ^ 2) (4 / 3)) (a₂' 1 1 (m ^ 2) (4 / 3)) (4 / 3))
        (Vc 1 ε δ (Ac 1 1 χh h (4 / 3 - h) / c₀ ^ 2) (Bconst 1 1 χh (4 / 3 - h)) Sh)
        (Vc m ε δ (Ac 1 m χh h (4 / 3 - h) / c₀ ^ 2) (Bconst 1 m χh (4 / 3 - h)) Sh) j j

/-- The level cost depends on the sup norms only through `grow0`, so a common scaling of them is invisible. -/
theorem Ecost_congr_scale {c : ℝ} (hc : c ≠ 0) (m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ : ℝ) (k l : ℕ) :
    Ecost m₁ m₂ μ₁ μ₂ S' (κ₁ / c ^ 2) (κ₂ / c ^ 2) (κ₁' / c ^ 2) (κ₂' / c ^ 2) C₁ C₂ V₁ V₂ k l
      = Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ k l := by
  unfold Ecost; rw [grow0_scale hc]

/-- The level cost is monotone in the `V`-norm constants. -/
theorem Ecost_mono_V {m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ V₁' V₂' : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (h₁ : V₁ ≤ V₁') (h₂ : V₂ ≤ V₂') (k l : ℕ) :
    Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ k l ≤ Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁' V₂' k l := by
  unfold Ecost
  have := div_le_div_of_nonneg_right h₂ (by positivity : (0:ℝ) ≤ 2 * μ₁)
  have := div_le_div_of_nonneg_right h₁ (by positivity : (0:ℝ) ≤ 2 * μ₂)
  linarith

/-- `A ≥ 0` at `c = 1` once `m² ≥ χ̂/α²`. -/
theorem Ac_unit_nonneg {m χh h α : ℝ} (hq : 0 ≤ m ^ 2 - χh / α ^ 2) : 0 ≤ Ac 1 m χh h α := by
  unfold Ac
  have e : (1:ℝ) ^ 2 * m ^ 2 - χh / α ^ 2 = m ^ 2 - χh / α ^ 2 := by ring
  rw [e]
  set X := m ^ 2 - χh / α ^ 2
  positivity

/-- The depth ratio of a mode pair is nonnegative. -/
theorem ρm_nonneg {m₁ m₂ χm : ℝ} (hm₁ : 2 ≤ m₁) (hm₁₂ : m₁ + 1 ≤ m₂) (hχm : 0 ≤ χm) : 0 ≤ ρm m₁ m₂ χm := by
  have hs : (4:ℝ) ≤ m₁ ^ 2 := by nlinarith
  have hst : m₁ ^ 2 + 5 ≤ m₂ ^ 2 := by nlinarith
  have hts : 0 < m₂ ^ 2 - m₁ ^ 2 := by linarith
  have hden : 0 < (1:ℝ) ^ 2 * (361 / 400) * (m₂ ^ 2 - m₁ ^ 2) * (m₁ ^ 2 * m₂ ^ 2 * (361 / 400) - m₂ ^ 2 - m₁ ^ 2) := by
    apply mul_pos (mul_pos (by norm_num) hts); nlinarith
  have h1 : 0 ≤ κ₁m 1 (m₁ ^ 2) (m₂ ^ 2) := by unfold κ₁m; exact div_nonneg (by linarith) hden.le
  have h2 : 0 ≤ κ₂m 1 (m₁ ^ 2) (m₂ ^ 2) := by unfold κ₂m; exact div_nonneg (by linarith) hden.le
  unfold ρm; positivity

/-- The depth ratio of a pair `(1, m)` is nonnegative. -/
theorem ρf_nonneg {m χm : ℝ} (hm : 2 ≤ m) (hχm : 0 ≤ χm) : 0 ≤ ρf m χm := by
  have ht : (4:ℝ) ≤ m ^ 2 := by nlinarith
  have hts : 0 < m ^ 2 - 1 := by linarith
  have hden : 0 < (1:ℝ) ^ 2 * (16 / 9) * (m ^ 2 - 1) * (1 * m ^ 2 * (16 / 9) - m ^ 2 - 1) := by
    apply mul_pos (mul_pos (by norm_num) hts); nlinarith
  have h1 : 0 ≤ κ₁f 1 (m ^ 2) := by unfold κ₁f; exact div_nonneg (by norm_num) hden.le
  have h2 : 0 ≤ κ₂f 1 (m ^ 2) := by unfold κ₂f; exact div_nonneg (by linarith) hden.le
  unfold ρf; positivity

set_option maxHeartbeats 800000 in
/-- **The tree bound of a mode pair scales like `1/c`**: `T_m(c) ≤ L_m/c + ρ^N (1/m₁ + 1/m₂)/2`. -/
theorem Tm_scale {c c₀ m₁ m₂ χh χm Sh h h₂ ε δ μ₁ μ₂ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) (hm₁ : 2 ≤ m₁)
    (hm₁₂ : m₁ + 1 ≤ m₂)
    (hχm : 0 ≤ χm) (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hq₁ : 0 ≤ m₁ ^ 2 - χh / (19 / 20 - h) ^ 2) (hq₂ : 0 ≤ m₂ ^ 2 - χh / (19 / 20 - h) ^ 2) (N : ℕ) :
    Tm c m₁ m₂ (c ^ 2 * χh) (c ^ 2 * χm) (c ^ 2 * Sh) h h₂ ε δ (c * μ₁) (c * μ₂) N
      ≤ Lm m₁ m₂ χh χm Sh h h₂ ε δ μ₁ μ₂ c₀ N / c + ρm m₁ m₂ χm ^ N * ((1 / m₁ + 1 / m₂) / 2) := by
  have hc0 : 0 < c := by linarith
  have hc' : c ≠ 0 := hc0.ne'
  have hm₁0 : 0 < m₁ := by linarith
  have hm₂0 : 0 < m₂ := by linarith
  have eρ : m₂ ^ 2 * κ₁m c (m₁ ^ 2) (m₂ ^ 2) * (c ^ 2 * χm) + m₁ ^ 2 * κ₂m c (m₁ ^ 2) (m₂ ^ 2) * (c ^ 2 * χm)
      = ρm m₁ m₂ χm := by
    unfold ρm; rw [κ₁m_scale, κ₂m_scale]; field_simp
  unfold Tm
  rw [eρ, κ₁m_scale, κ₂m_scale, κ₁'m_scale, κ₂'m_scale, a₁_scale, a₂_scale, a₁'_scale, a₂'_scale,
    Cf_scale hc', Cf_scale hc', Ac_scale hc', Ac_scale hc', Bconst_scale hc', Bconst_scale hc']
  unfold Lm
  rw [Finset.sum_div]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro j _
  rw [Ecost_congr_scale hc', Ecost_scale hc', ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hc0.le
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (ρm_nonneg hm₁ hm₁₂ hχm) j)
  apply Ecost_mono_V hμ₁ hμ₂
  · exact Vc_scale_le hc₀ hc hm₁0 hε hε2 hδ (Ac_unit_nonneg hq₁)
  · exact Vc_scale_le hc₀ hc hm₂0 hε hε2 hδ (Ac_unit_nonneg hq₂)

set_option maxHeartbeats 800000 in
/-- **The tree bound of a pair `(1, m)` scales like `1/c`**, boundary and leaf apart:
`T_f(c) ≤ L_f/c + B_d Σ_{j<N} ρ^j + ρ^N (1 + 1/m)/2` for rung sums `c q₁`, `c³ q₂`. -/
theorem Tf_scale {c c₀ m χh χm Sh h hη b ε δ μ₁ μ₂ q₁ q₂ : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) (hm : 2 ≤ m)
    (hχm : 0 ≤ χm) (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hq₁ : 0 ≤ 1 ^ 2 - χh / (4 / 3 - h) ^ 2) (hq₂ : 0 ≤ m ^ 2 - χh / (4 / 3 - h) ^ 2) (N : ℕ) :
    Tf c m (c ^ 2 * χh) (c ^ 2 * χm) (c ^ 2 * Sh) h hη b ε δ (c * μ₁) (c * μ₂) (c * q₁) (c ^ 3 * q₂) N
      ≤ Lf m χh χm Sh h hη b ε δ μ₁ μ₂ c₀ N / c + Bd 1 m b q₁ q₂ * ∑ j ∈ range N, ρf m χm ^ j
        + ρf m χm ^ N * ((1 / 1 + 1 / m) / 2) := by
  have hc0 : 0 < c := by linarith
  have hc' : c ≠ 0 := hc0.ne'
  have hm0 : 0 < m := by linarith
  have eρ : m ^ 2 * κ₁f c (m ^ 2) * (c ^ 2 * χm) + 1 * κ₂f c (m ^ 2) * (c ^ 2 * χm) = ρf m χm := by
    unfold ρf; rw [κ₁f_scale, κ₂f_scale]; field_simp
  unfold Tf
  rw [eρ, κ₁f_scale, κ₂f_scale, κ₁'f_scale, κ₂'f_scale, a₁_scale, a₂_scale, a₁'_scale, a₂'_scale,
    Cf_scale hc', Cf_scale hc', Ac_scale hc', Ac_scale hc', Bconst_scale hc', Bconst_scale hc', Bd_scale hc0]
  unfold Lf
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro j _
  rw [Ecost_congr_scale hc', Ecost_scale hc', mul_add, ← mul_div_assoc, mul_comm (Bd 1 m b q₁ q₂)]
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ hc0.le
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (ρf_nonneg hm hχm) j)
  apply Ecost_mono_V hμ₁ hμ₂
  · exact Vc_scale_le hc₀ hc one_pos hε hε2 hδ (Ac_unit_nonneg hq₁)
  · exact Vc_scale_le hc₀ hc hm0 hε hε2 hδ (Ac_unit_nonneg hq₂)

end Cvs.L2a.TreeBoundInverseScaling
