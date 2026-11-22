import Mathlib
import Cvs.L2a.CutoffDerivativeSup
import Cvs.L2a.CutoffFactorSupNorms
import Cvs.L2a.HierarchyFactorDecay
import Cvs.L2a.HierarchyFactorDerivativeDecay
import Cvs.L2a.HierarchyModePairNode
import Cvs.L2a.TreeBoundModePair
import Cvs.L2a.TreeConstantSupBounds
import Cvs.L2a.TreeStepModePair
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.SineSquaredBump

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The explicit tree bound of a mode pair under the plateau bump

For `2 ≤ m₁ < m₂` the node of the empty path on `[19/20, 3/2]` with the weight `bump (19/20) (3/2) h₂` obeys
`|node| ≤ N₀ · T_m(N)` with `T_m(N) = Σ_{j<N} ρ^j E(j) + ρ^N (1/m₁ + 1/m₂)/2` and every constant explicit: the
sup norms of the factors at `θ₀ = 19/20` (Cvs.L2a.CutoffFactorSupNorms), the `V`-norm constants on `[19/20 − h, 3/2 + h]` (Cvs.L2a.TreeConstantSupBounds), the
`f u` constants from the decay of the factors (Cvs.L2a.HierarchyFactorDecay, Cvs.L2a.HierarchyFactorDerivativeDecay), `S' = π/h₂` (Cvs.L2a.CutoffDerivativeSup): the project bound (Cvs.L2a.TreeBoundModePair) instantiated.
-/

namespace Cvs.L2a.ExplicitTreeBoundPlateau

open Real Set Finset Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.Upstream.SineSquaredBump Cvs.L2a.TreeStepModePair Cvs.L2a.TreeBoundModePair Cvs.L2a.TreeConstantSupBounds Cvs.L2a.CutoffFactorSupNorms Cvs.L2a.CutoffDerivativeSup Cvs.L2a.HierarchyFactorDecay Cvs.L2a.HierarchyFactorDerivativeDecay

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The majorant constant `A` of the `V`-norm bump on `[α, ∞)` (Cvs.L2a.TreeConstantSupBounds): `q̂ = c²m² − χ̄/α²`. -/
noncomputable def Ac (c m χb h α : ℝ) : ℝ :=
  2 * ((Real.pi / h) ^ 2 / (c ^ 2 * m ^ 2 - χb / α ^ 2) + 4 * c ^ 4 * m ^ 4 / ((c ^ 2 * m ^ 2 - χb / α ^ 2) ^ 3 * α ^ 2))
/-- The constant `B = 1/q̄(α)²`. -/
noncomputable def Bconst (c m χb α : ℝ) : ℝ := 1 / qb c m χb α ^ 2

/-- The `f u` constant of a factor decaying like `a/θ²` with derivative `a'/θ³` on `[θ₀, ∞)`, against the mode `m`. -/
noncomputable def Cf (c m S' a a' θ₀ : ℝ) : ℝ := c ^ 2 * (m ^ 2) ^ 3 * (S' * a + a' / θ₀) ^ 2

/-- **The `f u` constant from the decay of a factor** (Cvs.L2a.HierarchyFactorDerivativeDecay): `(S'|g| + |g'|)² P(θ) ≤ Cf` for `θ ≥ θ₀`. -/
theorem fu_const_of {c m χb S' θ₀ θ a a' g g' : ℝ} (hS' : 0 ≤ S') (ha : 0 ≤ a) (ha' : 0 ≤ a') (hθ₀ : 0 < θ₀)
    (hθ : θ₀ ≤ θ) (hg : |g| ≤ a / θ ^ 2) (hg' : |g'| ≤ a' / θ ^ 3) (hχb : 0 ≤ χb) (hm : 0 ≤ m)
    (h1 : 1 ≤ m ^ 2 * θ ^ 2) (hq : 0 ≤ c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2 - m ^ 2 * χb) :
    (S' * |g| + |g'|) ^ 2 * ((m ^ 2 * θ ^ 2 - 1) * (c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2 - m ^ 2 * χb))
      ≤ Cf c m S' a a' θ₀ :=
  fu_const_le hS' ha ha' hθ₀ hθ hg hg' (mul_nonneg (by linarith) hq) (centred_prod_le hχb hm h1 hq)

/-- `Cf ≥ 0`. -/
theorem Cf_nonneg (c m S' a a' θ₀ : ℝ) : 0 ≤ Cf c m S' a a' θ₀ := by unfold Cf; positivity

/-- The explicit tree bound of a mode pair `(m₁, m₂)` at depth `N`. -/
noncomputable def Tm (c m₁ m₂ χb χm Sp h h₂ ε δ μ₁ μ₂ : ℝ) (N : ℕ) : ℝ :=
  (∑ j ∈ range N, (m₂ ^ 2 * κ₁m c (m₁ ^ 2) (m₂ ^ 2) * χm + m₁ ^ 2 * κ₂m c (m₁ ^ 2) (m₂ ^ 2) * χm) ^ j
      * Ecost m₁ m₂ μ₁ μ₂ (Real.pi / h₂) (κ₁m c (m₁ ^ 2) (m₂ ^ 2)) (κ₂m c (m₁ ^ 2) (m₂ ^ 2))
          (κ₁'m c (m₁ ^ 2) (m₂ ^ 2)) (κ₂'m c (m₁ ^ 2) (m₂ ^ 2))
          (Cf c m₂ (Real.pi / h₂) (a₁ c (m₁ ^ 2) (m₂ ^ 2) (19 / 20)) (a₁' c (m₁ ^ 2) (m₂ ^ 2) (19 / 20)) (19 / 20))
          (Cf c m₁ (Real.pi / h₂) (a₂ c (m₁ ^ 2) (m₂ ^ 2) (19 / 20)) (a₂' c (m₁ ^ 2) (m₂ ^ 2) (19 / 20)) (19 / 20))
          (Vc m₁ ε δ (Ac c m₁ χb h (19 / 20 - h)) (Bconst c m₁ χb (19 / 20 - h)) Sp)
          (Vc m₂ ε δ (Ac c m₂ χb h (19 / 20 - h)) (Bconst c m₂ χb (19 / 20 - h)) Sp) j j)
    + (m₂ ^ 2 * κ₁m c (m₁ ^ 2) (m₂ ^ 2) * χm + m₁ ^ 2 * κ₂m c (m₁ ^ 2) (m₂ ^ 2) * χm) ^ N * ((1 / m₁ + 1 / m₂) / 2)

/-- `q̄(α) > 0` for `m ≥ 1` when `χ̄ < c²α²`. -/
theorem qb_pos_of {c m χb α : ℝ} (hm : 1 ≤ m) (hα : 0 < α) (hχb : χb < c ^ 2 * α ^ 2) : 0 < qb c m χb α := by
  unfold qb
  have hm2 : (1:ℝ) ≤ m ^ 2 := by nlinarith
  have : c ^ 2 * α ^ 2 ≤ c ^ 2 * m ^ 2 * α ^ 2 := by
    have := mul_le_mul_of_nonneg_left hm2 (by positivity : (0:ℝ) ≤ c ^ 2 * α ^ 2); linarith
  have h1 : 0 < c ^ 2 * m ^ 2 * α ^ 2 - χb := by linarith
  have : 0 < m ^ 2 * (c ^ 2 * m ^ 2 * α ^ 2 - χb) := mul_pos (by positivity) h1
  nlinarith

set_option maxHeartbeats 800000 in
/-- **The explicit tree bound of a mode pair.** -/
theorem mode_pair_bound {c χb χm Sp h h₂ ε δ μ₁ μ₂ : ℝ} {a χ Mm : ι → ℝ} {ψ u : ι → ℝ → ℝ} (K : ι → ι → ℝ)
    {m₁ m₂ : ℕ} (hm₁ : 2 ≤ m₁) (hm₁₂ : m₁ < m₂) (N : ℕ)
    (hc : 0 < c) (hh : 0 < h) (hh' : h ≤ 2 / 5) (hh₂ : 0 < h₂)
    (hχb : χb < c ^ 2 * (19 / 20 - h) ^ 2) (hχb0 : 0 ≤ χb)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hχm : 0 < χm) (hM : ∀ i, 0 < Mm i) (hS : ∀ i, |χ i - χb| ≤ Sp)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) (huc : ∀ i, Continuous (u i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hN₀ : 0 < ∑ i, a i ^ 2 * Mm i) :
    |node c (m₁ : ℝ) (m₂ : ℝ) (19 / 20) (3 / 2) (bump (19 / 20) (3 / 2) h₂) a χ ψ []|
      ≤ (∑ i, a i ^ 2 * Mm i) * Tm c m₁ m₂ χb χm Sp h h₂ ε δ μ₁ μ₂ N := by
  have hm₁r : (2 : ℝ) ≤ m₁ := by exact_mod_cast hm₁
  have hm₁₂r : (m₁ : ℝ) + 1 ≤ m₂ := by exact_mod_cast hm₁₂
  have hm₁0 : (0:ℝ) < m₁ := by linarith
  have hm₂0 : (0:ℝ) < m₂ := by linarith
  have hm₂r : (2 : ℝ) ≤ m₂ := by linarith
  have hs : (4:ℝ) ≤ (m₁:ℝ) ^ 2 := by nlinarith
  have hst : (m₁:ℝ) ^ 2 + 5 ≤ (m₂:ℝ) ^ 2 := by nlinarith
  have hα : 0 < (19 / 20 : ℝ) - h := by linarith
  have hα₁ : 1 < (m₁:ℝ) * (19 / 20 - h) := by nlinarith
  have hχb₁ : χb < c ^ 2 * (m₁:ℝ) ^ 2 * (19 / 20 - h) ^ 2 := by
    have h1 : (1:ℝ) ≤ (m₁:ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ c ^ 2 * (19 / 20 - h) ^ 2)
    linarith
  -- the plateau bump as the weight
  have hσ : ∀ θ ∈ Icc (19 / 20 : ℝ) (3 / 2),
      HasDerivAt (bump (19 / 20) (3 / 2) h₂) (bump' (19 / 20) (3 / 2) h₂ θ) θ := fun θ _ => hasDerivAt_bump hh₂ θ
  have hσ'c : ContinuousOn (bump' (19 / 20) (3 / 2) h₂) (Icc (19 / 20 : ℝ) (3 / 2)) :=
    (continuous_bump' hh₂).continuousOn
  have hσL : bump (19 / 20) (3 / 2) h₂ (19 / 20) = 0 := bump_of_le le_rfl
  have hσR : bump (19 / 20) (3 / 2) h₂ (3 / 2) = 0 := bump_of_ge le_rfl
  have hσ1 : ∀ θ ∈ Icc (19 / 20 : ℝ) (3 / 2), |bump (19 / 20) (3 / 2) h₂ θ| ≤ 1 := fun θ _ => by
    rw [abs_of_nonneg (bump_nonneg _ _ _ _)]; exact bump_le_one _ _ _ _
  have hσ'b : ∀ θ ∈ Icc (19 / 20 : ℝ) (3 / 2), |bump' (19 / 20) (3 / 2) h₂ θ| ≤ Real.pi / h₂ :=
    fun θ _ => abs_bump'_le hh₂ θ
  have hS' : 0 < Real.pi / h₂ := by positivity
  -- the factors (Cvs.L2a.CutoffFactorSupNorms) and their positivity
  have hfac : ∀ θ ∈ Icc (19 / 20 : ℝ) (3 / 2),
      |Cvs.L2a.HierarchyModePairNode.g₁ c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) θ| ≤ κ₁m c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) ∧
      |Cvs.L2a.HierarchyModePairNode.g₂ c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) θ| ≤ κ₂m c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) ∧
      |Cvs.L2a.HierarchyModePairNode.g₁' c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) θ| ≤ κ₁'m c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) ∧
      |Cvs.L2a.HierarchyModePairNode.g₂' c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) θ| ≤ κ₂'m c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) :=
    fun θ hθ => factors_modes hc hs hst hθ.1
  obtain ⟨c1, c2, hD, -, -⟩ := modes_conditions hs hst
  have hts : (0:ℝ) < (m₂:ℝ) ^ 2 - (m₁:ℝ) ^ 2 := by linarith
  have hden : 0 < c ^ 2 * (361 / 400) * ((m₂:ℝ) ^ 2 - (m₁:ℝ) ^ 2) * ((m₁:ℝ) ^ 2 * (m₂:ℝ) ^ 2 * (361 / 400) - (m₂:ℝ) ^ 2 - (m₁:ℝ) ^ 2) :=
    mul_pos (mul_pos (mul_pos (by positivity) (by norm_num)) hts) (by linarith)
  have hκ₁ : 0 < κ₁m c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) := by unfold κ₁m; exact div_pos (by linarith) hden
  have hκ₂ : 0 < κ₂m c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) := by unfold κ₂m; exact div_pos (by linarith) hden
  have hCd : 0 < (m₁:ℝ) ^ 2 * (m₂:ℝ) ^ 2 - ((m₂:ℝ) ^ 2 + (m₁:ℝ) ^ 2) / (19 / 20 : ℝ) ^ 2 := by
    rw [sub_pos, div_lt_iff₀ (by norm_num)]; norm_num; linarith
  have hden' : 0 < c ^ 2 * ((m₂:ℝ) ^ 2 - (m₁:ℝ) ^ 2) * (19 / 20 : ℝ) ^ 3
      * ((m₁:ℝ) ^ 2 * (m₂:ℝ) ^ 2 - ((m₂:ℝ) ^ 2 + (m₁:ℝ) ^ 2) / (19 / 20 : ℝ) ^ 2) ^ 2 :=
    mul_pos (mul_pos (mul_pos (by positivity) hts) (by norm_num)) (pow_pos hCd 2)
  have hκ₁' : 0 ≤ κ₁'m c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) := by unfold κ₁'m; exact div_nonneg (by positivity) hden'.le
  have hκ₂' : 0 ≤ κ₂'m c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) := by unfold κ₂'m; exact div_nonneg (by positivity) hden'.le
  -- the `V`-norm constants (Cvs.L2a.TreeConstantSupBounds)
  have hqα : ∀ m : ℝ, 1 ≤ m → 0 < qb c m χb (19 / 20 - h) := fun m hm => qb_pos_of hm hα hχb
  have hA : ∀ m : ℝ, 1 ≤ m → ∀ θ ∈ Icc (19 / 20 - h) (3 / 2 + h),
      2 * (m ^ 2 * θ ^ 2 - 1) * ((Real.pi / h) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb)
        + (2 * c ^ 2 * m ^ 4 * θ) ^ 2 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 3)
      ≤ Ac c m χb h (19 / 20 - h) := fun m hm θ hθ => by
    have hχbm : χb < c ^ 2 * m ^ 2 * (19 / 20 - h) ^ 2 := by
      have h1 : (1:ℝ) ≤ m ^ 2 := one_le_pow₀ hm
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ c ^ 2 * (19 / 20 - h) ^ 2)
      nlinarith
    exact W2_le_uniform hh hα (by linarith) hχb0 hχbm hθ.1
  have hB : ∀ m : ℝ, 1 ≤ m → ∀ θ ∈ Icc (19 / 20 - h) (3 / 2 + h),
      1 / (c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb) ^ 2 ≤ Bconst c m χb (19 / 20 - h) :=
    fun m hm θ hθ => qb_inv_sq_le hα (hqα m hm) hθ
  have hqL : ∀ m : ℝ, 1 ≤ m → 0 ≤ qb c m χb (19 / 20) :=
    fun m hm => (hqα m hm).le.trans (qb_mono hα.le (by linarith))
  -- the `f u` constants (Cvs.L2a.HierarchyFactorDecay, Cvs.L2a.HierarchyFactorDerivativeDecay)
  have hθ₀ : (0:ℝ) < 19 / 20 := by norm_num
  have hD' : (m₂:ℝ) ^ 2 + (m₁:ℝ) ^ 2 < (m₁:ℝ) ^ 2 * (m₂:ℝ) ^ 2 * (19 / 20 : ℝ) ^ 2 := by
    rw [show (19 / 20 : ℝ) ^ 2 = 361 / 400 by norm_num]; exact hD
  have hs0 : (0:ℝ) < (m₁:ℝ) ^ 2 := by positivity
  have hts' : (m₁:ℝ) ^ 2 < (m₂:ℝ) ^ 2 := by linarith
  have hCd' := Cd_pos hθ₀ hD'
  have hdenA : 0 ≤ c ^ 2 * ((m₂:ℝ) ^ 2 - (m₁:ℝ) ^ 2) * Cd ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hts.le) hCd'.le
  have hdenA' : 0 ≤ c ^ 2 * ((m₂:ℝ) ^ 2 - (m₁:ℝ) ^ 2) * Cd ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20) ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hts.le) (sq_nonneg _)
  have ha₁ : 0 ≤ a₁ c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20) := div_nonneg hs0.le hdenA
  have ha₂ : 0 ≤ a₂ c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20) := div_nonneg (by positivity) hdenA
  have ha₁' : 0 ≤ a₁' c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20) := div_nonneg (by positivity) hdenA'
  have ha₂' : 0 ≤ a₂' c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20) := div_nonneg (by positivity) hdenA'
  have hq : ∀ m : ℝ, 1 ≤ m → ∀ θ ∈ Icc (19 / 20 : ℝ) (3 / 2), 0 ≤ c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2 - m ^ 2 * χb :=
    fun m hm θ hθ => by
      have := (hqL m hm).trans (qb_mono (by norm_num) hθ.1)
      unfold qb at this
      have e : c ^ 2 * (m ^ 2) ^ 2 * θ ^ 2 - m ^ 2 * χb = c ^ 2 * m ^ 4 * θ ^ 2 - m ^ 2 * χb := by ring
      rw [e]; exact this
  have h1 : ∀ m : ℝ, 2 ≤ m → ∀ θ ∈ Icc (19 / 20 : ℝ) (3 / 2), 1 ≤ m ^ 2 * θ ^ 2 := fun m hm θ hθ => by
    have hθ2 : (361 / 400 : ℝ) ≤ θ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 19 / 20) hθ.1 2
      norm_num at this; linarith
    nlinarith [mul_le_mul (by nlinarith : (4:ℝ) ≤ m ^ 2) hθ2 (by norm_num) (by positivity)]
  have hC₁ : ∀ θ ∈ Icc (19 / 20 : ℝ) (3 / 2),
      (Real.pi / h₂ * |Cvs.L2a.HierarchyModePairNode.g₁ c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) θ|
          + |Cvs.L2a.HierarchyModePairNode.g₁' c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) θ|) ^ 2
        * (((m₂:ℝ) ^ 2 * θ ^ 2 - 1) * (c ^ 2 * ((m₂:ℝ) ^ 2) ^ 2 * θ ^ 2 - (m₂:ℝ) ^ 2 * χb))
      ≤ Cf c m₂ (Real.pi / h₂) (a₁ c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20)) (a₁' c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20))
          (19 / 20) := fun θ hθ =>
    fu_const_of hS'.le ha₁ ha₁' hθ₀ hθ.1 (abs_g₁_decay hc hs0 hts' hθ₀ hD' hθ.1) (abs_g₁'_decay hc hs0 hts' hθ₀ hD' hθ.1)
      hχb0 hm₂0.le (h1 m₂ hm₂r θ hθ) (hq m₂ (by linarith) θ hθ)
  have hC₂ : ∀ θ ∈ Icc (19 / 20 : ℝ) (3 / 2),
      (Real.pi / h₂ * |Cvs.L2a.HierarchyModePairNode.g₂ c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) θ|
          + |Cvs.L2a.HierarchyModePairNode.g₂' c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) θ|) ^ 2
        * (((m₁:ℝ) ^ 2 * θ ^ 2 - 1) * (c ^ 2 * ((m₁:ℝ) ^ 2) ^ 2 * θ ^ 2 - (m₁:ℝ) ^ 2 * χb))
      ≤ Cf c m₁ (Real.pi / h₂) (a₂ c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20)) (a₂' c ((m₁:ℝ) ^ 2) ((m₂:ℝ) ^ 2) (19 / 20))
          (19 / 20) := fun θ hθ =>
    fu_const_of hS'.le ha₂ ha₂' hθ₀ hθ.1 (abs_g₂_decay hc hs0 hts' hθ₀ hD' hθ.1) (abs_g₂'_decay hc hs0 hts' hθ₀ hD' hθ.1)
      hχb0 hm₁0.le (h1 m₁ hm₁r θ hθ) (hq m₁ (by linarith) θ hθ)
  have h := pair_tree_bound (a := a) (χ := χ) (Mm := Mm) (ψ := ψ) (u := u) K hc hm₁r hm₁₂r (le_refl (19 / 20 : ℝ))
    (by norm_num) hh hα₁ hχb₁ hχ hχm (fun i => (hM i).le) hS hε hε2 hδ hμ₁ hμ₂ hψ hu hψc huc hcross hmass
    hσ hσ'c hσL hσR hσ1 hσ'b hS' hκ₁ hκ₂ hκ₁' hκ₂'
    (fun θ hθ => (hfac θ hθ).1) (fun θ hθ => (hfac θ hθ).2.1) (fun θ hθ => (hfac θ hθ).2.2.1)
    (fun θ hθ => (hfac θ hθ).2.2.2)
    (hA m₁ (by linarith)) (hB m₁ (by linarith)) (hA m₂ (by linarith)) (hB m₂ (by linarith))
    hC₁ hC₂ hN₀ (Cf_nonneg _ _ _ _ _ _) (Cf_nonneg _ _ _ _ _ _) N
  rw [mul_comm]
  exact h

end Cvs.L2a.ExplicitTreeBoundPlateau
