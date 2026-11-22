import Mathlib
import Cvs.L2a.CutoffFactorSupNorms
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.HierarchyFactorDecay
import Cvs.L2a.HierarchyNodeWeight
import Cvs.L2a.TreeConstantSupBounds
import Cvs.L2a.TreeStepModePair

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The scaling of the explicit constants in `c`

Every explicit constant of the project bound is a `c`-free unit constant times a power of `c`: the sup norms and
decay constants of the factors and the `f u` constants carry `1/c²`, the majorant `A` carries `1/c²` and `B`
carries `1/c⁴` once `χ̄ = c²χh`, the depth ratio `grow0` is `c`-free, and the level cost at `μ = c` is the unit
level cost over `c`.
-/

namespace Cvs.L2a.TreeConstantScaling

open Real Cvs.L2a.HierarchyNodeWeight Cvs.L2a.TreeStepModePair Cvs.L2a.TreeConstantSupBounds Cvs.L2a.CutoffFactorSupNorms Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.HierarchyFactorDecay

theorem κ₁m_scale (c s t : ℝ) : κ₁m c s t = κ₁m 1 s t / c ^ 2 := by
  unfold κ₁m; rw [div_div]; ring_nf
theorem κ₂m_scale (c s t : ℝ) : κ₂m c s t = κ₂m 1 s t / c ^ 2 := by
  unfold κ₂m; rw [div_div]; ring_nf
theorem κ₁'m_scale (c s t : ℝ) : κ₁'m c s t = κ₁'m 1 s t / c ^ 2 := by
  unfold κ₁'m; rw [div_div]; ring_nf
theorem κ₂'m_scale (c s t : ℝ) : κ₂'m c s t = κ₂'m 1 s t / c ^ 2 := by
  unfold κ₂'m; rw [div_div]; ring_nf
theorem κ₁f_scale (c t : ℝ) : κ₁f c t = κ₁f 1 t / c ^ 2 := by
  unfold κ₁f; rw [div_div]; ring_nf
theorem κ₂f_scale (c t : ℝ) : κ₂f c t = κ₂f 1 t / c ^ 2 := by
  unfold κ₂f; rw [div_div]; ring_nf
theorem κ₁'f_scale (c t : ℝ) : κ₁'f c t = κ₁'f 1 t / c ^ 2 := by
  unfold κ₁'f; rw [div_div]; ring_nf
theorem κ₂'f_scale (c t : ℝ) : κ₂'f c t = κ₂'f 1 t / c ^ 2 := by
  unfold κ₂'f; rw [div_div]; ring_nf
theorem κ₁R_scale (c t b : ℝ) : κ₁R c t b = κ₁R 1 t b / c ^ 2 := by
  unfold κ₁R; rw [div_div]; ring_nf
theorem κ₂R_scale (c t b : ℝ) : κ₂R c t b = κ₂R 1 t b / c ^ 2 := by
  unfold κ₂R; rw [div_div]; ring_nf
theorem a₁_scale (c s t θ₀ : ℝ) : a₁ c s t θ₀ = a₁ 1 s t θ₀ / c ^ 2 := by
  unfold a₁; rw [div_div]; ring_nf
theorem a₂_scale (c s t θ₀ : ℝ) : a₂ c s t θ₀ = a₂ 1 s t θ₀ / c ^ 2 := by
  unfold a₂; rw [div_div]; ring_nf
theorem a₁'_scale (c s t θ₀ : ℝ) : a₁' c s t θ₀ = a₁' 1 s t θ₀ / c ^ 2 := by
  unfold a₁'; rw [div_div]; ring_nf
theorem a₂'_scale (c s t θ₀ : ℝ) : a₂' c s t θ₀ = a₂' 1 s t θ₀ / c ^ 2 := by
  unfold a₂'; rw [div_div]; ring_nf

/-- The `f u` constant of decay constants carrying `1/c²` carries `1/c²`. -/
theorem Cf_scale {c : ℝ} (hc : c ≠ 0) (m S' a a' θ₀ : ℝ) :
    Cvs.L2a.ExplicitTreeBoundPlateau.Cf c m S' (a / c ^ 2) (a' / c ^ 2) θ₀ = Cvs.L2a.ExplicitTreeBoundPlateau.Cf 1 m S' a a' θ₀ / c ^ 2 := by
  unfold Cvs.L2a.ExplicitTreeBoundPlateau.Cf; field_simp

/-- The depth ratio is invariant under a common scaling of the four sup norms. -/
theorem grow0_scale {c : ℝ} (hc : c ≠ 0) (κ₁ κ₂ κ₁' κ₂' : ℝ) (k l : ℕ) :
    grow0 (κ₁ / c ^ 2) (κ₂ / c ^ 2) (κ₁' / c ^ 2) (κ₂' / c ^ 2) k l = grow0 κ₁ κ₂ κ₁' κ₂' k l := by
  unfold grow0; field_simp

theorem qb_scale (c m χh α : ℝ) : qb c m (c ^ 2 * χh) α = c ^ 2 * qb 1 m χh α := by
  unfold qb; ring

/-- The majorant `A` at `χ̄ = c²χh` carries `1/c²`. -/
theorem Ac_scale {c : ℝ} (hc : c ≠ 0) (m χh h α : ℝ) :
    Ac c m (c ^ 2 * χh) h α = Ac 1 m χh h α / c ^ 2 := by
  unfold Ac
  have e : c ^ 2 * m ^ 2 - c ^ 2 * χh / α ^ 2 = c ^ 2 * (1 ^ 2 * m ^ 2 - χh / α ^ 2) := by ring
  rw [e]; field_simp

/-- The constant `B` at `χ̄ = c²χh` carries `1/c⁴`. -/
theorem Bconst_scale {c : ℝ} (hc : c ≠ 0) (m χh α : ℝ) :
    Bconst c m (c ^ 2 * χh) α = Bconst 1 m χh α / c ^ 4 := by
  unfold Bconst; rw [qb_scale]; field_simp

/-- The `V`-norm constant with `A/c²`, `B/c⁴` and spread `c²Sh` is at most the one with `A/c₀²`, `B`, `Sh`, for
`c ≥ c₀ > 0`, `A ≥ 0`. -/
theorem Vc_scale_le {c c₀ m ε δ A B Sh : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) (hm : 0 < m) (hε : 0 < ε) (hε2 : ε < 2)
    (hδ : 0 < δ) (hA : 0 ≤ A) :
    Vc m ε δ (A / c ^ 2) (B / c ^ 4) (c ^ 2 * Sh) ≤ Vc m ε δ (A / c₀ ^ 2) B Sh := by
  unfold Vc
  have hc0 : 0 < c := by linarith
  have hε' : 0 < 1 - ε / 2 := by linarith
  have e : B / c ^ 4 * m ^ 3 * (c ^ 2 * Sh) ^ 2 / (2 * δ) = B * m ^ 3 * Sh ^ 2 / (2 * δ) := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hε'.le
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ hm.le
  have hc2 : c₀ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hc₀.le hc 2
  have : A / c ^ 2 ≤ A / c₀ ^ 2 := div_le_div_of_nonneg_left hA (by positivity) hc2
  have : A / c ^ 2 / (2 * ε) ≤ A / c₀ ^ 2 / (2 * ε) := div_le_div_of_nonneg_right this (by positivity)
  linarith

/-- The level cost at `μ_i = c μ̂_i` with `f u` constants `C/c²` is the level cost at `μ̂` over `c`. -/
theorem Ecost_scale {c : ℝ} (hc : c ≠ 0) (m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ : ℝ) (k l : ℕ) :
    Ecost m₁ m₂ (c * μ₁) (c * μ₂) S' κ₁ κ₂ κ₁' κ₂' (C₁ / c ^ 2) (C₂ / c ^ 2) V₁ V₂ k l
      = Ecost m₁ m₂ μ₁ μ₂ S' κ₁ κ₂ κ₁' κ₂' C₁ C₂ V₁ V₂ k l / c := by
  unfold Ecost; field_simp

/-- The boundary constant at `b` with rung sums `Q_ψ = c q₁`, `Q_u = c³ q₂` is `c`-free. -/
theorem Bd_scale {c : ℝ} (hc : 0 < c) (m b q₁ q₂ : ℝ) :
    Bd c m b (c * q₁) (c ^ 3 * q₂) = Bd 1 m b q₁ q₂ := by
  unfold Bd
  rw [κ₁R_scale, κ₂R_scale]
  have e : c * q₁ * (c ^ 3 * q₂) = (c ^ 2) ^ 2 * (q₁ * q₂) := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  field_simp

end Cvs.L2a.TreeConstantScaling
