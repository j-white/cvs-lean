import Mathlib
import Cvs.L2a.BoundaryConstantMassSum
import Cvs.L2a.CutoffDerivativeSup
import Cvs.L2a.CutoffFactorSupNorms
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.HierarchyFactorDecay
import Cvs.L2a.HierarchyFactorDerivativeDecay
import Cvs.L2a.HierarchyModePairNode
import Cvs.L2a.TreeBoundFirstPairBoundary
import Cvs.L2a.TreeConstantSupBounds
import Cvs.L2a.TreeStepFirstPair
import Cvs.L2a.TreeStepModePair
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.SineSquaredRamp

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The explicit tree bound of a pair `(1, k)` under the ramp, with the boundary at `b`

For `2 ≤ m` the node of the empty path on `[4/3, b]` with the weight `ramp (4/3) h_η` obeys `|node| ≤ N₀ · T_f(N)`
with `T_f(N) = Σ_{j<N} ρ^j (E(j) + B_d) + ρ^N (1 + 1/m)/2`, `B_d = √(Q_ψ Q_u)(κ₁ᴿm² + κ₂ᴿ/m)` the boundary constant
at `b` (Cvs.L2a.BoundaryConstantMassSum, Cvs.L2a.CutoffDerivativeSup), the `f u` constants from the decay of the factors (Cvs.L2a.ExplicitTreeBoundPlateau) and every other constant explicit
(Cvs.L2a.TreeConstantSupBounds, Cvs.L2a.CutoffFactorSupNorms, Cvs.L2a.CutoffDerivativeSup): the project bound with the boundary (Cvs.L2a.TreeBoundFirstPairBoundary) instantiated.
-/

namespace Cvs.L2a.ExplicitTreeBoundRamp

open Real Set Finset Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungChiHierarchy Cvs.Upstream.SineSquaredRamp Cvs.L2a.TreeStepModePair Cvs.L2a.TreeStepFirstPair Cvs.L2a.TreeBoundFirstPairBoundary Cvs.L2a.TreeConstantSupBounds Cvs.L2a.BoundaryConstantMassSum Cvs.L2a.CutoffFactorSupNorms Cvs.L2a.CutoffDerivativeSup Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.HierarchyFactorDecay Cvs.L2a.HierarchyFactorDerivativeDecay

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The value bounds of the factors of `(1, m)` at `b`. -/
noncomputable def κ₁R (c t b : ℝ) : ℝ := (1 * b ^ 2 - 1) / (c ^ 2 * b ^ 2 * (t - 1) * (1 * t * b ^ 2 - t - 1))
noncomputable def κ₂R (c t b : ℝ) : ℝ := (t * b ^ 2 - 1) / (c ^ 2 * b ^ 2 * (t - 1) * (1 * t * b ^ 2 - t - 1))

/-- The boundary constant at `b` in units of `N₀`. -/
noncomputable def Bd (c m b Qψ Qu : ℝ) : ℝ := √(Qψ * Qu) * (κ₁R c (m ^ 2) b * m ^ 2 + κ₂R c (m ^ 2) b / m)

/-- The explicit tree bound of a pair `(1, m)` at depth `N`. -/
noncomputable def Tf (c m χb χm Sp h hη b ε δ μ₁ μ₂ Qψ Qu : ℝ) (N : ℕ) : ℝ :=
  (∑ j ∈ range N, (m ^ 2 * κ₁f c (m ^ 2) * χm + 1 * κ₂f c (m ^ 2) * χm) ^ j
      * (Ecost 1 m μ₁ μ₂ (Real.pi / (2 * hη)) (κ₁f c (m ^ 2)) (κ₂f c (m ^ 2)) (κ₁'f c (m ^ 2)) (κ₂'f c (m ^ 2))
          (Cf c m (Real.pi / (2 * hη)) (a₁ c 1 (m ^ 2) (4 / 3)) (a₁' c 1 (m ^ 2) (4 / 3)) (4 / 3))
          (Cf c 1 (Real.pi / (2 * hη)) (a₂ c 1 (m ^ 2) (4 / 3)) (a₂' c 1 (m ^ 2) (4 / 3)) (4 / 3))
          (Vc 1 ε δ (Ac c 1 χb h (4 / 3 - h)) (Bconst c 1 χb (4 / 3 - h)) Sp)
          (Vc m ε δ (Ac c m χb h (4 / 3 - h)) (Bconst c m χb (4 / 3 - h)) Sp) j j
        + Bd c m b Qψ Qu))
    + (m ^ 2 * κ₁f c (m ^ 2) * χm + 1 * κ₂f c (m ^ 2) * χm) ^ N * ((1 / 1 + 1 / m) / 2)

set_option maxHeartbeats 800000 in
/-- **The explicit tree bound of a pair `(1, m)` with its boundary at `b`.** -/
theorem first_pair_bound {c χb χm Sp h hη b ε δ μ₁ μ₂ : ℝ} {a χ Mm Kψ Ku : ι → ℝ} {ψ u : ι → ℝ → ℝ}
    (K : ι → ι → ℝ) {m : ℕ} (hm : 2 ≤ m) (N : ℕ)
    (hc : 0 < c) (hh : 0 < h) (hh' : h ≤ 1 / 4) (hη0 : 0 < hη) (hb : 2 ≤ b) (hθ₀b : 4 / 3 + hη ≤ b)
    (hχb : χb < c ^ 2 * (19 / 20 - h) ^ 2) (hχb0 : 0 ≤ χb)
    (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ χm) (hχm : 0 < χm) (hM : ∀ i, 0 < Mm i) (hS : ∀ i, |χ i - χb| ≤ Sp)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hψ : ∀ i, ∀ ξ, 1 < ξ → HasDerivAt (ψ i) (u i ξ / pP ξ) ξ)
    (hu : ∀ i, ∀ ξ, HasDerivAt (u i) (-(qP c (χ i) ξ * ψ i ξ)) ξ)
    (hψc : ∀ i, Continuous (ψ i)) (huc : ∀ i, Continuous (u i))
    (hcross : ∀ i j, i ≠ j → ∀ t, 1 ≤ t → |∫ ξ in (1 : ℝ)..t, ψ i ξ * ψ j ξ| ≤ K i j / t)
    (hmass : ∀ i, ∀ t, 1 ≤ t → ∫ ξ in (1 : ℝ)..t, ψ i ξ ^ 2 ≤ Mm i)
    (hψK : ∀ i, ∀ ξ, 1 ≤ ξ → |ψ i ξ| ≤ Kψ i / ξ) (huK : ∀ i, ∀ ξ, 1 ≤ ξ → |u i ξ| ≤ Ku i * ξ)
    (hN₀ : 0 < ∑ i, a i ^ 2 * Mm i) :
    |nodeFirst c (m : ℝ) (4 / 3) b (ramp (4 / 3) hη) a χ ψ []|
      ≤ (∑ i, a i ^ 2 * Mm i)
        * Tf c m χb χm Sp h hη b ε δ μ₁ μ₂ (∑ i, Kψ i ^ 2 / Mm i) (∑ i, Ku i ^ 2 / Mm i) N := by
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have ht : (4:ℝ) ≤ (m:ℝ) ^ 2 := by nlinarith
  have hLb : (4 / 3 : ℝ) ≤ b := by linarith
  have hα : 0 < (4 / 3 : ℝ) - h := by linarith
  have hα₁ : 1 < 1 * ((4 / 3 : ℝ) - h) := by linarith
  have hχb' : χb < c ^ 2 * (4 / 3 - h) ^ 2 := by
    have : (19 / 20 - h : ℝ) ^ 2 ≤ (4 / 3 - h) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have := mul_le_mul_of_nonneg_left this (sq_nonneg c)
    linarith
  have hχb₁ : χb < c ^ 2 * 1 ^ 2 * (4 / 3 - h) ^ 2 := by simpa using hχb'
  -- the ramp as the weight
  have hσ : ∀ θ ∈ Icc (4 / 3 : ℝ) b, HasDerivAt (ramp (4 / 3) hη) (ramp' (4 / 3) hη θ) θ :=
    fun θ _ => hasDerivAt_ramp hη0 θ
  have hσ'c : ContinuousOn (ramp' (4 / 3) hη) (Icc (4 / 3 : ℝ) b) := (continuous_ramp' hη0).continuousOn
  have hσL : ramp (4 / 3) hη (4 / 3) = 0 := ramp_of_le le_rfl
  have hσ1 : ∀ θ ∈ Icc (4 / 3 : ℝ) b, |ramp (4 / 3) hη θ| ≤ 1 := fun θ _ => by
    rw [abs_of_nonneg (ramp_nonneg _ _ _)]; exact ramp_le_one _ _ _
  have hσ'b : ∀ θ ∈ Icc (4 / 3 : ℝ) b, |ramp' (4 / 3) hη θ| ≤ Real.pi / (2 * hη) := fun θ _ => abs_ramp'_le hη0 θ
  have hS' : 0 < Real.pi / (2 * hη) := by positivity
  -- the factors (Cvs.L2a.CutoffFactorSupNorms, Cvs.L2a.CutoffDerivativeSup)
  have hfac : ∀ θ ∈ Icc (4 / 3 : ℝ) b,
      |Cvs.L2a.HierarchyModePairNode.g₁ c 1 ((m:ℝ) ^ 2) θ| ≤ κ₁f c ((m:ℝ) ^ 2) ∧
      |Cvs.L2a.HierarchyModePairNode.g₂ c 1 ((m:ℝ) ^ 2) θ| ≤ κ₂f c ((m:ℝ) ^ 2) ∧
      |Cvs.L2a.HierarchyModePairNode.g₁' c 1 ((m:ℝ) ^ 2) θ| ≤ κ₁'f c ((m:ℝ) ^ 2) ∧
      |Cvs.L2a.HierarchyModePairNode.g₂' c 1 ((m:ℝ) ^ 2) θ| ≤ κ₂'f c ((m:ℝ) ^ 2) := fun θ hθ => factors_first hc ht hθ.1
  obtain ⟨hgR₁, hgR₂⟩ := factors_first_at hc ht hb
  obtain ⟨c1, c2, hD, -, -⟩ := first_conditions ht
  have hts : (0:ℝ) < (m:ℝ) ^ 2 - 1 := by linarith
  have hden : 0 < c ^ 2 * (16 / 9) * ((m:ℝ) ^ 2 - 1) * (1 * (m:ℝ) ^ 2 * (16 / 9) - (m:ℝ) ^ 2 - 1) :=
    mul_pos (mul_pos (mul_pos (by positivity) (by norm_num)) hts) (by linarith)
  have hκ₁ : 0 < κ₁f c ((m:ℝ) ^ 2) := by unfold κ₁f; exact div_pos (by norm_num) hden
  have hκ₂ : 0 < κ₂f c ((m:ℝ) ^ 2) := by unfold κ₂f; exact div_pos (by linarith) hden
  have hCd : 0 < 1 * (m:ℝ) ^ 2 - ((m:ℝ) ^ 2 + 1) / (4 / 3 : ℝ) ^ 2 := by
    rw [sub_pos, div_lt_iff₀ (by norm_num)]; norm_num; linarith
  have hden' : 0 < c ^ 2 * ((m:ℝ) ^ 2 - 1) * (4 / 3 : ℝ) ^ 3 * (1 * (m:ℝ) ^ 2 - ((m:ℝ) ^ 2 + 1) / (4 / 3 : ℝ) ^ 2) ^ 2 :=
    mul_pos (mul_pos (mul_pos (by positivity) hts) (by norm_num)) (pow_pos hCd 2)
  have hκ₁' : 0 ≤ κ₁'f c ((m:ℝ) ^ 2) := by unfold κ₁'f; exact div_nonneg (by positivity) hden'.le
  have hκ₂' : 0 ≤ κ₂'f c ((m:ℝ) ^ 2) := by unfold κ₂'f; exact div_nonneg (by positivity) hden'.le
  have hκ₁R : 0 ≤ κ₁R c ((m:ℝ) ^ 2) b := (abs_nonneg _).trans hgR₁
  have hκ₂R : 0 ≤ κ₂R c ((m:ℝ) ^ 2) b := (abs_nonneg _).trans hgR₂
  -- the `V`-norm constants (Cvs.L2a.TreeConstantSupBounds)
  have hqα : ∀ m' : ℝ, 1 ≤ m' → 0 < qb c m' χb (4 / 3 - h) := fun m' hm' => qb_pos_of hm' hα hχb'
  have hA : ∀ m' : ℝ, 1 ≤ m' → ∀ θ ∈ Icc (4 / 3 - h) (b + h),
      2 * (m' ^ 2 * θ ^ 2 - 1) * ((Real.pi / h) ^ 2 / (c ^ 2 * m' ^ 4 * θ ^ 2 - m' ^ 2 * χb)
        + (2 * c ^ 2 * m' ^ 4 * θ) ^ 2 / (c ^ 2 * m' ^ 4 * θ ^ 2 - m' ^ 2 * χb) ^ 3)
      ≤ Ac c m' χb h (4 / 3 - h) := fun m' hm' θ hθ => by
    have hχbm : χb < c ^ 2 * m' ^ 2 * (4 / 3 - h) ^ 2 := by
      have h1 : (1:ℝ) ≤ m' ^ 2 := one_le_pow₀ hm'
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ c ^ 2 * (4 / 3 - h) ^ 2)
      nlinarith
    exact W2_le_uniform hh hα (by linarith) hχb0 hχbm hθ.1
  have hB : ∀ m' : ℝ, 1 ≤ m' → ∀ θ ∈ Icc (4 / 3 - h) (b + h),
      1 / (c ^ 2 * m' ^ 4 * θ ^ 2 - m' ^ 2 * χb) ^ 2 ≤ Bconst c m' χb (4 / 3 - h) :=
    fun m' hm' θ hθ => qb_inv_sq_le hα (hqα m' hm') hθ
  have hqL : ∀ m' : ℝ, 1 ≤ m' → 0 ≤ qb c m' χb (4 / 3) :=
    fun m' hm' => (hqα m' hm').le.trans (qb_mono hα.le (by linarith))
  -- the `f u` constants (Cvs.L2a.ExplicitTreeBoundPlateau)
  have hθ₀ : (0:ℝ) < 4 / 3 := by norm_num
  have hD' : (m:ℝ) ^ 2 + 1 < 1 * (m:ℝ) ^ 2 * (4 / 3 : ℝ) ^ 2 := by
    rw [show (4 / 3 : ℝ) ^ 2 = 16 / 9 by norm_num]; exact hD
  have hts' : (1:ℝ) < (m:ℝ) ^ 2 := by linarith
  have hCd' := Cd_pos hθ₀ hD'
  have hdenA : 0 ≤ c ^ 2 * ((m:ℝ) ^ 2 - 1) * Cd 1 ((m:ℝ) ^ 2) (4 / 3) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hts.le) hCd'.le
  have hdenA' : 0 ≤ c ^ 2 * ((m:ℝ) ^ 2 - 1) * Cd 1 ((m:ℝ) ^ 2) (4 / 3) ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hts.le) (sq_nonneg _)
  have ha₁ : 0 ≤ a₁ c 1 ((m:ℝ) ^ 2) (4 / 3) := div_nonneg zero_le_one hdenA
  have ha₂ : 0 ≤ a₂ c 1 ((m:ℝ) ^ 2) (4 / 3) := div_nonneg (by positivity) hdenA
  have ha₁' : 0 ≤ a₁' c 1 ((m:ℝ) ^ 2) (4 / 3) := div_nonneg (by positivity) hdenA'
  have ha₂' : 0 ≤ a₂' c 1 ((m:ℝ) ^ 2) (4 / 3) := div_nonneg (by positivity) hdenA'
  have hq : ∀ m' : ℝ, 1 ≤ m' → ∀ θ ∈ Icc (4 / 3 : ℝ) b, 0 ≤ c ^ 2 * (m' ^ 2) ^ 2 * θ ^ 2 - m' ^ 2 * χb :=
    fun m' hm' θ hθ => by
      have := (hqL m' hm').trans (qb_mono (by norm_num) hθ.1)
      unfold qb at this
      have e : c ^ 2 * (m' ^ 2) ^ 2 * θ ^ 2 - m' ^ 2 * χb = c ^ 2 * m' ^ 4 * θ ^ 2 - m' ^ 2 * χb := by ring
      rw [e]; exact this
  have h1 : ∀ m' : ℝ, 1 ≤ m' → ∀ θ ∈ Icc (4 / 3 : ℝ) b, 1 ≤ m' ^ 2 * θ ^ 2 := fun m' hm' θ hθ => by
    have hθ2 : (16 / 9 : ℝ) ≤ θ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4 / 3) hθ.1 2
      norm_num at this; linarith
    nlinarith [mul_le_mul (by nlinarith : (1:ℝ) ≤ m' ^ 2) hθ2 (by norm_num) (by positivity)]
  have hC₁ : ∀ θ ∈ Icc (4 / 3 : ℝ) b,
      (Real.pi / (2 * hη) * |Cvs.L2a.HierarchyModePairNode.g₁ c 1 ((m:ℝ) ^ 2) θ|
          + |Cvs.L2a.HierarchyModePairNode.g₁' c 1 ((m:ℝ) ^ 2) θ|) ^ 2
        * (((m:ℝ) ^ 2 * θ ^ 2 - 1) * (c ^ 2 * ((m:ℝ) ^ 2) ^ 2 * θ ^ 2 - (m:ℝ) ^ 2 * χb))
      ≤ Cf c m (Real.pi / (2 * hη)) (a₁ c 1 ((m:ℝ) ^ 2) (4 / 3)) (a₁' c 1 ((m:ℝ) ^ 2) (4 / 3)) (4 / 3) :=
    fun θ hθ =>
    fu_const_of hS'.le ha₁ ha₁' hθ₀ hθ.1 (abs_g₁_decay hc one_pos hts' hθ₀ hD' hθ.1)
      (abs_g₁'_decay hc one_pos hts' hθ₀ hD' hθ.1) hχb0 hm0.le (h1 m (by linarith) θ hθ) (hq m (by linarith) θ hθ)
  have hC₂ : ∀ θ ∈ Icc (4 / 3 : ℝ) b,
      (Real.pi / (2 * hη) * |Cvs.L2a.HierarchyModePairNode.g₂ c 1 ((m:ℝ) ^ 2) θ|
          + |Cvs.L2a.HierarchyModePairNode.g₂' c 1 ((m:ℝ) ^ 2) θ|) ^ 2
        * ((1 * θ ^ 2 - 1) * (c ^ 2 * 1 ^ 2 * θ ^ 2 - 1 * χb))
      ≤ Cf c 1 (Real.pi / (2 * hη)) (a₂ c 1 ((m:ℝ) ^ 2) (4 / 3)) (a₂' c 1 ((m:ℝ) ^ 2) (4 / 3)) (4 / 3) :=
    fun θ hθ => by
    have := fu_const_of (m := 1) hS'.le ha₂ ha₂' hθ₀ hθ.1 (abs_g₂_decay hc one_pos hts' hθ₀ hD' hθ.1)
      (abs_g₂'_decay hc one_pos hts' hθ₀ hD' hθ.1) hχb0 zero_le_one (h1 1 le_rfl θ hθ) (hq 1 le_rfl θ hθ)
    simpa using this
  have htree := pair_tree_bound_first_bd (a := a) (χ := χ) (Mm := Mm) (ψ := ψ) (u := u) K hc hmr (le_refl (4 / 3 : ℝ))
    hLb hh hα₁ hχb₁ hχ hχm (fun i => (hM i).le) hS hε hε2 hδ hμ₁ hμ₂ hψ hu hψc huc hcross hmass
    hσ hσ'c hσL hσ1 hσ'b hS' hκ₁ hκ₂ hκ₁' hκ₂'
    (fun θ hθ => (hfac θ hθ).1) (fun θ hθ => (hfac θ hθ).2.1) (fun θ hθ => (hfac θ hθ).2.2.1)
    (fun θ hθ => (hfac θ hθ).2.2.2) hgR₁ hgR₂
    (hA 1 le_rfl) (hB 1 le_rfl) (hA m (by linarith)) (hB m (by linarith)) hC₁ hC₂
    hN₀ (Cf_nonneg _ _ _ _ _ _) (Cf_nonneg _ _ _ _ _ _) N
  -- the boundary constant in units of `N₀` (Cvs.L2a.BoundaryConstantMassSum)
  have hBc := Bc_le_N0 (a := a) (Kψ := Kψ) (Ku := Ku) (Mm := Mm) (κ₁R := κ₁R c ((m:ℝ) ^ 2) b) (κ₂R := κ₂R c ((m:ℝ) ^ 2) b)
    (by linarith : (1:ℝ) ≤ m) (by linarith : (1:ℝ) ≤ b) hκ₁R hκ₂R hM hψK huK
  have hBd : Bc a ψ u (m:ℝ) b (κ₁R c ((m:ℝ) ^ 2) b) (κ₂R c ((m:ℝ) ^ 2) b) / ∑ i, a i ^ 2 * Mm i
      ≤ Bd c m b (∑ i, Kψ i ^ 2 / Mm i) (∑ i, Ku i ^ 2 / Mm i) := by
    rw [div_le_iff₀ hN₀]; unfold Bd
    calc _ ≤ _ := hBc
      _ = _ := by ring
  -- monotonicity of the sum in the boundary term
  have hρ0 : 0 ≤ (m:ℝ) ^ 2 * κ₁f c ((m:ℝ) ^ 2) * χm + 1 * κ₂f c ((m:ℝ) ^ 2) * χm := by positivity
  rw [mul_comm]
  unfold Tf
  refine htree.trans (mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) hN₀.le)
  apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hρ0 j)
  exact add_le_add le_rfl hBd

end Cvs.L2a.ExplicitTreeBoundRamp
