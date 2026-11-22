import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.RecentredTransform
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.CriticalStripOffAxes
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Route.JointGapStripLimit
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# RH from the angle between the even ground state and Connes' vector

The squared sine `1 − (g⬝v)²` of the angle between the even ground state `g` and Connes' vector `v`,
at most `ε(x)` for arbitrarily large `x` with `log x · x^{a/2} · √ε(x) → 0` for every `a < 1/2`,
gives RH. The joint gap at `K = √x log x` bounds this squared sine by `2/K`.
-/

noncomputable section

open Filter Topology Matrix

namespace Cvs.Route.GroundConnesAngle
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx negI)
open Cvs.Limit.SpineWithoutSimplicity (ground ground_spec)

/-- The squared distance from `σ • g` to `v`, `σ = ±1`, for unit `g` and `v`. -/
theorem dotProduct_smul_sub_self {N : ℕ} {g v : Idx N → ℝ} (hg : g ⬝ᵥ g = 1) (hv : v ⬝ᵥ v = 1)
    (σ : ℝ) : (σ • g - v) ⬝ᵥ (σ • g - v) = σ ^ 2 + 1 - 2 * σ * (g ⬝ᵥ v) := by
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm v g, hg, hv]
  ring

/-- **A sign of a unit vector lies within twice the squared sine of another**:
`‖σg − v‖² ≤ 2(1 − (g⬝v)²)` for `σ` the sign of `g⬝v`. -/
theorem exists_sign_sq_le_two_sinSq {N : ℕ} {g v : Idx N → ℝ} (hg : g ⬝ᵥ g = 1)
    (hv : v ⬝ᵥ v = 1) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (σ • g - v) ⬝ᵥ (σ • g - v) ≤ 2 * (1 - (g ⬝ᵥ v) ^ 2) := by
  have h1 := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' ((1 : ℝ) • g - v)
  have h2 := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' ((-1 : ℝ) • g - v)
  rw [dotProduct_smul_sub_self hg hv] at h1 h2
  by_cases hc : 0 ≤ g ⬝ᵥ v
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [dotProduct_smul_sub_self hg hv]
    nlinarith
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [dotProduct_smul_sub_self hg hv]
    nlinarith

/-- **The squared sine is at most the squared distance from either sign.** -/
theorem one_sub_sq_le_of_sign {N : ℕ} {g v : Idx N → ℝ} (hg : g ⬝ᵥ g = 1) (hv : v ⬝ᵥ v = 1)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : 1 - (g ⬝ᵥ v) ^ 2 ≤ (σ • g - v) ⬝ᵥ (σ • g - v) := by
  rw [dotProduct_smul_sub_self hg hv]
  rcases hσ with rfl | rfl
  · nlinarith [sq_nonneg (1 - g ⬝ᵥ v)]
  · nlinarith [sq_nonneg (1 + g ⬝ᵥ v)]

/-- **The angle bound**: at scale `L` the even ground state and `v` have squared sine `1 − (g⬝v)²`
at most `ε`. -/
def SinSqClose (P R : ℕ) (L : ℝ) (N : ℕ) (ε : ℝ) (v : Idx N → ℝ) : Prop :=
  ∃ hL : 0 < L, 1 - (ground P R L hL N ⬝ᵥ v) ^ 2 ≤ ε

/-- **The joint gap gives the angle bound**: `Cvs.Route.GroundRouteJointGap.JointGap` at `K` against unit even `v` gives
`SinSqClose` at `2/K`. -/
theorem sinSqClose_of_jointGap {P R N : ℕ} {L K : ℝ} (hK : 0 < K) {v : Idx N → ℝ}
    (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hgap : Cvs.Route.GroundRouteJointGap.JointGap P R L N K v) : SinSqClose P R L N (2 / K) v := by
  have hL : 0 < L := hgap.1
  obtain ⟨σ, hσ, hd⟩ := Cvs.Route.GroundRouteJointGap.exists_sign_close_of_jointGap hL hK hve hv1 hgap
  exact ⟨hL, (one_sub_sq_le_of_sign (ground_spec P R hL N).2.1 hv1 hσ).trans hd⟩

/-- **When the even bottom is simple the squared sine does not depend on the chosen ground
state**: it is the squared sine against `Cvs.Finite.EvenMinimisers.evMin`. -/
theorem sq_ground_dotProduct_eq_evMin {P R : ℕ} {L : ℝ} (hL : 0 < L) {N : ℕ}
    (h : Cvs.Finite.EvenMinimisers.EvenSimple P R L hL N) (v : Idx N → ℝ) :
    (ground P R L hL N ⬝ᵥ v) ^ 2 = (Cvs.Finite.EvenMinimisers.evMin P R L hL N ⬝ᵥ v) ^ 2 := by
  rcases Cvs.Limit.SpineWithoutSimplicity.ground_eq_of_evenSimple hL h with h' | h' <;> rw [h']
  rw [neg_dotProduct, neg_sq]

/-- **With a simple even bottom the angle bound is choice-free**: it is the bound against
`Cvs.Finite.EvenMinimisers.evMin`. -/
theorem sinSqClose_iff_evMin {P R : ℕ} {L : ℝ} (hL : 0 < L) {N : ℕ}
    (h : Cvs.Finite.EvenMinimisers.EvenSimple P R L hL N) (ε : ℝ) (v : Idx N → ℝ) :
    SinSqClose P R L N ε v ↔ 1 - (Cvs.Finite.EvenMinimisers.evMin P R L hL N ⬝ᵥ v) ^ 2 ≤ ε := by
  rw [← sq_ground_dotProduct_eq_evMin hL h v]
  exact ⟨fun ⟨_, h'⟩ => h', fun h' => ⟨hL, h'⟩⟩

/-- **RH from the angle at infinitely many scales.** Strip-approximable `v`, and
`1 − (g⬝v x)² ≤ ε x` against the even ground state `g` for arbitrarily large `x`, with
`log x · x^{a/2} · √(ε x) → 0` for every `a < 1/2`, give RH. -/
theorem riemannHypothesis_of_frequently_sinSq (P R N : ℝ → ℕ) (v : ∀ x, Idx (N x) → ℝ)
    (hA : Cvs.Route.GroundRouteJointGap.StripApproximable N v) (ε : ℝ → ℝ)
    (hbudget : ∀ a : ℝ, a < 1 / 2 →
      Tendsto (fun x => Real.log x * x ^ (a / 2) * √(ε x)) atTop (𝓝 0))
    (hclose : ∃ᶠ x in atTop, SinSqClose (P x) (R x) (Real.log x) (N x) (ε x) (v x)) :
    RiemannHypothesis := by
  obtain ⟨hve, hv1, s, S, hs, hS, hconvA⟩ := hA
  have hex : ∀ n : ℕ, ∃ x : ℝ, max (n : ℝ) 2 ≤ x ∧ SinSqClose (P x) (R x) (Real.log x) (N x) (ε x) (v x) :=
    fun n => frequently_atTop.mp hclose (max n 2)
  choose y hy hgy using hex
  have hy1 : ∀ n, 1 < y n := fun n => by linarith [le_max_right (n : ℝ) 2, hy n]
  have hyt : Tendsto y atTop atTop :=
    tendsto_atTop_mono (fun n => le_trans (le_max_left _ _) (hy n)) tendsto_natCast_atTop_atTop
  have hL : ∀ n, 0 < Real.log (y n) := fun n => Real.log_pos (hy1 n)
  have hconv : TendstoLocallyUniformlyOn
      (fun n z => (s (y n) : ℂ) * Cvs.Route.GroundRouteJointGap.ctransform (Real.log (y n)) (N (y n))
        (v (y n)) z)
      Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop Cvs.Limit.CriticalStripOffAxes.criticalOffAxes := by
    intro u hu z hz
    obtain ⟨t, ht, hev⟩ := hconvA u hu z hz
    exact ⟨t, ht, hyt.eventually hev⟩
  have hclose' : ∀ n, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (σ • ground (P (y n)) (R (y n)) (Real.log (y n)) (hL n) (N (y n)) - v (y n))
        ⬝ᵥ (σ • ground (P (y n)) (R (y n)) (Real.log (y n)) (hL n) (N (y n)) - v (y n))
        ≤ 2 * ε (y n) := by
    intro n
    obtain ⟨hLn, hn⟩ := hgy n
    obtain ⟨σ, hσ, hd⟩ := exists_sign_sq_le_two_sinSq (ground_spec _ _ hLn _).2.1 (hv1 (y n))
    exact ⟨σ, hσ, hd.trans (by linarith)⟩
  have hbud : ∀ a : ℝ, a < 1 / 2 → Tendsto (fun n => Real.log (y n) * Real.exp (a * Real.log (y n) / 2)
      * √(2 * ε (y n))) atTop (𝓝 0) := by
    intro a ha
    have hb := ((hbudget a ha).comp hyt).const_mul √2
    rw [mul_zero] at hb
    refine hb.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by linarith [hy1 n] : (0 : ℝ) < y n),
      show Real.log (y n) * (a / 2) = a * Real.log (y n) / 2 by ring]
    ring
  obtain ⟨c, hc, hcg⟩ := Cvs.Route.GroundRouteJointGap.tendsto_ground_of_close_strip hL
    (fun n => P (y n)) (fun n => R (y n)) (fun n => N (y n)) (fun n => v (y n))
    (fun n => hve (y n)) (fun n => s (y n)) (fun n => hs (y n)) (fun n => hS (y n))
    (fun n => 2 * ε (y n)) hclose' hbud hconv
  exact Cvs.Limit.CriticalStripOffAxes.riemannHypothesis_of_ground_centred_strip hL _ _ _ c hc hcg

/-- **RH from the angle at Connes' vectors**: a truncation eventually at least `⌈x^{1/4}⌉` and
`1 − (g⬝connesVec)² ≤ ε x` for arbitrarily large `x`, with the budget, give RH. -/
theorem riemannHypothesis_of_frequently_sinSq_connes (P R N : ℝ → ℕ)
    (hN : ∀ᶠ x in atTop, Cvs.Route.JointGapAtConnesVectors.connesThreshold x ≤ N x) (ε : ℝ → ℝ)
    (hbudget : ∀ a : ℝ, a < 1 / 2 →
      Tendsto (fun x => Real.log x * x ^ (a / 2) * √(ε x)) atTop (𝓝 0))
    (hclose : ∃ᶠ x in atTop, SinSqClose (P x) (R x) (Real.log x) (N x) (ε x)
      (Cvs.Approximant.ConnesVectorRealScale.connesVec N x)) :
    RiemannHypothesis :=
  riemannHypothesis_of_frequently_sinSq P R N (Cvs.Approximant.ConnesVectorRealScale.connesVec N)
    (Cvs.Route.JointGapAtConnesVectors.stripApproximable_connesVec_of_threshold_le N hN) ε hbudget hclose

/-- **The budget at `ε = 2/(√x log x)`**: `log x · x^{a/2} · √(2/(√x log x)) → 0` for `a < 1/2`. -/
theorem tendsto_budget_two_div {a : ℝ} (ha : a < 1 / 2) :
    Tendsto (fun x : ℝ => Real.log x * x ^ (a / 2) * √(2 / (√x * Real.log x))) atTop (𝓝 0) := by
  refine (Cvs.Route.JointGapStripLimit.tendsto_scale Real.tendsto_log_atTop ha).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have h1 : √x * Real.log x = Real.log x * Real.exp (Real.log x / 2) := by
    rw [Real.exp_half, Real.exp_log hx, mul_comm]
  have h2 : x ^ (a / 2) = Real.exp (a * Real.log x / 2) := by
    rw [Real.rpow_def_of_pos hx]; ring_nf
  rw [h1, h2]

/-- **RH from the angle at Connes' vectors, at the joint gap's scale**: a truncation eventually at
least `⌈x^{1/4}⌉` with `1 − (g⬝connesVec)² ≤ 2/(√x log x)` for arbitrarily large `x` gives RH. -/
theorem riemannHypothesis_of_frequently_sinSq_connes_two_div (P R : ℝ → ℕ)
    (hclose : ∃ N : ℝ → ℕ, (∀ᶠ x in atTop, Cvs.Route.JointGapAtConnesVectors.connesThreshold x ≤ N x) ∧
      ∃ᶠ x in atTop, SinSqClose (P x) (R x) (Real.log x) (N x) (2 / (√x * Real.log x))
        (Cvs.Approximant.ConnesVectorRealScale.connesVec N x)) :
    RiemannHypothesis := by
  obtain ⟨N, hN, h⟩ := hclose
  exact riemannHypothesis_of_frequently_sinSq_connes P R N hN (fun x => 2 / (√x * Real.log x))
    (fun _ ha => tendsto_budget_two_div ha) h

/-- **`Cvs.Route.JointGapAtConnesVectors`'s hypothesis gives the angle bound at infinitely many scales**: the joint gap at
`K = √x log x` frequently gives `SinSqClose` at `2/(√x log x)` frequently. -/
theorem frequently_sinSqClose_of_frequently_jointGap (P R N : ℝ → ℕ) (v : ∀ x, Idx (N x) → ℝ)
    (hve : ∀ x i, v x (negI (N x) i) = v x i) (hv1 : ∀ x, v x ⬝ᵥ v x = 1)
    (hgap : ∃ᶠ x in atTop, Cvs.Route.GroundRouteJointGap.JointGap (P x) (R x) (Real.log x) (N x)
      (√x * Real.log x) (v x)) :
    ∃ᶠ x in atTop, SinSqClose (P x) (R x) (Real.log x) (N x) (2 / (√x * Real.log x)) (v x) := by
  refine (hgap.and_eventually (eventually_gt_atTop 1)).mono fun x hx => ?_
  exact sinSqClose_of_jointGap (mul_pos (Real.sqrt_pos.mpr (by linarith [hx.2]))
    (Real.log_pos hx.2)) (hve x) (hv1 x) hx.1

end Cvs.Route.GroundConnesAngle
