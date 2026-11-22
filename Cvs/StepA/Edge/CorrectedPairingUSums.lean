import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FiniteTopTieTerm
import Cvs.StepA.Edge.OffTopPairingBound
import Cvs.StepA.OneZeroParitySectors
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `U`-sums of the corrected pairing vector off a finite top set

`⟪U_z, U_{z'}⟫ = ¼ Σ cosCoshC(γ ∓ γ', y ± y', log x)`; with `b⊥ = V_σ − Σ_R a_r U_r` and `Σ a_r² ≤ K` this gives
`m_ρ⟪b⊥, U_ρ⟫² ≤ (1 + K)(m_ρ pairUe² + Σ_R m_ρ ueUe²)`, so the `U` sum of `b⊥` is summable and its part off `S`
is `o(x^{2δ})` by the dominated convergence of Cvs.StepA.Edge.OffTopPairingBound; `PerpRates` reduces to the share and Bessel conjuncts.
-/

noncomputable section

open Real MeasureTheory Filter Topology
open scoped InnerProductSpace
open Cvs.StepA.OneZeroParitySectors (ue)
open Cvs.StepA.Edge.FiniteTopGap (FiniteTop mult mult_nonneg)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec ueProf)
open Cvs.StepA.Edge.FiniteTopTieTerm (cosCoshC cosCoshInt pairUe)
open Cvs.StepA.Edge.OffTopPairingBound (OffTopBound)
open Cvs.StepA.Edge.FiniteTopCorrectedClosing (bPerp reps)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.StepA.Edge.CorrectedPairingUSums
open Cvs.ZeroCounting

/-! ### The Gram entries of the `ue` vectors in closed form -/

/-- `ue_z ue_{z'} = ¼ Σ cos((γ ∓ γ')t) cosh((y ± y')t)`, with `z = γ + iy`, `z' = γ' + iy'`. -/
theorem ue_mul_ue (z z' : ℂ) (t : ℝ) :
    ue z t * ue z' t = (1 / 4) * (cos ((z.re - z'.re) * t) * cosh ((z.im + z'.im) * t)
      + cos ((z.re - z'.re) * t) * cosh ((z.im - z'.im) * t)
      + cos ((z.re + z'.re) * t) * cosh ((z.im + z'.im) * t)
      + cos ((z.re + z'.re) * t) * cosh ((z.im - z'.im) * t)) := by
  simp only [ue, add_mul, sub_mul, Real.cos_add, Real.cos_sub, Real.cosh_add, Real.cosh_sub]
  ring

/-- The closed form of `⟪U_z, U_{z'}⟫` at `L`: `¼ Σ cosCoshC(γ ∓ γ', y ± y', L)`. -/
def ueUe (L : ℝ) (z z' : ℂ) : ℝ :=
  (1 / 4) * (cosCoshC (z.re - z'.re) (z.im + z'.im) L + cosCoshC (z.re - z'.re) (z.im - z'.im) L
    + cosCoshC (z.re + z'.re) (z.im + z'.im) L + cosCoshC (z.re + z'.re) (z.im - z'.im) L)

/-- `∫ ue_z ue_{z'}` over the centred window is `ueUe`. -/
theorem integral_ue_mul_ue (L : ℝ) (z z' : ℂ) :
    ∫ t in -(L / 2)..L / 2, ue z t * ue z' t = ueUe L z z' := by
  have hi : ∀ {f : ℝ → ℝ}, Continuous f → IntervalIntegrable f volume (-(L / 2)) (L / 2) :=
    fun hf => hf.intervalIntegrable _ _
  simp_rw [ue_mul_ue]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    intervalIntegral.integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    intervalIntegral.integral_add (hi (by fun_prop)) (hi (by fun_prop))]
  simp only [ueUe, ← Cvs.StepA.Edge.FiniteTopTieTerm.cosCoshInt_eq, cosCoshInt]

/-- **`⟪U_z, U_{z'}⟫` in closed form**: `⟪ueVec z, ueVec z'⟫ = ueUe(log x, z, z')`. -/
theorem inner_ueVec_ueVec {x : ℕ} (hx0 : (0 : ℝ) < x) (z z' : ℂ) :
    ⟪ueVec hx0 z, ueVec hx0 z'⟫_ℝ = ueUe (Real.log x) z z' := by
  rw [Cvs.Route.Visibility.VisibilityClosingStep.inner_ueVec hx0 z' _ (Cvs.Route.Visibility.VisibilityClosingStep.coe_ueVec_ae hx0 z), ← integral_ue_mul_ue]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(Set.countable_singleton (Real.log x / 2)).ae_notMem volume] with t ht hmem
  have ht : t ≠ Real.log x / 2 := ht
  rw [Set.uIoc_of_le (by linarith [Real.log_natCast_nonneg x])] at hmem
  have hm : t + Real.log x / 2 ∈ Set.Ico 0 (Real.log x) :=
    ⟨by linarith [hmem.1], by linarith [lt_of_le_of_ne hmem.2 ht]⟩
  rw [Set.indicator_of_mem hm, ueProf, add_sub_cancel_right]

/-! ### The off-top bounds for the `ue` Gram entries -/

/-- `ueUe(L, z, z')² ≤ M` when `cosCoshC(γ ± γ', y ± y', L)² ≤ M` for all four sign choices. -/
theorem ueUe_sq_le {L M : ℝ} {z z' : ℂ}
    (h : ∀ a b : ℝ, (a = z.re + z'.re ∨ a = z.re - z'.re) → (b = z.im + z'.im ∨ b = z.im - z'.im) →
      cosCoshC a b L ^ 2 ≤ M) : ueUe L z z' ^ 2 ≤ M :=
  Cvs.StepA.Edge.OffTopPairingBound.quarter_sum_sq_le (h _ _ (.inr rfl) (.inl rfl)) (h _ _ (.inr rfl) (.inr rfl))
    (h _ _ (.inl rfl) (.inl rfl)) (h _ _ (.inl rfl) (.inr rfl))

/-- **`U`-Gram entries of a top zero satisfy `OffTopBound`** with `R = 2|γ_r| + 1`, `K = 16`, for `r ∈ S`. -/
theorem offTopBound_ueUe {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ)
    {r : nonTrivialZeroSet} (hr : r ∈ S) :
    OffTopBound S δ (2 * |(r : ℂ).im| + 1) 16
      (fun ρ L => ueUe L (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ) ^ 2) where
  lt := hS.2.2.2
  K_nonneg := by norm_num
  nonneg := fun _ _ => sq_nonneg _
  near := fun ρ L hL => ueUe_sq_le fun a b _ hb =>
    (Cvs.StepA.Edge.OffTopPairingBound.cosCoshC_sq_le_mul a b hL).trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonneg_right (Cvs.StepA.Edge.OffTopPairingBound.abs_im_pm_le (hS.2.2.1 r hr) hb) hL)) (sq_nonneg L))
  far := fun ρ L hL hR => ueUe_sq_le fun a b ha hb => by
    rw [Cvs.ZeroCounting.zPoint_re, Cvs.ZeroCounting.zPoint_re] at ha
    obtain ⟨ha0, hc⟩ := Cvs.StepA.Edge.OffTopPairingBound.far_coef hR ha
    exact (Cvs.StepA.Edge.OffTopPairingBound.cosCoshC_sq_le_div ha0 b hL).trans (mul_le_mul hc
      (exp_le_exp.2 (mul_le_mul_of_nonneg_right (Cvs.StepA.Edge.OffTopPairingBound.abs_im_pm_le (hS.2.2.1 r hr) hb) hL))
      (exp_pos _).le (by positivity))

/-! ### The pairings of `b⊥` -/

/-- `(p − Σ aᵢqᵢ)² ≤ (1 + Σ aᵢ²)(p² + Σ qᵢ²)`. -/
theorem sub_sum_sq_le {ι : Type*} (s : Finset ι) (p : ℝ) (a q : ι → ℝ) :
    (p - ∑ i ∈ s, a i * q i) ^ 2 ≤ (1 + ∑ i ∈ s, a i ^ 2) * (p ^ 2 + ∑ i ∈ s, q i ^ 2) := by
  have hX := Finset.sum_mul_sq_le_sq_mul_sq s a q
  set X := ∑ i ∈ s, a i * q i
  set A := ∑ i ∈ s, a i ^ 2
  set Q := ∑ i ∈ s, q i ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases hA.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul] at hX
    have : X = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hX (sq_nonneg X))
    rw [this, ← h0]; nlinarith
  · have h1 : 0 ≤ A * (A * p ^ 2 + 2 * p * X + Q) := by nlinarith [sq_nonneg (A * p + X)]
    have h2 : 0 ≤ A * p ^ 2 + 2 * p * X + Q := nonneg_of_mul_nonneg_right (by linarith) hpos
    nlinarith

/-- `⟪v − Σ aᵢUᵢ, u⟫ = ⟪v, u⟫ − Σ aᵢ⟪Uᵢ, u⟫` in a real inner product space. -/
theorem inner_sub_sum_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}
    (s : Finset ι) (v : E) (a : ι → ℝ) (U : ι → E) (u : E) :
    ⟪v - ∑ i ∈ s, a i • U i, u⟫_ℝ = ⟪v, u⟫_ℝ - ∑ i ∈ s, a i * ⟪U i, u⟫_ℝ := by
  rw [inner_sub_left, sum_inner]
  simp only [real_inner_smul_left]

/-- **`⟪b⊥, U_ρ⟫` in closed form**: from `V_σ = b⊥ + Σ_R a_r U_r`,
`⟪b⊥, U_ρ⟫ = pairUe(log x, z_σ, z_ρ) − Σ_R a_r ueUe(log x, z_r, z_ρ)`. -/
theorem inner_bPerp_ueVec_eq {x : ℕ} (hx0 : (0 : ℝ) < x) {S : Finset nonTrivialZeroSet}
    {σ : nonTrivialZeroSet} {a : nonTrivialZeroSet → ℝ}
    (hV : Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
      = bPerp hx0 S σ + ∑ r ∈ reps S, a r • ueVec hx0 (Cvs.ZeroCounting.zPoint r)) (ρ : nonTrivialZeroSet) :
    ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ
      = pairUe (Real.log x) (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ)
        - ∑ r ∈ reps S, a r * ueUe (Real.log x) (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ) := by
  rw [eq_sub_of_add_eq hV.symm, inner_sub_sum_smul, Cvs.StepA.Edge.FiniteTopTieTerm.inner_pairVec_ueVec]
  simp only [inner_ueVec_ueVec]

/-- The dominating family at `ρ`: `m_ρ pairUe(L, z_σ, z_ρ)² + Σ_R m_ρ ueUe(L, z_r, z_ρ)²`. -/
def domF (S : Finset nonTrivialZeroSet) (σ ρ : nonTrivialZeroSet) (L : ℝ) : ℝ :=
  mult ρ * pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2
    + ∑ r ∈ reps S, mult ρ * ueUe L (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ) ^ 2

/-- **Pointwise domination**: with `V_σ = b⊥ + Σ_R a_r U_r` and `Σ a_r² ≤ K`,
`m_ρ⟪b⊥, U_ρ⟫² ≤ (1 + K) domF(ρ, log x)`. -/
theorem mul_inner_bPerp_sq_le {x : ℕ} (hx0 : (0 : ℝ) < x) {S : Finset nonTrivialZeroSet}
    {σ : nonTrivialZeroSet} {a : nonTrivialZeroSet → ℝ} {K : ℝ}
    (hV : Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ)
      = bPerp hx0 S σ + ∑ r ∈ reps S, a r • ueVec hx0 (Cvs.ZeroCounting.zPoint r))
    (hK : ∑ r ∈ reps S, a r ^ 2 ≤ K) (ρ : nonTrivialZeroSet) :
    mult ρ * ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ (1 + K) * domF S σ ρ (Real.log x) := by
  rw [inner_bPerp_ueVec_eq hx0 hV ρ, domF, ← Finset.mul_sum, ← mul_add]
  have h := sub_sum_sq_le (reps S) (pairUe (Real.log x) (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ))
    a (fun r => ueUe (Real.log x) (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ))
  have hP : 0 ≤ pairUe (Real.log x) (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2
      + ∑ r ∈ reps S, ueUe (Real.log x) (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ) ^ 2 :=
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hK1 : 1 + ∑ r ∈ reps S, a r ^ 2 ≤ 1 + K := by linarith
  have h2 := h.trans (mul_le_mul_of_nonneg_right hK1 hP)
  have h3 := mul_le_mul_of_nonneg_left h2 (mult_nonneg ρ)
  refine h3.trans_eq ?_
  ring

/-- **The dominating family is summable off `S`** at every `L ≥ 0`. -/
theorem summable_domF {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ)
    {σ : nonTrivialZeroSet} (hσ : σ ∈ S) {L : ℝ} (hL : 0 ≤ L) :
    Summable fun ρ : {ρ // ρ ∉ S} => domF S σ ρ L :=
  (Cvs.StepA.Edge.OffTopPairingBound.summable_offTop (Cvs.StepA.Edge.OffTopPairingBound.offTopBound_pairUe hS hσ) hL).add
    (summable_sum fun _ hr => Cvs.StepA.Edge.OffTopPairingBound.summable_offTop (offTopBound_ueUe hS (Cvs.StepA.Edge.FiniteTopCorrectedClosing.reps_subset S hr)) hL)

/-- **Tannery for the dominating family**: `(Σ_{ρ ∉ S} domF(ρ, L))/e^{2δL} → 0`. -/
theorem tendsto_tsum_domF {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ)
    {σ : nonTrivialZeroSet} (hσ : σ ∈ S) :
    Tendsto (fun L => (∑' ρ : {ρ // ρ ∉ S}, domF S σ ρ L) / exp (2 * δ * L)) atTop (𝓝 0) := by
  have h0 := Cvs.StepA.Edge.OffTopPairingBound.tendsto_tsum_div_exp (Cvs.StepA.Edge.OffTopPairingBound.offTopBound_pairUe hS hσ)
  have hr : ∀ r ∈ reps S, Tendsto (fun L => (∑' ρ : {ρ // ρ ∉ S}, mult ρ
      * ueUe L (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ) ^ 2) / exp (2 * δ * L)) atTop (𝓝 0) :=
    fun r hr => Cvs.StepA.Edge.OffTopPairingBound.tendsto_tsum_div_exp
      (f := fun ρ L => ueUe L (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ) ^ 2)
      (offTopBound_ueUe hS (Cvs.StepA.Edge.FiniteTopCorrectedClosing.reps_subset S hr))
  have h := h0.add (tendsto_finsetSum (reps S) hr)
  simp only [Finset.sum_const_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with L hL
  rw [← Finset.sum_div, ← add_div]
  refine congrArg (· / exp (2 * δ * L)) ?_
  simp only [domF]
  rw [(Cvs.StepA.Edge.OffTopPairingBound.summable_offTop (Cvs.StepA.Edge.OffTopPairingBound.offTopBound_pairUe hS hσ) hL).tsum_add
      (summable_sum fun r hr => Cvs.StepA.Edge.OffTopPairingBound.summable_offTop (offTopBound_ueUe hS (Cvs.StepA.Edge.FiniteTopCorrectedClosing.reps_subset S hr)) hL),
    Summable.tsum_finsetSum fun r hr => Cvs.StepA.Edge.OffTopPairingBound.summable_offTop (offTopBound_ueUe hS (Cvs.StepA.Edge.FiniteTopCorrectedClosing.reps_subset S hr)) hL]

/-! ### Summability and the rate off `S` for `b⊥` -/

/-- **The `U` sum of `b⊥` is summable** at every `x > 0`, for `σ` in a finite top set. -/
theorem summable_bPerp {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ)
    {σ : nonTrivialZeroSet} (hσ : σ ∈ S) {x : ℕ} (hx0 : (0 : ℝ) < x) :
    Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
      * ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 := by
  obtain ⟨a, hV⟩ := Cvs.StepA.Edge.FiniteTopCorrectedClosing.exists_coeff hx0 hS.2.2.1 σ
  refine (Finset.summable_compl_iff (s := S)).1 ?_
  exact Summable.of_nonneg_of_le (fun _ => mul_nonneg (mult_nonneg _) (sq_nonneg _))
    (fun ρ => mul_inner_bPerp_sq_le hx0 hV le_rfl ρ)
    ((summable_domF hS hσ (Real.log_natCast_nonneg x)).mul_left _)

/-- `x^{2δ} = e^{2δ log x}` for `x > 0`. -/
theorem rpow_two_mul_eq {x : ℕ} (hx0 : (0 : ℝ) < x) (δ : ℝ) :
    (x : ℝ) ^ (2 * δ) = exp (2 * δ * Real.log x) := by
  rw [Real.rpow_def_of_pos hx0, mul_comm]

/-- **F8 off `S` for `b⊥`**: for `σ` in a finite top set and every `ε > 0`, at all large `x`,
`Σ_{ρ ∉ S} m_ρ⟪b⊥, U_ρ⟫² ≤ ε x^{2δ}`. -/
theorem eventually_offTop_bPerp_le {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ)
    {σ : nonTrivialZeroSet} (hσ : σ ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      ∑' ρ : ↥((S : Set nonTrivialZeroSet)ᶜ), (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ)
          * ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ ε * (x : ℝ) ^ (2 * δ) := by
  obtain ⟨β, -, K, hK0, hev⟩ := Cvs.StepA.Edge.FiniteTopCorrectedClosing.eventually_bPerp_bounds hS hσ
  have hK1 : 0 < 1 + K := by linarith
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (tendsto_tsum_domF hS hσ).comp hlog
  filter_upwards [hev, h.eventually (gt_mem_nhds (div_pos hε hK1))] with x hx hlt hx0
  obtain ⟨-, a, hV, hKa⟩ := hx hx0
  simp only [Function.comp_apply] at hlt
  rw [div_lt_iff₀ (exp_pos _)] at hlt
  rw [rpow_two_mul_eq hx0]
  have hsum := summable_domF hS hσ (Real.log_natCast_nonneg x)
  calc ∑' ρ : ↥((S : Set nonTrivialZeroSet)ᶜ), (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ)
          * ⟪bPerp hx0 S σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ ∑' ρ : {ρ // ρ ∉ S}, (1 + K) * domF S σ ρ (Real.log x) :=
          Summable.tsum_le_tsum (fun ρ => mul_inner_bPerp_sq_le hx0 hV hKa ρ)
            (Summable.of_nonneg_of_le (fun _ => mul_nonneg (mult_nonneg _) (sq_nonneg _))
              (fun ρ => mul_inner_bPerp_sq_le hx0 hV hKa ρ) (hsum.mul_left _)) (hsum.mul_left _)
      _ = (1 + K) * ∑' ρ : {ρ // ρ ∉ S}, domF S σ ρ (Real.log x) := tsum_mul_left
      _ ≤ (1 + K) * (ε / (1 + K) * exp (2 * δ * Real.log x)) := mul_le_mul_of_nonneg_left hlt.le hK1.le
      _ = ε * exp (2 * δ * Real.log x) := by field_simp

/-! ### The reduced closing theorem -/

/-- The share and Bessel conjuncts of `PerpRates S δ σ`: a share `s₀ > 0` of `b⊥` off `R₁`, and the summable
Bessel sum `Σ_ρ m_ρ⟪P_{R₁}b⊥, U_ρ⟫² = o(x^{2δ})`. -/
def ShareBessel (S : Finset nonTrivialZeroSet) (δ : ℝ) (σ : nonTrivialZeroSet) : Prop :=
  (∃ s₀ > 0, ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      ‖(R1 x).starProjection (bPerp hx0 S σ)‖ ^ 2 ≤ (1 - s₀) * ‖bPerp hx0 S σ‖ ^ 2)
  ∧ (∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      Summable fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪(R1 x).starProjection (bPerp hx0 S σ), ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
  ∧ ∀ ε > 0, ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      ∑' ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
          * ⟪(R1 x).starProjection (bPerp hx0 S σ), ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ ε * (x : ℝ) ^ (2 * δ)

/-- **`PerpRates` from the share and Bessel conjuncts** for `σ` in a finite top set. -/
theorem perpRates_of_shareBessel {S : Finset nonTrivialZeroSet} {δ : ℝ} (hS : FiniteTop S δ)
    {σ : nonTrivialZeroSet} (hσ : σ ∈ S) (h : ShareBessel S δ σ) : Cvs.StepA.Edge.FiniteTopCorrectedClosing.PerpRates S δ σ := by
  obtain ⟨hsh, hsum, hB⟩ := h
  refine ⟨hsh, hsum.mono fun x hx hx0 => ⟨hx hx0, summable_bPerp hS hσ hx0⟩, fun ε hε => ?_⟩
  filter_upwards [hB ε hε, eventually_offTop_bPerp_le hS hσ hε] with x h1 h2 hx0
  exact ⟨h1 hx0, h2 hx0⟩

end Cvs.StepA.Edge.CorrectedPairingUSums

end
