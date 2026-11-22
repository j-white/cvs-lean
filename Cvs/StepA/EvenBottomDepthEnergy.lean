import Mathlib
import Cvs.Finite.EvenMinimisers
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.SymmetricModeSet
import Cvs.Prolate.RungEnvelopeSchurTest
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.TopSetCriterion
import Cvs.StepA.EvenBottomNearZeroFrame
import Cvs.StepA.ModePolynomialFarEnvelope
import Cvs.StepA.OneZeroParitySectors
import Cvs.StepA.TopQuadruple
import Cvs.WeilForm.OddPoleTermBound
import Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.ZeroLorentzianSums
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
# The even bottom against the depth-weighted local energy of the zeros off the line

With test vector `p_ρ = e^{|del ρ|(L+2)/2}` in the weighted Schur test, `AveragedWindowFrameBound`'s averaged-window frame bound gives
`bandBotE ≥ −4(L+2) sup_j W_L(γ_j)`, `W_L(γ_j) = Σ_k m_k e^{|del_k|(L+2)}/(1 + (γ_j − γ_k)²)`, hence a lower bound
for `evLam`; under a uniform depth `d`, `W_L ≤ 2112 e^{d(L+2)} log(2|T| + H + 5)` by `ZeroLorentzianSums`'s local count.
-/

noncomputable section

open Real Matrix
open scoped ComplexConjugate

namespace Cvs.StepA.EvenBottomDepthEnergy
open Cvs.ZeroCounting

open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.StepA.OneZeroParitySectors (ctr)
open Cvs.StepA.TopQuadruple (offLine pairE)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)
open Cvs.StepA.Edge.TopSetCriterion (bandBotE restE)
open Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound (frameKernel)

/-! ### The weighted Schur test -/

/-- **The Schur test with a test vector**: for `m ≥ 0`, a nonnegative symmetric `κ` and `p > 0` with
`Σ_k m_k κ_jk p_k ≤ Λ p_j` for every `j`, `Σ_{j,k} (m_j β_j)(m_k β_k) κ_jk ≤ Λ Σ_j m_j β_j²`. -/
theorem sum_sum_mul_le_schur_weighted {ι : Type} (s : Finset ι) {m : ι → ℝ} (hm : ∀ j ∈ s, 0 ≤ m j)
    (β : ι → ℝ) {κ : ι → ι → ℝ} (hκ0 : ∀ j ∈ s, ∀ k ∈ s, 0 ≤ κ j k)
    (hsym : ∀ j ∈ s, ∀ k ∈ s, κ j k = κ k j) {p : ι → ℝ} (hp : ∀ j ∈ s, 0 < p j) {Λ : ℝ}
    (hΛ : ∀ j ∈ s, ∑ k ∈ s, m k * κ j k * p k ≤ Λ * p j) :
    ∑ j ∈ s, ∑ k ∈ s, (m j * β j) * (m k * β k) * κ j k ≤ Λ * ∑ j ∈ s, m j * β j ^ 2 := by
  classical
  set t := s.filter (fun j => 0 < m j) with ht
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hz : ∀ j ∈ s, j ∉ t → m j = 0 := fun j hj hjt =>
    le_antisymm (not_lt.1 fun h => hjt (Finset.mem_filter.2 ⟨hj, h⟩)) (hm j hj)
  have hpos : ∀ j ∈ t, 0 < m j := fun j hj => (Finset.mem_filter.1 hj).2
  have hLt : ∑ j ∈ s, ∑ k ∈ s, (m j * β j) * (m k * β k) * κ j k
      = ∑ j ∈ t, ∑ k ∈ t, (m j * β j) * (m k * β k) * κ j k := by
    rw [← Finset.sum_subset hts fun j hj hjt => by simp [hz j hj hjt]]
    exact Finset.sum_congr rfl fun j _ =>
      (Finset.sum_subset hts fun k hk hkt => by simp [hz k hk hkt]).symm
  have hRt : ∑ j ∈ s, m j * β j ^ 2 = ∑ j ∈ t, m j * β j ^ 2 :=
    (Finset.sum_subset hts fun j hj hjt => by simp [hz j hj hjt]).symm
  have hrowt : ∀ j ∈ t, ∑ k ∈ t, m k * κ j k * p k ≤ Λ * p j := fun j hj => by
    rw [Finset.sum_subset hts fun k hk hkt => by simp [hz k hk hkt]]
    exact hΛ j (hts hj)
  rw [hLt, hRt]
  have hqq : ∀ j ∈ t, √(m j) * √(m j) = m j := fun j hj => Real.mul_self_sqrt (hm j (hts hj))
  have hq0 : ∀ j ∈ t, 0 < √(m j) := fun j hj => Real.sqrt_pos.2 (hpos j hj)
  have key := Cvs.Prolate.RungEnvelopeSchurTest.schur_bound_weighted (ι := t)
    (fun j => √(m j) * β j) (fun j k => √(m j) * √(m k) * κ j k) (fun j => √(m j) * p j) (e := Λ)
    (fun j k => mul_nonneg (mul_nonneg (hq0 j j.2).le (hq0 k k.2).le) (hκ0 j (hts j.2) k (hts k.2)))
    (fun j k => by rw [hsym j (hts j.2) k (hts k.2)]; ring)
    (fun j => mul_pos (hq0 j j.2) (hp j (hts j.2)))
    (fun j => by
      have e : ∑ k : t, √(m j) * √(m k) * κ j k * (√(m k) * p k)
          = √(m j) * ∑ k ∈ t, m k * κ j k * p k := by
        rw [Finset.mul_sum, ← Finset.sum_coe_sort t]
        refine Finset.sum_congr rfl fun k _ => ?_
        linear_combination (√(m j) * κ j k * p k) * hqq k k.2
      rw [e, show Λ * (√(m j) * p j) = √(m j) * (Λ * p j) by ring]
      exact mul_le_mul_of_nonneg_left (hrowt j j.2) (hq0 j j.2).le)
  have hR : ∑ i : t, (√(m i) * β i) ^ 2 = ∑ j ∈ t, m j * β j ^ 2 := by
    rw [Finset.sum_coe_sort t (fun j => (√(m j) * β j) ^ 2)]
    exact Finset.sum_congr rfl fun j hj => by rw [mul_pow, sq (√(m j)), hqq j hj]
  have hL : ∑ j ∈ t, ∑ k ∈ t, (m j * β j) * (m k * β k) * κ j k
      ≤ ∑ i : t, ∑ k : t, |√(m i) * β i| * |√(m k) * β k| * (√(m i) * √(m k) * κ i k) := by
    rw [← Finset.sum_coe_sort t]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_coe_sort t]
    refine Finset.sum_le_sum fun k _ => ?_
    have hw : 0 ≤ m j * m k * κ j k :=
      mul_nonneg (mul_nonneg (hm j (hts j.2)) (hm k (hts k.2))) (hκ0 j (hts j.2) k (hts k.2))
    rw [abs_mul, abs_mul, abs_of_pos (hq0 j j.2), abs_of_pos (hq0 k k.2)]
    calc (m j * β j) * (m k * β k) * κ j k = m j * m k * κ j k * (β j * β k) := by ring
      _ ≤ m j * m k * κ j k * |β j * β k| := mul_le_mul_of_nonneg_left (le_abs_self _) hw
      _ = _ := by
          rw [abs_mul]
          linear_combination (-(|β j| * |β k| * κ j k * m j)) * hqq k k.2
            - (|β j| * |β k| * κ j k * (√(m k) * √(m k))) * hqq j j.2
  calc _ ≤ _ := hL
    _ ≤ _ := key
    _ = _ := by rw [hR]

/-! ### The frame bound with a test vector -/

/-- **The averaged-window frame bound with a test vector**: `AveragedWindowFrameBound`'s frame bound with the row condition
`Σ_k m_k ‖K_L(z_j − z̄_k)‖ p_k ≤ Λ p_j` (`p > 0`) in place of `Σ_k m_k ‖K_L(z_j − z̄_k)‖ ≤ Λ`. -/
theorem sum_mul_norm_ctr_sq_le_weighted {ι : Type} (s : Finset ι) {m : ι → ℝ} (hm : ∀ j ∈ s, 0 ≤ m j)
    (z : ι → ℂ) {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℝ} (hg : Continuous g) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    {p : ι → ℝ} (hp : ∀ j ∈ s, 0 < p j)
    (hΛ : ∀ j ∈ s, ∑ k ∈ s, m k * ‖frameKernel L (z j - conj (z k))‖ * p k ≤ Λ * p j) :
    ∑ j ∈ s, m j * ‖ctr L g (z j)‖ ^ 2 ≤ Λ * ∫ t in -(L / 2)..L / 2, g t ^ 2 := by
  set S := ∑ j ∈ s, m j * ‖ctr L g (z j)‖ ^ 2 with hSdef
  set c : ι → ℂ := fun j => (m j : ℂ) * conj (ctr L g (z j)) with hc
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j hj => mul_nonneg (hm j hj) (sq_nonneg _)
  have hhc : Continuous fun τ : ℝ => ∑ j ∈ s, c j * Complex.exp (-((τ : ℂ) * z j) * Complex.I) := by
    fun_prop
  have hab : -(L / 2) ≤ L / 2 := by linarith
  have hSint : (S : ℂ) = ∫ t in -(L / 2)..L / 2,
      (∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)) * ((g t : ℝ) : ℂ) := by
    simp_rw [Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum fun j _ => by
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [hSdef]; push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, hc]
    show _ = (m j : ℂ) * conj (ctr L g (z j)) * ctr L g (z j)
    rw [mul_assoc, Complex.conj_mul']
  have hSle : S ≤ ∫ t in -(L / 2)..L / 2,
      ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ * |g t| := by
    have h1 : S = ‖(S : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
    rw [h1, hSint]
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  set Ih := ∫ t in -(L / 2)..L / 2,
    ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ ^ 2 with hIh
  set Ig := ∫ t in -(L / 2)..L / 2, g t ^ 2 with hIg
  have hIg0 : 0 ≤ Ig := intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have hCS : (∫ t in -(L / 2)..L / 2,
      ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ * |g t|) ^ 2 ≤ Ih * Ig := by
    have h := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le hab
      (f := fun t => ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖)
      (w := fun t => |g t|) ((hhc.norm.pow 2).intervalIntegrable _ _)
      ((hg.abs.pow 2).intervalIntegrable _ _) ((hhc.norm.mul hg.abs).intervalIntegrable _ _)
    simp only [sq_abs] at h
    exact h
  have havg := Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound.integral_le_avg hL (φ := fun t =>
      ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ ^ 2) (hhc.norm.pow 2)
    (fun t => sq_nonneg _)
  set R := ∫ u in -(1 / 2 : ℝ)..1 / 2, ∫ t in -((L + 1) / 2)..(L + 1) / 2,
    ‖∑ j ∈ s, c j * Complex.exp (-(((t + u : ℝ) : ℂ) * z j) * Complex.I)‖ ^ 2 with hR
  have hIhR : Ih ≤ R := havg
  have hRQ : R ≤ ∑ j ∈ s, ∑ k ∈ s, (m j * ‖ctr L g (z j)‖) * (m k * ‖ctr L g (z k)‖)
      * ‖frameKernel L (z j - conj (z k))‖ := by
    have hexp := Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound.avg_norm_sq_sum_eq s c z L
    rw [← hR] at hexp
    calc R ≤ |R| := le_abs_self R
      _ = ‖(R : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = _ := by rw [hexp]
      _ ≤ ∑ j ∈ s, ‖∑ k ∈ s, c j * conj (c k) * frameKernel L (z j - conj (z k))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ s, ∑ k ∈ s, ‖c j * conj (c k) * frameKernel L (z j - conj (z k))‖ :=
          Finset.sum_le_sum fun j _ => norm_sum_le _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, hc]
          simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hm j hj), abs_of_nonneg (hm k hk)]
  have hQ : ∑ j ∈ s, ∑ k ∈ s, (m j * ‖ctr L g (z j)‖) * (m k * ‖ctr L g (z k)‖)
      * ‖frameKernel L (z j - conj (z k))‖ ≤ Λ * S :=
    sum_sum_mul_le_schur_weighted s hm (fun j => ‖ctr L g (z j)‖) (fun _ _ _ _ => norm_nonneg _)
      (fun j _ k _ => by
        rw [show z k - conj (z j) = -conj (z j - conj (z k)) by simp,
          Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound.norm_frameKernel_neg_conj hL]) hp hΛ
  have hS2 : S ^ 2 ≤ (Λ * Ig) * S := by
    calc S ^ 2 ≤ (∫ t in -(L / 2)..L / 2,
          ‖∑ j ∈ s, c j * Complex.exp (-((t : ℂ) * z j) * Complex.I)‖ * |g t|) ^ 2 :=
          pow_le_pow_left₀ hS0 hSle 2
      _ ≤ Ih * Ig := hCS
      _ ≤ (Λ * S) * Ig := mul_le_mul_of_nonneg_right ((hIhR.trans hRQ).trans hQ) hIg0
      _ = (Λ * Ig) * S := by ring
  rcases eq_or_lt_of_le hS0 with h0 | hpos
  · rw [← h0]; exact mul_nonneg hΛ0 hIg0
  · nlinarith

/-! ### The kernel between two zeros, depth by depth -/

/-- **The kernel between two zeros at their own depths**: for `L ≥ 0`,
`‖K_L(z_ρ − z̄_σ)‖ ≤ 4(L + 2) e^{|del ρ|(L+2)/2} e^{|del σ|(L+2)/2}/(1 + (γ_ρ − γ_σ)²)`. -/
theorem norm_frameKernel_zPoint_le_depth {L : ℝ} (hL : 0 ≤ L) (ρ σ : nonTrivialZeroSet) :
    ‖frameKernel L (Cvs.ZeroCounting.zPoint ρ - conj (Cvs.ZeroCounting.zPoint σ))‖
      ≤ 4 * (L + 2) * Real.exp (|Cvs.GaussKernel.del ρ| * ((L + 2) / 2))
          * Real.exp (|Cvs.GaussKernel.del σ| * ((L + 2) / 2))
          * (1 / (1 + ((ρ : ℂ).im - (σ : ℂ).im) ^ 2)) := by
  have h := Cvs.Zeta.ExplicitFormula.AveragedWindowFrameBound.norm_frameKernel_le hL
    (Cvs.ZeroCounting.zPoint ρ - conj (Cvs.ZeroCounting.zPoint σ))
  have hre : (Cvs.ZeroCounting.zPoint ρ - conj (Cvs.ZeroCounting.zPoint σ)).re
      = (ρ : ℂ).im - (σ : ℂ).im := by
    rw [Complex.sub_re, Complex.conj_re, Cvs.ZeroCounting.zPoint_re, Cvs.ZeroCounting.zPoint_re]
  have him : (Cvs.ZeroCounting.zPoint ρ - conj (Cvs.ZeroCounting.zPoint σ)).im
      = -Cvs.GaussKernel.del ρ - Cvs.GaussKernel.del σ := by
    rw [Complex.sub_im, Complex.conj_im, Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del,
      Cvs.StepA.TopQuadruple.im_zPoint_eq_neg_del]; ring
  rw [hre, him, div_eq_mul_one_div] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [mul_assoc (4 * (L + 2)), ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by linarith)
  have habs : |-Cvs.GaussKernel.del ρ - Cvs.GaussKernel.del σ|
      ≤ |Cvs.GaussKernel.del ρ| + |Cvs.GaussKernel.del σ| := by
    rw [show -Cvs.GaussKernel.del ρ - Cvs.GaussKernel.del σ
      = -Cvs.GaussKernel.del ρ + -Cvs.GaussKernel.del σ by ring]
    exact (abs_add_le _ _).trans (by rw [abs_neg, abs_neg])
  have hL2 : 0 ≤ (L + 2) / 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right habs hL2]

/-! ### The near zeros against their depth-weighted local energy -/

/-- The depth-weighted local energy of a finite set `F` of zeros at height `T` and scale `L`:
`W_L(F, T) = Σ_{ρ ∈ F} m_ρ e^{|del ρ|(L+2)}/(1 + (γ_ρ − T)²)`. -/
def depthEnergy (L : ℝ) (F : Finset nonTrivialZeroSet) (T : ℝ) : ℝ :=
  ∑ ρ ∈ F, mult ρ * Real.exp (|Cvs.GaussKernel.del ρ| * (L + 2)) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2))

/-- **The near zeros through their depth-weighted local energy**: for `L > 0`, a finite set `F` of zeros and
`W ≥ 0` with `W_L(F, γ_j) ≤ W` at every `j ∈ F`, `Σ_F m_ρ pairE(L, N, ξ, z_ρ) ≥ −4(L + 2) W · L‖ξ‖²`. -/
theorem sum_mult_pairE_ge_depth {L : ℝ} (hL : 0 < L) (N : ℕ) (ξ : Idx N → ℝ)
    (F : Finset nonTrivialZeroSet) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∀ j ∈ F, depthEnergy L F (j : ℂ).im ≤ W) :
    -(4 * (L + 2) * W * (L * (ξ ⬝ᵥ ξ)))
      ≤ ∑ ρ ∈ F, mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := by
  set g := fun t => Cvs.Finite.EvenSectorZeroSide.cosPoly L (mode N) ξ (t + L / 2) with hg
  set Λ := 4 * (L + 2) * W with hΛ
  set p : nonTrivialZeroSet → ℝ := fun ρ => Real.exp (|Cvs.GaussKernel.del ρ| * ((L + 2) / 2)) with hp
  have hΛ0 : 0 ≤ Λ := by have : 0 ≤ L + 2 := by linarith
                         positivity
  have hrow : ∀ j ∈ F, ∑ k ∈ F, mult k
      * ‖frameKernel L (Cvs.ZeroCounting.zPoint j - conj (Cvs.ZeroCounting.zPoint k))‖ * p k ≤ Λ * p j := by
    intro j hj
    calc ∑ k ∈ F, mult k
          * ‖frameKernel L (Cvs.ZeroCounting.zPoint j - conj (Cvs.ZeroCounting.zPoint k))‖ * p k
        ≤ ∑ k ∈ F, mult k * (4 * (L + 2) * p j * p k
            * (1 / (1 + ((j : ℂ).im - (k : ℂ).im) ^ 2))) * p k := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (mult_nonneg k))
            (Real.exp_pos _).le
          exact norm_frameKernel_zPoint_le_depth hL.le j k
      _ = 4 * (L + 2) * p j * depthEnergy L F (j : ℂ).im := by
          unfold depthEnergy
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hpk : p k * p k = Real.exp (|Cvs.GaussKernel.del k| * (L + 2)) := by
            rw [hp]; simp only; rw [← Real.exp_add]; congr 1; ring
          rw [← hpk]
          ring
      _ ≤ 4 * (L + 2) * p j * W :=
          mul_le_mul_of_nonneg_left (hW j hj) (by have := (Real.exp_pos (|Cvs.GaussKernel.del j| * ((L + 2) / 2))).le
                                                  have : 0 ≤ L + 2 := by linarith
                                                  positivity)
      _ = Λ * p j := by rw [hΛ]; ring
  have hframe := sum_mul_norm_ctr_sq_le_weighted F (fun ρ _ => mult_nonneg ρ)
    Cvs.ZeroCounting.zPoint hL.le (Cvs.StepA.EvenBottomNearZeroFrame.continuous_cosPoly_centred L N ξ) hΛ0
    (fun ρ _ => Real.exp_pos _) hrow
  have hE := Cvs.StepA.ModePolynomialFarEnvelope.integral_cosPoly_centred_sq_le hL
    (Cvs.Finite.SymmetricModeSet.mode_injective N) (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) ξ
  have hpt : ∀ ρ ∈ F, -(mult ρ * ‖ctr L g (Cvs.ZeroCounting.zPoint ρ)‖ ^ 2)
      ≤ mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ) := fun ρ _ => by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left
      (Cvs.StepA.EvenBottomNearZeroFrame.neg_norm_ctr_sq_le_pairE hL.ne' N ξ _) (mult_nonneg ρ)
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_neg_distrib] at hsum
  have := mul_le_mul_of_nonneg_left hE hΛ0
  linarith

/-- **The even band bottom against the depth-weighted local energy**: for `L > 0`, a finite set `F` of zeros
and `W ≥ 0` with `W_L(F, γ_j) ≤ W` at every `j ∈ F`, `bandBotE L N F ≥ −4(L + 2) W`. -/
theorem neg_le_bandBotE_depth {L : ℝ} (hL : 0 < L) (N : ℕ) (F : Finset nonTrivialZeroSet) {W : ℝ}
    (hW0 : 0 ≤ W) (hW : ∀ j ∈ F, depthEnergy L F (j : ℂ).im ≤ W) :
    -(4 * (L + 2) * W) ≤ bandBotE L N (F : Set nonTrivialZeroSet) := by
  refine le_csInf (Cvs.StepA.Edge.TopSetCriterion.bandRayE_nonempty hL N _) ?_
  rintro r ⟨ξ, -, hne, rfl⟩
  rw [le_div_iff₀ (Cvs.StepA.Edge.TopSetCriterion.mul_dot_pos hL hne), Finset.tsum_subtype' F
    (fun ρ => mult ρ * pairE L N ξ (Cvs.ZeroCounting.zPoint ρ))]
  have := sum_mult_pairE_ge_depth hL N ξ F hW0 hW
  linarith

/-- **The even bottom against the depth-weighted local energy of the near off-line zeros**: for `L > 0`, every
`N`, every height `H` and `W ≥ 0` bounding the depth-weighted local energy of the off-line zeros below `H` at each
of their ordinates, `evLam ≥ −4(L + 2) W − restE L N (nearZeros H)`. -/
theorem evLam_ge_neg_depthEnergy {L : ℝ} (hL : 0 < L) (N : ℕ) (H : ℝ) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∀ j ∈ (Cvs.StepA.EvenBottomNearZeroFrame.nearZeros_finite H).toFinset,
      depthEnergy L (Cvs.StepA.EvenBottomNearZeroFrame.nearZeros_finite H).toFinset (j : ℂ).im ≤ W) :
    -(4 * (L + 2) * W) - restE L N (Cvs.StepA.EvenBottomNearZeroFrame.nearZeros H)
      ≤ Cvs.Finite.EvenMinimisers.evLam ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L hL N := by
  have hfin := Cvs.StepA.EvenBottomNearZeroFrame.nearZeros_finite H
  have hband := Cvs.StepA.Edge.TopSetCriterion.evLam_ge_band hL N
    (S := Cvs.StepA.EvenBottomNearZeroFrame.nearZeros H) fun _ hρ => hρ.1
  have hbot : -(4 * (L + 2) * W) ≤ bandBotE L N (Cvs.StepA.EvenBottomNearZeroFrame.nearZeros H) := by
    rw [← hfin.coe_toFinset]
    exact neg_le_bandBotE_depth hL N hfin.toFinset hW0 hW
  linarith

/-! ### A uniform depth -/

/-- **A uniform depth bounds the local energy by the local count**: if every zero of `F` has `|del| ≤ d` and
`|γ| ≤ H`, then `W_L(F, T) ≤ 2112 e^{d(L+2)} log(2|T| + H + 5)` (Cvs.Zeta.ZeroCounting.ZeroLorentzianSums). -/
theorem depthEnergy_le_of_depth {L : ℝ} (hL : 0 ≤ L) (F : Finset nonTrivialZeroSet) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ ρ ∈ F, |(ρ : ℂ).im| ≤ H) {d : ℝ} (hd : ∀ ρ ∈ F, |Cvs.GaussKernel.del ρ| ≤ d) (T : ℝ) :
    depthEnergy L F T ≤ Real.exp (d * (L + 2)) * (2112 * Real.log (2 * |T| + H + 5)) := by
  have hc := Cvs.Zeta.ZeroCounting.ZeroLorentzianSums.sum_mult_inv_one_add_sq_le F hH0 hH T
  unfold depthEnergy
  calc ∑ ρ ∈ F, mult ρ * Real.exp (|Cvs.GaussKernel.del ρ| * (L + 2)) * (1 / (1 + (T - (ρ : ℂ).im) ^ 2))
      ≤ ∑ ρ ∈ F, Real.exp (d * (L + 2)) * (mult ρ * (1 / (1 + (T - (ρ : ℂ).im) ^ 2))) := by
        refine Finset.sum_le_sum fun ρ hρ => ?_
        have h1 : Real.exp (|Cvs.GaussKernel.del ρ| * (L + 2)) ≤ Real.exp (d * (L + 2)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hd ρ hρ) (by linarith))
        have h2 : 0 ≤ mult ρ * (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) :=
          mul_nonneg (mult_nonneg ρ) (by positivity)
        nlinarith
    _ = Real.exp (d * (L + 2)) * ∑ ρ ∈ F, mult ρ * (1 / (1 + (T - (ρ : ℂ).im) ^ 2)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (d * (L + 2)) * (2112 * Real.log (2 * |T| + H + 5)) :=
        mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le

end Cvs.StepA.EvenBottomDepthEnergy
