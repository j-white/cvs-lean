import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.DeepPointBlaschkeCount
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.HighDeepProjection
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.ExpSumContourInterpolation
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.RectArgument
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The gap rectangle, and the Blaschke product at a high deep point

When no deep ordinate lies within `1` of `H`, the rectangle `[δ_D/4, 2] × [−H, H]` holds the deep points strictly,
its boundary Blaschke bound is `DeepPointBlaschkeCount`'s, and every deep `w_ρ` above `H` is at distance `≥ |γ_ρ| − H ≥ 1` from it.
At such `w_ρ`, `1 − |B(w_ρ)|² ≤ φ_ρ` and `|B(w_ρ)|^{−2} ≤ e^{φ_ρ}`, `φ_ρ = Σ_{ρ' ∈ D} (|γ_ρ| − |γ_ρ'|)^{−2}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Upstream.ExpSumBlaschkeProduct (blaschke bfac)
open Cvs.Upstream.ExpSumContourInterpolation (OnBd Inside)
open Cvs.StepA.Edge.WindowCoshTransformDuality (wR)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)
open Cvs.StepA.Edge.DeepPointBlaschkeCount (deepPts bexp)

namespace Cvs.StepA.Edge.GapRectangleBlaschke
open Cvs.ZeroCounting

/-- The gap rectangle's lower-left corner `δ_D/4 − iH`. -/
def zg (δD H : ℝ) : ℂ := ((δD / 4 : ℝ) : ℂ) - ((H : ℝ) : ℂ) * I

/-- The gap rectangle's upper-right corner `2 + iH`. -/
def wg (H : ℝ) : ℂ := ((2 : ℝ) : ℂ) + ((H : ℝ) : ℂ) * I

@[simp] theorem zg_re (δD H : ℝ) : (zg δD H).re = δD / 4 := by simp [zg]
@[simp] theorem zg_im (δD H : ℝ) : (zg δD H).im = -H := by simp [zg]
@[simp] theorem wg_re (H : ℝ) : (wg H).re = 2 := by simp [wg]
@[simp] theorem wg_im (H : ℝ) : (wg H).im = H := by simp [wg]

/-- No deep ordinate lies within `1` of `H`. -/
def Gap (δD H : ℝ) : Prop :=
  ∀ ρ : nonTrivialZeroSet, δD ≤ |Cvs.GaussKernel.del ρ| → 1 ≤ |(|(ρ : ℂ).im| - H)|

theorem im_le_of_gap {δD H : ℝ} (hg : Gap δD H) {ζ : ℂ} (hζ : ζ ∈ deepPts δD H) : |ζ.im| ≤ H - 1 := by
  obtain ⟨ρ, hρ, rfl, _, _, h3⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts hζ
  have h := hg ρ (mem_deepSet.1 hρ).2
  rw [Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im] at h3 ⊢
  rw [abs_of_nonpos (by linarith)] at h
  linarith

theorem inside_gap {δD H : ℝ} (hδ : 0 < δD) (hg : Gap δD H) {ζ : ℂ} (hζ : ζ ∈ deepPts δD H) :
    Inside (zg δD H) (wg H) ζ := by
  obtain ⟨_, _, _, h1, h2, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts hζ
  have h3 := abs_le.1 (im_le_of_gap hg hζ)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith [h3.1, h3.2]

/-- **The boundary Blaschke bound on the gap rectangle**: `|B_Λ| ≥ e^{−bexp·log(5H + 7)}`. -/
theorem norm_blaschke_ge_onBd_gap {δD H : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2) (hH : 1 ≤ H) (hg : Gap δD H)
    {u : ℂ} (hu : OnBd (zg δD H) (wg H) u) :
    Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7))) ≤ ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) u‖ := by
  rw [Cvs.StepA.Edge.DeepPointBlaschkeCount.bexp_cast]
  set Λ := deepPts δD H
  obtain ⟨⟨hure, huim⟩, hedge⟩ := hu
  rw [Set.mem_preimage, zg_re, wg_re, Set.uIcc_of_le (by linarith)] at hure
  rw [Set.mem_preimage, zg_im, wg_im, Set.uIcc_of_le (by linarith)] at huim
  rw [zg_re, wg_re, zg_im, wg_im] at hedge
  have hu0 : 0 < u.re := by linarith [hure.1]
  have hfac : ∀ ζ ∈ Λ, Real.exp (-(8 * (1 / (1 + (u.im - ζ.im) ^ 2)))) ≤ ‖bfac ζ u‖ := by
    intro ζ hζ
    obtain ⟨ρ, _, _, h1, h2, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts hζ
    have h3 := abs_le.1 (im_le_of_gap hg hζ)
    have hζ0 : 0 < ζ.re := by linarith
    have hne : u ≠ ζ := by
      intro h; subst h
      rcases hedge with h | h | h | h <;> linarith [h3.1, h3.2]
    refine le_trans ?_ (Cvs.StepA.Edge.DeepPointBlaschkeCount.exp_le_norm_bfac hζ0 hu0.le hne)
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have key : 4 * u.re * ζ.re / ‖u - ζ‖ ^ 2 ≤ 16 / (1 + (u.im - ζ.im) ^ 2) := by
      rcases hedge with h | h | h | h
      · exact Cvs.StepA.Edge.DeepPointBlaschkeCount.ratio_le_left hu0 (by rw [h]; linarith) h2.le
      · exact Cvs.StepA.Edge.DeepPointBlaschkeCount.ratio_le_right (by rw [h]) (by rw [h]; linarith) hζ0
      · refine Cvs.StepA.Edge.DeepPointBlaschkeCount.ratio_le_far hu0.le hure.2 hζ0 h2.le ?_
        rw [h, abs_of_nonpos (by linarith [h3.1])]; linarith [h3.1]
      · refine Cvs.StepA.Edge.DeepPointBlaschkeCount.ratio_le_far hu0.le hure.2 hζ0 h2.le ?_
        rw [h, abs_of_nonneg (by linarith [h3.2])]; linarith [h3.2]
    have e : 2 * u.re * ζ.re / ‖u - ζ‖ ^ 2 = (4 * u.re * ζ.re / ‖u - ζ‖ ^ 2) / 2 := by ring
    rw [e]
    have : 16 / (1 + (u.im - ζ.im) ^ 2) / 2 = 8 * (1 / (1 + (u.im - ζ.im) ^ 2)) := by ring
    linarith
  have hprod : Real.exp (-(8 * ∑ ζ ∈ Λ, 1 / (1 + (u.im - ζ.im) ^ 2)))
      ≤ ‖blaschke (fun ζ : Λ => (ζ : ℂ)) u‖ := by
    rw [Cvs.Upstream.ExpSumBlaschkeProduct.blaschke, norm_prod, Finset.prod_coe_sort Λ (fun ζ => ‖bfac ζ u‖), Finset.mul_sum,
      ← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun ζ _ => (Real.exp_pos _).le) hfac
  refine le_trans (Real.exp_le_exp.2 (neg_le_neg ?_)) hprod
  have hs := Cvs.StepA.Edge.DeepPointBlaschkeCount.sum_deepPts_le (δD := δD) (by linarith : (0 : ℝ) ≤ H) u.im
  have hyabs : |u.im| ≤ H := abs_le.2 ⟨huim.1, huim.2⟩
  have hlog : Real.log (2 * |u.im| + H + 5) ≤ Real.log (5 * H + 7) :=
    Real.log_le_log (by positivity) (by linarith)
  nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 * |u.im| + H + 5 by linarith [abs_nonneg u.im])]

/-- A deep `w_ρ` above `H` is at distance `≥ |γ_ρ| − H` from the gap rectangle's boundary, with either sign and
conjugate. -/
theorem dist_onBd {δD H : ℝ} (hH : 0 ≤ H) {ρ : nonTrivialZeroSet} {u : ℂ} (hu : OnBd (zg δD H) (wg H) u) (c : ℂ)
    (hc : |c.im| = |(ρ : ℂ).im|) : |(ρ : ℂ).im| - H ≤ ‖u - c‖ ∧ |(ρ : ℂ).im| - H ≤ ‖u + c‖ := by
  obtain ⟨⟨_, huim⟩, _⟩ := hu
  rw [Set.mem_preimage, zg_im, wg_im] at huim
  have hy : |u.im| ≤ H := by
    rw [Set.uIcc_of_le (by linarith)] at huim; exact abs_le.2 ⟨huim.1, huim.2⟩
  constructor
  · have h1 : |(u - c).im| ≤ ‖u - c‖ := Complex.abs_im_le_norm _
    have h2 : |c.im| - |u.im| ≤ |(u - c).im| := by
      rw [Complex.sub_im, abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    linarith
  · have h1 : |(u + c).im| ≤ ‖u + c‖ := Complex.abs_im_le_norm _
    have h2 : |c.im| - |u.im| ≤ |(u + c).im| := by
      rw [Complex.add_im]
      have := abs_sub_abs_le_abs_sub c.im (-u.im)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this; exact this
    linarith

/-- `|b_q(u)|²(1 + 4 Re u Re q/|u − q|²) = 1` for `u ≠ q`, `Re q > 0`, `Re u ≥ 0`. -/
theorem norm_sq_bfac_mul {q u : ℂ} (hq : 0 < q.re) (hu : 0 ≤ u.re) (hne : u ≠ q) :
    ‖bfac q u‖ ^ 2 * (1 + 4 * u.re * q.re / ‖u - q‖ ^ 2) = 1 := by
  have h0 : 0 < ‖u - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hd := Cvs.Upstream.ExpSumBlaschkeProduct.add_conj_ne_zero hq hu
  have hd0 : 0 < ‖u + conj q‖ := norm_pos_iff.2 hd
  have hid := Cvs.Upstream.ExpSumBlaschkeProduct.normSq_add_conj_sub q u
  rw [Cvs.Upstream.ExpSumBlaschkeProduct.bfac, norm_div, div_pow]
  have : ‖u + conj q‖ ^ 2 = ‖u - q‖ ^ 2 + 4 * u.re * q.re := by linarith
  rw [this]
  field_simp

/-- The pair sum `φ_ρ = Σ_{ρ' ∈ D} (|γ_ρ| − |γ_ρ'|)^{−2}`. -/
def phi (δD H : ℝ) (ρ : nonTrivialZeroSet) : ℝ :=
  ∑ ρ' ∈ deepSet δD H, 1 / (|(ρ : ℂ).im| - |(ρ' : ℂ).im|) ^ 2

/-- One deep point against a higher zero: `4 Re w_ρ Re ζ/|w_ρ − ζ|² ≤ (|γ_ρ| − |Im ζ|)^{−2}`. -/
theorem ratio_le_inv_sq {ρ : nonTrivialZeroSet} {ζ : ℂ} (hζ0 : 0 < ζ.re) (hζ1 : ζ.re < 1 / 2)
    (hlt : |ζ.im| < |(ρ : ℂ).im|) :
    4 * (wR ρ).re * ζ.re / ‖wR ρ - ζ‖ ^ 2 ≤ 1 / (|(ρ : ℂ).im| - |ζ.im|) ^ 2 := by
  have hre : (wR ρ).re < 1 / 2 := by rw [Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re]; exact Cvs.StepA.Edge.TransplantAngleHighZeros.abs_del_lt_half ρ
  have hre0 : 0 ≤ (wR ρ).re := by rw [Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re]; exact abs_nonneg _
  have hd : 0 < |(ρ : ℂ).im| - |ζ.im| := by linarith
  have him : |(ρ : ℂ).im| - |ζ.im| ≤ ‖wR ρ - ζ‖ := by
    have h1 : |(wR ρ - ζ).im| ≤ ‖wR ρ - ζ‖ := Complex.abs_im_le_norm _
    have h2 : |(wR ρ).im| - |ζ.im| ≤ |(wR ρ - ζ).im| := by
      rw [Complex.sub_im]; exact abs_sub_abs_le_abs_sub _ _
    rw [Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im] at h2
    linarith
  have hsq : (|(ρ : ℂ).im| - |ζ.im|) ^ 2 ≤ ‖wR ρ - ζ‖ ^ 2 := pow_le_pow_left₀ hd.le him 2
  have hn : 0 < ‖wR ρ - ζ‖ ^ 2 := lt_of_lt_of_le (by positivity) hsq
  rw [div_le_div_iff₀ hn (by positivity)]
  have h4 : 4 * (wR ρ).re * ζ.re ≤ 1 := by nlinarith
  nlinarith

/-- **The Blaschke product at a higher zero**: if every deep ordinate below `H` is below `|γ_ρ|`, then
`|B(w_ρ)|^{−2} ≤ e^{φ_ρ}` and `1 − |B(w_ρ)|² ≤ φ_ρ`. -/
theorem blaschke_at_high {δD H : ℝ} (hδ : 0 < δD) {ρ : nonTrivialZeroSet}
    (hab : ∀ ρ' ∈ deepSet δD H, |(ρ' : ℂ).im| < |(ρ : ℂ).im|) :
    0 < ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) (wR ρ)‖
      ∧ ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) (wR ρ)‖⁻¹ ^ 2 ≤ Real.exp (phi δD H ρ)
      ∧ 1 - ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) (wR ρ)‖ ^ 2 ≤ phi δD H ρ := by
  set Λ := deepPts δD H
  set α := wR ρ
  have hα0 : 0 ≤ α.re := by rw [Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re]; exact abs_nonneg _
  set t : ℂ → ℝ := fun ζ => 4 * α.re * ζ.re / ‖α - ζ‖ ^ 2 with ht
  have hfacts : ∀ ζ ∈ Λ, 0 < ζ.re ∧ ζ.re < 1 / 2 ∧ |ζ.im| < |(ρ : ℂ).im| ∧ α ≠ ζ := by
    intro ζ hζ
    obtain ⟨ρ', hρ', rfl, h1, h2, _⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts hζ
    have hlt := hab ρ' hρ'
    refine ⟨by linarith, h2, by rw [Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im]; exact hlt, fun h => ?_⟩
    have := congrArg (fun z : ℂ => |z.im|) h
    simp only [α, Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im] at this
    linarith
  have ht0 : ∀ ζ ∈ Λ, 0 ≤ t ζ := fun ζ hζ => by
    have := (hfacts ζ hζ).1; simp only [ht]; positivity
  have hfac : ∀ ζ ∈ Λ, ‖bfac ζ α‖ ^ 2 * (1 + t ζ) = 1 := fun ζ hζ =>
    norm_sq_bfac_mul (hfacts ζ hζ).1 hα0 (hfacts ζ hζ).2.2.2
  have hB : ‖blaschke (fun ζ : Λ => (ζ : ℂ)) α‖ = ∏ ζ ∈ Λ, ‖bfac ζ α‖ := by
    rw [Cvs.Upstream.ExpSumBlaschkeProduct.blaschke, norm_prod, Finset.prod_coe_sort Λ (fun ζ => ‖bfac ζ α‖)]
  have hprod : ‖blaschke (fun ζ : Λ => (ζ : ℂ)) α‖ ^ 2 * ∏ ζ ∈ Λ, (1 + t ζ) = 1 := by
    rw [hB, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one hfac
  have hP1 : 1 ≤ ∏ ζ ∈ Λ, (1 + t ζ) := by
    calc (1 : ℝ) = ∏ ζ ∈ Λ, (1 : ℝ) := by simp
      _ ≤ ∏ ζ ∈ Λ, (1 + t ζ) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun ζ hζ => by linarith [ht0 ζ hζ]
  have hβ2 : 0 < ‖blaschke (fun ζ : Λ => (ζ : ℂ)) α‖ ^ 2 := by
    by_contra h
    rw [not_lt] at h
    have h0 : ‖blaschke (fun ζ : Λ => (ζ : ℂ)) α‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
    rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
  have hβ : 0 < ‖blaschke (fun ζ : Λ => (ζ : ℂ)) α‖ := by
    rcases (norm_nonneg (blaschke (fun ζ : Λ => (ζ : ℂ)) α)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hβ2; simp at hβ2
  -- the sum of the ratios
  have hsum : ∑ ζ ∈ Λ, t ζ ≤ phi δD H ρ := by
    have h1 : ∑ ζ ∈ Λ, t ζ ≤ ∑ ζ ∈ Λ, 1 / (|(ρ : ℂ).im| - |ζ.im|) ^ 2 :=
      Finset.sum_le_sum fun ζ hζ => ratio_le_inv_sq (hfacts ζ hζ).1 (hfacts ζ hζ).2.1 (hfacts ζ hζ).2.2.1
    refine h1.trans ?_
    refine (Finset.sum_image_le_of_nonneg (s := deepSet δD H) (g := wR)
      (f := fun ζ : ℂ => 1 / (|(ρ : ℂ).im| - |ζ.im|) ^ 2) fun _ _ => by positivity).trans_eq ?_
    unfold phi
    refine Finset.sum_congr rfl fun ρ' _ => ?_
    rw [Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im]
  have hexp : ∏ ζ ∈ Λ, (1 + t ζ) ≤ Real.exp (∑ ζ ∈ Λ, t ζ) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun ζ hζ => by linarith [ht0 ζ hζ]) fun ζ _ => by
      have := Real.add_one_le_exp (t ζ); linarith
  have hinv : ‖blaschke (fun ζ : Λ => (ζ : ℂ)) α‖⁻¹ ^ 2 = ∏ ζ ∈ Λ, (1 + t ζ) := by
    rw [inv_pow]; exact (eq_inv_of_mul_eq_one_right hprod).symm
  refine ⟨hβ, ?_, ?_⟩
  · rw [hinv]; exact hexp.trans (Real.exp_le_exp.2 hsum)
  · have h1 : ‖blaschke (fun ζ : Λ => (ζ : ℂ)) α‖ ^ 2 = 1 / ∏ ζ ∈ Λ, (1 + t ζ) := by
      rw [eq_div_iff (by linarith)]; exact hprod
    rw [h1]
    have hP : 0 < ∏ ζ ∈ Λ, (1 + t ζ) := by linarith
    have h2 : Real.exp (-(∑ ζ ∈ Λ, t ζ)) ≤ 1 / ∏ ζ ∈ Λ, (1 + t ζ) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hP hexp
    have h3 := Real.add_one_le_exp (-(∑ ζ ∈ Λ, t ζ))
    linarith

/-- The gap rectangle's contour constant. -/
def kcg (δD H : ℝ) : ℝ :=
  (2 * ((wg H).re - (zg δD H).re) + 2 * ((wg H).im - (zg δD H).im))
    / (2 * Real.pi * Real.exp (-((bexp : ℝ) * Real.log (5 * H + 7))) * √(2 * (zg δD H).re))

/-- The gap rectangle's contraction constant at `x`. -/
def qg (x : ℕ) (δD H : ℝ) : ℝ :=
  kcg δD H * (2 * Real.exp (-((zg δD H).re * (Real.log x / 2))) / √(2 * (zg δD H).re))

/-- `e^φ ≤ 1 + 2φ` for `0 ≤ φ ≤ 1`. -/
theorem exp_le_one_add_two_mul {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1) : Real.exp φ ≤ 1 + 2 * φ := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (by linarith : (0 : ℝ) ≤ 1 - φ) h0
    (by ring : (1 - φ) + φ = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at h
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The squared projection of a high deep `U_ρ`** (caseinf-W Theorem C (i)–(v)): on the gap rectangle with
`q ≤ ½` and `φ_ρ ≤ 1`, `‖P_{U_D}U_ρ‖² ≤ 16x^{Θ'}(3φ_ρ/δ_D + 4K_c²x^{−δ_D/2}/(|γ_ρ| − H)²)`. -/
theorem norm_sq_proj_le_gap {x : ℕ} (hx0 : (0 : ℝ) < x) {δD H : ℝ} (hδ : 0 < δD) (hδ' : δD < 1 / 2)
    (hH : 1 ≤ H) (hg : Gap δD H) (hq : qg x δD H ≤ 1 / 2) {ρ : nonTrivialZeroSet}
    (hρD : δD ≤ |Cvs.GaussKernel.del ρ|) (hρH : H < |(ρ : ℂ).im|) (hφ : phi δD H ρ ≤ 1) :
    ‖(Cvs.StepA.Edge.FiniteTopCorrectedClosing.USpan hx0 (deepSet δD H)).starProjection (Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2
      ≤ 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * (3 * phi δD H ρ / δD
        + 4 * kcg δD H ^ 2 * (x : ℝ) ^ (-(δD / 2)) / (|(ρ : ℂ).im| - H) ^ 2) := by
  set T : ℝ := Real.log x / 2 with hT
  have hx1 : (1 : ℝ) ≤ x := by
    rcases Nat.lt_or_ge x 1 with h | h
    · interval_cases x; simp at hx0
    · exact_mod_cast h
  have hT0 : 0 ≤ T := by have := Real.log_natCast_nonneg x; positivity
  set δ := |Cvs.GaussKernel.del ρ| with hδdef
  have hδ0 : 0 < δ := by linarith
  have hρδ : Cvs.GaussKernel.del ρ ≠ 0 := fun h => by rw [h, abs_zero] at hδdef; linarith
  set r := |(ρ : ℂ).im| - H with hr
  have hr0 : 0 < r := by linarith
  have hab : ∀ ρ' ∈ deepSet δD H, |(ρ' : ℂ).im| < |(ρ : ℂ).im| := fun ρ' hρ' => by
    linarith [(mem_deepSet.1 hρ').1]
  obtain ⟨hβ0, hβinv, hβ1⟩ := blaschke_at_high hδ hab
  set β := ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) (wR ρ)‖ with hβ
  set φ := phi δD H ρ with hφdef
  have hφ0 : 0 ≤ φ := Finset.sum_nonneg fun _ _ => by positivity
  have hdist : ∀ u, OnBd (zg δD H) (wg H) u → (r ≤ ‖u - wR ρ‖ ∧ r ≤ ‖u + wR ρ‖)
      ∧ (r ≤ ‖u - conj (wR ρ)‖ ∧ r ≤ ‖u + conj (wR ρ)‖) := fun u hu =>
    ⟨dist_onBd (by linarith) hu (wR ρ) (Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im ρ),
      dist_onBd (by linarith) hu (conj (wR ρ)) (by rw [Complex.conj_im, abs_neg, Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im])⟩
  have hqq : qg x δD H < 1 := by linarith
  have h := Cvs.StepA.Edge.HighDeepProjection.norm_proj_le hx0 (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (fun ζ hζ => inside_gap hδ hg hζ) (Real.exp_pos _)
    (fun u hu => norm_blaschke_ge_onBd_gap hδ hδ' hH hg hu) hqq hρδ hρH hr0 hdist
  have hKc0 : 0 ≤ kcg δD H := by
    unfold kcg; rw [zg_re, zg_im, wg_re, wg_im]
    refine div_nonneg (by nlinarith) ?_
    have := Real.pi_pos; have := Real.sqrt_nonneg (2 * (δD / 4)); positivity
  have hq0 : 0 ≤ qg x δD H := by
    unfold qg; rw [zg_re]
    have : 0 ≤ √(2 * (δD / 4)) := Real.sqrt_nonneg _
    exact mul_nonneg hKc0 (by positivity)
  set Kc := kcg δD H
  set q := qg x δD H
  -- the constant
  set E := Real.exp (δ * T) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hEm : Real.exp (-(δ * T)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hexpr : Real.exp (-(2 * (zg δD H).re * T)) / r = (x : ℝ) ^ (-(δD / 4)) / r := by
    rw [zg_re, Real.rpow_def_of_pos hx0, hT]; congr 1; congr 1; ring
  set er := (x : ℝ) ^ (-(δD / 4)) / r with her
  have her0 : 0 ≤ er := by positivity
  have hβi : β⁻¹ ≤ 2 := by
    have h1 : β⁻¹ ^ 2 ≤ Real.exp 1 := hβinv.trans (Real.exp_le_exp.2 hφ)
    have h2 : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; linarith
    nlinarith [inv_nonneg.2 hβ0.le]
  have hs1 : √((1 - β ^ 2) / (2 * δ)) ≤ √(3 * φ / δD) := Real.sqrt_le_sqrt (by
    rw [div_le_div_iff₀ (by positivity) hδ]; nlinarith)
  have hs2 : √((β⁻¹ ^ 2 - 1) / (2 * δ)) ≤ √(3 * φ / δD) := Real.sqrt_le_sqrt (by
    have hb : β⁻¹ ^ 2 - 1 ≤ 3 * φ := by
      have h1 := exp_le_one_add_two_mul hφ0 hφ
      linarith
    rw [div_le_div_iff₀ (by positivity) hδ]; nlinarith)
  set sφ := √(3 * φ / δD) with hsφ
  have hsφ0 : 0 ≤ sφ := Real.sqrt_nonneg _
  have hK : Cvs.StepA.Edge.HighDeepProjection.kRho T δ β Kc er ≤ E * (sφ + 2 * Kc * er) := by
    unfold Cvs.StepA.Edge.HighDeepProjection.kRho
    have hA := mul_le_mul_of_nonneg_left hs1 (Real.exp_pos (δ * T)).le
    have hB := mul_le_mul hEm hs2 (Real.sqrt_nonneg _) zero_le_one
    have hC : Kc * er * (Real.exp (-(δ * T)) + E * (1 + β⁻¹)) ≤ Kc * er * (4 * E) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKc0 her0)
      nlinarith
    rw [← hE] at hA
    nlinarith [mul_nonneg hKc0 her0]
  have hh : ‖(Cvs.StepA.Edge.FiniteTopCorrectedClosing.USpan hx0 (deepSet δD H)).starProjection (Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖
      ≤ √2 * Cvs.StepA.Edge.HighDeepProjection.kRho T δ β Kc er / (1 - q) := by
    have e1 : Real.exp (-(2 * (zg δD H).re * (Real.log x / 2))) / r = er := hexpr
    rw [e1] at h
    exact h
  have hq1 : 1 / 2 ≤ 1 - q := by linarith
  have hKr0 : 0 ≤ Cvs.StepA.Edge.HighDeepProjection.kRho T δ β Kc er := by
    unfold Cvs.StepA.Edge.HighDeepProjection.kRho
    have : 0 ≤ (1 - β ^ 2) / (2 * δ) ∨ True := Or.inr trivial
    positivity
  have hP : ‖(Cvs.StepA.Edge.FiniteTopCorrectedClosing.USpan hx0 (deepSet δD H)).starProjection (Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖
      ≤ 2 * √2 * (E * (sφ + 2 * Kc * er)) := by
    refine hh.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have h1 : √2 * Cvs.StepA.Edge.HighDeepProjection.kRho T δ β Kc er ≤ √2 * (E * (sφ + 2 * Kc * er)) :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    have hX : 0 ≤ √2 * (E * (sφ + 2 * Kc * er)) := by
      have := mul_nonneg hKc0 her0; positivity
    have h2 : √2 * (E * (sφ + 2 * Kc * er)) ≤ 2 * √2 * (E * (sφ + 2 * Kc * er)) * (1 - q) := by
      nlinarith
    linarith
  have hE2 : E ^ 2 ≤ (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth := by
    rw [hE, ← Real.exp_nat_mul, Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.2 ?_
    have hd := Cvs.StepA.Edge.CaseInfinityJointRates.abs_del_le_topDepth ρ
    have hL := Real.log_nonneg hx1
    rw [hT]; push_cast; nlinarith
  have hsq2 : (2 : ℝ) = √2 ^ 2 := (Real.sq_sqrt (by norm_num)).symm
  have hsφ2 : sφ ^ 2 = 3 * φ / δD := Real.sq_sqrt (by positivity)
  have her2 : er ^ 2 = (x : ℝ) ^ (-(δD / 2)) / r ^ 2 := by
    rw [her, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num; ring_nf
  calc ‖(Cvs.StepA.Edge.FiniteTopCorrectedClosing.USpan hx0 (deepSet δD H)).starProjection (Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2
      ≤ (2 * √2 * (E * (sφ + 2 * Kc * er))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hP 2
    _ = 8 * E ^ 2 * (sφ + 2 * Kc * er) ^ 2 := by rw [mul_pow, mul_pow, mul_pow, ← hsq2]; ring
    _ ≤ 8 * E ^ 2 * (2 * (sφ ^ 2 + 4 * Kc ^ 2 * er ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [sq_nonneg (sφ - 2 * Kc * er)]
    _ = 16 * E ^ 2 * (3 * φ / δD + 4 * Kc ^ 2 * (x : ℝ) ^ (-(δD / 2)) / r ^ 2) := by
        rw [hsφ2, her2]; ring
    _ ≤ 16 * (x : ℝ) ^ Cvs.StepA.Edge.CaseInfinityJointRates.topDepth * (3 * φ / δD + 4 * Kc ^ 2 * (x : ℝ) ^ (-(δD / 2)) / r ^ 2) := by
        refine mul_le_mul_of_nonneg_right (by linarith) ?_
        have : 0 ≤ (x : ℝ) ^ (-(δD / 2)) := by positivity
        positivity
