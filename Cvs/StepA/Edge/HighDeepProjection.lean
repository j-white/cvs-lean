import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.Edge.DeepPointBlaschkeCount
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.GramPairingInterpolation
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.StepA.Edge.ZeroVectorTransformSplit
import Cvs.Upstream.ExpSumBlaschkeProduct
import Cvs.Upstream.ExpSumContourInterpolation
import Cvs.Upstream.ModelSpaceKernels
import Cvs.Upstream.PointInterpolationHardyDatum
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
# The projection of a high deep `U_ρ` on the deep span

The pairing of `E_c` with the points splits into the kernel terms `I₁`, `I₃` (Cvs.Upstream.ModelSpaceKernels) and two contour terms carrying
`e^{−2ζT}` (Cvs.Upstream.ExpSumContourInterpolation). With Cvs.StepA.Edge.GramPairingInterpolation this gives a window class reproducing `F_{U_ρ}` on the deep points, so
`‖P_{U_D}U_ρ‖ ≤ 2^{1/2}K_ρ/(1 − q)` with `K_ρ` explicit in `|B(w_ρ)|`, `x^{|δ_ρ|/2}` and the contour constant
(caseinf-W Theorem C (ii)–(iv)).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate InnerProductSpace
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Upstream.ExpSumBlaschkeProduct (lap gram blaschke)
open Cvs.Upstream.ExpSumContourInterpolation (OnBd Inside)
open Cvs.StepA.Edge.WindowCoshTransformDuality (wR coshT emb)
open Cvs.StepA.Edge.ZeroVectorTransformSplit (E)
open Cvs.Zeta (closedRect)

namespace Cvs.StepA.Edge.HighDeepProjection
open Cvs.ZeroCounting

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The contour term with the pole removed: `g₄(ζ) = e^{−2ζT}(B(c) − B(ζ))/((ζ − c)B(c))`. -/
def g4 (p : ι → ℂ) (T : ℝ) (c ζ : ℂ) : ℂ := cexp (-(2 * ζ * T)) * (-(dslope (blaschke p) c ζ) / blaschke p c)

theorem E_eq (p : ι → ℂ) (T : ℝ) {c : ℂ} (hc : blaschke p c ≠ 0) (k : ι) (hk : p k ≠ c) (hk' : p k + c ≠ 0) :
    E T c (p k) = cexp (c * T) * (1 / (p k + c)) + cexp (-(c * T)) * (1 / (p k - c))
      - cexp (-(c * T)) * (cexp (-(2 * p k * T)) / (p k + c)) - cexp (c * T) * g4 p T c (p k) := by
  have h0 : blaschke p (p k) = 0 := Cvs.Upstream.ModelSpaceKernels.blaschke_self p k
  have hs : p k - c ≠ 0 := sub_ne_zero.2 hk
  unfold E g4
  rw [dslope_of_ne _ hk, slope_def_field, h0]
  field_simp
  ring

/-- **The pairing with `E_c`**: for `Re c > 0` off the points and `|u ± c| ≥ r` on the boundary,
`|Σ_k ā_k E_c(p_k)| ≤ (e^{T Re c}A₁ + e^{−T Re c}A₃ + K_c e^{−2T Re z}(e^{−T Re c} + e^{T Re c}(1 + |B(c)|^{−1}))/r)
(Re G(a))^{1/2}`, `A₁ = ((1 − |B(c̄)|²)/(2 Re c))^{1/2}`, `A₃ = ((|B(c)|^{−2} − 1)/(2 Re c))^{1/2}`. -/
theorem norm_sum_E_le {p : ι → ℂ} {z w : ℂ} (hz : 0 < z.re) (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hpin : ∀ k, Inside z w (p k)) {m : ℝ} (hm0 : 0 < m) (hm : ∀ u, OnBd z w u → m ≤ ‖blaschke p u‖)
    {T : ℝ} (hT : 0 ≤ T) {c : ℂ} (hc : 0 < c.re) (hcp : ∀ k, p k ≠ c) {r : ℝ} (hr : 0 < r)
    (hdist : ∀ u, OnBd z w u → r ≤ ‖u - c‖ ∧ r ≤ ‖u + c‖) (a : ι → ℂ) :
    ‖∑ k, conj (a k) * E T c (p k)‖
      ≤ (Real.exp (c.re * T) * √((1 - ‖blaschke p (conj c)‖ ^ 2) / (2 * c.re))
        + Real.exp (-(c.re * T)) * √((‖blaschke p c‖⁻¹ ^ 2 - 1) / (2 * c.re))
        + (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
          * (Real.exp (-(2 * z.re * T)) / r)
          * (Real.exp (-(c.re * T)) + Real.exp (c.re * T) * (1 + ‖blaschke p c‖⁻¹)))
        * √((gram p a).re) := by
  have hε : ∀ i, z.re ≤ (p i).re := fun i => (hpin i).1.le
  have hp : ∀ i, 0 < (p i).re := fun i => hz.trans_le (hε i)
  set B := blaschke p
  have hBc : B c ≠ 0 := Cvs.Upstream.ExpSumBlaschkeProduct.blaschke_ne_zero hp hc.le fun i h => hcp i h.symm
  have hBc0 : 0 < ‖B c‖ := norm_pos_iff.2 hBc
  set Kc := (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
  set G := √((gram p a).re)
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hk' : ∀ k, p k + c ≠ 0 := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [hp k]
  -- the four sums
  have hS1 := Cvs.Upstream.ModelSpaceKernels.norm_sum_div_add_le hz hε a (μ := conj c) (by rw [Complex.conj_re]; exact hc)
  rw [Complex.conj_conj, Complex.conj_re] at hS1
  have hS2 := Cvs.Upstream.ModelSpaceKernels.norm_sum_div_sub_le hz hε a hc hBc
  have hUre : closedRect z w ⊆ {s : ℂ | -c.re < s.re} := by
    intro u hu
    have := hu.1
    rw [Set.mem_preimage, Set.uIcc_of_le hre] at this
    show -c.re < u.re
    linarith [this.1]
  have hbd_re : ∀ u, OnBd z w u → z.re ≤ u.re := fun u hu => by
    have := hu.1.1
    rw [Set.mem_preimage, Set.uIcc_of_le hre] at this
    exact this.1
  have hexp_bd : ∀ u, OnBd z w u → ‖cexp (-(2 * u * T))‖ ≤ Real.exp (-(2 * z.re * T)) := fun u hu => by
    rw [Complex.norm_exp]
    have : (-(2 * u * (T : ℂ))).re = -(2 * u.re * T) := by simp
    rw [this]
    exact Real.exp_le_exp.2 (by nlinarith [hbd_re u hu])
  have hS3 := Cvs.Upstream.ExpSumContourInterpolation.norm_sum_conj_mul_le (a := a) hz hre him hpin hm0 hm
    (isOpen_lt continuous_const Complex.continuous_re) hUre
    (g := fun ζ => cexp (-(2 * ζ * T)) / (ζ + c)) (M := Real.exp (-(2 * z.re * T)) / r)
    (by
      intro ζ hζ
      simp only [mem_ofPred_eq] at hζ
      have hne : ζ + c ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
      exact ((by fun_prop : DifferentiableAt ℂ (fun ζ : ℂ => cexp (-(2 * ζ * T))) ζ).div
        (by fun_prop) hne).differentiableWithinAt)
    (fun u hu => by
      rw [norm_div]
      exact div_le_div₀ (Real.exp_pos _).le (hexp_bd u hu) hr (hdist u hu).2)
  -- the dslope term
  set ε' := min z.re c.re
  have hε' : 0 < ε' := lt_min hz hc
  have hU4 : IsOpen {s : ℂ | -ε' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU4r : closedRect z w ⊆ {s : ℂ | -ε' < s.re} := by
    intro u hu
    have := hu.1
    rw [Set.mem_preimage, Set.uIcc_of_le hre] at this
    show -ε' < u.re
    linarith [this.1, min_le_left z.re c.re]
  have hBd : DifferentiableOn ℂ B {s : ℂ | -ε' < s.re} :=
    (Cvs.Upstream.ModelSpaceKernels.differentiableOn_blaschke (ε := z.re) hε).mono fun s hs => by
      simp only [mem_ofPred_eq] at hs ⊢; linarith [min_le_left z.re c.re]
  have hcU : c ∈ {s : ℂ | -ε' < s.re} := by
    simp only [mem_ofPred_eq]; linarith [min_le_right z.re c.re]
  have hS4 := Cvs.Upstream.ExpSumContourInterpolation.norm_sum_conj_mul_le (a := a) hz hre him hpin hm0 hm hU4 hU4r
    (g := g4 p T c) (M := Real.exp (-(2 * z.re * T)) / r * (1 + ‖B c‖⁻¹))
    (by
      have hds := (differentiableOn_dslope (hU4.mem_nhds hcU)).2 hBd
      exact (DifferentiableOn.mul (fun ζ _ => (by fun_prop : DifferentiableAt ℂ
        (fun ζ : ℂ => cexp (-(2 * ζ * T))) ζ).differentiableWithinAt) (hds.neg.div_const _)))
    (fun u hu => by
      have hu0 : 0 ≤ u.re := hz.le.trans (hbd_re u hu)
      have hne : u ≠ c := fun h => by have := (hdist u hu).1; rw [h, sub_self, norm_zero] at this; linarith
      unfold g4
      rw [dslope_of_ne _ hne, slope_def_field, norm_mul, norm_div, norm_neg, norm_div]
      have hn : ‖B u - B c‖ ≤ 1 + ‖B c‖ :=
        (norm_sub_le _ _).trans (by linarith [Cvs.Upstream.ModelSpaceKernels.norm_blaschke_le_one hp hu0])
      have hq : ‖B u - B c‖ / ‖u - c‖ / ‖B c‖ ≤ (1 + ‖B c‖⁻¹) / r := by
        have h1 := (hdist u hu).1
        rw [div_div, div_le_div_iff₀ (mul_pos (hr.trans_le h1) hBc0) hr]
        calc ‖B u - B c‖ * r ≤ (1 + ‖B c‖) * ‖u - c‖ :=
              mul_le_mul hn h1 hr.le (by positivity)
          _ = (1 + ‖B c‖⁻¹) * (‖u - c‖ * ‖B c‖) := by field_simp; ring
      calc ‖cexp (-(2 * u * T))‖ * (‖B u - B c‖ / ‖u - c‖ / ‖B c‖)
          ≤ Real.exp (-(2 * z.re * T)) * ((1 + ‖B c‖⁻¹) / r) :=
            mul_le_mul (hexp_bd u hu) hq (by positivity) (Real.exp_pos _).le
        _ = Real.exp (-(2 * z.re * T)) / r * (1 + ‖B c‖⁻¹) := by ring)
  -- assemble
  have hsum : ∑ k, conj (a k) * E T c (p k)
      = cexp (c * T) * ∑ k, conj (a k) * (1 / (p k + c)) + cexp (-(c * T)) * ∑ k, conj (a k) * (1 / (p k - c))
        - cexp (-(c * T)) * ∑ k, conj (a k) * (cexp (-(2 * p k * T)) / (p k + c))
        - cexp (c * T) * ∑ k, conj (a k) * g4 p T c (p k) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [E_eq p T hBc k (hcp k) (hk' k)]
    ring
  have he1 : ‖cexp (c * T)‖ = Real.exp (c.re * T) := by rw [Complex.norm_exp]; simp
  have he2 : ‖cexp (-(c * T))‖ = Real.exp (-(c.re * T)) := by rw [Complex.norm_exp]; simp
  rw [hsum]
  set X1 := cexp (c * T) * ∑ k, conj (a k) * (1 / (p k + c))
  set X2 := cexp (-(c * T)) * ∑ k, conj (a k) * (1 / (p k - c))
  set X3 := cexp (-(c * T)) * ∑ k, conj (a k) * (cexp (-(2 * p k * T)) / (p k + c))
  set X4 := cexp (c * T) * ∑ k, conj (a k) * g4 p T c (p k)
  have t1 := norm_sub_le (X1 + X2 - X3) X4
  have t2 := norm_sub_le (X1 + X2) X3
  have t3 := norm_add_le X1 X2
  have n1 : ‖X1‖ = Real.exp (c.re * T) * ‖∑ k, conj (a k) * (1 / (p k + c))‖ := by rw [norm_mul, he1]
  have n2 : ‖X2‖ = Real.exp (-(c.re * T)) * ‖∑ k, conj (a k) * (1 / (p k - c))‖ := by rw [norm_mul, he2]
  have n3 : ‖X3‖ = Real.exp (-(c.re * T)) * ‖∑ k, conj (a k) * (cexp (-(2 * p k * T)) / (p k + c))‖ := by
    rw [norm_mul, he2]
  have n4 : ‖X4‖ = Real.exp (c.re * T) * ‖∑ k, conj (a k) * g4 p T c (p k)‖ := by rw [norm_mul, he1]
  have e1 := mul_le_mul_of_nonneg_left hS1 (Real.exp_pos (c.re * T)).le
  have e2 := mul_le_mul_of_nonneg_left hS2 (Real.exp_pos (-(c.re * T))).le
  have e3 := mul_le_mul_of_nonneg_left hS3 (Real.exp_pos (-(c.re * T))).le
  have e4 := mul_le_mul_of_nonneg_left hS4 (Real.exp_pos (c.re * T)).le
  have key : (Real.exp (c.re * T) * √((1 - ‖blaschke p (conj c)‖ ^ 2) / (2 * c.re))
        + Real.exp (-(c.re * T)) * √((‖blaschke p c‖⁻¹ ^ 2 - 1) / (2 * c.re))
        + Kc * (Real.exp (-(2 * z.re * T)) / r)
          * (Real.exp (-(c.re * T)) + Real.exp (c.re * T) * (1 + ‖blaschke p c‖⁻¹)))
        * √((gram p a).re)
      = Real.exp (c.re * T) * (√((gram p a).re) * √((1 - ‖blaschke p (conj c)‖ ^ 2) / (2 * c.re)))
        + Real.exp (-(c.re * T)) * (√((gram p a).re) * √((‖blaschke p c‖⁻¹ ^ 2 - 1) / (2 * c.re)))
        + Real.exp (-(c.re * T)) * (Kc * (Real.exp (-(2 * z.re * T)) / r) * √((gram p a).re))
        + Real.exp (c.re * T) * (Kc * (Real.exp (-(2 * z.re * T)) / r * (1 + ‖B c‖⁻¹)) * √((gram p a).re)) := by
    ring
  rw [key]
  linarith

open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)
open Cvs.StepA.Edge.DeepPointBlaschkeCount (deepPts)
open Cvs.StepA.Edge.FiniteTopCorrectedClosing (USpan)

/-- The per-zero constant `K_ρ = ½(e^{δT}((1 − β²)/(2δ))^{1/2} + e^{−δT}((β^{−2} − 1)/(2δ))^{1/2}
+ K_c ε_r (e^{−δT} + e^{δT}(1 + β^{−1})))`. -/
def kRho (T δ β Kc εr : ℝ) : ℝ :=
  1 / 2 * (Real.exp (δ * T) * √((1 - β ^ 2) / (2 * δ)) + Real.exp (-(δ * T)) * √((β⁻¹ ^ 2 - 1) / (2 * δ))
    + Kc * εr * (Real.exp (-(δ * T)) + Real.exp (δ * T) * (1 + β⁻¹)))

theorem blaschke_deepPts_conj (δD H : ℝ) (z : ℂ) :
    blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) (conj z) = conj (blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) z) := by
  have h : ∀ u, blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) u = Cvs.Upstream.PointInterpolationHardyDatum.bS (deepPts δD H) u := fun u => by
    unfold blaschke Cvs.Upstream.PointInterpolationHardyDatum.bS
    exact Finset.prod_coe_sort (deepPts δD H) (fun ζ => Cvs.Upstream.ExpSumBlaschkeProduct.bfac ζ u)
  rw [h, h, Cvs.Upstream.PointInterpolationHardyDatum.bS_conj (fun ζ hζ => Cvs.StepA.Edge.DeepPointBlaschkeCount.conj_mem_deepPts hζ)]

/-- **The projection of a high deep `U_ρ` on the deep span** (caseinf-W Theorem C (ii)–(iv)): for `ρ` off the
line above `H` with `|u ± w_ρ|, |u ± w̄_ρ| ≥ r` on the boundary, `‖P_{U_D}U_ρ‖ ≤ 2^{1/2}K_ρ/(1 − q)`. -/
theorem norm_proj_le {x : ℕ} (hx0 : (0 : ℝ) < x) {δD H : ℝ} {z w : ℂ} (hz : 0 < z.re)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hin : ∀ ζ ∈ deepPts δD H, Inside z w ζ) {m : ℝ} (hm0 : 0 < m)
    (hm : ∀ u, OnBd z w u → m ≤ ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) u‖)
    (hq : (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
      * (2 * Real.exp (-(z.re * (Real.log x / 2))) / √(2 * z.re)) < 1)
    {ρ : nonTrivialZeroSet} (hρδ : Cvs.GaussKernel.del ρ ≠ 0) (hρH : H < |(ρ : ℂ).im|) {r : ℝ} (hr : 0 < r)
    (hdist : ∀ u, OnBd z w u → (r ≤ ‖u - wR ρ‖ ∧ r ≤ ‖u + wR ρ‖)
      ∧ (r ≤ ‖u - conj (wR ρ)‖ ∧ r ≤ ‖u + conj (wR ρ)‖)) :
    ‖(USpan hx0 (deepSet δD H)).starProjection (Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖
      ≤ √2 * kRho (Real.log x / 2) |Cvs.GaussKernel.del ρ| ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) (wR ρ)‖
          ((2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re)))
          (Real.exp (-(2 * z.re * (Real.log x / 2))) / r)
        / (1 - (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
          * (2 * Real.exp (-(z.re * (Real.log x / 2))) / √(2 * z.re))) := by
  classical
  set Λ := deepPts δD H
  set T : ℝ := Real.log x / 2 with hT
  have hT0 : 0 ≤ T := by have := Real.log_natCast_nonneg x; positivity
  set α := wR ρ with hα
  set U := Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)
  set p : Λ → ℂ := fun ζ => (ζ : ℂ) with hp
  set B := blaschke p
  set δ := |Cvs.GaussKernel.del ρ| with hδdef
  have hαre : α.re = δ := Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re ρ
  have hδ0 : 0 < δ := abs_pos.2 hρδ
  have hαim : |α.im| = |(ρ : ℂ).im| := Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im ρ
  have hpim : ∀ k, |(p k).im| ≤ H := fun k => by
    obtain ⟨_, _, _, _, _, h⟩ := Cvs.StepA.Edge.DeepPointBlaschkeCount.deepPts_facts k.2; exact h
  have hpα : ∀ k, p k ≠ α := fun k h => by
    have := hpim k; rw [h, hαim] at this; linarith
  have hpαb : ∀ k, p k ≠ conj α := fun k h => by
    have := hpim k; rw [h, Complex.conj_im, abs_neg, hαim] at this; linarith
  have hpin : ∀ k, Inside z w (p k) := fun k => hin k.1 k.2
  have hBconj : ‖B (conj α)‖ = ‖B α‖ := by
    show ‖blaschke (fun ζ : deepPts δD H => (ζ : ℂ)) (conj α)‖ = _
    rw [blaschke_deepPts_conj, Complex.norm_conj]
  set Kc := (2 * (w.re - z.re) + 2 * (w.im - z.im)) / (2 * Real.pi * m * √(2 * z.re))
  set εr := Real.exp (-(2 * z.re * T)) / r
  set K := kRho T δ ‖B α‖ Kc εr with hK
  -- the data
  set f : ℂ → ℂ := fun ζ => cexp (-(ζ * (T : ℂ))) * coshT x (emb x U) ζ with hf
  have hfconj : ∀ ζ ∈ Λ, f (conj ζ) = conj (f ζ) := fun ζ _ => by
    simp only [hf]
    rw [Cvs.StepA.Edge.WindowCoshTransformDuality.coshT_conj, map_mul, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal]
  have hfpt : ∀ k, f (p k) = (E T α (p k) + E T (conj α) (p k)) / 4 := fun k => by
    simp only [hf]
    exact Cvs.StepA.Edge.ZeroVectorTransformSplit.exp_mul_coshT_ueVec hx0 ρ ((hpim k).trans_lt hρH)
  have hb1 := fun a => norm_sum_E_le (a := a) hz hre him hpin hm0 hm hT0 (by rw [hαre]; exact hδ0) hpα hr
    (fun u hu => (hdist u hu).1)
  have hb2 := fun a => norm_sum_E_le (a := a) hz hre him hpin hm0 hm hT0
    (by rw [Complex.conj_re, hαre]; exact hδ0) hpαb hr (fun u hu => (hdist u hu).2)
  have hBc : ‖B (conj α)‖ = ‖B α‖ := hBconj
  have hK0 : 0 ≤ K := by
    rw [hK, kRho]
    have h1 : 0 ≤ Kc := by
      refine div_nonneg (by nlinarith) ?_
      have := Real.pi_pos; have := Real.sqrt_nonneg (2 * z.re); positivity
    positivity
  have hpair : ∀ a : Λ → ℂ, ‖∑ k, conj (a k) * f k‖ ≤ K * √((gram p a).re) := by
    intro a
    have e : ∑ k, conj (a k) * f k
        = (∑ k, conj (a k) * E T α (p k) + ∑ k, conj (a k) * E T (conj α) (p k)) / 4 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show f k = f (p k) from rfl, hfpt k]; ring
    rw [e, norm_div, Complex.norm_ofNat]
    have h1 := hb1 a
    have h2 := hb2 a
    rw [Complex.conj_conj, Complex.conj_re, hαre] at h2
    rw [hαre] at h1
    rw [hBc] at h2
    rw [hBc] at h1
    have h3 : ‖∑ k, conj (a k) * E T α (p k) + ∑ k, conj (a k) * E T (conj α) (p k)‖ ≤ 4 * (K * √((gram p a).re)) := by
      refine (norm_add_le _ _).trans ?_
      have : 4 * (K * √((gram p a).re))
          = (Real.exp (δ * T) * √((1 - ‖B α‖ ^ 2) / (2 * δ))
            + Real.exp (-(δ * T)) * √((‖B α‖⁻¹ ^ 2 - 1) / (2 * δ))
            + Kc * (Real.exp (-(2 * z.re * T)) / r)
              * (Real.exp (-(δ * T)) + Real.exp (δ * T) * (1 + ‖B α‖⁻¹))) * √((gram p a).re)
          + (Real.exp (δ * T) * √((1 - ‖B α‖ ^ 2) / (2 * δ))
            + Real.exp (-(δ * T)) * √((‖B α‖⁻¹ ^ 2 - 1) / (2 * δ))
            + Kc * (Real.exp (-(2 * z.re * T)) / r)
              * (Real.exp (-(δ * T)) + Real.exp (δ * T) * (1 + ‖B α‖⁻¹))) * √((gram p a).re) := by
        rw [hK, kRho]; ring
      rw [this]
      exact add_le_add h1 h2
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  obtain ⟨v, hv, hvn⟩ := Cvs.StepA.Edge.GramPairingInterpolation.exists_window (x := x) (fun ζ hζ => Cvs.StepA.Edge.DeepPointBlaschkeCount.conj_mem_deepPts hζ) hz hre him hin
    hm0 hm hq f hfconj hK0 hpair
  refine (Cvs.StepA.Edge.WindowCoshTransformDuality.norm_proj_USpan_le hx0 U v fun ρ' hρ' => ?_).trans hvn
  have hmem : wR ρ' ∈ Λ := Finset.mem_image.2 ⟨ρ', hρ', rfl⟩
  have h1 := hv (wR ρ') hmem
  have h2 : cexp (wR ρ' * (T : ℂ)) * f (wR ρ') = coshT x (emb x U) (wR ρ') := by
    simp only [hf]
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  rw [h1, h2, ← Cvs.StepA.Edge.WindowCoshTransformDuality.inner_emb_ueVec_eq_re hx0 (emb x U) ρ', LinearIsometry.inner_map_map]

end Cvs.StepA.Edge.HighDeepProjection

end
