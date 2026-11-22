import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.RightEdgeAliasLaw
import Cvs.Prolate.Mellin.RightEdgePoissonSplit
import Cvs.Prolate.Mellin.UnitCircleMellinSolution
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Upstream.TwoConstantsOutsideCircle

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A rung profile and its derivative outside the unit circle

`H_k` has exponential type `c`, is bounded by `M_k = ∫|h_k|/|μ_k|` on `ℝ` and by `|h_k(1)|` on `|t| ≥ 1` (Sonin);
`H_k′` is bounded by `cM_k` on `ℝ` and by `c²|t||h_k(1)|` on `|t| ≥ 1` (the radial equation). Cvs.Upstream.TwoConstantsOutsideCircle then gives
`|H_k(z)| ≤ √(A e(M + A)) e^{c|Im z|}` and `|H_k′(z)| ≤ (|z| + 1)√(c²A e(cM + c²A)) e^{c|Im z|}` for `|z| ≥ 1`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.RungProfileEntireExtension (psiC)
open Cvs.Prolate.EntireRungProlateEquation (Hk)
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR lev IsLevelIdx)
open Cvs.L2a.AngularProlateTailPositive (psi)
open scoped ComplexConjugate

namespace Cvs.Prolate.Mellin.RungProfileOutsideCircle
open Cvs.ZeroCounting

/-- `|cos w| ≤ e^{|Im w|}`. -/
theorem norm_cos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by rw [Complex.norm_exp]; simp
  rw [norm_div, Complex.norm_ofNat]
  have h3 := norm_add_le (Complex.exp (w * I)) (Complex.exp (-w * I))
  have h4 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.2 (neg_le_abs _)
  have h5 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.2 (le_abs_self _)
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- The real-line bound `M_k = ∫|h_k|/|μ_k|`. -/
def Mk (c : ℝ) (k : ℕ) : ℝ := (∫ u in (-1 : ℝ)..1, |rung c k u|) / |muR c k|

theorem Mk_nonneg (c : ℝ) (k : ℕ) : 0 ≤ Mk c k := by
  unfold Mk
  exact div_nonneg (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _) (abs_nonneg _)

/-- `|ψ_g(z)| ≤ (∫|g|) e^{c|Im z|}`. -/
theorem norm_psiC_le {c : ℝ} (hc : 0 ≤ c) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1) (z : ℂ) :
    ‖psiC c g z‖ ≤ (∫ u in (-1 : ℝ)..1, |g u|) * Real.exp (c * |z.im|) := by
  unfold psiC
  have hb : ∀ u ∈ Ioc (-1 : ℝ) 1, ‖(g u : ℂ) * Complex.cos (c * z * u)‖ ≤ |g u| * Real.exp (c * |z.im|) := by
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ((norm_cos_le _).trans (Real.exp_le_exp.2 ?_)) (abs_nonneg _)
    have : ((c : ℂ) * z * u).im = c * u * z.im := by simp; ring
    rw [this, abs_mul, abs_mul, abs_of_nonneg hc]
    have hu1 : |u| ≤ 1 := abs_le.2 ⟨by linarith [hu.1], hu.2⟩
    calc c * |u| * |z.im| ≤ c * 1 * |z.im| := by gcongr
      _ = c * |z.im| := by ring
  refine (intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Eventually.of_forall fun u hu => hb u hu) (hg.abs.mul_const _)).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const]

/-- **Exponential type**: `|H_k(z)| ≤ M_k e^{c|Im z|}`. -/
theorem norm_Hk_le {c : ℝ} (hc : 0 ≤ c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (z : ℂ) :
    ‖Hk c k z‖ ≤ Mk c k * Real.exp (c * |z.im|) := by
  unfold Hk Mk
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (norm_psiC_le hc (Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung h) z) (abs_nonneg _)

/-- On the real line `|H_k(t)| ≤ M_k`. -/
theorem norm_Hk_ofReal_le {c : ℝ} (hc : 0 ≤ c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (t : ℝ) :
    ‖Hk c k t‖ ≤ Mk c k := by
  have := norm_Hk_le hc h t
  simpa using this

/-- `H_k(t) = ψ(t)/μ` at real `t`. -/
theorem Hk_ofReal_eq (c : ℝ) (k : ℕ) (t : ℝ) : Hk c k t = ((psi c (rung c k) t / muR c k : ℝ) : ℂ) := by
  unfold Hk; rw [Cvs.Prolate.RungProfileEntireExtension.psiC_ofReal]; push_cast; rfl

/-- **Sonin outside the band**: `|H_k(t)| ≤ |h_k(1)|` for real `|t| ≥ 1`. -/
theorem norm_Hk_ext_le {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hχ : lev c k < c ^ 2) (hμ : muR c k ≠ 0)
    {t : ℝ} (ht : 1 ≤ |t|) : ‖Hk c k t‖ ≤ |rung c k 1| := by
  rw [Hk_ofReal_eq, Complex.norm_real, Real.norm_eq_abs, abs_div]
  have hμ0 : 0 < |muR c k| := abs_pos.2 hμ
  rw [div_le_iff₀ hμ0]
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht
    have := Cvs.Prolate.Mellin.RightEdgePoissonSplit.abs_psi_rung_le h hχ ht
    linarith
  · rw [abs_of_nonpos h0] at ht
    have := Cvs.Prolate.Mellin.RightEdgePoissonSplit.abs_psi_rung_le h hχ ht
    rw [Cvs.Prolate.RungSpanBernsteinNikolskii.psi_neg] at this
    linarith

/-- `H_k(z̄) = conj H_k(z)`. -/
theorem Hk_conj (c : ℝ) (k : ℕ) (z : ℂ) : Hk c k (conj z) = conj (Hk c k z) := by
  unfold Hk; rw [Cvs.Prolate.Mellin.RightEdgeAliasLaw.psiC_conj, map_div₀, Complex.conj_ofReal]

theorem norm_Hk_conj (c : ℝ) (k : ℕ) (z : ℂ) : ‖Hk c k (conj z)‖ = ‖Hk c k z‖ := by
  rw [Hk_conj, Complex.norm_conj]

/-- `|H_k(z)| ≤ √(A e(M + A)) e^{c|Im z|}` for `|z| ≥ 1`, `A = |h_k(1)|`. -/
theorem norm_Hk_outside {c : ℝ} (hc : 0 ≤ c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hχ : lev c k < c ^ 2)
    (hμ : muR c k ≠ 0) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖Hk c k z‖ ≤ √(|rung c k 1| * (Real.exp 1 * (Mk c k + |rung c k 1|))) * Real.exp (c * |z.im|) := by
  have hA0 : 0 < |rung c k 1| := abs_pos.2 (Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero h)
  have hM0 := Mk_nonneg c k
  have hd := (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h).differentiableOn (s := {z : ℂ | -1 < z.im})
  have hM : ∀ w : ℂ, 0 ≤ w.im → ‖Hk c k w‖ ≤ Mk c k * Real.exp (c * w.im) := fun w hw => by
    have := norm_Hk_le hc h w; rwa [abs_of_nonneg hw] at this
  have hA := fun t (ht : 1 ≤ |t|) => norm_Hk_ext_le h hχ hμ ht
  have hB : ∀ t : ℝ, |t| ≤ 1 → ‖Hk c k t‖ ≤ Mk c k + |rung c k 1| := fun t _ =>
    (norm_Hk_ofReal_le hc h t).trans (by linarith)
  rcases le_total 0 z.im with hz0 | hz0
  · rw [abs_of_nonneg hz0]
    exact Cvs.Upstream.TwoConstantsOutsideCircle.norm_le_sqrt_mul hd hM hA hB hA0 (by linarith) hz0 hz
  · rw [← norm_Hk_conj, abs_of_nonpos hz0, show -z.im = (conj z).im by simp]
    exact Cvs.Upstream.TwoConstantsOutsideCircle.norm_le_sqrt_mul hd hM hA hB hA0 (by linarith) (by simp; linarith)
      (by rwa [Complex.norm_conj])

/-! ### The derivative -/

/-- At a real point the complex derivative of `H_k` is `ψ′(t)/μ`. -/
theorem deriv_Hk_ofReal {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (t : ℝ) :
    deriv (Hk c k) t = ((Cvs.Prolate.RungSpanBernsteinNikolskii.psiD c (rung c k) t / muR c k : ℝ) : ℂ) := by
  have hgc : ContinuousOn (rung c k) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num)]; exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h
  exact Cvs.Prolate.EntireRungProlateEquation.deriv_ofReal_eq (f := fun y => psi c (rung c k) y / muR c k)
    (f₁ := fun y => Cvs.Prolate.RungSpanBernsteinNikolskii.psiD c (rung c k) y / muR c k) (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h) Filter.univ_mem
    (fun y _ => Hk_ofReal_eq c k y) ((Cvs.Prolate.RungSpanBernsteinNikolskii.hasDerivAt_psi' hgc t).div_const _)

/-- `|ψ′(t)| ≤ c∫|g|`. -/
theorem abs_psiD_le {c : ℝ} (hc : 0 ≤ c) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1) (t : ℝ) :
    |Cvs.Prolate.RungSpanBernsteinNikolskii.psiD c g t| ≤ c * ∫ u in (-1 : ℝ)..1, |g u| := by
  unfold Cvs.Prolate.RungSpanBernsteinNikolskii.psiD Cvs.Prolate.SlepianCommutingRelation.kint
  rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Eventually.of_forall fun u (hu : u ∈ Ioc (-1 : ℝ) 1) => ?_) (hg.abs.const_mul _)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_of_nonneg hc]
  have hu1 : |u| ≤ 1 := abs_le.2 ⟨by linarith [hu.1], hu.2⟩
  have hs := Real.abs_sin_le_one (c * t * u)
  calc |g u| * (c * |u| * |Real.sin (c * t * u)|) ≤ |g u| * (c * 1 * 1) := by gcongr
    _ = c * |g u| := by ring

/-- On the real line `|H_k′(t)| ≤ cM_k`. -/
theorem norm_deriv_Hk_ofReal_le {c : ℝ} (hc : 0 ≤ c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (t : ℝ) :
    ‖deriv (Hk c k) t‖ ≤ c * Mk c k := by
  rw [deriv_Hk_ofReal h, Complex.norm_real, Real.norm_eq_abs, abs_div]
  unfold Mk
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (abs_psiD_le hc (Cvs.Prolate.RungProfileEntireExtension.intervalIntegrable_rung h) t) (abs_nonneg _)

/-- **The radial equation outside the band**: `|ψ′(ξ)| ≤ c²ξ|ψ(1)|` for `ξ ≥ 1`, `|χ| ≤ c²`, `χ < c²`. -/
theorem abs_psiD_ext_le {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hχ : lev c k < c ^ 2)
    (hχ' : |lev c k| ≤ c ^ 2) {ξ : ℝ} (hξ : 1 ≤ ξ) :
    |Cvs.Prolate.RungSpanBernsteinNikolskii.psiD c (rung c k) ξ| ≤ c ^ 2 * ξ * (|muR c k| * |rung c k 1|) := by
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
  obtain ⟨hψ, hv, hode⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  set χ := lev c k
  set ψ := psi c (rung c k) with hψd
  set v : ℝ → ℝ := Cvs.Prolate.RungSpanBernsteinNikolskii.psiD c (rung c k) with hvd
  set v' : ℝ → ℝ := Cvs.Prolate.SlepianCommutingRelation.kint (rung c k) (fun ξ s => -(c ^ 2 * s ^ 2 * Real.cos (c * ξ * s))) with hv'd
  have hS : ∀ r, 1 ≤ r → |ψ r| ≤ |muR c k| * |rung c k 1| := fun r hr => Cvs.Prolate.Mellin.RightEdgePoissonSplit.abs_psi_rung_le h hχ hr
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hP : 0 ≤ |muR c k| * |rung c k 1| := by positivity
  rcases eq_or_lt_of_le hξ with he | hlt
  · subst he
    have h1 : (1 ^ 2 - 1) * v' 1 + 2 * 1 * v 1 + (c ^ 2 * 1 ^ 2 - χ) * ψ 1 = 0 := hode 1
    have hv1 : v 1 = -((c ^ 2 - χ) * ψ 1) / 2 := by
      norm_num at h1
      linarith
    rw [hv1, abs_div, abs_neg, abs_mul, abs_two]
    have hd : |c ^ 2 - χ| ≤ 2 * c ^ 2 := by
      rw [abs_le]; constructor <;> linarith [abs_le.1 hχ']
    have := hS 1 le_rfl
    calc |c ^ 2 - χ| * |ψ 1| / 2 ≤ 2 * c ^ 2 * (|muR c k| * |rung c k 1|) / 2 := by gcongr
      _ = c ^ 2 * 1 * (|muR c k| * |rung c k 1|) := by ring
  · -- `u = (ξ² − 1)ψ′` vanishes at `1` and has derivative `−(c²ξ² − χ)ψ`
    set u : ℝ → ℝ := fun r => (r ^ 2 - 1) * v r with hud
    have hu' : ∀ r, HasDerivAt u (-((c ^ 2 * r ^ 2 - χ) * ψ r)) r := fun r => by
      have h2 := (((hasDerivAt_pow 2 r).sub_const 1).mul (hv r))
      have h3 : (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0 := hode r
      have hvv : v r = Cvs.Prolate.SlepianCommutingRelation.kint (rung c k) (fun ξ s => -(c * s * Real.sin (c * ξ * s))) r := rfl
      refine h2.congr_deriv ?_
      rw [← hvv]
      norm_num
      linarith
    obtain ⟨η, hη, hmv⟩ := exists_hasDerivAt_eq_slope u (fun r => -((c ^ 2 * r ^ 2 - χ) * ψ r)) hlt
      (fun r _ => (hu' r).continuousAt.continuousWithinAt) (fun r _ => hu' r)
    have hu1 : u 1 = 0 := by simp [hud]
    rw [hu1, sub_zero] at hmv
    have hpos : 0 < ξ - 1 := by linarith
    have hux : u ξ = -((c ^ 2 * η ^ 2 - χ) * ψ η) * (ξ - 1) := by
      rw [hmv]; field_simp
    have hq : |c ^ 2 * η ^ 2 - χ| ≤ c ^ 2 * ξ ^ 2 + c ^ 2 := by
      have hη2 : η ^ 2 ≤ ξ ^ 2 := by nlinarith [hη.1, hη.2]
      rw [abs_le]; constructor <;> nlinarith [abs_le.1 hχ']
    have hψη := hS η hη.1.le
    have hp2 : 0 < ξ ^ 2 - 1 := by nlinarith
    have hvx : v ξ = u ξ / (ξ ^ 2 - 1) := by rw [hud]; field_simp
    rw [hvx, hux, abs_div, abs_mul, abs_neg, abs_mul, abs_of_pos hpos, abs_of_pos hp2, div_le_iff₀ hp2]
    calc |c ^ 2 * η ^ 2 - χ| * |ψ η| * (ξ - 1)
        ≤ (c ^ 2 * ξ ^ 2 + c ^ 2) * (|muR c k| * |rung c k 1|) * (ξ - 1) := by gcongr
      _ ≤ c ^ 2 * ξ * (|muR c k| * |rung c k 1|) * (ξ ^ 2 - 1) := by
          have : (c ^ 2 * ξ ^ 2 + c ^ 2) * (ξ - 1) ≤ c ^ 2 * ξ * (ξ ^ 2 - 1) := by
            have : (ξ ^ 2 + 1) * (ξ - 1) ≤ ξ * (ξ ^ 2 - 1) := by nlinarith
            nlinarith
          nlinarith

/-- **`|H_k′(t)| ≤ c²|t||h_k(1)|`** for real `|t| ≥ 1`. -/
theorem norm_deriv_Hk_ext_le {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hχ : lev c k < c ^ 2)
    (hχ' : |lev c k| ≤ c ^ 2) (hμ : muR c k ≠ 0) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖deriv (Hk c k) t‖ ≤ c ^ 2 * |t| * |rung c k 1| := by
  rw [deriv_Hk_ofReal h, Complex.norm_real, Real.norm_eq_abs, abs_div]
  have hμ0 : 0 < |muR c k| := abs_pos.2 hμ
  rw [div_le_iff₀ hμ0]
  have key : |Cvs.Prolate.RungSpanBernsteinNikolskii.psiD c (rung c k) t| ≤ c ^ 2 * |t| * (|muR c k| * |rung c k 1|) := by
    rcases le_total 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at ht ⊢; exact abs_psiD_ext_le h hχ hχ' ht
    · rw [abs_of_nonpos h0] at ht ⊢
      have := abs_psiD_ext_le h hχ hχ' ht
      rwa [Cvs.Prolate.RungSpanBernsteinNikolskii.psiD_neg, abs_neg] at this
  calc |Cvs.Prolate.RungSpanBernsteinNikolskii.psiD c (rung c k) t| ≤ c ^ 2 * |t| * (|muR c k| * |rung c k 1|) := key
    _ = c ^ 2 * |t| * |rung c k 1| * |muR c k| := by ring

/-- `H_k′(z̄) = conj H_k′(z)`. -/
theorem deriv_Hk_conj {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (z : ℂ) :
    deriv (Hk c k) (conj z) = conj (deriv (Hk c k) z) := by
  have hd := ((Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h) z).hasDerivAt.conj_conj
  have e : (conj ∘ Hk c k ∘ conj) = Hk c k := by
    funext w; simp only [Function.comp, Hk_conj, Complex.conj_conj]
  rw [e] at hd
  exact hd.deriv

/-- **Cauchy's estimate**: `|H_k′(z)| ≤ M_k e^c e^{c|Im z|}`. -/
theorem norm_deriv_Hk_le {c : ℝ} (hc : 0 ≤ c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (z : ℂ) :
    ‖deriv (Hk c k) z‖ ≤ Mk c k * Real.exp c * Real.exp (c * |z.im|) := by
  have hd := (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h).diffContOnCl (s := Metric.ball z 1)
  have hb : ∀ w ∈ Metric.sphere z 1, ‖Hk c k w‖ ≤ Mk c k * Real.exp c * Real.exp (c * |z.im|) := by
    intro w hw
    refine (norm_Hk_le hc h w).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    gcongr
    · exact Mk_nonneg c k
    · have h1 : |w.im - z.im| ≤ 1 := by
        have := Complex.abs_im_le_norm (w - z)
        rw [mem_sphere_iff_norm] at hw
        simpa [hw] using this
      have h2 : |w.im| ≤ |z.im| + 1 := by
        have := abs_sub_abs_le_abs_sub w.im z.im; linarith
      nlinarith
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hd hb
  simpa using this

/-- `|H_k′(z)| ≤ (|z| + 1)√(c²A e(cM + c²A)) e^{c|Im z|}` for `|z| ≥ 1`, `A = |h_k(1)|`. -/
theorem norm_deriv_Hk_outside {c : ℝ} (hc : 0 < c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hχ : lev c k < c ^ 2)
    (hχ' : |lev c k| ≤ c ^ 2) (hμ : muR c k ≠ 0) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖deriv (Hk c k) z‖ ≤ (‖z‖ + 1) * √(c ^ 2 * |rung c k 1| * (Real.exp 1 * (c * Mk c k
      + c ^ 2 * |rung c k 1|))) * Real.exp (c * |z.im|) := by
  have hA0 : 0 < c ^ 2 * |rung c k 1| := mul_pos (by positivity) (abs_pos.2 (Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero h))
  have hM0 := Mk_nonneg c k
  have hH := Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h
  set f₁ : ℂ → ℂ := fun w => deriv (Hk c k) w / (w + I) with hf₁
  have hne : ∀ w : ℂ, -1 < w.im → w + I ≠ 0 := fun w hw he => by
    have := congrArg Complex.im he; simp at this; linarith
  have hd : DifferentiableOn ℂ f₁ {w : ℂ | -1 < w.im} := fun w hw =>
    (((Cvs.Prolate.Mellin.UnitCircleMellinSolution.deriv_differentiable hH) w).div (differentiableAt_id.add_const I) (hne w hw)).differentiableWithinAt
  have hnI : ∀ w : ℂ, 0 ≤ w.im → 1 ≤ ‖w + I‖ := fun w hw => by
    have := Complex.abs_im_le_norm (w + I)
    simp only [add_im, I_im] at this
    rw [abs_of_nonneg (by linarith)] at this; linarith
  have hf₁le : ∀ w : ℂ, 0 ≤ w.im → ‖f₁ w‖ ≤ ‖deriv (Hk c k) w‖ := fun w hw => by
    rw [hf₁, norm_div]
    exact div_le_self (norm_nonneg _) (hnI w hw)
  have hM : ∀ w : ℂ, 0 ≤ w.im → ‖f₁ w‖ ≤ Mk c k * Real.exp c * Real.exp (c * w.im) := fun w hw => by
    have := norm_deriv_Hk_le hc.le h w; rw [abs_of_nonneg hw] at this
    exact (hf₁le w hw).trans this
  have hA : ∀ t : ℝ, 1 ≤ |t| → ‖f₁ t‖ ≤ c ^ 2 * |rung c k 1| := fun t ht => by
    rw [hf₁, norm_div]
    have h1 := norm_deriv_Hk_ext_le h hχ hχ' hμ ht
    have h2 : |t| ≤ ‖(t : ℂ) + I‖ := by
      have := Complex.abs_re_le_norm ((t : ℂ) + I); simpa using this
    have h3 : 0 < ‖(t : ℂ) + I‖ := by linarith
    rw [div_le_iff₀ h3]
    calc ‖deriv (Hk c k) t‖ ≤ c ^ 2 * |t| * |rung c k 1| := h1
      _ ≤ c ^ 2 * |rung c k 1| * ‖(t : ℂ) + I‖ := by nlinarith [abs_nonneg (rung c k 1)]
  have hB : ∀ t : ℝ, |t| ≤ 1 → ‖f₁ t‖ ≤ c * Mk c k + c ^ 2 * |rung c k 1| := fun t _ => by
    refine (hf₁le t (by simp)).trans ((norm_deriv_Hk_ofReal_le hc.le h t).trans ?_)
    linarith
  have upper : ∀ w : ℂ, 0 ≤ w.im → 1 ≤ ‖w‖ → ‖deriv (Hk c k) w‖ ≤ (‖w‖ + 1) * √(c ^ 2 * |rung c k 1| *
      (Real.exp 1 * (c * Mk c k + c ^ 2 * |rung c k 1|))) * Real.exp (c * w.im) := by
    intro w hw hw1
    have h1 := Cvs.Upstream.TwoConstantsOutsideCircle.norm_le_sqrt_mul hd hM hA hB hA0 (by nlinarith [mul_nonneg hc.le hM0]) hw hw1
    have hwI : w + I ≠ 0 := hne w (by linarith)
    have e : deriv (Hk c k) w = f₁ w * (w + I) := by rw [hf₁]; field_simp
    rw [e, norm_mul]
    have h2 : ‖w + I‖ ≤ ‖w‖ + 1 := by
      have := norm_add_le w I; rwa [Complex.norm_I] at this
    calc ‖f₁ w‖ * ‖w + I‖ ≤ (√(c ^ 2 * |rung c k 1| * (Real.exp 1 * (c * Mk c k + c ^ 2 * |rung c k 1|)))
          * Real.exp (c * w.im)) * (‖w‖ + 1) := by gcongr
      _ = _ := by ring
  rcases le_total 0 z.im with hz0 | hz0
  · rw [abs_of_nonneg hz0]; exact upper z hz0 hz
  · have h1 := upper (conj z) (by simp; linarith) (by rwa [Complex.norm_conj])
    rw [deriv_Hk_conj h, Complex.norm_conj, Complex.norm_conj] at h1
    rw [abs_of_nonpos hz0]
    simpa using h1

end Cvs.Prolate.Mellin.RungProfileOutsideCircle

end
