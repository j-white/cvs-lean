import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosine transform is real analytic, and the spine profile extends analytically

`ψ(ξ) = ∫_{−1}^{1} g(s) cos(cξs) ds` is the real part of the entire function `z ↦ ∫_{−1}^{1} g(s) cos(czs) ds`, so
it is real analytic on `ℝ`. An even rung is `μ⁻¹ψ` of itself on `[−1, 1]` with `μ > 0`, so every spine profile
`Σ_j a_j(h_{2j} − α_j h₀)` agrees on `[−1, 1]` with the real-analytic `Σ_j a_j(μ_{2j}⁻¹ψ_{2j} − α_j μ₀⁻¹ψ₀)`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology

namespace Cvs.Prolate.CosineTransformAnalytic

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.EvenRungsByIndex (rung muR IsLevelIdx)
open Cvs.Approximant.DeepIndexSpineSpan (spineG alpha)

/-! ### The complex cosine transform -/

/-- The complex cosine transform `z ↦ ∫_{−1}^{1} g(s) cos(czs) ds`. -/
def cosC (c : ℝ) (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ s in (-1 : ℝ)..1, (g s : ℂ) * Complex.cos (c * z * s)

/-- **The complex cosine transform is entire** for `g` integrable on `[−1, 1]`. -/
theorem differentiable_cosC (c : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1) :
    Differentiable ℂ (cosC c g) := by
  intro z₀
  have hK : IsCompact (Metric.closedBall z₀ 1 ×ˢ Icc (-1 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hcont : Continuous (fun p : ℂ × ℝ => -Complex.sin (c * p.1 * p.2) * (c * p.2)) := by fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hgi : IntervalIntegrable (fun s => (g s : ℂ)) volume (-1) 1 := ⟨hg.1.ofReal, hg.2.ofReal⟩
  have hcos : ∀ z : ℂ, Continuous fun s : ℝ => Complex.cos (c * z * s) := fun z => by fun_prop
  have hsin : Continuous fun s : ℝ => -Complex.sin (c * z₀ * s) * (c * s) := by fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -1) (b := 1) (F := fun z s => (g s : ℂ) * Complex.cos (c * z * s))
    (F' := fun z s => (g s : ℂ) * (-Complex.sin (c * z * s) * (c * s))) (x₀ := z₀)
    (bound := fun s => ‖g s‖ * C) (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z =>
      ((hgi.mul_continuousOn (hcos z).continuousOn).def').aestronglyMeasurable)
    (hgi.mul_continuousOn (hcos z₀).continuousOn)
    ((hgi.mul_continuousOn hsin.continuousOn).def').aestronglyMeasurable
    (ae_of_all _ fun s hs z hz => by
      have hs' : s ∈ Icc (-1 : ℝ) 1 := by
        rw [uIoc_of_le (by norm_num)] at hs
        exact ⟨hs.1.le, hs.2⟩
      have hb := hC (z, s) ⟨Metric.ball_subset_closedBall hz, hs'⟩
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    (hg.norm.mul_const C)
    (ae_of_all _ fun s _ z _ => by
      have h := ((Complex.hasDerivAt_cos (c * z * s)).comp z
        (((hasDerivAt_id' z).const_mul (c : ℂ)).mul_const (s : ℂ))).const_mul (g s : ℂ)
      exact h.congr_deriv (by ring))
  exact key.2.differentiableAt

/-- `ψ(ξ)` is the complex cosine transform at the real point `ξ`. -/
theorem cosC_ofReal (c : ℝ) (g : ℝ → ℝ) (ξ : ℝ) : cosC c g ξ = (psi c g ξ : ℂ) := by
  unfold cosC psi Cvs.Prolate.SlepianCommutingRelation.kint
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s _ => ?_
  push_cast
  rfl

/-- **The cosine transform is real analytic** for `g` integrable on `[−1, 1]`. -/
theorem analyticAt_psi (c : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1) (ξ : ℝ) :
    AnalyticAt ℝ (psi c g) ξ := by
  have h : AnalyticAt ℝ (fun t : ℝ => (cosC c g (t : ℂ)).re) ξ :=
    (Complex.reCLM.analyticAt _).comp
      ((((differentiable_cosC c hg).analyticAt (ξ : ℂ)).restrictScalars (𝕜 := ℝ)).comp
        (Complex.ofRealCLM.analyticAt ξ))
  have e : (fun t : ℝ => (cosC c g (t : ℂ)).re) = psi c g := by
    funext t; rw [cosC_ofReal, Complex.ofReal_re]
  rwa [e] at h

/-! ### The analytic extension of the rungs and of the spine profile -/

/-- The analytic extension `μ⁻¹ψ(h)` of the rung `h = rung c k`. -/
def rungExt (c : ℝ) (k : ℕ) (s : ℝ) : ℝ := (muR c k)⁻¹ * psi c (rung c k) s

/-- `rungExt c k` is real analytic. -/
theorem analyticAt_rungExt {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (s : ℝ) :
    AnalyticAt ℝ (rungExt c k) s := by
  have hi : IntervalIntegrable (rung c k) volume (-1) 1 :=
    (Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h).intervalIntegrable_of_Icc (by norm_num)
  exact analyticAt_const.mul (analyticAt_psi c hi s)

/-- **An even rung is its analytic extension on `[−1, 1]`**, for `c > 0`. -/
theorem rung_eq_rungExt {c : ℝ} (hc : 0 < c) {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) (hk : Even k) :
    ∀ s ∈ Icc (-1 : ℝ) 1, rung c k s = rungExt c k s := by
  intro s hs
  have hμ := (Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h hk).ne'
  rw [rungExt, Cvs.Prolate.EvenRungsByIndex.psi_rung h s hs, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]

/-- The analytic extension of the spine profile, `Σ_j a_j(μ_{2j}⁻¹ψ_{2j} − α_j μ₀⁻¹ψ₀)`. -/
def spineExt (c : ℝ) {S : Finset ℕ} (a : S → ℝ) (s : ℝ) : ℝ :=
  ∑ j, a j * (rungExt c (2 * j) s - alpha c j * rungExt c 0 s)

/-- **The spine extension is real analytic** when the levels of index `2j` exist. -/
theorem analyticAt_spineExt {c : ℝ} {S : Finset ℕ} (hex : ∀ j ∈ S, ∃ χ, IsLevelIdx c (2 * j) χ)
    (a : S → ℝ) (s : ℝ) : AnalyticAt ℝ (spineExt c a) s := by
  have h : AnalyticAt ℝ (fun s => ∑ j : S, a j * (rungExt c (2 * j) s - alpha c j * rungExt c 0 s)) s :=
    Finset.analyticAt_fun_sum _ fun (j : S) _ => analyticAt_const.mul ((analyticAt_rungExt (hex j j.2) s).sub
      (analyticAt_const.mul (analyticAt_rungExt (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c) s)))
  exact h

/-- **The spine profile is its analytic extension on `[−1, 1]`**, for `c > 0`. -/
theorem spineG_eq_spineExt {c : ℝ} (hc : 0 < c) {S : Finset ℕ} (hex : ∀ j ∈ S, ∃ χ, IsLevelIdx c (2 * j) χ)
    (a : S → ℝ) : ∀ s ∈ Icc (-1 : ℝ) 1, spineG c a s = spineExt c a s := by
  intro s hs
  show ∑ j : S, a j * (rung c (2 * j) s - alpha c j * rung c 0 s) = _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rung_eq_rungExt hc (hex j j.2) (even_two_mul _) s hs,
    rung_eq_rungExt hc (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c) (even_iff_two_dvd.2 (dvd_zero 2)) s hs]

end Cvs.Prolate.CosineTransformAnalytic
