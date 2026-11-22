import Mathlib
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
# The virial identity of the finite cosine transform: the edge value is the scale derivative

For `ψ_c g(ξ) = ∫_{−1}^{1} g(s) cos(cξs) ds` the bandwidth is a dilation, `c ∂_c ψ_c g = ξ ∂_ξ ψ_c g`. On an even
`C¹` eigenfunction (`ψ_c g = μg` on `[−1, 1]`) integrating by parts against `g` leaves only the edge:
`∫ g · ∂_c ψ_c g = (μ/c)(g(1)² − ½∫g²)`, on a rung `(μ/c)(g(1)² − ½)`. The endpoint value is the expectation of the
scale generator: the fixed-vector form of Slepian's `d log λ/dc = 2ψ(1)²/c`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open scoped Interval

namespace Cvs.Prolate.CosineTransformVirial

open Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.EvenRungsByIndex

/-- **The transform in the frequency variable**: `∂_ξ ψ_c g = ∫ g(s)(−cs sin(cξs)) ds`. -/
theorem hasDerivAt_psi_freq {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1)) (c ξ : ℝ) :
    HasDerivAt (psi c g) (kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ) ξ := by
  apply hasDerivAt_kint (C := |c|) hg (fun s => by fun_prop) (fun ξ => by fun_prop) (fun ξ => by fun_prop)
  · intro ξ s
    have := ((hasDerivAt_id ξ).const_mul c |>.mul_const s).cos
    refine this.congr_deriv ?_; simp; ring
  · intro ξ s hs
    rw [abs_neg, abs_mul, abs_mul]
    calc |c| * |s| * |sin (c * ξ * s)| ≤ |c| * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg c)) (abs_sin_le_one _) (abs_nonneg _) (by positivity)
      _ = |c| := by ring

/-- **The transform in the bandwidth**: `∂_c ψ_c g(ξ) = ∫ g(s)(−ξs sin(cξs)) ds`. -/
theorem hasDerivAt_psi_band {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1)) (c ξ : ℝ) :
    HasDerivAt (fun c => psi c g ξ) (kint g (fun c s => -(ξ * s * sin (c * ξ * s))) c) c := by
  have heq : (fun c => psi c g ξ) = kint g (fun c s => cos (c * ξ * s)) := by
    funext c; simp only [psi, kint]
  rw [heq]
  apply hasDerivAt_kint (C := |ξ|) hg (fun s => by fun_prop) (fun c => by fun_prop) (fun c => by fun_prop)
  · intro c s
    have := ((hasDerivAt_id c).mul_const ξ |>.mul_const s).cos
    refine this.congr_deriv ?_; simp; ring
  · intro c s hs
    rw [abs_neg, abs_mul, abs_mul]
    calc |ξ| * |s| * |sin (c * ξ * s)| ≤ |ξ| * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg ξ)) (abs_sin_le_one _) (abs_nonneg _) (by positivity)
      _ = |ξ| := by ring

/-- **The bandwidth is a dilation**: `c ∂_c ψ_c g(ξ) = ξ ∂_ξ ψ_c g(ξ)`, kernel by kernel. -/
theorem scale_generator (g : ℝ → ℝ) (c ξ : ℝ) :
    c * kint g (fun c s => -(ξ * s * sin (c * ξ * s))) c
      = ξ * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ := by
  unfold kint
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  congr 1; funext s; ring

/-- `∫_{−1}^{1} ξ g g′ = g(1)² − ½∫g²` for `g(−1) = g(1)`. -/
theorem integral_mul_self_deriv {g g₁ : ℝ → ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁c : ContinuousOn g₁ (uIcc (-1) 1)) (heven : g (-1) = g 1) :
    ∫ ξ in (-1 : ℝ)..1, ξ * g ξ * g₁ ξ = g 1 ^ 2 - (1 / 2) * ∫ ξ in (-1 : ℝ)..1, g ξ ^ 2 := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hF : ∀ x ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun x => x * g x ^ 2 / 2) (g x ^ 2 / 2 + x * g x * g₁ x) x := by
    intro x hx
    have := ((hasDerivAt_id x).mul ((hg x hx).pow 2)).div_const 2
    refine this.congr_deriv ?_; simp; ring
  have hi1 : IntervalIntegrable (fun x => g x ^ 2 / 2) volume (-1) 1 :=
    ((hgc.pow 2).div_const 2).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => x * g x * g₁ x) volume (-1) 1 :=
    ((continuousOn_id.mul hgc).mul hg₁c).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_div, heven] at hFTC
  linarith

/-- **The virial identity**: for an even `C¹` eigenfunction of the finite cosine transform,
`∫ g · ∂_c ψ_c g = (μ/c)(g(1)² − ½∫g²)`. -/
theorem virial {g g₁ : ℝ → ℝ} {c μ : ℝ} (hc : c ≠ 0)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁c : ContinuousOn g₁ (uIcc (-1) 1))
    (heven : g (-1) = g 1) (heig : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) :
    ∫ ξ in (-1 : ℝ)..1, g ξ * kint g (fun c s => -(ξ * s * sin (c * ξ * s))) c
      = μ / c * (g 1 ^ 2 - (1 / 2) * ∫ ξ in (-1 : ℝ)..1, g ξ ^ 2) := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hpt : ∀ ξ ∈ Ioo (-1 : ℝ) 1,
      g ξ * kint g (fun c s => -(ξ * s * sin (c * ξ * s))) c = μ / c * (ξ * g ξ * g₁ ξ) := by
    intro ξ hξ
    have hξI : ξ ∈ uIcc (-1 : ℝ) 1 := by
      rw [uIcc_of_le (by norm_num)]; exact Ioo_subset_Icc_self hξ
    have hev : psi c g =ᶠ[𝓝 ξ] fun s => μ * g s :=
      Filter.eventually_of_mem (Ioo_mem_nhds hξ.1 hξ.2) fun s hs => heig s (Ioo_subset_Icc_self hs)
    have hd2 : HasDerivAt (psi c g) (μ * g₁ ξ) ξ := ((hg ξ hξI).const_mul μ).congr_of_eventuallyEq hev
    have hu := (hasDerivAt_psi_freq hgc c ξ).unique hd2
    have hs := scale_generator g c ξ
    rw [hu] at hs
    have : kint g (fun c s => -(ξ * s * sin (c * ξ * s))) c = ξ * (μ * g₁ ξ) / c := by
      rw [eq_div_iff hc, mul_comm]; exact hs
    rw [this]; field_simp
  have hae : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∈ Ι (-1 : ℝ) 1 →
      g ξ * kint g (fun c s => -(ξ * s * sin (c * ξ * s))) c = μ / c * (ξ * g ξ * g₁ ξ) := by
    have h1 : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ≠ 1 := by
      rw [ae_iff]; simp [measure_singleton]
    filter_upwards [h1] with ξ hξ1 hξ
    rw [uIoc_of_le (by norm_num)] at hξ
    exact hpt ξ ⟨hξ.1, lt_of_le_of_ne hξ.2 hξ1⟩
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    integral_mul_self_deriv hg hg₁c heven]

/-- **The virial identity on a rung**: `∫ rung · ∂_c ψ_c rung = (muR/c)(rung(1)² − ½)`. -/
theorem virial_rung {c : ℝ} {k : ℕ} (hc : c ≠ 0) (h : ∃ χ, IsLevelIdx c k χ) :
    ∫ ξ in (-1 : ℝ)..1, rung c k ξ * kint (rung c k) (fun c s => -(ξ * s * sin (c * ξ * s))) c
      = muR c k / c * (rung c k 1 ^ 2 - 1 / 2) := by
  obtain ⟨hg, hg₁, -, -, heven, hnorm⟩ := rung_spec h
  have hg₁c : ContinuousOn (rung₁ c k) (uIcc (-1) 1) :=
    fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  have hev : rung c k (-1) = rung c k 1 := heven 1 ⟨by norm_num, le_rfl⟩
  rw [virial hc hg hg₁c hev (psi_rung h), hnorm, mul_one]

end Cvs.Prolate.CosineTransformVirial
