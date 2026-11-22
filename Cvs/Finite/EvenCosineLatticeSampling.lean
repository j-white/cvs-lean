import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Upstream.BandLimitedLatticeSampling

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Lattice sampling of the even cosine transform, and the lattice derivative constant

For `g` even and continuous on `[−1, 1]`, `ψ(ξ) = ∫_{−1}^{1} g(s) cos(cξs) ds` is the band-limited transform
of `g` at `cξ`, so for `cD ≤ π` and every phase `θ`: `∑ₙ ψ(nD + θ)² = (2π/(cD)) ∫_{−1}^{1} g²`. Also
`4 (c³D/2π) ∫ s² sin²(cγs) = 2c³D/(3π) − (c³D/π) ∫ s² cos(2cγs)`, which at `c = L/2` is
`DL³/(12π) − (DL³/8π) ∫ s² cos(Lγs)`, with `∫_{−1}^{1} s² cos(ws) = 2(sin w/w + 2cos w/w² − 2 sin w/w³)`.
-/

noncomputable section

open MeasureTheory Set Complex Real

namespace Cvs.Finite.EvenCosineLatticeSampling

open Cvs.Upstream.BandLimitedLatticeSampling Cvs.L2a.AngularProlateTailPositive

theorem integral_odd_eq_zero {f : ℝ → ℝ} (hf : ∀ s, f (-s) = -f s) : ∫ s in (-1 : ℝ)..1, f s = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) f
  simp only [neg_neg, hf, intervalIntegral.integral_neg] at h
  linarith

/-- **The even cosine transform is the band-limited transform**: `ψ(ξ) = F_g(cξ)` for `g` even. -/
theorem psi_eq_bandT {g : ℝ → ℝ} (heven : ∀ s, g (-s) = g s) (hg : IntervalIntegrable g volume (-1) 1)
    (c ξ : ℝ) : (psi c g ξ : ℂ) = bandT 1 (fun u => (g u : ℂ)) (c * ξ) := by
  have hcos : IntervalIntegrable (fun s => g s * Real.cos (c * ξ * s)) volume (-1) 1 :=
    hg.mul_continuousOn (by fun_prop)
  have hsin : IntervalIntegrable (fun s => g s * Real.sin (c * ξ * s)) volume (-1) 1 :=
    hg.mul_continuousOn (by fun_prop)
  have h0 : ∫ s in (-1 : ℝ)..1, g s * Real.sin (c * ξ * s) = 0 :=
    integral_odd_eq_zero fun s => by rw [heven, mul_neg, Real.sin_neg, mul_neg]
  have hpt : ∀ u : ℝ, (g u : ℂ) * cexp (↑u * ↑(c * ξ) * I)
      = ((g u * Real.cos (c * ξ * u) : ℝ) : ℂ) + ((g u * Real.sin (c * ξ * u) : ℝ) : ℂ) * I := by
    intro u
    rw [show (↑u * ↑(c * ξ) * I : ℂ) = ↑(c * ξ * u) * I by push_cast; ring, Complex.exp_mul_I]
    push_cast
    ring
  unfold bandT
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [hpt]
  have hcosC : IntervalIntegrable (fun s => ((g s * Real.cos (c * ξ * s) : ℝ) : ℂ)) volume (-1) 1 :=
    ⟨Integrable.ofReal hcos.1, Integrable.ofReal hcos.2⟩
  have hsinC : IntervalIntegrable (fun s => ((g s * Real.sin (c * ξ * s) : ℝ) : ℂ)) volume (-1) 1 :=
    ⟨Integrable.ofReal hsin.1, Integrable.ofReal hsin.2⟩
  rw [intervalIntegral.integral_add hcosC (hsinC.mul_const I), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, h0]
  simp [psi, Cvs.Prolate.SlepianCommutingRelation.kint]

theorem memLp_two_of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) :
    MemLp (fun u => (g u : ℂ)) 2 (volume.restrict (Ioc (-1) 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine MemLp.of_bound ((Complex.continuous_ofReal.comp_continuousOn
    (hg.mono Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioc) C ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
  simpa using hC u (Ioc_subset_Icc_self hu)

/-- **Lattice sampling of the even cosine transform**: for `cD ≤ π` and every phase `θ`,
`∑ₙ ψ(nD + θ)² = (2π/(cD)) ∫_{−1}^{1} g²`. -/
theorem hasSum_sq_psi {c D : ℝ} (hc : 0 < c) (hD : 0 < D) (hcD : c * D ≤ π) (θ : ℝ) {g : ℝ → ℝ}
    (heven : ∀ s, g (-s) = g s) (hg : ContinuousOn g (Icc (-1) 1)) :
    HasSum (fun n : ℤ => psi c g (n * D + θ) ^ 2) (2 * π / (c * D) * ∫ s in (-1 : ℝ)..1, g s ^ 2) := by
  have hgi : IntervalIntegrable g volume (-1) 1 :=
    hg.intervalIntegrable_of_Icc (by norm_num)
  have h := hasSum_sq_bandT (a := 1) (D := c * D) (by positivity) (by linarith) (c * θ)
    (memLp_two_of_continuousOn hg)
  have hpt : ∀ n : ℤ, ‖bandT 1 (fun u => (g u : ℂ)) (n * (c * D) + c * θ)‖ ^ 2 = psi c g (n * D + θ) ^ 2 := by
    intro n
    rw [show (n : ℝ) * (c * D) + c * θ = c * (n * D + θ) by ring, ← psi_eq_bandT heven hgi,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hint : ∫ u in Ioc (-1 : ℝ) 1, ‖(g u : ℂ)‖ ^ 2 = ∫ s in (-1 : ℝ)..1, g s ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    congr 1
    funext u
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hpt] at h
  rwa [hint] at h

end Cvs.Finite.EvenCosineLatticeSampling
