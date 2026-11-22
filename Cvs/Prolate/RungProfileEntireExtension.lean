import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SingletonRegularisationColumn
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Route.Visibility.WindowLaplaceUPairing

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The entire extension of the rung profile `G_j = h_{4j} − α_j h₀`

The cosine transform `ψ_g(ζ) = ∫_{−1}^{1} g(u) cos(cζu) du` is entire, so `G_j(ζ) = ψ_{h_{4j}}(ζ)/μ_{4j} −
α_j ψ_{h₀}(ζ)/μ₀` is an entire function of `ζ` that agrees with `h_{4j} − α_j h₀` on `[−1, 1]` and is bounded on
the closed unit disc.
-/

noncomputable section

open Real Set MeasureTheory Complex Metric
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR IsLevelIdx psi_rung continuousOn_rung)

namespace Cvs.Prolate.RungProfileEntireExtension
open Cvs.ZeroCounting

/-- The complex cosine transform `ψ_g(ζ) = ∫_{−1}^{1} g(u) cos(cζu) du`. -/
def psiC (c : ℝ) (g : ℝ → ℝ) (ζ : ℂ) : ℂ := ∫ u in (-1 : ℝ)..1, (g u : ℂ) * Complex.cos (c * ζ * u)

/-- `cos(cζu)` is the mean of the two exponentials `e^{±icζu}`. -/
theorem psiC_eq (c : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1) (ζ : ℂ) :
    psiC c g ζ = ((∫ u in (-1 : ℝ)..1, (g u : ℂ) * Complex.exp (I * c * ζ * u))
      + ∫ u in (-1 : ℝ)..1, (g u : ℂ) * Complex.exp (-(I * c * ζ) * u)) / 2 := by
  have hgc : IntervalIntegrable (fun u => (g u : ℂ)) volume (-1) 1 := ⟨hg.1.ofReal, hg.2.ofReal⟩
  have h1 : IntervalIntegrable (fun u : ℝ => (g u : ℂ) * Complex.exp (I * c * ζ * u)) volume (-1) 1 :=
    hgc.mul_continuousOn (by fun_prop)
  have h2 : IntervalIntegrable (fun u : ℝ => (g u : ℂ) * Complex.exp (-(I * c * ζ) * u)) volume (-1) 1 :=
    hgc.mul_continuousOn (by fun_prop)
  rw [← intervalIntegral.integral_add h1 h2, ← intervalIntegral.integral_div, psiC]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [Complex.cos]
  ring_nf

/-- **The cosine transform of an integrable profile is entire**. -/
theorem differentiable_psiC (c : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-1) 1) :
    Differentiable ℂ (psiC c g) := by
  have hL := Cvs.Route.Visibility.WindowLaplaceUPairing.differentiable_laplace (φ := g) (h := 1) zero_le_one (by simpa using hg)
  have e : psiC c g = fun ζ => ((fun w : ℂ => ∫ t in -1..1, ((g t : ℝ) : ℂ) * Complex.exp (w * t)) (I * c * ζ)
      + (fun w : ℂ => ∫ t in -1..1, ((g t : ℝ) : ℂ) * Complex.exp (w * t)) (-(I * c * ζ))) / 2 := by
    funext ζ; rw [psiC_eq c hg ζ]
  rw [e]
  have hl : Differentiable ℂ fun ζ : ℂ => I * c * ζ := by fun_prop
  exact ((hL.comp hl).add (hL.comp hl.neg)).div_const 2

/-- On the real line `ψ_g` is the real cosine transform `psi c g`. -/
theorem psiC_ofReal (c : ℝ) (g : ℝ → ℝ) (s : ℝ) : psiC c g s = (Cvs.L2a.AngularProlateTailPositive.psi c g s : ℂ) := by
  unfold psiC Cvs.L2a.AngularProlateTailPositive.psi Cvs.Prolate.SlepianCommutingRelation.kint
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only
  push_cast
  ring_nf

/-- **The entire rung profile** `G_j(ζ) = ψ_{h_{4j}}(ζ)/μ_{4j} − α_j ψ_{h₀}(ζ)/μ₀` at `c = 2πx`. -/
def GC (x j : ℕ) (ζ : ℂ) : ℂ :=
  psiC (2 * π * x) (rung (2 * π * x) (2 * j)) ζ / muR (2 * π * x) (2 * j)
    - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * (psiC (2 * π * x) (rung (2 * π * x) 0) ζ / muR (2 * π * x) 0)

/-- A rung is interval integrable on `[−1, 1]`. -/
theorem intervalIntegrable_rung {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) :
    IntervalIntegrable (rung c k) volume (-1) 1 :=
  (continuousOn_rung h).intervalIntegrable_of_Icc (by norm_num)

/-- **`G_j` is entire** for `j < x` at `2πx ≥ 80`. -/
theorem differentiable_GC {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) : Differentiable ℂ (GC x j) := by
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj).1
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero (2 * π * x)
  unfold GC
  exact ((differentiable_psiC _ (intervalIntegrable_rung h1)).div_const _).sub
    (((differentiable_psiC _ (intervalIntegrable_rung h0)).div_const _).const_mul _)

/-- `μ ≠ 0` on a rung with `λ ≥ ½`. -/
theorem muR_ne_zero {c : ℝ} {k : ℕ} (hl : 1 / 2 ≤ lamR c k) : muR c k ≠ 0 := by
  intro h
  rw [Cvs.Prolate.EvenRungsByIndex.lamR, h, zero_mul] at hl
  norm_num at hl

/-- **`G_j` is the real profile on `[−1, 1]`**: `G_j(s) = h_{4j}(s) − α_j h₀(s)`. -/
theorem GC_ofReal {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    GC x j s = ((rung (2 * π * x) (2 * j) s - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 s : ℝ)
      : ℂ) := by
  have h1 := (Cvs.L2a.FullSpanIndexFloor.full_index x hx hj).1
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero (2 * π * x)
  have hm1 := muR_ne_zero (Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hj)
  have hm0 := muR_ne_zero (c := 2 * π * x) (k := 0) (by simpa using Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx (j := 0) (by omega))
  unfold GC
  rw [psiC_ofReal, psiC_ofReal, psi_rung h1 s hs, psi_rung h0 s hs]
  have e1 : ((muR (2 * π * x) (2 * j) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm1
  have e0 : ((muR (2 * π * x) 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm0
  push_cast
  field_simp

/-- **`G_j` is bounded on the closed unit disc**. -/
theorem exists_bound_GC {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    ∃ M : ℝ, ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ‖GC x j ζ‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (differentiable_GC hx hj).continuous.continuousOn
  exact ⟨M, fun ζ hζ => hM ζ (by simpa using hζ)⟩

end Cvs.Prolate.RungProfileEntireExtension

end
