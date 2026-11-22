import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungParseval
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.ExteriorSeriesBox
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.Route.Visibility.PerRungLogTailLaw
import Cvs.Route.Visibility.RungXBoxExplicit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band-limited extension of a unit rung and its constants

For `G_j = h_{4j} − α_j h₀` put `g̃ = h_{4j}/μ_{4j} − α_j h₀/μ₀` and `ψ = ψ_{g̃}`, the band-limited extension with
`ψ = G_j` on `[−1, 1]`. Then `‖ψ‖²_{L²(1,∞)} ≤ (1 − λ_{4j})/λ_{4j} + α_j²(1 − λ₀)/λ₀ = P̄_j²`,
`∫_ℝ ψ′² ≤ 2c²(1 + α_j²)`,
`|ψ(1)| ≤ √(8x(1 + α_j²))`, and the constant `B = 2(|ψ(1)| + D + P/√3)` has `B/(2c) ≤ 2√(1 + α_j²)` for `c = 2πx ≥ 80`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.EvenRungsByIndex (rung lamR muR)
open Cvs.Prolate.RungSpanBernsteinNikolskii (psiD)

namespace Cvs.Prolate.Mellin.UnitRungBandExtension
open Cvs.ZeroCounting

/-- The source `g̃ = h_{4j}/μ_{4j} − α_j h₀/μ₀` of the extension of the unit rung. -/
def gSrc (c : ℝ) (j : ℕ) (σ : ℝ) : ℝ :=
  rung c (2 * j) σ / muR c (2 * j) - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * (rung c 0 σ / muR c 0)

/-- The data of a unit rung at `c = 2πx ≥ 80`. -/
structure RungData (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : Prop where
  hex : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * (j : ℕ)) χ
  hex0 : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) 0 χ
  hlam : 1 / 2 ≤ lamR (2 * π * x) (2 * (j : ℕ))
  hlam0 : 1 / 2 ≤ lamR (2 * π * x) 0
  hlam1 : lamR (2 * π * x) (2 * (j : ℕ)) ≤ 1
  hlam01 : lamR (2 * π * x) 0 ≤ 1
  hc : 80 ≤ 2 * π * x

theorem rungData {x : ℕ} (hsc : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) : RungData x j := by
  have hjx := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith
  have hex := (Cvs.L2a.FullSpanIndexFloor.full_index x hsc hjx).1
  exact ⟨hex, Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero _, Cvs.L2a.WindowChainInputsProlate.half_le_lamR hsc hjx,
    by simpa using Cvs.L2a.WindowChainInputsProlate.half_le_lamR hsc (lt_of_le_of_lt (Nat.zero_le _) hjx),
    Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 hex, Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc0, hsc⟩

variable {x : ℕ} {j : Cvs.Approximant.SpineSubspace.SF x}

theorem x_pos (D : RungData x j) : (0 : ℝ) < x := by
  have h := D.hc
  by_contra hx
  push Not at hx
  nlinarith [Real.pi_pos]

theorem muR_ne_zero (D : RungData x j) : muR (2 * π * x) (2 * (j : ℕ)) ≠ 0 :=
  Cvs.Prolate.RungSpanBernsteinNikolskii.muR_ne_zero_of_lam (by norm_num : (0 : ℝ) < 1 / 2) D.hlam

theorem muR0_ne_zero (D : RungData x j) : muR (2 * π * x) 0 ≠ 0 :=
  Cvs.Prolate.RungSpanBernsteinNikolskii.muR_ne_zero_of_lam (by norm_num : (0 : ℝ) < 1 / 2) D.hlam0

theorem continuousOn_gSrc (D : RungData x j) : ContinuousOn (gSrc (2 * π * x) j) (uIcc (-1) 1) := by
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  unfold gSrc
  exact ((Cvs.Prolate.EvenRungsByIndex.continuousOn_rung D.hex).div_const _).sub
    (continuousOn_const.mul ((Cvs.Prolate.EvenRungsByIndex.continuousOn_rung D.hex0).div_const _))

theorem gSrc_even (D : RungData x j) : ∀ v ∈ Icc (-1 : ℝ) 1, gSrc (2 * π * x) j (-v) = gSrc (2 * π * x) j v := by
  intro v hv
  unfold gSrc
  rw [(Cvs.Prolate.EvenRungsByIndex.rung_spec D.hex).2.2.2.2.1 v hv, (Cvs.Prolate.EvenRungsByIndex.rung_spec D.hex0).2.2.2.2.1 v hv]

/-- `ψ_{g̃} = μ⁻¹ψ_h − (α/μ₀)ψ_{h₀}` on `ℝ`. -/
theorem psi_gSrc (D : RungData x j) (t : ℝ) :
    psi (2 * π * x) (gSrc (2 * π * x) j) t
      = psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) t / muR (2 * π * x) (2 * (j : ℕ))
        - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * (psi (2 * π * x) (rung (2 * π * x) 0) t / muR (2 * π * x) 0) := by
  have h1 : ContinuousOn (rung (2 * π * x) (2 * (j : ℕ))) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung D.hex
  have h0 : ContinuousOn (rung (2 * π * x) 0) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung D.hex0
  have hk : ContinuousOn (fun s => Real.cos (2 * π * x * t * s)) (uIcc (-1) 1) := by fun_prop
  have hi1 : IntervalIntegrable (fun s => rung (2 * π * x) (2 * (j : ℕ)) s * Real.cos (2 * π * x * t * s)
      / muR (2 * π * x) (2 * (j : ℕ))) volume (-1) 1 := ((h1.mul hk).div_const _).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * (rung (2 * π * x) 0 s
      * Real.cos (2 * π * x * t * s) / muR (2 * π * x) 0)) volume (-1) 1 :=
    (continuousOn_const.mul ((h0.mul hk).div_const _)).intervalIntegrable
  show ∫ s in (-1 : ℝ)..1, gSrc (2 * π * x) j s * Real.cos (2 * π * x * t * s)
      = (∫ s in (-1 : ℝ)..1, rung (2 * π * x) (2 * (j : ℕ)) s * Real.cos (2 * π * x * t * s))
          / muR (2 * π * x) (2 * (j : ℕ))
        - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * ((∫ s in (-1 : ℝ)..1, rung (2 * π * x) 0 s * Real.cos (2 * π * x * t * s))
          / muR (2 * π * x) 0)
  rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hi1 hi2]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [gSrc]
  ring

/-- **The extension agrees with the profile**: `ψ_{g̃} = G_j` on `[−1, 1]`. -/
theorem psi_gSrc_eq (D : RungData x j) :
    ∀ t ∈ Icc (-1 : ℝ) 1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) t = psi (2 * π * x) (gSrc (2 * π * x) j) t := by
  intro t ht
  rw [psi_gSrc D, Cvs.Prolate.EvenRungsByIndex.psi_rung D.hex t ht, Cvs.Prolate.EvenRungsByIndex.psi_rung D.hex0 t ht, Cvs.Route.Visibility.CaseFiniteFromWindowChain.spineG_single]
  field_simp [muR_ne_zero D, muR0_ne_zero D]

/-! ### The exterior mass -/

theorem one_div_muR_sq (D : RungData x j) (k : ℕ) (hl : 1 / 2 ≤ lamR (2 * π * x) k) :
    1 / muR (2 * π * x) k ^ 2 = 2 * π * x / (2 * π) / lamR (2 * π * x) k := by
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith [D.hc]
  have hμ : muR (2 * π * x) k ≠ 0 := Cvs.Prolate.RungSpanBernsteinNikolskii.muR_ne_zero_of_lam (by norm_num : (0 : ℝ) < 1 / 2) hl
  rw [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq hc0]
  have := (x_pos D).ne'
  field_simp

/-- `∫₁^∞ (ψ_h/μ)² = (1 − λ)/(2λ)` for a rung `h` with `λ ≥ ½`. -/
theorem integral_psi_div_sq (D : RungData x j) (k : ℕ) (hk : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) k χ)
    (hl : 1 / 2 ≤ lamR (2 * π * x) k) :
    ∫ t in Ioi (1 : ℝ), (psi (2 * π * x) (rung (2 * π * x) k) t / muR (2 * π * x) k) ^ 2
      = (1 - lamR (2 * π * x) k) / (2 * lamR (2 * π * x) k) := by
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith [D.hc]
  simp only [div_pow]
  rw [integral_div, Cvs.Prolate.Envelope.RungExteriorLaw.mass_eq hc0 hk, div_eq_mul_one_div, one_div_muR_sq D k hl]
  have : 0 < lamR (2 * π * x) k := by linarith
  have := (x_pos D).ne'
  field_simp

theorem integrableOn_psi_sq (D : RungData x j) (k : ℕ) (hk : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) k χ) :
    IntegrableOn (fun t => psi (2 * π * x) (rung (2 * π * x) k) t ^ 2) (Ioi 1) := by
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith [D.hc]
  refine (Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc0 ?_).integrableOn
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung hk

/-- **The exterior mass of the extension**: `∫₁^∞ ψ² ≤ P̄_j²`. -/
theorem integral_psi_gSrc_sq_le (D : RungData x j) :
    IntegrableOn (fun t => psi (2 * π * x) (gSrc (2 * π * x) j) t ^ 2) (Ioi 1)
      ∧ ∫ t in Ioi (1 : ℝ), psi (2 * π * x) (gSrc (2 * π * x) j) t ^ 2 ≤ Cvs.Route.Visibility.RungXBoxExplicit.pBar x j ^ 2 := by
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith [D.hc]
  set A := fun t => psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) t / muR (2 * π * x) (2 * (j : ℕ))
  set Bf := fun t => psi (2 * π * x) (rung (2 * π * x) 0) t / muR (2 * π * x) 0
  set α := Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j
  have iA : IntegrableOn (fun t => A t ^ 2) (Ioi 1) := by
    simp only [A, div_pow]; exact (integrableOn_psi_sq D _ D.hex).div_const _
  have iB : IntegrableOn (fun t => Bf t ^ 2) (Ioi 1) := by
    simp only [Bf, div_pow]; exact (integrableOn_psi_sq D _ D.hex0).div_const _
  have hpt : ∀ t, psi (2 * π * x) (gSrc (2 * π * x) j) t ^ 2 ≤ 2 * A t ^ 2 + 2 * α ^ 2 * Bf t ^ 2 := fun t => by
    rw [psi_gSrc D t]
    nlinarith [sq_nonneg (A t + α * Bf t)]
  have hdom : IntegrableOn (fun t => 2 * A t ^ 2 + 2 * α ^ 2 * Bf t ^ 2) (Ioi 1) :=
    (iA.const_mul 2).add (iB.const_mul (2 * α ^ 2))
  have hm : Measurable fun t => psi (2 * π * x) (gSrc (2 * π * x) j) t ^ 2 :=
    ((Cvs.Prolate.RungSpanBernsteinNikolskii.continuous_psi (continuousOn_gSrc D)).pow 2).measurable
  have hI : IntegrableOn (fun t => psi (2 * π * x) (gSrc (2 * π * x) j) t ^ 2) (Ioi 1) :=
    hdom.mono' hm.aestronglyMeasurable (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt t)
  refine ⟨hI, ?_⟩
  calc ∫ t in Ioi (1 : ℝ), psi (2 * π * x) (gSrc (2 * π * x) j) t ^ 2
      ≤ ∫ t in Ioi (1 : ℝ), (2 * A t ^ 2 + 2 * α ^ 2 * Bf t ^ 2) :=
        setIntegral_mono_on hI hdom measurableSet_Ioi fun t _ => hpt t
    _ = 2 * ((1 - lamR (2 * π * x) (2 * (j : ℕ))) / (2 * lamR (2 * π * x) (2 * (j : ℕ))))
        + 2 * α ^ 2 * ((1 - lamR (2 * π * x) 0) / (2 * lamR (2 * π * x) 0)) := by
        rw [integral_add (iA.const_mul 2) (iB.const_mul _), integral_const_mul, integral_const_mul]
        simp only [A, Bf]
        rw [integral_psi_div_sq D _ D.hex D.hlam, integral_psi_div_sq D _ D.hex0 D.hlam0]
    _ = Cvs.Route.Visibility.RungXBoxExplicit.pBar x j ^ 2 := by
        have h1 : 0 < lamR (2 * π * x) (2 * (j : ℕ)) := by linarith [D.hlam]
        have h2 : 0 < lamR (2 * π * x) 0 := by linarith [D.hlam0]
        rw [Cvs.Route.Visibility.RungXBoxExplicit.pBar, Real.sq_sqrt (by
          have := D.hlam1; have := D.hlam01
          have : 0 ≤ 1 - lamR (2 * π * x) (2 * (j : ℕ)) := by linarith
          have : 0 ≤ 1 - lamR (2 * π * x) 0 := by linarith
          positivity)]
        field_simp
        ring

/-! ### The source norm, the derivative and the edge value -/

theorem integral_rung_mul_rung_zero (D : RungData x j) :
    ∫ s in (-1 : ℝ)..1, rung (2 * π * x) (2 * (j : ℕ)) s * rung (2 * π * x) 0 s = 0 := by
  have hj1 : 1 ≤ (j : ℕ) := (Finset.mem_filter.1 j.2).2
  exact Cvs.Prolate.EvenRungParseval.integral_rung_mul_rung (k := ⟨2 * (j : ℕ), D.hex⟩) (j := ⟨0, D.hex0⟩)
    (fun h => by have h2 : 2 * (j : ℕ) = 0 := congrArg Subtype.val h; omega)

/-- `∫_{−1}^{1} g̃² = μ_{4j}⁻² + α_j²μ₀⁻²`, by orthonormality of the rungs. -/
theorem integral_gSrc_sq (D : RungData x j) :
    ∫ s in (-1 : ℝ)..1, gSrc (2 * π * x) j s ^ 2
      = 1 / muR (2 * π * x) (2 * (j : ℕ)) ^ 2 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 / muR (2 * π * x) 0 ^ 2 := by
  have horth := integral_rung_mul_rung_zero D
  set c := 2 * π * (x : ℝ)
  set h := rung c (2 * (j : ℕ))
  set h0 := rung c 0
  set μ := muR c (2 * (j : ℕ))
  set μ0 := muR c 0
  set α := Cvs.Approximant.DeepIndexSpineSpan.alpha c j
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have c1 : ContinuousOn h (uIcc (-1) 1) := by rw [hI]; exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung D.hex
  have c0 : ContinuousOn h0 (uIcc (-1) 1) := by rw [hI]; exact Cvs.Prolate.EvenRungsByIndex.continuousOn_rung D.hex0
  have n1 := (Cvs.Prolate.EvenRungsByIndex.rung_spec D.hex).2.2.2.2.2
  have n0 := (Cvs.Prolate.EvenRungsByIndex.rung_spec D.hex0).2.2.2.2.2
  have e : ∀ s, gSrc c j s ^ 2 = h s ^ 2 * (1 / μ ^ 2) + (h s * h0 s) * (-2 * α / (μ * μ0))
      + h0 s ^ 2 * (α ^ 2 / μ0 ^ 2) := fun s => by
    unfold gSrc
    ring
  simp only [e]
  have i1 : IntervalIntegrable (fun s => h s ^ 2 * (1 / μ ^ 2)) volume (-1) 1 :=
    ((c1.pow 2).mul continuousOn_const).intervalIntegrable
  have i2 : IntervalIntegrable (fun s => h s * h0 s * (-2 * α / (μ * μ0))) volume (-1) 1 :=
    ((c1.mul c0).mul continuousOn_const).intervalIntegrable
  have i3 : IntervalIntegrable (fun s => h0 s ^ 2 * (α ^ 2 / μ0 ^ 2)) volume (-1) 1 :=
    ((c0.pow 2).mul continuousOn_const).intervalIntegrable
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    n1, n0, horth]
  ring

/-- `∫_{−1}^{1} g̃² ≤ (c/2π)·2(1 + α_j²)`. -/
theorem integral_gSrc_sq_le (D : RungData x j) :
    ∫ s in (-1 : ℝ)..1, gSrc (2 * π * x) j s ^ 2 ≤ 2 * π * x / (2 * π) * (2 * (1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2)) := by
  rw [integral_gSrc_sq D, div_eq_mul_one_div (Cvs.Approximant.DeepIndexSpineSpan.alpha _ _ ^ 2), one_div_muR_sq D _ D.hlam,
    one_div_muR_sq D _ D.hlam0]
  have hl := D.hlam; have hl0 := D.hlam0
  have h1 : 1 / lamR (2 * π * x) (2 * (j : ℕ)) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : 1 / lamR (2 * π * x) 0 ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hk : 0 ≤ 2 * π * (x : ℝ) / (2 * π) := by have := x_pos D; positivity
  have hα : 0 ≤ Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 := sq_nonneg _
  calc 2 * π * x / (2 * π) / lamR (2 * π * x) (2 * (j : ℕ))
        + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 * (2 * π * x / (2 * π) / lamR (2 * π * x) 0)
      = 2 * π * x / (2 * π) * (1 / lamR (2 * π * x) (2 * (j : ℕ)))
        + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 * (2 * π * x / (2 * π) * (1 / lamR (2 * π * x) 0)) := by ring
    _ ≤ 2 * π * x / (2 * π) * 2 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 * (2 * π * x / (2 * π) * 2) := by gcongr
    _ = _ := by ring

/-- **The derivative**: `∫₁^∞ ψ′² ≤ 2c²(1 + α_j²)` for `ψ′ = ψ′_{g̃}`. -/
theorem integral_psiD_gSrc_sq_le (D : RungData x j) :
    IntegrableOn (fun t => psiD (2 * π * x) (gSrc (2 * π * x) j) t ^ 2) (Ioi 1)
      ∧ ∫ t in Ioi (1 : ℝ), psiD (2 * π * x) (gSrc (2 * π * x) j) t ^ 2
        ≤ 2 * (2 * π * x) ^ 2 * (1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2) := by
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith [D.hc]
  have hi := Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psiD_sq hc0 (continuousOn_gSrc D)
  refine ⟨hi.integrableOn, ?_⟩
  calc ∫ t in Ioi (1 : ℝ), psiD (2 * π * x) (gSrc (2 * π * x) j) t ^ 2
      ≤ ∫ t, psiD (2 * π * x) (gSrc (2 * π * x) j) t ^ 2 :=
        setIntegral_le_integral hi (Eventually.of_forall fun t => sq_nonneg _)
    _ ≤ 2 * π * (2 * π * x) * ∫ s in (-1 : ℝ)..1, gSrc (2 * π * x) j s ^ 2 :=
        Cvs.Prolate.RungSpanBernsteinNikolskii.integral_psiD_sq_le hc0 (continuousOn_gSrc D)
    _ ≤ 2 * π * (2 * π * x) * (2 * π * x / (2 * π) * (2 * (1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2))) :=
        mul_le_mul_of_nonneg_left (integral_gSrc_sq_le D) (by positivity)
    _ = _ := by field_simp

/-- **The edge value**: `|ψ(1)| = |G_j(1)| ≤ 4√x·√(1 + α_j²)`. -/
theorem abs_psi_gSrc_one_le (D : RungData x j) :
    |psi (2 * π * x) (gSrc (2 * π * x) j) 1| ≤ 4 * √(x : ℝ) * √(1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2) := by
  rw [← psi_gSrc_eq D 1 ⟨by norm_num, le_rfl⟩]
  have h1 := Cvs.Prolate.RungSpanBernsteinNikolskii.spine_nikolskii D.hc (Pi.single j 1) 1 ⟨by norm_num, le_rfl⟩
  have h2 := Cvs.Route.Visibility.PerRungLogTailLaw.integral_single_sq_le D.hc j
  have hx0 := (x_pos D).le
  have hsq : Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) 1 ^ 2
      ≤ (4 * √(x : ℝ) * √(1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hx0, Real.sq_sqrt (by positivity)]
    calc _ ≤ 8 * x * ∫ s in (0 : ℝ)..1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (Pi.single j 1) s ^ 2 := h1
      _ ≤ 8 * x * (2 + 2 * Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2) := by gcongr
      _ = 4 ^ 2 * x * (1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2) := by ring
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (by positivity))

/-- `|ψ_{g̃}| ≤ √(2∫_{−1}^{1} g̃²)` on `ℝ`. -/
theorem abs_psi_gSrc_le (D : RungData x j) (t : ℝ) :
    |psi (2 * π * x) (gSrc (2 * π * x) j) t| ≤ √(2 * ∫ s in (-1 : ℝ)..1, gSrc (2 * π * x) j s ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Cvs.Prolate.RungSpanBernsteinNikolskii.psi_sq_le (continuousOn_gSrc D) t)

/-! ### The constants against `lemXBound` -/

theorem pBar_sq_le (D : RungData x j) : Cvs.Route.Visibility.RungXBoxExplicit.pBar x j ^ 2 ≤ 1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2 := by
  have h1 : 0 < lamR (2 * π * x) (2 * (j : ℕ)) := by linarith [D.hlam]
  have h2 : 0 < lamR (2 * π * x) 0 := by linarith [D.hlam0]
  have a1 : (1 - lamR (2 * π * x) (2 * (j : ℕ))) / lamR (2 * π * x) (2 * (j : ℕ)) ≤ 1 := by
    rw [div_le_one h1]; linarith [D.hlam]
  have a2 : (1 - lamR (2 * π * x) 0) / lamR (2 * π * x) 0 ≤ 1 := by rw [div_le_one h2]; linarith [D.hlam0]
  have b1 : 0 ≤ (1 - lamR (2 * π * x) (2 * (j : ℕ))) / lamR (2 * π * x) (2 * (j : ℕ)) :=
    div_nonneg (by linarith [D.hlam1]) h1.le
  have b2 : 0 ≤ (1 - lamR (2 * π * x) 0) / lamR (2 * π * x) 0 := div_nonneg (by linarith [D.hlam01]) h2.le
  rw [Cvs.Route.Visibility.RungXBoxExplicit.pBar, Real.sq_sqrt (by
    rw [mul_div_assoc]; exact add_nonneg b1 (mul_nonneg (sq_nonneg _) b2))]
  rw [mul_div_assoc]
  nlinarith [sq_nonneg (Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j)]

theorem pNorm_le_pBar (D : RungData x j) : Cvs.Prolate.Mellin.ExteriorSeriesBox.pNorm (psi (2 * π * x) (gSrc (2 * π * x) j)) ≤ Cvs.Route.Visibility.RungXBoxExplicit.pBar x j := by
  unfold Cvs.Prolate.Mellin.ExteriorSeriesBox.pNorm
  calc √(∫ t in Ioi (1 : ℝ), psi (2 * π * x) (gSrc (2 * π * x) j) t ^ 2) ≤ √(Cvs.Route.Visibility.RungXBoxExplicit.pBar x j ^ 2) :=
        Real.sqrt_le_sqrt (integral_psi_gSrc_sq_le D).2
    _ = Cvs.Route.Visibility.RungXBoxExplicit.pBar x j := Real.sqrt_sq (Real.sqrt_nonneg _)

/-- **The integration-by-parts constant**: `B/(2c) ≤ 2√(1 + α_j²)` for `x ≥ 14`. -/
theorem bConst_div_le (D : RungData x j) (hx : 14 ≤ x) :
    Cvs.Prolate.Mellin.ExteriorSeriesBox.bConst (psi (2 * π * x) (gSrc (2 * π * x) j)) (psiD (2 * π * x) (gSrc (2 * π * x) j)) / (2 * (2 * π * x))
      ≤ 2 * √(1 + Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j ^ 2) := by
  set α := Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j
  set r := √(1 + α ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hx14 : (14 : ℝ) ≤ x := by exact_mod_cast hx
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by positivity
  have h1 := abs_psi_gSrc_one_le D
  have h2 : √(∫ t in Ioi (1 : ℝ), psiD (2 * π * x) (gSrc (2 * π * x) j) t ^ 2) ≤ √2 * c * r := by
    have := Real.sqrt_le_sqrt (integral_psiD_gSrc_sq_le D).2
    refine this.trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hc0.le]
  have h3 : Cvs.Prolate.Mellin.ExteriorSeriesBox.pNorm (psi (2 * π * x) (gSrc (2 * π * x) j)) / √3 ≤ r := by
    have hp := pNorm_le_pBar D
    have hpb : Cvs.Route.Visibility.RungXBoxExplicit.pBar x j ≤ r := by
      calc Cvs.Route.Visibility.RungXBoxExplicit.pBar x j = √(Cvs.Route.Visibility.RungXBoxExplicit.pBar x j ^ 2) := (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
        _ ≤ r := Real.sqrt_le_sqrt (pBar_sq_le D)
    have h3 : 1 ≤ √3 := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    calc Cvs.Prolate.Mellin.ExteriorSeriesBox.pNorm _ / √3 ≤ Cvs.Prolate.Mellin.ExteriorSeriesBox.pNorm _ / 1 :=
          div_le_div_of_nonneg_left (Cvs.Prolate.Mellin.ExteriorSeriesBox.pNorm_nonneg _) one_pos h3
      _ ≤ r := by rw [div_one]; exact hp.trans hpb
  have hsx : √(x : ℝ) ≤ x / 3 := by
    have h9 : (3 : ℝ) ≤ √(x : ℝ) := by
      rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ x by linarith)
    nlinarith
  have hs2 : √2 ≤ 1.415 := by
    rw [show (1.415 : ℝ) = √(1.415 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hπ := Real.pi_gt_three
  unfold Cvs.Prolate.Mellin.ExteriorSeriesBox.bConst
  rw [div_le_iff₀ (by positivity)]
  have key : |psi (2 * π * x) (gSrc (2 * π * x) j) 1|
      + √(∫ t in Ioi (1 : ℝ), psiD (2 * π * x) (gSrc (2 * π * x) j) t ^ 2)
      + Cvs.Prolate.Mellin.ExteriorSeriesBox.pNorm (psi (2 * π * x) (gSrc (2 * π * x) j)) / √3 ≤ (4 * (x / 3) + √2 * c + 1) * r := by
    have : 4 * √(x : ℝ) * r ≤ 4 * (x / 3) * r := by gcongr
    nlinarith
  have hfin : (4 * ((x : ℝ) / 3) + √2 * c + 1) ≤ 2 * c := by rw [hc]; nlinarith
  nlinarith

end Cvs.Prolate.Mellin.UnitRungBandExtension

end
