import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.QIdentityCutPoint
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungStieltjesTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-! The finite Q-identity at `w ≡ 1` for the z-Stieltjes transform of an angular rung: for
`y > 1` and `1 < z ≤ Z`, `e^{icyz}Fs(y, z)` equals `e^{icyZ}Fs(y, Z)` minus `ic` times the
remainder integral `∫_z^Z e^{icyt}ψ R` plus the cut boundary terms `S[μ_cut](Z) − S[μ_cut](z)`. -/

noncomputable section
open Real Set Filter Topology MeasureTheory Complex Metric
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts
open Cvs.Prolate.RungStieltjesTransform
open scoped Interval

namespace Cvs.Prolate.RungStieltjesIdentity

/-- For `y > 1` and `1 < z ≤ Z`: `e^{icyz}Fs(y, z) = e^{icyZ}Fs(y, Z)
− ic[∫_z^Z e^{icyt}ψR + S[μ_cut](Z) − S[μ_cut](z)]`, by FTC and the Q-identity at `w ≡ 1`. -/
theorem fsZ_identity {g g₁ g₂ : ℝ → ℝ} {c χ y z Z : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hc : 0 < c) (hχc : χ < c ^ 2) (hy : 1 < y)
    (hz : 1 < z) (hzZ : z ≤ Z) :
    eF c y z * fsZ c g y z
      = eF c y Z * fsZ c g y Z
        - I * c * ((∫ t in z..Z, eF c y t * (psi c g t : ℂ)
              * Cvs.L2a.QIdentityComplexWeight.rRc (fun _ => 1) (fun _ => 0) (fun _ => 0) c χ y t)
          + Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c y Z) c χ g Z
          - Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c y z) c χ g z) := by
  have hgc : ContinuousOn g (Icc (-1) 1) := Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt hg
  obtain ⟨-, -, hψc, -⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang
  have hint : IntervalIntegrable (fun t => I * c * eF c y t * (psi c g t : ℂ)) volume z Z :=
    ((continuous_const.mul (continuous_eF c y).1).mul
      (Complex.continuous_ofReal.comp hψc)).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_eF_mul_fsZ (c := c) hgc heven hy t) hint
  have hq := Cvs.L2a.QIdentityComplexWeight.ibpC_Icc (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0)
    (w₂ := fun _ => 0) (χ := χ) (y := y) hg hg₁ hg₂c hang hc (by linarith) hz hzZ
    (fun x _ => hasDerivAt_const x 1) (fun x _ => hasDerivAt_const x 0) continuousOn_const
  have hBZ := Cvs.L2a.QIdentityCutPoint.bBc_cut_split (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0)
    (g := g) (y := y) (by linarith : 1 < Z) hc hχc rfl rfl
  have hBz := Cvs.L2a.QIdentityCutPoint.bBc_cut_split (w := fun _ => (1 : ℂ)) (w₁ := fun _ => 0)
    (g := g) (y := y) hz hc hχc rfl rfl
  rw [hBZ, hBz] at hq
  have e1 : ∫ t in z..Z, I * c * eF c y t * (psi c g t : ℂ)
      = I * c * ∫ t in z..Z, (fun _ => (1 : ℂ)) t * (psi c g t : ℂ) * eF c y t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only; ring
  rw [e1, hq] at hftc
  linear_combination hftc

end Cvs.Prolate.RungStieltjesIdentity
