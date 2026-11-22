import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.RungTailIntegralMass
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.SelfConvolutionCosine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# E2: `|W_∞(Φ, Ψ)| ≤ A₁√N + A₂√P`, and `w₁ ≤ A₁ + A₂/√κ`

The three channels of Cvs.L2a.FullTailBilinearChannels add to E2 with `A₁ = Π₊(Ψ) + C_A + C_L1 + log 2‖T⁺‖ + 2‖log θ T⁺‖`,
`Π₊(Ψ) = ½(49/24 − log 2π)`, and `A₂ = (59/630)C_π + log 2‖T⁺‖ + (4√(6J)/c)(½ + V₀)(2 + ½log 2)`.
A floor `κP ≤ N` (or `FullTailFloorLimit`'s frequent floor) gives `w₁ = |W_∞(Φ, Ψ)|/√N ≤ A₁ + A₂/√κ`; for `J ≤ c/4 + 1` and
`c ≥ 80`, `A₂ ≤ Ā₂`, a constant free of `c` and of the span.
-/

namespace Cvs.L2a.FullTailBilinearBound

open Real Set Filter MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FullTailConvergence Cvs.L2a.BetaProfilePoissonTail Cvs.L2a.FullTailPolarisation Cvs.L2a.FullTailBilinearChannels

/-! ### The constants -/

/-- `A₁ = ½(49/24 − log 2π) + C_A + C_L1 + log 2‖T⁺‖ + 2‖log θ T⁺‖`. -/
noncomputable def A1 : ℝ :=
  (49 / 48 - Real.log (2 * π) / 2) + CA + CL1 + Real.log 2 * normT + 2 * normLogT

/-- `A₂(J, c) = (59/630)C_π(J, c) + log 2‖T⁺‖ + (4√(6J)/c)(½ + V₀)(2 + ½log 2)`. -/
noncomputable def A2 (J c : ℝ) : ℝ :=
  59 / 630 * Cvs.Prolate.RungTailIntegralMass.piConst J c + Real.log 2 * normT
    + 4 * √(6 * J) / c * (1 / 2 + V0) * (2 + Real.log 2 / 2)

/-- `Ā₂ = (59/630)(5^{−1/2} + ¾(30/11 + ¾)) + log 2‖T⁺‖ + (½ + V₀)(2 + ½log 2)`: `A₂` at `√(6J)/c = ¼`. -/
noncomputable def A2bar : ℝ :=
  59 / 630 * (1 / √5 + 3 / 4 * (30 / 11 + 3 / 4)) + Real.log 2 * normT + (1 / 2 + V0) * (2 + Real.log 2 / 2)

theorem abs_piPlus_Psi : |Cvs.L2a.FullTailPoleChannel.piPlus Psi| = 49 / 48 - Real.log (2 * π) / 2 := by
  rw [abs_of_pos (lt_of_lt_of_le (by norm_num) piPlus_Psi_bounds.1), piPlus_Psi]

theorem CL1_nonneg : 0 ≤ CL1 :=
  setIntegral_nonneg measurableSet_Ioi fun _k hk =>
    div_nonneg (Real.sqrt_nonneg _) (le_of_lt (lt_trans one_pos hk))

theorem A1_nonneg : 0 ≤ A1 := by
  have h := abs_piPlus_Psi ▸ abs_nonneg (Cvs.L2a.FullTailPoleChannel.piPlus Psi)
  have hCA : 0 ≤ CA := Real.sqrt_nonneg _
  have hT : 0 ≤ normT := Real.sqrt_nonneg _
  have hLT : 0 ≤ normLogT := Real.sqrt_nonneg _
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold A1
  have := CL1_nonneg
  positivity

theorem piConst_nonneg {J c : ℝ} (hc : 0 < c) : 0 ≤ Cvs.Prolate.RungTailIntegralMass.piConst J c := by
  unfold Cvs.Prolate.RungTailIntegralMass.piConst; positivity

theorem A2_nonneg {J c : ℝ} (hc : 0 < c) : 0 ≤ A2 J c := by
  have hT : 0 ≤ normT := Real.sqrt_nonneg _
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have := piConst_nonneg (J := J) hc
  have := V0_nonneg
  unfold A2
  positivity

/-- On the deep family's count `J ≤ c/4 + 1`, `c ≥ 80`: `√(6J)/c ≤ ¼`. -/
theorem sqrt_six_card_div_le {J c : ℝ} (hc : 80 ≤ c) (hJ : J ≤ c / 4 + 1) : √(6 * J) / c ≤ 1 / 4 := by
  have hc0 : 0 < c := by linarith
  rw [div_le_iff₀ hc0, Real.sqrt_le_left (by linarith)]
  nlinarith

/-- **`A₂ ≤ Ā₂`**, uniformly in `c ≥ 80` and in the span, once `J ≤ c/4 + 1`. -/
theorem A2_le_A2bar {J c : ℝ} (hc : 80 ≤ c) (hJ : J ≤ c / 4 + 1) : A2 J c ≤ A2bar := by
  have hq := sqrt_six_card_div_le hc hJ
  have hq0 : 0 ≤ √(6 * J) / c := div_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hW : 0 ≤ (1 / 2 + V0) * (2 + Real.log 2 / 2) := by have := V0_nonneg; positivity
  have e1 : Cvs.Prolate.RungTailIntegralMass.piConst J c = 1 / √5 + 3 * (√(6 * J) / c) * (30 / 11 + 3 / 4) := by
    unfold Cvs.Prolate.RungTailIntegralMass.piConst; ring
  have e2 : 4 * √(6 * J) / c * (1 / 2 + V0) * (2 + Real.log 2 / 2)
      = 4 * (√(6 * J) / c) * ((1 / 2 + V0) * (2 + Real.log 2 / 2)) := by ring
  unfold A2 A2bar
  rw [e1, e2]
  have h1 : 3 * (√(6 * J) / c) * (30 / 11 + 3 / 4) ≤ 3 / 4 * (30 / 11 + 3 / 4) := by nlinarith
  have h2 : 4 * (√(6 * J) / c) * ((1 / 2 + V0) * (2 + Real.log 2 / 2))
      ≤ (1 / 2 + V0) * (2 + Real.log 2 / 2) := by nlinarith
  nlinarith

/-! ### E2 on the span -/

section span

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-- **E2**: `|W_∞(Φ, Ψ)| ≤ A₁√N + A₂√P` for `Φ = Σ bᵢψ_c gᵢ`, `N = ‖F_∞(Φ)‖²`, `P = Σ bᵢ²Mᵢ`. -/
theorem polar_bil_le (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχ : Function.Injective χ) :
    |WinfBil (fun ξ => ∑ i, b i * psi c (g i) ξ) Psi|
      ≤ A1 * √(∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (g i) ξ) θ ^ 2)
        + A2 (Fintype.card ι) c * √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) := by
  have h2π : 2 * π ≤ c := by linarith [Real.pi_lt_four]
  have hP := pole_bil_le b hg hg₁ hg₂c hang hc hχ0 hχc hχ
  have hA := arch_bil_le b hg hg₁ hg₂c h2π
  have hR := prime_bil_le b hg hg₁ hg₂c hang hc hχ0 hχc hχ
  rw [abs_piPlus_Psi] at hP
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (g i) ξ
  have htri : |WinfBil Φ Psi| ≤ |poleBil Φ Psi| + |archBil Φ Psi| + |primeBil Φ Psi| := by
    unfold WinfBil
    exact (abs_sub _ _).trans (by linarith [abs_add_le (poleBil Φ Psi) (archBil Φ Psi)])
  refine htri.trans ((add_le_add (add_le_add hP hA) hR).trans (le_of_eq ?_))
  unfold A1 A2
  ring

/-- **`w₁ ≤ A₁ + A₂/√κ`** in product form: a floor `κP ≤ N` gives `|W_∞(Φ, Ψ)| ≤ (A₁ + A₂/√κ)√N`. -/
theorem polar_bil_le_of_floor (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχ : Function.Injective χ)
    {κ : ℝ} (hκ : 0 < κ)
    (hfloor : κ * ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (g i) ξ) θ ^ 2) :
    |WinfBil (fun ξ => ∑ i, b i * psi c (g i) ξ) Psi|
      ≤ (A1 + A2 (Fintype.card ι) c / √κ)
        * √(∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (g i) ξ) θ ^ 2) := by
  have hc0 : 0 < c := by linarith
  set sN := √(∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (g i) ξ) θ ^ 2)
  set P := ∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2
  have hE2 := polar_bil_le b hg hg₁ hg₂c hang hc hχ0 hχc hχ
  have hsκ : 0 < √κ := Real.sqrt_pos.mpr hκ
  have hPN : √P ≤ sN / √κ := by
    rw [le_div_iff₀ hsκ, mul_comm, ← Real.sqrt_mul hκ.le]
    exact Real.sqrt_le_sqrt hfloor
  have hA2 := A2_nonneg (J := (Fintype.card ι : ℝ)) hc0
  calc _ ≤ A1 * sN + A2 (Fintype.card ι) c * √P := hE2
    _ ≤ A1 * sN + A2 (Fintype.card ι) c * (sN / √κ) := by gcongr
    _ = (A1 + A2 (Fintype.card ι) c / √κ) * sN := by ring

end span

end Cvs.L2a.FullTailBilinearBound
