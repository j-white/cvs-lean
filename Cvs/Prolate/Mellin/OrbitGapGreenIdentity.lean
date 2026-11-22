import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SturmProductByParts
import Cvs.Prolate.Mellin.FirstModeMellinEdge
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The orbit-gap Green identity against the Mellin kernel

`SturmProductByParts`'s cross identity with the rung `ψ' = u/p`, `u' = −qψ` against a Mellin pair `y' = v/ξ²`, `v' = −wy`
(`w = t² + ¼`): `∫_s^X ψy = [(p/D)ψv − (ξ²/D)uy]_s^X − ∫ αψv + ∫ βuy` with the mismatch `D = ξ²q − pw`,
`α = (p/D)'`, `β = (ξ²/D)'`. The identity is exact wherever `D > 0`, which `DM_ge` gives from `w < c²ξ²`.
-/

namespace Cvs.Prolate.Mellin.OrbitGapGreenIdentity

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.MellinKernelSturmLiouville

/-- The Mellin mismatch `D = ξ²q − p w` of a rung against `ξ^{−1/2−it}`, `p = ξ² − 1`, `q = c²ξ² − χ`,
`w = t² + ¼`. -/
noncomputable def DM (c χ w ξ : ℝ) : ℝ := ξ ^ 2 * qP c χ ξ - pP ξ * w

/-- `D' = 2ξ q + 2c²ξ³ − 2ξ w`. -/
noncomputable def dDM (c χ w ξ : ℝ) : ℝ := 2 * ξ * qP c χ ξ + ξ ^ 2 * (2 * c ^ 2 * ξ) - 2 * ξ * w

/-- `α = (p/D)' = −2ξ(c²p² − (c² − χ))/D²` (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.numA_euler at `m = 1`). -/
noncomputable def alphaM (c χ w ξ : ℝ) : ℝ :=
  -(2 * ξ * (c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ))) / DM c χ w ξ ^ 2

/-- `β = (ξ²/D)' = −2ξ(c²ξ⁴ − w)/D²` (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.numB_euler at `m = 1`). -/
noncomputable def betaM (c χ w ξ : ℝ) : ℝ := -(2 * ξ * (c ^ 2 * ξ ^ 4 - w)) / DM c χ w ξ ^ 2

theorem DM_eq_DE (c χ w ξ : ℝ) : DM c χ w ξ = DE c χ 1 w ξ := by
  unfold DM DE; rw [Cvs.Prolate.Mellin.FirstModeMellinEdge.pm_one, Cvs.Prolate.Mellin.FirstModeMellinEdge.qm_one]

theorem hasDerivAt_pP (ξ : ℝ) : HasDerivAt pP (2 * ξ) ξ := by
  have h := Cvs.L2a.NonresonantCrossIntegral.hasDerivAt_pm one_ne_zero ξ
  rwa [show Cvs.L2a.NonresonantCrossIntegral.pm 1 = pP from funext Cvs.Prolate.Mellin.FirstModeMellinEdge.pm_one] at h

theorem hasDerivAt_DM (c χ w ξ : ℝ) : HasDerivAt (DM c χ w) (dDM c χ w ξ) ξ := by
  have h := hasDerivAt_DE (c := c) (χ := χ) (w := w) one_ne_zero ξ
  rw [show DM c χ w = DE c χ 1 w from funext (DM_eq_DE c χ w)]
  refine h.congr_deriv ?_
  unfold dDM dDE; rw [Cvs.Prolate.Mellin.FirstModeMellinEdge.qm_one]; ring

/-- `D = p(c²ξ² − w) + (c² − χ)ξ² ≥ p(c²ξ² − w)` for `χ ≤ c²`. -/
theorem DM_ge {c χ w ξ : ℝ} (hχ : χ ≤ c ^ 2) (hξ : 1 ≤ ξ) :
    pP ξ * (c ^ 2 * ξ ^ 2 - w) ≤ DM c χ w ξ := by
  have e : DM c χ w ξ - pP ξ * (c ^ 2 * ξ ^ 2 - w) = (c ^ 2 - χ) * ξ ^ 2 := by
    unfold DM pP qP; ring
  have h : 0 ≤ (c ^ 2 - χ) * ξ ^ 2 := mul_nonneg (by linarith) (zero_le_one.trans (one_le_pow₀ hξ))
  linarith

theorem DM_pos {c χ w ξ : ℝ} (hχ : χ ≤ c ^ 2) (hξ : 1 < ξ) (hw : w < c ^ 2 * ξ ^ 2) : 0 < DM c χ w ξ := by
  have h1 := DM_ge (w := w) hχ hξ.le
  have h2 : 0 < pP ξ * (c ^ 2 * ξ ^ 2 - w) := mul_pos (pP_pos hξ) (by linarith)
  linarith

theorem num_alpha (c χ w ξ : ℝ) :
    2 * ξ * DM c χ w ξ - pP ξ * dDM c χ w ξ = -(2 * ξ * (c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ))) := by
  unfold DM dDM pP qP; ring

theorem num_beta (c χ w ξ : ℝ) :
    2 * ξ * DM c χ w ξ - ξ ^ 2 * dDM c χ w ξ = -(2 * ξ * (c ^ 2 * ξ ^ 4 - w)) := by
  unfold DM dDM pP qP; ring

/-- The coefficient `p/D` of Cvs.Prolate.LiouvilleGreen.SturmProductByParts (with `σ = 1`, `p₂ = ξ²`, `q₂ = w`) has derivative `α`. -/
theorem hasDerivAt_pdivD {c χ w ξ : ℝ} (hD : DM c χ w ξ ≠ 0) :
    HasDerivAt (fun r => (1 : ℝ) * pP r / (r ^ 2 * qP c χ r - pP r * w)) (alphaM c χ w ξ) ξ := by
  have h1 : HasDerivAt (fun r => (1 : ℝ) * pP r) (1 * (2 * ξ)) ξ := (hasDerivAt_pP ξ).const_mul 1
  have h2 : HasDerivAt (DM c χ w) (dDM c χ w ξ) ξ := hasDerivAt_DM c χ w ξ
  refine (h1.div h2 hD).congr_deriv ?_
  unfold alphaM; rw [← num_alpha]; ring

/-- The coefficient `ξ²/D` of Cvs.Prolate.LiouvilleGreen.SturmProductByParts has derivative `β`. -/
theorem hasDerivAt_sqdivD {c χ w ξ : ℝ} (hD : DM c χ w ξ ≠ 0) :
    HasDerivAt (fun r => (1 : ℝ) * r ^ 2 / (r ^ 2 * qP c χ r - pP r * w)) (betaM c χ w ξ) ξ := by
  have h1 : HasDerivAt (fun r => (1 : ℝ) * r ^ 2) (1 * (2 * ξ)) ξ := by
    have := (hasDerivAt_pow 2 ξ).const_mul (1 : ℝ)
    refine this.congr_deriv ?_; push_cast; ring
  have h2 : HasDerivAt (DM c χ w) (dDM c χ w ξ) ξ := hasDerivAt_DM c χ w ξ
  refine (h1.div h2 hD).congr_deriv ?_
  unfold betaM; rw [← num_beta]; ring

theorem continuous_DM (c χ w : ℝ) : Continuous (DM c χ w) := by
  unfold DM qP pP; fun_prop

/-- **Lemma G (exact)**: `∫_s^X ψy = [(p/D)ψv − (ξ²/D)uy]_s^X − ∫_s^X αψv + ∫_s^X βuy` for any rung pair
`ψ' = u/p`, `u' = −qψ` and any Mellin pair `y' = v/ξ²`, `v' = −wy`, wherever `D > 0`. -/
theorem mellin_green {c χ w s X : ℝ} {ψ u y v : ℝ → ℝ} (hs : 1 < s) (hsX : s ≤ X)
    (hD : ∀ ξ ∈ Icc s X, 0 < DM c χ w ξ)
    (hψ : ∀ ξ ∈ Icc s X, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc s X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hy : ∀ ξ ∈ Icc s X, HasDerivAt y (v ξ / ξ ^ 2) ξ)
    (hv : ∀ ξ ∈ Icc s X, HasDerivAt v (-(w * y ξ)) ξ) :
    ∫ ξ in s..X, ψ ξ * y ξ
      = (pP X / DM c χ w X * (ψ X * v X) - X ^ 2 / DM c χ w X * (u X * y X))
        - (pP s / DM c χ w s * (ψ s * v s) - s ^ 2 / DM c χ w s * (u s * y s))
        - (∫ ξ in s..X, alphaM c χ w ξ * (ψ ξ * v ξ)) + ∫ ξ in s..X, betaM c χ w ξ * (u ξ * y ξ) := by
  have hp₁ : ∀ r ∈ Icc s X, pP r ≠ 0 := fun r hr => (pP_pos (lt_of_lt_of_le hs hr.1)).ne'
  have hp₂ : ∀ r ∈ Icc s X, r ^ 2 ≠ 0 := fun r hr => pow_ne_zero 2 (by linarith [hr.1])
  have hD' : ∀ r ∈ Icc s X, r ^ 2 * qP c χ r - pP r * w ≠ 0 := fun r hr => (hD r hr).ne'
  have hA : ∀ r ∈ Icc s X,
      HasDerivAt (fun r => (1 : ℝ) * pP r / (r ^ 2 * qP c χ r - pP r * w)) (alphaM c χ w r) r :=
    fun r hr => hasDerivAt_pdivD (hD r hr).ne'
  have hB : ∀ r ∈ Icc s X,
      HasDerivAt (fun r => (1 : ℝ) * r ^ 2 / (r ^ 2 * qP c χ r - pP r * w)) (betaM c χ w r) r :=
    fun r hr => hasDerivAt_sqdivD (hD r hr).ne'
  have hDsq : ∀ r ∈ Icc s X, DM c χ w r ^ 2 ≠ 0 := fun r hr => pow_ne_zero 2 (hD r hr).ne'
  have hαc : ContinuousOn (alphaM c χ w) (Icc s X) := by
    have h := ContinuousOn.div (f := fun ξ => -(2 * ξ * (c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ))))
      (s := Icc s X) ?_ ((continuous_DM c χ w).pow 2).continuousOn hDsq
    · exact h
    exact Continuous.continuousOn (by unfold pP; fun_prop)
  have hβc : ContinuousOn (betaM c χ w) (Icc s X) := by
    have h := ContinuousOn.div (f := fun ξ => -(2 * ξ * (c ^ 2 * ξ ^ 4 - w)))
      (s := Icc s X) ?_ ((continuous_DM c χ w).pow 2).continuousOn hDsq
    · exact h
    exact Continuous.continuousOn (by fun_prop)
  have hc : ContinuousOn (fun r => (1 : ℝ) * (ψ r * y r)) (Icc s X) := fun r hr =>
    (continuousAt_const.mul ((hψ r hr).continuousAt.mul (hy r hr).continuousAt)).continuousWithinAt
  have hq₁ : ContinuousOn (qP c χ) (Icc s X) := Continuous.continuousOn (by unfold qP; fun_prop)
  have hq₂ : ContinuousOn (fun _ : ℝ => w) (Icc s X) := continuousOn_const
  have hpc₁ : ContinuousOn pP (Icc s X) := Continuous.continuousOn (by unfold pP; fun_prop)
  have hpc₂ : ContinuousOn (fun r : ℝ => r ^ 2) (Icc s X) := Continuous.continuousOn (by fun_prop)
  have h := Cvs.Prolate.LiouvilleGreen.SturmProductByParts.integral_cross (σ := fun _ => (1 : ℝ)) (p₁ := pP) (q₁ := qP c χ)
    (u₁ := u) (f₁ := ψ) (p₂ := fun ξ => ξ ^ 2) (q₂ := fun _ => w) (f₂ := y) (u₂ := v)
    (α := alphaM c χ w) (β := betaM c χ w) hsX hp₁ hp₂ hD' hψ hu hy hv hA hB hαc hβc hc hq₁ hq₂
    hpc₁ hpc₂
  simp only [one_mul] at h
  exact h

/-- Lemma G for the cosine kernel `y_t = ky t`, flux `ku t`, `w = t² + ¼`. -/
theorem mellin_green_cos {c χ s X t : ℝ} {ψ u : ℝ → ℝ} (hs : 1 < s) (hsX : s ≤ X)
    (hD : ∀ ξ ∈ Icc s X, 0 < DM c χ (t ^ 2 + 1 / 4) ξ)
    (hψ : ∀ ξ ∈ Icc s X, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc s X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) :
    ∫ ξ in s..X, ψ ξ * ky t ξ
      = (pP X / DM c χ (t ^ 2 + 1 / 4) X * (ψ X * ku t X) - X ^ 2 / DM c χ (t ^ 2 + 1 / 4) X * (u X * ky t X))
        - (pP s / DM c χ (t ^ 2 + 1 / 4) s * (ψ s * ku t s) - s ^ 2 / DM c χ (t ^ 2 + 1 / 4) s * (u s * ky t s))
        - (∫ ξ in s..X, alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * ku t ξ))
        + ∫ ξ in s..X, betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * ky t ξ) :=
  mellin_green hs hsX hD hψ hu
    (fun ξ hξ => hasDerivAt_ky (by linarith [hξ.1]))
    (fun ξ hξ => hasDerivAt_ku (by linarith [hξ.1]))

/-- Lemma G for the sine kernel `ỹ_t = kys t`, flux `kus t`. -/
theorem mellin_green_sin {c χ s X t : ℝ} {ψ u : ℝ → ℝ} (hs : 1 < s) (hsX : s ≤ X)
    (hD : ∀ ξ ∈ Icc s X, 0 < DM c χ (t ^ 2 + 1 / 4) ξ)
    (hψ : ∀ ξ ∈ Icc s X, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc s X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) :
    ∫ ξ in s..X, ψ ξ * kys t ξ
      = (pP X / DM c χ (t ^ 2 + 1 / 4) X * (ψ X * kus t X) - X ^ 2 / DM c χ (t ^ 2 + 1 / 4) X * (u X * kys t X))
        - (pP s / DM c χ (t ^ 2 + 1 / 4) s * (ψ s * kus t s) - s ^ 2 / DM c χ (t ^ 2 + 1 / 4) s * (u s * kys t s))
        - (∫ ξ in s..X, alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * kus t ξ))
        + ∫ ξ in s..X, betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * kys t ξ) :=
  mellin_green hs hsX hD hψ hu
    (fun ξ hξ => hasDerivAt_kys (by linarith [hξ.1]))
    (fun ξ hξ => hasDerivAt_kus (by linarith [hξ.1]))

/-- `|ξ²y'|² = ξ(t² + ¼)` for the complex kernel: `ku² + kus² = ξ w`. -/
theorem ku_sq_add_kus_sq {t ξ : ℝ} (hξ : 0 < ξ) : ku t ξ ^ 2 + kus t ξ ^ 2 = ξ * (t ^ 2 + 1 / 4) := by
  unfold ku kus
  have hs : √ξ ^ 2 = ξ := Real.sq_sqrt hξ.le
  have h := sin_sq_add_cos_sq (t * log ξ)
  linear_combination
    ((t * sin (t * log ξ) + cos (t * log ξ) / 2) ^ 2 + (t * cos (t * log ξ) - sin (t * log ξ) / 2) ^ 2) * hs
    + ξ * (t ^ 2 + 1 / 4) * h

/-- `|y|² = 1/ξ`: `ky² + kys² = 1/ξ`. -/
theorem ky_sq_add_kys_sq {t ξ : ℝ} (hξ : 0 < ξ) : ky t ξ ^ 2 + kys t ξ ^ 2 = 1 / ξ := by
  unfold ky kys
  rw [div_pow, div_pow, Real.sq_sqrt hξ.le, ← add_div, cos_sq_add_sin_sq]

end Cvs.Prolate.Mellin.OrbitGapGreenIdentity
