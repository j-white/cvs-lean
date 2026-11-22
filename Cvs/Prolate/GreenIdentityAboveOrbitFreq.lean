import Mathlib
import Cvs.L2a.FarPartDirichletSplit
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SturmProductByParts
import Cvs.Prolate.Mellin.GreenBoundaryBound
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.OrbitGapGreenIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Lemma G above the orbit frequency

The Green identity of Cvs.Prolate.Mellin.OrbitGapGreenIdentity holds wherever `D ≠ 0`; for `w = t² + ¼ ≥ 2c²ξ²` on `ξ ≥ 2`, `D ≤ −ξ²w/4`, so
`|p/D|, |ξ²/D| ≤ 4/w`, `|α| ≤ 32c²ξ/w²`, `|β| ≤ 32/(ξw)`, the boundary term has `‖B‖² ≤ 32E/(cξw)` and the bulk
density `‖ρ‖² ≤ 920E/(cξ³w)`: `|I(s, X; t)| ≤ 72√(Ē/(cw))/√s` at high frequency.
-/

namespace Cvs.Prolate.GreenIdentityAboveOrbitFreq

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.MellinKernelSturmLiouville Cvs.Prolate.Mellin.OrbitGapGreenIdentity Cvs.Prolate.Mellin.GreenBoundaryBound

/-! ### Green's identity wherever `D ≠ 0` -/

/-- **Lemma G (exact), `D ≠ 0`**: `OrbitGapGreenIdentity`'s identity for any rung pair and Mellin pair on `[s, X]`, `1 < s`. -/
theorem mellin_green_ne {c χ w s X : ℝ} {ψ u y v : ℝ → ℝ} (hs : 1 < s) (hsX : s ≤ X)
    (hD : ∀ ξ ∈ Icc s X, DM c χ w ξ ≠ 0)
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
  have hD' : ∀ r ∈ Icc s X, r ^ 2 * qP c χ r - pP r * w ≠ 0 := fun r hr => hD r hr
  have hA : ∀ r ∈ Icc s X,
      HasDerivAt (fun r => (1 : ℝ) * pP r / (r ^ 2 * qP c χ r - pP r * w)) (alphaM c χ w r) r :=
    fun r hr => hasDerivAt_pdivD (hD r hr)
  have hB : ∀ r ∈ Icc s X,
      HasDerivAt (fun r => (1 : ℝ) * r ^ 2 / (r ^ 2 * qP c χ r - pP r * w)) (betaM c χ w r) r :=
    fun r hr => hasDerivAt_sqdivD (hD r hr)
  have hDsq : ∀ r ∈ Icc s X, DM c χ w r ^ 2 ≠ 0 := fun r hr => pow_ne_zero 2 (hD r hr)
  have hαc : ContinuousOn (alphaM c χ w) (Icc s X) := by
    unfold alphaM
    refine ContinuousOn.div ?_ ((continuous_DM c χ w).pow 2).continuousOn hDsq
    exact (Continuous.continuousOn (by unfold pP; fun_prop) : ContinuousOn (fun ξ : ℝ => -(2 * ξ * (c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ)))) _)
  have hβc : ContinuousOn (betaM c χ w) (Icc s X) := by
    unfold betaM
    refine ContinuousOn.div ?_ ((continuous_DM c χ w).pow 2).continuousOn hDsq
    exact (Continuous.continuousOn (by fun_prop) : ContinuousOn (fun ξ : ℝ => -(2 * ξ * (c ^ 2 * ξ ^ 4 - w))) _)
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

theorem continuousOn_alphaM_ne {c χ w s X : ℝ} (hD : ∀ ξ ∈ Icc s X, DM c χ w ξ ≠ 0) :
    ContinuousOn (alphaM c χ w) (Icc s X) := by
  unfold alphaM
  refine ContinuousOn.div ?_ ((continuous_DM c χ w).pow 2).continuousOn fun ξ hξ => pow_ne_zero 2 (hD ξ hξ)
  exact (Continuous.continuousOn (by unfold pP; fun_prop) : ContinuousOn (fun ξ : ℝ => -(2 * ξ * (c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ)))) _)

theorem continuousOn_betaM_ne {c χ w s X : ℝ} (hD : ∀ ξ ∈ Icc s X, DM c χ w ξ ≠ 0) :
    ContinuousOn (betaM c χ w) (Icc s X) := by
  unfold betaM
  refine ContinuousOn.div ?_ ((continuous_DM c χ w).pow 2).continuousOn fun ξ hξ => pow_ne_zero 2 (hD ξ hξ)
  exact (Continuous.continuousOn (by fun_prop) : ContinuousOn (fun ξ : ℝ => -(2 * ξ * (c ^ 2 * ξ ^ 4 - w))) _)

/-- **Lemma G, complex form, `D ≠ 0`**: `I(s, X; t) = B(X) − B(s) − ∫_s^X ρ`. -/
theorem mellinI_eq_green_ne {c χ s X t : ℝ} {ψ u : ℝ → ℝ} (hs : 1 < s) (hsX : s ≤ X)
    (hD : ∀ ξ ∈ Icc s X, DM c χ (t ^ 2 + 1 / 4) ξ ≠ 0)
    (hψ : ∀ ξ ∈ Icc s X, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc s X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) :
    Cvs.L2a.FarPartDirichletSplit.mellinI ψ s X t
      = bdryC c χ t ψ u X - bdryC c χ t ψ u s - ∫ ξ in s..X, remDens c χ t ψ u ξ := by
  have hcos := mellin_green_ne hs hsX hD hψ hu
    (fun ξ hξ => hasDerivAt_ky (by linarith [hξ.1])) (fun ξ hξ => hasDerivAt_ku (by linarith [hξ.1]))
  have hsin := mellin_green_ne hs hsX hD hψ hu
    (fun ξ hξ => hasDerivAt_kys (by linarith [hξ.1])) (fun ξ hξ => hasDerivAt_kus (by linarith [hξ.1]))
  have hpos : ∀ ξ ∈ Icc s X, 0 < ξ := fun ξ hξ => by linarith [hξ.1]
  have hψc : ContinuousOn ψ (Icc s X) := fun ξ hξ => (hψ ξ hξ).continuousAt.continuousWithinAt
  have huc : ContinuousOn u (Icc s X) := fun ξ hξ => (hu ξ hξ).continuousAt.continuousWithinAt
  have hky : ContinuousOn (ky t) (Icc s X) := fun ξ hξ =>
    (hasDerivAt_ky (hpos ξ hξ)).continuousAt.continuousWithinAt
  have hku : ContinuousOn (ku t) (Icc s X) := fun ξ hξ =>
    (hasDerivAt_ku (hpos ξ hξ)).continuousAt.continuousWithinAt
  have hkys : ContinuousOn (kys t) (Icc s X) := fun ξ hξ =>
    (hasDerivAt_kys (hpos ξ hξ)).continuousAt.continuousWithinAt
  have hkus : ContinuousOn (kus t) (Icc s X) := fun ξ hξ =>
    (hasDerivAt_kus (hpos ξ hξ)).continuousAt.continuousWithinAt
  have hα := continuousOn_alphaM_ne hD
  have hβ := continuousOn_betaM_ne hD
  have iA1 : IntervalIntegrable (fun ξ => alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * ku t ξ)) MeasureTheory.volume s X :=
    (hα.mul (hψc.mul hku)).intervalIntegrable_of_Icc hsX
  have iB1 : IntervalIntegrable (fun ξ => betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * ky t ξ)) MeasureTheory.volume s X :=
    (hβ.mul (huc.mul hky)).intervalIntegrable_of_Icc hsX
  have iA2 : IntervalIntegrable (fun ξ => alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * kus t ξ)) MeasureTheory.volume s X :=
    (hα.mul (hψc.mul hkus)).intervalIntegrable_of_Icc hsX
  have iB2 : IntervalIntegrable (fun ξ => betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * kys t ξ)) MeasureTheory.volume s X :=
    (hβ.mul (huc.mul hkys)).intervalIntegrable_of_Icc hsX
  have i1 : IntervalIntegrable (fun ξ => ((alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * ku t ξ)
      - betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * ky t ξ) : ℝ) : ℂ)) MeasureTheory.volume s X :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((hα.mul (hψc.mul hku)).sub (hβ.mul (huc.mul hky)))).intervalIntegrable_of_Icc hsX
  have i2 : IntervalIntegrable (fun ξ => Complex.I * ((alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * kus t ξ)
      - betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * kys t ξ) : ℝ) : ℂ)) MeasureTheory.volume s X :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      ((hα.mul (hψc.mul hkus)).sub (hβ.mul (huc.mul hkys))))).intervalIntegrable_of_Icc hsX
  have e : ∫ ξ in s..X, remDens c χ t ψ u ξ
      = (((∫ ξ in s..X, alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * ku t ξ))
          - ∫ ξ in s..X, betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * ky t ξ) : ℝ) : ℂ)
        - Complex.I * (((∫ ξ in s..X, alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * kus t ξ))
          - ∫ ξ in s..X, betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * kys t ξ) : ℝ) : ℂ) := by
    unfold remDens
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_sub iA1 iB1, intervalIntegral.integral_sub iA2 iB2]
  rw [e]
  unfold Cvs.L2a.FarPartDirichletSplit.mellinI bdryC
  rw [hcos, hsin]
  push_cast
  ring

/-! ### The coefficients above the orbit frequency -/

/-- For `0 ≤ χ`, `ξ ≥ 2` and `w ≥ 2c²ξ²`: `D ≤ −ξ²w/4`. -/
theorem DM_le_neg {c χ w ξ : ℝ} (hχ0 : 0 ≤ χ) (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w) :
    DM c χ w ξ ≤ -(ξ ^ 2 * w / 4) := by
  have e : DM c χ w ξ = pP ξ * (c ^ 2 * ξ ^ 2 - w) + (c ^ 2 - χ) * ξ ^ 2 := by unfold DM pP qP; ring
  have hξ2 : 4 ≤ ξ ^ 2 := by nlinarith
  have hp : 3 * ξ ^ 2 / 4 ≤ pP ξ := by unfold pP; nlinarith
  have hw0 : 0 ≤ w := le_trans (by positivity) hw
  have hcw : c ^ 2 * ξ ^ 2 ≤ w / 2 := by linarith
  have h1 : pP ξ * (c ^ 2 * ξ ^ 2 - w) ≤ pP ξ * (-(w / 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : 3 * ξ ^ 2 / 4 * (w / 2) ≤ pP ξ * (w / 2) := mul_le_mul_of_nonneg_right hp (by linarith)
  have h3 : (c ^ 2 - χ) * ξ ^ 2 ≤ c ^ 2 * ξ ^ 2 := by nlinarith [sq_nonneg ξ]
  have h4 : c ^ 2 * ξ ^ 2 ≤ ξ ^ 2 * w / 8 := by
    have hA : ξ ^ 2 * (2 * c ^ 2 * ξ ^ 2) ≤ ξ ^ 2 * w := mul_le_mul_of_nonneg_left hw (sq_nonneg ξ)
    have hB : 0 ≤ c ^ 2 * ξ ^ 2 * (ξ ^ 2 - 4) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  rw [e]; nlinarith

theorem abs_DM_ge {c χ w ξ : ℝ} (hχ0 : 0 ≤ χ) (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w) :
    ξ ^ 2 * w / 4 ≤ |DM c χ w ξ| := by
  have h := DM_le_neg hχ0 hξ hw
  exact le_trans (by linarith) (neg_le_abs (DM c χ w ξ))

theorem DM_ne {c χ w ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w) :
    DM c χ w ξ ≠ 0 := by
  have h := abs_DM_ge hχ0 hξ hw
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have : 0 < ξ ^ 2 * w / 4 := by positivity
  intro h0; rw [h0, abs_zero] at h; linarith

/-- `|p/D| ≤ 4/w`. -/
theorem abs_pdivD_le {c χ w ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w) :
    |pP ξ / DM c χ w ξ| ≤ 4 / w := by
  have hD := abs_DM_ge hχ0 hξ hw
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hp0 : 0 ≤ pP ξ := by unfold pP; nlinarith
  have hp : pP ξ ≤ ξ ^ 2 := by unfold pP; linarith
  have hD0 : 0 < |DM c χ w ξ| := lt_of_lt_of_le (by positivity) hD
  rw [abs_div, abs_of_nonneg hp0, div_le_div_iff₀ hD0 hw0]
  nlinarith

/-- `|ξ²/D| ≤ 4/w`. -/
theorem abs_sqdivD_le {c χ w ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w) :
    |ξ ^ 2 / DM c χ w ξ| ≤ 4 / w := by
  have hD := abs_DM_ge hχ0 hξ hw
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hD0 : 0 < |DM c χ w ξ| := lt_of_lt_of_le (by positivity) hD
  rw [abs_div, abs_of_nonneg (sq_nonneg ξ), div_le_div_iff₀ hD0 hw0]
  nlinarith

theorem DM_sq_ge {c χ w ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w) :
    (ξ ^ 2 * w / 4) ^ 2 ≤ DM c χ w ξ ^ 2 := by
  have hD := abs_DM_ge hχ0 hξ hw
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  rw [← sq_abs (DM c χ w ξ)]; exact pow_le_pow_left₀ (by positivity) hD 2

/-- `|α| ≤ 32c²ξ/w²` for `χ ≤ c²`. -/
theorem abs_alphaM_le_hi {c χ w ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (hξ : 2 ≤ ξ)
    (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w) :
    |alphaM c χ w ξ| ≤ 32 * c ^ 2 * ξ / w ^ 2 := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hξ0 : 0 < ξ := by linarith
  have hp : 3 * ξ ^ 2 / 4 ≤ pP ξ := by unfold pP; nlinarith
  have hp' : pP ξ ≤ ξ ^ 2 := by unfold pP; linarith
  have hp1 : 1 ≤ pP ξ := by nlinarith
  have hnum : |c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ)| ≤ c ^ 2 * ξ ^ 4 := by
    have hpp : 1 ≤ pP ξ ^ 2 := one_le_pow₀ hp1
    have h1 : c ^ 2 - χ ≤ c ^ 2 * pP ξ ^ 2 := by nlinarith
    have h2 : c ^ 2 * pP ξ ^ 2 ≤ c ^ 2 * ξ ^ 4 := by
      have : pP ξ ^ 2 ≤ (ξ ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hp' 2
      nlinarith
    rw [abs_of_nonneg (by linarith)]; linarith
  have hD2 := DM_sq_ge hc hχ0 hξ hw
  have hDp : 0 < DM c χ w ξ ^ 2 := lt_of_lt_of_le (by positivity) hD2
  have hn : |-(2 * ξ * (c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ)))| ≤ 2 * ξ * (c ^ 2 * ξ ^ 4) := by
    rw [abs_neg, abs_mul, abs_mul, abs_two, abs_of_pos hξ0]
    exact mul_le_mul_of_nonneg_left hnum (by positivity)
  unfold alphaM
  rw [abs_div, abs_of_pos hDp, div_le_div_iff₀ hDp (by positivity)]
  calc |-(2 * ξ * (c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ)))| * w ^ 2 ≤ 2 * ξ * (c ^ 2 * ξ ^ 4) * w ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg w)
    _ = 32 * c ^ 2 * ξ * (ξ ^ 2 * w / 4) ^ 2 := by ring
    _ ≤ 32 * c ^ 2 * ξ * DM c χ w ξ ^ 2 := mul_le_mul_of_nonneg_left hD2 (by positivity)

/-- `|β| ≤ 32/(ξw)`. -/
theorem abs_betaM_le_hi {c χ w ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w) :
    |betaM c χ w ξ| ≤ 32 / (ξ * w) := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hξ0 : 0 < ξ := by linarith
  have hξ2 : 4 ≤ ξ ^ 2 := by nlinarith
  have hnum : |c ^ 2 * ξ ^ 4 - w| ≤ ξ ^ 2 * w := by
    have h1 : c ^ 2 * ξ ^ 4 ≤ ξ ^ 2 * w / 2 := by
      have := mul_le_mul_of_nonneg_left hw (sq_nonneg ξ)
      nlinarith
    have h2 : w ≤ ξ ^ 2 * w / 2 := by nlinarith
    have h3 : 0 ≤ c ^ 2 * ξ ^ 4 := by positivity
    rw [abs_le]; constructor <;> linarith
  have hD2 := DM_sq_ge hc hχ0 hξ hw
  have hDp : 0 < DM c χ w ξ ^ 2 := lt_of_lt_of_le (by positivity) hD2
  have hn : |-(2 * ξ * (c ^ 2 * ξ ^ 4 - w))| ≤ 2 * ξ * (ξ ^ 2 * w) := by
    rw [abs_neg, abs_mul, abs_mul, abs_two, abs_of_pos hξ0]
    exact mul_le_mul_of_nonneg_left hnum (by positivity)
  unfold betaM
  rw [abs_div, abs_of_pos hDp, div_le_div_iff₀ hDp (by positivity)]
  calc |-(2 * ξ * (c ^ 2 * ξ ^ 4 - w))| * (ξ * w) ≤ 2 * ξ * (ξ ^ 2 * w) * (ξ * w) :=
        mul_le_mul_of_nonneg_right hn (by positivity)
    _ = 32 * (ξ ^ 2 * w / 4) ^ 2 := by ring
    _ ≤ 32 * DM c χ w ξ ^ 2 := mul_le_mul_of_nonneg_left hD2 (by norm_num)

/-! ### The boundary and bulk terms against the energy -/

/-- `(3/4)cξ² ≤ a = √(pq) ≤ cξ²` for `0 ≤ χ ≤ c²`, `ξ ≥ 2`. -/
theorem aP_bounds {c χ ξ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2) (hξ : 2 ≤ ξ) :
    3 / 4 * c * ξ ^ 2 ≤ aP c χ ξ ∧ aP c χ ξ ≤ c * ξ ^ 2 := by
  have hξ2 : 4 ≤ ξ ^ 2 := by nlinarith
  have hp : 3 * ξ ^ 2 / 4 ≤ pP ξ := by unfold pP; nlinarith
  have hp' : pP ξ ≤ ξ ^ 2 := by unfold pP; linarith
  have hq : 3 * c ^ 2 * ξ ^ 2 / 4 ≤ qP c χ ξ := by unfold qP; nlinarith [sq_nonneg c]
  have hq' : qP c χ ξ ≤ c ^ 2 * ξ ^ 2 := by unfold qP; linarith
  have hq0 : 0 ≤ qP c χ ξ := le_trans (by positivity) hq
  unfold aP
  constructor
  · rw [Real.le_sqrt (by positivity) (mul_nonneg (by linarith) hq0)]
    have := mul_le_mul hp hq (by positivity) (by linarith)
    nlinarith
  · rw [Real.sqrt_le_left (by positivity)]
    have := mul_le_mul hp' hq' hq0 (by positivity)
    nlinarith

/-- The boundary bracket: `A²ξw/a + |AB|/2 + B²a/ξ ≤ 32/(cξw)` for `|A|, |B| ≤ 4/w`. -/
theorem bracket_bdry_le {c ξ w a A B : ℝ} (hc : 1 ≤ c) (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w)
    (ha : 3 / 4 * c * ξ ^ 2 ≤ a) (ha' : a ≤ c * ξ ^ 2) (hA : |A| ≤ 4 / w) (hB : |B| ≤ 4 / w) :
    A ^ 2 * (ξ * w) / a + |A * B| / 2 + B ^ 2 * a / ξ ≤ 32 / (c * ξ * w) := by
  have hc0 : 0 < c := by linarith
  have hξ0 : 0 < ξ := by linarith
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hAw : |A| * w ≤ 4 := by rw [le_div_iff₀ hw0] at hA; exact hA
  have hBw : |B| * w ≤ 4 := by rw [le_div_iff₀ hw0] at hB; exact hB
  have hA2 : A ^ 2 * w ^ 2 ≤ 16 := by
    have := pow_le_pow_left₀ (by positivity) hAw 2
    rw [mul_pow, sq_abs] at this; linarith
  have hB2 : B ^ 2 * w ^ 2 ≤ 16 := by
    have := pow_le_pow_left₀ (by positivity) hBw 2
    rw [mul_pow, sq_abs] at this; linarith
  have hAB : |A * B| * w ^ 2 ≤ 16 := by
    rw [abs_mul]
    have := mul_le_mul hAw hBw (by positivity) (by norm_num)
    nlinarith
  have hcξ : 4 * c * ξ ≤ w := by nlinarith
  have t1 : A ^ 2 * (ξ * w) / a ≤ 64 / 3 / (c * ξ * w) := by
    rw [div_le_div_iff₀ ha0 (by positivity)]
    have : A ^ 2 * (ξ * w) * (c * ξ * w) = (A ^ 2 * w ^ 2) * (c * ξ ^ 2) := by ring
    rw [this]
    nlinarith
  have t2 : |A * B| / 2 ≤ 2 / (c * ξ * w) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have h1 : |A * B| * (c * ξ * w) * w ≤ 4 * w := by
      have e : |A * B| * (c * ξ * w) * w = (|A * B| * w ^ 2) * (c * ξ) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hAB (show 0 ≤ c * ξ by positivity)
      linarith
    have := le_of_mul_le_mul_right h1 hw0
    linarith
  have t3 : B ^ 2 * a / ξ ≤ 8 / (c * ξ * w) := by
    rw [div_le_div_iff₀ hξ0 (by positivity)]
    have h1 : B ^ 2 * a * (c * ξ * w) * w ≤ 8 * ξ * w := by
      have e : B ^ 2 * a * (c * ξ * w) * w = (B ^ 2 * w ^ 2) * (a * (c * ξ)) := by ring
      rw [e]
      have h2 := mul_le_mul_of_nonneg_right hB2 (show 0 ≤ a * (c * ξ) by positivity)
      have h3 : 16 * (a * (c * ξ)) ≤ 16 * (c * ξ ^ 2 * (c * ξ)) := by
        have : 0 ≤ c * ξ := by positivity
        nlinarith
      have h4 : 16 * (c * ξ ^ 2 * (c * ξ)) ≤ 8 * ξ * w := by
        have := mul_le_mul_of_nonneg_left hw (show 0 ≤ 8 * ξ by positivity)
        nlinarith
      linarith
    exact le_of_mul_le_mul_right h1 hw0
  have e : (64 / 3 + 2 + 8 : ℝ) / (c * ξ * w) ≤ 32 / (c * ξ * w) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have e2 : 64 / 3 / (c * ξ * w) + 2 / (c * ξ * w) + 8 / (c * ξ * w) = (64 / 3 + 2 + 8 : ℝ) / (c * ξ * w) := by
    ring
  linarith

/-- The bulk bracket: `α²ξw/a + |αβ|/2 + β²a/ξ ≤ 920/(cξ³w)` for `|α| ≤ 32c²ξ/w²`, `|β| ≤ 32/(ξw)`. -/
theorem bracket_rem_le {c ξ w a A B : ℝ} (hc : 1 ≤ c) (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ w)
    (ha : 3 / 4 * c * ξ ^ 2 ≤ a) (ha' : a ≤ c * ξ ^ 2) (hA : |A| ≤ 32 * c ^ 2 * ξ / w ^ 2)
    (hB : |B| ≤ 32 / (ξ * w)) :
    A ^ 2 * (ξ * w) / a + |A * B| / 2 + B ^ 2 * a / ξ ≤ 920 / (c * ξ ^ 3 * w) := by
  have hc0 : 0 < c := by linarith
  have hξ0 : 0 < ξ := by linarith
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hAw : |A| * w ^ 2 ≤ 32 * c ^ 2 * ξ := by rw [le_div_iff₀ (by positivity)] at hA; exact hA
  have hBw : |B| * (ξ * w) ≤ 32 := by rw [le_div_iff₀ (by positivity)] at hB; exact hB
  have hA2 : A ^ 2 * w ^ 4 ≤ (32 * c ^ 2 * ξ) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hAw 2
    rw [mul_pow, sq_abs, ← pow_mul] at this; exact this
  have hB2 : B ^ 2 * (ξ * w) ^ 2 ≤ 32 ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hBw 2
    rw [mul_pow, sq_abs] at this; exact this
  have hAB : |A * B| * (w ^ 2 * (ξ * w)) ≤ 32 * c ^ 2 * ξ * 32 := by
    rw [abs_mul]
    have := mul_le_mul hAw hBw (by positivity) (by positivity)
    nlinarith
  have hw2 : 4 * c ^ 4 * ξ ^ 4 ≤ w ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hw 2
    nlinarith
  have hcξ : 2 ≤ c * ξ := by nlinarith
  have hw2p : 0 < w ^ 2 := by positivity
  -- term 1: `α²ξw/a ≤ (1024/3)/(cξ³w)`
  have t1 : A ^ 2 * (ξ * w) / a ≤ 1024 / 3 / (c * ξ ^ 3 * w) := by
    rw [div_le_div_iff₀ ha0 (by positivity)]
    have h1 : A ^ 2 * (ξ * w) * (c * ξ ^ 3 * w) * w ^ 2 ≤ 1024 / 3 * a * w ^ 2 := by
      have e : A ^ 2 * (ξ * w) * (c * ξ ^ 3 * w) * w ^ 2 = (A ^ 2 * w ^ 4) * (c * ξ ^ 4) := by ring
      rw [e]
      have h2 := mul_le_mul_of_nonneg_right hA2 (show 0 ≤ c * ξ ^ 4 by positivity)
      have h3 : (32 * c ^ 2 * ξ) ^ 2 * (c * ξ ^ 4) = 256 * (c * ξ ^ 2) * (4 * c ^ 4 * ξ ^ 4) := by ring
      have h4 : 256 * (c * ξ ^ 2) * (4 * c ^ 4 * ξ ^ 4) ≤ 256 * (c * ξ ^ 2) * w ^ 2 :=
        mul_le_mul_of_nonneg_left hw2 (by positivity)
      have h5 : 256 * (c * ξ ^ 2) * w ^ 2 ≤ 1024 / 3 * a * w ^ 2 := by
        have : 256 * (c * ξ ^ 2) ≤ 1024 / 3 * a := by linarith
        exact mul_le_mul_of_nonneg_right this (sq_nonneg w)
      linarith
    exact le_of_mul_le_mul_right h1 hw2p
  -- term 2: `|αβ|/2 ≤ 64/(cξ³w)`
  have t2 : |A * B| / 2 ≤ 64 / (c * ξ ^ 3 * w) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hpos : 0 < w ^ 2 * ξ := by positivity
    have h1 : |A * B| * (c * ξ ^ 3 * w) * (w ^ 2 * ξ) ≤ 64 * 2 * (w ^ 2 * ξ) := by
      have e : |A * B| * (c * ξ ^ 3 * w) * (w ^ 2 * ξ) = (|A * B| * (w ^ 2 * (ξ * w))) * (c * ξ ^ 3) := by ring
      rw [e]
      have h2 := mul_le_mul_of_nonneg_right hAB (show 0 ≤ c * ξ ^ 3 by positivity)
      have h3 : 32 * c ^ 2 * ξ * 32 * (c * ξ ^ 3) ≤ 128 * (4 * c ^ 4 * ξ ^ 4) * ξ := by
        have h0 : 0 ≤ c ^ 3 * ξ ^ 4 := by positivity
        have : 1024 * c ^ 3 * ξ ^ 4 ≤ 512 * c ^ 4 * ξ ^ 5 := by
          have := mul_le_mul_of_nonneg_left hcξ h0
          nlinarith
        nlinarith
      have h4 : 128 * (4 * c ^ 4 * ξ ^ 4) * ξ ≤ 64 * 2 * (w ^ 2 * ξ) := by
        have := mul_le_mul_of_nonneg_right hw2 (show 0 ≤ 64 * ξ by positivity)
        nlinarith
      linarith
    exact le_of_mul_le_mul_right h1 hpos
  -- term 3: `β²a/ξ ≤ 512/(cξ³w)`
  have t3 : B ^ 2 * a / ξ ≤ 512 / (c * ξ ^ 3 * w) := by
    rw [div_le_div_iff₀ hξ0 (by positivity)]
    have hpos : 0 < ξ ^ 2 * w := by positivity
    have h1 : B ^ 2 * a * (c * ξ ^ 3 * w) * (ξ ^ 2 * w) ≤ 512 * ξ * (ξ ^ 2 * w) := by
      have e : B ^ 2 * a * (c * ξ ^ 3 * w) * (ξ ^ 2 * w) = (B ^ 2 * (ξ * w) ^ 2) * (a * (c * ξ ^ 3)) := by ring
      rw [e]
      have h2 := mul_le_mul_of_nonneg_right hB2 (show 0 ≤ a * (c * ξ ^ 3) by positivity)
      have h3 : 32 ^ 2 * (a * (c * ξ ^ 3)) ≤ 32 ^ 2 * (c * ξ ^ 2 * (c * ξ ^ 3)) := by
        have : 0 ≤ c * ξ ^ 3 := by positivity
        nlinarith
      have h4 : 32 ^ 2 * (c * ξ ^ 2 * (c * ξ ^ 3)) ≤ 512 * ξ * (ξ ^ 2 * w) := by
        have := mul_le_mul_of_nonneg_left hw (show 0 ≤ 512 * ξ ^ 3 by positivity)
        nlinarith
      linarith
    exact le_of_mul_le_mul_right h1 hpos
  have e2 : 1024 / 3 / (c * ξ ^ 3 * w) + 64 / (c * ξ ^ 3 * w) + 512 / (c * ξ ^ 3 * w)
      = (1024 / 3 + 64 + 512 : ℝ) / (c * ξ ^ 3 * w) := by ring
  have e : (1024 / 3 + 64 + 512 : ℝ) / (c * ξ ^ 3 * w) ≤ 920 / (c * ξ ^ 3 * w) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

/-- **The boundary term above the orbit frequency**: `‖B(ξ)‖² ≤ 32E(ξ)/(cξw)`. -/
theorem norm_bdryC_sq_le_hi {c χ t ξ : ℝ} (ψ u : ℝ → ℝ) (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ t ^ 2 + 1 / 4) :
    ‖bdryC c χ t ψ u ξ‖ ^ 2 ≤ energy (aP c χ) ψ u ξ * (32 / (c * ξ * (t ^ 2 + 1 / 4))) := by
  have hc0 : 0 < c := by linarith
  have hξ0 : 0 < ξ := by linarith
  obtain ⟨ha, ha'⟩ := aP_bounds hc0 hχ0 hχ hξ
  have ha0 : 0 < aP c χ ξ := lt_of_lt_of_le (by positivity) ha
  have h := norm_pair_sq_le (a := aP c χ) (ψ := ψ) (u := u) t (pP ξ / DM c χ (t ^ 2 + 1 / 4) ξ)
    (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ) hξ0 ha0
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ := by unfold energy; positivity
  unfold bdryC
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hE0)
  exact bracket_bdry_le hc hξ hw ha ha' (abs_pdivD_le hc0 hχ0 hξ hw) (abs_sqdivD_le hc0 hχ0 hξ hw)

/-- **The bulk density above the orbit frequency**: `‖ρ(ξ)‖² ≤ 920E(ξ)/(cξ³w)`. -/
theorem norm_remDens_sq_le_hi {c χ t ξ : ℝ} (ψ u : ℝ → ℝ) (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hξ : 2 ≤ ξ) (hw : 2 * c ^ 2 * ξ ^ 2 ≤ t ^ 2 + 1 / 4) :
    ‖remDens c χ t ψ u ξ‖ ^ 2 ≤ energy (aP c χ) ψ u ξ * (920 / (c * ξ ^ 3 * (t ^ 2 + 1 / 4))) := by
  have hc0 : 0 < c := by linarith
  have hξ0 : 0 < ξ := by linarith
  obtain ⟨ha, ha'⟩ := aP_bounds hc0 hχ0 hχ hξ
  have ha0 : 0 < aP c χ ξ := lt_of_lt_of_le (by positivity) ha
  have h := norm_pair_sq_le (a := aP c χ) (ψ := ψ) (u := u) t (alphaM c χ (t ^ 2 + 1 / 4) ξ)
    (betaM c χ (t ^ 2 + 1 / 4) ξ) hξ0 ha0
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ := by unfold energy; positivity
  unfold remDens
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hE0)
  exact bracket_rem_le hc hξ hw ha ha' (abs_alphaM_le_hi hc0 hχ0 hχ hξ hw) (abs_betaM_le_hi hc0 hχ0 hξ hw)

/-! ### One mode above the orbit frequency -/

/-- `(−2/√ξ)′ = 1/(ξ√ξ)` for `ξ > 0`. -/
theorem hasDerivAt_neg_two_inv_sqrt {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun x => -2 * (√x)⁻¹) (1 / (ξ * √ξ)) ξ := by
  have hs : 0 < √ξ := Real.sqrt_pos.mpr hξ
  have h := ((Real.hasDerivAt_sqrt hξ.ne').inv hs.ne').const_mul (-2 : ℝ)
  refine h.congr_deriv ?_
  have hss : √ξ * √ξ = ξ := Real.mul_self_sqrt hξ.le
  field_simp
  nlinarith [hss]

/-- `∫_s^X dξ/(ξ√ξ) ≤ 2/√s` for `0 < s ≤ X`. -/
theorem integral_inv_mul_sqrt_le {s X : ℝ} (hs : 0 < s) (hsX : s ≤ X) :
    ∫ ξ in s..X, 1 / (ξ * √ξ) ≤ 2 / √s := by
  have hpos : ∀ x ∈ uIcc s X, 0 < x := fun x hx => by rw [uIcc_of_le hsX] at hx; linarith [hx.1]
  have hc : ContinuousOn (fun ξ : ℝ => 1 / (ξ * √ξ)) (uIcc s X) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_id.mul continuous_sqrt.continuousOn) ?_
    intro x hx; have := hpos x hx; exact mul_ne_zero this.ne' (Real.sqrt_pos.mpr this).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_neg_two_inv_sqrt (hpos x hx))
    hc.intervalIntegrable]
  have hX0 : 0 < X := lt_of_lt_of_le hs hsX
  have : 0 ≤ (√X)⁻¹ := by positivity
  have e : -2 * (√X)⁻¹ - -2 * (√s)⁻¹ = 2 / √s - 2 * (√X)⁻¹ := by ring
  rw [e]; linarith

theorem sqrt_32_le : √(32 : ℝ) ≤ 6 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem sqrt_920_le : √(920 : ℝ) ≤ 31 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- **One mode above the orbit frequency**: for `2 ≤ s ≤ X`, `c ≥ 1`, `0 ≤ χ ≤ c²`, `2c²X² ≤ w = t² + ¼` and a rung
pair on `[s, X]` with energy at most `Ē`, `‖I(s, X; t)‖ ≤ 74√(Ē/(cw))/√s`. -/
theorem norm_mellinI_le_hi {c χ s X t Ebar : ℝ} {ψ u : ℝ → ℝ} (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hs : 2 ≤ s) (hsX : s ≤ X) (hw : 2 * c ^ 2 * X ^ 2 ≤ t ^ 2 + 1 / 4)
    (hψ : ∀ ξ ∈ Icc s X, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc s X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hE : ∀ ξ ∈ Icc s X, energy (aP c χ) ψ u ξ ≤ Ebar) :
    ‖Cvs.L2a.FarPartDirichletSplit.mellinI ψ s X t‖ ≤ 74 * √(Ebar / (c * (t ^ 2 + 1 / 4))) / √s := by
  set w := t ^ 2 + 1 / 4 with hwd
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < s := by linarith
  have hw0 : 0 < w := by positivity
  have hwξ : ∀ ξ ∈ Icc s X, 2 * c ^ 2 * ξ ^ 2 ≤ w := fun ξ hξ => by
    have : ξ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by linarith [hξ.1]) hξ.2 2
    nlinarith [sq_nonneg c]
  have hξ2 : ∀ ξ ∈ Icc s X, 2 ≤ ξ := fun ξ hξ => le_trans hs hξ.1
  have hD : ∀ ξ ∈ Icc s X, DM c χ w ξ ≠ 0 := fun ξ hξ => DM_ne hc0 hχ0 (hξ2 ξ hξ) (hwξ ξ hξ)
  rw [mellinI_eq_green_ne (by linarith) hsX hD hψ hu]
  have hE0 : ∀ ξ ∈ Icc s X, 0 ≤ energy (aP c χ) ψ u ξ := fun ξ _ => by unfold energy aP; positivity
  have hEb : 0 ≤ Ebar := le_trans (hE0 s ⟨le_rfl, hsX⟩) (hE s ⟨le_rfl, hsX⟩)
  set S := √(Ebar / (c * w)) with hSd
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  -- the boundary terms
  have hB : ∀ ξ ∈ Icc s X, ‖bdryC c χ t ψ u ξ‖ ≤ 6 * S / √ξ := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ2 ξ hξ]
    have h := norm_bdryC_sq_le_hi ψ u hc hχ0 hχ (hξ2 ξ hξ) (hwξ ξ hξ)
    have h2 : energy (aP c χ) ψ u ξ * (32 / (c * ξ * w)) ≤ Ebar * (32 / (c * ξ * w)) :=
      mul_le_mul_of_nonneg_right (hE ξ hξ) (by positivity)
    have e : Ebar * (32 / (c * ξ * w)) = (√32 * S / √ξ) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), hSd, Real.sq_sqrt (by positivity), Real.sq_sqrt hξ0.le]
      field_simp
    have hsq : ‖bdryC c χ t ψ u ξ‖ ^ 2 ≤ (√32 * S / √ξ) ^ 2 := by linarith
    have h3 := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
    refine h3.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    exact mul_le_mul_of_nonneg_right sqrt_32_le hS0
  -- the bulk term
  have hR : ∀ ξ ∈ Icc s X, ‖remDens c χ t ψ u ξ‖ ≤ 31 * S * (1 / (ξ * √ξ)) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ2 ξ hξ]
    have h := norm_remDens_sq_le_hi ψ u hc hχ0 hχ (hξ2 ξ hξ) (hwξ ξ hξ)
    have h2 : energy (aP c χ) ψ u ξ * (920 / (c * ξ ^ 3 * w)) ≤ Ebar * (920 / (c * ξ ^ 3 * w)) :=
      mul_le_mul_of_nonneg_right (hE ξ hξ) (by positivity)
    have e : Ebar * (920 / (c * ξ ^ 3 * w)) = (√920 * S * (1 / (ξ * √ξ))) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), hSd, Real.sq_sqrt (by positivity), div_pow, mul_pow,
        Real.sq_sqrt hξ0.le]
      field_simp
    have hsq : ‖remDens c χ t ψ u ξ‖ ^ 2 ≤ (√920 * S * (1 / (ξ * √ξ))) ^ 2 := by linarith
    have h3 := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
    refine h3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right sqrt_920_le hS0) (by positivity))
  have hgi : IntervalIntegrable (fun ξ => 31 * S * (1 / (ξ * √ξ))) MeasureTheory.volume s X := by
    refine ContinuousOn.intervalIntegrable_of_Icc hsX (continuousOn_const.mul ?_)
    refine ContinuousOn.div continuousOn_const (continuousOn_id.mul continuous_sqrt.continuousOn) ?_
    intro x hx; have : 0 < x := by linarith [hx.1]
    exact mul_ne_zero this.ne' (Real.sqrt_pos.mpr this).ne'
  have hI := intervalIntegral.norm_integral_le_of_norm_le hsX
    (Filter.Eventually.of_forall fun ξ hξ => hR ξ ⟨hξ.1.le, hξ.2⟩) hgi
  rw [intervalIntegral.integral_const_mul] at hI
  have hI2 := integral_inv_mul_sqrt_le hs0 hsX
  have hIb : ‖∫ ξ in s..X, remDens c χ t ψ u ξ‖ ≤ 62 * S / √s := by
    calc _ ≤ _ := hI
      _ ≤ 31 * S * (2 / √s) := mul_le_mul_of_nonneg_left hI2 (by positivity)
      _ = 62 * S / √s := by ring
  have hBX := hB X ⟨hsX, le_rfl⟩
  have hBs := hB s ⟨le_rfl, hsX⟩
  have hXs : 6 * S / √X ≤ 6 * S / √s :=
    div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hs0) (Real.sqrt_le_sqrt hsX)
  calc ‖bdryC c χ t ψ u X - bdryC c χ t ψ u s - ∫ ξ in s..X, remDens c χ t ψ u ξ‖
      ≤ ‖bdryC c χ t ψ u X‖ + ‖bdryC c χ t ψ u s‖ + ‖∫ ξ in s..X, remDens c χ t ψ u ξ‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 6 * S / √s + 6 * S / √s + 62 * S / √s := by linarith
    _ = 74 * S / √s := by ring

end Cvs.Prolate.GreenIdentityAboveOrbitFreq
