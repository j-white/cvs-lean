import Mathlib
import Cvs.L2a.FarPartDirichletSplit
import Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.OrbitGapGreenIdentity
import Cvs.Prolate.RungConnectionIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Lemma G in complex form and the boundary bound

With `w = t² + ¼`, `u_t y_t + ũ_t ỹ_t = −½` gives `‖Pv − Qy‖² = P²ξw + PQ + Q²/ξ`; Cvs.Prolate.Mellin.OrbitGapGreenIdentity reads
`I(s, X; t) = B(X) − B(s) − ∫_s^X ρ`, and on `ξ ≥ 2`, `w ≤ r c²ξ²`, `r < 1`: `‖B‖² ≤ β²·E/(c³ξ³)` (Lemma B).
-/
namespace Cvs.Prolate.Mellin.GreenBoundaryBound

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.MellinKernelSturmLiouville Cvs.Prolate.Mellin.OrbitGapGreenIdentity

/-- `u_t y_t + ũ_t ỹ_t = −1/2` for `ξ > 0`. -/
theorem ku_mul_ky_add_kus_mul_kys (t : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ku t ξ * ky t ξ + kus t ξ * kys t ξ = -1 / 2 := by
  unfold ku ky kus kys
  have hs : √ξ ≠ 0 := (Real.sqrt_pos.mpr hξ).ne'
  have h := sin_sq_add_cos_sq (t * Real.log ξ)
  field_simp
  linear_combination (-1 : ℝ) * h

/-- **The kernel pair**: `‖(P u_t − Q y_t) − i(P ũ_t − Q ỹ_t)‖² = P²ξ(t² + ¼) + PQ + Q²/ξ` for `ξ > 0`. -/
theorem norm_pair_sq (t P Q : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ‖((P * ku t ξ - Q * ky t ξ : ℝ) : ℂ) - Complex.I * ((P * kus t ξ - Q * kys t ξ : ℝ) : ℂ)‖ ^ 2
      = P ^ 2 * (ξ * (t ^ 2 + 1 / 4)) + P * Q + Q ^ 2 / ξ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.sub_im, Complex.mul_im]
  have h1 := ku_sq_add_kus_sq (t := t) hξ
  have h2 := ky_sq_add_kys_sq (t := t) hξ
  have h3 := ku_mul_ky_add_kus_mul_kys t hξ
  linear_combination P ^ 2 * h1 + Q ^ 2 * h2 - 2 * P * Q * h3

/-- **The pair against the energy**: for `a ξ > 0` and `E = aψ² + u²/a` at `ξ`, the kernel pair of `Aψ` and `Bu`
has `‖·‖² ≤ E(A²ξw/a + |AB|/2 + B²a/ξ)`, `w = t² + ¼` (`PointwiseEnergyEnvelopes`'s envelopes and `LiouvilleGreenEnergyExact`'s `2|ψu| ≤ E`). -/
theorem norm_pair_sq_le (t A B : ℝ) {ξ : ℝ} {a ψ u : ℝ → ℝ} (hξ : 0 < ξ) (ha : 0 < a ξ) :
    ‖((A * (ψ ξ * ku t ξ) - B * (u ξ * ky t ξ) : ℝ) : ℂ)
        - Complex.I * ((A * (ψ ξ * kus t ξ) - B * (u ξ * kys t ξ) : ℝ) : ℂ)‖ ^ 2
      ≤ energy a ψ u ξ * (A ^ 2 * (ξ * (t ^ 2 + 1 / 4)) / a ξ + |A * B| / 2 + B ^ 2 * a ξ / ξ) := by
  have e1 : A * (ψ ξ * ku t ξ) - B * (u ξ * ky t ξ) = (A * ψ ξ) * ku t ξ - (B * u ξ) * ky t ξ := by ring
  have e2 : A * (ψ ξ * kus t ξ) - B * (u ξ * kys t ξ) = (A * ψ ξ) * kus t ξ - (B * u ξ) * kys t ξ := by ring
  rw [e1, e2, norm_pair_sq t (A * ψ ξ) (B * u ξ) hξ]
  set E := energy a ψ u ξ
  have hψ : ψ ξ ^ 2 ≤ E / a ξ := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.sq_le_energy_div ha
  have hu : u ξ ^ 2 ≤ a ξ * E := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.flux_sq_le ha
  have hψu : 2 * |ψ ξ * u ξ| ≤ E := two_mul_abs_le_energy ha
  have t1 : (A * ψ ξ) ^ 2 * (ξ * (t ^ 2 + 1 / 4)) ≤ E * (A ^ 2 * (ξ * (t ^ 2 + 1 / 4)) / a ξ) := by
    have : (A * ψ ξ) ^ 2 * (ξ * (t ^ 2 + 1 / 4)) = A ^ 2 * (ξ * (t ^ 2 + 1 / 4)) * ψ ξ ^ 2 := by ring
    rw [this]
    calc A ^ 2 * (ξ * (t ^ 2 + 1 / 4)) * ψ ξ ^ 2 ≤ A ^ 2 * (ξ * (t ^ 2 + 1 / 4)) * (E / a ξ) :=
          mul_le_mul_of_nonneg_left hψ (by positivity)
      _ = _ := by ring
  have t2 : A * ψ ξ * (B * u ξ) ≤ E * (|A * B| / 2) := by
    have h0 : A * ψ ξ * (B * u ξ) ≤ |A * B| * |ψ ξ * u ξ| := by
      calc A * ψ ξ * (B * u ξ) = (A * B) * (ψ ξ * u ξ) := by ring
        _ ≤ |(A * B) * (ψ ξ * u ξ)| := le_abs_self _
        _ = _ := abs_mul _ _
    have : |A * B| * |ψ ξ * u ξ| ≤ |A * B| * (E / 2) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    linarith
  have t3 : (B * u ξ) ^ 2 / ξ ≤ E * (B ^ 2 * a ξ / ξ) := by
    have : (B * u ξ) ^ 2 / ξ = B ^ 2 / ξ * u ξ ^ 2 := by ring
    rw [this]
    calc B ^ 2 / ξ * u ξ ^ 2 ≤ B ^ 2 / ξ * (a ξ * E) := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = _ := by ring
  nlinarith

/-- The complex boundary term `(p/D)ψ·(u_t − iũ_t) − (ξ²/D)u·(y_t − iỹ_t)` of Lemma G at `ξ`, `w = t² + ¼`. -/
noncomputable def bdryC (c χ t : ℝ) (ψ u : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ((pP ξ / DM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * ku t ξ) - ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * ky t ξ) : ℝ) : ℂ)
    - Complex.I * ((pP ξ / DM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * kus t ξ)
        - ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * kys t ξ) : ℝ) : ℂ)

/-- The complex bulk integrand `αψ·(u_t − iũ_t) − βu·(y_t − iỹ_t)` of Lemma G at `ξ`. -/
noncomputable def remDens (c χ t : ℝ) (ψ u : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ((alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * ku t ξ) - betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * ky t ξ) : ℝ) : ℂ)
    - Complex.I * ((alphaM c χ (t ^ 2 + 1 / 4) ξ * (ψ ξ * kus t ξ)
        - betaM c χ (t ^ 2 + 1 / 4) ξ * (u ξ * kys t ξ) : ℝ) : ℂ)

/-- `α` is continuous on `[s, X]` where `D > 0`. -/
theorem continuousOn_alphaM {c χ w s X : ℝ} (hD : ∀ ξ ∈ Icc s X, 0 < DM c χ w ξ) :
    ContinuousOn (alphaM c χ w) (Icc s X) := by
  have hn : Continuous fun ξ : ℝ => -(2 * ξ * (c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ))) := by
    unfold pP; fun_prop
  exact ContinuousOn.div (f := fun ξ : ℝ => -(2 * ξ * (c ^ 2 * pP ξ ^ 2 - (c ^ 2 - χ))))
    (g := fun ξ => DM c χ w ξ ^ 2) hn.continuousOn ((continuous_DM c χ w).pow 2).continuousOn
    fun ξ hξ => pow_ne_zero 2 (hD ξ hξ).ne'

/-- `β` is continuous on `[s, X]` where `D > 0`. -/
theorem continuousOn_betaM {c χ w s X : ℝ} (hD : ∀ ξ ∈ Icc s X, 0 < DM c χ w ξ) :
    ContinuousOn (betaM c χ w) (Icc s X) := by
  have hn : Continuous fun ξ : ℝ => -(2 * ξ * (c ^ 2 * ξ ^ 4 - w)) := by fun_prop
  exact ContinuousOn.div (f := fun ξ : ℝ => -(2 * ξ * (c ^ 2 * ξ ^ 4 - w)))
    (g := fun ξ => DM c χ w ξ ^ 2) hn.continuousOn ((continuous_DM c χ w).pow 2).continuousOn
    fun ξ hξ => pow_ne_zero 2 (hD ξ hξ).ne'

/-- **Lemma G, complex form**: `I(s, X; t) = B(X) − B(s) − ∫_s^X ρ` for a rung pair on `[s, X]`, `1 < s`, `D > 0`. -/
theorem mellinI_eq_green {c χ s X t : ℝ} {ψ u : ℝ → ℝ} (hs : 1 < s) (hsX : s ≤ X)
    (hD : ∀ ξ ∈ Icc s X, 0 < DM c χ (t ^ 2 + 1 / 4) ξ)
    (hψ : ∀ ξ ∈ Icc s X, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc s X, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) :
    Cvs.L2a.FarPartDirichletSplit.mellinI ψ s X t
      = bdryC c χ t ψ u X - bdryC c χ t ψ u s - ∫ ξ in s..X, remDens c χ t ψ u ξ := by
  have hcos := mellin_green_cos hs hsX hD hψ hu
  have hsin := mellin_green_sin hs hsX hD hψ hu
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
  have hα := continuousOn_alphaM hD
  have hβ := continuousOn_betaM hD
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

/-- The boundary constant `β² = (16/9 + 4r/3 + 1/(3c))/(1 − r)²`. -/
noncomputable def betaSq (c r : ℝ) : ℝ := (16 / 9 + 4 / 3 * r + 1 / (3 * c)) / (1 - r) ^ 2

/-- The coefficient bound behind Lemma B: with `D ≥ p c²ξ²(1 − r)`, `cp ≤ a ≤ cξ²`, `w ≤ r c²ξ²`, `ξ ≥ 2`. -/
theorem bdry_coeff_le {c r ξ p D a w : ℝ} (hc : 0 < c) (hξ : 2 ≤ ξ) (hr : r < 1)
    (hp : 3 / 4 * ξ ^ 2 ≤ p) (hD : p * (c ^ 2 * ξ ^ 2) * (1 - r) ≤ D) (haL : c * p ≤ a) (haU : a ≤ c * ξ ^ 2)
    (hw0 : 0 ≤ w) (hw : w ≤ r * (c ^ 2 * ξ ^ 2)) :
    (p / D) ^ 2 * (ξ * w) / a + |p / D * (ξ ^ 2 / D)| / 2 + (ξ ^ 2 / D) ^ 2 * a / ξ
      ≤ betaSq c r / (c ^ 3 * ξ ^ 3) := by
  have hξ0 : 0 < ξ := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hL0 : 0 < p * (c ^ 2 * ξ ^ 2) * (1 - r) := by positivity
  have hD0 : 0 < D := lt_of_lt_of_le hL0 hD
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) haL
  have hr0 : 0 ≤ r := by
    by_contra h; push Not at h
    have : r * (c ^ 2 * ξ ^ 2) < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith
  set K := c ^ 2 * ξ ^ 2 * (1 - r) with hK
  have hK0 : 0 < K := by positivity
  -- `p/D ≤ 1/K` and `ξ²/D ≤ (4/3)/K`
  have hA : p / D ≤ 1 / K := by
    rw [div_le_div_iff₀ hD0 hK0]; nlinarith
  have hB : ξ ^ 2 / D ≤ 4 / 3 / K := by
    rw [div_le_div_iff₀ hD0 hK0]
    have : ξ ^ 2 * K ≤ 4 / 3 * (p * (c ^ 2 * ξ ^ 2) * (1 - r)) := by
      rw [hK]; have := mul_le_mul_of_nonneg_right hp (le_of_lt (by positivity : 0 < c ^ 2 * ξ ^ 2 * (1 - r)))
      nlinarith
    nlinarith
  have hA0 : 0 ≤ p / D := by positivity
  have hB0 : 0 ≤ ξ ^ 2 / D := by positivity
  -- `ξw/a ≤ (4/3) r c ξ` and `a/ξ ≤ cξ`
  have hwa : ξ * w / a ≤ 4 / 3 * r * c * ξ := by
    rw [div_le_iff₀ ha0]
    have h1 : ξ * w ≤ ξ * (r * (c ^ 2 * ξ ^ 2)) := mul_le_mul_of_nonneg_left hw hξ0.le
    have h2 : 4 / 3 * r * c * ξ * (c * (3 / 4 * ξ ^ 2)) ≤ 4 / 3 * r * c * ξ * a := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    nlinarith
  have haξ : a / ξ ≤ c * ξ := by
    rw [div_le_iff₀ hξ0]; nlinarith
  have t1 : (p / D) ^ 2 * (ξ * w) / a ≤ (1 / K) ^ 2 * (4 / 3 * r * c * ξ) := by
    rw [mul_div_assoc]
    exact mul_le_mul (pow_le_pow_left₀ hA0 hA 2) hwa (by positivity) (by positivity)
  have t2 : |p / D * (ξ ^ 2 / D)| / 2 ≤ (1 / K) * (4 / 3 / K) / 2 := by
    rw [abs_of_nonneg (mul_nonneg hA0 hB0)]
    have := mul_le_mul hA hB hB0 (by positivity)
    linarith
  have t3 : (ξ ^ 2 / D) ^ 2 * a / ξ ≤ (4 / 3 / K) ^ 2 * (c * ξ) := by
    rw [mul_div_assoc]
    exact mul_le_mul (pow_le_pow_left₀ hB0 hB 2) haξ (by positivity) (by positivity)
  have hsum : (1 / K) ^ 2 * (4 / 3 * r * c * ξ) + (1 / K) * (4 / 3 / K) / 2 + (4 / 3 / K) ^ 2 * (c * ξ)
      ≤ betaSq c r / (c ^ 3 * ξ ^ 3) := by
    rw [hK, betaSq]
    have hc3 : 0 < c ^ 3 * ξ ^ 3 := by positivity
    rw [div_div, le_div_iff₀ (by positivity)]
    field_simp
    have hcx : 2 * c ≤ c * ξ := by nlinarith
    nlinarith [mul_pos hc hξ0, sq_nonneg (1 - r), mul_pos (mul_pos hc hξ0) h1r]
  linarith

/-- **Lemma B**: for `ξ ≥ 2`, `0 ≤ χ ≤ c²` and `t² + ¼ ≤ r c²ξ²` with `r < 1`, `‖B(ξ)‖² ≤ β²·E(ξ)/(c³ξ³)`. -/
theorem green_boundary_le {c χ r t ξ : ℝ} (ψ u : ℝ → ℝ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ c ^ 2)
    (hξ : 2 ≤ ξ) (hr : r < 1) (hw : t ^ 2 + 1 / 4 ≤ r * (c ^ 2 * ξ ^ 2)) :
    ‖bdryC c χ t ψ u ξ‖ ^ 2 ≤ betaSq c r * energy (aP c χ) ψ u ξ / (c ^ 3 * ξ ^ 3) := by
  have hξ0 : 0 < ξ := by linarith
  have hp : 3 / 4 * ξ ^ 2 ≤ pP ξ := by unfold pP; nlinarith
  have haL : c * pP ξ ≤ aP c χ ξ := Cvs.Prolate.RungConnectionIdentity.le_aP_far hχ (by linarith)
  have haU : aP c χ ξ ≤ c * ξ ^ 2 := Cvs.Prolate.Envelope.PointwiseEnergyEnvelopes.aP_le hc hχ0 (by linarith)
  have ha0 : 0 < aP c χ ξ := lt_of_lt_of_le (mul_pos hc (lt_of_lt_of_le (by positivity) hp)) haL
  have hD : pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r) ≤ DM c χ (t ^ 2 + 1 / 4) ξ := by
    have h := DM_ge (w := t ^ 2 + 1 / 4) hχ (by linarith : (1 : ℝ) ≤ ξ)
    have hp0 : 0 ≤ pP ξ := le_trans (by positivity) hp
    have : pP ξ * (c ^ 2 * ξ ^ 2) * (1 - r) ≤ pP ξ * (c ^ 2 * ξ ^ 2 - (t ^ 2 + 1 / 4)) := by
      have : c ^ 2 * ξ ^ 2 * (1 - r) ≤ c ^ 2 * ξ ^ 2 - (t ^ 2 + 1 / 4) := by nlinarith
      nlinarith
    linarith
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ := by unfold energy; positivity
  have key := bdry_coeff_le hc hξ hr hp hD haL haU (by positivity) hw
  have h := norm_pair_sq_le t (pP ξ / DM c χ (t ^ 2 + 1 / 4) ξ) (ξ ^ 2 / DM c χ (t ^ 2 + 1 / 4) ξ)
    (ψ := ψ) (u := u) hξ0 ha0
  unfold bdryC
  calc _ ≤ _ := h
    _ ≤ energy (aP c χ) ψ u ξ * (betaSq c r / (c ^ 3 * ξ ^ 3)) := mul_le_mul_of_nonneg_left key hE0
    _ = _ := by ring

end Cvs.Prolate.Mellin.GreenBoundaryBound
