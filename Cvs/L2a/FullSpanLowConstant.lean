import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandEdgeLowMass
import Cvs.L2a.EdgeCountSSums
import Cvs.L2a.FullSpanLowMass
import Cvs.L2a.LowConstantUniform
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanLowMass
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.Mellin.EdgeGreenIdentity
import Cvs.Prolate.Mellin.EdgeRemainderClosedForm
import Cvs.Prolate.Mellin.FarPartLevelBound
import Cvs.WeilForm.SelfConvolutionCosine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The full-span low constant uniformly in `c`

For `c ≥ 80`, `X ≥ 2`, `0 ≤ r ≤ r̄`: `C_M(c, X) ≤ C_M(80, 2)`, `c·LE(c, r, 5) ≤ 80·LE(80, r̄, 5)`, so
`Bnd(c, r, X) ≤ B̄`; with `K0 = κ(1 + log c)`, `κ ≥ 1`, `J ≤ c/4 + 1` this gives `η_P^full ≤ Ē_full/κ`, where
`Ē_full = ((√F̄ + 2√W̄ + √R̄₀ + √B̄)/√(1 + log 80) + √R̄₁)²/π`.
-/

namespace Cvs.L2a.FullSpanLowConstant

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.SpectralMassLevelLeak Cvs.Prolate.Mellin.EdgeGreenIdentity Cvs.Prolate.Mellin.EdgeRemainderClosedForm Cvs.Prolate.EdgeBesselCount Cvs.L2a.EdgeCountSSums Cvs.L2a.RungSpanLowMass Cvs.L2a.LowConstantUniform Cvs.L2a.BandEdgeLowMass Cvs.L2a.FullSpanLowMass
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- `C_M(c, X) ≤ C_M(80, 2)` for `c ≥ 80`, `X ≥ 2`. -/
theorem CM_le {c X : ℝ} (hc : 80 ≤ c) (hX : 2 ≤ X) : CM c X ≤ CM 80 2 := by
  have hc0 : 0 < c := by linarith
  have hp : 0 < X ^ 2 - 1 := by nlinarith
  set y := X / (c * (X ^ 2 - 1)) with hyd
  set y0 : ℝ := 2 / (80 * (2 ^ 2 - 1)) with hy0d
  have hy0v : y0 = 1 / 120 := by rw [hy0d]; norm_num
  have hy0 : 0 ≤ y := by positivity
  have hy : y ≤ y0 := by
    rw [hyd, hy0v, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X - 2) (by linarith : (0 : ℝ) ≤ 2 * X + 1)]
  have hfr : (1 + y) / (1 - 2 * y) ≤ (1 + y0) / (1 - 2 * y0) := by
    rw [hy0v] at hy ⊢
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hfr0 : 0 ≤ (1 + y) / (1 - 2 * y) := div_nonneg (by linarith) (by rw [hy0v] at hy; linarith)
  have hL0 : 0 ≤ Real.log ((X + 1) / (X - 1)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hL : Real.log ((X + 1) / (X - 1)) ≤ Real.log ((2 + 1) / (2 - 1)) :=
    Real.log_le_log (by apply div_pos <;> linarith)
      (by rw [div_le_iff₀ (by linarith)]; norm_num; linarith)
  have hy2 : 2 * X / (c * (X ^ 2 - 1)) = 2 * y := by rw [hyd]; ring
  have hy02 : (2 * 2 : ℝ) / (80 * (2 ^ 2 - 1)) = 2 * y0 := by rw [hy0d]; ring
  unfold CM
  rw [hy2, hy02, ← hyd, ← hy0d]
  have hfr0' : 0 ≤ (1 + y0) / (1 - 2 * y0) := hfr0.trans hfr
  have := mul_le_mul hfr hL hL0 hfr0'
  nlinarith

/-- `c·LE(c, r, 5) ≤ 80·LE(80, r̄, 5)` for `c ≥ 80`, `0 ≤ r ≤ r̄`. -/
theorem cLE_le {c r : ℝ} (hc : 80 ≤ c) (hr0 : 0 ≤ r) (hr : r ≤ rBar) :
    c * lemmaEBound c r 5 ≤ 80 * lemmaEBound 80 rBar 5 := by
  have hc0 : 0 < c := by linarith
  have hb := rBar_mem.2
  have h1r : 0 < 1 - r := by linarith
  have h1b : 0 < 1 - rBar := by linarith
  obtain ⟨he0, he, hI1, hI2⟩ := consts_le hr0 hr
  have hI20 : 0 ≤ I2bar r := by unfold I2bar; positivity
  have hI1b : 0 ≤ I1bar rBar := by unfold I1bar; positivity
  have hLc0 : ∀ x : ℝ, 80 ≤ x → 0 ≤ Lc x / x := fun x hx => div_nonneg (Lc_nonneg hx) (by linarith)
  -- `L_c/c = (log(c/5)/(c/5))/(5(1 − 5/c))` decreases on `c ≥ 80`
  have hLc : Lc c / c ≤ Lc 80 / 80 := by
    have e : ∀ x : ℝ, 0 < x → Lc x / x = Real.log (x / 5) / (x / 5) / (5 * (1 - 5 / x)) := fun x hx => by
      unfold Lc; field_simp
    rw [e c hc0, e 80 (by norm_num)]
    have hA := log_div_le (by norm_num : (3 : ℝ) ≤ 80 / 5) (by linarith : (80 : ℝ) / 5 ≤ c / 5)
    have hB : 5 / c ≤ 5 / 80 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
    have hA0 : 0 ≤ Real.log (c / 5) / (c / 5) :=
      div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)) (by positivity)
    exact div_le_div₀ (hA0.trans hA) hA (by norm_num) (by linarith)
  have key : ∀ x ρ : ℝ, 0 < x → x * lemmaEBound x ρ 5
      = (√(32 / 15) + 5 / x * e1 ρ) ^ 2 / 250
        + 2 * ρ * (1 / (3 * (1 - ρ)) + (2 * (2 + ρ) * (5 * (Lc x / x)) + 5 / x * (2 + ρ) ^ 2 / 2) / (1 - ρ) ^ 4)
          / 5
        + √(I1bar ρ * I2bar ρ) / 25 / x := fun x ρ hx => by
    unfold lemmaEBound
    field_simp
    ring
  rw [key c r hc0, key 80 rBar (by norm_num)]
  have h5 : 5 / c ≤ 5 / 80 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
  have t1 : (√(32 / 15) + 5 / c * e1 r) ^ 2 / 250 ≤ (√(32 / 15) + 5 / 80 * e1 rBar) ^ 2 / 250 := by
    gcongr
  have t2 : 2 * r * (1 / (3 * (1 - r)) + (2 * (2 + r) * (5 * (Lc c / c)) + 5 / c * (2 + r) ^ 2 / 2) / (1 - r) ^ 4)
        / 5
      ≤ 2 * rBar * (1 / (3 * (1 - rBar))
          + (2 * (2 + rBar) * (5 * (Lc 80 / 80)) + 5 / 80 * (2 + rBar) ^ 2 / 2) / (1 - rBar) ^ 4) / 5 := by
    have := hLc0 c hc
    have := rBar_mem.1
    have := hLc0 80 le_rfl
    gcongr
  have t3 : √(I1bar r * I2bar r) / 25 / c ≤ √(I1bar rBar * I2bar rBar) / 25 / 80 := by
    gcongr
  linarith

/-- The band constant at `c = 80`, `r = r̄`, `X = 2`: `B̄ = C_M(80, 2)(√(80·LE(80, r̄, 5)) + √(5/(2(1 − r̄))))²`. -/
noncomputable def Bbar : ℝ :=
  CM 80 2 * (√(80 * lemmaEBound 80 rBar 5) + √(5 / (2 * (1 - rBar)))) ^ 2

/-- `Bnd(c, r, X) ≤ B̄` for `c ≥ 80`, `X ≥ 2`, `0 ≤ r ≤ r̄`. -/
theorem Bnd_le {c r X : ℝ} (hc : 80 ≤ c) (hX : 2 ≤ X) (hr0 : 0 ≤ r) (hr : r ≤ rBar) : Bnd c r X ≤ Bbar := by
  have hb := rBar_mem.2
  have h1b : 0 < 1 - rBar := by linarith
  have hCM := CM_le hc hX
  have hCM0 := CM_nonneg hc hX
  have hLE := cLE_le hc hr0 hr
  have := CM_nonneg (c := 80) (X := 2) le_rfl le_rfl
  unfold Bnd Bbar
  gcongr

/-- `Ē_full = ((√F̄ + 2√W̄ + √R̄₀ + √B̄)/√(1 + log 80) + √R̄₁)²/π`. -/
noncomputable def EbarFull : ℝ :=
  ((√Fbar + 2 * √Wbar + √R0bar + √Bbar) / √(1 + Real.log 80) + √R1bar) ^ 2 / π

/-- **η_P^full uniformly in `c`**: `η_P^full(c, κ(1 + log c), J, X) ≤ Ē_full/κ` for `c ≥ 80`, `X ≥ 2`, `κ ≥ 1`,
`0 ≤ J ≤ c/4 + 1`. -/
theorem etaPfull_le_EbarFull {c κ J X : ℝ} (hc : 80 ≤ c) (hX : 2 ≤ X) (hκ : 1 ≤ κ) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1) : etaPfull c (κ * (1 + Real.log c)) J X ≤ EbarFull / κ := by
  have hc0 : 0 < c := by linarith
  have hL80 : Real.log 80 ≤ Real.log c := Real.log_le_log (by norm_num) hc
  have hlog1 := one_le_log_80
  have hL0 : 0 ≤ Real.log c := by linarith
  obtain ⟨hr0, hrρ, hρb⟩ := rLow_le hc hκ
  have hfb := (rf_le hc hκ).2
  have hJc := J_div_le hc hJ
  have hJc0 : 0 ≤ J / c := by positivity
  have hFar : Far c (κ * (1 + Real.log c)) J ≤ Fbar := by
    obtain ⟨hC0, hC⟩ := Cbar_le hc hfb
    unfold Far Fbar
    gcongr
  have hWb : Wb c (κ * (1 + Real.log c)) J ≤ Wbar := by
    obtain ⟨hω0, hω⟩ := omega2Sq_le hc (hrρ.trans hρb)
    unfold Wb Wbar
    exact mul_le_mul hJc hω hω0 (by norm_num)
  have hR := Rcal_le hc hκ hJ0 hJ
  have hB := Bnd_le hc hX hr0 (hrρ.trans hρb) (X := X)
  have hR1 : 0 ≤ R1bar := by
    unfold R1bar a1; have : 0 < betaEdge := by unfold betaEdge; norm_num
    positivity
  set A := √Fbar + 2 * √Wbar + √R0bar + √Bbar with hAd
  set S := √(Far c (κ * (1 + Real.log c)) J) + 2 * √(Wb c (κ * (1 + Real.log c)) J)
    + √(Rcal c (rLow c (κ * (1 + Real.log c))) J) + √(Bnd c (rLow c (κ * (1 + Real.log c))) X) with hSd
  have hS : S ≤ A + √R1bar * √(Real.log c) := by
    have h3 : √(Rcal c (rLow c (κ * (1 + Real.log c))) J) ≤ √R0bar + √R1bar * √(Real.log c) := by
      rw [← Real.sqrt_mul hR1]
      exact (Real.sqrt_le_sqrt hR).trans (sqrt_add_le_add (by positivity))
    have h1 := Real.sqrt_le_sqrt hFar
    have h2 := Real.sqrt_le_sqrt hWb
    have h4 := Real.sqrt_le_sqrt hB
    rw [hSd, hAd]
    linarith
  have hS0 : 0 ≤ S := by positivity
  have hu0 : 0 < √(1 + Real.log 80) := Real.sqrt_pos.mpr (by linarith)
  have hu : √(1 + Real.log 80) ≤ √(1 + Real.log c) := Real.sqrt_le_sqrt (by linarith)
  have hupos : 0 < √(1 + Real.log c) := hu0.trans_le hu
  have hLu : √(Real.log c) ≤ √(1 + Real.log c) := Real.sqrt_le_sqrt (by linarith)
  have hA0 : 0 ≤ A := by positivity
  have hSu : S / √(1 + Real.log c) ≤ A / √(1 + Real.log 80) + √R1bar := by
    rw [div_le_iff₀ hupos]
    have : A ≤ A / √(1 + Real.log 80) * √(1 + Real.log c) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hu0]
      exact mul_le_mul_of_nonneg_left hu hA0
    have : √R1bar * √(Real.log c) ≤ √R1bar * √(1 + Real.log c) :=
      mul_le_mul_of_nonneg_left hLu (Real.sqrt_nonneg _)
    nlinarith
  have hκ0 : 0 < κ := by linarith
  have e : etaPfull c (κ * (1 + Real.log c)) J X = (S / √(1 + Real.log c)) ^ 2 / π / κ := by
    unfold etaPfull
    rw [div_pow, Real.sq_sqrt (by linarith)]
    field_simp
    rw [hSd]
  rw [e]
  unfold EbarFull
  gcongr

variable {ι : Type} [Fintype ι]

/-- **hlow on the full span, uniformly in `c`**: under the floor `κ_F·P ≤ N`, the low band `|t| < c/K0` of
`logScale (posTail Φ X)` carries at most `Ē_full/(κκ_F)·N`, at `K0 = κ(1 + log c)`, `κ ≥ 1`. -/
theorem hlow_of_FF_full_unif (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} {X κ κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (hχinj : Function.Injective χ) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hκ1 : 1 ≤ κ) (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    ∫ t in {t : ℝ | |t| < c / (κ * (1 + Real.log c))},
        specDensity (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) t
      ≤ EbarFull / (κ * κF) * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 := by
  have hL0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hκ0 : 0 < κ := by linarith
  have hK0 : 0 < κ * (1 + Real.log c) := by positivity
  obtain ⟨-, hrρ, hρb⟩ := rLow_le hc hκ1
  have hr : rLow c (κ * (1 + Real.log c)) < 1 := (hrρ.trans hρb).trans_lt rBar_mem.2
  have h := hlow_of_FF_full a hg hg₁ hg₂c hang hX hc hχ0 hχc hχinj hM hK0 hr hκ hFF
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _))
  rw [← div_div]
  exact div_le_div_of_nonneg_right (etaPfull_le_EbarFull hc hX hκ1 (Nat.cast_nonneg _) hJ) hκ.le

end Cvs.L2a.FullSpanLowConstant
