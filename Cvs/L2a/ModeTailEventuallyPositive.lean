import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.FirstModeHigherModeScale
import Cvs.L2a.ModeTailNormLowerExactRoot
import Cvs.L2a.ModeTailTerminalExactRoot
import Cvs.L2a.NormCrossTermsVanish
import Cvs.L2a.ProlateWeightSizesBelowPlunge
import Cvs.L2a.TailFormPositiveLargeScale
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesPoleMellinValues
import Cvs.L2a.TailModesPositiveLargeC
import Cvs.L2a.TailModesTerminalInequality
import Cvs.L2a.TailOfModes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a for the tail of `M` modes, for every `χ ≤ (1 − ℓ)c²`, eventually in `c`

`TailModesPositiveLargeC`'s argument with the exact-root chain: at cutoff `2πx' = √c`, `η = 1/c`, window scale `c^{2/5}`, `ξ₀ = √2`, for
fixed `0 < ℓ ≤ 1`, edge ratio `K` and energy ratio `Γ`, the Weil form of every tail of `M` modes of a prolate with
`ℓc² ≤ c² − χ` is positive for every large `c`, uniformly in `M`, `J ≥ 1` and the prime truncation.
-/

namespace Cvs.L2a.ModeTailEventuallyPositive

open Real Set MeasureTheory Filter Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)
open Cvs.L2a.TailModesPositiveLargeC (cK floorK_le log_le_two_sqrt mellinBound_nonneg)

set_option maxHeartbeats 8000000 in
/-- **L2a for the tail of `M` modes, for every `χ ≤ (1 − ℓ)c²`**: for every large `c`, the Weil form of the tail
is positive. -/
theorem weilForm_tailF_eventually_pos (K Γ ℓ : ℝ) (Kf : ℕ) (hK : 0 ≤ K) (hΓ : 1 ≤ Γ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (hKf : 1 ≤ Kf) :
    ∀ᶠ c in atTop, ∀ (χ G Gm Ξ : ℝ) (ψ u : ℝ → ℝ) (P R N M J : ℕ),
      0 ≤ χ → ℓ * c ^ 2 ≤ c ^ 2 - χ →
      (∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ) →
      (∀ ξ ∈ Icc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) → u 1 = 0 →
      ContDiffOn ℝ 1 ψ (Icc 1 Ξ) →
      (∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) →
      (∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) → ψ 1 ^ 2 ≤ K * G →
      (∀ t ∈ Icc (√2) (2 ^ (J + 1)), Gm ≤ energy (aP c χ) ψ u t) → 0 < Gm → G ≤ Γ * Gm →
      1 ≤ J → 1 ≤ M → (M : ℝ) * 2 ^ (J + 1) ≤ Ξ →
      Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N → (N : ℝ) + 2 ≤ 2 ^ (J + 1) →
      0 < Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF ψ M (2 ^ (J + 1)))) := by
  -- the constants
  set L := π ^ 2 / 6 + 6 with hL
  set Cx := Cvs.L2a.ProlateWeightSizesBelowPlunge.Cxl K ℓ with hCx
  set Pc := Cvs.L2a.ProlateWeightSizesBelowPlunge.Pl K ℓ with hPc
  set Bm := Cvs.L2a.ProlateWeightSizesBelowPlunge.Bml K ℓ with hBm
  set Ql := Cvs.L2a.ProlateWeightSizesBelowPlunge.Ql ℓ with hQl
  set a₀ := archSymbol 0 with ha₀
  set D := |cK Kf - a₀| with hD
  set r₀ := arccos (1 / 2) - arccos (1 / √2) with hr₀
  have hr₀0 : 0 < r₀ := by
    have h2 : (1 : ℝ) / 2 < 1 / √2 := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
      have : √2 < 2 := by rw [sqrt_lt' (by norm_num)]; norm_num
      linarith
    have hs2 : 1 / √2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    have := strictAntiOn_arccos ⟨by norm_num, by norm_num⟩ ⟨by
      have : 0 < 1 / √2 := by positivity
      linarith, hs2⟩ h2
    rw [hr₀]; linarith
  set τ2 := 4 * Γ * (1 + 2 * Cx + 48 / √3 * L) / r₀ with hτ2
  set τ3 := Γ * Ql * 4 / r₀ with hτ3
  set C4 := 16 * Γ * Bm ^ 2 / r₀ with hC4
  set τ4 := (2 + D) * C4 with hτ4
  set pinf := Γ * Pc * 4 / r₀ with hpinf
  have hL0 : 0 < L := by positivity
  have hPc0 : 0 ≤ Pc := by
    rw [hPc]; unfold Cvs.L2a.ProlateWeightSizesBelowPlunge.Pl
    have : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 :=
      tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    have : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * √n) :=
      tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    positivity
  have hCx0 : 0 ≤ Cx := by
    rw [hCx]; unfold Cvs.L2a.ProlateWeightSizesBelowPlunge.Cxl; positivity
  have hQl0 : 0 ≤ Ql := by rw [hQl]; unfold Cvs.L2a.ProlateWeightSizesBelowPlunge.Ql; positivity
  have hτ20 : 0 ≤ τ2 := by positivity
  have hpinf0 : 0 ≤ pinf := by
    rw [hpinf]; exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hPc0) (by norm_num)) hr₀0.le
  -- floorK along `x' = √c/(2π)` tends to infinity
  have hx' : Tendsto (fun c : ℝ => √c / (2 * π)) atTop atTop :=
    (tendsto_sqrt_atTop).atTop_div_const (by positivity)
  have hF := (Cvs.L2a.TailFormPositiveLargeScale.tendsto_floorK Kf).comp hx'
  have hF1 : ∀ᶠ c in atTop, pinf + 3 + |a₀| ≤ floorK (√c / (2 * π)) Kf := hF.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (5 : ℝ), eventually_ge_atTop (τ2 ^ 10), eventually_ge_atTop τ3,
    eventually_ge_atTop (τ4 ^ 4), hF1, eventually_ge_atTop (9 / ℓ), eventually_ge_atTop ((5 / (3 * ℓ)) ^ 10)]
    with c hc5 hc2 hc3 hc4 hcF hcℓ hcℓ2
  intro χ G Gm Ξ ψ u P R N M J hχ0 hσℓ hψ hu hu1 hC1 hG hedge hedge1 hGm hGm0 hGΓ hJ hM hΞ hidx hrb
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hc4' : (4 : ℝ) ≤ c := by linarith
  have hsc0 : 0 < √c := sqrt_pos.mpr hc0
  have hscc : √c ≤ c := by rw [sqrt_le_left hc0.le]; nlinarith
  have hcc : √c * √c = c := mul_self_sqrt hc0.le
  have hb4 : (4 : ℝ) ≤ 2 ^ (J + 1) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hs2 : √2 ≤ 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
  have h1s2 : (1 : ℝ) < √2 := by
    rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbΞ : (2 : ℝ) ^ (J + 1) ≤ Ξ := le_trans (by nlinarith) hΞ
  have hGmE := hGm (√2) ⟨le_rfl, by linarith⟩
  have hEG := hG (√2) ⟨h1s2, by linarith⟩
  have hG0 : 0 ≤ G := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hGG : G ≤ Γ * Gm := hGΓ
  have hℓc : 0 < ℓ * c ^ 2 := by positivity
  have hχ : χ < c ^ 2 := by linarith
  have hℓσ : ℓ ≤ (c ^ 2 - χ) / c ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  -- `c^{1/10} ≥ 5/(3ℓ)`, so `(3/5)√c ℓ ≥ 1` and `(3/5)c^{2/5} ℓ ≥ 1`
  have h53 : 1 ≤ 5 / (3 * ℓ) := by rw [le_div_iff₀ (by positivity)]; linarith
  have ht53 : 5 / (3 * ℓ) ≤ c ^ ((1 : ℝ) / 10) := by
    have h := rpow_le_rpow (by positivity) hcℓ2 (by norm_num : (0 : ℝ) ≤ 1 / 10)
    rw [show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num, pow_rpow_inv_natCast (by positivity) (by norm_num)] at h
    rw [show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num]; exact h
  have hcont : ContinuousOn ψ (Icc 1 Ξ) := hC1.continuousOn
  have hIcc : ∀ ξ ∈ Ioc (1 : ℝ) Ξ, ξ ∈ Icc 1 Ξ := fun ξ h => ⟨h.1.le, h.2⟩
  set b : ℝ := 2 ^ (J + 1) with hbdef
  -- the window scale `s = c^{2/5}`
  set sw : ℝ := c ^ ((2 : ℝ) / 5) with hsw
  have hs1 : 1 ≤ sw := one_le_rpow hc1 (by norm_num)
  have hsc : sw ^ 2 ≤ c := by
    rw [hsw, ← rpow_natCast, ← rpow_mul hc0.le]
    calc c ^ ((2 : ℝ) / 5 * ((2 : ℕ) : ℝ)) ≤ c ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      _ = c := rpow_one c
  -- `c^{1/10} ≥ τ2`
  have ht10 : τ2 ≤ c ^ ((1 : ℝ) / 10) := by
    have h := rpow_le_rpow (by positivity) hc2 (by norm_num : (0 : ℝ) ≤ 1 / 10)
    rw [show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num, pow_rpow_inv_natCast hτ20 (by norm_num)] at h
    rw [show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num]; exact h
  have ht0 : 0 < c ^ ((1 : ℝ) / 10) := rpow_pos_of_pos hc0 _
  have ht1 : 1 ≤ c ^ ((1 : ℝ) / 10) := one_le_rpow hc1 (by norm_num)
  have hs4 : sw = (c ^ ((1 : ℝ) / 10)) ^ 4 := by rw [hsw, ← Cvs.L2a.NormCrossTermsVanish.rpow_tenth hc0 4]; norm_num
  have hs5 : √c = (c ^ ((1 : ℝ) / 10)) ^ 5 := by
    rw [← Cvs.L2a.NormCrossTermsVanish.rpow_tenth hc0 5, sqrt_eq_rpow]; norm_num
  have hswℓ : 1 ≤ 3 / 5 * (sw * ℓ) := by
    rw [hs4]
    have : c ^ ((1 : ℝ) / 10) ≤ (c ^ ((1 : ℝ) / 10)) ^ 4 := by
      nlinarith [pow_le_pow_right₀ ht1 (show 1 ≤ 4 by norm_num), pow_one (c ^ ((1 : ℝ) / 10))]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 3 * ℓ)).mp (ht53.trans this)
    linarith
  have hscℓ : 1 ≤ 3 / 5 * (√c * ℓ) := by
    rw [hs5]
    have : c ^ ((1 : ℝ) / 10) ≤ (c ^ ((1 : ℝ) / 10)) ^ 5 := by
      nlinarith [pow_le_pow_right₀ ht1 (show 1 ≤ 5 by norm_num), pow_one (c ^ ((1 : ℝ) / 10))]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 3 * ℓ)).mp (ht53.trans this)
    linarith
  have htc : c ^ ((1 : ℝ) / 10) ≤ c := by
    calc c ^ ((1 : ℝ) / 10) ≤ c ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      _ = c := rpow_one c
  -- the norm from below
  have nb := Cvs.L2a.ModeTailNormLowerExactRoot.norm_ge (c := c) (χ := χ) (G := G) (K := K) (Gm := Gm) (Ξ := Ξ) (ξ₀ := √2)
    (s := sw) (ℓ := ℓ) (ψ := ψ) (u := u) M J hc1 hχ0 hχ hℓ0 hℓσ hs1 hsc hswℓ (by linarith) hΞ hψ
    (fun ξ h => hu ξ (hIcc ξ h)) hG hG0 hK hcont hedge hedge1 h1s2 (by linarith) hGm hGm0.le hM
  rw [← hbdef] at nb
  set Nn := ∫ θ in Ioi 1, tailF ψ M b θ ^ 2 with hNn
  have harc : r₀ ≤ arccos (1 / b) - arccos (1 / √2) := by
    have : arccos (1 / 2) ≤ arccos (1 / b) := arccos_le_arccos (by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
    rw [hr₀]; linarith
  have hq2 : c ^ 2 ≤ qP c χ √2 := by
    unfold qP; rw [sq_sqrt (by norm_num)]; nlinarith
  have hcX := Cvs.L2a.ProlateWeightSizesBelowPlunge.c_mul_Xbar_le hc1 hℓ0 hℓ1 hσℓ hK (by rw [← hsw]; exact hswℓ)
  rw [← hsw, ← hCx] at hcX
  have hNlow : Gm * r₀ / (4 * c) ≤ Nn := by
    have e1 : Gm * r₀ / (2 * c) ≤ Gm * (arccos (1 / b) - arccos (1 / √2)) / (2 * c) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left harc hGm0.le) (by positivity)
    have e2 : G / (2 * qP c χ √2) ≤ Γ * Gm / (2 * c ^ 2) :=
      div_le_div₀ (by positivity) hGG (by positivity) (by linarith)
    have e3 : 2 * G * Cvs.L2a.FirstModeHigherModeScale.Xbar c χ K sw ℓ ≤ 2 * (Γ * Gm) * (Cx / (c * c ^ ((1 : ℝ) / 10))) := by
      have hX1 : Cvs.L2a.FirstModeHigherModeScale.Xbar c χ K sw ℓ ≤ Cx / (c * c ^ ((1 : ℝ) / 10)) := by
        rw [le_div_iff₀ (by positivity)]
        calc Cvs.L2a.FirstModeHigherModeScale.Xbar c χ K sw ℓ * (c * c ^ ((1 : ℝ) / 10))
            = c * Cvs.L2a.FirstModeHigherModeScale.Xbar c χ K sw ℓ * c ^ ((1 : ℝ) / 10) := by ring
          _ ≤ Cx / c ^ ((1 : ℝ) / 10) * c ^ ((1 : ℝ) / 10) := by gcongr
          _ = Cx := by field_simp
      have hX0 : 0 ≤ Cvs.L2a.FirstModeHigherModeScale.Xbar c χ K sw ℓ := by
        have := Cvs.L2a.FirstModeHigherModeScale.X_sum_le (c := c) (χ := χ) (K := K) (s := sw) (ℓ := ℓ) 0 hc0 hs1 hℓ0 hswℓ
        simpa using this
      calc 2 * G * Cvs.L2a.FirstModeHigherModeScale.Xbar c χ K sw ℓ ≤ 2 * (Γ * Gm) * Cvs.L2a.FirstModeHigherModeScale.Xbar c χ K sw ℓ := by
            gcongr
        _ ≤ _ := by gcongr
    have e4 : 8 * G * (2 / √3) / c ^ 2 * (3 * (π ^ 2 / 6 + 6)) ≤ Γ * Gm * (48 / √3 * L) / c ^ 2 := by
      rw [hL]
      calc 8 * G * (2 / √3) / c ^ 2 * (3 * (π ^ 2 / 6 + 6)) ≤ 8 * (Γ * Gm) * (2 / √3) / c ^ 2 * (3 * (π ^ 2 / 6 + 6)) := by
            gcongr
        _ = Γ * Gm * (48 / √3 * (π ^ 2 / 6 + 6)) / c ^ 2 := by ring
    -- the error is at most `r₀ Gm/(4c)`
    have herr : Γ * Gm / (2 * c ^ 2) + 2 * (Γ * Gm) * (Cx / (c * c ^ ((1 : ℝ) / 10)))
        + Γ * Gm * (48 / √3 * L) / c ^ 2 ≤ Gm * r₀ / (4 * c) := by
      have hsum : 1 / (2 * c) + 2 * Cx / c ^ ((1 : ℝ) / 10) + 48 / √3 * L / c
          ≤ (1 + 2 * Cx + 48 / √3 * L) / c ^ ((1 : ℝ) / 10) := by
        have a1 : 1 / (2 * c) ≤ 1 / c ^ ((1 : ℝ) / 10) := one_div_le_one_div_of_le ht0 (by linarith)
        have a2 : 48 / √3 * L / c ≤ 48 / √3 * L / c ^ ((1 : ℝ) / 10) :=
          div_le_div_of_nonneg_left (by positivity) ht0 htc
        have e : (1 + 2 * Cx + 48 / √3 * L) / c ^ ((1 : ℝ) / 10)
            = 1 / c ^ ((1 : ℝ) / 10) + 2 * Cx / c ^ ((1 : ℝ) / 10) + 48 / √3 * L / c ^ ((1 : ℝ) / 10) := by ring
        linarith
      have hτ : Γ * ((1 + 2 * Cx + 48 / √3 * L) / c ^ ((1 : ℝ) / 10)) ≤ r₀ / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ ht0 (by norm_num)]
        have : 4 * Γ * (1 + 2 * Cx + 48 / √3 * L) ≤ r₀ * c ^ ((1 : ℝ) / 10) := by
          rw [hτ2, div_le_iff₀ hr₀0] at ht10; linarith
        linarith
      have e : Γ * Gm / (2 * c ^ 2) + 2 * (Γ * Gm) * (Cx / (c * c ^ ((1 : ℝ) / 10))) + Γ * Gm * (48 / √3 * L) / c ^ 2
          = Gm / c * (Γ * (1 / (2 * c) + 2 * Cx / c ^ ((1 : ℝ) / 10) + 48 / √3 * L / c)) := by field_simp
      rw [e]
      calc Gm / c * (Γ * (1 / (2 * c) + 2 * Cx / c ^ ((1 : ℝ) / 10) + 48 / √3 * L / c))
          ≤ Gm / c * (Γ * ((1 + 2 * Cx + 48 / √3 * L) / c ^ ((1 : ℝ) / 10))) := by gcongr
        _ ≤ Gm / c * (r₀ / 4) := by gcongr
        _ = Gm * r₀ / (4 * c) := by ring
    have e5 : Gm * r₀ / (2 * c) = Gm * r₀ / (4 * c) + Gm * r₀ / (4 * c) := by ring
    linarith
  have hNpos : 0 < Nn := lt_of_lt_of_le (by positivity) hNlow
  -- Cvs.L2a.TailModesTerminalInequality at `x' = √c/(2π)`, `η = 1/c`
  set x' := √c / (2 * π) with hx'def
  have hx'0 : 0 < x' := by positivity
  have h2πx : 2 * π * x' = √c := by rw [hx'def]; field_simp
  have hT : 2 * (2 * π * x') ^ 2 + 1 / 2 ≤ c ^ 2 - χ := by
    rw [h2πx, sq_sqrt hc0.le]
    have h9 : 9 ≤ ℓ * c := by rw [div_le_iff₀ hℓ0] at hcℓ; linarith
    nlinarith
  have hηθ : 1 + 1 / c ≤ √(1 + √(c ^ 2 - χ) / c) := by
    apply Real.le_sqrt_of_sq_le
    have hσ := Cvs.L2a.ProlateWeightSizesBelowPlunge.sigma_ge hℓ0.le hσℓ
    have h1 : √ℓ ≤ √(c ^ 2 - χ) / c := by rw [le_div_iff₀ hc0]; linarith
    have hsl1 : √ℓ ≤ 1 := (sqrt_le_sqrt hℓ1).trans_eq sqrt_one
    have hsl : ℓ ≤ √ℓ := by nlinarith [mul_self_sqrt hℓ0.le, sqrt_nonneg ℓ]
    have h2 : 3 / c ≤ ℓ := by
      rw [div_le_iff₀ hc0]; rw [div_le_iff₀ hℓ0] at hcℓ; nlinarith
    have h3 : 0 ≤ 1 / c := by positivity
    have h4 : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc1
    have h5 : 1 / c * (1 / c) ≤ 1 / c := mul_le_of_le_one_left h3 h4
    have e : (1 + 1 / c) ^ 2 = 1 + 2 * (1 / c) + 1 / c * (1 / c) := by ring
    have e3 : 3 / c = 3 * (1 / c) := by ring
    rw [e]; linarith
  set F := floorK x' Kf with hFdef
  have hFa : a₀ ≤ F := by
    have := le_abs_self a₀
    linarith
  have key := Cvs.L2a.ModeTailTerminalExactRoot.weilForm_tailF_ge (c := c) (χ := χ) (G := G) (K := K) (Ξ := Ξ) (η := 1 / c)
    (x' := x') (ℓ := ℓ) (ψ := ψ) (u := u) P R N M J Kf hc1 hχ0 hχ hℓ0 hℓσ hscℓ hψ hu hu1 hC1 hG hG0 hK hedge hedge1
    hM hΞ hidx hrb hx'0 hKf hFa hT (by positivity) hηθ hNpos
  rw [← hbdef, ← hNn, ← hFdef, h2πx] at key
  set B := Cvs.L2a.TailModesPoleMellinValues.mellinBound c χ G (1 / c) √c (ψ 1) with hBdef
  set pB := Cvs.L2a.ModeTailTerminalExactRoot.primeBound c χ G K ℓ with hpB
  set qB := Cvs.L2a.TailModesTerminalInequality.poleBound c χ G with hqB
  have hexp : (F - (F - a₀) * (4 * x' * B ^ 2 / Nn) - pB / Nn - qB / Nn) * Nn
      = F * Nn - (F - a₀) * (4 * x' * B ^ 2) - pB - qB := by field_simp
  rw [hexp] at key
  -- the three margins
  have hpB' : pB ≤ pinf * Nn := by
    have h1 := Cvs.L2a.ProlateWeightSizesBelowPlunge.primeBound_le hc1 hℓ0 hℓ1 hσℓ hscℓ hG0 hK
    rw [← hpB, ← hPc] at h1
    calc pB ≤ G * Pc / c := h1
      _ ≤ Γ * Gm * Pc / c := by gcongr
      _ = pinf * (Gm * r₀ / (4 * c)) := by rw [hpinf]; field_simp
      _ ≤ pinf * Nn := by gcongr
  have hqB' : qB ≤ Nn := by
    have h1 := Cvs.L2a.ProlateWeightSizesBelowPlunge.poleBound_le hc0 hℓ0 hσℓ hG0
    rw [← hqB, ← hQl] at h1
    have hc2' : τ3 ≤ c ^ 2 := hc3.trans (by rw [sq]; exact le_mul_of_one_le_left hc0.le hc1)
    calc qB ≤ Ql * G / c ^ 3 := h1
      _ ≤ Ql * (Γ * Gm) / c ^ 3 := by gcongr
      _ = Gm * r₀ / (4 * c) * (τ3 / c ^ 2) := by rw [hτ3]; field_simp
      _ ≤ Gm * r₀ / (4 * c) * 1 := by
          gcongr; rw [div_le_one (by positivity)]; exact hc2'
      _ ≤ Nn := by linarith
  have hlow : (F - a₀) * (4 * x' * B ^ 2) ≤ Nn := by
    have hB0 : 0 ≤ B := mellinBound_nonneg hc0 hG0 (by positivity) hsc0.le hχ
    have hB := Cvs.L2a.ProlateWeightSizesBelowPlunge.mellinBound_le hc1 hℓ0 hσℓ hK hedge1
    rw [← hBdef, ← hBm] at hB
    have hB2 : B ^ 2 ≤ G * Bm ^ 2 / c ^ 2 := by
      have := pow_le_pow_left₀ hB0 hB 2
      rw [div_pow, mul_pow, sq_sqrt hG0] at this; exact this
    have hx'c : x' ≤ √c := by rw [hx'def]; exact div_le_self hsc0.le (by linarith [pi_gt_three])
    have hFlog : F - a₀ ≤ 2 * √(√c) + D := by
      have h1 := floorK_le hx'0 Kf
      have h2 := log_le_two_sqrt hx'0
      have h3 : √x' ≤ √(√c) := Real.sqrt_le_sqrt hx'c
      have h4 : cK Kf - a₀ ≤ D := le_abs_self _
      rw [← hFdef] at h1; linarith
    have hss1 : 1 ≤ √(√c) := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hc1)
    have hssq : √(√c) * √(√c) = √c := mul_self_sqrt hsc0.le
    have hτ4c : τ4 ≤ √(√c) := by
      have h := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hc4)
      have hτ40 : 0 ≤ τ4 := by rw [hτ4, hC4]; positivity
      rwa [show τ4 ^ 4 = (τ4 ^ 2) ^ 2 by ring, sqrt_sq (by positivity), sqrt_sq hτ40] at h
    have hFa0 : 0 ≤ F - a₀ := by linarith
    have hD0 : 0 ≤ D := abs_nonneg _
    calc (F - a₀) * (4 * x' * B ^ 2) ≤ (2 * √(√c) + D) * (4 * √c * (Γ * Gm * Bm ^ 2 / c ^ 2)) := by
          apply mul_le_mul hFlog _ (by positivity) (by positivity)
          have : G * Bm ^ 2 / c ^ 2 ≤ Γ * Gm * Bm ^ 2 / c ^ 2 := by gcongr
          have hx4 : 4 * x' * B ^ 2 ≤ 4 * √c * (G * Bm ^ 2 / c ^ 2) := by gcongr
          calc 4 * x' * B ^ 2 ≤ 4 * √c * (G * Bm ^ 2 / c ^ 2) := hx4
            _ ≤ 4 * √c * (Γ * Gm * Bm ^ 2 / c ^ 2) := by gcongr
      _ ≤ (2 + D) * √(√c) * (4 * √c * (Γ * Gm * Bm ^ 2 / c ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : D ≤ D * √(√c) := le_mul_of_one_le_right hD0 hss1
          linarith
      _ ≤ Gm * r₀ / (4 * c) := by
          have hC4' : (2 + D) * (16 * Γ * Bm ^ 2 / r₀) ≤ √(√c) := by rw [← hC4, ← hτ4]; exact hτ4c
          have e : (2 + D) * √(√c) * (4 * √c * (Γ * Gm * Bm ^ 2 / c ^ 2))
              = Gm * r₀ / (4 * c) * ((2 + D) * (16 * Γ * Bm ^ 2 / r₀) * √(√c) / √c) := by
            set q := √(√c) with hqdef
            have hq : √c = q ^ 2 := by rw [← hssq]; ring
            have hcq : c = q ^ 4 := by rw [← hcc, hq]; ring
            have hq0 : 0 < q := by positivity
            rw [hq, hcq]; field_simp; ring
          rw [e]
          have hr : (2 + D) * (16 * Γ * Bm ^ 2 / r₀) * √(√c) / √c ≤ 1 := by
            rw [div_le_one hsc0]
            calc (2 + D) * (16 * Γ * Bm ^ 2 / r₀) * √(√c) ≤ √(√c) * √(√c) :=
                  mul_le_mul_of_nonneg_right hC4' (by positivity)
              _ = √c := hssq
          calc Gm * r₀ / (4 * c) * ((2 + D) * (16 * Γ * Bm ^ 2 / r₀) * √(√c) / √c)
              ≤ Gm * r₀ / (4 * c) * 1 := mul_le_mul_of_nonneg_left hr (by positivity)
            _ = Gm * r₀ / (4 * c) := mul_one _
      _ ≤ Nn := hNlow
  -- the margin
  have hF3 : pinf + 3 ≤ F := by have := abs_nonneg a₀; linarith
  have hm := mul_nonneg (sub_nonneg.mpr hF3) hNpos.le
  have e : F * Nn = (F - (pinf + 3)) * Nn + pinf * Nn + 3 * Nn := by ring
  linarith

end Cvs.L2a.ModeTailEventuallyPositive
