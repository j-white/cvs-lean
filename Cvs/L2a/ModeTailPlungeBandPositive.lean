import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.ModeTailNormLowerSigmaFree
import Cvs.L2a.ModeTailTerminalSigmaFree
import Cvs.L2a.SigmaFreeBoundSizesPlunge
import Cvs.L2a.SigmaFreeWeightedPairTotal
import Cvs.L2a.TailFormPositiveLargeScale
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesPoleMellinValues
import Cvs.L2a.TailModesPositiveLargeC
import Cvs.L2a.TailOfModes
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.RungMellinBoundFixedCutoff
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
# L2a for the tail of `M` modes across the plunge band: every `χ` with `c² − χ ≥ C c`

`ModeTailTerminalSigmaFree`'s terminal inequality with `SigmaFreeBoundSizesPlunge`'s norm, prime and pole sizes and `RungMellinBoundFixedCutoff`'s Mellin bound at a fixed cutoff `X`,
chosen once so that `floorK X` beats the prime constant: for fixed `K`, `Γ` there is `C` such that for every large `c`
the Weil form of every tail with `C c ≤ c² − χ` is positive, uniformly in `M`, `J ≥ 1`, the truncation, and `χ`.
-/

namespace Cvs.L2a.ModeTailPlungeBandPositive

open Real Set MeasureTheory Filter Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)
open Cvs.L2a.TailModesPositiveLargeC (cK floorK_le log_le_two_sqrt mellinBound_nonneg)

set_option maxHeartbeats 8000000 in
/-- **L2a for the tail of `M` modes across the plunge band, in `t = c^{1/40}`**: there is `C` such that for every
large `t`, every `χ` with `C t⁴⁰ ≤ t⁸⁰ − χ`, the Weil form of the tail is positive. -/
theorem weilForm_tailF_plunge_pos_t (K Γ : ℝ) (Kf : ℕ) (hΓ : 1 ≤ Γ) (hKf : 1 ≤ Kf) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ t in atTop, ∀ (χ G Gm Ξ : ℝ) (ψ u : ℝ → ℝ) (P R N M J : ℕ),
      0 ≤ χ → C * t ^ 40 ≤ (t ^ 40) ^ 2 - χ →
      (∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ) →
      (∀ ξ ∈ Icc 1 Ξ, HasDerivAt u (-(qP (t ^ 40) χ ξ * ψ ξ)) ξ) → u 1 = 0 →
      ContDiffOn ℝ 1 ψ (Icc 1 Ξ) →
      (∀ ξ ∈ Ioc 1 Ξ, energy (aP (t ^ 40) χ) ψ u ξ ≤ G) →
      (∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) → ψ 1 ^ 2 ≤ K * G →
      (∀ τ ∈ Icc (√2) (2 ^ (J + 1)), Gm ≤ energy (aP (t ^ 40) χ) ψ u τ) → 0 < Gm → G ≤ Γ * Gm →
      1 ≤ J → 1 ≤ M → (M : ℝ) * 2 ^ (J + 1) ≤ Ξ →
      Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N → (N : ℝ) + 2 ≤ 2 ^ (J + 1) →
      0 < Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF ψ M (2 ^ (J + 1)))) := by
  -- the constants
  set L' := π ^ 2 / 6 + 6 with hL'
  set Cn := Cvs.L2a.SigmaFreeBoundSizesPlunge.Cn K with hCn
  set Pc := Cvs.L2a.SigmaFreeBoundSizesPlunge.Pc K with hPc
  set Qc := Cvs.L2a.SigmaFreeBoundSizesPlunge.Qc K with hQc
  set a₀ := archSymbol 0 with ha₀
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
  have hκ : 0 ≤ Cvs.L2a.SigmaFreeWeightedPairTotal.κ₁ := by unfold Cvs.L2a.SigmaFreeWeightedPairTotal.κ₁; positivity
  have hS2 : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hS3 : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * √n) :=
    tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hCn0 : 0 ≤ Cn := by rw [hCn]; unfold Cvs.L2a.SigmaFreeBoundSizesPlunge.Cn; positivity
  have hPc0 : 0 ≤ Pc := by rw [hPc]; unfold Cvs.L2a.SigmaFreeBoundSizesPlunge.Pc; positivity
  have hQc0 : 0 ≤ Qc := by rw [hQc]; unfold Cvs.L2a.SigmaFreeBoundSizesPlunge.Qc; positivity
  have hL'0 : 0 < L' := by positivity
  set τ2 := 4 * Γ * (1 + 2 * Cn + 48 / √3 * L') / r₀ with hτ2
  set τ3 := 4 * Γ * Qc / r₀ with hτ3
  set pinf := 4 * Γ * Pc / r₀ with hpinf
  have hpinf0 : 0 ≤ pinf := by positivity
  -- the cutoff `X`, once: `floorK X ≥ p_∞ + 3 + |a₀|`
  have hFX : ∀ᶠ x in atTop, pinf + 3 + |a₀| ≤ floorK x Kf :=
    (Cvs.L2a.TailFormPositiveLargeScale.tendsto_floorK Kf).eventually (eventually_ge_atTop _)
  obtain ⟨X, hX1, hXF⟩ := ((eventually_ge_atTop (1 : ℝ)).and hFX).exists
  have hX0 : 0 < X := by linarith
  set F := floorK X Kf with hFdef
  have hFa0 : 0 ≤ F - a₀ := by have := le_abs_self a₀; linarith
  set T := 2 * π * X with hTdef
  have hT0 : 0 ≤ T := by positivity
  set Em := Cvs.Prolate.Mellin.RungMellinBoundFixedCutoff.E K T with hEm
  set M₀ := 4 * X * (F - a₀) with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  set C := 10 + 32768 * M₀ * Γ / r₀ with hCdef
  have hC1 : 1 ≤ C := by have : 0 ≤ 32768 * M₀ * Γ / r₀ := by positivity
                         linarith
  have hC9 : 9 ≤ C := by have : 0 ≤ 32768 * M₀ * Γ / r₀ := by positivity
                         linarith
  have hCM : 32768 * M₀ * Γ ≤ r₀ * C ^ 2 := by
    have h1 : 32768 * M₀ * Γ / r₀ ≤ C := by linarith
    have h2 : C ≤ C ^ 2 := by nlinarith
    rw [div_le_iff₀ hr₀0] at h1; nlinarith
  set τ5 := 16 * M₀ * Γ * Em ^ 2 / r₀ with hτ5
  refine ⟨C, hC1, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop τ2, eventually_ge_atTop τ3,
    eventually_ge_atTop τ5, eventually_ge_atTop (2 * T ^ 2 + 1 / 2)]
    with t ht2 htτ2 htτ3 htτ5 htT
  intro χ G Gm Ξ ψ u P R N M J hχ0 hband hψ hu hu1 hC1' hG hedge hedge1 hGm hGm0 hGΓ hJ hM hΞ hidx hrb
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  set c := t ^ 40 with hcdef
  have hc1 : 1 ≤ c := one_le_pow₀ ht1
  have hc0 : 0 < c := by linarith
  have hct : t ≤ c := le_self_pow₀ ht1 (by norm_num)
  have hCc : c ≤ C * c := le_mul_of_one_le_left hc0.le hC1
  have hσ1 : 1 ≤ c ^ 2 - χ := by linarith
  have hd : 0 < c ^ 2 - χ := by linarith
  have hχ : χ < c ^ 2 := by linarith
  -- `ρ = L^{1/4}`
  set L := (c ^ 2 - χ) / c ^ 2 with hLdef
  have hL0 : 0 < L := by positivity
  have hL1 : L ≤ 1 := by rw [hLdef, div_le_one (by positivity)]; linarith
  set ρ := √(√L) with hρdef
  have hρ4 : ρ ^ 4 = L := by
    rw [hρdef, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_sqrt (sqrt_nonneg _), sq_sqrt hL0.le]
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef]; exact (sqrt_le_one.mpr ((sqrt_le_sqrt hL1).trans_eq sqrt_one))
  have hLC : C ≤ c * L := by
    rw [hLdef, mul_div_assoc', le_div_iff₀ (by positivity)]
    calc C * c ^ 2 = c * (C * c) := by ring
      _ ≤ c * (c ^ 2 - χ) := mul_le_mul_of_nonneg_left hband hc0.le
  have hρt : 1 ≤ t ^ 10 * ρ := by
    by_contra h
    push Not at h
    have h4 := pow_lt_pow_left₀ h (by positivity) (by norm_num : (4 : ℕ) ≠ 0)
    rw [mul_pow, ← pow_mul, hρ4, one_pow] at h4
    norm_num at h4
    linarith
  have hLρ : ((t ^ 40) ^ 2 - χ) / (t ^ 40) ^ 2 = ρ ^ 4 := by rw [hρ4]
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
  have hGG : G ≤ Γ * Gm := hGΓ
  have hcont : ContinuousOn ψ (Icc 1 Ξ) := hC1'.continuousOn
  have hIcc : ∀ ξ ∈ Ioc (1 : ℝ) Ξ, ξ ∈ Icc 1 Ξ := fun ξ h => ⟨h.1.le, h.2⟩
  set b : ℝ := 2 ^ (J + 1) with hbdef
  -- the norm window `s = t¹⁶/ρ²`
  set sn := t ^ 16 / ρ ^ 2 with hsn
  have hsn1 : 1 ≤ sn := by
    rw [hsn, le_div_iff₀ (by positivity), one_mul]
    exact (pow_le_one₀ hρ0.le hρ1).trans (one_le_pow₀ ht1)
  have hsnc : sn ^ 2 * L ≤ c := by
    have e : sn ^ 2 * L = t ^ 32 := by rw [hsn, ← hρ4]; field_simp
    rw [e, hcdef]; exact pow_le_pow_right₀ ht1 (by norm_num)
  have nb := Cvs.L2a.ModeTailNormLowerSigmaFree.norm_ge (c := c) (χ := χ) (G := G) (K := K) (Gm := Gm) (Ξ := Ξ) (ξ₀ := √2)
    (s := sn) (ψ := ψ) (u := u) M J hc1 hχ0 hχ hsn1 hsnc (by linarith) hΞ hψ
    (fun ξ h => hu ξ (hIcc ξ h)) hG hG0 hcont hedge hedge1 h1s2 (by linarith) hGm hGm0.le hM
  rw [← hbdef] at nb
  set Nn := ∫ θ in Ioi 1, tailF ψ M b θ ^ 2 with hNn
  have harc : r₀ ≤ arccos (1 / b) - arccos (1 / √2) := by
    have : arccos (1 / 2) ≤ arccos (1 / b) := arccos_le_arccos (by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
    rw [hr₀]; linarith
  have hq2 : c ^ 2 ≤ qP c χ √2 := by
    unfold qP; rw [sq_sqrt (by norm_num)]; nlinarith
  have hcX := Cvs.L2a.SigmaFreeBoundSizesPlunge.c_mul_Xbar_le (χ := χ) (K := K) ht1 hρ0 hρ1 hρt hLρ
  rw [← hcdef, ← hsn, ← hCn] at hcX
  have hNlow : Gm * r₀ / (4 * c) ≤ Nn := by
    have e1 : Gm * r₀ / (2 * c) ≤ Gm * (arccos (1 / b) - arccos (1 / √2)) / (2 * c) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left harc hGm0.le) (by positivity)
    have e2 : G / (2 * qP c χ √2) ≤ Γ * Gm / (2 * (c * t)) := by
      apply div_le_div₀ (by positivity) hGG (by positivity)
      have : c * t ≤ c ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hct hc0.le
      linarith
    have hX0' : 0 ≤ Cvs.L2a.ModeTailNormLowerSigmaFree.Xbar c χ K sn := by
      have := Cvs.L2a.ModeTailNormLowerSigmaFree.X_sum_le (c := c) (χ := χ) (K := K) (s := sn) 0 hc0 hχ hsn1
      simpa using this
    have e3 : 2 * G * Cvs.L2a.ModeTailNormLowerSigmaFree.Xbar c χ K sn ≤ 2 * (Γ * Gm) * (Cn / (c * t)) := by
      have hX1' : Cvs.L2a.ModeTailNormLowerSigmaFree.Xbar c χ K sn ≤ Cn / (c * t) := by
        rw [le_div_iff₀ (by positivity)]
        calc Cvs.L2a.ModeTailNormLowerSigmaFree.Xbar c χ K sn * (c * t) = c * Cvs.L2a.ModeTailNormLowerSigmaFree.Xbar c χ K sn * t := by ring
          _ ≤ Cn / t * t := by gcongr
          _ = Cn := by field_simp
      calc 2 * G * Cvs.L2a.ModeTailNormLowerSigmaFree.Xbar c χ K sn ≤ 2 * (Γ * Gm) * Cvs.L2a.ModeTailNormLowerSigmaFree.Xbar c χ K sn := by
            gcongr
        _ ≤ _ := by gcongr
    have e4 : 8 * G * (2 / √3) / c ^ 2 * (3 * (π ^ 2 / 6 + 6)) ≤ Γ * Gm * (48 / √3 * L') / (c * t) := by
      rw [hL']
      have : c * t ≤ c ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hct hc0.le
      calc 8 * G * (2 / √3) / c ^ 2 * (3 * (π ^ 2 / 6 + 6))
          ≤ 8 * (Γ * Gm) * (2 / √3) / c ^ 2 * (3 * (π ^ 2 / 6 + 6)) := by gcongr
        _ = Γ * Gm * (48 / √3 * (π ^ 2 / 6 + 6)) / c ^ 2 := by ring
        _ ≤ Γ * Gm * (48 / √3 * (π ^ 2 / 6 + 6)) / (c * t) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) this
    have herr : Γ * Gm / (2 * (c * t)) + 2 * (Γ * Gm) * (Cn / (c * t))
        + Γ * Gm * (48 / √3 * L') / (c * t) ≤ Gm * r₀ / (4 * c) := by
      have hτ : Γ * (1 + 2 * Cn + 48 / √3 * L') ≤ r₀ / 4 * t := by
        rw [hτ2, div_le_iff₀ hr₀0] at htτ2; linarith
      have e : Γ * Gm / (2 * (c * t)) + 2 * (Γ * Gm) * (Cn / (c * t)) + Γ * Gm * (48 / √3 * L') / (c * t)
          = Gm / (c * t) * (Γ * (1 / 2 + 2 * Cn + 48 / √3 * L')) := by field_simp
      rw [e]
      have h1 : Γ * (1 / 2 + 2 * Cn + 48 / √3 * L') ≤ Γ * (1 + 2 * Cn + 48 / √3 * L') := by gcongr; norm_num
      calc Gm / (c * t) * (Γ * (1 / 2 + 2 * Cn + 48 / √3 * L'))
          ≤ Gm / (c * t) * (r₀ / 4 * t) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = Gm * r₀ / (4 * c) := by field_simp
    have e5 : Gm * r₀ / (2 * c) = Gm * r₀ / (4 * c) + Gm * r₀ / (4 * c) := by ring
    linarith
  have hNpos : 0 < Nn := lt_of_lt_of_le (by positivity) hNlow
  -- Cvs.L2a.ModeTailTerminalSigmaFree at the fixed cutoff `X`, `η = 1/c`, `η_p = t^{−30}`, prime window `t²⁰/ρ²`
  have hT : 2 * (2 * π * X) ^ 2 + 1 / 2 ≤ c ^ 2 - χ := by
    rw [← hTdef]; linarith
  have hηθ : 1 + 1 / c ≤ √(1 + √(c ^ 2 - χ) / c) := by
    apply Real.le_sqrt_of_sq_le
    have hσ : √(c ^ 2 - χ) / c = ρ ^ 2 := by
      have hd' : c ^ 2 - χ = (c * ρ ^ 2) ^ 2 := by
        have := hLdef; rw [← hρ4] at this
        have h := this.symm; rw [div_eq_iff (by positivity)] at h; rw [h]; ring
      rw [hd', sqrt_sq (by positivity)]; field_simp
    rw [hσ]
    have h3 : 3 / c ≤ ρ ^ 2 := by
      by_contra h
      push Not at h
      have hm := mul_lt_mul'' h h (by positivity) (by positivity)
      have h9 : 9 / c ≤ ρ ^ 4 := by
        rw [hρ4, div_le_iff₀ hc0]; linarith
      have h9' : 9 / c ^ 2 ≤ 9 / c := div_le_div_of_nonneg_left (by norm_num) hc0 (by nlinarith)
      have e : 3 / c * (3 / c) = 9 / c ^ 2 := by field_simp; norm_num
      have e' : ρ ^ 2 * ρ ^ 2 = ρ ^ 4 := by ring
      linarith
    have h4 : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc1
    have h5 : 1 / c * (1 / c) ≤ 1 / c := mul_le_of_le_one_left (by positivity) h4
    have e : (1 + 1 / c) ^ 2 = 1 + 2 * (1 / c) + 1 / c * (1 / c) := by ring
    have e3 : 3 / c = 3 * (1 / c) := by ring
    rw [e]; linarith
  set sp := t ^ 20 / ρ ^ 2 with hspdef
  have hsp1 : 1 ≤ sp := by
    rw [hspdef, le_div_iff₀ (by positivity), one_mul]
    exact (pow_le_one₀ hρ0.le hρ1).trans (one_le_pow₀ ht1)
  have hspc : sp ^ 2 * L ≤ c := by
    have e : sp ^ 2 * L = t ^ 40 := by rw [hspdef, ← hρ4]; field_simp
    rw [e]
  have hFa : a₀ ≤ F := by linarith
  have hηp : (0 : ℝ) < 1 / t ^ 30 := by positivity
  have hηpb : 1 + 1 / t ^ 30 ≤ 2 ^ (J + 1) := by
    have : 1 / t ^ 30 ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ ht1
    linarith
  have key := Cvs.L2a.ModeTailTerminalSigmaFree.weilForm_tailF_ge (c := c) (χ := χ) (G := G) (K := K) (Ξ := Ξ) (η := 1 / c)
    (ηp := 1 / t ^ 30) (x' := X) (s := sp) (ψ := ψ) (u := u) P R N M J Kf hc1 hχ0 hχ hsp1 hspc hηp hηpb
    hψ hu hu1 hC1' hG hG0 hedge hedge1 hM hΞ hidx hrb hX0 hKf hFa hT (by positivity) hηθ hNpos
  rw [← hbdef, ← hNn, ← hFdef, ← hTdef] at key
  set B := Cvs.L2a.TailModesPoleMellinValues.mellinBound c χ G (1 / c) T (ψ 1) with hBdef
  set pB := Cvs.L2a.ModeTailTerminalSigmaFree.primeBound c χ G K sp with hpB
  set qB := Cvs.L2a.ModeTailTerminalSigmaFree.poleBound c G (1 / t ^ 30) (ψ 1) with hqB
  have hexp : (F - (F - a₀) * (4 * X * B ^ 2 / Nn) - pB / Nn - qB / Nn) * Nn
      = F * Nn - (F - a₀) * (4 * X * B ^ 2) - pB - qB := by field_simp
  rw [hexp] at key
  -- the three margins
  have hpB' : pB ≤ pinf * Nn := by
    have h1 := Cvs.L2a.SigmaFreeBoundSizesPlunge.primeBound_le (χ := χ) (K := K) hG0 ht1 hρ0 hρ1 hρt hLρ
    rw [← hcdef, ← hspdef, ← hpB, ← hPc] at h1
    calc pB ≤ G * Pc / c := h1
      _ ≤ Γ * Gm * Pc / c := by gcongr
      _ = pinf * (Gm * r₀ / (4 * c)) := by rw [hpinf]; field_simp
      _ ≤ pinf * Nn := by gcongr
  have hqB' : qB ≤ Nn := by
    have h1 := Cvs.L2a.SigmaFreeBoundSizesPlunge.poleBound_le (K := K) (ψ1 := ψ 1) hG0 ht1 hedge1
    rw [← hcdef, ← hqB, ← hQc] at h1
    have ht20 : τ3 ≤ t ^ 20 := htτ3.trans (le_self_pow₀ ht1 (by norm_num))
    calc qB ≤ G * Qc / (c * t ^ 20) := h1
      _ ≤ Γ * Gm * Qc / (c * t ^ 20) := by gcongr
      _ = Gm * r₀ / (4 * c) * (τ3 / t ^ 20) := by rw [hτ3]; field_simp
      _ ≤ Gm * r₀ / (4 * c) * 1 := by
          gcongr; rw [div_le_one (by positivity)]; exact ht20
      _ ≤ Nn := by linarith
  have hlow : (F - a₀) * (4 * X * B ^ 2) ≤ Nn := by
    have hB0 : 0 ≤ B := mellinBound_nonneg hc0 hG0 (by positivity) hT0 hχ
    have hB := Cvs.Prolate.Mellin.RungMellinBoundFixedCutoff.mellinBound_le (K := K) (T := T) (ψ1 := ψ 1) hc1 hσ1 hT0 hG0 hedge1
    rw [← hBdef, ← hEm] at hB
    have hsc0 : 0 < √c := sqrt_pos.mpr hc0
    have hcc : √c * √c = c := mul_self_sqrt hc0.le
    have he2 : 32 * √2 * √c / (c ^ 2 - χ) ≤ 32 * √2 / (C * √c) := by
      rw [div_le_div_iff₀ hd (by positivity)]
      calc 32 * √2 * √c * (C * √c) = 32 * √2 * (C * (√c * √c)) := by ring
        _ = 32 * √2 * (C * c) := by rw [hcc]
        _ ≤ 32 * √2 * (c ^ 2 - χ) := by gcongr
    have hB' : B ≤ √G * (Em / c + 32 * √2 / (C * √c)) :=
      hB.trans (mul_le_mul_of_nonneg_left (by linarith) (sqrt_nonneg _))
    have hEm0 : 0 ≤ Em := by rw [hEm]; unfold Cvs.Prolate.Mellin.RungMellinBoundFixedCutoff.E; positivity
    have hB2 : B ^ 2 ≤ 2 * G * (Em ^ 2 / c ^ 2 + 2048 / (C ^ 2 * c)) := by
      have h1 := pow_le_pow_left₀ hB0 hB' 2
      have h2 : (Em / c + 32 * √2 / (C * √c)) ^ 2 ≤ 2 * ((Em / c) ^ 2 + (32 * √2 / (C * √c)) ^ 2) := by
        have key : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := fun a b => by
          rw [show (a + b) ^ 2 = 2 * (a ^ 2 + b ^ 2) - (a - b) ^ 2 by ring]
          exact sub_le_self _ (sq_nonneg _)
        exact key _ _
      have e1 : (32 * √2 / (C * √c)) ^ 2 = 2048 / (C ^ 2 * c) := by
        rw [div_pow, mul_pow, mul_pow, sq_sqrt (by norm_num), sq_sqrt hc0.le]; norm_num
      have e2 : (Em / c) ^ 2 = Em ^ 2 / c ^ 2 := by rw [div_pow]
      rw [mul_pow, sq_sqrt hG0] at h1
      rw [e1, e2] at h2
      calc B ^ 2 ≤ G * (Em / c + 32 * √2 / (C * √c)) ^ 2 := h1
        _ ≤ G * (2 * (Em ^ 2 / c ^ 2 + 2048 / (C ^ 2 * c))) := mul_le_mul_of_nonneg_left h2 hG0
        _ = 2 * G * (Em ^ 2 / c ^ 2 + 2048 / (C ^ 2 * c)) := by ring
    have hk1 : 16 * M₀ * Γ * Em ^ 2 ≤ r₀ * c := by
      rw [hτ5, div_le_iff₀ hr₀0] at htτ5
      have := mul_le_mul_of_nonneg_left hct hr₀0.le
      linarith
    calc (F - a₀) * (4 * X * B ^ 2) = M₀ * B ^ 2 := by rw [hM₀]; ring
      _ ≤ M₀ * (2 * (Γ * Gm) * (Em ^ 2 / c ^ 2 + 2048 / (C ^ 2 * c))) := by
          apply mul_le_mul_of_nonneg_left _ hM₀0
          have : 2 * G * (Em ^ 2 / c ^ 2 + 2048 / (C ^ 2 * c))
              ≤ 2 * (Γ * Gm) * (Em ^ 2 / c ^ 2 + 2048 / (C ^ 2 * c)) := by gcongr
          exact hB2.trans this
      _ = Gm / c * (2 * M₀ * Γ * Em ^ 2 / c + 2 * M₀ * Γ * 2048 / C ^ 2) := by
          field_simp
      _ ≤ Gm / c * (r₀ / 8 + r₀ / 8) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have a1 : 2 * M₀ * Γ * Em ^ 2 / c ≤ r₀ / 8 := by
            rw [div_le_div_iff₀ hc0 (by norm_num)]; linarith
          have a2 : 2 * M₀ * Γ * 2048 / C ^ 2 ≤ r₀ / 8 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          exact add_le_add a1 a2
      _ = Gm * r₀ / (4 * c) := by field_simp; ring
      _ ≤ Nn := hNlow
  -- the margin
  have hF3 : pinf + 3 ≤ F := by have := abs_nonneg a₀; linarith
  have hm := mul_nonneg (sub_nonneg.mpr hF3) hNpos.le
  have e : F * Nn = (F - (pinf + 3)) * Nn + pinf * Nn + 3 * Nn := by ring
  linarith

/-- **L2a for the tail of `M` modes across the plunge band**: for fixed `K`, `Γ` there is `C ≥ 1` such that for
every large `c`, every `χ ≥ 0` with `C c ≤ c² − χ`, the Weil form of the tail is positive, uniformly in `M`, `J ≥ 1`
and the prime truncation. -/
theorem weilForm_tailF_plunge_pos (K Γ : ℝ) (Kf : ℕ) (hΓ : 1 ≤ Γ) (hKf : 1 ≤ Kf) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ c in atTop, ∀ (χ G Gm Ξ : ℝ) (ψ u : ℝ → ℝ) (P R N M J : ℕ),
      0 ≤ χ → C * c ≤ c ^ 2 - χ →
      (∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ) →
      (∀ ξ ∈ Icc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) → u 1 = 0 →
      ContDiffOn ℝ 1 ψ (Icc 1 Ξ) →
      (∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) →
      (∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) → ψ 1 ^ 2 ≤ K * G →
      (∀ τ ∈ Icc (√2) (2 ^ (J + 1)), Gm ≤ energy (aP c χ) ψ u τ) → 0 < Gm → G ≤ Γ * Gm →
      1 ≤ J → 1 ≤ M → (M : ℝ) * 2 ^ (J + 1) ≤ Ξ →
      Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N → (N : ℝ) + 2 ≤ 2 ^ (J + 1) →
      0 < Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF ψ M (2 ^ (J + 1)))) := by
  obtain ⟨C, hC, h⟩ := weilForm_tailF_plunge_pos_t K Γ Kf hΓ hKf
  refine ⟨C, hC, ?_⟩
  have ht : Tendsto (fun c : ℝ => c ^ ((1 : ℝ) / 40)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [ht.eventually h, eventually_gt_atTop 0] with c hc hc0
  have e40 : (c ^ ((1 : ℝ) / 40)) ^ 40 = c := by
    rw [← rpow_natCast, ← rpow_mul hc0.le]; norm_num
  rw [e40] at hc
  exact hc

end Cvs.L2a.ModeTailPlungeBandPositive
