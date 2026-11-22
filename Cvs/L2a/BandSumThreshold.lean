import Mathlib
import Cvs.L2a.BandCouplingDischarged
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.FullSpanConditional
import Cvs.L2a.FullSpanThreshold
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.PlungeMassTrace

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band sum `θ̄ + 7c^{-1/8} + rSig(σ̲)` past `c0F`, factor by factor in `L = log c`
Each factor is bounded by an elementary function of `L` (`D̄ ≤ (L/2 + 1.85)/π²`, `2k(2, 10) ≤ 2.64`,
`δ_c(3/2), λ̂(wUp(c, 2)) − 1 ≤ 10⁻⁹`); then `θ̄ ≤ 0.1802` once `L ≥ 1360`, so the sum is at most `0.1804`
past `c0F ≥ e^{1360}`. The `0.2074 − 0.027` form is a target (`1/2 − RbarJ` less `0.027`, without
`3ε_τ`), not a derived `A`; `hm_full_RbarJ` compares with `1/2 − 3ε_τ(5) − RbarJ` (Cvs.L2a.SpanPlungeBound, Cvs.L2a.JointMainTerm), above `153/1000`.
-/

noncomputable section

open Real

namespace Cvs.L2a.BandSumThreshold

open Cvs.Prolate.BandMassLaw (twoK wBar deltaC wUp ellF)

/-! ### Elementary bounds on the factors -/

/-- `2k(c; 2, 10) ≤ 2.64` for `c ≥ 10⁶`. -/
theorem twoK_two_ten_le {c : ℝ} (hc : 10 ^ 6 ≤ c) : twoK c 2 10 ≤ 264 / 100 := by
  have hc0 : 0 < c := by linarith
  have hw : wBar c 2 ≤ 1 / 2 + 1 / c := by
    unfold wBar
    rw [div_le_iff₀ (by positivity)]
    have h1 : 0 < 1 / c := by positivity
    have e : 2 / c = 2 * (1 / c) := by ring
    rw [e]
    nlinarith
  have hcinv : 1 / c ≤ 1 / 10 ^ 6 := one_div_le_one_div_of_le (by norm_num) hc
  have hd : (7499 / 10000 : ℝ) ≤ 1 - wBar c 2 / 2 := by linarith
  have hd2 : (7499 / 10000 : ℝ) ^ 2 ≤ (1 - wBar c 2 / 2) ^ 2 := pow_le_pow_left₀ (by norm_num) hd 2
  have hinv : 1 / (1 - wBar c 2 / 2) ^ 2 ≤ 1 / (7499 / 10000 : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by norm_num) hd2
  have hden : (4 : ℝ) ≤ 2 * (2 + 2 / c) := by
    have : 0 < 2 / c := by positivity
    linarith
  unfold twoK
  rw [div_le_iff₀ (by positivity)]
  have hnum : 2 * (1 + 1 / (1 - wBar c 2 / 2) ^ 2) + 10 / 2 ≤ 2 * (1 + 1 / (7499 / 10000 : ℝ) ^ 2) + 5 := by
    linarith
  have hpos : 0 ≤ 2 * (1 + 1 / (1 - wBar c 2 / 2) ^ 2) + 10 / 2 := by positivity
  nlinarith

/-- `ℓ(3/2) = log 5`. -/
theorem ellF_three_halves : ellF (3 / 2) = Real.log 5 := by
  unfold ellF; norm_num

/-- `wUp(c, 3/2) = 12/(5c)`. -/
theorem wUp_three_halves (c : ℝ) : wUp c (3 / 2) = 12 / (5 * c) := by
  unfold wUp Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · field_simp; ring

/-- `wUp(c, 2) = 4/(3c)`. -/
theorem wUp_two (c : ℝ) : wUp c 2 = 4 / (3 * c) := by
  unfold wUp Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · field_simp; ring

/-- `δ_c(3/2) ≤ 10⁻⁹` for `c ≥ 10¹²`. -/
theorem deltaC_three_halves_le {c : ℝ} (hc : 10 ^ 12 ≤ c) : deltaC c (3 / 2) ≤ 1 / 10 ^ 9 := by
  have hc0 : 0 < c := by linarith
  have hl := Real.log_five_gt_d9
  set t := 1 / c with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 10 ^ 12 := one_div_le_one_div_of_le (by norm_num) hc
  have hpP : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP (3 / 2) = 5 / 4 := by unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP; norm_num
  have h2 : 2 / (c * Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP (3 / 2) * ellF (3 / 2)) ≤ t := by
    rw [hpP, ellF_three_halves, ht, div_le_div_iff₀ (by positivity) hc0]
    nlinarith
  have hw : wUp c (3 / 2) / 2 = 6 / 5 * t := by rw [wUp_three_halves, ht]; field_simp; ring
  have hd : 0 < (1 - wUp c (3 / 2) / 2) ^ 2 := by rw [hw]; nlinarith
  unfold deltaC
  rw [sub_le_iff_le_add, div_le_iff₀ hd, hw]
  nlinarith

/-- `λ̂(wUp(c, 2)) ≤ 1 + 10⁻⁹` for `c ≥ 10²⁰`. -/
theorem lamHat_wUp_two_le {c : ℝ} (hc : 10 ^ 20 ≤ c) :
    Cvs.L2a.BandRungOutgoingWave.lamHat (wUp c 2) ≤ 1 + 1 / 10 ^ 9 := by
  have hc0 : 0 < c := by linarith
  set w := wUp c 2 with hwd
  have hw : w = 4 / (3 * c) := wUp_two c
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw1 : w ≤ 2 / 10 ^ 20 := by
    rw [hw, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hd : 0 < (1 - w / 2) ^ 2 := by nlinarith
  have hB : Cvs.L2a.BandRungOutgoingWave.lamB w ≤ 1 + 2 * w := by
    unfold Cvs.L2a.BandRungOutgoingWave.lamB
    rw [div_le_iff₀ hd]
    have h1 : 0 ≤ w * (1 - 7 / 4 * w) := mul_nonneg hw0.le (by linarith)
    nlinarith [pow_pos hw0 3]
  have hB0 := Cvs.L2a.BandRungOutgoingWave.lamB_nonneg w
  have hsq : Cvs.L2a.BandRungOutgoingWave.lamB w ^ 2 - 1 ≤ (3 / 10 ^ 10 : ℝ) ^ 2 := by
    have : Cvs.L2a.BandRungOutgoingWave.lamB w ^ 2 ≤ (1 + 2 * w) ^ 2 := pow_le_pow_left₀ hB0 hB 2
    nlinarith
  have hs : √(Cvs.L2a.BandRungOutgoingWave.lamB w ^ 2 - 1) ≤ 3 / 10 ^ 10 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, hsq⟩
  unfold Cvs.L2a.BandRungOutgoingWave.lamHat
  linarith

/-- `log c ≤ 2√c` for `c > 0`. -/
theorem log_le_two_sqrt {c : ℝ} (hc : 0 < c) : Real.log c ≤ 2 * √c := by
  have hs : 0 < √c := Real.sqrt_pos.2 hc
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hc.le] at h
  linarith

/-- `D̄ = plungeBound c ≤ (log c/2 + 1.85)/π²` for `c ≥ 10¹²`. -/
theorem plungeBound_le_log {c : ℝ} (hc : 10 ^ 12 ≤ c) :
    Cvs.Prolate.PlungeMassTrace.plungeBound c ≤ (Real.log c / 2 + 185 / 100) / π ^ 2 := by
  have hc0 : 0 < c := by linarith
  refine (Cvs.Prolate.PlungeMassTrace.plungeBound_le (by linarith)).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hl2 : Real.log (2 * c) = Real.log 2 + Real.log c := Real.log_mul (by norm_num) hc0.ne'
  have h2 := Real.log_two_lt_d9
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  -- `log(2c³ + 1) ≤ 4 log c`
  have h4 : Real.log (2 * c ^ 3 + 1) ≤ 4 * Real.log c := by
    rw [show 4 * Real.log c = Real.log (c ^ 4) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    have : (3 : ℝ) * c ^ 3 ≤ c ^ 4 := by
      have : (3 : ℝ) ≤ c := by linarith
      nlinarith [pow_pos hc0 3]
    nlinarith [one_le_pow₀ (n := 3) (show (1 : ℝ) ≤ c by linarith)]
  have hsq := log_le_two_sqrt hc0
  have hs : (10 ^ 6 : ℝ) ≤ √c := by
    rw [Real.le_sqrt (by norm_num) hc0.le]; linarith
  have hcs : c = √c * √c := (Real.mul_self_sqrt hc0.le).symm
  have hs0 : 0 < √c := by linarith
  -- `(2 + log(2c³ + 1))/c ≤ 1/1000`
  have hA : (2 + Real.log (2 * c ^ 3 + 1)) / c ≤ 1 / 1000 := by
    rw [div_le_iff₀ hc0]
    have : 2 + 8 * √c ≤ c / 1000 := by nlinarith [mul_le_mul_of_nonneg_left hs hs0.le]
    linarith
  have hB : 1 / (4 * c) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  rw [hl2]
  linarith

/-- `7c^{-1/8} ≤ 7·10⁻¹⁰` for `c ≥ 10⁸⁰`. -/
theorem rho_le {c : ℝ} (hc : 10 ^ 80 ≤ c) : 7 * c ^ (-(1 / 8 : ℝ)) ≤ 7 / 10 ^ 10 := by
  have hc0 : 0 < c := by linarith
  have h8 : ((10 : ℝ) ^ 10) ≤ c ^ (1 / 8 : ℝ) := by
    have e : ((10 : ℝ) ^ 10) = (((10 : ℝ) ^ 10) ^ 8) ^ (((8 : ℕ) : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by positivity) (by norm_num)).symm
    rw [e, show (((8 : ℕ) : ℝ)⁻¹) = (1 / 8 : ℝ) by norm_num]
    exact Real.rpow_le_rpow (by positivity) (by norm_num; linarith) (by norm_num)
  rw [Real.rpow_neg hc0.le]
  have : (c ^ (1 / 8 : ℝ))⁻¹ ≤ 1 / 10 ^ 10 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by positivity) h8
  linarith

/-- `rSig(σ̲(c)) ≤ 129·10⁻⁹` for `c ≥ 10⁸⁰`, `σ̲ = 4c/log c`. -/
theorem rSig_sigmaLow_le {c : ℝ} (hc : 10 ^ 80 ≤ c) :
    Cvs.L2a.FullSpanConditional.rSig (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c) ≤ 129 / 10 ^ 9 := by
  have hc0 : 0 < c := by linarith
  have hlc : 0 < Real.log c := Real.log_pos (by linarith)
  have hsq := log_le_two_sqrt hc0
  have hs : (10 ^ 40 : ℝ) ≤ √c := by
    rw [Real.le_sqrt (by norm_num) hc0.le]; linarith
  have hcs : c = √c * √c := (Real.mul_self_sqrt hc0.le).symm
  set σ := Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c with hσd
  have hσ : 10 ^ 40 ≤ σ := by
    rw [hσd]; unfold Cvs.Prolate.EvenLevelIndexLemma.sigmaLow
    rw [le_div_iff₀ hlc]
    have : (10 : ℝ) ^ 40 * Real.log c ≤ 10 ^ 40 * (2 * √c) := by gcongr
    nlinarith
  have hσ0 : 0 < σ := by linarith
  have h5 : 5 / σ ≤ ((1 : ℝ) / 10 ^ 9) ^ 4 := by
    rw [div_le_iff₀ hσ0]; norm_num; linarith
  have hy : (5 / σ) ^ (1 / 4 : ℝ) ≤ 1 / 10 ^ 9 := by
    calc (5 / σ) ^ (1 / 4 : ℝ) ≤ (((1 : ℝ) / 10 ^ 9) ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h5 (by norm_num)
      _ = 1 / 10 ^ 9 := by
        rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
          Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  have := Cvs.L2a.FullSpanConditional.rSig_le_of_small hσ0 (hy.trans (by norm_num))
  linarith

/-! ### The angle `θ̄` from `f`, `e`, `D` bounded in `L` -/

/-- **`θ̄ ≤ 0.1802`**: from `f·s ≤ 1.60947`, `e·s ≤ 0.10814`, `s = L − 2.64`, `(1 + ω) ≤ 1.001`,
`D ≤ (L/2 + 1.85)/π²` and `L ≥ 1360`, `θ̄((√f + 2√(e(1 + ω)²))², D) ≤ 0.1802`. -/
theorem thetaBar_le_of {f e D L ω : ℝ} (hf : 0 ≤ f) (he : 0 ≤ e) (hL : 1360 ≤ L)
    (hfs : f * (L - 264 / 100) ≤ 160947 / 100000) (hes : e * (L - 264 / 100) ≤ 10814 / 100000)
    (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 1000) (hD : D ≤ (L / 2 + 185 / 100) / π ^ 2) :
    Cvs.L2a.BandCouplingDischarged.thetaBar ((√f + 2 * √(e * (1 + ω) ^ 2)) ^ 2) D ≤ 1802 / 10000 := by
  set s := L - 264 / 100 with hsd
  have hs0 : 0 < s := by linarith
  have hss := Real.sq_sqrt hs0.le
  have hss0 := Real.sqrt_nonneg s
  -- `√f·√s ≤ a`, `√(e(1+ω)²)·√s ≤ 1.001 b`
  have ha : √f * √s ≤ 126865 / 100000 := by
    rw [← Real.sqrt_mul hf]
    exact Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have hb : √(e * (1 + ω) ^ 2) * √s ≤ 1001 / 1000 * (32885 / 100000) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    have h1 : (1 + ω) ^ 2 ≤ (1001 / 1000 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : 0 ≤ (1 + ω) ^ 2 := sq_nonneg _
    calc e * (1 + ω) ^ 2 * s = (e * s) * (1 + ω) ^ 2 := by ring
      _ ≤ (10814 / 100000) * (1001 / 1000 : ℝ) ^ 2 := by
          apply mul_le_mul hes h1 h2 (by norm_num)
      _ ≤ _ := by norm_num
  set K : ℝ := (126865 / 100000 + 2 * (1001 / 1000 * (32885 / 100000))) ^ 2 with hK
  have hκs : (√f + 2 * √(e * (1 + ω) ^ 2)) ^ 2 * s ≤ K := by
    have hx : 0 ≤ (√f + 2 * √(e * (1 + ω) ^ 2)) * √s := by positivity
    have hy : (√f + 2 * √(e * (1 + ω) ^ 2)) * √s ≤ 126865 / 100000 + 2 * (1001 / 1000 * (32885 / 100000)) := by
      nlinarith
    calc (√f + 2 * √(e * (1 + ω) ^ 2)) ^ 2 * s = ((√f + 2 * √(e * (1 + ω) ^ 2)) * √s) ^ 2 := by
          rw [mul_pow, hss]
      _ ≤ K := pow_le_pow_left₀ hx hy 2
  -- the constants
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hr2 : (14142135 / 10000000 : ℝ) ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hq : 2 * ((3 - 2 * √2) / 2) ≤ 2 * (857865 / 10000000 : ℝ) := by linarith
  have hq0 := Cvs.L2a.BandCouplingDischarged.two_q_nonneg
  set q := 2 * ((3 - 2 * √2) / 2) with hqd
  set κ := (√f + 2 * √(e * (1 + ω) ^ 2)) ^ 2 with hκd
  have hκ0 : 0 ≤ κ := sq_nonneg _
  have hπ1' : (3141592 / 1000000 : ℝ) < π := by norm_num at hπ1 ⊢; linarith
  have hπsq : (3141592 / 1000000 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) hπ1'.le 2
  have hπ0 : 0 < π ^ 2 := by positivity
  have hD0 : D * π ^ 2 ≤ L / 2 + 185 / 100 := by rwa [le_div_iff₀ hπ0] at hD
  -- `q κ D ≤ T²`, multiplied through by `s π²`
  have key : q * κ * D * (s * π ^ 2) ≤ (1802 / 10000) ^ 2 * (s * π ^ 2) := by
    have e1 : q * κ * D * (s * π ^ 2) = q * (κ * s) * (D * π ^ 2) := by ring
    rw [e1]
    rcases le_or_gt (D * π ^ 2) 0 with hDn | hDn
    · have : 0 ≤ q * (κ * s) := mul_nonneg hq0 (mul_nonneg hκ0 hs0.le)
      have := mul_nonpos_of_nonneg_of_nonpos this hDn
      have : 0 ≤ (1802 / 10000 : ℝ) ^ 2 * (s * π ^ 2) := by positivity
      linarith
    · have t1 : q * (κ * s) * (D * π ^ 2) ≤ (2 * (857865 / 10000000)) * K * (L / 2 + 185 / 100) := by
        apply mul_le_mul _ hD0 hDn.le (by positivity)
        exact mul_le_mul hq hκs (mul_nonneg hκ0 hs0.le) (by norm_num)
      have t2 : (1802 / 10000 : ℝ) ^ 2 * (s * (3141592 / 1000000) ^ 2) ≤ (1802 / 10000) ^ 2 * (s * π ^ 2) := by
        gcongr
      have t3 : (2 * (857865 / 10000000)) * K * (L / 2 + 185 / 100)
          ≤ (1802 / 10000 : ℝ) ^ 2 * (s * (3141592 / 1000000) ^ 2) := by
        rw [hK, hsd]; norm_num; linarith
      linarith
  have hfin : q * (κ * D) ≤ (1802 / 10000) ^ 2 := by
    have hsp : 0 < s * π ^ 2 := by positivity
    have := le_of_mul_le_mul_right key hsp
    linarith [show q * (κ * D) = q * κ * D by ring]
  unfold Cvs.L2a.BandCouplingDischarged.thetaBar
  exact Real.sqrt_le_iff.2 ⟨by norm_num, hfin⟩

/-! ### The margin with `f̄` and `ē` written out at the band edge `s_b = 10` -/

/-- `L = log c ≥ 1360` and `c ≥ 10⁸⁰` from `c ≥ e^{1360}`. -/
theorem of_exp_le {c : ℝ} (hc : exp 1360 ≤ c) : 1360 ≤ Real.log c ∧ 10 ^ 80 ≤ c := by
  have hc0 : 0 < c := lt_of_lt_of_le (exp_pos _) hc
  refine ⟨by rw [← Real.log_exp 1360]; exact Real.log_le_log (exp_pos _) hc, le_trans ?_ hc⟩
  have h1 : (2 : ℝ) ^ 1360 ≤ exp 1 ^ 1360 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 1360
  rw [show (1360 : ℝ) = ((1360 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
  have : (10 : ℝ) ^ 80 ≤ 2 ^ 1360 :=
    calc (10 : ℝ) ^ 80 ≤ 16 ^ 80 := pow_le_pow_left₀ (by norm_num) (by norm_num) 80
      _ = 2 ^ 320 := by rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
      _ ≤ 2 ^ 1360 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  exact this.trans h1

/-- `log(1 + c) − 2k(c; 2, 10) ≥ log c − 2.64` for `c ≥ 10⁶`. -/
theorem den_ge {c : ℝ} (hc : 10 ^ 6 ≤ c) :
    Real.log c - 264 / 100 ≤ Real.log (1 + c) - twoK c 2 10 := by
  have := twoK_two_ten_le hc
  have : Real.log c ≤ Real.log (1 + c) := Real.log_le_log (by linarith) (by linarith)
  linarith

/-- `(N/d)·s ≤ N` for `N ≥ 0` and `0 < s ≤ d`. -/
theorem div_mul_le_of_le {N d s : ℝ} (hN : 0 ≤ N) (hs : 0 < s) (hsd : s ≤ d) : N / d * s ≤ N := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  exact mul_le_mul_of_nonneg_left hsd hN

/-- **The band margin in elementary form**: for `c ≥ e^{1360}`, `0 ≤ k ≤ 0.017211`, `0 ≤ ω ≤ 1/1000`,
`f = log 5(1 + δ_c(3/2))/(log(1 + c) − 2k(2, 10))`, `e = 2πλ̂(wUp(c, 2))k/(log(1 + c) − 2k(2, 10))`:
`θ̄((√f + 2√(e(1 + ω)²))², D̄) + 7c^{-1/8} + rSig(σ̲) ≤ 0.2074 − 0.027`. -/
theorem hm_closed {c k ω : ℝ} (hc : exp 1360 ≤ c) (hk0 : 0 ≤ k) (hk : k ≤ 17211 / 10 ^ 6)
    (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 1000) :
    Cvs.L2a.BandCouplingDischarged.thetaBar
        ((√(Real.log 5 * (1 + deltaC c (3 / 2)) / (Real.log (1 + c) - twoK c 2 10))
          + 2 * √(2 * π * Cvs.L2a.BandRungOutgoingWave.lamHat (wUp c 2) * k / (Real.log (1 + c) - twoK c 2 10)
            * (1 + ω) ^ 2)) ^ 2)
        (Cvs.Prolate.PlungeMassTrace.plungeBound c)
      + 7 * c ^ (-(1 / 8 : ℝ)) + Cvs.L2a.FullSpanConditional.rSig (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      ≤ 2074 / 10000 - 27 / 1000 := by
  obtain ⟨hL, hc80⟩ := of_exp_le hc
  have hc20 : (10 : ℝ) ^ 20 ≤ c := le_trans (by norm_num) hc80
  have hc12 : (10 : ℝ) ^ 12 ≤ c := le_trans (by norm_num) hc80
  have hc6 : (10 : ℝ) ^ 6 ≤ c := le_trans (by norm_num) hc80
  have hden := den_ge hc6
  have hs : 0 < Real.log c - 264 / 100 := by linarith
  have hδ0 := Cvs.L2a.BandCouplingDischarged.deltaC_three_halves_nonneg (show (80 : ℝ) ≤ c by linarith)
  have hδ := deltaC_three_halves_le hc12
  have hlam := lamHat_wUp_two_le hc20
  have hlam0 := Cvs.L2a.BandRungOutgoingWave.lamHat_nonneg (wUp c 2)
  have hl5 := Real.log_five_lt_d9
  have hl50 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hπ := Real.pi_lt_d6
  have hπ0 := Real.pi_pos
  have hd0 : 0 < Real.log (1 + c) - twoK c 2 10 := by linarith
  have hfs : Real.log 5 * (1 + deltaC c (3 / 2)) / (Real.log (1 + c) - twoK c 2 10) * (Real.log c - 264 / 100)
      ≤ 160947 / 100000 := by
    refine (div_mul_le_of_le (by positivity) hs hden).trans ?_
    norm_num at hl5 ⊢
    nlinarith
  have hes : 2 * π * Cvs.L2a.BandRungOutgoingWave.lamHat (wUp c 2) * k / (Real.log (1 + c) - twoK c 2 10)
      * (Real.log c - 264 / 100) ≤ 10814 / 100000 := by
    refine (div_mul_le_of_le (by positivity) hs hden).trans ?_
    have h1 : 2 * π * Cvs.L2a.BandRungOutgoingWave.lamHat (wUp c 2) ≤ 2 * 3.141593 * (1 + 1 / 10 ^ 9) := by
      nlinarith
    have h2 : 0 ≤ 2 * π * Cvs.L2a.BandRungOutgoingWave.lamHat (wUp c 2) := by positivity
    calc 2 * π * Cvs.L2a.BandRungOutgoingWave.lamHat (wUp c 2) * k
        ≤ 2 * 3.141593 * (1 + 1 / 10 ^ 9) * (17211 / 10 ^ 6) := mul_le_mul h1 hk hk0 (by norm_num)
      _ ≤ 10814 / 100000 := by norm_num
  have hθ := thetaBar_le_of (by positivity) (by positivity) hL hfs hes hω0 hω (plungeBound_le_log hc12)
  have hρ := rho_le hc80
  have hσ := rSig_sigmaLow_le hc80
  norm_num at hθ hρ hσ ⊢
  linarith

/-- **The band margin past `c0F`**: the elementary form of `hm_closed` at every `c ≥ c0F`
(Cvs.L2a.FullSpanThreshold, `c0F ≥ e^{1360}`). -/
theorem hm_c0F {c k ω : ℝ} (hc : Cvs.L2a.FullSpanThreshold.c0F ≤ c) (hk0 : 0 ≤ k) (hk : k ≤ 17211 / 10 ^ 6)
    (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 1000) :
    Cvs.L2a.BandCouplingDischarged.thetaBar
        ((√(Real.log 5 * (1 + deltaC c (3 / 2)) / (Real.log (1 + c) - twoK c 2 10))
          + 2 * √(2 * π * Cvs.L2a.BandRungOutgoingWave.lamHat (wUp c 2) * k / (Real.log (1 + c) - twoK c 2 10)
            * (1 + ω) ^ 2)) ^ 2)
        (Cvs.Prolate.PlungeMassTrace.plungeBound c)
      + 7 * c ^ (-(1 / 8 : ℝ)) + Cvs.L2a.FullSpanConditional.rSig (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      ≤ 2074 / 10000 - 27 / 1000 :=
  hm_closed (Cvs.L2a.FullSpanThreshold.c0F_bounds.1.trans hc) hk0 hk hω0 hω

/-- **The band margin past `c0F` with `BandRungOutgoingWave`'s `C_E`**: `k = cE ≤ 0.017211`. -/
theorem hm_c0F_cE {c ω : ℝ} (hc : Cvs.L2a.FullSpanThreshold.c0F ≤ c) (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 1000) :
    Cvs.L2a.BandCouplingDischarged.thetaBar
        ((√(Real.log 5 * (1 + deltaC c (3 / 2)) / (Real.log (1 + c) - twoK c 2 10))
          + 2 * √(2 * π * Cvs.L2a.BandRungOutgoingWave.lamHat (wUp c 2) * Cvs.L2a.BandRungOutgoingWave.cE
            / (Real.log (1 + c) - twoK c 2 10) * (1 + ω) ^ 2)) ^ 2)
        (Cvs.Prolate.PlungeMassTrace.plungeBound c)
      + 7 * c ^ (-(1 / 8 : ℝ)) + Cvs.L2a.FullSpanConditional.rSig (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      ≤ 2074 / 10000 - 27 / 1000 :=
  hm_c0F hc Cvs.L2a.BandRungOutgoingWave.cE_nonneg Cvs.L2a.BandRungOutgoingWave.cE_le_decimal hω0 hω

/-! ### `f̄` and `κ̄` at a general band edge `s` -/

/-- The arm fraction bound at band edge `s`, `f̄(c, s) = log 5·(1 + δ_c(3/2))/(log(1 + c) − 2k(2, s))`. -/
def fBarG (c s : ℝ) : ℝ := Real.log 5 * (1 + deltaC c (3 / 2)) / (Real.log (1 + c) - twoK c 2 s)

/-- The Cauchy–Schwarz coupling at band edge `s`, `κ̄(c, s, e) = (√f̄(c, s) + 2√e)²`. -/
def kapBarG (c s e : ℝ) : ℝ := (√(fBarG c s) + 2 * √e) ^ 2

/-! ### The margin with `κ̄(c, 10, ē_main(1 + ω)²)` -/

/-- **The band margin past `c0F` at edge `10`**: `θ̄(κ̄(c, 10, ē_main(c, 10)(1 + ω)²), D̄)
+ 7c^{-1/8} + rSig(σ̲) ≤ 0.2074 − 0.027` for `c ≥ c0F`, `0 ≤ ω ≤ 1/1000`, `ē_main` of Cvs.L2a.BandECouplingCollar. -/
theorem hm_full {c : ℝ} (hc : Cvs.L2a.FullSpanThreshold.c0F ≤ c) {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 1000) :
    Cvs.L2a.BandCouplingDischarged.thetaBar (kapBarG c 10 (Cvs.L2a.BandECouplingCollar.eMain c 10 * (1 + ω) ^ 2))
        (Cvs.Prolate.PlungeMassTrace.plungeBound c)
      + 7 * c ^ (-(1 / 8 : ℝ)) + Cvs.L2a.FullSpanConditional.rSig (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      ≤ 2074 / 10000 - 27 / 1000 :=
  hm_c0F_cE hc hω0 hω

end Cvs.L2a.BandSumThreshold
