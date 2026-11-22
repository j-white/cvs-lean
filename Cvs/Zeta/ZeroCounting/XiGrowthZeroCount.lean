import Mathlib
import Cvs.Zeta.CompletedXiOrderOneGrowth
import Cvs.Zeta.ZeroCounting.JensenChainConstants
import Cvs.Zeta.ZeroCounting.JensenConstantBound
import Cvs.Zeta.ZeroCounting.JensenGrowthConstant
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The zero count against a smaller number

`Γ(s/2)` carries the exponent `s.re/2 + 1` and the two polynomial factors cost two more, so
`‖ξ s‖ ≤ (π²/6)·(‖s‖+3)^(‖s‖/2+4)`.  Jensen reads `N(T) ≤ 4·T·log T` off that directly.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex Real Cvs.Zeta.Explicit.Venue

namespace Cvs.Zeta.ZeroCounting.XiGrowthZeroCount
open Cvs.ZeroFree

/-- **The right half-plane, with the Gamma exponent kept.** -/
theorem norm_right {s : ℂ} (hs : 2 ≤ s.re) :
    ‖completedXiCore s‖ ≤ Real.pi ^ 2 / 6 * (‖s‖ + 2) ^ (‖s‖ / 2 + 3) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hn : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
  set R : ℝ := ‖s‖ + 2 with hRdef
  have hR1 : (1:ℝ) ≤ R := by rw [hRdef]; linarith
  have hR0 : (0:ℝ) < R := by linarith
  have hre : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hx : (1:ℝ) ≤ s.re / 2 := by linarith
  have hgamma : ‖Complex.Gamma (s / 2)‖ ≤ R ^ (‖s‖ / 2 + 1) := by
    have h1 : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
      convert norm_Complex_Gamma_le_Real_Gamma (s := s / 2) (by simp; linarith) using 1
      simp
    have h2 : Real.Gamma (s.re / 2) ≤ (s.re / 2 + 1) ^ (s.re / 2 + 1) :=
      Cvs.Zeta.ZeroCounting.JensenChainConstants.Gamma_le_rpow_growth hx
    have h3 : (s.re / 2 + 1) ^ (s.re / 2 + 1) ≤ R ^ (s.re / 2 + 1) :=
      Real.rpow_le_rpow (by linarith) (by rw [hRdef]; linarith) (by linarith)
    have h4 : R ^ (s.re / 2 + 1) ≤ R ^ (‖s‖ / 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
    linarith
  have hzeta : ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6 := by
    have h := norm_riemannZeta_le_zetaTwoMajorant hs
    rwa [Cvs.Zeta.ZeroCounting.JensenChainConstants.zetaTwoMajorant_eq] at h
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := norm_pi_cpow_neg_half_le_one (by linarith)
  have hrp : (0:ℝ) ≤ R ^ (‖s‖ / 2 + 1) := Real.rpow_nonneg hR0.le _
  have hcz : ‖completedRiemannZeta s‖ ≤ Real.pi ^ 2 / 6 * R ^ (‖s‖ / 2 + 1) := by
    have hGR : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hmul : riemannZeta s * Complex.Gammaℝ s = completedRiemannZeta s :=
      (eq_div_iff hGR).mp (riemannZeta_def_of_ne_zero (s := s) hs0)
    rw [show completedRiemannZeta s
        = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s by
      rw [← Complex.Gammaℝ_def]
      calc completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := hmul.symm
        _ = Complex.Gammaℝ s * riemannZeta s := mul_comm _ _]
    rw [norm_mul, norm_mul]
    have hstep : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ 1 * R ^ (‖s‖ / 2 + 1) :=
      mul_le_mul hpi hgamma (norm_nonneg _) zero_le_one
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖
        ≤ (1 * R ^ (‖s‖ / 2 + 1)) * (Real.pi ^ 2 / 6) :=
          mul_le_mul hstep hzeta (norm_nonneg _) (by simpa using hrp)
      _ = Real.pi ^ 2 / 6 * R ^ (‖s‖ / 2 + 1) := by ring
  rw [completedXiCore_eq_mul_completedRiemannZeta hs0 hs1, norm_mul, norm_mul]
  have hsR : ‖s‖ ≤ R := by rw [hRdef]; linarith
  have hs1R : ‖s - 1‖ ≤ R := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ ≤ R := by rw [hRdef]; simp
  have hpoly : ‖s‖ * ‖s - 1‖ ≤ R ^ (2:ℝ) := by
    rw [Real.rpow_two]
    nlinarith [norm_nonneg (s - 1)]
  have hcomb : R ^ (2:ℝ) * R ^ (‖s‖ / 2 + 1) = R ^ (‖s‖ / 2 + 3) := by
    have he : (2:ℝ) + (‖s‖ / 2 + 1) = ‖s‖ / 2 + 3 := by ring
    rw [← Real.rpow_add hR0, he]
  calc ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta s‖
      ≤ R ^ (2:ℝ) * (Real.pi ^ 2 / 6 * R ^ (‖s‖ / 2 + 1)) :=
        mul_le_mul hpoly hcz (norm_nonneg _) (Real.rpow_nonneg hR0.le _)
    _ = Real.pi ^ 2 / 6 * (R ^ (2:ℝ) * R ^ (‖s‖ / 2 + 1)) := by ring
    _ = Real.pi ^ 2 / 6 * R ^ (‖s‖ / 2 + 3) := by rw [hcomb]

/-- **The global bound, in `‖s‖` alone.** -/
theorem norm_global (s : ℂ) :
    ‖completedXiCore s‖ ≤ Real.pi ^ 2 / 6 * (‖s‖ + 3) ^ (‖s‖ / 2 + 4) := by
  have hn : (0:ℝ) ≤ ‖s‖ := norm_nonneg s
  have hone : ‖(1:ℂ)‖ = 1 := by simp
  set G : ℝ := ‖s‖ + 3 with hGdef
  have hG3 : (3:ℝ) ≤ G := by rw [hGdef]; linarith
  have hG1 : (1:ℝ) ≤ G := by linarith
  have hG0 : (0:ℝ) < G := by linarith
  have hK1 : (1:ℝ) ≤ Real.pi ^ 2 / 6 := Cvs.Zeta.ZeroCounting.JensenGrowthConstant.one_le_zetaTwo
  by_cases hright : 2 ≤ s.re
  · have h := norm_right hright
    have hb : (‖s‖ + 2) ^ (‖s‖ / 2 + 3) ≤ G ^ (‖s‖ / 2 + 3) :=
      Real.rpow_le_rpow (by linarith) (by rw [hGdef]; linarith) (by linarith)
    have he : G ^ (‖s‖ / 2 + 3) ≤ G ^ (‖s‖ / 2 + 4) :=
      Real.rpow_le_rpow_of_exponent_le hG1 (by linarith)
    exact h.trans (mul_le_mul_of_nonneg_left (hb.trans he) (by linarith))
  · by_cases hleft : s.re ≤ -1
    · have hwre : 2 ≤ (1 - s).re := by
        have hre : (1 - s).re = 1 - s.re := by simp
        rw [hre]; linarith
      have hwn : ‖1 - s‖ ≤ ‖s‖ + 1 := by
        calc ‖1 - s‖ ≤ ‖(1:ℂ)‖ + ‖s‖ := norm_sub_le _ _
          _ = ‖s‖ + 1 := by rw [hone]; ring
      have hwnn : (0:ℝ) ≤ ‖1 - s‖ := norm_nonneg _
      have h := norm_right hwre
      have hxi : ‖completedXiCore s‖ = ‖completedXiCore (1 - s)‖ := by
        rw [completedXiCore_one_sub]
      have hb : (‖1 - s‖ + 2) ^ (‖1 - s‖ / 2 + 3) ≤ G ^ (‖1 - s‖ / 2 + 3) :=
        Real.rpow_le_rpow (by linarith) (by rw [hGdef]; linarith) (by linarith)
      have he : G ^ (‖1 - s‖ / 2 + 3) ≤ G ^ (‖s‖ / 2 + 4) :=
        Real.rpow_le_rpow_of_exponent_le hG1 (by linarith)
      rw [hxi]
      exact h.trans (mul_le_mul_of_nonneg_left (hb.trans he) (by linarith))
    · have h1 : (-1:ℝ) ≤ s.re := le_of_not_ge hleft
      have h2 : s.re ≤ 2 := le_of_not_ge hright
      have hL := Cvs.Zeta.ZeroCounting.JensenChainConstants.norm_completedRiemannZeta₀_le_strip_num h1 h2
      have hsG : ‖s‖ ≤ G := by rw [hGdef]; linarith
      have hs1G : ‖s - 1‖ ≤ G := by
        calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
          _ = ‖s‖ + 1 := by rw [hone]
          _ ≤ G := by rw [hGdef]; linarith
      have hLnn : (0:ℝ) ≤ ‖completedRiemannZeta₀ s‖ := norm_nonneg _
      have hbound : ‖completedXiCore s‖ ≤ G * G * (1/36.3) + 1 := by
        rw [completedXiCore]
        calc ‖s * (s - 1) * completedRiemannZeta₀ s + 1‖
            ≤ ‖s * (s - 1) * completedRiemannZeta₀ s‖ + ‖(1:ℂ)‖ := norm_add_le _ _
          _ = ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖ + 1 := by
              rw [norm_mul, norm_mul, hone]
          _ ≤ G * G * (1/36.3) + 1 := by
              have hp : ‖s‖ * ‖s - 1‖ ≤ G * G :=
                mul_le_mul hsG hs1G (norm_nonneg _) (by linarith)
              nlinarith
      have hGsq : G * G * (1/36.3) + 1 ≤ G ^ (2:ℝ) := by
        rw [Real.rpow_two]; nlinarith
      have hGe : G ^ (2:ℝ) ≤ G ^ (‖s‖ / 2 + 4) :=
        Real.rpow_le_rpow_of_exponent_le hG1 (by linarith)
      have hfin : G ^ (‖s‖ / 2 + 4) ≤ Real.pi ^ 2 / 6 * G ^ (‖s‖ / 2 + 4) :=
        le_mul_of_one_le_left (Real.rpow_nonneg hG0.le _) hK1
      exact hbound.trans (hGsq.trans (hGe.trans hfin))

/-- **The sphere of radius `2(T+2)` about `2`.** -/
theorem norm_sphere {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere (2 : ℂ) (2 * (T + 2))) :
    ‖completedXiCore z‖ ≤ Real.pi ^ 2 / 6 * (2 * T + 9) ^ (T + 7) := by
  have hzd : ‖z - 2‖ = 2 * (T + 2) := by
    simpa [Complex.dist_eq] using (Metric.mem_sphere.mp hz)
  have htwo : ‖(2:ℂ)‖ = 2 := by simp
  have hzn : ‖z‖ ≤ 2 * T + 6 := by
    calc ‖z‖ = ‖(z - 2) + 2‖ := by congr 1; ring
      _ ≤ ‖z - 2‖ + ‖(2:ℂ)‖ := norm_add_le _ _
      _ = 2 * (T + 2) + 2 := by rw [hzd, htwo]
      _ = 2 * T + 6 := by ring
  have hznn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hb : (‖z‖ + 3) ^ (‖z‖ / 2 + 4) ≤ (2 * T + 9) ^ (‖z‖ / 2 + 4) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have he : (2 * T + 9) ^ (‖z‖ / 2 + 4) ≤ (2 * T + 9) ^ (T + 7) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  exact (norm_global z).trans
    (mul_le_mul_of_nonneg_left (hb.trans he) (by positivity))

/-- The Jensen side condition. -/
theorem one_le_bound {T : ℝ} (hT : 0 ≤ T) :
    (1:ℝ) ≤ Real.pi ^ 2 / 6 * (2 * T + 9) ^ (T + 7) := by
  have h1 : (1:ℝ) ≤ Real.pi ^ 2 / 6 := Cvs.Zeta.ZeroCounting.JensenGrowthConstant.one_le_zetaTwo
  have h2 : (1:ℝ) ≤ (2 * T + 9) ^ (T + 7) :=
    Real.one_le_rpow (by linarith) (by linarith)
  nlinarith

/-- **`N(T) ≤ 4·T·log T` for `T ≥ 9 + e`.** -/
theorem nontrivialZetaZeroCount_le_four {T : ℝ} (hT : 9 + Real.exp 1 ≤ T) :
    (nontrivialZetaZeroCount T : ℝ) ≤ 4 * T * Real.log T := by
  have he1 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hu1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hT117 : (11.7:ℝ) ≤ T := by linarith
  have hTpos : (0:ℝ) < T := by linarith
  have hT0 : (0:ℝ) ≤ T := hTpos.le
  have he2 : Real.exp 2 ≤ T := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hlogT : (2:ℝ) ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).mpr he2
  have hlog2l : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2u : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have h34 : Real.log 3 ≤ Real.log 4 := by gcongr; norm_num
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hbase : (0:ℝ) < 2 * T + 9 := by linarith
  have hA : Real.log (2 * T + 9) ≤ Real.log 3 + Real.log T := by
    have h2 : Real.log (2 * T + 9) ≤ Real.log (3 * T) := by gcongr; linarith
    rwa [Real.log_mul (by norm_num) hTpos.ne'] at h2
  have hmul : (T + 7) * Real.log (2 * T + 9) ≤ (T + 7) * (Real.log 3 + Real.log T) :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have hxi2 : (0:ℝ) < ‖completedXiCore 2‖ := norm_pos_iff.mpr completedXiCore_two_ne_zero
  have hJ := nontrivialZetaZeroCount_le_of_completedXi_sphere_bound hT0
    (one_le_bound hT0) (fun z hz => norm_sphere hT0 hz)
  have hlogM : Real.log (Real.pi ^ 2 / 6 * (2 * T + 9) ^ (T + 7))
      = Real.log (Real.pi ^ 2 / 6) + (T + 7) * Real.log (2 * T + 9) := by
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hbase _).ne', Real.log_rpow hbase]
  have hnum : Real.log (Real.pi ^ 2 / 6 * (2 * T + 9) ^ (T + 7) / ‖completedXiCore 2‖)
      = Real.log (Real.pi ^ 2 / 6) + (T + 7) * Real.log (2 * T + 9)
        - Real.log ‖completedXiCore 2‖ := by
    rw [Real.log_div (by positivity) hxi2.ne', hlogM]
  have hD : Real.log (Real.pi ^ 2 / 6) - Real.log ‖completedXiCore 2‖ ≤ 0.71 := by
    have h := Cvs.Zeta.ZeroCounting.JensenConstantBound.jensenD_le
    have ha := le_abs_self (Real.log (Real.pi ^ 2 / 6))
    have hb := neg_le_abs (Real.log ‖completedXiCore 2‖)
    linarith
  rw [hnum] at hJ
  refine hJ.trans ?_
  rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
  have hkey : (0:ℝ) ≤ (T - 11.7) * (Real.log T - 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hkey, hmul, hD, hlog3, hlog2l, hlogT, hT117]

end Cvs.Zeta.ZeroCounting.XiGrowthZeroCount
