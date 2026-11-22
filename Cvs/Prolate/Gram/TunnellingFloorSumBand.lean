import Mathlib
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog
import Cvs.Prolate.PlungePowerSumPolylog

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tunnelling floor sum from the CP-b floor and the band floor alone

`TunnellingFloorSumPlunge`'s deep rungs as there; on the band rungs `σ'_j ≥ x^{−ε}` and `PlungePowerSumPolylog`'s polylogarithmic plunge power sum give
`x^{ε/2}·M(1 + log c)²`. Together: `CaseFiniteFromWindowChain`'s `ExtTunnelSum η` for every `η ≥ 0`.
-/

noncomputable section

open Real Set Filter Finset Topology
open Cvs.Prolate.EvenRungsByIndex (lev lamR)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram)
open Cvs.Route.Visibility.WindowChainCellFloors (finOfSF)
open Cvs.Prolate.TunnellingIntegralMargin (gStar)

namespace Cvs.Prolate.Gram.TunnellingFloorSumBand
open Cvs.ZeroCounting

/-- `plungePoly q c ≤ (4 + 2/q + 3)(1 + log c)²` for `c ≥ 1`. -/
theorem plungePoly_le {q c : ℝ} (hq : 0 < q) (hc : 1 ≤ c) :
    Cvs.Prolate.PlungePowerSumPolylog.plungePoly q c ≤ (4 + 2 / q + 3) * (1 + log c) ^ 2 := by
  have hc0 : 0 < c := by linarith
  set ℓ := log c with hℓ
  have hℓ0 : 0 ≤ ℓ := log_nonneg hc
  have hπ := pi_gt_three
  have hA : 0 ≤ 4 + 2 / q := by positivity
  have h2 : log (2 * c) ≤ 1 + ℓ := by
    rw [log_mul (by norm_num) hc0.ne']; linarith [log_two_lt_d9]
  have h8 : log (8 * c ^ 2 * 1) ≤ 3 + 2 * ℓ := by
    rw [mul_one, log_mul (by norm_num) (by positivity), log_pow]
    have : log 8 < 3 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; push_cast; linarith [log_two_lt_d9]
    push_cast; linarith
  have hsq : log (c ^ 2 * 1) = 2 * ℓ := by rw [mul_one, log_pow]; push_cast; ring
  have h80 : 0 ≤ log (8 * c ^ 2 * 1) := log_nonneg (by nlinarith)
  have herr : Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 ≤ 2 + ℓ := by
    unfold Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow
    rw [hsq]
    have hn : 0 ≤ log (8 * c ^ 2 * 1) / 2 + 1 + 2 * ℓ / 4 := by positivity
    have : (log (8 * c ^ 2 * 1) / 2 + 1 + 2 * ℓ / 4) / π ≤ (log (8 * c ^ 2 * 1) / 2 + 1 + 2 * ℓ / 4) / 3 :=
      div_le_div_of_nonneg_left hn (by norm_num) hπ.le
    linarith
  have hmain : (4 + 2 / q) * ℓ / (2 * π) * (1 + log (2 * c) / 2) ≤ (4 + 2 / q) * ℓ / 6 * (3 / 2 + ℓ / 2) := by
    have hl2 : 0 ≤ log (2 * c) := log_nonneg (by linarith)
    have hAℓ : 0 ≤ (4 + 2 / q) * ℓ := mul_nonneg hA hℓ0
    have e1 : (4 + 2 / q) * ℓ / (2 * π) ≤ (4 + 2 / q) * ℓ / 6 :=
      div_le_div_of_nonneg_left hAℓ (by norm_num) (by linarith)
    exact mul_le_mul e1 (by linarith) (by positivity) (by positivity)
  unfold Cvs.Prolate.PlungePowerSumPolylog.plungePoly
  rw [← hℓ]
  have hAℓ : 0 ≤ (4 + 2 / q) * ℓ := mul_nonneg hA hℓ0
  nlinarith [mul_nonneg hAℓ hℓ0, mul_nonneg hA (sq_nonneg ℓ)]

/-- **The plunge power sum is subpolynomial**: for `q, ε > 0` some `M` has, eventually,
`plungePoly q (2πx) ≤ M·x^ε`. -/
theorem exists_plungePoly_le {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ᶠ x : ℕ in atTop, Cvs.Prolate.PlungePowerSumPolylog.plungePoly q (2 * π * x) ≤ M * (x : ℝ) ^ ε := by
  set b := 2 / ε * (225 : ℝ) ^ (ε / 2)
  refine ⟨(4 + 2 / q + 3) * (1 + b) ^ 2, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with x hx1
  have hx : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hc : 1 ≤ 2 * π * (x : ℝ) := by nlinarith [pi_gt_three]
  have hb0 : 0 ≤ b := by positivity
  have hlog := Cvs.Prolate.Gram.TunnellingFloorSumPlunge.log_le_rpow hx hε
  have hlc : log (2 * π * x) ≤ log (100 * (2 * π * x) / π + 25) :=
    log_le_log (by linarith) (by
      have hπ := pi_pos
      rw [show 100 * (2 * π * (x : ℝ)) / π = 200 * x by field_simp; ring]
      nlinarith [pi_lt_four])
  set y := (x : ℝ) ^ (ε / 2)
  have hy1 : 1 ≤ y := one_le_rpow hx (by linarith)
  have hyy : y ^ 2 = (x : ℝ) ^ ε := by
    rw [← rpow_natCast, ← rpow_mul (by linarith)]; norm_num
  have hl0 : 0 ≤ log (2 * π * x) := log_nonneg hc
  have h1 : 1 + log (2 * π * x) ≤ (1 + b) * y := by nlinarith
  have hA : 0 ≤ 4 + 2 / q + 3 := by positivity
  calc Cvs.Prolate.PlungePowerSumPolylog.plungePoly q (2 * π * x) ≤ (4 + 2 / q + 3) * (1 + log (2 * π * x)) ^ 2 := plungePoly_le hq hc
    _ ≤ (4 + 2 / q + 3) * ((1 + b) * y) ^ 2 := by gcongr
    _ = (4 + 2 / q + 3) * (1 + b) ^ 2 * (x : ℝ) ^ ε := by rw [mul_pow, hyy]; ring

end Cvs.Prolate.Gram.TunnellingFloorSumBand

end
