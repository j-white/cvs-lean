import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.PlungeLawBandCellFloor
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog
import Cvs.Prolate.RungsAboveLevelCount
import Cvs.Prolate.TunnellingExponentSharpPlunge
import Cvs.Prolate.TunnellingIntegralMargin
import Cvs.Prolate.TunnellingIntegralsAgree
import Cvs.Prolate.TunnellingTraceBelowLevel
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plunge power sum of the rungs is polylogarithmic

Split at `T = 1 − δ`, `δ = A log c/c`, `A = 4 + 2/q`: below, the sharp plunge and `W(1 − δ) ≥ δ/2` give
`(1 − λ_j)^q ≤ c^{−2}`; above, Cvs.Prolate.RungsAboveLevelCount counts `O(log² c)` rungs. So `Σ_j (1 − λ_j)^q = O(log² c)` for every `q > 0`.
-/

noncomputable section

open Real Set Filter Finset Topology
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (lam levT)

namespace Cvs.Prolate.PlungePowerSumPolylog
open Cvs.ZeroCounting

/-- `0 ≤ 1 − λ_j ≤ ½` on the rungs `j < x`. -/
theorem one_sub_lam_mem {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : 0 ≤ 1 - lam x j ∧ 1 - lam x j ≤ 1 / 2 := by
  have hc0 : (0 : ℝ) < 2 * π * x := by linarith
  have h1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc0 (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx j)
  have h2 := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx j.isLt
  unfold lam
  constructor <;> linarith

/-- **The plunge power sum at a cut `1 − δ`**: with `c = 2πx`, `cδ ≥ 5` and `0 < δ ≤ 1`,
`Σ_j (1 − λ_j)^q ≤ x(c⁴e^{−cδ})^q + xδ(1 + ½ log(2/δ)) + (errLow(c, 1) + 1)/2`. -/
theorem sum_rpow_le_of_cut {x : ℕ} (hx : 80 ≤ 2 * π * x) {q : ℝ} (hq : 0 < q) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (h5 : 5 ≤ 2 * π * x * δ) :
    ∑ j : Fin x, (1 - lam x j) ^ q
      ≤ x * ((2 * π * x) ^ 4 * exp (-(2 * π * x * δ))) ^ q + x * δ * (1 + log (2 / δ) / 2)
        + (Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow (2 * π * x) 1 + 1) / 2 := by
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by linarith
  set B := c ^ 4 * exp (-(c * δ)) with hB
  have hB0 : 0 ≤ B := by positivity
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin x))
    (fun j : Fin x => levT x j ≤ 1 - δ) fun j => (1 - lam x j) ^ q
  rw [← hsplit]
  -- below the cut
  have hlow : ∑ j ∈ univ.filter (fun j : Fin x => levT x j ≤ 1 - δ), (1 - lam x j) ^ q ≤ x * B ^ q := by
    have hD : 5 ≤ c * (1 - (1 - δ)) := by rw [sub_sub_cancel]; exact h5
    have hW : δ / 2 ≤ Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (1 - δ) := by
      rw [← Cvs.Prolate.TunnellingIntegralsAgree.tunW_eq]
      have := Cvs.Prolate.RungsAboveLevelCount.half_one_sub_le_tunW (T := 1 - δ) (by linarith) (by linarith)
      rwa [sub_sub_cancel] at this
    have hterm : ∀ j ∈ univ.filter (fun j : Fin x => levT x j ≤ 1 - δ), (1 - lam x j) ^ q ≤ B ^ q := by
      intro j hj
      have h := Cvs.Prolate.TunnellingTraceBelowLevel.one_sub_lam_le_tun hx hD j (Finset.mem_filter.1 hj).2
      have hle : 1 - lam x j ≤ B := by
        refine h.trans ?_
        calc 33 / 40 * exp 5 * c * (c + 2) * exp (-(2 * (c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (1 - δ))))
            ≤ c ^ 4 * exp (-(2 * (c * Cvs.Prolate.TunnellingExponentSharpPlunge.tunW (1 - δ)))) :=
              mul_le_mul_of_nonneg_right (Cvs.Prolate.Gram.PlungeLawBandCellFloor.plunge_const_le hx) (exp_pos _).le
          _ ≤ B := by
              refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
              nlinarith
      exact rpow_le_rpow (one_sub_lam_mem hx j).1 hle hq.le
    calc _ ≤ ∑ _j ∈ univ.filter (fun j : Fin x => levT x j ≤ 1 - δ), B ^ q := Finset.sum_le_sum hterm
      _ = (univ.filter (fun j : Fin x => levT x j ≤ 1 - δ)).card * B ^ q := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ x * B ^ q := by
          refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg hB0 _)
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  -- above the cut
  have hhigh : ∑ j ∈ univ.filter (fun j : Fin x => ¬ levT x j ≤ 1 - δ), (1 - lam x j) ^ q
      ≤ x * δ * (1 + log (2 / δ) / 2) + (Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 + 1) / 2 := by
    have hterm : ∀ j ∈ univ.filter (fun j : Fin x => ¬ levT x j ≤ 1 - δ), (1 - lam x j) ^ q ≤ 1 := fun j _ =>
      rpow_le_one (one_sub_lam_mem hx j).1 (by linarith [(one_sub_lam_mem hx j).2]) hq.le
    have hcard := Cvs.Prolate.RungsAboveLevelCount.card_top_le hx hδ0 hδ1
    have he : (univ.filter fun j : Fin x => ¬ levT x j ≤ 1 - δ) = univ.filter fun j : Fin x => 1 - δ < levT x j :=
      Finset.filter_congr fun j _ => not_le
    calc _ ≤ ∑ _j ∈ univ.filter (fun j : Fin x => ¬ levT x j ≤ 1 - δ), (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (univ.filter (fun j : Fin x => 1 - δ < levT x j)).card := by rw [he]; simp
      _ ≤ _ := hcard
  exact add_le_add hlow hhigh |>.trans_eq (by ring)

/-- `x·(c⁴e^{−A log c})^q = x/c² ≤ 1` at `A = 4 + 2/q`, `c = 2πx ≥ 80`. -/
theorem low_term_le_one {x : ℕ} (hx : 80 ≤ 2 * π * x) {q : ℝ} (hq : 0 < q) :
    (x : ℝ) * ((2 * π * x) ^ 4 * exp (-((4 + 2 / q) * log (2 * π * x)))) ^ q ≤ 1 := by
  set c := 2 * π * (x : ℝ) with hc
  have hc0 : 0 < c := by linarith
  have hB : c ^ 4 * exp (-((4 + 2 / q) * log c)) = exp (-(2 / q * log c)) := by
    conv_lhs => rw [← exp_log hc0]
    rw [← exp_nat_mul, ← exp_add, exp_log hc0]; congr 1; push_cast; ring
  rw [hB, ← exp_mul, show -(2 / q * log c) * q = -(2 * log c) by field_simp, show 2 * log c = log (c ^ 2) by
    rw [log_pow]; push_cast; ring, exp_neg, exp_log (by positivity), ← div_eq_mul_inv,
    div_le_one (by positivity)]
  have hxc : (x : ℝ) ≤ c := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    nlinarith [pi_gt_three]
  nlinarith

/-- `log c ≥ 6 log 2 > 4` at `c ≥ 80`. -/
theorem four_lt_log {c : ℝ} (hc : 80 ≤ c) : 4 < log c := by
  have h64 : log 64 ≤ log c := log_le_log (by norm_num) (by linarith)
  have h2 : log 64 = 6 * log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow]; push_cast; ring
  have := log_two_gt_d9
  linarith

/-- The polylogarithmic bound `1 + A log c/(2π)·(1 + ½ log(2c)) + (errLow(c, 1) + 1)/2`, `A = 4 + 2/q`. -/
def plungePoly (q c : ℝ) : ℝ :=
  1 + (4 + 2 / q) * log c / (2 * π) * (1 + log (2 * c) / 2) + (Cvs.Prolate.LiouvilleGreen.WeylZeroCountLog.errLow c 1 + 1) / 2

/-- **The plunge power sum of the rungs is polylogarithmic**: for `q > 0`, eventually
`Σ_{j ∈ S_F} (1 − λ_{4j})^q ≤ plungePoly q c` at `c = 2πx`. -/
theorem eventually_sum_rpow_le {q : ℝ} (hq : 0 < q) :
    ∀ᶠ x : ℕ in atTop, ∑ j : Cvs.Approximant.SpineSubspace.SF x, (1 - Cvs.Prolate.EvenRungsByIndex.lamR (2 * π * x) (2 * (j : ℕ))) ^ q
      ≤ plungePoly q (2 * π * x) := by
  set A := 4 + 2 / q with hA
  have hA4 : 4 < A := by have : 0 < 2 / q := by positivity
                         linarith
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hlim : Tendsto (fun c : ℝ => log c / c) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hev : ∀ᶠ x : ℕ in atTop, log (2 * π * x) / (2 * π * x) ≤ 1 / A :=
    hc.eventually ((hlim.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / A))))
  filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, hev] with x hx hlog
  set c := 2 * π * (x : ℝ) with hcdef
  have hc0 : 0 < c := by linarith
  have hL4 := four_lt_log hx
  set δ := A * log c / c with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, mul_div_assoc]
    calc A * (log c / c) ≤ A * (1 / A) := mul_le_mul_of_nonneg_left hlog (by linarith)
      _ = 1 := by field_simp
  have hcδ : c * δ = A * log c := by rw [hδ]; field_simp
  have h5 : 5 ≤ c * δ := by rw [hcδ]; nlinarith
  have hmain := sum_rpow_le_of_cut hx hq hδ0 hδ1 h5
  rw [hcδ] at hmain
  have h1 := low_term_le_one hx hq
  -- the top count in closed form
  have hxne : (x : ℝ) ≠ 0 := fun h => by rw [hcdef, h, mul_zero] at hc0; exact lt_irrefl _ hc0
  have hxδ : (x : ℝ) * δ = A * log c / (2 * π) := by rw [hδ, hcdef]; field_simp
  have hlogδ : log (2 / δ) ≤ log (2 * c) := by
    refine log_le_log (by positivity) ?_
    rw [hδ, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have htop : (x : ℝ) * δ * (1 + log (2 / δ) / 2) ≤ A * log c / (2 * π) * (1 + log (2 * c) / 2) := by
    rw [hxδ]; gcongr
  -- from `Fin x` to `S_F`
  have hsub : ∑ j : Cvs.Approximant.SpineSubspace.SF x, (1 - Cvs.Prolate.EvenRungsByIndex.lamR c (2 * (j : ℕ))) ^ q ≤ ∑ j : Fin x, (1 - lam x j) ^ q := by
    rw [Finset.sum_coe_sort (Cvs.Approximant.SpineSubspace.SF x) fun n => (1 - Cvs.Prolate.EvenRungsByIndex.lamR c (2 * n)) ^ q,
      Fin.sum_univ_eq_sum_range (fun n => (1 - lam x n) ^ q)]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun n hn _ => ?_
    exact rpow_nonneg (one_sub_lam_mem hx ⟨n, Finset.mem_range.1 hn⟩).1 _
  unfold plungePoly
  linarith

end Cvs.Prolate.PlungePowerSumPolylog

end
