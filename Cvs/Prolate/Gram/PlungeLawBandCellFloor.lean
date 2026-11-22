import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Prolate.TunnellingExponentSharpPlunge
import Cvs.Prolate.TunnellingIntegralMargin
import Cvs.Prolate.TunnellingIntegralsAgree
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.WindowChainCellFloors
import Cvs.Upstream.CellFloorSandwichPosDef

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plunge law, the CP-b floor and the band cell floor from the project's floors

With `TunnellingIntegralsAgree`'s bridges: `TunnellingExponentSharpPlunge`'s sharp plunge `1 − λ ≤ (33/40)e⁵·c·(cW + 2)e^{−2cW}`, `0 ≤ W ≤ 1` and
`(33/40)e⁵c(c + 2) ≤ c⁴` give `TunnellingFloorSumPlunge`'s `PlungeLaw` with `K = 4`; `TunnellingFloorSumPlunge`'s `CPbFloor` is `DeepRemainderCellFloors`'s `DeepCellFloor` on
the spine rungs; and `DeepRemainderCellFloors`'s `BandCellFloor` follows from `TunnellingFloorSumPlunge`'s `BandFloor` (`x^{−ε} ≥ e^{−εc}`) on `T_j > ¾`,
from `DeepCellFloor` at `T_j = ¾` (`Δ(¾) = 0`), with the ground rung excluded by `χ₀ ≤ c²/3`.
-/

noncomputable section

open Real Filter

namespace Cvs.Prolate.Gram.PlungeLawBandCellFloor
open Cvs.ZeroCounting

/-- `(33/40)e⁵·c·(c + 2) ≤ c⁴` for `c ≥ 80`. -/
theorem plunge_const_le {c : ℝ} (hc : 80 ≤ c) : 33 / 40 * exp 5 * c * (c + 2) ≤ c ^ 4 := by
  have he : exp 5 ≤ 243 := by
    have h1 := Real.exp_one_lt_d9
    have h5 : exp 5 = exp 1 ^ 5 := by rw [← exp_nat_mul]; norm_num
    rw [h5]
    calc exp 1 ^ 5 ≤ 3 ^ 5 := pow_le_pow_left₀ (exp_pos 1).le (by linarith) 5
      _ = 243 := by norm_num
  have hc0 : 0 < c := by linarith
  have h2 : 80 * c ≤ c ^ 2 := by nlinarith
  have h4 : 6400 * c ^ 2 ≤ c ^ 4 := by nlinarith
  calc 33 / 40 * exp 5 * c * (c + 2) ≤ 33 / 40 * 243 * c * (c + 2) := by gcongr
    _ ≤ c ^ 4 := by nlinarith

/-- **The plunge law** `Cvs.Prolate.Gram.TunnellingFloorSumPlunge.PlungeLaw`, with `K = 4`. -/
theorem plungeLaw : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.PlungeLaw := by
  refine ⟨4, ?_⟩
  filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hx j h5
  have hlev : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * (j : ℕ)) χ := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j)
  have hP := Cvs.Prolate.TunnellingExponentSharpPlunge.one_sub_lamR_le_tunW hx hlev h5
  rw [← Cvs.Prolate.TunnellingIntegralsAgree.tunW_eq] at hP
  have hχ0 : 0 ≤ Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * (j : ℕ)) :=
    Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec _ (Cvs.Prolate.EvenRungsByIndex.lev_spec hlev).1
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  change 1 - Cvs.Prolate.EvenRungsByIndex.lamR (2 * π * x) (2 * (j : ℕ)) ≤ (2 * π * x) ^ (4 : ℝ) *
    exp (-(2 * (2 * π * x) * Cvs.Prolate.TunnellingIntegralMargin.tunW (Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * (j : ℕ)) / (2 * π * x) ^ 2)))
  set c := 2 * π * (x : ℝ)
  set W := Cvs.Prolate.TunnellingIntegralMargin.tunW (Cvs.Prolate.EvenRungsByIndex.lev c (2 * (j : ℕ)) / c ^ 2)
  have hW0 : 0 ≤ W := Cvs.Prolate.TunnellingIntegralMargin.tunW_nonneg _
  have hW1 : W ≤ 1 := Cvs.Prolate.TunnellingIntegralsAgree.tunW_le_one (div_nonneg hχ0 (sq_nonneg _))
  have hE : 0 ≤ exp (-(2 * c * W)) := (exp_pos _).le
  rw [show -(2 * (c * W)) = -(2 * c * W) by ring] at hP
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]
  calc 1 - Cvs.Prolate.EvenRungsByIndex.lamR c (2 * (j : ℕ)) ≤ 33 / 40 * exp 5 * c * (c * W + 2) * exp (-(2 * c * W)) := hP
    _ ≤ 33 / 40 * exp 5 * c * (c + 2) * exp (-(2 * c * W)) := by
        gcongr; nlinarith
    _ ≤ c ^ 4 * exp (-(2 * c * W)) := mul_le_mul_of_nonneg_right (plunge_const_le hx) hE

/-- **The CP-b floor** `Cvs.Prolate.Gram.TunnellingFloorSumPlunge.CPbFloor` from the deep cell floor. -/
theorem cPbFloor_of_deep (hD : Cvs.Prolate.Gram.DeepRemainderCellFloors.DeepCellFloor) : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.CPbFloor := by
  intro ε hε
  filter_upwards [hD ε hε] with x hx j hj
  rw [Cvs.Prolate.TunnellingIntegralsAgree.tunD_eq]
  exact hx (Cvs.Route.Visibility.WindowChainCellFloors.finOfSF j) hj

/-- `x^{−ε} ≥ e^{−εc}` at `c = 2πx`, `x > 0`, `ε ≥ 0`. -/
theorem exp_neg_le_rpow_neg {x ε : ℝ} (hx : 0 < x) (hε : 0 ≤ ε) : exp (-(ε * (2 * π * x))) ≤ x ^ (-ε) := by
  rw [rpow_def_of_pos hx, exp_le_exp]
  have h1 := log_le_sub_one_of_pos hx
  have h2 : log x ≤ 2 * π * x := by nlinarith [pi_gt_three]
  nlinarith

/-- **The band cell floor** `Cvs.Prolate.Gram.DeepRemainderCellFloors.BandCellFloor` from the band floor and the deep cell floor. -/
theorem bandCellFloor_of_bandFloor (hB : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor) (hD : Cvs.Prolate.Gram.DeepRemainderCellFloors.DeepCellFloor) : Cvs.Prolate.Gram.DeepRemainderCellFloors.BandCellFloor := by
  intro ε hε
  filter_upwards [hB ε hε, hD ε hε, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hBx hDx hx j hj
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  rcases hj.lt_or_eq with hlt | heq
  · have hj1 : 1 ≤ (j : ℕ) := by
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
      · exfalso
        have h13 : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ 1 / 3 := by
          unfold Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT
          rw [h0, mul_zero, Cvs.Prolate.EvenRungsByIndex.lev_zero, div_le_iff₀ (by positivity)]
          linarith [Cvs.Prolate.EvenSpectrumGroundLevel.groundLevel_le (2 * π * x)]
        linarith
      · exact h0
    set jj : Cvs.Approximant.SpineSubspace.SF x := ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 j.2, hj1⟩⟩
    have hfin : Cvs.Route.Visibility.WindowChainCellFloors.finOfSF jj = j := Fin.ext rfl
    have h := hBx jj (by rw [Cvs.Prolate.TunnellingIntegralsAgree.tLev_eq, hfin]; exact hlt)
    rw [hfin] at h
    have hx0 : (0 : ℝ) < x := by nlinarith [pi_gt_three]
    exact (exp_neg_le_rpow_neg hx0 (le_of_lt hε)).trans h
  · have h := hDx j heq.ge
    rw [← heq, Cvs.Prolate.TunnellingIntegralsAgree.tunDelta_three_quarters] at h
    simpa using h

end Cvs.Prolate.Gram.PlungeLawBandCellFloor

end
