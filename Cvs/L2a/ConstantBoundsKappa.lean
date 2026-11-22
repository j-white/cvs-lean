import Mathlib
import Cvs.L2a.ConstantBoundsKappaHigh
import Cvs.L2a.CutEstimateFrameFloor
import Cvs.L2a.CutGap
import Cvs.L2a.CutRemainderDensity
import Cvs.L2a.KappaGridRational
import Cvs.L2a.KappaUniformInX
import Cvs.L2a.RampCutSumsUniform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `κ̄₁ ≤ 4.2` and `κ̄ ≤ 12.1`

`g₁₂`, `G₃`, `A₁₂`, `A₁₃` at the fifteen grid points, then `KappaGridRational`'s cells: `𝒟(g₁₂, A₁₂) ≤ 1.21` and
`𝒟(G₃, A₁₃) ≤ 0.87`, so `κ̄₁ = 2𝒟(g₁₂, A₁₂) + 2𝒟(G₃, A₁₃) ≤ 4.2`; with Cvs.L2a.ConstantBoundsKappaHigh, `κ̄ = κ̄₁ + κ̄_{≥2} ≤ 12.1`.
-/

noncomputable section

open Real Set Cvs.L2a.CutEstimateFrameFloor Cvs.L2a.RampCutSumsUniform Cvs.L2a.CutRemainderDensity Cvs.L2a.KappaUniformInX Cvs.L2a.KappaGridRational

namespace Cvs.L2a.ConstantBoundsKappa

theorem g12_A0 : g12 (gridA 0) ≤ (1832481 / 1000000 : ℝ) := by
  rw [gridA_vals.1]
  refine (g12_le_at (w1 := 14320549 / 6250000) (w2 := 3 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_A0 : G3 (gridA 0) ≤ (109789 / 125000 : ℝ) := by
  rw [gridA_vals.1]
  refine (G3_le_at (w3 := 361420807 / 100000000) (w4 := 3 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_A0 : cutA 1 2 (gridA 0) ≤ (483859 / 40000 : ℝ) := by
  rw [gridA_vals.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_A0 : cutA 1 3 (gridA 0) ≤ (295251 / 50000 : ℝ) := by
  rw [gridA_vals.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_A1 : g12 (gridA 1) ≤ (1384661 / 1000000 : ℝ) := by
  rw [gridA_vals.2.1]
  refine (g12_le_at (w1 := 117966163 / 50000000) (w2 := 20025009 / 25000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_A1 : G3 (gridA 1) ≤ (764657 / 1000000 : ℝ) := by
  rw [gridA_vals.2.1]
  refine (G3_le_at (w3 := 371138977 / 100000000) (w4 := 16020007 / 20000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_A1 : cutA 1 2 (gridA 1) ≤ (9230581 / 1000000 : ℝ) := by
  rw [gridA_vals.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_A1 : cutA 1 3 (gridA 1) ≤ (641267 / 125000 : ℝ) := by
  rw [gridA_vals.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_A2 : g12 (gridA 2) ≤ (111169 / 100000 : ℝ) := by
  rw [gridA_vals.2.2.1]
  refine (g12_le_at (w1 := 242706097 / 100000000) (w2 := 85009191 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_A2 : G3 (gridA 2) ≤ (338437 / 500000 : ℝ) := by
  rw [gridA_vals.2.2.1]
  refine (G3_le_at (w3 := 380839943 / 100000000) (w4 := 8500919 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_A2 : cutA 1 2 (gridA 2) ≤ (7491381 / 1000000 : ℝ) := by
  rw [gridA_vals.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_A2 : cutA 1 3 (gridA 2) ≤ (2272463 / 500000 : ℝ) := by
  rw [gridA_vals.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_A3 : g12 (gridA 3) ≤ (185463 / 200000 : ℝ) := by
  rw [gridA_vals.2.2.2.1]
  refine (g12_le_at (w1 := 9978101 / 4000000) (w2 := 11219849 / 12500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_A3 : G3 (gridA 3) ≤ (9481 / 15625 : ℝ) := by
  rw [gridA_vals.2.2.2.1]
  refine (G3_le_at (w3 := 390524987 / 100000000) (w4 := 89758791 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_A3 : cutA 1 2 (gridA 3) ≤ (1580317 / 250000 : ℝ) := by
  rw [gridA_vals.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_A3 : cutA 1 3 (gridA 3) ≤ (163473 / 40000 : ℝ) := by
  rw [gridA_vals.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_A4 : g12 (gridA 4) ≤ (794127 / 1000000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.1]
  refine (g12_le_at (w1 := 256173769 / 100000000) (w2 := 94372931 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_A4 : G3 (gridA 4) ≤ (27469 / 50000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.1]
  refine (G3_le_at (w3 := 6253051 / 1562500) (w4 := 9437293 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_A4 : cutA 1 2 (gridA 4) ≤ (2739419 / 500000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_A4 : cutA 1 3 (gridA 4) ≤ (3718113 / 1000000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_A5 : g12 (gridA 5) ≤ (10832 / 15625 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.1]
  refine (g12_le_at (w1 := 3285897 / 1250000) (w2 := 6179411 / 6250000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_A5 : G3 (gridA 5) ≤ (100283 / 200000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.1]
  refine (G3_le_at (w3 := 409851821 / 100000000) (w4 := 3954823 / 4000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_A5 : cutA 1 2 (gridA 5) ≤ (121063 / 25000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_A5 : cutA 1 3 (gridA 5) ≤ (3414687 / 1000000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_A6 : g12 (gridA 6) ≤ (307053 / 500000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.2.1]
  refine (g12_le_at (w1 := 269548233 / 100000000) (w2 := 25816737 / 25000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_A6 : G3 (gridA 6) ≤ (92137 / 200000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.2.1]
  refine (G3_le_at (w3 := 104873901 / 25000000) (w4 := 103266947 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_A6 : cutA 1 2 (gridA 6) ≤ (2172193 / 500000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_A6 : cutA 1 3 (gridA 6) ≤ (3160423 / 1000000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_A7 : g12 (gridA 7) ≤ (55031 / 100000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.2.2.1]
  refine (g12_le_at (w1 := 276204747 / 100000000) (w2 := 53787233 / 50000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_A7 : G3 (gridA 7) ≤ (425633 / 1000000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.2.2.1]
  refine (G3_le_at (w3 := 17165099 / 4000000) (w4 := 21514893 / 20000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_A7 : cutA 1 2 (gridA 7) ≤ (3943483 / 1000000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_A7 : cutA 1 3 (gridA 7) ≤ (2944117 / 1000000 : ℝ) := by
  rw [gridA_vals.2.2.2.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_B0 : g12 (gridB 0) ≤ (248883 / 500000 : ℝ) := by
  rw [gridB_vals.1]
  refine (g12_le_at (w1 := 35355339 / 12500000) (w2 := 111803399 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_B0 : G3 (gridB 0) ≤ (39513 / 100000 : ℝ) := by
  rw [gridB_vals.1]
  refine (G3_le_at (w3 := 438748219 / 100000000) (w4 := 55901699 / 50000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_B0 : cutA 1 2 (gridB 0) ≤ (3613637 / 1000000 : ℝ) := by
  rw [gridB_vals.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_B0 : cutA 1 3 (gridB 0) ≤ (551549 / 200000 : ℝ) := by
  rw [gridB_vals.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_B1 : g12 (gridB 1) ≤ (272839 / 1000000 : ℝ) := by
  rw [gridB_vals.2.1]
  refine (g12_le_at (w1 := 83852549 / 25000000) (w2 := 143614067 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_B1 : G3 (gridB 1) ≤ (61141 / 250000 : ℝ) := by
  rw [gridB_vals.2.1]
  refine (G3_le_at (w3 := 515388203 / 100000000) (w4 := 71807033 / 50000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_B1 : cutA 1 2 (gridB 1) ≤ (1100009 / 500000 : ℝ) := by
  rw [gridB_vals.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_B1 : cutA 1 3 (gridB 1) ≤ (929959 / 500000 : ℝ) := by
  rw [gridB_vals.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_B2 : g12 (gridB 2) ≤ (9001 / 50000 : ℝ) := by
  rw [gridB_vals.2.2.1]
  refine (g12_le_at (w1 := 193649167 / 50000000) (w2 := 173205081 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_B2 : G3 (gridB 2) ≤ (170731 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.1]
  refine (G3_le_at (w3 := 295803989 / 50000000) (w4 := 4330127 / 2500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_B2 : cutA 1 2 (gridB 2) ≤ (1606667 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_B2 : cutA 1 3 (gridB 2) ≤ (356451 / 250000 : ℝ) := by
  rw [gridB_vals.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_B3 : g12 (gridB 3) ≤ (99323 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.2.1]
  refine (g12_le_at (w1 := 122474487 / 25000000) (w2 := 45825757 / 20000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_B3 : G3 (gridB 3) ≤ (99351 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.2.1]
  refine (G3_le_at (w3 := 743303437 / 100000000) (w4 := 14320549 / 6250000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_B3 : cutA 1 2 (gridB 3) ≤ (213277 / 200000 : ℝ) := by
  rw [gridB_vals.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_B3 : cutA 1 3 (gridB 3) ≤ (992599 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_B4 : g12 (gridB 4) ≤ (64211 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.1]
  refine (g12_le_at (w1 := 295803989 / 50000000) (w2 := 282842713 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_B4 : G3 (gridB 4) ≤ (65837 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.1]
  refine (G3_le_at (w3 := 89442719 / 10000000) (w4 := 35355339 / 12500000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_B4 : cutA 1 2 (gridB 4) ≤ (809867 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_B4 : cutA 1 3 (gridB 4) ≤ (192887 / 250000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_B5 : g12 (gridB 5) ≤ (33809 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.1]
  refine (g12_le_at (w1 := 793725393 / 100000000) (w2 := 77459667 / 20000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_B5 : G3 (gridB 5) ≤ (4431 / 125000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.1]
  refine (G3_le_at (w3 := 597913037 / 50000000) (w4 := 193649167 / 50000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_B5 : cutA 1 2 (gridB 5) ≤ (556449 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_B5 : cutA 1 3 (gridB 5) ≤ (54181 / 100000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.1]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem g12_B6 : g12 (gridB 6) ≤ (3593 / 250000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.2]
  refine (g12_le_at (w1 := 597913037 / 50000000) (w2 := 591607979 / 100000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  norm_num

theorem G3_B6 : G3 (gridB 6) ≤ (15293 / 1000000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.2]
  refine (G3_le_at (w3 := 71888803 / 4000000) (w4 := 295803989 / 50000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans ?_
  unfold aU
  norm_num

theorem A12_B6 : cutA 1 2 (gridB 6) ≤ (174657 / 500000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.2]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem A13_B6 : cutA 1 3 (gridB 6) ≤ (69051 / 200000 : ℝ) := by
  rw [gridB_vals.2.2.2.2.2.2]; unfold cutA Cvs.L2a.CutGap.cutDeltaBound Cvs.L2a.CutGap.cutGamma; norm_num

theorem gridSum_g12_le : gridSum g12 (cutA 1 2) ≤ (121 / 100 : ℝ) := by
  have hA : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 ≤ cutA 1 2 θ := fun θ hθ => cutA_one_nonneg (by norm_num) hθ
  have hF : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 ≤ g12 θ := fun θ hθ => g12_nonneg hθ
  have gA := gridA_vals
  have gB := gridB_vals
  have n0 := nsRamp_gridA_0
  have n1 := nsRamp_gridA_1
  have n2 := nsRamp_gridA_2
  have n3 := nsRamp_gridA_3
  have n4 := nsRamp_gridA_4
  have n5 := nsRamp_gridA_5
  have n6 := nsRamp_gridA_6
  have n7 := nsRamp_gridA_7
  have n8 := nsRamp_gridA_8
  have c0 := ramp_cell (C := 952781 / 40000000) (hF _ (by norm_num [gA.1])) g12_A0
    (hA _ (by norm_num [gA.1])) A12_A0 (le_of_eq n0.symm) n1.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.1]) (by norm_num [mem_Ici, gA.2.1])
      (by norm_num [gA.1, gA.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.1])) (by norm_num)
  have c1 := ramp_cell (C := 11597547 / 200000000) (hF _ (by norm_num [gA.2.1])) g12_A1
    (hA _ (by norm_num [gA.2.1])) A12_A1 n1.1 n2.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.1]) (by norm_num [mem_Ici, gA.2.2.1])
      (by norm_num [gA.2.1, gA.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.1])) (by norm_num)
  have c2 := ramp_cell (C := 8084621 / 100000000) (hF _ (by norm_num [gA.2.2.1])) g12_A2
    (hA _ (by norm_num [gA.2.2.1])) A12_A2 n2.1 n3.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.1])
      (by norm_num [gA.2.2.1, gA.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.1])) (by norm_num)
  have c3 := ramp_cell (C := 92252153 / 1000000000) (hF _ (by norm_num [gA.2.2.2.1])) g12_A3
    (hA _ (by norm_num [gA.2.2.2.1])) A12_A3 n3.1 n4.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.1])
      (by norm_num [gA.2.2.2.1, gA.2.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.1])) (by norm_num)
  have c4 := ramp_cell (C := 46386723 / 500000000) (hF _ (by norm_num [gA.2.2.2.2.1])) g12_A4
    (hA _ (by norm_num [gA.2.2.2.2.1])) A12_A4 n4.1 n5.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.2.1])
      (by norm_num [gA.2.2.2.2.1, gA.2.2.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.2.1])) (by norm_num)
  have c5 := ramp_cell (C := 41919991 / 500000000) (hF _ (by norm_num [gA.2.2.2.2.2.1])) g12_A5
    (hA _ (by norm_num [gA.2.2.2.2.2.1])) A12_A5 n5.1 n6.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.2.2.1])
      (by norm_num [gA.2.2.2.2.2.1, gA.2.2.2.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.2.2.1])) (by norm_num)
  have c6 := ramp_cell (C := 67689171 / 1000000000) (hF _ (by norm_num [gA.2.2.2.2.2.2.1])) g12_A6
    (hA _ (by norm_num [gA.2.2.2.2.2.2.1])) A12_A6 n6.1 n7.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.2.2.2.1])
      (by norm_num [gA.2.2.2.2.2.2.1, gA.2.2.2.2.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.2.2.2.1])) (by norm_num)
  have c7 := ramp_cell (C := 47134737 / 1000000000) (hF _ (by norm_num [gA.2.2.2.2.2.2.2.1])) g12_A7
    (hA _ (by norm_num [gA.2.2.2.2.2.2.2.1])) A12_A7 n7.1 n8.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.2.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.2.2.2.2])
      (by norm_num [gA.2.2.2.2.2.2.2.1, gA.2.2.2.2.2.2.2.2]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.2.2.2.2])) (by norm_num)
  have t0 := tail_cell (b := gridB 0) (b1 := gridB 1) (C := 5933073 / 25000000)
    (hF _ (by norm_num [gB.1])) g12_B0
    (hA _ (by norm_num [gB.1])) A12_B0 (by norm_num [gB.1])
    (by norm_num [gB.1, gB.2.1]) (L3_gridB_0).2 (L3_gridB_1).1
    (L3_anti (by norm_num [gB.1]) (by norm_num [gB.1, gB.2.1]))
    (by norm_num [gB.1, gB.2.1])
  have t1 := tail_cell (b := gridB 1) (b1 := gridB 2) (C := 108714877 / 1000000000)
    (hF _ (by norm_num [gB.2.1])) g12_B1
    (hA _ (by norm_num [gB.2.1])) A12_B1 (by norm_num [gB.2.1])
    (by norm_num [gB.2.1, gB.2.2.1]) (L3_gridB_1).2 (L3_gridB_2).1
    (L3_anti (by norm_num [gB.2.1]) (by norm_num [gB.2.1, gB.2.2.1]))
    (by norm_num [gB.2.1, gB.2.2.1])
  have t2 := tail_cell (b := gridB 2) (b1 := gridB 3) (C := 28833187 / 250000000)
    (hF _ (by norm_num [gB.2.2.1])) g12_B2
    (hA _ (by norm_num [gB.2.2.1])) A12_B2 (by norm_num [gB.2.2.1])
    (by norm_num [gB.2.2.1, gB.2.2.2.1]) (L3_gridB_2).2 (L3_gridB_3).1
    (L3_anti (by norm_num [gB.2.2.1]) (by norm_num [gB.2.2.1, gB.2.2.2.1]))
    (by norm_num [gB.2.2.1, gB.2.2.2.1])
  have t3 := tail_cell (b := gridB 3) (b1 := gridB 4) (C := 55706551 / 1000000000)
    (hF _ (by norm_num [gB.2.2.2.1])) g12_B3
    (hA _ (by norm_num [gB.2.2.2.1])) A12_B3 (by norm_num [gB.2.2.2.1])
    (by norm_num [gB.2.2.2.1, gB.2.2.2.2.1]) (L3_gridB_3).2 (L3_gridB_4).1
    (L3_anti (by norm_num [gB.2.2.2.1]) (by norm_num [gB.2.2.2.1, gB.2.2.2.2.1]))
    (by norm_num [gB.2.2.2.1, gB.2.2.2.2.1])
  have t4 := tail_cell (b := gridB 4) (b1 := gridB 5) (C := 55978663 / 1000000000)
    (hF _ (by norm_num [gB.2.2.2.2.1])) g12_B4
    (hA _ (by norm_num [gB.2.2.2.2.1])) A12_B4 (by norm_num [gB.2.2.2.2.1])
    (by norm_num [gB.2.2.2.2.1, gB.2.2.2.2.2.1]) (L3_gridB_4).2 (L3_gridB_5).1
    (L3_anti (by norm_num [gB.2.2.2.2.1]) (by norm_num [gB.2.2.2.2.1, gB.2.2.2.2.2.1]))
    (by norm_num [gB.2.2.2.2.1, gB.2.2.2.2.2.1])
  have t5 := tail_cell (b := gridB 5) (b1 := gridB 6) (C := 8408149 / 200000000)
    (hF _ (by norm_num [gB.2.2.2.2.2.1])) g12_B5
    (hA _ (by norm_num [gB.2.2.2.2.2.1])) A12_B5 (by norm_num [gB.2.2.2.2.2.1])
    (by norm_num [gB.2.2.2.2.2.1, gB.2.2.2.2.2.2]) (L3_gridB_5).2 (L3_gridB_6).1
    (L3_anti (by norm_num [gB.2.2.2.2.2.1]) (by norm_num [gB.2.2.2.2.2.1, gB.2.2.2.2.2.2]))
    (by norm_num [gB.2.2.2.2.2.1, gB.2.2.2.2.2.2])
  have l6 := L3_gridB_6
  have f6 := g12_B6
  have a6 := A12_B6
  rw [gB.2.2.2.2.2.2] at l6 f6 a6
  have c6' := last_cell (C := 20851121 / 500000000) (hF 6 (by norm_num)) f6 (hA 6 (by norm_num)) a6
    (L3_nonneg (by norm_num)) l6.2 (by norm_num)
  unfold gridSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only at c0 c1 c2 c3 c4 c5 c6 c7 t0 t1 t2 t3 t4 t5 c6' ⊢
  linarith

theorem gridSum_G3_le : gridSum G3 (cutA 1 3) ≤ (87 / 100 : ℝ) := by
  have hA : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 ≤ cutA 1 3 θ := fun θ hθ => cutA_one_nonneg (by norm_num) hθ
  have hF : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 ≤ G3 θ := fun θ hθ => G3_nonneg hθ
  have gA := gridA_vals
  have gB := gridB_vals
  have n0 := nsRamp_gridA_0
  have n1 := nsRamp_gridA_1
  have n2 := nsRamp_gridA_2
  have n3 := nsRamp_gridA_3
  have n4 := nsRamp_gridA_4
  have n5 := nsRamp_gridA_5
  have n6 := nsRamp_gridA_6
  have n7 := nsRamp_gridA_7
  have n8 := nsRamp_gridA_8
  have c0 := ramp_cell (C := 9813757 / 1000000000) (hF _ (by norm_num [gA.1])) G3_A0
    (hA _ (by norm_num [gA.1])) A13_A0 (le_of_eq n0.symm) n1.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.1]) (by norm_num [mem_Ici, gA.2.1])
      (by norm_num [gA.1, gA.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.1])) (by norm_num)
  have c1 := ramp_cell (C := 28120769 / 1000000000) (hF _ (by norm_num [gA.2.1])) G3_A1
    (hA _ (by norm_num [gA.2.1])) A13_A1 n1.1 n2.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.1]) (by norm_num [mem_Ici, gA.2.2.1])
      (by norm_num [gA.2.1, gA.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.1])) (by norm_num)
  have c2 := ramp_cell (C := 10885239 / 250000000) (hF _ (by norm_num [gA.2.2.1])) G3_A2
    (hA _ (by norm_num [gA.2.2.1])) A13_A2 n2.1 n3.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.1])
      (by norm_num [gA.2.2.1, gA.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.1])) (by norm_num)
  have c3 := ramp_cell (C := 53618377 / 1000000000) (hF _ (by norm_num [gA.2.2.2.1])) G3_A3
    (hA _ (by norm_num [gA.2.2.2.1])) A13_A3 n3.1 n4.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.1])
      (by norm_num [gA.2.2.2.1, gA.2.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.1])) (by norm_num)
  have c4 := ramp_cell (C := 5705629 / 100000000) (hF _ (by norm_num [gA.2.2.2.2.1])) G3_A4
    (hA _ (by norm_num [gA.2.2.2.2.1])) A13_A4 n4.1 n5.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.2.1])
      (by norm_num [gA.2.2.2.2.1, gA.2.2.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.2.1])) (by norm_num)
  have c5 := ramp_cell (C := 13427461 / 250000000) (hF _ (by norm_num [gA.2.2.2.2.2.1])) G3_A5
    (hA _ (by norm_num [gA.2.2.2.2.2.1])) A13_A5 n5.1 n6.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.2.2.1])
      (by norm_num [gA.2.2.2.2.2.1, gA.2.2.2.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.2.2.1])) (by norm_num)
  have c6 := ramp_cell (C := 2223783 / 50000000) (hF _ (by norm_num [gA.2.2.2.2.2.2.1])) G3_A6
    (hA _ (by norm_num [gA.2.2.2.2.2.2.1])) A13_A6 n6.1 n7.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.2.2.2.1])
      (by norm_num [gA.2.2.2.2.2.2.1, gA.2.2.2.2.2.2.2.1]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.2.2.2.1])) (by norm_num)
  have c7 := ramp_cell (C := 3883289 / 125000000) (hF _ (by norm_num [gA.2.2.2.2.2.2.2.1])) G3_A7
    (hA _ (by norm_num [gA.2.2.2.2.2.2.2.1])) A13_A7 n7.1 n8.2
    (nsRamp_monotoneOn (by norm_num [mem_Ici, gA.2.2.2.2.2.2.2.1]) (by norm_num [mem_Ici, gA.2.2.2.2.2.2.2.2])
      (by norm_num [gA.2.2.2.2.2.2.2.1, gA.2.2.2.2.2.2.2.2]))
    (nsRamp_nonneg (by norm_num [gA.2.2.2.2.2.2.2.2])) (by norm_num)
  have t0 := tail_cell (b := gridB 0) (b1 := gridB 1) (C := 15618317 / 100000000)
    (hF _ (by norm_num [gB.1])) G3_B0
    (hA _ (by norm_num [gB.1])) A13_B0 (by norm_num [gB.1])
    (by norm_num [gB.1, gB.2.1]) (L3_gridB_0).2 (L3_gridB_1).1
    (L3_anti (by norm_num [gB.1]) (by norm_num [gB.1, gB.2.1]))
    (by norm_num [gB.1, gB.2.1])
  have t1 := tail_cell (b := gridB 1) (b1 := gridB 2) (C := 86814467 / 1000000000)
    (hF _ (by norm_num [gB.2.1])) G3_B1
    (hA _ (by norm_num [gB.2.1])) A13_B1 (by norm_num [gB.2.1])
    (by norm_num [gB.2.1, gB.2.2.1]) (L3_gridB_1).2 (L3_gridB_2).1
    (L3_anti (by norm_num [gB.2.1]) (by norm_num [gB.2.1, gB.2.2.1]))
    (by norm_num [gB.2.1, gB.2.2.1])
  have t2 := tail_cell (b := gridB 2) (b1 := gridB 3) (C := 50263971 / 500000000)
    (hF _ (by norm_num [gB.2.2.1])) G3_B2
    (hA _ (by norm_num [gB.2.2.1])) A13_B2 (by norm_num [gB.2.2.1])
    (by norm_num [gB.2.2.1, gB.2.2.2.1]) (L3_gridB_2).2 (L3_gridB_3).1
    (L3_anti (by norm_num [gB.2.2.1]) (by norm_num [gB.2.2.1, gB.2.2.2.1]))
    (by norm_num [gB.2.2.1, gB.2.2.2.1])
  have t3 := tail_cell (b := gridB 3) (b1 := gridB 4) (C := 26458467 / 500000000)
    (hF _ (by norm_num [gB.2.2.2.1])) G3_B3
    (hA _ (by norm_num [gB.2.2.2.1])) A13_B3 (by norm_num [gB.2.2.2.1])
    (by norm_num [gB.2.2.2.1, gB.2.2.2.2.1]) (L3_gridB_3).2 (L3_gridB_4).1
    (L3_anti (by norm_num [gB.2.2.2.1]) (by norm_num [gB.2.2.2.1, gB.2.2.2.2.1]))
    (by norm_num [gB.2.2.2.1, gB.2.2.2.2.1])
  have t4 := tail_cell (b := gridB 4) (b1 := gridB 5) (C := 6920239 / 125000000)
    (hF _ (by norm_num [gB.2.2.2.2.1])) G3_B4
    (hA _ (by norm_num [gB.2.2.2.2.1])) A13_B4 (by norm_num [gB.2.2.2.2.1])
    (by norm_num [gB.2.2.2.2.1, gB.2.2.2.2.2.1]) (L3_gridB_4).2 (L3_gridB_5).1
    (L3_anti (by norm_num [gB.2.2.2.2.1]) (by norm_num [gB.2.2.2.2.1, gB.2.2.2.2.2.1]))
    (by norm_num [gB.2.2.2.2.1, gB.2.2.2.2.2.1])
  have t5 := tail_cell (b := gridB 5) (b1 := gridB 6) (C := 4317823 / 100000000)
    (hF _ (by norm_num [gB.2.2.2.2.2.1])) G3_B5
    (hA _ (by norm_num [gB.2.2.2.2.2.1])) A13_B5 (by norm_num [gB.2.2.2.2.2.1])
    (by norm_num [gB.2.2.2.2.2.1, gB.2.2.2.2.2.2]) (L3_gridB_5).2 (L3_gridB_6).1
    (L3_anti (by norm_num [gB.2.2.2.2.2.1]) (by norm_num [gB.2.2.2.2.2.1, gB.2.2.2.2.2.2]))
    (by norm_num [gB.2.2.2.2.2.1, gB.2.2.2.2.2.2])
  have l6 := L3_gridB_6
  have f6 := G3_B6
  have a6 := A13_B6
  rw [gB.2.2.2.2.2.2] at l6 f6 a6
  have c6' := last_cell (C := 21973933 / 500000000) (hF 6 (by norm_num)) f6 (hA 6 (by norm_num)) a6
    (L3_nonneg (by norm_num)) l6.2 (by norm_num)
  unfold gridSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num only at c0 c1 c2 c3 c4 c5 c6 c7 t0 t1 t2 t3 t4 t5 c6' ⊢
  linarith

/-- **`κ̄₁ ≤ 4.2`**. -/
theorem kappaBar1_le : kappaBar1 ≤ 21 / 5 := by
  unfold kappaBar1
  linarith [gridSum_g12_le, gridSum_G3_le]

/-- **`κ̄ ≤ 12.1`**. -/
theorem kappaBar_le : kappaBar ≤ 121 / 10 := by
  unfold kappaBar
  linarith [kappaBar1_le, Cvs.L2a.ConstantBoundsKappaHigh.kappaBar2_le]

end Cvs.L2a.ConstantBoundsKappa
