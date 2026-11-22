import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement
import Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel
import Cvs.Route.Visibility.WindowChainCellFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Theorem Q₀ on node positions only: (H2) removes the Robin rates

On `τ ≥ 5/8` (H2) (Cvs.Prolate.LiouvilleGreen.RobinDensityNear) bounds `θ'(σ)/θ'(χ)` by `C²(1 + τ_σ)(1 + τ_χ)s_χ/s_σ`, `s` the cell length to the next
node; below `5/8` lemQ's far-region bound `θ' ≤ c^K` (eq-cpb Lemma 7 at `b = ½`) and the (H2) floor at `χ` bound it by
`(C/π)c^K(1 + τ_χ)s_χ`. So Theorem Q₀ follows from a statement about node positions, rung levels and the zeros of `T`.
-/

noncomputable section

open Real Set Filter Topology Finset
open Cvs.Route.Visibility.WindowChainCellFloors (finOfSF)
open Cvs.Prolate.Gram.RobinNodeLatticeDualFloor (robinW chi)
open Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement (nodeRate ConsecNodes)
open Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel (H2 H2Upper H2Lower)

namespace Cvs.Prolate.Gram.RobinQZeroNodePositions
open Cvs.ZeroCounting

/-- **lemQ's (H2) on the far region** (lemQ §2, from eq-cpb Lemma 7 at `b = ½`): `θ'(σ) ≤ c^K` for
`c²/4 ≤ σ < 5c²/8`. -/
def FarRate : Prop :=
  ∃ K c₀ : ℝ, 0 < c₀ ∧ ∀ c, c₀ ≤ c → ∀ σ, c ^ 2 / 4 ≤ σ → σ < 5 * c ^ 2 / 8 → nodeRate c σ ≤ c ^ K

/-- The position weight of a node: `(1 + τ_σ)(1 + τ_χ)s_χ/s_σ` on `τ_σ ≥ 5/8`, `c^K(1 + τ_χ)s_χ` below. -/
def posWeight (c K χ σ nχ nσ : ℝ) : ℝ :=
  if 5 * c ^ 2 / 8 ≤ σ then (1 + σ / c ^ 2) * (1 + χ / c ^ 2) * (nχ - χ) / (nσ - σ)
  else c ^ K * (1 + χ / c ^ 2) * (nχ - χ)

/-- The band rung lies above `5c²/8`. -/
theorem five_eighths_le_chi {x : ℕ} (hx : 0 < x) (j : Cvs.Approximant.SpineSubspace.SF x) (hj : 3 / 4 < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j) :
    5 * (2 * π * x) ^ 2 / 8 ≤ chi x (finOfSF j) := by
  have hc : 0 < (2 * π * x : ℝ) ^ 2 := by
    have : (0 : ℝ) < x := by exact_mod_cast hx
    positivity
  unfold Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev at hj
  rw [lt_div_iff₀ hc] at hj
  have : chi x (finOfSF j) = Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * (j : ℕ)) := rfl
  rw [this]; linarith

/-- **The rate ratio on positions**: under (H2) on `[5/8, ∞)` with constant `C` and `FarRate` with exponent `K`,
`θ'(σ)/θ'(χ) ≤ max(C², C/π)·posWeight` for every node `σ ≥ c²/4` with a next node when `σ ≥ 5c²/8`. -/
theorem rate_div_le {C c₀ K c₁ : ℝ} (hC : 0 < C) (hu : H2Upper C c₀ (Ici (5 / 8)))
    (hl : H2Lower C c₀ (Ici (5 / 8)))
    (hF : ∀ c, c₁ ≤ c → ∀ σ, c ^ 2 / 4 ≤ σ → σ < 5 * c ^ 2 / 8 → nodeRate c σ ≤ c ^ K)
    {c χ σ nχ nσ : ℝ} (hc : 0 < c) (hc₀ : c₀ ≤ c) (hc₁ : c₁ ≤ c) (hχ : 5 * c ^ 2 / 8 ≤ χ)
    (hχn : ConsecNodes c χ χ nχ) (hσ : c ^ 2 / 4 ≤ σ) (hσn : 5 * c ^ 2 / 8 ≤ σ → ConsecNodes c χ σ nσ) :
    nodeRate c σ / nodeRate c χ ≤ max (C ^ 2) (C / π) * posWeight c K χ σ nχ nσ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hτ : ∀ s, 5 * c ^ 2 / 8 ≤ s → s / c ^ 2 ∈ Ici (5 / 8 : ℝ) := fun s hs => by
    rw [Set.mem_Ici, le_div_iff₀ hc2]; linarith
  have hχ' : χ / c ^ 2 ∈ Ici (5 / 8 : ℝ) := hτ χ hχ
  have hnχ' : nχ / c ^ 2 ∈ Ici (5 / 8 : ℝ) := hτ nχ (by linarith [hχn.1])
  have hlo := (hl c χ χ nχ hc₀ hχn hχ' hnχ').1
  have hrχ := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.nodeRate_pos hc χ
  have hrσ := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.nodeRate_pos hc σ
  have hdχ : 0 < nχ - χ := sub_pos.mpr hχn.1
  have h1χ : 0 < 1 + χ / c ^ 2 := by have := div_nonneg (by linarith : 0 ≤ χ) hc2.le; linarith
  have hπ := Real.pi_pos
  -- `θ'(χ) ≥ π/(C(1 + τ_χ)s_χ)`
  have hχlow : π / (C * (1 + χ / c ^ 2) * (nχ - χ)) ≤ nodeRate c χ := by
    rw [div_le_iff₀ (by positivity)]
    have h' := mul_le_mul_of_nonneg_right hlo (by positivity : 0 ≤ π * (C * (1 + χ / c ^ 2)))
    have hne : C * (1 + χ / c ^ 2) ≠ 0 := mul_ne_zero hC.ne' h1χ.ne'
    have e1 : 1 / (C * (1 + χ / c ^ 2)) * (π * (C * (1 + χ / c ^ 2))) = π := by
      rw [mul_comm π, ← mul_assoc, one_div_mul_cancel hne, one_mul]
    have e2 : nodeRate c χ / π * (nχ - χ) * (π * (C * (1 + χ / c ^ 2))) =
        nodeRate c χ * (C * (1 + χ / c ^ 2) * (nχ - χ)) := by field_simp; try ring
    linarith
  have hden : 0 < π / (C * (1 + χ / c ^ 2) * (nχ - χ)) := by positivity
  unfold posWeight
  split_ifs with hs
  · have hcell := hσn hs
    have hdσ : 0 < nσ - σ := sub_pos.mpr hcell.1
    have hup := (hu c χ σ nσ hc₀ hcell (hτ σ hs) (hτ nσ (by linarith [hcell.1]))).1
    have hσup : nodeRate c σ ≤ π * C * (1 + σ / c ^ 2) / (nσ - σ) := by
      rw [le_div_iff₀ hdσ]
      rw [div_mul_eq_mul_div, div_le_iff₀ hπ] at hup
      linarith
    have hτσ : 0 ≤ σ / c ^ 2 := div_nonneg (by linarith) hc2.le
    have hnum : 0 ≤ π * C * (1 + σ / c ^ 2) / (nσ - σ) :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) hdσ.le
    calc nodeRate c σ / nodeRate c χ ≤ (π * C * (1 + σ / c ^ 2) / (nσ - σ)) /
          (π / (C * (1 + χ / c ^ 2) * (nχ - χ))) := div_le_div₀ hnum hσup hden hχlow
      _ = C ^ 2 * ((1 + σ / c ^ 2) * (1 + χ / c ^ 2) * (nχ - χ) / (nσ - σ)) := by field_simp
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
        have := div_nonneg (by linarith : 0 ≤ σ) hc2.le
        exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) h1χ.le) hdχ.le) hdσ.le
  · push Not at hs
    have hσup := hF c hc₁ σ hσ hs
    have hK : 0 < c ^ K := Real.rpow_pos_of_pos hc K
    calc nodeRate c σ / nodeRate c χ ≤ c ^ K / (π / (C * (1 + χ / c ^ 2) * (nχ - χ))) :=
          div_le_div₀ hK.le hσup hden hχlow
      _ = C / π * (c ^ K * (1 + χ / c ^ 2) * (nχ - χ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end Cvs.Prolate.Gram.RobinQZeroNodePositions

end
