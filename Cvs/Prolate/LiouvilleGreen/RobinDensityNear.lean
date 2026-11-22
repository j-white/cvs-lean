import Mathlib
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement
import Cvs.Prolate.LiouvilleGreen.RobinDensityBand
import Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# LemQ's (H2) on `τ ≥ 5/8`, so on lemQ's `I_near = [¾ − δ₁, Θ_x]` for every `δ₁ ∈ (0, 1/8]`

The band (Cvs.Prolate.LiouvilleGreen.RobinDensityBand) and `τ ≥ 5/4` (Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel) overlap on `[5/4, 3/2]`, and a cell starting in the band below `5/4` is
shorter than `c²/4`, since the band rate is at least `k/c`; so every cell with `σ ≥ 5c²/8` lies in one of the two.
-/

noncomputable section

open Real Set Filter Topology
open Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement (nodeRate ConsecNodes)
open Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel (H2 H2Upper H2Lower)
open Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper (bandL bandM)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass energyHalf)

namespace Cvs.Prolate.LiouvilleGreen.RobinDensityNear
open Cvs.ZeroCounting

/-- **The band rate floor**: there is `k > 0` with `nodeRate ≥ k/c` for `c ≥ 2¹⁴`, `5c²/8 ≤ σ ≤ 3c²/2`. -/
theorem rate_floor_band : ∃ k : ℝ, 0 < k ∧ ∀ c σ : ℝ, 16384 ≤ c → 5 * c ^ 2 / 8 ≤ σ → σ ≤ 3 * c ^ 2 / 2 →
    k / c ≤ nodeRate c σ := by
  obtain ⟨k₁, k₂, hk₁, -, hb⟩ := Cvs.Prolate.LiouvilleGreen.RobinDensityBand.band_bounds
  refine ⟨k₁ / 2, by positivity, fun c σ hc h1 h2 => ?_⟩
  have hc0 : 0 < c := by linarith
  have hm := (hb c σ hc h1 h2).1
  have hr := (Cvs.Prolate.LiouvilleGreen.RobinDensityBand.rate_band hc0 h1 h2).1
  have hL : 0 ≤ bandL c σ := by
    apply Cvs.Prolate.LiouvilleGreen.NodeMassBandUpper.bandL_nonneg hc0
    have : |σ - c ^ 2| ≤ c ^ 2 / 2 := by rw [abs_le]; constructor <;> nlinarith
    have : |σ - c ^ 2| / (2 * c) ≤ c / 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hM : 1 / c ≤ bandM c σ := by
    unfold bandM; exact div_le_div_of_nonneg_right (by linarith) hc0.le
  have := mul_le_mul_of_nonneg_left hM hk₁.le
  calc k₁ / 2 / c = k₁ * (1 / c) / 2 := by ring
    _ ≤ k₁ * bandM c σ / 2 := by linarith
    _ ≤ nodeMass c σ / energyHalf c σ / 2 := by linarith
    _ ≤ nodeRate c σ := hr

/-- **lemQ (H2) on `τ ≥ 5/8`**: one constant and one threshold serve the soft edge, the Coulomb layer and the
whole tail. -/
theorem h2_near : H2 (Ici (5 / 8)) := by
  obtain ⟨C₁, c₁, hCp₁, hu₁, hl₁⟩ := Cvs.Prolate.LiouvilleGreen.RobinDensityBand.h2_band
  obtain ⟨C₂, c₂, hCp₂, hu₂, hl₂⟩ := Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel.h2_above (A := 1 / 4) (by norm_num)
  obtain ⟨k, hk, hrate⟩ := rate_floor_band
  set C := max C₁ C₂
  set c₀ := max (max c₁ c₂) (max 16384 (8 * π / k))
  have hC₁ : C₁ ≤ C := le_max_left _ _
  have hC₂ : C₂ ≤ C := le_max_right _ _
  -- a cell with `σ ≥ 5c²/8` lies in the band or above `5c²/4`
  have hsplit : ∀ c χ σ σ', c₀ ≤ c → ConsecNodes c χ σ σ' → 5 / 8 ≤ σ / c ^ 2 →
      (σ / c ^ 2 ∈ Icc (5 / 8 : ℝ) (3 / 2) ∧ σ' / c ^ 2 ∈ Icc (5 / 8 : ℝ) (3 / 2)) ∨
        (σ / c ^ 2 ∈ Ici (1 + 1 / 4 : ℝ) ∧ σ' / c ^ 2 ∈ Ici (1 + 1 / 4 : ℝ)) := by
    intro c χ σ σ' hc hcell hσ
    have hc16 : 16384 ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
    have hck : 8 * π / k ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
    have hc0 : 0 < c := by linarith
    have hc2 : 0 < c ^ 2 := by positivity
    have hlt := hcell.1
    have hτ' : σ / c ^ 2 ≤ σ' / c ^ 2 := div_le_div_of_nonneg_right hlt.le hc2.le
    rcases le_or_gt (σ' / c ^ 2) (3 / 2) with h | h
    · exact Or.inl ⟨⟨hσ, hτ'.trans h⟩, ⟨hσ.trans hτ', h⟩⟩
    rcases le_or_gt (1 + 1 / 4) (σ / c ^ 2) with h' | h'
    · exact Or.inr ⟨h', h'.trans hτ'⟩
    exfalso
    have hσl : 5 * c ^ 2 / 8 ≤ σ := by have := (le_div_iff₀ hc2).mp hσ; linarith
    have hσu : σ < 5 * c ^ 2 / 4 := by have := (div_lt_iff₀ hc2).mp h'; linarith
    have hσ'u : 3 * c ^ 2 / 2 < σ' := by have := (lt_div_iff₀ hc2).mp h; linarith
    have hπk : π / (k / c) ≤ c ^ 2 / 4 := by
      rw [div_div_eq_mul_div, div_le_div_iff₀ hk (by norm_num)]
      have := (div_le_iff₀ hk).mp hck
      nlinarith
    have hlen := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.cell_length_le hc0 hcell (by positivity : 0 < k / c) fun s hs hsm => by
      have h1 : 5 * c ^ 2 / 8 ≤ s := hσl.trans hs.1.le
      have h2 : s ≤ 3 * c ^ 2 / 2 := by linarith
      exact hrate c s hc16 h1 h2
    linarith
  refine ⟨C, c₀, lt_of_lt_of_le hCp₁ hC₁, ?_, ?_⟩
  · intro c χ σ σ' hc hcell hσ hσ'
    have hc1 : c₁ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
    have hc2' : c₂ ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
    have hτ0 : 0 ≤ σ / c ^ 2 := le_trans (by norm_num) (show (5 / 8 : ℝ) ≤ σ / c ^ 2 from hσ)
    have hτ0' : 0 ≤ σ' / c ^ 2 := le_trans (by norm_num) (show (5 / 8 : ℝ) ≤ σ' / c ^ 2 from hσ')
    rcases hsplit c χ σ σ' hc hcell hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨a, b⟩ := hu₁ c χ σ σ' hc1 hcell h1 h2
      exact ⟨a.trans (by gcongr), b.trans (by gcongr)⟩
    · obtain ⟨a, b⟩ := hu₂ c χ σ σ' hc2' hcell h1 h2
      exact ⟨a.trans (by gcongr), b.trans (by gcongr)⟩
  · intro c χ σ σ' hc hcell hσ hσ'
    have hc1 : c₁ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
    have hc2' : c₂ ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
    have hτ0 : 0 ≤ σ / c ^ 2 := le_trans (by norm_num) (show (5 / 8 : ℝ) ≤ σ / c ^ 2 from hσ)
    have hτ0' : 0 ≤ σ' / c ^ 2 := le_trans (by norm_num) (show (5 / 8 : ℝ) ≤ σ' / c ^ 2 from hσ')
    rcases hsplit c χ σ σ' hc hcell hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨a, b⟩ := hl₁ c χ σ σ' hc1 hcell h1 h2
      refine ⟨le_trans ?_ a, le_trans ?_ b⟩ <;>
        exact one_div_le_one_div_of_le (by positivity) (by gcongr)
    · obtain ⟨a, b⟩ := hl₂ c χ σ σ' hc2' hcell h1 h2
      refine ⟨le_trans ?_ a, le_trans ?_ b⟩ <;>
        exact one_div_le_one_div_of_le (by positivity) (by gcongr)

end Cvs.Prolate.LiouvilleGreen.RobinDensityNear

end
