import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinDualCertificate
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
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
# The band floor H-U ∧ H-top from Theorem Q₀ on the Robin lattice and the cell mass floor

The Robin weight is `ρ_σ = (θ'(σ)/θ'(χ_j))·(r_σ/r_{χ_j})²`, `θ` the Prüfer angle of `(c y(½), y'(½))` (lemQ §1.2–1.3).
Theorem Q₀ (lemQ §7.4) is stated on these weights: for every `ε > 0`, eventually every band rung `T_j > ¾` has a
finite Robin node set and a polynomial with `Σ_S ρ_σ ≤ x^ε`. With the cell mass floor `C_jj ≥ x^{−ε}` (CP-a-H) and
Cvs.Prolate.Gram.RobinNodeLatticeDualFloor this is `TunnellingFloorSumPlunge`'s `BandFloor`.
-/

noncomputable section

open Real Set Filter Topology Polynomial Finset
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram)
open Cvs.Route.Visibility.WindowChainCellFloors (finOfSF)
open Cvs.Prolate.Gram.RobinDualCertificate (resid robinWeight)
open Cvs.Prolate.Gram.RobinNodeLatticeDualFloor (robinW robinR robinG chi)

namespace Cvs.Prolate.Gram.BandFloorFromRobinQZero
open Cvs.ZeroCounting

/-! ### The reference weight -/

theorem resid_ne_zero (S : Finset ℝ) {Q : ℝ[X]} {σ : ℝ} (hQ : Q.eval σ ≠ 0) : resid S id Q σ ≠ 0 := by
  unfold resid
  refine mul_ne_zero hQ ?_
  unfold Lagrange.nodalWeight
  refine Finset.prod_ne_zero_iff.mpr fun l hl => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  exact (Finset.mem_erase.mp hl).1 h.symm

/-- The reference node has weight `ρ_{χ_j} = 1`. -/
theorem robinWeight_self (S : Finset ℝ) {g : ℝ → ℝ} {Q : ℝ[X]} {χ : ℝ} (hQ : Q.eval χ ≠ 0)
    (hg : g χ ≠ 0) : robinWeight S id g Q χ χ = 1 := by
  unfold robinWeight
  rw [div_self (mul_ne_zero (resid_ne_zero S hQ) hg), one_pow]

/-- `Σ_S ρ_σ ≥ 1`. -/
theorem one_le_sum_robinWeight {S : Finset ℝ} {g : ℝ → ℝ} {Q : ℝ[X]} {χ : ℝ} (hχ : χ ∈ S) (hQ : Q.eval χ ≠ 0)
    (hg : g χ ≠ 0) : 1 ≤ ∑ σ ∈ S, robinWeight S id g Q χ σ := by
  rw [← robinWeight_self S hQ hg]
  exact Finset.single_le_sum (f := fun σ => robinWeight S id g Q χ σ) (fun σ _ => sq_nonneg _) hχ

/-! ### The weights as Christoffel ratios of the node phase -/

/-! ### Theorem Q₀ and the cell mass floor -/

/-- **Theorem Q₀ on the Robin lattice** (lemQ §7.4): for every `ε > 0`, eventually every band rung `T_j > ¾` has a
finite set `S` of Robin nodes through `χ_j` containing `χ_j` and no other level, and `Q` of degree `< |S|` vanishing
at the other levels with `Q(χ_j) ≠ 0`, whose Robin weights satisfy `Σ_S ρ_σ ≤ x^ε`. -/
def RobinQ0 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 3 / 4 < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    ∃ (S : Finset ℝ) (Q : ℝ[X]), (∀ σ ∈ S, robinW (2 * π * x) (chi x (finOfSF j)) σ = 0) ∧
      chi x (finOfSF j) ∈ S ∧ (∀ b, b ≠ finOfSF j → chi x b ∉ S) ∧ Q.degree < S.card ∧
      (∀ b, b ≠ finOfSF j → Q.eval (chi x b) = 0) ∧ Q.eval (chi x (finOfSF j)) ≠ 0 ∧
      ∑ σ ∈ S, robinWeight S id (robinG (2 * π * x) (chi x (finOfSF j))) Q (chi x (finOfSF j)) σ ≤ (x : ℝ) ^ ε

/-- The band cell mass floor CP-a-H in subpolynomial form: `C_jj ≥ x^{−ε}` on `T_j > ¾`, for every `ε > 0`. -/
def BandCellMass : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 3 / 4 < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    (x : ℝ) ^ (-ε) ≤ cellGram x (finOfSF j) (finOfSF j)

/-- A constant cell mass floor `C_jj ≥ h₀ > 0` gives `BandCellMass`. -/
theorem bandCellMass_of_const {h₀ : ℝ} (hh : 0 < h₀)
    (h : ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 3 / 4 < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j → h₀ ≤ cellGram x (finOfSF j) (finOfSF j)) :
    BandCellMass := by
  intro ε hε
  have ht : Tendsto (fun x : ℕ => (x : ℝ) ^ (-ε)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [h, ht.eventually (gt_mem_nhds hh)] with x h1 h2 j hj
  exact h2.le.trans (h1 j hj)

/-- **The band floor** H-U ∧ H-top: Theorem Q₀ on the Robin lattice and the band cell mass floor give
`TunnellingFloorSumPlunge`'s `BandFloor`. -/
theorem bandFloor_of_robinQ0 (hH : BandCellMass) (hQ : RobinQ0) : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor := by
  intro ε hε
  have hx80 : ∀ᶠ x : ℕ in atTop, (80 : ℝ) ≤ 2 * π * x := by
    have : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    exact this.eventually_ge_atTop 80
  filter_upwards [hH (ε / 2) (by linarith), hQ (ε / 2) (by linarith), hx80, eventually_ge_atTop 1]
    with x h1 h2 h3 h4 j hj
  obtain ⟨S, Q, hS, hjS, hdisj, hdeg, hQz, hQj, hsum⟩ := h2 j hj
  have hfloor := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.cellGram_div_sum_le_sigmaP h3 (finOfSF j) S hS hjS hdisj hdeg hQz hQj
  have hg : robinG (2 * π * x) (chi x (finOfSF j)) (chi x (finOfSF j)) ≠ 0 :=
    div_ne_zero (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinR_ne_zero (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinW_self _ _))
      (Real.sqrt_pos.mpr (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos _ _)).ne'
  have hone := one_le_sum_robinWeight hjS hQj hg
  have hx : (0 : ℝ) < x := by exact_mod_cast h4
  have hm := h1 j hj
  refine le_trans ?_ hfloor
  have hpos : (0 : ℝ) < (x : ℝ) ^ (ε / 2) := by positivity
  calc (x : ℝ) ^ (-ε) = (x : ℝ) ^ (-(ε / 2)) / (x : ℝ) ^ (ε / 2) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hx.le (ε / 2), ← Real.rpow_add hx]; ring_nf
    _ ≤ cellGram x (finOfSF j) (finOfSF j) / (x : ℝ) ^ (ε / 2) := by gcongr
    _ ≤ _ := div_le_div_of_nonneg_left ((Real.rpow_nonneg hx.le _).trans hm) (by linarith) hsum

end Cvs.Prolate.Gram.BandFloorFromRobinQZero

end
