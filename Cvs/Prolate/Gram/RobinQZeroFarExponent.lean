import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.Gram.BandFloorFromRobinQZero
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.RobinQZeroNodePositions
import Cvs.Prolate.Gram.RobinWeightLogPotential
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.LiouvilleGreen.FarRobinRate
import Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement
import Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel
import Cvs.Prolate.LiouvilleGreen.RobinDensityNear
import Cvs.Route.Visibility.WindowChainCellFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Theorem Q₀ on positions at the one far exponent `K = 1`

`RobinQZeroNodePositions`'s `PosQ0` asks for its position sum at every far exponent `K`; its proof uses only the exponent of the far
rate bound, and Cvs.Prolate.LiouvilleGreen.FarRobinRate gives `θ' ≤ c` there. So `PosQ0At 1`, the position sum with far weight `c(1 + τ_χ)s_χ`,
gives `RobinQ0` and hV with `FarRate` discharged.
-/

noncomputable section

open Real Set Filter Topology Finset
open Cvs.Route.Visibility.WindowChainCellFloors (finOfSF)
open Cvs.Prolate.Gram.RobinNodeLatticeDualFloor (robinW chi)
open Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement (nodeRate ConsecNodes)
open Cvs.Prolate.Gram.RobinWeightLogPotential (logPot RobinPotQ0)
open Cvs.Prolate.Gram.RobinQZeroNodePositions (posWeight)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (C0inf muStar)

namespace Cvs.Prolate.Gram.RobinQZeroFarExponent
open Cvs.ZeroCounting

/-- **Theorem Q₀ on positions at far exponent `K`**: `RobinQZeroNodePositions`'s `PosQ0` with `K` fixed. -/
def PosQ0At (K : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 3 / 4 < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    ∃ (S : Finset ℝ) (Z : Multiset ℝ) (nxt : ℝ → ℝ),
      (∀ σ ∈ S, robinW (2 * π * x) (chi x (finOfSF j)) σ = 0) ∧
      chi x (finOfSF j) ∈ S ∧ (∀ b, b ≠ finOfSF j → chi x b ∉ S) ∧ (x - 1) + Multiset.card Z < S.card ∧
      (∀ σ ∈ S, σ ∉ Z) ∧ (∀ σ ∈ S, (2 * π * x) ^ 2 / 4 ≤ σ) ∧
      (∀ σ ∈ S, 5 * (2 * π * x) ^ 2 / 8 ≤ σ → ConsecNodes (2 * π * x) (chi x (finOfSF j)) σ (nxt σ)) ∧
      ∑ σ ∈ S, posWeight (2 * π * x) K (chi x (finOfSF j)) σ (nxt (chi x (finOfSF j))) (nxt σ) *
        Real.exp (2 * (logPot x (finOfSF j) S Z σ - logPot x (finOfSF j) S Z (chi x (finOfSF j)))) ≤
        (x : ℝ) ^ ε

/-- **Theorem Q₀ from positions at one exponent**: a far rate bound `θ' ≤ c^K` and `PosQ0At K` give
`RobinPotQ0`. -/
theorem robinPotQ0_of_posAt {K c₁ : ℝ}
    (hF : ∀ c, c₁ ≤ c → ∀ σ, c ^ 2 / 4 ≤ σ → σ < 5 * c ^ 2 / 8 → nodeRate c σ ≤ c ^ K) (hP : PosQ0At K) :
    RobinPotQ0 := by
  obtain ⟨C, c₀, hC, hu, hl⟩ := Cvs.Prolate.LiouvilleGreen.RobinDensityNear.h2_near
  set M := max (C ^ 2) (C / π) with hM
  have hM0 : 0 < M := lt_max_of_lt_left (by positivity)
  intro ε hε
  have hcT : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hsmall : ∀ᶠ x : ℕ in atTop, M * (x : ℝ) ^ (ε / 2) ≤ (x : ℝ) ^ ε := by
    have ht : Tendsto (fun x : ℕ => (x : ℝ) ^ (ε / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually_ge_atTop M, eventually_ge_atTop 1] with x hx hx1
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    have : (x : ℝ) ^ ε = (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_add hx0]; ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  filter_upwards [hP (ε / 2) (by linarith), hsmall, hcT.eventually_ge_atTop (max c₀ c₁),
    eventually_ge_atTop 1] with x hPx hsx hcx hx1 j hj
  obtain ⟨S, Z, nxt, hnode, hjS, hdisj, hcard, hZ, hlow, hcell, hsum⟩ := hPx j hj
  refine ⟨S, Z, hnode, hjS, hdisj, hcard, hZ, ?_⟩
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
  have hc : 0 < 2 * π * (x : ℝ) := by positivity
  have hχ := Cvs.Prolate.Gram.RobinQZeroNodePositions.five_eighths_le_chi hx1 j hj
  refine le_trans ?_ (le_trans (mul_le_mul_of_nonneg_left hsum hM0.le) hsx)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun σ hσ => ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact Cvs.Prolate.Gram.RobinQZeroNodePositions.rate_div_le hC hu hl hF hc ((le_max_left _ _).trans hcx) ((le_max_right _ _).trans hcx) hχ
    (hcell _ hjS hχ) (hlow σ hσ) (hcell σ hσ)

/-- **Theorem Q₀** (`BandFloorFromRobinQZero`'s `RobinQ0`) from `PosQ0At 1` alone. -/
theorem robinQ0_of_pos' (hP : PosQ0At 1) : Cvs.Prolate.Gram.BandFloorFromRobinQZero.RobinQ0 :=
  Cvs.Prolate.Gram.RobinWeightLogPotential.robinQ0_of_pot (robinPotQ0_of_posAt (c₁ := 2)
    (fun c hc σ h1 h2 => by rw [Real.rpow_one]; exact Cvs.Prolate.LiouvilleGreen.FarRobinRate.nodeRate_le_far hc h1 h2) hP)

end Cvs.Prolate.Gram.RobinQZeroFarExponent

end
