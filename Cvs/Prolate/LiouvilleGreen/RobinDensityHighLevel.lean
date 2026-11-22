import Mathlib
import Cvs.Prolate.Gram.BandCellMassFloor
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing
import Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# LemQ's (H2) on `τ ≥ 1 + A`: `p′(μ)·s ≍ 1 + τ` at both ends of every Robin cell

`H2Upper`/`H2Lower` state (H2) for the density `p′ = nodeRate/π` of Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement at both ends of a cell. Since
`nodeRate·G₀ = N(rX² + Y²/r)/(X² + Y²)` with `r = 4a₀/(3c) ≥ 1`, `NodeMassAboveCoulomb`'s bounds on `N/G₀` give
`k₁c/(2s) ≤ nodeRate ≤ 2k₂/c` above `(1 + A)c²`, and `RobinCellPhaseIncrement`'s cell identity turns them into (H2) with no upper limit.
-/

noncomputable section

open Real Set Filter Topology
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC)
open Cvs.Prolate.TopRungDepthBound (af)
open Cvs.Prolate.LiouvilleGreen.RateStrictlyDecreasing (kappa)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass energyHalf af_half regV_half)
open Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement (nodeRate ConsecNodes)

namespace Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-- **(H2), upper half**: `p′(ν)(σ′ − σ) ≤ C(1 + ν/c²)` at both ends `ν` of every Robin cell with ends in `c²I`. -/
def H2Upper (C c₀ : ℝ) (I : Set ℝ) : Prop :=
  ∀ c χ σ σ' : ℝ, c₀ ≤ c → ConsecNodes c χ σ σ' → σ / c ^ 2 ∈ I → σ' / c ^ 2 ∈ I →
    nodeRate c σ / π * (σ' - σ) ≤ C * (1 + σ / c ^ 2) ∧ nodeRate c σ' / π * (σ' - σ) ≤ C * (1 + σ' / c ^ 2)

/-- **(H2), lower half**: `p′(ν)(σ′ − σ) ≥ 1/(C(1 + ν/c²))` at both ends `ν` of every Robin cell with ends in `c²I`. -/
def H2Lower (C c₀ : ℝ) (I : Set ℝ) : Prop :=
  ∀ c χ σ σ' : ℝ, c₀ ≤ c → ConsecNodes c χ σ σ' → σ / c ^ 2 ∈ I → σ' / c ^ 2 ∈ I →
    1 / (C * (1 + σ / c ^ 2)) ≤ nodeRate c σ / π * (σ' - σ) ∧
      1 / (C * (1 + σ' / c ^ 2)) ≤ nodeRate c σ' / π * (σ' - σ)

/-- **lemQ (H2) on `c²I`**: both halves with one constant `C > 0` from one `c₀` on. -/
def H2 (I : Set ℝ) : Prop := ∃ C c₀ : ℝ, 0 < C ∧ H2Upper C c₀ I ∧ H2Lower C c₀ I

/-- **The rate against `N/G₀`**: `nodeRate·G₀ = N(rX² + Y²/r)/(X² + Y²)`, `X = cy`, `Y = y'`, `r = 4a₀/(3c)`. -/
theorem nodeRate_mul_energyHalf (hc : 0 < c) (hσ : c ^ 2 / 4 < σ) :
    nodeRate c σ * energyHalf c σ = nodeMass c σ *
      ((4 * af c ((c ^ 2 - σ) / c) (1 / 2) / (3 * c)) * (c * regSol (sqC c) σ (1 / 2)) ^ 2 +
        regV (sqC c) σ (1 / 2) ^ 2 / (4 * af c ((c ^ 2 - σ) / c) (1 / 2) / (3 * c))) /
      ((c * regSol (sqC c) σ (1 / 2)) ^ 2 + regV (sqC c) σ (1 / 2) ^ 2) := by
  have ha : 0 < af c ((c ^ 2 - σ) / c) (1 / 2) := by
    rw [af_half hc.ne']; apply Real.sqrt_pos.mpr; linarith
  have hR := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.refNorm_pos hc.ne' σ
  unfold nodeRate energyHalf Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy
  rw [regV_half]
  set a := af c ((c ^ 2 - σ) / c) (1 / 2)
  field_simp

/-- With `r ≥ 1`: `N/r ≤ nodeRate·G₀ ≤ rN`. -/
theorem rate_bounds_of_one_le (hc : 0 < c) (hσ : c ^ 2 / 4 < σ)
    (hr : 1 ≤ 4 * af c ((c ^ 2 - σ) / c) (1 / 2) / (3 * c)) :
    nodeMass c σ / (4 * af c ((c ^ 2 - σ) / c) (1 / 2) / (3 * c)) ≤ nodeRate c σ * energyHalf c σ ∧
      nodeRate c σ * energyHalf c σ ≤ (4 * af c ((c ^ 2 - σ) / c) (1 / 2) / (3 * c)) * nodeMass c σ := by
  rw [nodeRate_mul_energyHalf hc hσ]
  set r := 4 * af c ((c ^ 2 - σ) / c) (1 / 2) / (3 * c)
  set X := (c * regSol (sqC c) σ (1 / 2)) ^ 2
  set Y := regV (sqC c) σ (1 / 2) ^ 2
  have hR : 0 < X + Y := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.refNorm_pos hc.ne' σ
  have hX : 0 ≤ X := sq_nonneg _
  have hY : 0 ≤ Y := sq_nonneg _
  have hN := (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos c σ).le
  have hr0 : 0 < r := by linarith
  have hq1 : 1 / r ≤ (r * X + Y / r) / (X + Y) := by
    rw [div_le_div_iff₀ hr0 hR, one_mul]
    have e : (r * X + Y / r) * r = r ^ 2 * X + Y := by field_simp
    have h1 : 1 ≤ r ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hX
    rw [e]; linarith
  have hq2 : (r * X + Y / r) / (X + Y) ≤ r := by
    rw [div_le_iff₀ hR]
    have : Y / r ≤ r * Y := by
      rw [div_le_iff₀ hr0]
      have h1 : 1 ≤ r * r := by nlinarith
      have := mul_le_mul_of_nonneg_left h1 hY
      linarith
    nlinarith
  constructor
  · calc nodeMass c σ / r = nodeMass c σ * (1 / r) := by ring
      _ ≤ nodeMass c σ * ((r * X + Y / r) / (X + Y)) := mul_le_mul_of_nonneg_left hq1 hN
      _ = nodeMass c σ * (r * X + Y / r) / (X + Y) := by ring
  · calc nodeMass c σ * (r * X + Y / r) / (X + Y) = nodeMass c σ * ((r * X + Y / r) / (X + Y)) := by ring
      _ ≤ nodeMass c σ * r := mul_le_mul_of_nonneg_left hq2 hN
      _ = r * nodeMass c σ := by ring

/-- `r = 4a₀/(3c)` with `a₀ = √(¾(s − c²/4))` lies in `[1, 2√s/c]` for `s ≥ c²`. -/
theorem r_bounds (hc : 0 < c) (hs : c ^ 2 ≤ σ) :
    1 ≤ 4 * af c ((c ^ 2 - σ) / c) (1 / 2) / (3 * c) ∧
      4 * af c ((c ^ 2 - σ) / c) (1 / 2) / (3 * c) ≤ 2 * √σ / c := by
  rw [af_half hc.ne']
  have hσ0 : 0 ≤ σ := by nlinarith
  constructor
  · rw [le_div_iff₀ (by positivity), one_mul]
    have : (3 * c / 4) ^ 2 ≤ 3 / 4 * (σ - c ^ 2 / 4) := by nlinarith
    have := Real.le_sqrt_of_sq_le this
    linarith
  · rw [div_le_div_iff₀ (by positivity) hc]
    have : √(3 / 4 * (σ - c ^ 2 / 4)) ≤ √σ := Real.sqrt_le_sqrt (by nlinarith)
    have hs0 := Real.sqrt_nonneg σ
    nlinarith

/-- The constant `k₁ = 11/(400κ(½))` of `NodeMassAboveCoulomb`'s virial floor. -/
def kLow : ℝ := 11 / 400 / kappa (1 / 2)

/-- The constant `k₂ = 2κ(11/10)/√(A/(1 + A))` of `NodeMassAboveCoulomb`'s Bessel-side ceiling above `(1 + A)c²`. -/
def kHigh (A : ℝ) : ℝ := 2 * kappa (11 / 10) / √(A / (1 + A))

/-- The threshold `c₀ = max(80, 20κ(1 + κ), 16/A, 4π/k₁)`. -/
def cAbove (A : ℝ) : ℝ := max (max 80 (20 * kappa (1 / 2) * (1 + kappa (1 / 2)))) (max (16 / A) (4 * π / kLow))

theorem kLow_pos : 0 < kLow := div_pos (by norm_num) Cvs.Prolate.Gram.BandCellMassFloor.kappa_half_pos

theorem kHigh_pos {A : ℝ} (hA : 0 < A) : 0 < kHigh A := by
  unfold kHigh
  have : 0 < kappa (11 / 10) := by unfold kappa; positivity
  have : 0 < √(A / (1 + A)) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- **The rate above the Coulomb layer**: for `c ≥ c₀(A)` and `s ≥ (1 + A)c²`, `k₁c/(2s) ≤ nodeRate ≤ 2k₂/c`. -/
theorem rate_bounds_above {A : ℝ} (hA : 0 < A) (hc : cAbove A ≤ c) {s : ℝ} (hs : (1 + A) * c ^ 2 ≤ s) :
    kLow * c / (2 * s) ≤ nodeRate c s ∧ nodeRate c s ≤ 2 * kHigh A / c := by
  have hc80 : 80 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hck : 20 * kappa (1 / 2) * (1 + kappa (1 / 2)) ≤ c :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hcA : 16 / A ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hsc : c ^ 2 ≤ s := by nlinarith
  have hs0 : 0 < s := by linarith
  have hG := Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb.energyHalf_pos hc0.ne' (by linarith : c ^ 2 / 4 < s)
  obtain ⟨hr1, hr2⟩ := r_bounds hc0 hsc
  obtain ⟨hlo, hhi⟩ := rate_bounds_of_one_le hc0 (by linarith) hr1
  set r := 4 * af c ((c ^ 2 - s) / c) (1 / 2) / (3 * c)
  have hr0 : 0 < r := by linarith
  have hss : 0 < √s := Real.sqrt_pos.mpr hs0
  -- `N/G₀` bounds
  have hm1 := Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb.le_nodeMass_div hc80 hck hsc
  have hD : 16 * c ≤ s - c ^ 2 := by
    have : 16 ≤ A * c := by rwa [div_le_iff₀ hA, mul_comm] at hcA
    nlinarith
  have hm2 := Cvs.Prolate.LiouvilleGreen.NodeMassAboveCoulomb.nodeMass_div_le hc1 hD
  have hsD : √(A / (1 + A)) * √s ≤ √(s - c ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hAA : 0 < √(A / (1 + A)) := Real.sqrt_pos.mpr (by positivity)
  have hk : 0 < kappa (11 / 10) := by unfold kappa; positivity
  have hm2' : nodeMass c s / energyHalf c s ≤ kHigh A / √s := by
    refine hm2.trans ?_
    unfold kHigh
    rw [div_div, div_le_div_iff₀ (Real.sqrt_pos.mpr (by linarith)) (by positivity)]
    exact mul_le_mul_of_nonneg_left hsD (by positivity)
  constructor
  · -- lower
    have h1 : nodeMass c s / r ≤ nodeRate c s * energyHalf c s := hlo
    have h2 : kLow / √s ≤ nodeMass c s / energyHalf c s := by
      unfold kLow; rw [div_div]; exact hm1
    have h4 : nodeMass c s / energyHalf c s / r ≤ nodeRate c s := by
      rw [div_right_comm, div_le_iff₀ hG]; exact h1
    have h3 : kLow / √s / r ≤ nodeRate c s := (div_le_div_of_nonneg_right h2 hr0.le).trans h4
    have h5 : √s * r ≤ 2 * s / c := by
      calc √s * r ≤ √s * (2 * √s / c) := mul_le_mul_of_nonneg_left hr2 hss.le
        _ = 2 * (√s * √s) / c := by ring
        _ = 2 * s / c := by rw [Real.mul_self_sqrt hs0.le]
    calc kLow * c / (2 * s) = kLow / (2 * s / c) := by field_simp
      _ ≤ kLow / (√s * r) := div_le_div_of_nonneg_left kLow_pos.le (by positivity) h5
      _ = kLow / √s / r := by rw [div_div]
      _ ≤ nodeRate c s := h3
  · -- upper
    have h1 : nodeRate c s ≤ r * (nodeMass c s / energyHalf c s) := by
      rw [mul_div_assoc', le_div_iff₀ hG]; exact hhi
    calc nodeRate c s ≤ r * (nodeMass c s / energyHalf c s) := h1
      _ ≤ (2 * √s / c) * (kHigh A / √s) := mul_le_mul hr2 hm2' (div_nonneg (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos c s).le hG.le)
          (by positivity)
      _ = 2 * kHigh A / c := by field_simp

/-- **lemQ (H2) above the Coulomb layer**: for every `A > 0`, (H2) holds on `τ ≥ 1 + A`, with no upper limit. -/
theorem h2_above {A : ℝ} (hA : 0 < A) : H2 (Ici (1 + A)) := by
  have hk1 := kLow_pos
  have hk2 := kHigh_pos hA
  refine ⟨8 * kHigh A / kLow, cAbove A, by positivity, ?_, ?_⟩
  all_goals
    intro c χ σ σ' hc hcell hσI hσ'I
    have hc80 : 80 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
    have hc0 : 0 < c := by linarith
    have hc2 : 0 < c ^ 2 := by positivity
    have hcπ : 4 * π / kLow ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
    have hσ : (1 + A) * c ^ 2 ≤ σ := by
      have := (le_div_iff₀ hc2).mp (show 1 + A ≤ σ / c ^ 2 from hσI); linarith
    have hlt := hcell.1
    have hσ0 : 0 < σ := by nlinarith
    have hrate := fun s (hs : σ ≤ s) => rate_bounds_above hA hc (hσ.trans hs)
    -- the cell length
    have hL : 0 < kLow * c / (4 * σ) := by positivity
    have hlen : σ' - σ ≤ π / (kLow * c / (4 * σ)) := by
      refine Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.cell_length_le hc0 hcell hL fun s hs hsm => ?_
      have hle : π / (kLow * c / (4 * σ)) ≤ σ := by
        rw [div_le_iff₀ hL, show σ * (kLow * c / (4 * σ)) = kLow * c / 4 by field_simp]
        have := (div_le_iff₀ hk1).mp hcπ
        linarith
      have hs2 : s ≤ 2 * σ := by linarith
      have h := (hrate s hs.1.le).1
      calc kLow * c / (4 * σ) ≤ kLow * c / (2 * s) := by
            apply div_le_div_of_nonneg_left (by positivity) (by linarith [hs.1]) (by linarith)
        _ ≤ nodeRate c s := h
    have hlen' : σ' - σ ≤ 4 * π * σ / (kLow * c) := by
      rw [show 4 * π * σ / (kLow * c) = π / (kLow * c / (4 * σ)) by field_simp]; exact hlen
    -- the cell lower length
    obtain ⟨ξ, hξ, hξe⟩ := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.exists_nodeRate_mul_eq hc0 hcell
    have hξr := (hrate ξ hξ.1.le).2
    have hlenlo : π * c / (2 * kHigh A) ≤ σ' - σ := by
      rw [div_le_iff₀ (by positivity)]
      have : π ≤ 2 * kHigh A / c * (σ' - σ) := by
        rw [← hξe]; exact mul_le_mul_of_nonneg_right hξr (by linarith)
      rw [div_mul_eq_mul_div, le_div_iff₀ hc0] at this
      linarith
  · -- upper
    have key : ∀ ν, σ ≤ ν → nodeRate c ν / π * (σ' - σ) ≤ 8 * kHigh A / kLow * (σ / c ^ 2) := by
      intro ν hν
      have h := (hrate ν hν).2
      have h0 : 0 ≤ σ' - σ := by linarith
      calc nodeRate c ν / π * (σ' - σ) ≤ 2 * kHigh A / c / π * (4 * π * σ / (kLow * c)) := by
            apply mul_le_mul (div_le_div_of_nonneg_right h pi_pos.le) hlen' h0 (by positivity)
        _ = 8 * kHigh A / kLow * (σ / c ^ 2) := by field_simp; ring
    have hτ : σ / c ^ 2 ≤ σ' / c ^ 2 := div_le_div_of_nonneg_right hlt.le hc2.le
    have hτ0 : 0 ≤ σ / c ^ 2 := by positivity
    have hC : 0 ≤ 8 * kHigh A / kLow := by positivity
    constructor
    · refine (key σ le_rfl).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith) hC
    · refine (key σ' hlt.le).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith) hC
  · -- lower
    have key : ∀ ν, σ ≤ ν → kLow / (4 * kHigh A) / (ν / c ^ 2) ≤ nodeRate c ν / π * (σ' - σ) := by
      intro ν hν
      have hν0 : 0 < ν := by linarith
      have h := (hrate ν hν).1
      calc kLow / (4 * kHigh A) / (ν / c ^ 2) = kLow * c / (2 * ν) / π * (π * c / (2 * kHigh A)) := by
            field_simp; ring
        _ ≤ nodeRate c ν / π * (σ' - σ) := by
            apply mul_le_mul (div_le_div_of_nonneg_right h pi_pos.le) hlenlo (by positivity)
              (div_nonneg (Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.nodeRate_pos hc0 ν).le pi_pos.le)
    have hkC : kLow / (4 * kHigh A) * (8 * kHigh A / kLow) = 2 := by field_simp; ring
    have fin : ∀ ν, σ ≤ ν → 1 / (8 * kHigh A / kLow * (1 + ν / c ^ 2)) ≤ nodeRate c ν / π * (σ' - σ) := by
      intro ν hν
      have hν0 : 0 < ν := by linarith
      have hτ : 0 < ν / c ^ 2 := by positivity
      refine le_trans ?_ (key ν hν)
      rw [div_le_div_iff₀ (by positivity) hτ, one_mul]
      have e : kLow / (4 * kHigh A) * (8 * kHigh A / kLow * (1 + ν / c ^ 2)) = 2 * (1 + ν / c ^ 2) := by
        rw [← mul_assoc, hkC]
      rw [e]; linarith
    exact ⟨fin σ le_rfl, fin σ' hlt.le⟩

end Cvs.Prolate.LiouvilleGreen.RobinDensityHighLevel

end
