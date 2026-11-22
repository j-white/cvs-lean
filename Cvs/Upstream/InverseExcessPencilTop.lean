import Mathlib
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.HalfBandLayerFloor
import Cvs.Prolate.Gram.HalfCellGramHadamard
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.PoleRemovedTopBlockExcess
import Cvs.Route.Visibility.ConditionBWithoutCut
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.PencilLayerBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The weighted inverse excess bounds the pencil top

For `C ≻ 0` with `C ≤ I` and weights `0 ≤ μ ≤ m`, the pencil top of `diag μ` against `C` is at most
`m + Σ_j μ_j((C⁻¹)_jj − 1)`. On the prolate cell Gram this gives `cE ≤ μ_t + R`, and `CEBound W̃` follows from an
eventual bound `R ≤ r` with `C₀∞(W̃)(μ* + r) < 2`.
-/

noncomputable section
open Real Set Matrix Finset Filter Topology

namespace Cvs.Upstream.InverseExcessPencilTop
open Cvs.ZeroCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weighted inverse excess `Σ_j μ_j((C⁻¹)_jj − 1)`. -/
def excessTrace (μ : ι → ℝ) (C : Matrix ι ι ℝ) : ℝ :=
  ∑ j, μ j * (C⁻¹ j j - 1)

/-- `C ≻ 0` with `vᵀCv ≤ vᵀv` gives `C⁻¹ − I ⪰ 0`. -/
theorem inv_sub_one_posSemidef {C : Matrix ι ι ℝ} (hC : C.PosDef)
    (hU : ∀ v, v ⬝ᵥ (C *ᵥ v) ≤ v ⬝ᵥ v) : (C⁻¹ - 1).PosSemidef := by
  have hf := Cvs.Upstream.PencilLayerBound.isFloor_inv_of_quad_le hC (by norm_num : (0 : ℝ) < 1)
    (by simpa using hU)
  apply PosSemidef.of_dotProduct_mulVec_nonneg (hC.inv.isHermitian.sub isHermitian_one)
  intro v
  have h := hf v
  simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub]
  exact sub_nonneg.mpr (by simpa using h)

/-- The weighted inverse excess is nonnegative for `0 < C ≤ I` and `μ ≥ 0`. -/
theorem excessTrace_nonneg {C : Matrix ι ι ℝ} (hC : C.PosDef)
    (hU : ∀ v, v ⬝ᵥ (C *ᵥ v) ≤ v ⬝ᵥ v) {μ : ι → ℝ} (hμ : ∀ j, 0 ≤ μ j) :
    0 ≤ excessTrace μ C := by
  apply Finset.sum_nonneg
  intro j _
  have h := (inv_sub_one_posSemidef hC hU).diag_nonneg (i := j)
  exact mul_nonneg (hμ j) (by simpa using h)

/-- The pencil top of `diag μ` against `C` is at most `m + Σ_j μ_j((C⁻¹)_jj − 1)` when `0 ≤ μ ≤ m`. -/
theorem pencilTop_le_excessTrace {C : Matrix ι ι ℝ} (hC : C.PosDef)
    (hU : ∀ v, v ⬝ᵥ (C *ᵥ v) ≤ v ⬝ᵥ v) {μ : ι → ℝ} (hμ : ∀ j, 0 ≤ μ j)
    {m : ℝ} (hm : 0 ≤ m) (hmax : ∀ j, μ j ≤ m) :
    Cvs.Upstream.PencilLayerBound.pencilTop μ C Set.univ ≤ m + excessTrace μ C := by
  let B : Matrix ι ι ℝ := diagonal (fun j => √(μ j))
  let A := Bᴴ * (C⁻¹ - 1) * B
  have hA : A.PosSemidef := (inv_sub_one_posSemidef hC hU).conjTranspose_mul_mul_same B
  have hAe : ∀ i j, A i j = √(μ i) * (C⁻¹ i j - (1 : Matrix ι ι ℝ) i j) * √(μ j) := by
    intro i j
    simp [A, B, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have htr : A.trace = excessTrace μ C := by
    unfold Matrix.trace excessTrace
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.diag, hAe, Matrix.one_apply_eq]
    linear_combination (C⁻¹ j j - 1) * Real.sq_sqrt (hμ j)
  apply Cvs.Upstream.PencilLayerBound.pencilTop_le (add_nonneg hm (excessTrace_nonneg hC hU hμ))
  intro v _
  let u : ι → ℝ := fun j => √(μ j) * v j
  let z : ι → ℝ := fun j => μ j * v j
  let q : ℝ := ∑ j, μ j * v j ^ 2
  have hq : 0 ≤ q := Finset.sum_nonneg fun j _ => mul_nonneg (hμ j) (sq_nonneg _)
  have hu : u ⬝ᵥ u = q := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [u]
    nlinarith [Real.sq_sqrt (hμ j)]
  have hz : z ⬝ᵥ v = q := by
    simp only [dotProduct, z, q]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hBu : B *ᵥ u = z := by
    ext j
    simp only [B, Matrix.mulVec_diagonal, u, z]
    linear_combination v j * Real.sq_sqrt (hμ j)
  have hform : u ⬝ᵥ (A *ᵥ u) = z ⬝ᵥ (C⁻¹ *ᵥ z) - z ⬝ᵥ z := by
    have hBt : Bᴴ = Bᵀ := by ext i j; simp
    dsimp [A]
    rw [hBt]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    simp only [vecMul_transpose, hBu,
      sub_mulVec, one_mulVec, dotProduct_sub]
  have hzz : z ⬝ᵥ z ≤ m * q := by
    rw [← hu]
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right (hmax j) (mul_nonneg (hμ j) (sq_nonneg (v j)))
    dsimp [z, u]
    convert h using 1
    · ring
    · linear_combination m * v j ^ 2 * Real.sq_sqrt (hμ j)
  have hquad := Cvs.Prolate.Gram.HalfCellGramHadamard.quad_le_trace hA u
  rw [hform, htr, hu] at hquad
  have hbound : z ⬝ᵥ (C⁻¹ *ᵥ z) ≤ (m + excessTrace μ C) * q := by nlinarith
  have henergy : 0 ≤ v ⬝ᵥ (C *ᵥ v) := by simpa using hC.posSemidef.dotProduct_mulVec_nonneg v
  have hcs := Cvs.Route.PoleRemovedTopBlockExcess.sq_dotProduct_le_mul_inv hC v z
  rw [hz] at hcs
  have hprod := mul_le_mul_of_nonneg_left hbound henergy
  change q ≤ (m + excessTrace μ C) * (v ⬝ᵥ (C *ᵥ v))
  rcases eq_or_lt_of_le hq with heq | hpos
  · rw [← heq]
    exact mul_nonneg (add_nonneg hm (excessTrace_nonneg hC hU hμ)) henergy
  · nlinarith

open Cvs.ZeroCounting

/-- `R = Σ_j μ_j((C⁻¹)_jj − 1)` on the prolate cell Gram. -/
def prolateExcess (x : ℕ) : ℝ :=
  excessTrace (fun j : Fin x => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu x j) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x)

/-- `cE ≤ μ_t + R` at `80 ≤ 2πx`. -/
theorem cE_le_muTop_add_excess {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Cvs.Route.Visibility.LayerFloorDeepRemainderB.cE x ≤ Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu x (x - 1) + prolateExcess x := by
  have hx2 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx
  apply pencilTop_le_excessTrace (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_posDef hx)
  · intro v
    have h := (Cvs.Prolate.Gram.HalfBandLayerFloor.one_sub_cellGram_posSemidef hx).dotProduct_mulVec_nonneg v
    simpa only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub, sub_nonneg] using h
  · intro j
    exact Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_nonneg hx j.2
  · exact Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_nonneg hx (by omega)
  · intro j
    exact Cvs.Prolate.Gram.DeepRemainderCellFloors.mu_mono hx (k := j) (j := ⟨x - 1, by omega⟩) (by exact_mod_cast Nat.le_sub_one_of_lt j.2)

/-- `CEBound W̃` from an eventual bound `R ≤ r` with `C₀∞(W̃)(μ* + r) < 2`. -/
theorem ceBound_of_excess {Wt r : ℝ}
    (hmargin : Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf Wt * (Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar + r) < 2)
    (hR : ∀ᶠ x : ℕ in atTop, prolateExcess x ≤ r) : Cvs.Route.Visibility.ConditionBWithoutCut.CEBound Wt := by
  refine ⟨Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf Wt * (Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar + r), hmargin, ?_⟩
  filter_upwards [hR, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hr hx
  apply mul_le_mul_of_nonneg_left _ (Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf_pos Wt).le
  exact (cE_le_muTop_add_excess hx).trans (add_le_add (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_top_le hx) hr)

/-- The margin `C₀∞(57/60)(μ* + 7/10) < 2`. -/
theorem excess_seven_tenths_margin :
    Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf (57 / 60) * (Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar + 7 / 10) < 2 := by
  have h2 : (707 : ℝ) / 500 < √2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hs : √((57 : ℝ) / 60 / 2) < 69 / 100 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 57 / 60 / 2 by norm_num),
      Real.sqrt_nonneg ((57 : ℝ) / 60 / 2)]
  have hC : Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf (57 / 60) < 14161 / 10000 := by
    unfold Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf
    nlinarith [Real.sqrt_nonneg ((57 : ℝ) / 60 / 2)]
  have hm : Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar + 7 / 10 < 347 / 250 := by
    unfold Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar
    linarith
  have hp : 0 < Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar + 7 / 10 := by linarith [Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos]
  have h := mul_lt_mul hC hm.le hp
    (by norm_num : (0 : ℝ) ≤ 14161 / 10000)
  norm_num at h ⊢
  linarith

/-- `CEBound (57/60)` from an eventual bound `R ≤ 7/10`. -/
theorem ceBound_of_excess_seven_tenths
    (hR : ∀ᶠ x : ℕ in atTop, prolateExcess x ≤ 7 / 10) :
    Cvs.Route.Visibility.ConditionBWithoutCut.CEBound (57 / 60) :=
  ceBound_of_excess excess_seven_tenths_margin hR

end Cvs.Upstream.InverseExcessPencilTop

end
