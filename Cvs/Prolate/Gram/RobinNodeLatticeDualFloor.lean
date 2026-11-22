import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinDualCertificate
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.WindowFloorMinNormInterp
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungEqRegularSolution
import Cvs.Upstream.CellFloorSandwichPosDef

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Robin node lattice at `t = ½` and the dual floor on the real cell Gram

For `y_σ = regSol (sqC c) σ` and `U_σ = (1 − t²)y_σ'`, the Robin nodes through `χ` are the `σ` with
`W(χ, σ) = y_χU_σ − U_χy_σ = 0` at `½`; `W(χ, σ) = (χ − σ)∫_{½}^1 y_χy_σ`, so the normalised cell restrictions
`ψ_σ = y_σ/√N_σ` of the nodes are orthonormal in `L²(½, 1]` and pair with the cell vectors in Cauchy form. Cvs.Prolate.Gram.RobinDualCertificate
then gives `C_jj/Σ_S ρ_σ ≤ σ'_j` for every finite node set `S ∋ χ_j` and every `Q` vanishing at the other levels.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Polynomial Finset
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC)
open Cvs.Prolate.EvenRungsByIndex (rung lev)
open Cvs.Prolate.Gram.EvenFirstCellEnergyGram (L2c)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass)

namespace Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
open Cvs.ZeroCounting

/-! ### The Robin Wronskian at `½` -/

/-- The Robin Wronskian `W(χ, σ) = y_χ(½)U_σ(½) − U_χ(½)y_σ(½)`. -/
def robinW (c χ σ : ℝ) : ℝ :=
  regSol (sqC c) χ (1 / 2) * regU (sqC c) σ (1 / 2) - regU (sqC c) χ (1 / 2) * regSol (sqC c) σ (1 / 2)

theorem robinW_anti (c χ σ : ℝ) : robinW c σ χ = -robinW c χ σ := by unfold robinW; ring

theorem robinW_self (c χ : ℝ) : robinW c χ χ = 0 := by unfold robinW; ring

/-- **Green's identity on the cell**: `W(χ, σ) = (χ − σ)∫_{½}^1 y_χy_σ`. -/
theorem robinW_eq (c χ σ : ℝ) :
    robinW c χ σ = (χ - σ) * ∫ t in (1 / 2 : ℝ)..1, regSol (sqC c) χ t * regSol (sqC c) σ t := by
  have h := Cvs.Prolate.EdgeCentreSign.cross_wronskian (sqC c) (sqC c) χ σ (show (-1 : ℝ) < 1 / 2 by norm_num)
  unfold robinW
  rw [h, intervalIntegral.integral_symm, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- The reference vector `(y_χ(½), U_χ(½))` is nonzero. -/
theorem ref_pos (c χ : ℝ) : 0 < regSol (sqC c) χ (1 / 2) ^ 2 + regU (sqC c) χ (1 / 2) ^ 2 := by
  by_cases hy : regSol (sqC c) χ (1 / 2) = 0
  · have hU := Cvs.Prolate.EdgeCentreSign.regU_ne_zero_of_regSol_eq_zero (sqC c) χ (show (-1 : ℝ) < 1 / 2 by norm_num)
      (by norm_num) hy
    positivity
  · positivity

/-- The Robin ratio `R_σ = (y_σy_χ + U_σU_χ)/(y_χ² + U_χ²)` at `½`. -/
def robinR (c χ σ : ℝ) : ℝ :=
  (regSol (sqC c) σ (1 / 2) * regSol (sqC c) χ (1 / 2) + regU (sqC c) σ (1 / 2) * regU (sqC c) χ (1 / 2)) /
    (regSol (sqC c) χ (1 / 2) ^ 2 + regU (sqC c) χ (1 / 2) ^ 2)

theorem robinR_self (c χ : ℝ) : robinR c χ χ = 1 := by
  have := ref_pos c χ
  unfold robinR; field_simp

/-- At a Robin node, `(y_σ, U_σ)(½) = R_σ (y_χ, U_χ)(½)`. -/
theorem parallel {c χ σ : ℝ} (h : robinW c χ σ = 0) :
    regSol (sqC c) σ (1 / 2) = robinR c χ σ * regSol (sqC c) χ (1 / 2) ∧
      regU (sqC c) σ (1 / 2) = robinR c χ σ * regU (sqC c) χ (1 / 2) := by
  have hp := ref_pos c χ
  unfold robinW at h
  unfold robinR
  constructor
  · rw [div_mul_eq_mul_div, eq_div_iff hp.ne']
    linear_combination (-(regU (sqC c) χ (1 / 2))) * h
  · rw [div_mul_eq_mul_div, eq_div_iff hp.ne']
    linear_combination (regSol (sqC c) χ (1 / 2)) * h

/-- At a Robin node through `χ`, `W(b, σ) = R_σ W(b, χ)` for every `b`. -/
theorem robinW_node {c χ σ : ℝ} (h : robinW c χ σ = 0) (b : ℝ) :
    robinW c b σ = robinR c χ σ * robinW c b χ := by
  obtain ⟨h1, h2⟩ := parallel h
  unfold robinW; rw [h1, h2]; ring

theorem robinR_ne_zero {c χ σ : ℝ} (h : robinW c χ σ = 0) : robinR c χ σ ≠ 0 := by
  intro h0
  obtain ⟨h1, h2⟩ := parallel h
  rw [h0, zero_mul] at h1 h2
  have := ref_pos c σ
  rw [h1, h2] at this; norm_num at this

/-- Two Robin nodes through `χ` have `W(σ, σ') = 0`. -/
theorem robinW_nodes {c χ σ σ' : ℝ} (h : robinW c χ σ = 0) (h' : robinW c χ σ' = 0) : robinW c σ σ' = 0 := by
  rw [robinW_node h' σ, robinW_anti, h, neg_zero, mul_zero]

/-! ### The node mass and the cell restriction -/

theorem continuousOn_regSol_cell (c σ : ℝ) : ContinuousOn (regSol (sqC c) σ) (Icc (1 / 2 : ℝ) 1) :=
  (Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).mono fun t ht => show (-1 : ℝ) < t by linarith [ht.1]

/-- `N_σ = ∫_{½}^1 y_σ² > 0`. -/
theorem nodeMass_pos (c σ : ℝ) : 0 < nodeMass c σ := by
  set f : ℝ → ℝ := fun t => regSol (sqC c) σ t ^ 2 with hf
  have hcont : ContinuousOn f (Ioi (-1)) := (Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).pow 2
  have hca : ContinuousAt f 1 := hcont.continuousAt (Ioi_mem_nhds (by norm_num))
  have hf1 : f 1 = 1 := by simp [f, Cvs.Prolate.RegularSolutionEdge.regSol_one]
  have hev : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < f t := hca.eventually (lt_mem_nhds (by rw [hf1]; norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set d := min (ε / 2) (1 / 4) with hd_def
  have hd : 0 < d := by positivity
  have hd4 : d ≤ 1 / 4 := min_le_right _ _
  have hdε : d ≤ ε / 2 := min_le_left _ _
  have hint : ∀ a b : ℝ, a ∈ Icc (1 / 2 : ℝ) 1 → b ∈ Icc (1 / 2 : ℝ) 1 → IntervalIntegrable f volume a b :=
    fun a b ha hb => (hcont.mono fun t ht => show (-1 : ℝ) < t by
      linarith [(Set.uIcc_subset_Icc ha hb ht).1]).intervalIntegrable
  have hm : (1 - d) ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hh : (1 / 2 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hsplit : nodeMass c σ = (∫ t in (1 / 2 : ℝ)..(1 - d), f t) + ∫ t in (1 - d)..1, f t :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _ hh hm) (hint _ _ hm h1)).symm
  have hA : 0 ≤ ∫ t in (1 / 2 : ℝ)..(1 - d), f t :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _
  have hB : 0 < ∫ t in (1 - d)..1, f t := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint _ _ hm h1) (fun t ht => hball ?_) (by linarith)
    rw [Real.dist_eq, abs_of_neg (by linarith [ht.2])]
    linarith [ht.1]
  linarith

/-- The cell restriction `y_σ ∈ L²(½, 1]`. -/
def cellY (c σ : ℝ) : L2c := (Cvs.Prolate.Gram.WindowFloorMinNormInterp.memLp_cell (continuousOn_regSol_cell c σ)).toLp (regSol (sqC c) σ)

theorem inner_cellY (c σ σ' : ℝ) :
    inner ℝ (cellY c σ) (cellY c σ') = ∫ t in (1 / 2 : ℝ)..1, regSol (sqC c) σ t * regSol (sqC c) σ' t := by
  rw [L2.inner_def, intervalIntegral.integral_of_le (by norm_num)]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (Cvs.Prolate.Gram.WindowFloorMinNormInterp.memLp_cell (continuousOn_regSol_cell c σ)),
    MemLp.coeFn_toLp (Cvs.Prolate.Gram.WindowFloorMinNormInterp.memLp_cell (continuousOn_regSol_cell c σ'))] with t h1 h2
  simp only [cellY] at *
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, mul_comm]

theorem inner_cellY_self (c σ : ℝ) : inner ℝ (cellY c σ) (cellY c σ) = nodeMass c σ := by
  rw [inner_cellY]; unfold nodeMass; congr 1; ext t; ring

/-- The cell vector `√2 h_{4b}` is `√2 h_{4b}(1) y_{χ_b}` on the cell. -/
theorem cellVec_eq_smul {x : ℕ} (hx : 80 ≤ 2 * π * x) (b : Fin x) :
    Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellVec x b =
      (√2 * rung (2 * π * x) (2 * (b : ℕ)) 1) • cellY (2 * π * x) (lev (2 * π * x) (2 * (b : ℕ))) := by
  have hlev : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * (b : ℕ)) χ := Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx b
  rw [cellY, ← MemLp.toLp_const_smul]
  unfold Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellVec
  refine MemLp.toLp_congr _ _ ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht => ?_
  simp only [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun, Pi.smul_apply, smul_eq_mul]
  rw [(Cvs.Prolate.RungEqRegularSolution.rung_eq_mul_regSol hlev).2 t ⟨by linarith [ht.1], ht.2⟩]
  ring

/-! ### The normalised node vectors -/

/-- The normalised node vector `ψ_σ = y_σ/√N_σ`. -/
def robinVec (c σ : ℝ) : L2c := (√(nodeMass c σ))⁻¹ • cellY c σ

/-- The Cauchy weight `g_σ = R_σ/√N_σ` of a node through `χ`. -/
def robinG (c χ σ : ℝ) : ℝ := robinR c χ σ / √(nodeMass c σ)

theorem inner_robinVec_cellY (c σ σ' : ℝ) : inner ℝ (robinVec c σ) (cellY c σ') =
    (√(nodeMass c σ))⁻¹ * ∫ t in (1 / 2 : ℝ)..1, regSol (sqC c) σ t * regSol (sqC c) σ' t := by
  rw [robinVec, inner_smul_left, conj_trivial, inner_cellY]

/-- The node vectors of a Robin lattice are orthonormal. -/
theorem inner_robinVec {c χ σ σ' : ℝ} (h : robinW c χ σ = 0) (h' : robinW c χ σ' = 0) :
    inner ℝ (robinVec c σ) (robinVec c σ') = if σ = σ' then 1 else 0 := by
  rw [show robinVec c σ' = (√(nodeMass c σ'))⁻¹ • cellY c σ' from rfl, inner_smul_right,
    inner_robinVec_cellY]
  split_ifs with hs
  · subst hs
    have hN := nodeMass_pos c σ
    have hq := Real.sq_sqrt hN.le
    have hs0 : 0 < √(nodeMass c σ) := Real.sqrt_pos.mpr hN
    rw [show (∫ t in (1 / 2 : ℝ)..1, regSol (sqC c) σ t * regSol (sqC c) σ t) = nodeMass c σ by
      unfold nodeMass; congr 1; ext t; ring]
    field_simp
    linarith
  · have hW := robinW_nodes h h'
    rw [robinW_eq] at hW
    rcases mul_eq_zero.mp hW with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hs
    · rw [h0]; ring

/-! ### The dual floor on the cell Gram -/

/-- The rung level `χ_b = χ_{4b}` at `c = 2πx`. -/
abbrev chi (x : ℕ) (b : Fin x) : ℝ := lev (2 * π * x) (2 * (b : ℕ))

/-- The cell pairing: `⟨ψ_σ, Y_b⟩ = √2 h_{4b}(1) N_σ^{−1/2} ∫_{½}^1 y_σ y_{χ_b}`. -/
theorem inner_robinVec_cellVec {x : ℕ} (hx : 80 ≤ 2 * π * x) (σ : ℝ) (b : Fin x) :
    inner ℝ (robinVec (2 * π * x) σ) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellVec x b) = √2 * rung (2 * π * x) (2 * (b : ℕ)) 1 *
      ((√(nodeMass (2 * π * x) σ))⁻¹ *
        ∫ t in (1 / 2 : ℝ)..1, regSol (sqC (2 * π * x)) σ t * regSol (sqC (2 * π * x)) (chi x b) t) := by
  rw [cellVec_eq_smul hx, inner_smul_right, inner_robinVec_cellY]

/-- The cell mass `C_jj = 2h_{4j}(1)² N_{χ_j}`. -/
theorem cellGram_self {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) :
    Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x j j = (√2 * rung (2 * π * x) (2 * (j : ℕ)) 1 * √(nodeMass (2 * π * x) (chi x j))) ^ 2 := by
  rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram, Matrix.gram_apply, cellVec_eq_smul hx, inner_smul_left, inner_smul_right,
    inner_cellY_self, conj_trivial, mul_pow, mul_pow, Real.sq_sqrt (nodeMass_pos _ _).le]
  ring

/-- **The Robin dual floor on the cell Gram** (lemQ §1.2, cpa-loc P2): for a finite set `S` of Robin nodes through
`χ_j` containing `χ_j` and no other level, and `Q` of degree `< |S|` vanishing at `χ_b` (`b ≠ j`) with
`Q(χ_j) ≠ 0`, `C_jj/Σ_S ρ_σ ≤ σ'_j` with `ρ_σ = ((r_σ g_{χ_j})/(r_{χ_j} g_σ))²`, `g = robinG`. -/
theorem cellGram_div_sum_le_sigmaP {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) (S : Finset ℝ)
    (hS : ∀ σ ∈ S, robinW (2 * π * x) (chi x j) σ = 0) (hj : chi x j ∈ S) (hdisj : ∀ b, b ≠ j → chi x b ∉ S)
    {Q : ℝ[X]} (hQ : Q.degree < S.card) (hQz : ∀ b, b ≠ j → Q.eval (chi x b) = 0) (hQj : Q.eval (chi x j) ≠ 0) :
    Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x j j / ∑ σ ∈ S, Cvs.Prolate.Gram.RobinDualCertificate.robinWeight S id (robinG (2 * π * x) (chi x j)) Q (chi x j) σ
      ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x) j := by
  set c := 2 * π * x with hc
  set n : Fin x → ℝ := fun b => √2 * rung c (2 * (b : ℕ)) 1 * robinW c (chi x b) (chi x j) with hn
  have hint : ∀ σ ∈ S, ∀ b : Fin x, chi x b ≠ σ → ∫ t in (1 / 2 : ℝ)..1, regSol (sqC c) σ t *
      regSol (sqC c) (chi x b) t = robinR c (chi x j) σ * robinW c (chi x b) (chi x j) / (chi x b - σ) := by
    intro σ hσ b hb
    have hne : chi x b - σ ≠ 0 := sub_ne_zero.mpr hb
    have h1 := robinW_node (hS σ hσ) (chi x b)
    rw [robinW_eq] at h1
    rw [eq_div_iff hne, ← h1, mul_comm]
    exact congrArg ((chi x b - σ) * ·) (intervalIntegral.integral_congr fun t _ => mul_comm _ _)
  have hpair : ∀ b, b ≠ j → ∀ σ ∈ S, inner ℝ (robinVec c σ) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellVec x b) =
      n b * robinG c (chi x j) σ / (chi x b - id σ) := by
    intro b hb σ hσ
    have hb' : chi x b ≠ σ := fun h => hdisj b hb (h ▸ hσ)
    rw [inner_robinVec_cellVec hx, hint σ hσ b hb', hn, robinG, id]
    have := sub_ne_zero.mpr hb'
    field_simp
    rw [← hc]; ring
  have hjk : ∀ σ ∈ S, σ ≠ chi x j → inner ℝ (robinVec c σ) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellVec x j) = 0 := by
    intro σ hσ hne
    rw [inner_robinVec_cellVec hx, hint σ hσ j (Ne.symm hne), robinW_self]
    simp
  have ha : inner ℝ (robinVec c (chi x j)) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellVec x j) =
      √2 * rung c (2 * (j : ℕ)) 1 * √(nodeMass c (chi x j)) := by
    rw [inner_robinVec_cellVec hx]
    rw [show (∫ t in (1 / 2 : ℝ)..1, regSol (sqC c) (chi x j) t * regSol (sqC c) (chi x j) t)
      = nodeMass c (chi x j) by unfold nodeMass; congr 1; ext t; ring]
    have hN := nodeMass_pos c (chi x j)
    have hq := Real.sq_sqrt hN.le
    have hs0 : 0 < √(nodeMass c (chi x j)) := Real.sqrt_pos.mpr hN
    field_simp
    rw [← hc, div_eq_iff hs0.ne', mul_assoc, Real.mul_self_sqrt hN.le]
  have hg : ∀ σ ∈ S, robinG c (chi x j) σ ≠ 0 := fun σ hσ =>
    div_ne_zero (robinR_ne_zero (hS σ hσ)) (Real.sqrt_pos.mpr (nodeMass_pos c σ)).ne'
  have hz : ∀ b, b ≠ j → ∀ σ ∈ S, chi x b ≠ id σ := fun b hb σ hσ h => hdisj b hb (h ▸ hσ)
  have key := Cvs.Prolate.Gram.RobinDualCertificate.div_sum_robinWeight_le (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellVec x) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_posDef hx) j (robinVec c) S
    (fun σ hσ σ' hσ' => inner_robinVec (hS σ hσ) (hS σ' hσ')) id (Set.injOn_id _) (chi x) n
    (robinG c (chi x j)) hg hj rfl hz hpair hjk ha hQ hQz hQj
  rw [cellGram_self hx]
  exact key

end Cvs.Prolate.Gram.RobinNodeLatticeDualFloor

end
