import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinDualCertificate
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.WindowFloorMinNormInterp
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
# The Dirichlet dual floor on a shifted cell `(a, 1]` (eq-cpb Lemma 1)

For Dirichlet nodes `y_σ(a) = 0` the restrictions `ψ_σ = 1_{(a,1]}y_σ/√N_a(σ)` are orthonormal in `L²(½, 1]` and
`(χ_b − σ)⟨ψ_σ, Y_b⟩ = √2h_{4b}(a)·U_σ(a)/√N_a(σ)`, so any `Q` of degree `< |S|` vanishing at the other levels gives
`(√2h_{4j}(a)Q(χ_j)/Π_S(χ_j))² / Σ_S (r_σ/g_σ)² ≤ σ'_j`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Polynomial Finset
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC)
open Cvs.Prolate.EvenRungsByIndex (rung lev)
open Cvs.Prolate.Gram.EvenFirstCellEnergyGram (L2c)

namespace Cvs.Prolate.Gram.DirichletDualFloorShifted
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.RobinDualCertificate (resid)

/-! ### The Cauchy dual certificate without a reference node -/

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cauchy dual floor**: orthonormal `ψ_k` (`k ∈ S`) with `(χ_b − k)⟨ψ_k, u_b⟩ = n_b g_k` and `Q` of degree
`< |S|` vanishing at `χ_b` (`b ≠ j`) give `(n_j Q(χ_j)/Π_S(χ_j))²/Σ_S (r_k/g_k)² ≤ σ'_j`. -/
theorem sq_div_sum_le_sigmaP (u : ι → E) (hM : (Matrix.gram ℝ u).PosDef) (j : ι) (ψ : ℝ → E) (S : Finset ℝ)
    (hψ : ∀ k ∈ S, ∀ l ∈ S, inner ℝ (ψ k) (ψ l) = if k = l then 1 else 0) (χ n : ι → ℝ) (g : ℝ → ℝ)
    (hg : ∀ k ∈ S, g k ≠ 0) (hpair : ∀ b, ∀ k ∈ S, (χ b - k) * inner ℝ (ψ k) (u b) = n b * g k)
    {Q : ℝ[X]} (hQ : Q.degree < S.card) (hQz : ∀ b, b ≠ j → Q.eval (χ b) = 0) :
    (n j * (Q.eval (χ j) / ∏ k ∈ S, (χ j - k))) ^ 2 / ∑ k ∈ S, (resid S id Q k / g k) ^ 2
      ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (Matrix.gram ℝ u) j := by
  have hσpos := (Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos hM j).le
  have hsum : ∀ {z : ℝ}, (∀ k ∈ S, z ≠ k) →
      ∑ k ∈ S, resid S id Q k / (z - k) = Q.eval z / ∏ k ∈ S, (z - k) := fun hz =>
    Cvs.Prolate.Gram.RobinDualCertificate.sum_resid_div (Set.injOn_id _) hQ hz
  set β : ℝ → ℝ := fun k => resid S id Q k / g k with hβ
  set v : E := ∑ k ∈ S, β k • ψ k with hvdef
  have hterm : ∀ b, (∀ k ∈ S, χ b ≠ k) → ∀ k ∈ S,
      inner ℝ (β k • ψ k) (u b) = n b * (resid S id Q k / (χ b - k)) := by
    intro b hb k hk
    have hne : χ b - k ≠ 0 := sub_ne_zero.mpr (hb k hk)
    have hp : inner ℝ (ψ k) (u b) = n b * g k / (χ b - k) := by
      rw [eq_div_iff hne, mul_comm]; exact hpair b k hk
    rw [inner_smul_left, conj_trivial, hp, hβ]
    have := hg k hk
    field_simp
  have hvb : ∀ b, (∀ k ∈ S, χ b ≠ k) → inner ℝ v (u b) = n b * (Q.eval (χ b) / ∏ k ∈ S, (χ b - k)) := by
    intro b hb
    rw [hvdef, sum_inner, Finset.sum_congr rfl (hterm b hb), ← Finset.mul_sum, hsum hb]
  have hv : ∀ b, b ≠ j → inner ℝ v (u b) = 0 := by
    intro b hbj
    by_cases hb : ∀ k ∈ S, χ b ≠ k
    · rw [hvb b hb, hQz b hbj, zero_div, mul_zero]
    · push Not at hb
      obtain ⟨k₀, hk₀, hbk⟩ := hb
      have hn : n b = 0 := by
        have := hpair b k₀ hk₀
        rw [hbk, sub_self, zero_mul] at this
        exact (mul_eq_zero.mp this.symm).resolve_right (hg k₀ hk₀)
      rw [hvdef, sum_inner]
      refine Finset.sum_eq_zero fun k hk => ?_
      by_cases hkk : k = k₀
      · subst hkk
        have hr : resid S id Q k = 0 := by
          unfold resid; rw [id, ← hbk, hQz b hbj, zero_mul]
        rw [inner_smul_left, hβ]; simp [hr]
      · have := hpair b k hk
        rw [hn, zero_mul, hbk] at this
        have hne : k₀ - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hkk)
        rw [inner_smul_left, (mul_eq_zero.mp this).resolve_left hne, mul_zero]
  by_cases hj : ∀ k ∈ S, χ j ≠ k
  · have hkey := Cvs.Prolate.Gram.RobinDualCertificate.sq_inner_le_sigmaP u hM j v hv
    rw [hvb j hj] at hkey
    have hnorm : ‖v‖ ^ 2 = ∑ k ∈ S, β k ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hvdef, sum_inner]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [inner_sum, Finset.sum_eq_single k (fun l hl hne => by
        rw [inner_smul_left, inner_smul_right, hψ k hk l hl, ite_eq_right (Ne.symm hne)]; simp)
        (fun h => absurd hk h), inner_smul_left, inner_smul_right, hψ k hk k hk, ite_eq_left rfl]
      simp; ring
    rw [hnorm] at hkey
    rcases (Finset.sum_nonneg fun k _ => sq_nonneg (β k) : 0 ≤ ∑ k ∈ S, β k ^ 2).eq_or_lt with h0 | h0
    · rw [← h0, div_zero]; exact hσpos
    · rw [div_le_iff₀ h0]; linarith
  · push Not at hj
    obtain ⟨k₀, hk₀, hjk⟩ := hj
    rw [Finset.prod_eq_zero hk₀ (by rw [hjk, sub_self]), div_zero, mul_zero]
    simpa using hσpos

end Gram

/-! ### The Dirichlet restrictions on `(a, 1]` -/

/-- The Dirichlet mass `N_a(σ) = ∫_a^1 y_σ²`. -/
def dirMass (c a σ : ℝ) : ℝ := ∫ t in a..1, regSol (sqC c) σ t ^ 2

/-- **Green's identity at `a`**: `y_χ(a)U_σ(a) − U_χ(a)y_σ(a) = (χ − σ)∫_a^1 y_χy_σ`. -/
theorem wronskian_eq (c χ σ : ℝ) {a : ℝ} (ha : -1 < a) :
    regSol (sqC c) χ a * regU (sqC c) σ a - regU (sqC c) χ a * regSol (sqC c) σ a =
      (χ - σ) * ∫ t in a..1, regSol (sqC c) χ t * regSol (sqC c) σ t := by
  rw [Cvs.Prolate.EdgeCentreSign.cross_wronskian (sqC c) (sqC c) χ σ ha, intervalIntegral.integral_symm,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- `N_a(σ) > 0` for `−1 < a < 1`. -/
theorem dirMass_pos (c σ : ℝ) {a : ℝ} (ha : -1 < a) (ha1 : a < 1) : 0 < dirMass c a σ := by
  set f : ℝ → ℝ := fun t => regSol (sqC c) σ t ^ 2 with hf
  have hcont : ContinuousOn f (Ioi (-1)) := (Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).pow 2
  have hca : ContinuousAt f 1 := hcont.continuousAt (Ioi_mem_nhds (by norm_num))
  have hf1 : f 1 = 1 := by simp [f, Cvs.Prolate.RegularSolutionEdge.regSol_one]
  have hev : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < f t := hca.eventually (lt_mem_nhds (by rw [hf1]; norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set d := min (ε / 2) ((1 - a) / 2) with hd_def
  have hd : 0 < d := lt_min (by positivity) (by linarith)
  have hd4 : d ≤ (1 - a) / 2 := min_le_right _ _
  have hdε : d ≤ ε / 2 := min_le_left _ _
  have hint : ∀ s t : ℝ, s ∈ Icc a 1 → t ∈ Icc a 1 → IntervalIntegrable f volume s t :=
    fun s t hs ht => (hcont.mono fun r hr => show (-1 : ℝ) < r by
      linarith [(Set.uIcc_subset_Icc hs ht hr).1]).intervalIntegrable
  have hm : (1 - d) ∈ Icc a 1 := ⟨by linarith, by linarith⟩
  have hh : a ∈ Icc a 1 := ⟨le_rfl, ha1.le⟩
  have h1 : (1 : ℝ) ∈ Icc a 1 := ⟨ha1.le, le_rfl⟩
  have hsplit : dirMass c a σ = (∫ t in a..(1 - d), f t) + ∫ t in (1 - d)..1, f t :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _ hh hm) (hint _ _ hm h1)).symm
  have hA : 0 ≤ ∫ t in a..(1 - d), f t :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => sq_nonneg _
  have hB : 0 < ∫ t in (1 - d)..1, f t := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint _ _ hm h1) (fun t ht => hball ?_) (by linarith)
    rw [Real.dist_eq, abs_of_neg (by linarith [ht.2])]
    linarith [ht.1]
  linarith

theorem memLp_dir (c a σ : ℝ) :
    MemLp ((Ioi a).indicator (regSol (sqC c) σ)) 2 (volume.restrict (Ioc (1 / 2 : ℝ) 1)) :=
  (Cvs.Prolate.Gram.WindowFloorMinNormInterp.memLp_cell (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.continuousOn_regSol_cell c σ)).indicator measurableSet_Ioi.nullMeasurableSet

/-- The restriction `1_{(a,1]}y_σ ∈ L²(½, 1]`. -/
def dirY (c a σ : ℝ) : L2c := (memLp_dir c a σ).toLp _

/-- `∫_{(½,1]} 1_{(a,∞)}f = ∫_a^1 f` for `½ ≤ a ≤ 1`. -/
theorem integral_cell_indicator {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) (f : ℝ → ℝ) :
    ∫ t in Ioc (1 / 2 : ℝ) 1, (Ioi a).indicator f t = ∫ t in a..1, f t := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    intervalIntegral.integral_of_le ha1]
  congr 2
  ext t
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith, h3⟩

theorem inner_dirY_cellY {c a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) (σ σ' : ℝ) :
    inner ℝ (dirY c a σ) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.cellY c σ') =
      ∫ t in a..1, regSol (sqC c) σ t * regSol (sqC c) σ' t := by
  rw [L2.inner_def, ← integral_cell_indicator ha ha1]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_dir c a σ),
    MemLp.coeFn_toLp (Cvs.Prolate.Gram.WindowFloorMinNormInterp.memLp_cell (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.continuousOn_regSol_cell c σ'))] with t h1 h2
  simp only [dirY, Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.cellY] at *
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
  by_cases ht : t ∈ Ioi a
  · simp [Set.indicator_of_mem ht, mul_comm]
  · simp [Set.indicator_of_notMem ht]

theorem inner_dirY_dirY {c a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1) (σ σ' : ℝ) :
    inner ℝ (dirY c a σ) (dirY c a σ') = ∫ t in a..1, regSol (sqC c) σ t * regSol (sqC c) σ' t := by
  rw [L2.inner_def, ← integral_cell_indicator ha ha1]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_dir c a σ), MemLp.coeFn_toLp (memLp_dir c a σ')] with t h1 h2
  simp only [dirY] at *
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
  by_cases ht : t ∈ Ioi a
  · simp [Set.indicator_of_mem ht, mul_comm]
  · simp [Set.indicator_of_notMem ht]

/-- The normalised Dirichlet vector `ψ_σ = 1_{(a,1]}y_σ/√N_a(σ)`. -/
def dirVec (c a σ : ℝ) : L2c := (√(dirMass c a σ))⁻¹ • dirY c a σ

/-- The Cauchy weight `g_σ = U_σ(a)/√N_a(σ)` of a Dirichlet node. -/
def dirG (c a σ : ℝ) : ℝ := regU (sqC c) σ a / √(dirMass c a σ)

/-- **Dirichlet nodes are orthonormal** on `(a, 1]`. -/
theorem inner_dirVec {c a σ σ' : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) (h : regSol (sqC c) σ a = 0)
    (h' : regSol (sqC c) σ' a = 0) :
    inner ℝ (dirVec c a σ) (dirVec c a σ') = if σ = σ' then 1 else 0 := by
  rw [dirVec, dirVec, inner_smul_left, inner_smul_right, inner_dirY_dirY ha ha1.le, conj_trivial]
  split_ifs with hs
  · subst hs
    have hN := dirMass_pos c σ (by linarith) ha1
    have hs0 : 0 < √(dirMass c a σ) := Real.sqrt_pos.mpr hN
    rw [show (∫ t in a..1, regSol (sqC c) σ t * regSol (sqC c) σ t) = dirMass c a σ by
      unfold dirMass; congr 1; ext t; ring]
    have hq := Real.mul_self_sqrt hN.le
    field_simp
    linarith
  · have hW := wronskian_eq c σ σ' (show -1 < a by linarith)
    rw [h, h', zero_mul, mul_zero, sub_zero] at hW
    rcases mul_eq_zero.mp hW.symm with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hs
    · rw [h0]; ring

/-- `g_σ ≠ 0` at a Dirichlet node with `−1 < a < 1`. -/
theorem dirG_ne_zero {c a σ : ℝ} (ha : -1 < a) (ha1 : a < 1) (h : regSol (sqC c) σ a = 0) : dirG c a σ ≠ 0 :=
  div_ne_zero (Cvs.Prolate.EdgeCentreSign.regU_ne_zero_of_regSol_eq_zero (sqC c) σ ha ha1 h)
    (Real.sqrt_pos.mpr (dirMass_pos c σ ha ha1)).ne'

/-- **The Dirichlet pairing**: `(χ_b − σ)⟨ψ_σ, Y_b⟩ = Y_b(a)·g_σ` for a node `y_σ(a) = 0`. -/
theorem pair_dirVec_cellVec {x : ℕ} (hx : 80 ≤ 2 * π * x) {a σ : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    (h : regSol (sqC (2 * π * x)) σ a = 0) (b : Fin x) :
    (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b - σ) * inner ℝ (dirVec (2 * π * x) a σ) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellVec x b) =
      Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x b a * dirG (2 * π * x) a σ := by
  set c := 2 * π * (x : ℝ) with hc
  have hlev : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c (2 * (b : ℕ)) χ := Cvs.Prolate.Gram.RungCellGramDisplacement.rungIdx_level hx b
  have hW := wronskian_eq c (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) σ (show -1 < a by linarith)
  rw [h, mul_zero, sub_zero] at hW
  rw [Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.cellVec_eq_smul hx, dirVec, inner_smul_left, inner_smul_right, conj_trivial,
    inner_dirY_cellY ha ha1, Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun, (Cvs.Prolate.RungEqRegularSolution.rung_eq_mul_regSol hlev).2 a ⟨by linarith, ha1⟩, dirG]
  have hcomm : (∫ t in a..1, regSol (sqC c) σ t * regSol (sqC c) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) t) =
      ∫ t in a..1, regSol (sqC c) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) t * regSol (sqC c) σ t := by
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hcomm]
  calc (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b - σ) * ((√(dirMass c a σ))⁻¹ * (√2 * rung c (2 * (b : ℕ)) 1 *
        ∫ t in a..1, regSol (sqC c) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) t * regSol (sqC c) σ t))
      = (√(dirMass c a σ))⁻¹ * √2 * rung c (2 * (b : ℕ)) 1 *
        ((Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b - σ) * ∫ t in a..1, regSol (sqC c) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) t * regSol (sqC c) σ t) := by ring
    _ = _ := by rw [← hW]; ring

/-- **The Dirichlet dual floor on the cell Gram** (eq-cpb Lemma 1): for `½ ≤ a < 1`, a finite set `S` of Dirichlet
nodes `y_σ(a) = 0` and `Q` of degree `< |S|` vanishing at `χ_b` (`b ≠ j`),
`(Y_j(a)Q(χ_j)/Π_S(χ_j))²/Σ_S (r_σ/g_σ)² ≤ σ'_j`, with `Y_j(a) = √2h_{4j}(a)` and `g = dirG`. -/
theorem dirichlet_le_sigmaP {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1)
    (S : Finset ℝ) (hS : ∀ σ ∈ S, regSol (sqC (2 * π * x)) σ a = 0) {Q : ℝ[X]} (hQ : Q.degree < S.card)
    (hQz : ∀ b, b ≠ j → Q.eval (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x b) = 0) :
    (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x j a * (Q.eval (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j) / ∏ σ ∈ S, (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x j - σ))) ^ 2 /
        ∑ σ ∈ S, (resid S id Q σ / dirG (2 * π * x) a σ) ^ 2
      ≤ Cvs.Upstream.CellFloorSandwichPosDef.sigmaP (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x) j :=
  sq_div_sum_le_sigmaP (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellVec x) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_posDef hx) j (dirVec (2 * π * x) a) S
    (fun σ hσ σ' hσ' => inner_dirVec ha ha1 (hS σ hσ) (hS σ' hσ')) (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.chi x) (fun b => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellFun x b a)
    (dirG (2 * π * x) a) (fun σ hσ => dirG_ne_zero (by linarith) ha1 (hS σ hσ))
    (fun b σ hσ => pair_dirVec_cellVec hx ha ha1.le (hS σ hσ) b) hQ hQz

end Cvs.Prolate.Gram.DirichletDualFloorShifted

end
