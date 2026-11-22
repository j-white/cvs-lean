import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.BandFloorFromRobinQZero
import Cvs.Prolate.Gram.LogWeightDipolePotential
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RobinDualCertificate
import Cvs.Prolate.Gram.RobinNodeLatticeDualFloor
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate
import Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Route.Visibility.WindowChainCellFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Robin weight is a rate ratio times the exponential of a discrete log-potential difference

At a Robin node `σ` through `χ`, `g_χ²/g_σ² = θ'(σ)/θ'(χ)` with `θ' = nodeRate`, so `ρ_σ = (θ'_σ/θ'_χ)(r_σ/r_χ)²`
needs no Prüfer angle. For `Q = ∏_{b ≠ j}(X − χ_b)·∏_{z ∈ Z}(X − z)` (lemQ §1.3, `Q = T·∏_{b≠j}(z − χ_b)`),
`log|r_σ| = L(σ)` with `L(y) = Σ_{b≠j} log|y − χ_b| + Σ_Z log|y − z| − Σ_{l ∈ S, l ≠ y} log|y − l|`, which is
identity (7.2) before any lattice is introduced; Theorem Q₀ then bounds `Σ_S (θ'_σ/θ'_χ)e^{2(L(σ) − L(χ))}`.
-/

noncomputable section

open Real Set Filter Topology Polynomial Finset
open Cvs.Prolate.RegularSolutionEdge (regSol regU regV sqC)
open Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate (nodeMass)
open Cvs.Route.Visibility.WindowChainCellFloors (finOfSF)
open Cvs.Prolate.Gram.RobinDualCertificate (resid robinWeight)
open Cvs.Prolate.Gram.RobinNodeLatticeDualFloor (robinW robinR robinG chi)
open Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement (nodeRate)

namespace Cvs.Prolate.Gram.RobinWeightLogPotential
open Cvs.ZeroCounting

/-! ### The rate ratio -/

/-- At a Robin node through `χ`, `g_χ²/g_σ² = θ'(σ)/θ'(χ)` for `g = robinG`, `θ' = nodeRate`. -/
theorem robinG_sq_div {c χ σ : ℝ} (hc : c ≠ 0) (hσ : robinW c χ σ = 0) :
    robinG c χ χ ^ 2 / robinG c χ σ ^ 2 = nodeRate c σ / nodeRate c χ := by
  obtain ⟨hy, hU⟩ := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.parallel hσ
  have hR := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinR_ne_zero hσ
  have hNσ := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos c σ
  have hNχ := Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos c χ
  have hEχ := Cvs.Prolate.LiouvilleGreen.RobinCellPhaseIncrement.refNorm_pos hc χ
  unfold robinG nodeRate
  rw [Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinR_self, Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate.regV_half, Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate.regV_half, hy, hU, div_pow, div_pow, one_pow,
    Real.sq_sqrt hNσ.le, Real.sq_sqrt hNχ.le]
  rw [Cvs.Prolate.LiouvilleGreen.PruferAngleRobinRate.regV_half] at hEχ
  field_simp
  exact (div_self (by nlinarith [hEχ])).symm

/-! ### The polynomial `T·∏_{b≠j}(X − χ_b)` -/

/-- `Q = ∏_{b ≠ j}(X − χ_b)·∏_{z ∈ Z}(X − z)`. -/
def robinQ (x : ℕ) (j : Fin x) (Z : Multiset ℝ) : ℝ[X] :=
  (∏ b ∈ univ.erase j, (X - C (chi x b))) * (Z.map fun z => X - C z).prod

theorem eval_robinQ (x : ℕ) (j : Fin x) (Z : Multiset ℝ) (y : ℝ) :
    (robinQ x j Z).eval y = (∏ b ∈ univ.erase j, (y - chi x b)) * (Z.map fun z => y - z).prod := by
  unfold robinQ
  rw [eval_mul, eval_prod, eval_multiset_prod, Multiset.map_map]
  simp

theorem natDegree_robinQ (x : ℕ) (j : Fin x) (Z : Multiset ℝ) :
    (robinQ x j Z).natDegree = (x - 1) + Multiset.card Z := by
  unfold robinQ
  rw [natDegree_mul (Monic.ne_zero (monic_prod_of_monic _ _ fun b _ => monic_X_sub_C _))
      (Monic.ne_zero (monic_multiset_prod_of_monic _ _ fun z _ => monic_X_sub_C _)),
    natDegree_prod_of_monic _ _ fun b _ => monic_X_sub_C _,
    natDegree_multiset_prod_of_monic _ fun f hf => by
      obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hf; exact monic_X_sub_C z]
  simp [Finset.card_erase_of_mem (mem_univ j)]

theorem degree_robinQ_lt {x : ℕ} (j : Fin x) (Z : Multiset ℝ) {S : Finset ℝ}
    (h : (x - 1) + Multiset.card Z < S.card) : (robinQ x j Z).degree < S.card := by
  refine (degree_le_natDegree).trans_lt ?_
  rw [natDegree_robinQ]; exact_mod_cast h

theorem eval_robinQ_other {x : ℕ} (j : Fin x) (Z : Multiset ℝ) {b : Fin x} (hb : b ≠ j) :
    (robinQ x j Z).eval (chi x b) = 0 := by
  rw [eval_robinQ, Finset.prod_eq_zero (mem_erase.mpr ⟨hb, mem_univ b⟩) (sub_self _), zero_mul]

theorem eval_robinQ_ne_zero {x : ℕ} (j : Fin x) (Z : Multiset ℝ) {y : ℝ} (hb : ∀ b, b ≠ j → y ≠ chi x b)
    (hZ : y ∉ Z) : (robinQ x j Z).eval y ≠ 0 := by
  rw [eval_robinQ]
  refine mul_ne_zero (prod_ne_zero_iff.mpr fun b hb' => sub_ne_zero.mpr (hb b (ne_of_mem_erase hb'))) ?_
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp h0
  exact hZ (sub_eq_zero.mp hz0 ▸ hz)

/-! ### The discrete log-potential -/

/-- `L(y) = Σ_{b≠j} log|y − χ_b| + Σ_{z ∈ Z} log|y − z| − Σ_{l ∈ S, l ≠ y} log|y − l|`. -/
def logPot (x : ℕ) (j : Fin x) (S : Finset ℝ) (Z : Multiset ℝ) (y : ℝ) : ℝ :=
  ∑ b ∈ univ.erase j, Real.log |y - chi x b| + (Z.map fun z => Real.log |y - z|).sum -
    ∑ l ∈ S.erase y, Real.log |y - l|

/-- `log|r_y| = L(y)` for the residue of `Q/∏_S(z − l)` at `y ∈ S` off the zeros of `Q`. -/
theorem log_abs_resid {x : ℕ} (j : Fin x) (Z : Multiset ℝ) (S : Finset ℝ) {y : ℝ}
    (hQ : (robinQ x j Z).eval y ≠ 0) :
    Real.log |resid S id (robinQ x j Z) y| = logPot x j S Z y := by
  have hP : (∏ b ∈ univ.erase j, (y - chi x b)) ≠ 0 := by
    intro h; apply hQ; rw [eval_robinQ, h, zero_mul]
  have hM : (Z.map fun z => y - z).prod ≠ 0 := by
    intro h; apply hQ; rw [eval_robinQ, h, mul_zero]
  have hW : ∀ l ∈ S.erase y, (y - l) ≠ 0 := fun l hl => sub_ne_zero.mpr (ne_of_mem_erase hl).symm
  have hI : (∏ l ∈ S.erase y, (y - l)⁻¹) ≠ 0 := prod_ne_zero_iff.mpr fun l hl => inv_ne_zero (hW l hl)
  unfold resid Lagrange.nodalWeight logPot
  simp only [id]
  rw [eval_robinQ, abs_mul, abs_mul, Real.log_mul (mul_ne_zero (abs_ne_zero.mpr hP) (abs_ne_zero.mpr hM))
      (abs_ne_zero.mpr hI), Real.log_mul (abs_ne_zero.mpr hP) (abs_ne_zero.mpr hM),
    Cvs.Prolate.Gram.LogWeightDipolePotential.log_abs_multiset_prod _ hM, Multiset.map_map, abs_prod, abs_prod,
    Real.log_prod (fun b hb => abs_ne_zero.mpr (sub_ne_zero.mpr fun h => hP (prod_eq_zero hb (sub_eq_zero.mpr h)))),
    Real.log_prod (fun l hl => abs_ne_zero.mpr (inv_ne_zero (hW l hl)))]
  simp only [Function.comp_def, abs_inv, Real.log_inv, Finset.sum_neg_distrib]
  ring

/-- `r_y² = e^{2L(y)}` off the zeros of `Q`. -/
theorem resid_sq_eq_exp {x : ℕ} (j : Fin x) (Z : Multiset ℝ) (S : Finset ℝ) {y : ℝ}
    (hQ : (robinQ x j Z).eval y ≠ 0) :
    resid S id (robinQ x j Z) y ^ 2 = Real.exp (2 * logPot x j S Z y) := by
  rw [← log_abs_resid j Z S hQ, ← sq_abs, mul_comm, Real.exp_mul, Real.exp_log
    (abs_pos.mpr (Cvs.Prolate.Gram.BandFloorFromRobinQZero.resid_ne_zero S hQ))]
  norm_cast

/-- **Identity (7.2) in potential form**: at a Robin node `σ ∈ S` through `χ ∈ S`, off the zeros of `Q`,
`ρ_σ = (θ'(σ)/θ'(χ))·e^{2(L(σ) − L(χ))}`. -/
theorem robinWeight_eq_exp {x : ℕ} (hx : 0 < x) (j : Fin x) (Z : Multiset ℝ) (S : Finset ℝ) {σ : ℝ}
    (hσ : robinW (2 * π * x) (chi x j) σ = 0) (hQσ : (robinQ x j Z).eval σ ≠ 0)
    (hQχ : (robinQ x j Z).eval (chi x j) ≠ 0) :
    robinWeight S id (robinG (2 * π * x) (chi x j)) (robinQ x j Z) (chi x j) σ =
      nodeRate (2 * π * x) σ / nodeRate (2 * π * x) (chi x j) *
        Real.exp (2 * (logPot x j S Z σ - logPot x j S Z (chi x j))) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hc : (2 * π * x : ℝ) ≠ 0 := by positivity
  have hgσ : robinG (2 * π * x) (chi x j) σ ≠ 0 :=
    div_ne_zero (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.robinR_ne_zero hσ) (Real.sqrt_pos.mpr (Cvs.Prolate.Gram.RobinNodeLatticeDualFloor.nodeMass_pos _ _)).ne'
  have hrχ := Cvs.Prolate.Gram.BandFloorFromRobinQZero.resid_ne_zero S hQχ
  unfold robinWeight
  rw [div_pow, mul_pow, mul_pow, resid_sq_eq_exp j Z S hQσ, resid_sq_eq_exp j Z S hQχ,
    ← robinG_sq_div hc hσ, mul_sub, Real.exp_sub]
  have : robinG (2 * π * x) (chi x j) σ ^ 2 ≠ 0 := pow_ne_zero 2 hgσ
  have : Real.exp (2 * logPot x j S Z (chi x j)) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-! ### Theorem Q₀ in potential form -/

/-- **Theorem Q₀ in potential form**: for every `ε > 0`, eventually every band rung `T_j > ¾` has a finite set `S`
of Robin nodes through `χ_j` containing `χ_j` and no other level, and a multiset `Z` of real zeros off `S` with
`(x − 1) + |Z| < |S|`, such that `Σ_S (θ'(σ)/θ'(χ_j))e^{2(L(σ) − L(χ_j))} ≤ x^ε`. -/
def RobinPotQ0 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, ∀ j : Cvs.Approximant.SpineSubspace.SF x, 3 / 4 < Cvs.Prolate.Gram.TunnellingFloorSumPlunge.tLev x j →
    ∃ (S : Finset ℝ) (Z : Multiset ℝ), (∀ σ ∈ S, robinW (2 * π * x) (chi x (finOfSF j)) σ = 0) ∧
      chi x (finOfSF j) ∈ S ∧ (∀ b, b ≠ finOfSF j → chi x b ∉ S) ∧ (x - 1) + Multiset.card Z < S.card ∧
      (∀ σ ∈ S, σ ∉ Z) ∧
      ∑ σ ∈ S, nodeRate (2 * π * x) σ / nodeRate (2 * π * x) (chi x (finOfSF j)) *
        Real.exp (2 * (logPot x (finOfSF j) S Z σ - logPot x (finOfSF j) S Z (chi x (finOfSF j)))) ≤
        (x : ℝ) ^ ε

/-- `RobinPotQ0` gives `BandFloorFromRobinQZero`'s `RobinQ0`, with `Q = robinQ`. -/
theorem robinQ0_of_pot (h : RobinPotQ0) : Cvs.Prolate.Gram.BandFloorFromRobinQZero.RobinQ0 := by
  intro ε hε
  have hx80 : ∀ᶠ x : ℕ in atTop, (80 : ℝ) ≤ 2 * π * x := by
    have : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    exact this.eventually_ge_atTop 80
  filter_upwards [h ε hε, hx80, eventually_ge_atTop 1] with x hS h80 hx1 j hj
  obtain ⟨S, Z, hnode, hjS, hdisj, hcard, hZ, hsum⟩ := hS j hj
  have hmono := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lev_strictMono h80
  have hlev : ∀ σ ∈ S, ∀ b, b ≠ finOfSF j → σ ≠ chi x b := fun σ hσ b hb h => hdisj b hb (h ▸ hσ)
  have hQS : ∀ σ ∈ S, (robinQ x (finOfSF j) Z).eval σ ≠ 0 := fun σ hσ =>
    eval_robinQ_ne_zero _ Z (hlev σ hσ) (hZ σ hσ)
  refine ⟨S, robinQ x (finOfSF j) Z, hnode, hjS, hdisj, degree_robinQ_lt _ Z hcard,
    fun b hb => eval_robinQ_other _ Z hb, hQS _ hjS, ?_⟩
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun σ hσ => ?_)) hsum
  exact robinWeight_eq_exp hx1 (finOfSF j) Z S (hnode σ hσ) (hQS σ hσ) (hQS _ hjS)

end Cvs.Prolate.Gram.RobinWeightLogPotential

end
