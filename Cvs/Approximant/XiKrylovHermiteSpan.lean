import Mathlib
import Cvs.Finite.WindowCoefficientIntertwining
import Cvs.Prolate.CcmAlgebraicFormHermite
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Xi.NodeValuesWindowImage

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `Ξ` Krylov space is the point-zero Fourier-selfdual Hermite span; the index `j* = ⌊(c − 9)/8⌋`

`−(θ + ½)²` acts on `pg c Q` as `nl = −aA²` (Cvs.Prolate.CcmAlgebraicFormHermite), so `nl H_{2m} ∈ span{H_{2m−4}, H_{2m}, H_{2m+4}}`. With
`G_Ξ = F_4/16 − 3F_0/4`, `u_j = (−(θ + ½)²)^jG_Ξ = pg (2πx) Q_j`, `deg Q_j = 2j + 2`, leading `(−1)^j`, `Q_j(0) = 0`, and
`span{Q_0, …, Q_d} = {Q ∈ span{H_0, H_4, …, H_{4d+4}} : Q(0) = 0}`. For `j* = ⌊(c − 9)/8⌋`, `c = 2πx`:
`j ≤ j* ⟺ 8j + 9 ≤ c`, `dim R_F − j* = (1 − π/4)x + 1/8 + O(1)`, `j*/dim R_F → π/4`.
-/

noncomputable section

open Real Polynomial Filter Topology Module

namespace Cvs.Approximant.XiKrylovHermiteSpan

open Cvs.Prolate.HermiteTrialResiduals (pg dq bOp herm)
open Cvs.Finite.WindowCoefficientIntertwining (negScal2)

/-! ### The ladder on the trials -/

/-- The polynomial ladder `nl Q = −bOp Q − Q/4`, the action of `−(θ + ½)²` in `X = cw²`. -/
def nl (Q : ℝ[X]) : ℝ[X] := -bOp Q - C (1 / 4) * Q

/-- **`−(θ + ½)²` on the trials**: `negScal2 (pg c Q) = pg c (nl Q)`. -/
theorem negScal2_pg (c : ℝ) (Q : ℝ[X]) : negScal2 (pg c Q) = pg c (nl Q) := by
  funext w
  have h := Cvs.Prolate.CcmAlgebraicFormHermite.thetaTheta_pg c Q w
  simp only [nl, pg, eval_sub, eval_neg, eval_mul, eval_C] at h ⊢
  linarith

/-- `(−(θ + ½)²)^j (pg c Q) = pg c (nl^[j] Q)`. -/
theorem negScal2_iterate_pg (c : ℝ) (Q : ℝ[X]) (j : ℕ) : negScal2^[j] (pg c Q) = pg c (nl^[j] Q) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, negScal2_pg, Function.iterate_succ_apply']

/-- `nl` in monomial form. -/
theorem nl_eq (Q : ℝ[X]) : nl Q = -(X * (X * Q)) + C 4 * (X * (X * derivative Q))
    - C 4 * (X * (X * derivative (derivative Q))) - C 6 * (X * derivative Q) + C 3 * (X * Q) - C (1 / 4) * Q := by
  simp only [nl, bOp, dq, derivative_sub, derivative_mul, derivative_ofNat, zero_mul, zero_add, map_ofNat]
  ring

/-- **The top coefficient of the ladder**: if `deg Q ≤ k`, then `[X^{k+2}] nl Q = −[X^k] Q`. -/
theorem coeff_nl {Q : ℝ[X]} {k : ℕ} (hQ : Q.natDegree ≤ k) : (nl Q).coeff (k + 2) = -Q.coeff k := by
  have z : ∀ n, k < n → Q.coeff n = 0 := fun n hn => coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ hn)
  rw [nl_eq]
  simp only [coeff_sub, coeff_add, coeff_neg, coeff_C_mul, show k + 2 = (k + 1) + 1 from rfl, coeff_X_mul,
    coeff_derivative]
  rw [z (k + 1) (by omega), z (k + 2) (by omega)]
  ring

/-- `deg Q ≤ k` gives `deg (nl Q) ≤ k + 2`. -/
theorem natDegree_nl_le {Q : ℝ[X]} {k : ℕ} (hQ : Q.natDegree ≤ k) : (nl Q).natDegree ≤ k + 2 := by
  have z : ∀ n, k < n → Q.coeff n = 0 := fun n hn => coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ hn)
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rw [nl_eq]
  simp only [coeff_sub, coeff_add, coeff_neg, coeff_C_mul, show n + 2 = (n + 1) + 1 from rfl, coeff_X_mul,
    coeff_derivative, coeff_C_mul]
  rw [z n (by omega), z (n + 1) (by omega), z (n + 1 + 1) (by omega)]
  ring

/-- The `Ξ` profile in `X = cw²`: `G_Ξ = pg (2πx) (X² − 3X)`. -/
def qXi : ℝ[X] := X ^ 2 - C 3 * X

/-- **`G_Ξ` is a level-2 trial**: `Cvs.Xi.NodeValuesWindowImage.GXi x = pg (2πx) (X² − 3X)`. -/
theorem GXi_eq_pg (x : ℝ) : Cvs.Xi.NodeValuesWindowImage.GXi x = pg (2 * π * x) qXi := by
  funext v
  simp only [Cvs.Xi.NodeValuesWindowImage.GXi, pg, qXi, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
  rw [show -(2 * π * x / 2) * v ^ 2 = -(π * x * v ^ 2) by ring]
  ring

/-- The ladder polynomial `Q_j = nl^[j](X² − 3X)`. -/
def qLad (j : ℕ) : ℝ[X] := nl^[j] qXi

/-- **The `Ξ` ladder on the trials**: `(−(θ + ½)²)^j G_Ξ = pg (2πx) Q_j`. -/
theorem negScal2_iterate_GXi (x : ℝ) (j : ℕ) : negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) = pg (2 * π * x) (qLad j) := by
  rw [GXi_eq_pg, negScal2_iterate_pg]; rfl

/-- `deg Q_j ≤ 2j + 2` and `[X^{2j+2}] Q_j = (−1)^j`. -/
theorem qLad_spec (j : ℕ) : (qLad j).natDegree ≤ 2 * j + 2 ∧ (qLad j).coeff (2 * j + 2) = (-1) ^ j := by
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [qLad, Function.iterate_zero, id, qXi]
      exact (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
    · simp [qLad, qXi]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : qLad (j + 1) = nl (qLad j) := Function.iterate_succ_apply' _ _ _
    rw [e, show 2 * (j + 1) + 2 = (2 * j + 2) + 2 by ring]
    exact ⟨natDegree_nl_le h1, by rw [coeff_nl h1, h2, pow_succ]; ring⟩

/-! ### Hermite levels -/

/-- The even Hermite polynomials as a polynomial sequence: `deg H_{2m} = m` in `X = y²`. -/
theorem herm_spec (m : ℕ) : (herm m).natDegree ≤ m ∧ (herm m).coeff m = 4 ^ m := by
  induction m with
  | zero => simp [herm]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have z : ∀ n, m < n → (herm m).coeff n = 0 :=
      fun n hn => coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h1 hn)
    have e : herm (m + 1) = C 4 * (X * herm m) - C 2 * herm m - C 8 * (X * derivative (herm m))
        + C 2 * derivative (herm m) + C 4 * (X * derivative (derivative (herm m))) := by
      rw [Cvs.Prolate.CcmAlgebraicFormHermite.herm_succ_eq, Cvs.Prolate.CcmAlgebraicFormHermite.rais]; simp only [map_ofNat]; ring
    refine ⟨?_, ?_⟩
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      rw [e]
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative]
      rw [z n (by omega), z (n + 1) (by omega), z (n + 1 + 1) (by omega)]
      ring
    · rw [e]
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative]
      rw [h2, z (m + 1) (by omega), z (m + 1 + 1) (by omega), pow_succ]
      ring

/-- `herm` as a `Polynomial.Sequence`. -/
def hermSeq : Polynomial.Sequence ℝ where
  elems' := herm
  degree_eq' m := by
    obtain ⟨h1, h2⟩ := herm_spec m
    have hne : (herm m).coeff m ≠ 0 := by rw [h2]; positivity
    rw [degree_eq_natDegree (fun h => hne (by rw [h, coeff_zero])), natDegree_eq_of_le_of_coeff_ne_zero h1 hne]

/-- **`H_0, …, H_{2m}` span the polynomials of degree `≤ m` in `X = y²`**. -/
theorem span_herm (m : ℕ) : Submodule.span ℝ (herm '' Set.Iic m) = degreeLE ℝ m := by
  have h := hermSeq.span_degreeLE (m := m) fun i _ => by
    rw [isUnit_iff_ne_zero, leadingCoeff_ne_zero]; exact hermSeq.ne_zero i
  exact h

/-- `Q ↦ pg c Q` as a linear map. -/
def pgL (c : ℝ) : ℝ[X] →ₗ[ℝ] (ℝ → ℝ) where
  toFun Q := pg c Q
  map_add' P Q := by funext w; simp only [pg, eval_add, Pi.add_apply]; ring
  map_smul' r Q := by funext w; simp only [pg, eval_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]; ring

/-- The Hermite level space `E_m = span {F_0, F_2, …, F_{2m}}`, `F_{2k} = pg c (herm k)`. -/
def level (c : ℝ) (m : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ ((fun k => pg c (herm k)) '' Set.Iic m)

/-- **The level space is the trials of degree `≤ m`**: `E_m = pg c (degreeLE m)`. -/
theorem level_eq_map (c : ℝ) (m : ℕ) : level c m = (degreeLE ℝ m).map (pgL c) := by
  rw [← span_herm, Submodule.map_span, level, ← Set.image_comp]; rfl

/-- A trial `pg c Q` with `deg Q ≤ m` lies in the level space `E_m`. -/
theorem pg_mem_level (c : ℝ) {Q : ℝ[X]} {m : ℕ} (hQ : Q.natDegree ≤ m) : pg c Q ∈ level c m := by
  rw [level_eq_map]
  exact ⟨Q, mem_degreeLE.2 (natDegree_le_iff_degree_le.1 hQ), rfl⟩

/-- **The `Ξ` ladder sits at level `2j + 2`**: `(−(θ + ½)²)^j G_Ξ ∈ E_{2j+2}` at `c = 2πx`. -/
theorem ladder_mem_level (x : ℝ) (j : ℕ) : negScal2^[j] (Cvs.Xi.NodeValuesWindowImage.GXi x) ∈ level (2 * π * x) (2 * j + 2) := by
  rw [negScal2_iterate_GXi]; exact pg_mem_level _ (qLad_spec j).1

/-! ### The Fourier-selfdual Krylov space -/

/-! ### The exit count -/

/-- The exit index `j* = ⌊(c − 9)/8⌋`, `c = 2πx`. -/
def jstar (x : ℝ) : ℕ := ⌊(2 * π * x - 9) / 8⌋₊

end Cvs.Approximant.XiKrylovHermiteSpan
