/-
The Single-Atom Path Law — Lean 4 formalization, core definitions and
the algebraically exact layer.

Mirrors `paper/numerics/pathlaw_core.py`:
* `capacity`      ↔ `m = ceil(L / y)`
* `chebFactor`    ↔ `2 * cos(pi / (m + 1))`
* `weight`        ↔ `Lambda(q) / sqrt(q)`  (von Mangoldt, from Mathlib)
* `pathLawNorm`   ↔ `pathLawNorm(q, c)`
* `atomEntry`     ↔ `atomEntry(q, c, k, l)` (the entries of `atom_matrix(..., parity="unfolded")`)

Proved here (no `sorry`, standard axioms only):
* the exact Chebyshev algebraic rungs  m = 2, 3, 4, 5  ↦  1, √2, φ, √3;
* `chebFactor m < 2` and the universal stability cap
  `pathLawNorm q c ≤ 2 * Λ(q)/√q`;
* monotonicity of the Chebyshev staircase.

The analytic Path Law itself (operator norm on ℓ²(ℤ)) is proved in
`PathLaw/Model.lean` (over ℂ) and `PathLaw/RealAtom.lean` (over ℝ).
-/
import Mathlib

open Real

namespace Cvs.PathLaw

/-! ## Definitions -/

/-- The capacity integer `m = ⌈L / y⌉` of a lag `y` at window length `L`
(the length of the longest chain). -/
noncomputable def capacity (L y : ℝ) : ℕ := ⌈L / y⌉₊

/-- The Chebyshev factor `2 cos (π / (m + 1))`: the spectral norm of the
path graph `P_m` (largest root of the Chebyshev polynomial `U_m`). -/
noncomputable def chebFactor (m : ℕ) : ℝ := 2 * Real.cos (π / (m + 1 : ℝ))

/-- The arithmetic weight `Λ(q) / √q` of a prime power `q`. -/
noncomputable def weight (q : ℕ) : ℝ := ArithmeticFunction.vonMangoldt q / Real.sqrt q

/-- The Single-Atom Path Law norm
`‖ΔO_q‖ = 2 cos(π / (⌈L / log q⌉ + 1)) · Λ(q)/√q` at cutoff `c`. -/
noncomputable def pathLawNorm (q c : ℕ) : ℝ :=
  chebFactor (capacity (Real.log c) (Real.log q)) * weight q

/-! ## The exact Chebyshev algebraic rungs -/

theorem chebFactor_two : chebFactor 2 = 1 := by
  have h3 : ((2 : ℕ) + 1 : ℝ) = 3 := by norm_num
  rw [chebFactor, h3, Real.cos_pi_div_three]
  norm_num

theorem chebFactor_three : chebFactor 3 = Real.sqrt 2 := by
  have h4 : ((3 : ℕ) + 1 : ℝ) = 4 := by norm_num
  rw [chebFactor, h4, Real.cos_pi_div_four]
  ring

/-- The golden rung: `2 cos(π/5)` is Mathlib's golden ratio `φ = (1 + √5)/2`. -/
theorem chebFactor_four : chebFactor 4 = Real.goldenRatio := by
  have h5 : ((4 : ℕ) + 1 : ℝ) = 5 := by norm_num
  rw [chebFactor, h5, Real.cos_pi_div_five]
  show 2 * ((1 + √5) / 4) = (1 + √5) / 2
  ring

theorem chebFactor_five : chebFactor 5 = Real.sqrt 3 := by
  have h6 : ((5 : ℕ) + 1 : ℝ) = 6 := by norm_num
  rw [chebFactor, h6, Real.cos_pi_div_six]
  ring

/-! ## Bounds and monotonicity -/

private lemma pi_div_succ_pos (m : ℕ) : 0 < π / (m + 1 : ℝ) :=
  div_pos Real.pi_pos (by positivity)

private lemma pi_div_succ_le_pi (m : ℕ) : π / (m + 1 : ℝ) ≤ π := by
  apply div_le_self Real.pi_pos.le
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Strict spectral gap below the band edge: `chebFactor m < 2`. -/
theorem chebFactor_lt_two (m : ℕ) : chebFactor m < 2 := by
  have h : Real.cos (π / (m + 1 : ℝ)) < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (pi_div_succ_le_pi m) (pi_div_succ_pos m)
  rw [Real.cos_zero] at h
  unfold chebFactor
  linarith

theorem chebFactor_le_two (m : ℕ) : chebFactor m ≤ 2 := (chebFactor_lt_two m).le

theorem weight_nonneg (q : ℕ) : 0 ≤ weight q :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- **Universal stability cap** (Weyl budget): adding the prime atom `q`
shifts the spectrum of the truncated Weil matrix by at most `2 Λ(q)/√q`,
independently of the truncation dimension. -/
theorem pathLawNorm_le_cap (q c : ℕ) : pathLawNorm q c ≤ 2 * weight q := by
  rw [pathLawNorm, two_mul]
  have h := mul_le_mul_of_nonneg_right
    (chebFactor_le_two (capacity (Real.log c) (Real.log q))) (weight_nonneg q)
  linarith [h]

theorem pathLawNorm_nonneg (q c : ℕ) (hm : 1 ≤ capacity (Real.log c) (Real.log q)) :
    0 ≤ pathLawNorm q c := by
  refine mul_nonneg ?_ (weight_nonneg q)
  unfold chebFactor
  have h2 : (2 : ℝ) ≤ (capacity (Real.log c) (Real.log q) : ℝ) + 1 := by
    have := (Nat.one_le_cast (α := ℝ)).mpr hm
    linarith
  have hle : π / ((capacity (Real.log c) (Real.log q) : ℝ) + 1) ≤ π / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h2
  have hnn : 0 ≤ π / ((capacity (Real.log c) (Real.log q) : ℝ) + 1) :=
    (pi_div_succ_pos _).le
  have := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos.le, hnn], hle⟩
  linarith

/-- The Chebyshev staircase climbs: longer chains have larger norms. -/
theorem chebFactor_monotone : Monotone chebFactor := by
  intro a b hab
  unfold chebFactor
  have hcast : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hab
    linarith
  have hdiv : π / (b + 1 : ℝ) ≤ π / (a + 1 : ℝ) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hcast
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (pi_div_succ_pos b).le
    (pi_div_succ_le_pi a) hdiv
  linarith

end Cvs.PathLaw
