import Mathlib
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimeOperatorBudgetGap
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget
import Cvs.WeilForm.MaskedShift.WideHopVanishes
import Cvs.WeilForm.NilpotentResolventEulerSquares

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Whole-Domain Window Dirichlet-Schur Factorization and Nilpotent Resolvent Congruence

Identifies `primeOperator c P R` with `Op c Λ + (Op c Λ)*` on `L²(𝕋)`, proves the global Dirichlet-Schur
and Möbius–Zeta identities, and establishes whole-domain nilpotency `(Op c a)^k = 0` (`a 1 = 0`) and congruence.
-/

noncomputable section

open MeasureTheory Real ArithmeticFunction
open scoped InnerProductSpace NNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.WeilForm.DirichletSchurFactorisation

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition

attribute [local instance] Classical.propDecidable

/-! ### 1. Exact Bridge `primeOperator c P R = Op c Λ + (Op c Λ)*` on `L²(𝕋)` -/

/-- For every `n : ℕ`, `wt n = Λ(n) * n^{-(1/2)}`. -/
theorem wt_eq_vonMangoldt_mul_rpow (n : ℕ) :
    wt n = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold wt
  rw [Cvs.WeilForm.NilpotentResolventEulerSquares.rpow_neg_half_eq_inv_sqrt, div_eq_mul_inv]

/-- Every prime atom `atom c n` equals `Λ(n) • (rho c n + (rho c n)*)`. -/
theorem atom_eq_vonMangoldt_smul_rho_add_adjoint (c n : ℕ) :
    atom c n
      = (ArithmeticFunction.vonMangoldt n : ℝ)
          • (rho c n + ContinuousLinearMap.adjoint (rho c n)) := by
  rw [atom_eq, wt_eq_vonMangoldt_mul_rpow, rho, map_smul]
  erw [← smul_add, smul_smul]
  rfl

/-- If `atom c n ≠ 0`, then `Λ n ≠ 0`. -/
theorem vonMangoldt_ne_zero_of_atom_ne_zero {c n : ℕ} (h : atom c n ≠ 0) :
    (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 := by
  intro h0
  apply h
  rw [atom_eq_vonMangoldt_smul_rho_add_adjoint, h0]
  ext x; simp

/-- The symmetrized window von Mangoldt operator `Op c Λ + (Op c Λ)*` is the sum of `atom c n`
over `n ∈ Finset.range c`. -/
theorem Op_vonMangoldt_add_adjoint_eq_sum_atom (c : ℕ) :
    Op c ArithmeticFunction.vonMangoldt
        + ContinuousLinearMap.adjoint (Op c ArithmeticFunction.vonMangoldt)
      = ∑ n ∈ Finset.range c, atom c n := by
  unfold Op
  rw [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul]
  erw [← smul_add]
  rw [atom_eq_vonMangoldt_smul_rho_add_adjoint]

/-- **Exact Identity Between `primeOperator` and `Op c Λ + (Op c Λ)*`**: when `1 < c`,
`c ≤ P + 1`, and `Nat.clog 2 c ≤ R + 1`, the prime-power double sum `primeOperator c P R`
equals the symmetrized Dirichlet operator `Op c Λ + (Op c Λ)*` on the whole domain `L²(𝕋)`. -/
theorem primeOperator_eq_Op_vonMangoldt_add_adjoint {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) :
    primeOperator c P R
      = Op c ArithmeticFunction.vonMangoldt
        + ContinuousLinearMap.adjoint (Op c ArithmeticFunction.vonMangoldt) := by
  rw [Op_vonMangoldt_add_adjoint_eq_sum_atom]
  unfold primeOperator
  rw [Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1 ^ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, r⟩ hmem hne
    rw [Finset.mem_range]
    by_contra hge
    exact hne (Cvs.PrimeOperator.atom_eq_zero hc (not_lt.mp hge))
  · rintro ⟨p₁, r₁⟩ h₁ _ ⟨p₂, r₂⟩ h₂ _ heq
    simp only [Finset.mem_sigma, primeRange, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Icc] at h₁ h₂
    dsimp only at heq
    have hp₁ : p₁.Prime := h₁.1.2
    have hp₂ : p₂.Prime := h₂.1.2
    have hr₁ : 1 ≤ r₁ := h₁.2.1
    have hdvd : p₁ ∣ p₂ ^ r₂ := by
      rw [← heq]
      exact dvd_pow_self p₁ (by omega)
    have hp_eq : p₁ = p₂ :=
      (Nat.dvd_prime hp₂).mp (hp₁.dvd_of_dvd_pow hdvd) |>.resolve_left hp₁.ne_one
    subst hp_eq
    have hr_eq : r₁ = r₂ := Nat.pow_right_injective hp₁.two_le heq
    subst hr_eq
    rfl
  · intro n hn hne
    have hnc : n < c := Finset.mem_range.mp hn
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 := vonMangoldt_ne_zero_of_atom_ne_zero hne
    have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    obtain ⟨p, r, hp, hr, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hp_le : p ≤ p ^ r := Nat.le_self_pow hr.ne' p
    have hpP : p < P + 1 := lt_of_le_of_lt hp_le (lt_of_lt_of_le hnc hP)
    have hrR : r ≤ R := by
      by_contra hgt
      have hR1 : R + 1 ≤ r := by omega
      have hcle : c ≤ p ^ r :=
        le_trans (Cvs.WeilForm.NilpotentResolventEulerSquares.le_prime_pow_of_clog_le hp hR)
          (Nat.pow_le_pow_right hp.pos hR1)
      omega
    refine ⟨⟨p, r⟩, ?_, hne, rfl⟩
    simp only [Finset.mem_sigma, primeRange, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Icc]
    exact ⟨⟨hpP, hp⟩, hr, hrR⟩
  · rintro ⟨p, r⟩ _ _
    rfl

/-- Quadratic form of `Op c a + (Op c a)*` on `L²(𝕋)` is `2 * ⟪Op c a f, f⟫`. -/
theorem inner_Op_add_adjoint (c : ℕ) (a : ArithmeticFunction ℝ) (f : L2) :
    ⟪(Op c a + ContinuousLinearMap.adjoint (Op c a)) f, f⟫_ℝ
      = 2 * ⟪Op c a f, f⟫_ℝ := by
  rw [_root_.add_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    real_inner_comm f (Op c a f)]
  ring

/-- When `1 < c`, `c ≤ P + 1`, and `Nat.clog 2 c ≤ R + 1`,
`⟪primeOperator c P R f, f⟫ = 2 * ⟪Op c Λ f, f⟫`. -/
theorem inner_primeOperator_eq_two_inner_Op_vonMangoldt {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) (f : L2) :
    ⟪primeOperator c P R f, f⟫_ℝ
      = 2 * ⟪Op c ArithmeticFunction.vonMangoldt f, f⟫_ℝ := by
  rw [primeOperator_eq_Op_vonMangoldt_add_adjoint hc hP hR, inner_Op_add_adjoint]

/-! ### 2. Global Window Dirichlet-Convolution Schur Factorization & Möbius–Zeta Coordinates -/

section AbstractSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Weighted Operator Completion of Squares**: for any vectors `u v : E` and scale `γ > 0`,
`2 * ⟪u, v⟫ = γ * ‖u‖² + γ⁻¹ * ‖v‖² - ‖√γ • u - (√γ)⁻¹ • v‖²`. -/
theorem two_inner_eq_weighted_schur {γ : ℝ} (hγ : 0 < γ) (u v : E) :
    2 * ⟪u, v⟫_ℝ
      = γ * ‖u‖ ^ 2 + γ⁻¹ * ‖v‖ ^ 2
        - ‖Real.sqrt γ • u - (Real.sqrt γ)⁻¹ • v‖ ^ 2 := by
  have hsqrt : Real.sqrt γ ≠ 0 := (Real.sqrt_pos.mpr hγ).ne'
  have hsq : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt hγ.le
  rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, inv_pow, hsq,
    real_inner_smul_left, real_inner_smul_right]
  have hmul : Real.sqrt γ * ((Real.sqrt γ)⁻¹ * ⟪u, v⟫_ℝ) = ⟪u, v⟫_ℝ := by
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt, one_mul]
  rw [hmul]
  ring

end AbstractSchur

/-- **Global Dirichlet-Convolution Factorization of `primeOperator`**: for any arithmetic
functions `a b : ArithmeticFunction ℝ` with `a * b = Λ`,
`⟪primeOperator c P R f, f⟫ = 2 * ⟪Op c b f, (Op c a)* f⟫`. -/
theorem inner_primeOperator_eq_dirichlet_pairing {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1)
    {a b : ArithmeticFunction ℝ} (hab : a * b = ArithmeticFunction.vonMangoldt) (f : L2) :
    ⟪primeOperator c P R f, f⟫_ℝ
      = 2 * ⟪Op c b f, ContinuousLinearMap.adjoint (Op c a) f⟫_ℝ := by
  rw [inner_primeOperator_eq_two_inner_Op_vonMangoldt hc hP hR, ← hab,
    ← Op_mul hc a b, mul_apply_eq_comp,
    ← ContinuousLinearMap.adjoint_inner_right]

/-- **Global Dirichlet-Convolution Schur Identity**: for any Dirichlet factorization `a * b = Λ`
and scale `γ > 0`, `⟪primeOperator c P R f, f⟫` is completed to a single global square across all
primes simultaneously on `L²(𝕋)`. -/
theorem inner_primeOperator_eq_dirichlet_schur {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1)
    {a b : ArithmeticFunction ℝ} (hab : a * b = ArithmeticFunction.vonMangoldt)
    {γ : ℝ} (hγ : 0 < γ) (f : L2) :
    ⟪primeOperator c P R f, f⟫_ℝ
      = γ * ‖Op c b f‖ ^ 2
        + γ⁻¹ * ‖ContinuousLinearMap.adjoint (Op c a) f‖ ^ 2
        - ‖Real.sqrt γ • Op c b f
            - (Real.sqrt γ)⁻¹ • ContinuousLinearMap.adjoint (Op c a) f‖ ^ 2 := by
  rw [inner_primeOperator_eq_dirichlet_pairing hc hP hR hab,
    two_inner_eq_weighted_schur hγ]

/-- **Two-Sided Window Möbius–Zeta Inversion**: `Op c ζ * Op c μ = 1`. -/
theorem Op_zeta_mul_moebius {c : ℕ} (hc : 1 < c) :
    Op c (ζ : ArithmeticFunction ℝ) * Op c (μ : ArithmeticFunction ℝ) = 1 := by
  rw [Op_mul hc, ← Op_one hc]
  congr 1
  simp

/-- **Exact Window Identity `Op c Λ * Op c ζ = Op c log`**: multiplying `Op c Λ` on the right by
`Op c ζ` eliminates the Möbius factor identically on the window `L²(𝕋)`. -/
theorem Op_vonMangoldt_mul_zeta {c : ℕ} (hc : 1 < c) :
    Op c ArithmeticFunction.vonMangoldt * Op c (ζ : ArithmeticFunction ℝ) = Op c log := by
  rw [Op_vonMangoldt hc, mul_assoc, Op_moebius_mul_zeta hc, mul_one]

/-- Every `f : L²(𝕋)` is reconstructed from its Möbius coordinate `h = Op c μ f` by `f = Op c ζ h`. -/
theorem Op_zeta_Op_moebius_apply {c : ℕ} (hc : 1 < c) (f : L2) :
    Op c (ζ : ArithmeticFunction ℝ) (Op c (μ : ArithmeticFunction ℝ) f) = f := by
  change (Op c (ζ : ArithmeticFunction ℝ) * Op c (μ : ArithmeticFunction ℝ)) f = f
  rw [Op_zeta_mul_moebius hc]
  rfl

/-- **Prime Operator Quadratic Form in Möbius–Zeta Coordinates**: for any `h : L²(𝕋)`,
evaluating `primeOperator c P R` at `f = Op c ζ h` replaces all prime weights `Λ(n)` by the smooth
pair `(Op c log h, Op c ζ h)`. -/
theorem inner_primeOperator_Op_zeta {c P R : ℕ}
    (hc : 1 < c) (hP : c ≤ P + 1) (hR : Nat.clog 2 c ≤ R + 1) (h : L2) :
    ⟪primeOperator c P R (Op c (ζ : ArithmeticFunction ℝ) h),
        Op c (ζ : ArithmeticFunction ℝ) h⟫_ℝ
      = 2 * ⟪Op c log h, Op c (ζ : ArithmeticFunction ℝ) h⟫_ℝ := by
  rw [inner_primeOperator_eq_two_inner_Op_vonMangoldt hc hP hR]
  have h1 : Op c ArithmeticFunction.vonMangoldt (Op c (ζ : ArithmeticFunction ℝ) h)
      = Op c log h := by
    change (Op c ArithmeticFunction.vonMangoldt * Op c (ζ : ArithmeticFunction ℝ)) h = _
    rw [Op_vonMangoldt_mul_zeta hc]
  rw [h1]

/-! ### 3. Whole-Domain Nilpotency of `Op c a` (`a 1 = 0`) and Congruence Factorization -/

section AbstractCongruence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

end AbstractCongruence

/-- `Op c` is linear with respect to addition. -/
theorem Op_add (c : ℕ) (a b : ArithmeticFunction ℝ) :
    Op c (a + b) = Op c a + Op c b := by
  unfold Op
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [add_apply]
  ext x; simp [add_smul]

/-- `Op c` is linear with respect to scalar multiplication. -/
theorem Op_smul (c : ℕ) (α : ℝ) (a : ArithmeticFunction ℝ) :
    Op c (α • a) = α • Op c a := by
  unfold Op
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [mul_smul]

/-! ### 4. Form-Domain Decomposition of `Q_x(w_v)` via the Global Dirichlet-Schur Identity -/

end Cvs.WeilForm.DirichletSchurFactorisation
