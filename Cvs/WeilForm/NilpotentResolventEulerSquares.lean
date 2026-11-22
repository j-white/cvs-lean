import Mathlib
import Cvs.WeilForm.MaskedShift.AtomBoundElementary
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedLiftToLine
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimeOperatorBudgetGap
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget
import Cvs.WeilForm.MaskedShift.PrimeSideAtomForm
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Noncommutative Nilpotent Resolvent and Per-Prime Euler Sum-of-Squares on the Window

Proves the noncommutative right-inverse Toeplitz identity `R + R* - 1 = R* (1 - T* T) R` and
instantiates it on Steinhaus chain walks `S β` and nilpotent prime Euler factors `E_p(c, R)`.
-/

noncomputable section

open MeasureTheory Real ArithmeticFunction
open scoped InnerProductSpace NNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.WeilForm.NilpotentResolventEulerSquares

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition

attribute [local instance] Classical.propDecidable

/-! ### 1. Noncommutative Right-Inverse Toeplitz / Herglotz Factorization -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Noncommutative polynomial identity `1 - T* T = (1 - T*) + (1 - T) - (1 - T*)(1 - T)`. -/
theorem one_sub_adjoint_mul_self (T : E →L[ℝ] E) :
    (1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T * T
      = ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T) + ((1 : E →L[ℝ] E) - T)
        - ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T) * ((1 : E →L[ℝ] E) - T) := by
  noncomm_ring

/-- **Noncommutative Right-Inverse Toeplitz Identity**: if `(1 - T) * R = 1`, then without
any commutativity between `T` and `T*`, `R + R* - 1 = R* * (1 - T* * T) * R`. -/
theorem resolvent_toeplitz_identity {T R : E →L[ℝ] E}
    (hR : ((1 : E →L[ℝ] E) - T) * R = 1) :
    R + ContinuousLinearMap.adjoint R - 1
      = ContinuousLinearMap.adjoint R
        * ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T * T) * R := by
  have hmul : ContinuousLinearMap.adjoint (((1 : E →L[ℝ] E) - T) * R)
      = ContinuousLinearMap.adjoint R * ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T) := by
    change ContinuousLinearMap.adjoint (((1 : E →L[ℝ] E) - T) ∘L R) = _
    rw [ContinuousLinearMap.adjoint_comp, map_sub, ContinuousLinearMap.adjoint_one]
    rfl
  have hRstar : ContinuousLinearMap.adjoint R * ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T) = 1 := by
    rw [← hmul, hR, ContinuousLinearMap.adjoint_one]
  calc R + ContinuousLinearMap.adjoint R - 1
      = (ContinuousLinearMap.adjoint R * ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T)) * R
        + ContinuousLinearMap.adjoint R * (((1 : E →L[ℝ] E) - T) * R)
        - (ContinuousLinearMap.adjoint R * ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T))
          * (((1 : E →L[ℝ] E) - T) * R) := by
        rw [hRstar, hR]; noncomm_ring
    _ = ContinuousLinearMap.adjoint R
        * (((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T) + ((1 : E →L[ℝ] E) - T)
          - ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T) * ((1 : E →L[ℝ] E) - T)) * R := by
        noncomm_ring
    _ = ContinuousLinearMap.adjoint R
        * ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T * T) * R := by
        rw [← one_sub_adjoint_mul_self]

/-- Quadratic form of the right-inverse Toeplitz identity:
`⟪(R + R* - 1) f, f⟫ = ‖R f‖² - ‖T (R f)‖²`. -/
theorem inner_resolvent_toeplitz {T R : E →L[ℝ] E}
    (hR : ((1 : E →L[ℝ] E) - T) * R = 1) (f : E) :
    ⟪(R + ContinuousLinearMap.adjoint R - 1) f, f⟫_ℝ
      = ‖R f‖ ^ 2 - ‖T (R f)‖ ^ 2 := by
  rw [resolvent_toeplitz_identity hR]
  change ⟪(ContinuousLinearMap.adjoint R
      ∘L ((1 : E →L[ℝ] E) - ContinuousLinearMap.adjoint T ∘L T) ∘L R) f, f⟫_ℝ
    = ‖R f‖ ^ 2 - ‖T (R f)‖ ^ 2
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, sub_apply,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- Finite geometric series `∑_{k < m} T^k` of a bounded operator. -/
def geomSum (T : E →L[ℝ] E) (m : ℕ) : E →L[ℝ] E :=
  ∑ k ∈ Finset.range m, T ^ k

omit [CompleteSpace E] in
/-- Telescoping identity `(1 - T) * geomSum T m = 1 - T^m`. -/
theorem one_sub_mul_geomSum (T : E →L[ℝ] E) (m : ℕ) :
    ((1 : E →L[ℝ] E) - T) * geomSum T m = 1 - T ^ m := by
  unfold geomSum
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ']
    noncomm_ring

omit [CompleteSpace E] in
/-- For a nilpotent operator with `T^m = 0`, `geomSum T m` is a right inverse of `1 - T`. -/
theorem one_sub_mul_geomSum_eq_one {T : E →L[ℝ] E} {m : ℕ} (hT : T ^ m = 0) :
    ((1 : E →L[ℝ] E) - T) * geomSum T m = 1 := by
  rw [one_sub_mul_geomSum, hT, sub_zero]

/-- Decomposition of `geomSum T (R + 1) + (geomSum T (R + 1))* - 1` into `1` plus the symmetric hops
over `r ∈ Icc 1 R`. -/
theorem geomSum_succ_add_adjoint_sub_one (T : E →L[ℝ] E) (R : ℕ) :
    geomSum T (R + 1) + ContinuousLinearMap.adjoint (geomSum T (R + 1)) - 1
      = 1 + ∑ r ∈ Finset.Icc 1 R, (T ^ r + ContinuousLinearMap.adjoint (T ^ r)) := by
  induction R with
  | zero =>
    unfold geomSum
    simp [ContinuousLinearMap.adjoint_one]
  | succ R ih =>
    have h1 : geomSum T (R + 1 + 1) = geomSum T (R + 1) + T ^ (R + 1) := by
      unfold geomSum
      exact Finset.sum_range_succ _ (R + 1)
    rw [h1, map_add, Finset.sum_Icc_succ_top (by omega : 1 ≤ R + 1), ← add_assoc 1, ← ih]
    abel

/-- **Nilpotent Operator Sum-of-Squares Identity**: if `T^(R + 1) = 0`, then for every `f : E`,
`‖f‖² + ∑_{r=1}^R ⟪(T^r + (T^r)*) f, f⟫ = ‖geomSum T (R + 1) f‖² - ‖T (geomSum T (R + 1) f)‖²`. -/
theorem norm_sq_add_sum_inner_eq_geomSum {T : E →L[ℝ] E} {R : ℕ}
    (hT : T ^ (R + 1) = 0) (f : E) :
    ‖f‖ ^ 2 + ∑ r ∈ Finset.Icc 1 R, ⟪(T ^ r + ContinuousLinearMap.adjoint (T ^ r)) f, f⟫_ℝ
      = ‖geomSum T (R + 1) f‖ ^ 2 - ‖T (geomSum T (R + 1) f)‖ ^ 2 := by
  have h1 := inner_resolvent_toeplitz (one_sub_mul_geomSum_eq_one hT) f
  rw [geomSum_succ_add_adjoint_sub_one, _root_.add_apply,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, inner_add_left,
    real_inner_self_eq_norm_sq, sum_apply, sum_inner] at h1
  exact h1

end Abstract

/-! ### 2. Exact Isometry Defect of a Masked Walk on `L²(𝕋)` -/

/-! ### 3. Per-Prime Nilpotent Euler-Factor Sum-of-Squares on the Window -/

/-- Powers of the multiplicative window representation `rho c n` are `rho c (n^r)`. -/
theorem rho_pow {c n : ℕ} (hc : 1 < c) (hn : 1 ≤ n) (r : ℕ) :
    rho c n ^ r = rho c (n ^ r) := by
  induction r with
  | zero => simp [rho_one]
  | succ r ih =>
    rw [pow_succ, ih, pow_succ, ← rho_mul hc (Nat.one_le_pow r n hn) hn]

/-- For `1 ≤ q`, `q^{-(1/2)} = (√q)⁻¹`. -/
theorem rpow_neg_half_eq_inv_sqrt (q : ℕ) :
    (q : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt q)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg q), ← Real.sqrt_eq_rpow]

/-- Each prime-power atom `atom c (p^r)` (`r ≥ 1`) is `log p` times the symmetric `r`-th power
of the prime's nilpotent walk `rho c p`. -/
theorem atom_prime_pow_eq_log_smul_rho {c p r : ℕ} (hc : 1 < c) (hp : p.Prime) (hr : 1 ≤ r) :
    atom c (p ^ r)
      = Real.log p • (rho c p ^ r + ContinuousLinearMap.adjoint (rho c p ^ r)) := by
  have hwt : wt (p ^ r) = Real.log p * ((p ^ r : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    unfold wt
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, rpow_neg_half_eq_inv_sqrt, div_eq_mul_inv]
  rw [rho_pow hc hp.one_lt.le r, atom_eq, hwt, rho, map_smul, Cvs.Operator.W]
  simp only [smul_add, smul_smul]

/-- The finite Euler factor `(I - rho c p)⁻¹ = ∑_{k=0}^R (rho c p)^k` on the window. -/
def windowEulerFactor (c p R : ℕ) : L2 →L[ℝ] L2 :=
  geomSum (rho c p) (R + 1)

/-- When `c ≤ p^(R + 1)`, `(rho c p)^(R + 1) = 0`. -/
theorem rho_pow_eq_zero_of_le {c p R : ℕ} (hc : 1 < c) (hp : p.Prime)
    (hpow : c ≤ p ^ (R + 1)) :
    rho c p ^ (R + 1) = 0 := by
  rw [rho_pow hc hp.one_lt.le (R + 1)]
  exact rho_eq_zero hc hpow

/-- **Per-Prime Nilpotent Euler-Factor Identity on the Window**: when `c ≤ p^(R + 1)`,
`log p · ‖f‖² + ∑_{r=1}^R ⟪atom c (p^r) f, f⟫ = log p · (‖E_p f‖² - ‖rho c p (E_p f)‖²)`. -/
theorem prime_euler_resolvent_identity {c p R : ℕ} (hc : 1 < c) (hp : p.Prime)
    (hpow : c ≤ p ^ (R + 1)) (f : L2) :
    Real.log p * ‖f‖ ^ 2 + ∑ r ∈ Finset.Icc 1 R, ⟪atom c (p ^ r) f, f⟫_ℝ
      = Real.log p * (‖windowEulerFactor c p R f‖ ^ 2
          - ‖rho c p (windowEulerFactor c p R f)‖ ^ 2) := by
  have hnil := rho_pow_eq_zero_of_le hc hp hpow
  have hgeom := norm_sq_add_sum_inner_eq_geomSum hnil f
  have hsum : ∑ r ∈ Finset.Icc 1 R, ⟪atom c (p ^ r) f, f⟫_ℝ
      = Real.log p * ∑ r ∈ Finset.Icc 1 R,
          ⟪(rho c p ^ r + ContinuousLinearMap.adjoint (rho c p ^ r)) f, f⟫_ℝ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [atom_prime_pow_eq_log_smul_rho hc hp (Finset.mem_Icc.mp hr).1,
      _root_.smul_apply, real_inner_smul_left]
  rw [hsum, windowEulerFactor]
  linear_combination Real.log p * hgeom

/-! ### 4. Summed Prime-Operator Euler Resolvent and Full Window Weil Form Identity -/

/-- Whenever `Nat.clog 2 c ≤ R + 1`, every prime `p` satisfies `c ≤ p^(R + 1)`. -/
theorem le_prime_pow_of_clog_le {c p R : ℕ} (hp : p.Prime) (hR : Nat.clog 2 c ≤ R + 1) :
    c ≤ p ^ (R + 1) :=
  calc c ≤ 2 ^ Nat.clog 2 c := Nat.le_pow_clog one_lt_two c
    _ ≤ 2 ^ (R + 1) := Nat.pow_le_pow_right (by omega) hR
    _ ≤ p ^ (R + 1) := Nat.pow_le_pow_left hp.two_le (R + 1)

/-- The summed per-prime Euler-resolvent quadratic form on the window. -/
def primeEulerResolventForm (c P R : ℕ) (f : L2) : ℝ :=
  ∑ p ∈ primeRange P,
    Real.log p * (‖windowEulerFactor c p R f‖ ^ 2
      - ‖rho c p (windowEulerFactor c p R f)‖ ^ 2)

/-- **Summed Prime-Operator Euler-Resolvent Identity**: when `Nat.clog 2 c ≤ R + 1`,
`(∑_{p ∈ primeRange P} log p) · ‖f‖² + ⟪primeOperator c P R f, f⟫ = primeEulerResolventForm c P R f`. -/
theorem inner_primeOperator_eq_euler_resolvent {c P R : ℕ} (hc : 1 < c)
    (hR : Nat.clog 2 c ≤ R + 1) (f : L2) :
    (∑ p ∈ primeRange P, Real.log p) * ‖f‖ ^ 2 + ⟪primeOperator c P R f, f⟫_ℝ
      = primeEulerResolventForm c P R f := by
  rw [inner_primeOperator, primeEulerResolventForm, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  exact prime_euler_resolvent_identity hc hprime (le_prime_pow_of_clog_le hprime hR) f

/-- `testFn c f 0 = ‖f‖²`. -/
theorem testFn_zero (c : ℕ) (f : L2) : testFn c f 0 = ‖f‖ ^ 2 := by
  unfold testFn
  rw [zero_div, norm_sq_eq_integral_lift_sq]
  unfold Cvs.Zeta.Explicit.Weil.selfConvolution
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [sq]

end Cvs.WeilForm.NilpotentResolventEulerSquares
