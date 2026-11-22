import Mathlib
import Cvs.Route.OneCellChebyshevInequality
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.DivisorHyperbolaFactorisation
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.WholeDomainUnification

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Real-to-Integer Interpolation of `M - Psihalf` and Smooth Inverse Equations for `partialSumHalf μ`

Proves monotonicity of `Psihalf` and `trivTail` for real-to-integer interpolation (Step B), the floor-division inverse
identities for `partialSumHalf μ`, and the smooth arithmetic projection `w = (Op c b)* vac` (Step C).
-/

noncomputable section

open MeasureTheory Real Set
open scoped InnerProductSpace NNReal ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Cvs.Zeta.PsihalfIntegerInterpolation
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.Finite.WindowMatrixSymbolKernel (bk bk_pos)
open Cvs.Route.OneCellLaplaceTransform (G primeSide)
open Cvs.Route.OneCellChebyshevInequality (Psihalf S0 trivTail M Psihalf_eq summable_exp_div_bk_sq)
open Cvs.WeilForm.WindowVacuumRieszMean (vac inner_vac_Op)
open Cvs.WeilForm.DirichletSchurFactorisation
open Cvs.WeilForm.ShiftedDirichletSchurVacuum
open Cvs.WeilForm.DivisorHyperbolaFactorisation
open Cvs.WeilForm.WholeDomainUnification

attribute [local instance] Classical.propDecidable

/-! ### 1. Step B — Unconditional Real-to-Integer Interpolation of `Psihalf` and `M` -/

/-- The summand of `primeSide L` is finitely supported for every `L : ℝ`, hence `Summable`. -/
theorem summable_primeSide_term (L : ℝ) :
    Summable fun n : ℕ => Λ n / Real.sqrt n * max (L - Real.log n) 0 := by
  refine summable_of_ne_finset_zero (s := Finset.range ⌈Real.exp L⌉₊) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have h1 : Real.exp L ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < n := (Real.exp_pos L).trans_le h1
  have h2 : L ≤ Real.log n := (Real.le_log_iff_exp_le hnpos).2 h1
  rw [max_eq_right (by linarith), mul_zero]

/-- `primeSide` is monotonically increasing on `ℝ`. -/
theorem primeSide_mono {L₁ L₂ : ℝ} (hL : L₁ ≤ L₂) :
    primeSide L₁ ≤ primeSide L₂ := by
  unfold primeSide
  refine (summable_primeSide_term L₁).tsum_le_tsum (fun n => ?_) (summable_primeSide_term L₂)
  have h0 : 0 ≤ Λ n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left (max_le_max_right 0 (by linarith)) h0

/-- `Psihalf` is monotonically increasing on `(0, ∞)`. -/
theorem Psihalf_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Psihalf x ≤ Psihalf y := by
  rw [Psihalf_eq, Psihalf_eq]
  exact primeSide_mono (Real.log_le_log hx hxy)

/-- For any real `0 < x`, `Psihalf x ≤ Psihalf ⌈x⌉₊`. -/
theorem Psihalf_le_Psihalf_ceil {x : ℝ} (hx : 0 < x) :
    Psihalf x ≤ Psihalf (⌈x⌉₊ : ℝ) :=
  Psihalf_mono hx (Nat.le_ceil x)

/-- **Real-to-Integer Interpolation Lower Bound on `M x - Psihalf x`**:
for any real `1 < x`, `M x - Psihalf x ≥ (M ⌈x⌉₊ - Psihalf ⌈x⌉₊) - (M ⌈x⌉₊ - M x)`. -/
theorem M_sub_Psihalf_ge_ceil_sub_interp {x : ℝ} (hx : 1 < x) :
    (M (⌈x⌉₊ : ℝ) - Psihalf (⌈x⌉₊ : ℝ)) - (M (⌈x⌉₊ : ℝ) - M x)
      ≤ M x - Psihalf x := by
  have hpsi := Psihalf_le_Psihalf_ceil (by linarith : 0 < x)
  linarith

/-- Explicit identity for the smooth majorant step `M y - M x`. -/
theorem M_sub_M_eq {x y : ℝ} :
    M y - M x
      = 4 * (Real.sqrt y - Real.sqrt x)
        + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 / 2 * (Real.log y - Real.log x)
        + (trivTail x - trivTail y) := by
  unfold M
  ring

/-- Lipschitz bound on `√y - √x` for `0 < x ≤ y`: `√y - √x ≤ (y - x) / (2 * √x)`. -/
theorem sqrt_sub_sqrt_le_div_two_sqrt {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.sqrt y - Real.sqrt x ≤ (y - x) / (2 * Real.sqrt x) := by
  have hy : 0 ≤ y := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsy : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  rw [le_div_iff₀ (by positivity)]
  have hprod : (Real.sqrt y - Real.sqrt x) * (Real.sqrt y + Real.sqrt x) = y - x := by
    calc (Real.sqrt y - Real.sqrt x) * (Real.sqrt y + Real.sqrt x)
        = Real.sqrt y ^ 2 - Real.sqrt x ^ 2 := by ring
      _ = y - x := by rw [Real.sq_sqrt hy, Real.sq_sqrt hx.le]
  nlinarith

/-- For `1 < x`, `1 < ⌈x⌉₊`. -/
theorem one_lt_ceil_of_one_lt {x : ℝ} (hx : 1 < x) : 1 < ⌈x⌉₊ :=
  Nat.lt_ceil.mpr (by exact_mod_cast hx)

/-! ### 2. Step C — General Convolution Formula and Exact Inverse Equations for `partialSumHalf μ` -/

/-- **General Dirichlet Convolution Formula for `partialSumHalf (a * b) k`**:
`partialSumHalf (a * b) k = ∑_{n=1}^k b(n) n^{-1/2} * partialSumHalf a (k / n)`. -/
theorem partialSumHalf_mul_eq_sum_div (a b : ArithmeticFunction ℝ) (k : ℕ) :
    partialSumHalf (a * b) k
      = ∑ n ∈ Finset.Icc 1 k,
          b n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * partialSumHalf a (k / n) := by
  unfold partialSumHalf
  simp_rw [ArithmeticFunction.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun p => ⟨p.2.2, p.2.1⟩)
    (fun q => ⟨q.2 * q.1, (q.2, q.1)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, m, n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp ⊢
    obtain ⟨⟨hj1, hjk⟩, hmn, hj0⟩ := hp
    subst hmn
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h => by simp [h] at hj0
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h => by simp [h] at hj0
    exact ⟨⟨hn1, le_trans (Nat.le_mul_of_pos_left n hm1) hjk⟩,
      hm1, (Nat.le_div_iff_mul_le hn1).mpr hjk⟩
  · rintro ⟨n, m⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hq ⊢
    obtain ⟨⟨hn1, hnk⟩, hm1, hmk⟩ := hq
    have hmn : m * n ≤ k := (Nat.le_div_iff_mul_le hn1).mp hmk
    exact ⟨⟨by nlinarith, hmn⟩, trivial, by positivity⟩
  · rintro ⟨j, m, n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨_, hmn, _⟩ := hp
    ext <;> simp [hmn]
  · rintro ⟨n, m⟩ _
    rfl
  · rintro ⟨j, m, n⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨_, rfl, _⟩ := hp
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

/-- Commuted convolution formula: `partialSumHalf (a * b) k = ∑_{m=1}^k a(m) m^{-1/2} * partialSumHalf b (k / m)`. -/
theorem partialSumHalf_mul_eq_sum_div_left (a b : ArithmeticFunction ℝ) (k : ℕ) :
    partialSumHalf (a * b) k
      = ∑ m ∈ Finset.Icc 1 k,
          a m * (m : ℝ) ^ (-(1 / 2 : ℝ)) * partialSumHalf b (k / m) := by
  rw [mul_comm, partialSumHalf_mul_eq_sum_div]

/-! ### 3. Step C — Smooth Arithmetic Adjoint Projection `w = (Op c b)* vac` -/

/-- `(Op c ζ)* ((Op c b)* f) = (Op c (b * ζ))* f` on `L²(𝕋)` for `1 < c`. -/
theorem adj_Op_zeta_apply_adj_Op {c : ℕ} (hc : 1 < c)
    (b : ArithmeticFunction ℝ) (f : L2) :
    ContinuousLinearMap.adjoint (Op c (ζ : ArithmeticFunction ℝ))
        (ContinuousLinearMap.adjoint (Op c b) f)
      = ContinuousLinearMap.adjoint (Op c (b * (ζ : ArithmeticFunction ℝ))) f := by
  change (ContinuousLinearMap.adjoint (Op c (ζ : ArithmeticFunction ℝ))
      ∘L ContinuousLinearMap.adjoint (Op c b)) f = _
  rw [← ContinuousLinearMap.adjoint_comp]
  change ContinuousLinearMap.adjoint (Op c b * Op c (ζ : ArithmeticFunction ℝ)) f = _
  rw [← Op_mul hc]

/-- Residual identity `(Op c a)* f - (Op c ζ)* ((Op c b)* f) = (Op c (a - b * ζ))* f` (`1 < c`). -/
theorem adj_Op_sub_adj_Op_zeta_apply_adj_Op {c : ℕ} (hc : 1 < c)
    (a b : ArithmeticFunction ℝ) (f : L2) :
    ContinuousLinearMap.adjoint (Op c a) f
        - ContinuousLinearMap.adjoint (Op c (ζ : ArithmeticFunction ℝ))
            (ContinuousLinearMap.adjoint (Op c b) f)
      = ContinuousLinearMap.adjoint (Op c (a - b * (ζ : ArithmeticFunction ℝ))) f := by
  rw [adj_Op_zeta_apply_adj_Op hc, Op_sub, map_sub, sub_apply]

end Cvs.Zeta.PsihalfIntegerInterpolation
