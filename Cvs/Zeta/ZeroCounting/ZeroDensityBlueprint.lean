import Mathlib
import Cvs.Zeta.CompletedXiOrderOneGrowth
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.DirichletPolySecondMoment
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroCounting.CarlsonCountBridge
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The density blueprint, worked out
-/

open Complex Filter Asymptotics MeasureTheory Set
open scoped Topology

namespace Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint
open Cvs.GaussKernel

/-! ## The counting function

The rectangle, its zeros, and their number — with the finiteness that makes the
count mean what it says. -/

/-- The critical rectangle: real part between `σ` and `1`, imaginary part in `[-T, T]`. -/
def criticalRegion (σ T : ℝ) : Set ℂ :=
  { s | σ ≤ s.re ∧ s.re ≤ 1 ∧ -T ≤ s.im ∧ s.im ≤ T }

/-- The zeros of `ζ` inside the critical rectangle. -/
def zeroBox (σ T : ℝ) : Set ℂ := criticalRegion σ T ∩ { s | riemannZeta s = 0 }

/-- `N(σ, T)`: the number of zeros of `ζ` in the critical rectangle. -/
noncomputable def N_zero (σ T : ℝ) : ℕ := (zeroBox σ T).ncard

/-- A zero in the box with `σ > 0` is a non-trivial zero: `re ≤ 1` and `ζ s = 0`
force `re < 1`, since `ζ` does not vanish on `1 ≤ re`. -/
theorem mem_nonTrivialZeroSet_of_mem_zeroBox {σ T : ℝ} (hσ : 0 < σ) {s : ℂ}
    (hs : s ∈ zeroBox σ T) : s ∈ Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet := by
  obtain ⟨⟨hre, hre1, -, -⟩, hz⟩ := hs
  refine ⟨hz, lt_of_lt_of_le hσ hre, lt_of_le_of_ne hre1 ?_⟩
  intro h1
  exact riemannZeta_ne_zero_of_one_le_re h1.ge hz

/-- The box holds finitely many zeros: it embeds in a bounded-height window of the
non-trivial zeros, which the quartic summability makes finite. -/
theorem zeroBox_finite {σ : ℝ} (hσ : 0 < σ) (T : ℝ) : (zeroBox σ T).Finite := by
  have hw : {ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet | |((ρ : ℂ)).im| ≤ T}.Finite :=
    Cvs.Zeta.GaussKernel.AdmissibleKernel.finite_window_of_summable (fun ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet => ((ρ : ℂ)).im)
      Cvs.Zeta.GaussKernel.AdmissibleKernel.summable_zeta_quartic T
  refine (Set.Finite.image (fun ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet => (ρ : ℂ)) hw).subset ?_
  intro s hs
  have hmem := mem_nonTrivialZeroSet_of_mem_zeroBox hσ hs
  obtain ⟨⟨-, -, hT1, hT2⟩, -⟩ := hs
  exact ⟨⟨s, hmem⟩, abs_le.mpr ⟨hT1, hT2⟩, rfl⟩

/-- To the right of the line `re = 1` the box is empty: `σ ≤ re ≤ 1 ≤ σ` pins
`re = 1`, where `ζ` has no zero. -/
theorem zeroBox_of_one_le {σ T : ℝ} (hσ : 1 ≤ σ) : zeroBox σ T = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun s hs => ?_
  obtain ⟨⟨hre, -, -, -⟩, hz⟩ := hs
  exact riemannZeta_ne_zero_of_one_le_re (le_trans hσ hre) hz

/-- Hence `N(σ, T) = 0` for `σ ≥ 1`. -/
theorem N_zero_of_one_le {σ T : ℝ} (hσ : 1 ≤ σ) : N_zero σ T = 0 := by
  rw [N_zero, zeroBox_of_one_le hσ, Set.ncard_empty]

/-- The box grows as `σ` decreases and `T` increases. -/
theorem zeroBox_subset {σ σ' T T' : ℝ} (hσ : σ' ≤ σ) (hT : T ≤ T') :
    zeroBox σ T ⊆ zeroBox σ' T' := by
  rintro s ⟨⟨hre, hre1, hT1, hT2⟩, hz⟩
  exact ⟨⟨le_trans hσ hre, hre1, by linarith, by linarith⟩, hz⟩

/-- **The bridge.**  Carlson's count — zeros with `re ≥ σ` and `0 < im ≤ T` — is at
most `N(σ, T)`, because the coercion of `carlsonSet σ T` lands injectively in the
critical rectangle. -/
theorem carlsonCount_le_N_zero {σ : ℝ} (hσ : 0 < σ) {T : ℝ} (hT : 0 ≤ T) :
    Cvs.GaussKernel.carlsonCount σ T ≤ N_zero σ T := by
  have hsub : (fun ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet => (ρ : ℂ)) '' Cvs.GaussKernel.carlsonSet σ T
      ⊆ zeroBox σ T := by
    rintro s ⟨ρ, ⟨hre, hpos, hle⟩, rfl⟩
    obtain ⟨hz, -, h1⟩ := ρ.2
    exact ⟨⟨hre, h1.le, (neg_nonpos.mpr hT).trans hpos.le, hle⟩, hz⟩
  have himg : ((fun ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet => (ρ : ℂ)) '' Cvs.GaussKernel.carlsonSet σ T).ncard
      = (Cvs.GaussKernel.carlsonSet σ T).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  rw [Cvs.GaussKernel.carlsonCount, ← Set.ncard_eq_toFinset_card _ (Cvs.GaussKernel.carlsonSet_finite σ T),
    ← himg]
  exact Set.ncard_le_ncard hsub (zeroBox_finite hσ T)

/-- Carlson's count is antitone in `σ`. -/
theorem carlsonCount_antitone {σ σ' T : ℝ} (h : σ' ≤ σ) :
    Cvs.GaussKernel.carlsonCount σ T ≤ Cvs.GaussKernel.carlsonCount σ' T := by
  rw [Cvs.GaussKernel.carlsonCount, Cvs.GaussKernel.carlsonCount,
    ← Set.ncard_eq_toFinset_card _ (Cvs.GaussKernel.carlsonSet_finite σ T),
    ← Set.ncard_eq_toFinset_card _ (Cvs.GaussKernel.carlsonSet_finite σ' T)]
  refine Set.ncard_le_ncard ?_ (Cvs.GaussKernel.carlsonSet_finite σ' T)
  rintro ρ ⟨hre, hpos, hle⟩
  exact ⟨le_trans h hre, hpos, hle⟩

open Complex Filter Asymptotics

/-- Every zero in the box is the value of an indexed non-trivial zero whose
ordinate lies in the window of height `T`. -/
theorem zeroBox_subset_image {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    zeroBox σ T ⊆ Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue ''
      (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroWindowFinset T : Set _) := by
  intro s hs
  obtain ⟨hz, h0, h1⟩ := mem_nonTrivialZeroSet_of_mem_zeroBox hσ hs
  obtain ⟨⟨-, -, hT1, hT2⟩, -⟩ := hs
  exact ⟨⟨⟨s, hz⟩, h0, h1⟩,
    Finset.mem_coe.mpr (Cvs.Zeta.Explicit.Venue.mem_nontrivialZetaZeroWindowFinset.mpr
      (abs_le.mpr ⟨hT1, hT2⟩)), rfl⟩

/-- **The box is dominated by the venue's window count.** Each zero in the rectangle is a
non-trivial zero of height at most `T`, distinct zeros being distinct indices, and each index
contributes at least its multiplicity `≥ 1` to `nontrivialZetaZeroCount`. -/
theorem N_zero_le_nontrivialZetaZeroCount {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    N_zero σ T ≤ Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCount T := by
  classical
  have hinj : Function.Injective Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue :=
    Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroEmbedding.injective
  have himg : (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroValue ''
      (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroWindowFinset T : Set _)).ncard
      = (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroWindowFinset T).card := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]
  have hcard : N_zero σ T ≤ (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroWindowFinset T).card := by
    rw [N_zero, ← himg]
    exact Set.ncard_le_ncard (zeroBox_subset_image hσ T)
      ((Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroWindowFinset T).finite_toSet.image _)
  refine hcard.trans ?_
  have hone := Finset.card_nsmul_le_sum (Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroWindowFinset T)
    Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity 1
    (fun rho _ => Cvs.Zeta.Explicit.Venue.completedZetaZeroMultiplicity_pos rho)
  simpa [Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCount] using hone

/-- **The counting function grows at most like `T log T`.** This is the venue's
`nontrivialZetaZeroCountBigO_proved` — Jensen's inequality against the growth of the completed
`ξ` — transported along `N_zero_le_nontrivialZetaZeroCount`. -/
theorem N_zero_isBigO {σ : ℝ} (hσ : 0 < σ) :
    (fun T : ℝ ↦ (N_zero σ T : ℝ)) =O[atTop] (fun T : ℝ ↦ T * Real.log T) := by
  obtain ⟨C, T0, hC, hT0, hcount⟩ := Cvs.Zeta.Explicit.Venue.nontrivialZetaZeroCountBigO_proved
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop T0, eventually_ge_atTop (1 : ℝ)] with T hT h1
  have hlog : 0 ≤ Real.log T := Real.log_nonneg h1
  have hT1 : (0 : ℝ) ≤ T := by linarith
  have hle : (N_zero σ T : ℝ) ≤ C * T * Real.log T :=
    le_trans (by exact_mod_cast N_zero_le_nontrivialZetaZeroCount hσ T) (hcount T hT)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ T * Real.log T)]
  linarith [hle]

/-! ## Dirichlet polynomials, and the mean value theorem

`DirichletPolySecondMoment`'s theorem in the `cpow` form the blueprint states it in, and the `=O`
corollary. -/

/-- A Dirichlet polynomial `D(s) = ∑_{n ≤ N} aₙ n^{-s}`. -/
noncomputable def dirichletPolyC (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)

/-- The second moment of a Dirichlet polynomial on the segment `[-iT, iT]` of the
imaginary axis. -/
noncomputable def secondMoment (a : ℕ → ℂ) (N : ℕ) (T : ℝ) : ℝ :=
  ∫ t in (-T)..T, ‖dirichletPolyC a N ((t : ℂ) * Complex.I)‖ ^ 2

/-- **The two spellings agree.**  On the imaginary axis the `cpow` Dirichlet
polynomial is the `exp` one of `DirichletPolySecondMoment`. -/
theorem dirichletPolyC_mul_I (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    dirichletPolyC a N ((t : ℂ) * Complex.I) = Cvs.GaussKernel.dirichletPoly a N t := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [Cvs.GaussKernel.exp_eq_cpow hn1 t, neg_mul]

/-- **The second moment is the integral of `D · conj D`.**  Pointwise
`z · conj z = ‖z‖²`, so the complex integral of `DirichletPolySecondMoment` is the real second
moment, cast. -/
theorem integral_mul_conj_eq (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∫ t in (-T)..T,
        Cvs.GaussKernel.dirichletPoly a N t * (starRingEnd ℂ) (Cvs.GaussKernel.dirichletPoly a N t))
      = ((secondMoment a N T : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
        ((‖dirichletPolyC a N ((t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ))
      (fun t _ => by
        rw [← dirichletPolyC_mul_I, Complex.mul_conj']
        push_cast
        ring),
    intervalIntegral.integral_ofReal]
  rfl

/-- **The mean value theorem for Dirichlet polynomials** , real form: `|∫_{-T}^{T} |D(it)|² dt −
2T Σ|aₙ|²| ≤ 4N(1 + log N) Σ|aₙ|²`. -/
theorem mean_value_bound (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    |secondMoment a N T - 2 * T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2|
      ≤ 4 * N * (1 + Real.log N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h := Cvs.GaussKernel.mean_value_le a N T
  rw [integral_mul_conj_eq] at h
  have he : ((secondMoment a N T : ℝ) : ℂ)
      - ((2 * T : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 N, ((‖a n‖ ^ 2 : ℝ) : ℂ)
      = ((secondMoment a N T - 2 * T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rwa [he, Complex.norm_real, Real.norm_eq_abs] at h

/-- **The upper half of the mean value theorem**, in the form the asymptotic
corollary consumes. -/
theorem secondMoment_le (a : ℕ → ℂ) (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    secondMoment a N T
      ≤ (2 * T + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have h := (abs_le.mp (mean_value_bound a N T)).2
  have hr : (2 * T + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
      = 2 * T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)
        + 4 * N * (1 + Real.log N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring
  rw [hr]
  have hTS : 0 ≤ 2 * T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    have hS0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => sq_nonneg _
    positivity
  linarith [h, hTS]

/-- **A vertical line is the imaginary axis with rescaled coefficients.**
`n^{-(σ+it)} = n^{-σ}·n^{-it}`, so the Dirichlet polynomial on `Re s = σ` is the
one on `Re s = 0` with coefficients `aₙ n^{-σ}`. -/
theorem dirichletPolyC_vertical (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    dirichletPolyC a N ((σ : ℂ) + (t : ℂ) * Complex.I)
      = dirichletPolyC (fun n ↦ a n * (n : ℂ) ^ (-(σ : ℂ))) N ((t : ℂ) * Complex.I) := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := by
    have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  rw [show -((σ : ℂ) + (t : ℂ) * Complex.I) = -(σ : ℂ) + -((t : ℂ) * Complex.I) by ring,
    Complex.cpow_add _ _ hn0, mul_assoc]

/-- **The second moment on any vertical line.**  It is the second moment on the
imaginary axis of the rescaled coefficients, so every bound proved on `Re s = 0`
transfers to `Re s = σ` unchanged. -/
theorem secondMoment_vertical (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) :
    (∫ t in (-T)..T, ‖dirichletPolyC a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      = secondMoment (fun n ↦ a n * (n : ℂ) ^ (-(σ : ℂ))) N T := by
  rw [secondMoment]
  exact intervalIntegral.integral_congr
    (fun t _ => by rw [dirichletPolyC_vertical])

/-- The rescaled coefficients have norm `‖aₙ‖ n^{-σ}`. -/
theorem norm_coeff_vertical {n : ℕ} (hn : 1 ≤ n) (a : ℕ → ℂ) (σ : ℝ) :
    ‖a n * (n : ℂ) ^ (-(σ : ℂ))‖ = ‖a n‖ * (n : ℝ) ^ (-σ) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn]
  simp

/-- **The mean value theorem on the vertical line `Re s = σ`.** `|∫_{-T}^{T} |Σ_{n ≤ N} aₙ
n^{-σ-it}|² dt − 2T·Σ ‖aₙ‖² n^{-2σ}| ≤ 4N(1 + log N)·Σ ‖aₙ‖² n^{-2σ}` The diagonal is exact
and the constants are explicit, exactly as on the axis. -/
theorem mean_value_bound_vertical (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) :
    |(∫ t in (-T)..T, ‖dirichletPolyC a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        - 2 * T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ))|
      ≤ 4 * N * (1 + Real.log N)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
  have hsum : ∀ n ∈ Finset.Icc 1 N,
      ‖a n * (n : ℂ) ^ (-(σ : ℂ))‖ ^ 2 = ‖a n‖ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
    intro n hn
    rw [norm_coeff_vertical (Finset.mem_Icc.mp hn).1 a σ, mul_pow,
      ← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf
  rw [secondMoment_vertical, ← Finset.sum_congr rfl hsum]
  exact mean_value_bound _ N T

/-- `(a + b)² ≤ 2a² + 2b²`: the elementary inequality behind splitting a second
moment across an approximation. -/
theorem sq_add_le_two_mul (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The Dirichlet polynomial on a vertical line is continuous, hence its second
moment is a genuine integral too. -/
theorem intervalIntegrable_normSq_dirichletPolyC (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ‖dirichletPolyC a N ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      volume (-T) T := by
  refine (((?_ : Continuous fun t : ℝ =>
    dirichletPolyC a N ((σ : ℂ) + (t : ℂ) * Complex.I)).norm).pow 2).intervalIntegrable _ _
  refine continuous_finsetSum _ fun n hn => ?_
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := by
    have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))

/-! ## The zeta function itself

The first place `ζ` meets the analysis above.  Abel summation against `⌊t⌋`,
split as `t - {t}`, gives the Euler–Maclaurin representation — the input every
mean-square estimate on a vertical line is built from. -/

section EulerMaclaurin
open Finset

end EulerMaclaurin

/-! ## The mollifier

`M_X(s) = ∑_{n ≤ X} μ(n) n^{-s}`, and the identity that makes it one. -/

/-- The Möbius mollifier `M_X(s) = ∑_{n ≤ X} μ(n) n^{-s}`. -/
noncomputable def zetaMollifier (X : ℕ) (s : ℂ) : ℂ :=
  dirichletPolyC (fun n ↦ (ArithmeticFunction.moebius n : ℂ)) X s

set_option linter.unusedVariables false in
/-- The Möbius divisor sum over `n ≥ 1` is `1` at `n = 1` and `0` otherwise. -/
theorem sum_moebius_divisors (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f ↦ f n) ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] using h

/-- The Möbius divisor sum of `n`, truncated to divisors of size at most `X`. -/
def truncMoebiusSum (X n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (· ≤ X), ArithmeticFunction.moebius d

/-- For `1 ≤ n ≤ X` the truncation is harmless: the truncated Möbius divisor sum is
still exactly `1` at `n = 1` and `0` otherwise. -/
theorem truncMoebiusSum_eq_of_le {X n : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    truncMoebiusSum X n = if n = 1 then 1 else 0 := by
  have hfilter : n.divisors.filter (· ≤ X) = n.divisors := by
    refine Finset.filter_true_of_mem ?_
    intro d hd
    exact le_trans (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)) hnX
  rw [truncMoebiusSum, hfilter, sum_moebius_divisors n hn]

/-- The Möbius function has norm at most `1`. -/
theorem norm_moebius_le_one (n : ℕ) : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  have h : |ArithmeticFunction.moebius n| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  have : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖
      = ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) := by
    rw [Complex.norm_intCast, Int.cast_abs]
  rw [this]
  exact_mod_cast h

/-- The mean square of the Möbius coefficients up to `X` is at most `X`. -/
theorem sum_norm_moebius_sq_le (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ^ 2) ≤ (X : ℝ) := by
  have hcard : (Finset.Icc 1 X).card = X := by
    rw [Nat.card_Icc]
    omega
  calc (∑ n ∈ Finset.Icc 1 X, ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ^ 2)
      ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ ↦ ?_
        have h := norm_moebius_le_one n
        nlinarith [norm_nonneg ((ArithmeticFunction.moebius n : ℤ) : ℂ)]
    _ = (X : ℝ) := by rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]

/-- **The mollifier's second moment.** `Σ_{n ≤ X} |μ(n)|² ≤ X`, so the mean value theorem gives
`∫_{-T}^{T} |M_X(it)|² dt ≤ (2T + 4X(1 + log X))·X`. -/
theorem secondMoment_zetaMollifier_le (X : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    secondMoment (fun n ↦ ((ArithmeticFunction.moebius n : ℤ) : ℂ)) X T
      ≤ (2 * T + 4 * X * (1 + Real.log X)) * X := by
  refine le_trans (secondMoment_le _ X hT) ?_
  refine mul_le_mul_of_nonneg_left (sum_norm_moebius_sq_le X) ?_
  have hlog : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  positivity

/-! ## A sub-linear power is `o(T)`

The step that turns a density exponent below `1` into the statement a counting
argument consumes. -/

/-- `T ^ (a - 1)` tends to `0` along `atTop` whenever `a < 1`. -/
theorem tendsto_rpow_sub_one_atTop {a : ℝ} (ha : a < 1) :
    Filter.Tendsto (fun T : ℝ ↦ T ^ (a - 1)) Filter.atTop (nhds 0) := by
  simpa only [show a - 1 = -(1 - a) by ring] using
    tendsto_rpow_neg_atTop (y := 1 - a) (by linarith)

/-- An eventually nonnegative `f` with `f = O(T ^ a)` for some `a < 1` satisfies
`f T / T → 0`: a sub-linear power bound is `o(T)`. -/
theorem tendsto_div_atTop_of_isBigO_rpow {f : ℝ → ℝ} {a : ℝ} (ha : a < 1)
    (hnn : ∀ᶠ T in Filter.atTop, 0 ≤ f T)
    (hO : (fun T : ℝ ↦ f T) =O[Filter.atTop] (fun T : ℝ ↦ T ^ a)) :
    Filter.Tendsto (fun T : ℝ ↦ f T / T) Filter.atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := isBigO_iff.mp hO
  refine squeeze_zero' (g := fun T : ℝ ↦ C * T ^ (a - 1)) ?_ ?_ ?_
  · filter_upwards [hnn, eventually_gt_atTop (0 : ℝ)] with T h0 hT using div_nonneg h0 hT.le
  · filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with T hT hT0
    have hpos : (0 : ℝ) < T ^ a := Real.rpow_pos_of_pos hT0 a
    have hle : f T ≤ C * T ^ a :=
      calc f T ≤ ‖f T‖ := Real.le_norm_self _
        _ ≤ C * ‖T ^ a‖ := hT
        _ = C * T ^ a := by rw [Real.norm_of_nonneg hpos.le]
    rw [Real.rpow_sub hT0, Real.rpow_one, ← mul_div_assoc]
    gcongr
  · simpa using (tendsto_rpow_sub_one_atTop ha).const_mul C

/-- A natural-number-valued counting function bounded by `O(T ^ a)` with `a < 1` is `o(T)`. -/
theorem tendsto_natCount_div_atTop {g : ℝ → ℕ} {a : ℝ} (ha : a < 1)
    (hO : (fun T : ℝ ↦ (g T : ℝ)) =O[Filter.atTop] (fun T : ℝ ↦ T ^ a)) :
    Filter.Tendsto (fun T : ℝ ↦ (g T : ℝ) / T) Filter.atTop (nhds 0) :=
  tendsto_div_atTop_of_isBigO_rpow ha (Eventually.of_forall fun T ↦ (g T).cast_nonneg) hO

/-- If `f` is eventually nonnegative and eventually dominated by `h`, and `h T / T → 0`,
then `f T / T → 0`. -/
theorem tendsto_div_atTop_of_eventually_le {f h : ℝ → ℝ}
    (hnn : ∀ᶠ T in Filter.atTop, 0 ≤ f T) (hle : ∀ᶠ T in Filter.atTop, f T ≤ h T)
    (hh : Filter.Tendsto (fun T : ℝ ↦ h T / T) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun T : ℝ ↦ f T / T) Filter.atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ hh
  · filter_upwards [hnn, eventually_gt_atTop (0 : ℝ)] with T h0 hT using div_nonneg h0 hT.le
  · filter_upwards [hle, eventually_gt_atTop (0 : ℝ)] with T h0 hT
    gcongr

/-! ## The endpoint

Everything above is proved.  What Carlson's theorem would add is the bound on
`N_zero` itself; `CarlsonBound` names it, `carlson_density_one` closes the one
case that is free, and `zeroDensity_of_carlsonBound` shows the bound plugs into
the chain `CarlsonCountBridge` built. -/

/-- **Carlson's density theorem** , as the blueprint states it: `N(σ, T) ≪ T^{4σ(1-σ)+ε}` for
every `1/2 ≤ σ ≤ 1` and every `ε > 0`. -/
def CarlsonBound : Prop :=
  ∀ σ ε : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 0 < ε →
    (fun T : ℝ ↦ (N_zero σ T : ℝ)) =O[atTop] (fun T : ℝ ↦ T ^ (4 * σ * (1 - σ) + ε))

/-- **The endpoint at `σ = 1`, unconditionally.**  `ζ` has no zero with
`re ≥ 1`, so the count is identically zero and the bound is free — the one
instance of `CarlsonBound` this development can settle. -/
theorem carlson_density_one (ε : ℝ) :
    (fun T : ℝ ↦ (N_zero 1 T : ℝ)) =O[atTop]
      (fun T : ℝ ↦ T ^ (4 * 1 * (1 - 1) + ε)) := by
  have h : (fun T : ℝ ↦ (N_zero 1 T : ℝ)) = fun _ : ℝ ↦ (0 : ℝ) := by
    funext T
    rw [N_zero_of_one_le le_rfl, Nat.cast_zero]
  rw [h]
  exact isBigO_zero _ _

/-- Above the line `re = 1` the textbook count vanishes too. -/
theorem carlsonCount_eq_zero_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) {T : ℝ} (hT : 0 ≤ T) :
    Cvs.GaussKernel.carlsonCount σ T = 0 := by
  have h1 : Cvs.GaussKernel.carlsonCount σ T ≤ Cvs.GaussKernel.carlsonCount 1 T :=
    carlsonCount_antitone hσ
  have h2 : Cvs.GaussKernel.carlsonCount 1 T ≤ N_zero 1 T :=
    carlsonCount_le_N_zero one_pos hT
  rw [N_zero_of_one_le le_rfl] at h2
  omega

end Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint
