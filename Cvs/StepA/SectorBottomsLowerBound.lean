import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.OddSectorZeroSide
import Cvs.Finite.TruncationZeroFreeOffAxes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window matrix on each parity sector is at least the zeros' sector bottoms
For a symmetric injective mode set, `∫₀^L cosPoly² = (L/2)(xi⬝xi + xi⬝(xi∘neg))` and
`∫₀^L sinePoly² = (L/2)(o⬝o − o⬝(o∘neg))`, so `L‖xi‖²` on either sector. Hence for every `L > 0` at which
`m_ρ lamE(L, z_ρ)` (resp. `m_ρ lamO`) is summable, in particular whenever finitely many zeros lie off
the line: for even `xi`, `‖xi‖² ∑_ρ m_ρ lamE(L, z_ρ) ≤ xiᵀ M_L xi`, so `evLam ≥ ∑_ρ m_ρ lamE(L, z_ρ)`;
for odd `o`, `‖o‖² ∑_ρ m_ρ lamO(L, z_ρ) ≤ oᵀ M_L o`.
-/

noncomputable section

open Real MeasureTheory Matrix Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.StepA.SectorBottomsLowerBound
open Cvs.ZeroCounting

open Cvs.Finite.TruncationZeroFreeOffAxes (omega)

/-! ### The energy of the window cosine and sine polynomials -/

section Energy

variable {ι : Type*} [Fintype ι]

/-- A lattice cosine integrates over `[0, L]` to `L` when flat and to `0` otherwise. -/
theorem integral_cos_lattice {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    ∫ s in (0 : ℝ)..L, cos (2 * π * k / L * s) = if k = 0 then L else 0 := by
  split_ifs with hk
  · simp [hk]
  · have hc : 2 * π * (k : ℝ) / L ≠ 0 :=
      div_ne_zero (mul_ne_zero (by positivity) (Int.cast_ne_zero.mpr hk)) hL
    have hkL : 2 * π * (k : ℝ) / L * L = ((2 * k : ℤ) : ℝ) * π := by
      push_cast; field_simp
    rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) hc, integral_cos, mul_zero,
      Real.sin_zero, sub_zero, hkL, Real.sin_int_mul_pi, smul_zero]

omit [Fintype ι] in
/-- The difference and sum frequencies of two window modes are lattice frequencies. -/
theorem omega_sub_add (L : ℝ) (mode : ι → ℤ) (i j : ι) (s : ℝ) :
    omega L mode i * s - omega L mode j * s = 2 * π * ((mode i - mode j : ℤ) : ℝ) / L * s ∧
      omega L mode i * s + omega L mode j * s = 2 * π * ((mode i + mode j : ℤ) : ℝ) / L * s := by
  unfold omega
  push_cast
  constructor <;> ring

omit [Fintype ι] in
/-- For a symmetric injective mode set, the difference mode vanishes exactly on the diagonal and the
sum mode exactly on the mirror pairs. -/
theorem mode_sub_add_eq_zero {mode : ι → ℤ} (hinj : Function.Injective mode) {neg : ι → ι}
    (hmode : ∀ i, mode (neg i) = -mode i) (i j : ι) :
    (mode i - mode j = 0 ↔ j = i) ∧ (mode i + mode j = 0 ↔ j = neg i) := by
  refine ⟨⟨fun h => (hinj (by linarith)).symm, fun h => by rw [h]; ring⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have : mode j = mode (neg i) := by rw [hmode]; linarith
    exact hinj this
  · rw [h, hmode]; ring

omit [Fintype ι] in
/-- **Two window cosines are orthogonal on `[0, L]`** unless their indices agree or are mirror images. -/
theorem integral_cos_mul_cos [DecidableEq ι] {L : ℝ} (hL : L ≠ 0) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hmode : ∀ i, mode (neg i) = -mode i) (i j : ι) :
    ∫ s in (0 : ℝ)..L, cos (omega L mode i * s) * cos (omega L mode j * s)
      = L / 2 * ((if j = i then 1 else 0) + (if j = neg i then 1 else 0)) := by
  have e : ∀ s, cos (omega L mode i * s) * cos (omega L mode j * s)
      = (cos (2 * π * ((mode i - mode j : ℤ) : ℝ) / L * s)
          + cos (2 * π * ((mode i + mode j : ℤ) : ℝ) / L * s)) / 2 := by
    intro s
    obtain ⟨h1, h2⟩ := omega_sub_add L mode i j s
    rw [← h1, ← h2, Real.cos_sub, Real.cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun s =>
      cos (2 * π * ((mode i - mode j : ℤ) : ℝ) / L * s)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s =>
      cos (2 * π * ((mode i + mode j : ℤ) : ℝ) / L * s)).intervalIntegrable _ _),
    integral_cos_lattice hL, integral_cos_lattice hL]
  obtain ⟨hsub, hadd⟩ := mode_sub_add_eq_zero hinj hmode i j
  simp only [hsub, hadd]
  split_ifs <;> ring

omit [Fintype ι] in
/-- **Two window sines are orthogonal on `[0, L]`** unless their indices agree or are mirror images. -/
theorem integral_sin_mul_sin [DecidableEq ι] {L : ℝ} (hL : L ≠ 0) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι} (hmode : ∀ i, mode (neg i) = -mode i) (i j : ι) :
    ∫ s in (0 : ℝ)..L, sin (omega L mode i * s) * sin (omega L mode j * s)
      = L / 2 * ((if j = i then 1 else 0) - (if j = neg i then 1 else 0)) := by
  have e : ∀ s, sin (omega L mode i * s) * sin (omega L mode j * s)
      = (cos (2 * π * ((mode i - mode j : ℤ) : ℝ) / L * s)
          - cos (2 * π * ((mode i + mode j : ℤ) : ℝ) / L * s)) / 2 := by
    intro s
    obtain ⟨h1, h2⟩ := omega_sub_add L mode i j s
    rw [← h1, ← h2, Real.cos_sub, Real.cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun s =>
      cos (2 * π * ((mode i - mode j : ℤ) : ℝ) / L * s)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s =>
      cos (2 * π * ((mode i + mode j : ℤ) : ℝ) / L * s)).intervalIntegrable _ _),
    integral_cos_lattice hL, integral_cos_lattice hL]
  obtain ⟨hsub, hadd⟩ := mode_sub_add_eq_zero hinj hmode i j
  simp only [hsub, hadd]
  split_ifs <;> ring

/-- **The energy of a window cosine polynomial**:
`∫₀^L cosPoly² = (L/2)(xi ⬝ xi + xi ⬝ (xi ∘ neg))`. -/
theorem integral_cosPoly_sq {L : ℝ} (hL : L ≠ 0) {mode : ι → ℤ} (hinj : Function.Injective mode)
    {neg : ι → ι} (hmode : ∀ i, mode (neg i) = -mode i) (xi : ι → ℝ) :
    ∫ s in (0 : ℝ)..L, Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi s ^ 2
      = L / 2 * (xi ⬝ᵥ xi + xi ⬝ᵥ fun i => xi (neg i)) := by
  classical
  have hpt : ∀ s, Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi s ^ 2
      = ∑ i, ∑ j, xi i * xi j * (cos (omega L mode i * s) * cos (omega L mode j * s)) := by
    intro s
    unfold Cvs.Finite.EvenSectorZeroSide.cosPoly
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun i _ => (by fun_prop : Continuous fun s =>
    ∑ j, xi i * xi j * (cos (omega L mode i * s) * cos (omega L mode j * s))).intervalIntegrable _ _]
  have hrow : ∀ i, ∫ s in (0 : ℝ)..L,
      ∑ j, xi i * xi j * (cos (omega L mode i * s) * cos (omega L mode j * s))
        = L / 2 * (xi i * xi i + xi i * xi (neg i)) := by
    intro i
    rw [intervalIntegral.integral_finsetSum fun j _ => (by fun_prop : Continuous fun s =>
      xi i * xi j * (cos (omega L mode i * s) * cos (omega L mode j * s))).intervalIntegrable _ _]
    simp_rw [intervalIntegral.integral_const_mul, integral_cos_mul_cos hL hinj hmode i]
    simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  simp_rw [hrow]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  rfl

/-- **The energy of a window sine polynomial**:
`∫₀^L sinePoly² = (L/2)(o ⬝ o − o ⬝ (o ∘ neg))`. -/
theorem integral_sinePoly_sq {L : ℝ} (hL : L ≠ 0) {mode : ι → ℤ} (hinj : Function.Injective mode)
    {neg : ι → ι} (hmode : ∀ i, mode (neg i) = -mode i) (o : ι → ℝ) :
    ∫ s in (0 : ℝ)..L, Cvs.Finite.OddSectorZeroSide.sinePoly L mode o s ^ 2
      = L / 2 * (o ⬝ᵥ o - o ⬝ᵥ fun i => o (neg i)) := by
  classical
  have hpt : ∀ s, Cvs.Finite.OddSectorZeroSide.sinePoly L mode o s ^ 2
      = ∑ i, ∑ j, o i * o j * (sin (omega L mode i * s) * sin (omega L mode j * s)) := by
    intro s
    unfold Cvs.Finite.OddSectorZeroSide.sinePoly
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun i _ => (by fun_prop : Continuous fun s =>
    ∑ j, o i * o j * (sin (omega L mode i * s) * sin (omega L mode j * s))).intervalIntegrable _ _]
  have hrow : ∀ i, ∫ s in (0 : ℝ)..L,
      ∑ j, o i * o j * (sin (omega L mode i * s) * sin (omega L mode j * s))
        = L / 2 * (o i * o i - o i * o (neg i)) := by
    intro i
    rw [intervalIntegral.integral_finsetSum fun j _ => (by fun_prop : Continuous fun s =>
      o i * o j * (sin (omega L mode i * s) * sin (omega L mode j * s))).intervalIntegrable _ _]
    simp_rw [intervalIntegral.integral_const_mul, integral_sin_mul_sin hL hinj hmode i]
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  simp_rw [hrow]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rfl

/-- **Even sector energy on the centred window**: for even `xi`,
`∫_{−L/2}^{L/2} cosPoly(t + L/2)² dt = L ‖xi‖²`. -/
theorem integral_cosPoly_centred_sq {L : ℝ} (hL : L ≠ 0) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι}
    (hmode : ∀ i, mode (neg i) = -mode i) {xi : ι → ℝ} (hxieven : ∀ i, xi (neg i) = xi i) :
    ∫ t in -(L / 2)..L / 2, Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi (t + L / 2) ^ 2
      = L * (xi ⬝ᵥ xi) := by
  rw [intervalIntegral.integral_comp_add_right
      (fun s => Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi s ^ 2),
    show -(L / 2) + L / 2 = 0 by ring, show L / 2 + L / 2 = L by ring,
    integral_cosPoly_sq hL hinj hmode, show (fun i => xi (neg i)) = xi from funext hxieven]
  ring

/-- **Odd sector energy on the centred window**: for odd `o`,
`∫_{−L/2}^{L/2} sinePoly(t + L/2)² dt = L ‖o‖²`. -/
theorem integral_sinePoly_centred_sq {L : ℝ} (hL : L ≠ 0) {mode : ι → ℤ}
    (hinj : Function.Injective mode) {neg : ι → ι}
    (hmode : ∀ i, mode (neg i) = -mode i) {o : ι → ℝ} (hodd : ∀ i, o (neg i) = -o i) :
    ∫ t in -(L / 2)..L / 2, Cvs.Finite.OddSectorZeroSide.sinePoly L mode o (t + L / 2) ^ 2
      = L * (o ⬝ᵥ o) := by
  rw [intervalIntegral.integral_comp_add_right
      (fun s => Cvs.Finite.OddSectorZeroSide.sinePoly L mode o s ^ 2),
    show -(L / 2) + L / 2 = 0 by ring, show L / 2 + L / 2 = L by ring,
    integral_sinePoly_sq hL hinj hmode, show (fun i => o (neg i)) = -o from funext hodd,
    dotProduct_neg]
  ring

end Energy

/-! ### Zeros on the line have bottom `0` -/

variable {ι : Type*} [Fintype ι]

/-! ### The even sector -/

/-! ### The odd sector -/

end Cvs.StepA.SectorBottomsLowerBound
