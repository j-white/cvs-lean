import Mathlib
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.WindowMatrixSymbolKernel
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prime Schur products are phase energies, and the even-sector sign structure

`sinc` Toeplitz matrices are positive semidefinite, so each prime term of the kernel is a
cosine-phase energy minus a sine-phase energy; on even data the quadratic form of `M` is the
symbol plus archimedean squares plus cosine energies minus sine energies.
-/

namespace Cvs.WeilForm.PrimeSchurPhaseEnergies

open scoped Real
open Cvs.Finite.WindowMatrixSymbolKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sinc quadratic form `Σ ξ_i ξ_j sinc(a(ω_i − ω_j))`. -/
noncomputable def sincQ (a : ℝ) (ω ξ : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ξ i * ξ j * sinc (a * (ω i - ω j))

/-- The cosine-phase energy at lag `t`: `ξᵀ D_c Σ_t D_c ξ`. -/
noncomputable def cosQ (t : ℝ) (ω ξ : ι → ℝ) : ℝ :=
  sincQ (t / 2) ω fun i => ξ i * Real.cos (t * ω i / 2)

/-- The sine-phase energy at lag `t`: `ξᵀ D_s Σ_t D_s ξ`. -/
noncomputable def sinQ (t : ℝ) (ω ξ : ι → ℝ) : ℝ :=
  sincQ (t / 2) ω fun i => ξ i * Real.sin (t * ω i / 2)

/-- **Each prime term of the kernel is `cosQ − sinQ`.** -/
theorem quadForm_lag (t : ℝ) (ω ξ : ι → ℝ) :
    ∑ i, ∑ j, ξ i * ξ j * (t * Real.cos (t * (ω i + ω j) / 2) * sinc (t * (ω i - ω j) / 2))
      = t * (cosQ t ω ξ - sinQ t ω ξ) := by
  unfold cosQ sinQ sincQ
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : t * (ω i + ω j) / 2 = t * ω i / 2 + t * ω j / 2 := by ring
  have e2 : t * (ω i - ω j) / 2 = t / 2 * (ω i - ω j) := by ring
  rw [e1, e2, Real.cos_add]
  ring

theorem sum4_comm {α β γ δ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ) (v : Finset δ)
    (F : α → β → γ → δ → ℝ) :
    ∑ i ∈ s, ∑ j ∈ t, ∑ p ∈ u, ∑ r ∈ v, F i j p r = ∑ p ∈ u, ∑ r ∈ v, ∑ i ∈ s, ∑ j ∈ t, F i j p r := by
  calc ∑ i ∈ s, ∑ j ∈ t, ∑ p ∈ u, ∑ r ∈ v, F i j p r
      = ∑ i ∈ s, ∑ p ∈ u, ∑ j ∈ t, ∑ r ∈ v, F i j p r :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ p ∈ u, ∑ i ∈ s, ∑ j ∈ t, ∑ r ∈ v, F i j p r := Finset.sum_comm
    _ = ∑ p ∈ u, ∑ i ∈ s, ∑ r ∈ v, ∑ j ∈ t, F i j p r :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ p ∈ u, ∑ r ∈ v, ∑ i ∈ s, ∑ j ∈ t, F i j p r :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-- The prime kernel's quadratic form: weighted cosine energies minus sine energies. -/
theorem quadForm_kPrime (P R : ℕ) (L : ℝ) (ω ξ : ι → ℝ) :
    ∑ i, ∑ j, ξ i * ξ j * kPrime P R L (ω i) (ω j)
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
          Cvs.Zeta.Explicit.Weil.primePowerWeight p r
            * (2 * (if (r : ℝ) * Real.log p ≤ L then
                (r : ℝ) * Real.log p * (cosQ ((r : ℝ) * Real.log p) ω ξ - sinQ ((r : ℝ) * Real.log p) ω ξ)
              else 0)) := by
  have key : ∀ i j, ξ i * ξ j * kPrime P R L (ω i) (ω j)
      = ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
          Cvs.Zeta.Explicit.Weil.primePowerWeight p r
            * (2 * (if (r : ℝ) * Real.log p ≤ L then
                ξ i * ξ j * ((r : ℝ) * Real.log p * Real.cos ((r : ℝ) * Real.log p * (ω i + ω j) / 2)
                  * sinc ((r : ℝ) * Real.log p * (ω i - ω j) / 2))
              else 0)) := by
    intro i j
    unfold kPrime
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  simp_rw [key]
  rw [sum4_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  by_cases h : (r : ℝ) * Real.log p ≤ L
  · simp only [if_pos h]
    rw [← quadForm_lag]
    simp only [Finset.mul_sum]
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero]

/-- **The quadratic form of `M`**: symbol, archimedean part, and prime phase energies. -/
theorem quadForm_M {L : ℝ} (hL : 0 < L) (P R : ℕ) {mode : ι → ℤ} (hinj : Function.Injective mode)
    (ξ : ι → ℝ) :
    ∑ i, ∑ j, ξ i * ξ j * Cvs.Finite.TruncationQuadraticForm.M P R L mode i j
      = ∑ i, ξ i ^ 2 * symbolCut P R L (2 * π * mode i / L)
        + 1 / L * ∑ i, ∑ j, ξ i * ξ j * kArch L (2 * π * mode i / L) (2 * π * mode j / L)
        + 1 / L * ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
            Cvs.Zeta.Explicit.Weil.primePowerWeight p r
              * (2 * (if (r : ℝ) * Real.log p ≤ L then
                  (r : ℝ) * Real.log p * (cosQ ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ
                    - sinQ ((r : ℝ) * Real.log p) (fun i => 2 * π * mode i / L) ξ)
                else 0)) := by
  rw [← quadForm_kPrime]
  simp_rw [M_apply_kernel hL P R hinj]
  have hdiag : ∀ i, ∑ j, ξ i * ξ j * ((if i = j then symbolCut P R L (2 * π * mode i / L) else 0)
        + 1 / L * kK P R L (2 * π * mode i / L) (2 * π * mode j / L))
      = ξ i ^ 2 * symbolCut P R L (2 * π * mode i / L)
        + (1 / L * ∑ j, ξ i * ξ j * kArch L (2 * π * mode i / L) (2 * π * mode j / L)
          + 1 / L * ∑ j, ξ i * ξ j * kPrime P R L (2 * π * mode i / L) (2 * π * mode j / L)) := by
    intro i
    have hA : ∑ j, ξ i * ξ j * (if i = j then symbolCut P R L (2 * π * mode i / L) else 0)
        = ξ i ^ 2 * symbolCut P R L (2 * π * mode i / L) := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]; ring
      · intro j _ hji; rw [if_neg (Ne.symm hji)]; ring
      · intro h; exact absurd (Finset.mem_univ i) h
    have hB : ∑ j, ξ i * ξ j * (1 / L * kK P R L (2 * π * mode i / L) (2 * π * mode j / L))
        = 1 / L * ∑ j, ξ i * ξ j * kArch L (2 * π * mode i / L) (2 * π * mode j / L)
          + 1 / L * ∑ j, ξ i * ξ j * kPrime P R L (2 * π * mode i / L) (2 * π * mode j / L) := by
      unfold kK
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [← hA, ← hB, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hdiag, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Cvs.WeilForm.PrimeSchurPhaseEnergies
