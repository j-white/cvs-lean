import Mathlib
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootCoreBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootStep
import Cvs.Prolate.Mellin.NearRegionDamping
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Growth and damping split of the step coefficient on a line

On `s_i = s₀ + 2i` with `Re s_i ≤ 2c`, `‖A(s_i)‖ ≤ exp(g_i − d_i)` with `g_i = 1/((x_i+1)(x_i+4)) + G_i/2 + G_{i+1}/2`
and `d_i = D_i/2 + D_{i+1}/2`; `d_i ≥ √(2c)/(189c)` once `2i ≥ √(2c)`, so the damped products sum to at most
`⌈√(2c)/2⌉ + 189c/√(2c)`.
-/

noncomputable section

open Finset

namespace Cvs.Prolate.Mellin.StepCoefficientSplit

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.ForcingSmallBound Cvs.Prolate.Mellin.StepAmplification Cvs.Prolate.Mellin.NearRegionDamping

/-- **Damped tail**: if `S(j+1) − S(j) ≥ ν > 0` for `j ≥ m`, then `Σ_{m≤j<n} exp(−S(j+1)) ≤ exp(−S m)/ν`. -/
theorem sum_exp_neg_le {S : ℕ → ℝ} {ν : ℝ} (hν : 0 < ν) {m : ℕ} (hS : ∀ j, m ≤ j → ν ≤ S (j + 1) - S j) :
    ∀ n, ∑ j ∈ Ico m n, Real.exp (-S (j + 1)) ≤ Real.exp (-S m) / ν := by
  have key : ∀ n, m ≤ n → ∑ j ∈ Ico m n, Real.exp (-S (j + 1)) ≤ (Real.exp (-S m) - Real.exp (-S n)) / ν := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [Finset.sum_Ico_succ_top hmn]
      have h1 := hS n hmn
      have h2 : (1 + ν) * Real.exp (-S (n + 1)) ≤ Real.exp (-S n) := by
        have : 1 + ν ≤ Real.exp (S (n + 1) - S n) := by
          have := Real.add_one_le_exp ν
          linarith [Real.exp_le_exp.mpr h1]
        calc (1 + ν) * Real.exp (-S (n + 1)) ≤ Real.exp (S (n + 1) - S n) * Real.exp (-S (n + 1)) :=
              mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
          _ = Real.exp (-S n) := by rw [← Real.exp_add]; ring_nf
      have h3 : Real.exp (-S (n + 1)) ≤ (Real.exp (-S n) - Real.exp (-S (n + 1))) / ν := by
        rw [le_div_iff₀ hν]; linarith
      calc _ ≤ (Real.exp (-S m) - Real.exp (-S n)) / ν + (Real.exp (-S n) - Real.exp (-S (n + 1))) / ν :=
            add_le_add ih h3
        _ = _ := by ring
  intro n
  by_cases hn : m ≤ n
  · refine (key n hn).trans ?_
    apply div_le_div_of_nonneg_right _ hν.le
    linarith [Real.exp_pos (-S n)]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; positivity

/-- **The damping sum**: if `d ≥ 0` and `d_i ≥ ν > 0` for `i ≥ N₀`, then
`Σ_{k≤j<J} exp(−Σ_{k≤i≤j} d_i) ≤ N₀ + 1/ν`. -/
theorem sum_damp_le {d : ℕ → ℝ} {ν : ℝ} {N₀ : ℕ} (hν : 0 < ν) (hd0 : ∀ i, 0 ≤ d i)
    (hd : ∀ i, N₀ ≤ i → ν ≤ d i) (k J : ℕ) :
    ∑ j ∈ Ico k J, Real.exp (-∑ i ∈ Ico k (j + 1), d i) ≤ N₀ + 1 / ν := by
  set S := fun j => ∑ i ∈ Ico k j, d i
  set m := max k N₀
  have hle1 : ∀ j, Real.exp (-S (j + 1)) ≤ 1 := fun j => by
    rw [Real.exp_le_one_iff, neg_nonpos]; exact Finset.sum_nonneg fun i _ => hd0 i
  have hhead : ∑ j ∈ Ico k m, Real.exp (-S (j + 1)) ≤ N₀ := by
    calc _ ≤ ∑ j ∈ Ico k m, (1 : ℝ) := Finset.sum_le_sum fun j _ => hle1 j
      _ = (m - k : ℕ) := by simp
      _ ≤ N₀ := by exact_mod_cast (show m - k ≤ N₀ by omega)
  have hstep : ∀ j, m ≤ j → ν ≤ S (j + 1) - S j := fun j hj => by
    simp only [S]; rw [Finset.sum_Ico_succ_top (by omega)]; ring_nf; exact hd j (by omega)
  have htail : ∑ j ∈ Ico m J, Real.exp (-S (j + 1)) ≤ 1 / ν := by
    refine (sum_exp_neg_le hν hstep J).trans ?_
    apply div_le_div_of_nonneg_right _ hν.le
    rw [Real.exp_le_one_iff, neg_nonpos]; exact Finset.sum_nonneg fun i _ => hd0 i
  show ∑ j ∈ Ico k J, Real.exp (-S (j + 1)) ≤ _
  by_cases hmJ : m ≤ J
  · rw [← Finset.sum_Ico_consecutive _ (le_max_left k N₀) hmJ]; linarith
  · have hsub : Ico k J ⊆ Ico k m := Finset.Ico_subset_Ico_right (by omega)
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (Real.exp_pos (-S (j + 1))).le)
    have : 0 ≤ 1 / ν := by positivity
    linarith

/-- Growth exponent on the line. -/
def gL (c : ℝ) (s₀ : ℂ) (i : ℕ) : ℝ :=
  1 / (((s₀ + 2 * (i : ℂ)).re + 1) * ((s₀ + 2 * (i : ℂ)).re + 4)) + Gw c (s₀ + 2 * i) / 2 + Gw c (s₀ + 2 * i + 2) / 2

/-- Damping exponent on the line. -/
def dL (c χ : ℝ) (s₀ : ℂ) (i : ℕ) : ℝ := Dw c χ (s₀ + 2 * i) / 2 + Dw c χ (s₀ + 2 * i + 2) / 2

variable {ε c χ : ℝ} {s₀ : ℂ}

theorem Dw_nonneg (h : Hyp ε c χ s₀) : 0 ≤ Dw c χ s₀ := by
  unfold Dw; split_ifs
  · have := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.re_omega_ge h; have := h.hre; have := h.c_pos
    exact div_nonneg (by linarith) (by positivity)
  · exact le_rfl

/-- `D(s) ≥ √(2c)/(189c)` once `Re s ≥ √(2c)`. -/
theorem Dw_ge (h : Hyp ε c χ s₀) (hx : Real.sqrt (2 * c) ≤ s₀.re) :
    Real.sqrt (2 * c) / (189 * c) ≤ Dw c χ s₀ := by
  have hre := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.re_omega_ge h
  have hc := h.c_pos
  have hω : Real.sqrt (2 * c) ≤ (omega s₀).re := by linarith
  have hact : 2 * χ ≤ ‖omega s₀‖ ^ 2 := by
    have h1 : (omega s₀).re ≤ ‖omega s₀‖ := Complex.re_le_norm _
    have h2 : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt (by linarith)
    have h3 : Real.sqrt (2 * c) ^ 2 ≤ ‖omega s₀‖ ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (hω.trans h1) 2
    linarith [h.hχ1]
  unfold Dw; rw [if_pos hact]
  exact div_le_div_of_nonneg_right hω (by positivity)

theorem gL_nonneg (h : Hyp ε c χ s₀) (i : ℕ) : 0 ≤ gL c s₀ i := by
  have hi := hyp_line h i
  have hi' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two hi
  have := Gw_nonneg hi; have := Gw_nonneg hi'
  have hx := hi.hre
  unfold gL
  have : 0 < ((s₀ + 2 * (i : ℂ)).re + 1) * ((s₀ + 2 * (i : ℂ)).re + 4) := by nlinarith
  have := one_div_pos.mpr this
  linarith

theorem dL_nonneg (h : Hyp ε c χ s₀) (i : ℕ) : 0 ≤ dL c χ s₀ i := by
  have hi := hyp_line h i
  have := Dw_nonneg hi; have := Dw_nonneg (Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two hi)
  unfold dL; linarith

/-- `d_i ≥ √(2c)/(189c)` once `2i ≥ √(2c)`. -/
theorem dL_ge (h : Hyp ε c χ s₀) {i : ℕ} (hi : Real.sqrt (2 * c) ≤ 2 * i) :
    Real.sqrt (2 * c) / (189 * c) ≤ dL c χ s₀ i := by
  have hl := hyp_line h i
  have hl' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two hl
  have hx : (s₀ + 2 * (i : ℂ)).re = s₀.re + 2 * i := by simp
  have h0 := h.hre
  have a1 := Dw_ge hl (by rw [hx]; linarith)
  have hx' : (s₀ + 2 * (i : ℂ) + 2).re = s₀.re + 2 * i + 2 := by simp
  have a2 := Dw_ge hl' (by rw [hx']; linarith)
  unfold dL; linarith

/-- **Split of the step coefficient** in the near region `Re s_i ≤ 2c`: `‖A(s_i)‖ ≤ exp(g_i − d_i)`. -/
theorem norm_Af_le_split (h : Hyp ε c χ s₀) {i : ℕ} (hx : (s₀ + 2 * (i : ℂ)).re ≤ 2 * c) :
    ‖Af c χ (s₀ + 2 * i)‖ ≤ Real.exp (gL c s₀ i - dL c χ s₀ i) := by
  have hl := hyp_line h i
  have hl' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two hl
  have hn : ∀ t : ℂ, t.re ≤ 2 * c + 2 → |t.im| ≤ (2 - ε) * c → 0 ≤ t.re → ‖t‖ ≤ 4 * c + 2 := by
    intro t ht hti ht0
    have := Complex.norm_le_abs_re_add_abs_im t
    rw [abs_of_nonneg ht0] at this
    have := hl.hε; nlinarith [h.c_pos]
  have hz := Hyp.normSq_zeta_le_GD hl (hn _ (by linarith) hl.him (by linarith [hl.hre]))
  have hz' := Hyp.normSq_zeta_le_GD hl' (hn _ (by simp at hx ⊢; linarith) hl'.him (by linarith [hl'.hre]))
  refine (norm_Af_le_of hl hz hz').trans (le_of_eq ?_)
  unfold gL dL; ring_nf

end Cvs.Prolate.Mellin.StepCoefficientSplit
