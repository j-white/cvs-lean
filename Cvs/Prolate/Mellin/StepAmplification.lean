import Mathlib
import Cvs.Prolate.Mellin.FrozenRootCoreBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootStep
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The amplification of the step recursion is at most `e^{17/15} c^{3/8}`

Along `s_i = s₀ + 2i` in the region with `ε ≤ 1/4`, `∏_{k ≤ i < j} |A(s_i)| ≤ exp(17/15 + (3/8) log c)` for all `k ≤ j`:
`|A|² = |(s+2)(s+3)|/|(s+1)(s+4)| |ζ(s)|²|ζ(s+2)|²`, the first factor is at most `exp(2/((x+1)(x+4)))`, and `|ζ|² ≤ 1`
except in the core `Re ω < √c`, where `|ζ|² ≤ exp(3/(2 Re ω))`.
-/

noncomputable section

open Complex Finset

namespace Cvs.Prolate.Mellin.StepAmplification

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)

variable {ε c χ : ℝ} {s₀ : ℂ}

/-- The core weight `G(s) = 3/(2 Re ω)` if `Re ω < √c`, else `0`. -/
def Gw (c : ℝ) (s : ℂ) : ℝ := if (omega s).re < Real.sqrt c then 3 / (2 * (omega s).re) else 0

theorem hyp_line (h : Hyp ε c χ s₀) (i : ℕ) : Hyp ε c χ (s₀ + 2 * i) := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    have := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two ih
    rwa [show s₀ + 2 * (i : ℂ) + 2 = s₀ + 2 * ((i + 1 : ℕ) : ℂ) by push_cast; ring] at this

theorem Gw_nonneg (h : Hyp ε c χ s₀) : 0 ≤ Gw c s₀ := by
  unfold Gw; split_ifs
  · have := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.re_omega_ge h; have := h.hre
    exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

/-- **`|ζ|² ≤ exp(G)`** on the region. -/
theorem normSq_zeta_le_exp_Gw (h : Hyp ε c χ s₀) : ‖zeta c χ s₀‖ ^ 2 ≤ Real.exp (Gw c s₀) := by
  by_cases hx : (tau c χ s₀).re < 0
  · have hcore := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.normSq_omega_lt h hx
    have hlt : (omega s₀).re < Real.sqrt c := by
      have h1 := Complex.re_le_norm (omega s₀)
      have h2 : ‖omega s₀‖ < Real.sqrt c := by
        rw [← Real.sqrt_sq (norm_nonneg _)]; exact Real.sqrt_lt_sqrt (sq_nonneg _) hcore
      linarith
    unfold Gw; rw [if_pos hlt]
    exact Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.normSq_zeta_le_core h hx
  · push Not at hx
    exact (Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.normSq_zeta_le_one h hx).trans
      (Real.one_le_exp_iff.mpr (Gw_nonneg h) |> le_of_eq_of_le rfl)

/-- Telescoping over `Ico`. -/
theorem sum_Ico_sub {f : ℕ → ℝ} {k j : ℕ} (hkj : k ≤ j) : ∑ i ∈ Ico k j, (f i - f (i + 1)) = f k - f j := by
  induction j, hkj using Nat.le_induction with
  | base => simp
  | succ j hkj ih => rw [Finset.sum_Ico_succ_top hkj, ih]; ring

/-- The core majorant `H_i = 3/(2(15/8 + 2i))` for `i ≤ ⌊√c/2⌋`, else `0`. -/
def Hw (c : ℝ) (i : ℕ) : ℝ := if i < ⌊Real.sqrt c / 2⌋₊ + 1 then 3 / (2 * (15 / 8 + 2 * i)) else 0

theorem Hw_nonneg (c : ℝ) (i : ℕ) : 0 ≤ Hw c i := by unfold Hw; split_ifs <;> positivity

theorem Gw_le_Hw (h : Hyp ε c χ s₀) (i : ℕ) : Gw c (s₀ + 2 * i) ≤ Hw c i := by
  have hi := hyp_line h i
  have hre := Cvs.Prolate.Mellin.FrozenRootCoreBound.Hyp.re_omega_ge hi
  have hx : (s₀ + 2 * (i : ℂ)).re = s₀.re + 2 * i := by simp
  rw [hx] at hre
  have h0 := h.hre
  unfold Gw Hw
  split_ifs with h1 h2
  · apply div_le_div_of_nonneg_left (by norm_num) (by positivity); linarith
  · exfalso; apply h2
    have : (i : ℝ) < Real.sqrt c / 2 := by linarith
    have := Nat.le_floor this.le
    omega
  · exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

theorem sum_Hw_le (hc : 64 ≤ c) : ∑ i ∈ range (⌊Real.sqrt c / 2⌋₊ + 1), Hw c i ≤ 4 / 5 + 3 / 8 * Real.log c := by
  set M := ⌊Real.sqrt c / 2⌋₊
  have e : ∑ i ∈ range (M + 1), Hw c i = 3 / 2 * ∑ i ∈ range (M + 1), 1 / (15 / 8 + 2 * (i : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    unfold Hw; rw [if_pos hi]; field_simp
  rw [e]
  have hs := Cvs.Prolate.Mellin.FrozenRootCoreBound.sum_inv_le_log (a := 15 / 8) (by norm_num) M
  have hr8 : 8 ≤ Real.sqrt c := by
    rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hc
  have hM : 2 * (M : ℝ) ≤ Real.sqrt c := by
    have := Nat.floor_le (show 0 ≤ Real.sqrt c / 2 by positivity); linarith
  have hlog : Real.log ((15 / 8 + 2 * (M : ℝ)) / (15 / 8)) ≤ 1 / 2 * Real.log c := by
    have h1 : Real.log ((15 / 8 + 2 * (M : ℝ)) / (15 / 8)) ≤ Real.log (Real.sqrt c) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ (by norm_num)]; linarith
    rw [Real.log_sqrt (by linarith)] at h1
    linarith
  nlinarith

/-- **The total growth exponent** along a line: `Σ_{k≤i<j} (1/((x_i+1)(x_i+4)) + G_i/2 + G_{i+1}/2) ≤ 17/15 + (3/8) log c`. -/
theorem sum_growth_le (h : Hyp ε c χ s₀) {k j : ℕ} (hkj : k ≤ j) :
    ∑ i ∈ Ico k j, (1 / (((s₀ + 2 * (i : ℂ)).re + 1) * ((s₀ + 2 * (i : ℂ)).re + 4))
      + Gw c (s₀ + 2 * i) / 2 + Gw c (s₀ + 2 * i + 2) / 2) ≤ 17 / 15 + 3 / 8 * Real.log c := by
  set e := fun i : ℕ => 1 / (((s₀ + 2 * (i : ℂ)).re + 1) * ((s₀ + 2 * (i : ℂ)).re + 4))
    + Gw c (s₀ + 2 * i) / 2 + Gw c (s₀ + 2 * i + 2) / 2
  show ∑ i ∈ Ico k j, e i ≤ _
  have hx0 := h.hre
  -- rational part ≤ 1/3
  have hrat : ∑ i ∈ Ico k j, 1 / (((s₀ + 2 * (i : ℂ)).re + 1) * ((s₀ + 2 * (i : ℂ)).re + 4)) ≤ 1 / 3 := by
    set f := fun i : ℕ => 1 / 2 * (1 / (s₀.re + 1 + 2 * i))
    have hle : ∀ i ∈ Ico k j, 1 / (((s₀ + 2 * (i : ℂ)).re + 1) * ((s₀ + 2 * (i : ℂ)).re + 4)) ≤ f i - f (i + 1) := by
      intro i _
      have hx : (s₀ + 2 * (i : ℂ)).re = s₀.re + 2 * i := by simp
      rw [hx]
      simp only [f]; push_cast
      have hi0 : (0 : ℝ) ≤ i := i.cast_nonneg
      have e2 : (1 : ℝ) / 2 * (1 / (s₀.re + 1 + 2 * i)) - 1 / 2 * (1 / (s₀.re + 1 + 2 * (i + 1)))
          = 1 / ((s₀.re + 1 + 2 * i) * (s₀.re + 3 + 2 * i)) := by
        have : 0 < s₀.re + 1 + 2 * (i : ℝ) := by linarith
        have : 0 < s₀.re + 3 + 2 * (i : ℝ) := by linarith
        field_simp; ring
      rw [e2]
      apply one_div_le_one_div_of_le (by nlinarith); nlinarith
    calc _ ≤ ∑ i ∈ Ico k j, (f i - f (i + 1)) := Finset.sum_le_sum hle
      _ = f k - f j := sum_Ico_sub hkj
      _ ≤ 1 / 3 := by
          simp only [f]
          have h1 : 1 / (s₀.re + 1 + 2 * (k : ℝ)) ≤ 2 / 3 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; have := (k.cast_nonneg : (0 : ℝ) ≤ k); linarith
          have h2 : 0 ≤ 1 / (s₀.re + 1 + 2 * (j : ℝ)) := by positivity
          linarith
  -- core part
  have hcore : ∑ i ∈ Ico k j, (Gw c (s₀ + 2 * i) / 2 + Gw c (s₀ + 2 * i + 2) / 2) ≤ 4 / 5 + 3 / 8 * Real.log c := by
    have hH : ∀ S : Finset ℕ, ∑ i ∈ S, Hw c i ≤ ∑ i ∈ range (⌊Real.sqrt c / 2⌋₊ + 1), Hw c i := by
      intro S
      rw [← Finset.sum_filter_add_sum_filter_not S (fun i => i < ⌊Real.sqrt c / 2⌋₊ + 1)]
      have hz : ∑ i ∈ S.filter (fun i => ¬ i < ⌊Real.sqrt c / 2⌋₊ + 1), Hw c i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [Finset.mem_filter] at hi; unfold Hw; rw [if_neg hi.2]
      rw [hz, add_zero]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => by rw [Finset.mem_filter] at hi; exact Finset.mem_range.mpr hi.2) (fun i _ _ => Hw_nonneg c i)
    have h1 : ∑ i ∈ Ico k j, Gw c (s₀ + 2 * i) ≤ ∑ i ∈ Ico k j, Hw c i :=
      Finset.sum_le_sum fun i _ => Gw_le_Hw h i
    have h2 : ∑ i ∈ Ico k j, Gw c (s₀ + 2 * i + 2) ≤ ∑ i ∈ (Ico k j).image (· + 1), Hw c i := by
      rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
      refine Finset.sum_le_sum fun i _ => ?_
      have := Gw_le_Hw h (i + 1)
      rwa [show s₀ + 2 * ((i + 1 : ℕ) : ℂ) = s₀ + 2 * (i : ℂ) + 2 by push_cast; ring] at this
    have hs := sum_Hw_le h.c_ge
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    have := hH (Ico k j)
    have := hH ((Ico k j).image (· + 1))
    linarith
  have : ∑ i ∈ Ico k j, e i = ∑ i ∈ Ico k j, 1 / (((s₀ + 2 * (i : ℂ)).re + 1) * ((s₀ + 2 * (i : ℂ)).re + 4))
      + ∑ i ∈ Ico k j, (Gw c (s₀ + 2 * i) / 2 + Gw c (s₀ + 2 * i + 2) / 2) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; simp only [e]; ring
  rw [this]
  linarith

end Cvs.Prolate.Mellin.StepAmplification
