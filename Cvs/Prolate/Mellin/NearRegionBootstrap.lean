import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootFirstDifference
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.NearRegionForcingSize
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.StepCoefficientSplit
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Upstream.AbelSummationRecursion
import Cvs.Upstream.ProfiledBootstrapStep

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The near-region bootstrap for the ground law ratio

On the line `s_k = s₀ + 2k` below the far region (`k ≤ J`), if `(40/9)Λ₁ΓT ≤ 1` and `2ΓΛ₁ ≤ 1/10` with
`Λ₁ = 5424/(cε) + DS(ε,c) + 750/c`, `Γ = exp(17/15 + (3/8) log c)` and `T = ⌈√(2c)/2⌉ + 189c/√(2c)`, then
`P_k ≠ 0` and `|v_k| ≤ 2γ_kΛ₁`, where `γ_k = exp(Σ_{k≤i<J} g_i) ≤ Γ`.
-/

noncomputable section

open Finset

namespace Cvs.Prolate.Mellin.NearRegionBootstrap

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.ForcingSmallBound Cvs.Prolate.Mellin.StepAmplification Cvs.Prolate.Mellin.NearRegionBetaStep Cvs.Prolate.Mellin.TrueRatioDownwardStep Cvs.Upstream.AbelSummationRecursion Cvs.Upstream.ProfiledBootstrapStep Cvs.Prolate.Mellin.StepCoefficientSplit Cvs.Prolate.Mellin.NearRegionForcingSize

/-- The amplification ceiling. -/
def Γc (c : ℝ) : ℝ := Real.exp (17 / 15 + 3 / 8 * Real.log c)

/-- The damping count. -/
def Tc (c : ℝ) : ℝ := ⌈Real.sqrt (2 * c) / 2⌉₊ + 189 * c / Real.sqrt (2 * c)

/-- The profile level. -/
def Λc (ε c : ℝ) : ℝ := 5424 / (c * ε) + DS ε c + 750 / c

/-- The profile `γ_k = exp(Σ_{k≤i<J} g_i)`. -/
def γL (c : ℝ) (s₀ : ℂ) (k : ℕ) : ℝ := Real.exp (∑ i ∈ Ico k (Jn c s₀), gL c s₀ i)

variable {ε c χ : ℝ} {s₀ : ℂ}

theorem one_le_γL (h : Hyp ε c χ s₀) (k : ℕ) : 1 ≤ γL c s₀ k :=
  Real.one_le_exp (Finset.sum_nonneg fun i _ => gL_nonneg h i)

theorem γL_le (h : Hyp ε c χ s₀) (k : ℕ) : γL c s₀ k ≤ Γc c := by
  unfold γL Γc
  refine Real.exp_le_exp.mpr ?_
  by_cases hk : k ≤ Jn c s₀
  · exact sum_growth_le h hk
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    have := Real.log_nonneg (show (1 : ℝ) ≤ c by linarith [h.c_ge]); positivity

/-- **The recursion at one index.** -/
theorem rec_at (h : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hε4 : ε ≤ 1 / 4) (j : ℕ) (hP1 : Pk c s₀ (j + 1) ≠ 0)
    (hP2 : Pk c s₀ (j + 2) ≠ 0) (hv : ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (j + 1)‖ ≤ 1 / 10) :
    vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ j = -Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (j : ℂ)) * vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (j + 1)
      + betaf c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (j : ℂ)) * (1 + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (j : ℂ)))
      + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * (j : ℂ)) * vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (j + 1) ^ 2
          / (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (j + 1)) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hl := hyp_line h j
  have h1v : 1 + vk c χ s₀ (j + 1) ≠ 0 := by
    intro h0
    have : ‖vk c χ s₀ (j + 1)‖ = 1 := by
      rw [show vk c χ s₀ (j + 1) = -1 by linear_combination h0]; simp
    linarith
  have h1A : 1 + Af c χ (s₀ + 2 * (j : ℂ)) ≠ 0 := by
    intro h0
    have := Hyp.norm_one_add_Af_ge hl hε4
    rw [h0, norm_zero] at this
    have := Cvs.Prolate.Mellin.FrozenRootFirstDifference.Hyp.a_pos hl
    have : 0 < min (1 / 2 : ℝ) ((csqrt (tau c χ (s₀ + 2 * (j : ℂ)) ^ 2 + 1)).re / 6) :=
      lt_min (by norm_num) (by positivity)
    linarith
  have hstep := line_step h j hP1 hP2 h1v
  have hv' : vk c χ s₀ j = Af c χ (s₀ + 2 * (j : ℂ)) * (-vk c χ s₀ (j + 1) / (1 + vk c χ s₀ (j + 1)))
      + Bf c χ (s₀ + 2 * (j : ℂ)) := by
    unfold vk at *
    rw [hstep]; field_simp; ring
  rw [hv']
  unfold betaf
  field_simp
  ring

/-- **The near-region bootstrap.** -/
theorem near_bootstrap (h : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hε16 : ε ≤ 1 / 16) (hc7 : 7500 ≤ c)
    (hs1 : 40 / 9 * Λc ε c * Γc c * Tc c ≤ 1) (hs2 : 2 * Γc c * Λc ε c ≤ 1 / 10) :
    ∀ k, k ≤ Jn c s₀ → Pk c s₀ k ≠ 0 ∧ ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ 2 * γL c s₀ k * Λc ε c := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  set J := Jn c s₀
  set Λ₁ := Λc ε c
  have hc := h.c_pos
  have hε := h.hε
  have hε4 : ε ≤ 1 / 4 := by linarith
  have far := far_bootstrap h hε4 hc7 J le_re_Jn
  have hDS0 : 0 ≤ DS ε c := by
    unfold DS; have := Real.log_nonneg (show (1 : ℝ) ≤ c by linarith); positivity
  have hΛ0 : 0 ≤ Λ₁ := by simp only [Λ₁, Λc]; positivity
  have hΓ1 : 1 ≤ Γc c := (one_le_γL h 0).trans (γL_le h 0)
  have hsmallv : ∀ j, ‖vk c χ s₀ j‖ ≤ 2 * γL c s₀ j * Λ₁ → ‖vk c χ s₀ j‖ ≤ 1 / 10 := fun j hj => by
    have := γL_le h j
    nlinarith
  have hP_of : ∀ j, ‖vk c χ s₀ j‖ ≤ 1 / 10 → Pk c s₀ j ≠ 0 := fun j hj h0 => by
    have : vk c χ s₀ j = -1 := by unfold vk; rw [h0]; simp
    rw [this] at hj; norm_num at hj
  -- S k : the claim holds on [k, J]
  have hS : ∀ m, m ≤ J → ∀ j, J - m ≤ j → j ≤ J →
      Pk c s₀ j ≠ 0 ∧ ‖vk c χ s₀ j‖ ≤ 2 * γL c s₀ j * Λ₁ := by
    intro m
    induction m with
    | zero =>
      intro _ j hj1 hj2
      have hjJ : j = J := by omega
      subst hjJ
      obtain ⟨hP, hv⟩ := far J le_rfl
      refine ⟨hP, hv.trans ?_⟩
      have := one_le_γL h J
      have : 750 / c ≤ Λ₁ := by
        simp only [Λ₁, Λc]; have : 0 ≤ 5424 / (c * ε) := by positivity
        linarith
      nlinarith
    | succ m ih =>
      intro hm j hj1 hj2
      by_cases hjm : J - m ≤ j
      · exact ih (by omega) j hjm hj2
      -- j = J - (m + 1) = k, and everything above holds
      set k := j
      have hkJ : k < J := by omega
      have above : ∀ i, k < i → i ≤ J → Pk c s₀ i ≠ 0 ∧ ‖vk c χ s₀ i‖ ≤ 2 * γL c s₀ i * Λ₁ :=
        fun i hi1 hi2 => ih (by omega) i (by omega) hi2
      have hPne : ∀ i, k < i → Pk c s₀ i ≠ 0 := fun i hi => by
        by_cases hiJ : i ≤ J
        · exact (above i hi hiJ).1
        · exact (far i (by omega)).1
      have hrec : ∀ i < J, k ≤ i → vk c χ s₀ i = -Af c χ (s₀ + 2 * (i : ℂ)) * vk c χ s₀ (i + 1)
          + betaf c χ (s₀ + 2 * (i : ℂ)) * (1 + Af c χ (s₀ + 2 * (i : ℂ)))
          + Af c χ (s₀ + 2 * (i : ℂ)) * vk c χ s₀ (i + 1) ^ 2 / (1 + vk c χ s₀ (i + 1)) := fun i hi hki =>
        rec_at h hε4 i (hPne (i + 1) (by omega)) (hPne (i + 2) (by omega))
          (hsmallv _ (above (i + 1) (by omega) (by omega)).2)
      have hbound : ‖vk c χ s₀ k‖ ≤ 2 * γL c s₀ k * Λ₁ := by
        refine profile_step (a := fun i => Af c χ (s₀ + 2 * (i : ℂ))) (β := fun i => betaf c χ (s₀ + 2 * (i : ℂ)))
          (γ := γL c s₀) (δ := fun j => Real.exp (-∑ i ∈ Ico k j, dL c χ s₀ i))
          (Bs := 2712 / (c * ε)) (DS := DS ε c) (VJ := 750 / c) (Γ := Γc c) (T := Tc c)
          hkJ hrec ?_ (one_le_γL h) (γL_le h) (fun j => (Real.exp_pos _).le) ?_ ?_ ?_ ?_ (far J le_rfl).2 ?_
          hs1 hs2 (fun i hi1 hi2 => (above i hi1 hi2).2)
        · -- the product bound
          intro j hkj hjJ
          have hp := norm_prodNeg_le (a := fun i => Af c χ (s₀ + 2 * (i : ℂ))) (g := gL c s₀) (d := dL c χ s₀)
            (k := k) (j := j) (fun i hi => by
              rw [Finset.mem_Ico] at hi
              exact norm_Af_le_split h (by rw [re_line]; exact (re_lt_of_lt_Jn (by omega)).le))
          refine hp.trans (le_of_eq ?_)
          unfold γL
          rw [exp_sum_Ico_eq hkj hjJ]
        · intro j
          rw [Real.exp_le_one_iff, neg_nonpos]; exact Finset.sum_nonneg fun i _ => dL_nonneg h i
        · -- the damping sum
          have hν : 0 < Real.sqrt (2 * c) / (189 * c) := by
            have : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.mpr (by linarith)
            positivity
          have := sum_damp_le (d := dL c χ s₀) (N₀ := ⌈Real.sqrt (2 * c) / 2⌉₊) hν (dL_nonneg h)
            (fun i hi => dL_ge h (by
              have := (Nat.ceil_le).mp hi
              linarith)) k J
          refine this.trans (le_of_eq ?_)
          unfold Tc; rw [one_div_div]
        · intro i hki hiJ
          exact Hyp.norm_betaf_le (hyp_line h i) hε4
        · exact sum_betaf_step_le h hε16 k
        · simp only [Λ₁, Λc]; ring_nf; rfl
      exact ⟨hP_of k (hsmallv k hbound), hbound⟩
  intro k hk
  exact hS J le_rfl k (by omega) hk

end Cvs.Prolate.Mellin.NearRegionBootstrap
