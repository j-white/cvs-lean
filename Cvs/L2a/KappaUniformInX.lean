import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutEstimateFrameFloor
import Cvs.L2a.CutGap
import Cvs.L2a.CutRemainderDensity
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.FirstStepRemainderCount
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RampCutSumsUniform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `κ(X)` uniformly in `X`, and `PositionTailFullTail`'s `hNS` with an `X`-free constant

The row `m = 1` of `kapCount nsRamp nsRamp' (5/4) X` integrates cell by cell on the grid `5/4 + j/32` (`j ≤ 8`),
`3/2, 7/4, 2, 5/2, 3, 4, 6, ∞` against `g₁₂` and `G₃ ≥ Σ_{n≥3} g_1n`, so `κ(X) ≤ κ̄ = κ̄₁ + 2Σ_{m≥2}σ_mΦ̄_m` for
every `X`; with `RampCutSumsUniform`'s `Λ̄₀` this feeds `CutEstimateFrameFloor`'s `NS_of_floor_unif` and Cvs.L2a.PositionTailFullTail with an `X`-free and `c`-free constant.
-/

namespace Cvs.L2a.KappaUniformInX

open MeasureTheory Real Set Cvs.L2a.CutGap Cvs.L2a.CutPointCountForm Cvs.L2a.FirstStepRemainderCount Cvs.L2a.CutEstimateFrameFloor Cvs.L2a.RampCutSumsUniform Cvs.L2a.CutRemainderDensity

/-- The ramp grid `a_j = 5/4 + j/32`: `a₀ = 5/4`, `a₈ = 3/2`. -/
noncomputable def gridA (j : ℕ) : ℝ := 5 / 4 + j / 32

/-- The tail grid `3/2, 7/4, 2, 5/2, 3, 4, 6`. -/
noncomputable def gridB : ℕ → ℝ
  | 0 => 3 / 2
  | 1 => 7 / 4
  | 2 => 2
  | 3 => 5 / 2
  | 4 => 3
  | 5 => 4
  | _ => 6

/-- The cell majorant `𝒟(F, A)`: eight ramp cells, six tail cells and the cell `[6, ∞)`. -/
noncomputable def gridSum (F A : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 8, F (gridA j) * (nsRamp (gridA (j + 1)) - nsRamp (gridA j)
      + A (gridA j) * nsRamp (gridA (j + 1)) / 32)
    + ∑ i ∈ Finset.range 6, F (gridB i) * gridB i ^ 2 * ((1 / gridB i ^ 2 - 1 / gridB (i + 1) ^ 2) / 2
      + A (gridB i) * gridB i * (L3 (gridB i) - L3 (gridB (i + 1))))
    + F 6 * 6 ^ 2 * (1 / 6 ^ 2 / 2 + A 6 * 6 * L3 6)

/-- `ζ(3) = Σ 1/n³`. -/
noncomputable def zeta3 : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ 3

/-- `G₃(θ) = [(ζ(3) − 9/8)k(3θ)/(θ² − 1) + (ζ(2) − 5/4)α(3θ)/(θ√(θ² − 1))]/(1 − α(θ)/9)`. -/
noncomputable def G3 (θ : ℝ) : ℝ :=
  ((zeta3 - 9 / 8) * kU (3 * θ) / (θ ^ 2 - 1) + (π ^ 2 / 6 - 5 / 4) * aU (3 * θ) / (θ * √(θ ^ 2 - 1)))
    / (1 - aU θ / 9)

/-- `κ̄₁ = 2𝒟(g₁₂, A₁₂) + 2𝒟(G₃, A₁₃)`, the row `m = 1`. -/
noncomputable def kappaBar1 : ℝ := 2 * gridSum g12 (cutA 1 2) + 2 * gridSum G3 (cutA 1 3)

/-- `κ̄ = κ̄₁ + κ̄_{≥2}`. -/
noncomputable def kappaBar : ℝ := kappaBar1 + kappaBar2

theorem gridA_succ_sub (j : ℕ) : gridA (j + 1) - gridA j = 1 / 32 := by
  unfold gridA; push_cast; ring

theorem gridA_bounds {j : ℕ} (hj : j ≤ 8) : 5 / 4 ≤ gridA j ∧ gridA j ≤ 3 / 2 := by
  have h : (j : ℝ) ≤ 8 := by exact_mod_cast hj
  have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold gridA
  constructor <;> linarith

theorem gridA_mono (j : ℕ) : gridA j ≤ gridA (j + 1) := by
  have := gridA_succ_sub j; linarith

theorem gridB_bounds {i : ℕ} (hi : i < 6) : 3 / 2 ≤ gridB i ∧ gridB i ≤ gridB (i + 1) := by
  interval_cases i <;> norm_num [gridB]

theorem gridB_le_six {i : ℕ} (hi : i ≤ 6) : gridB i ≤ 6 := by
  interval_cases i <;> norm_num [gridB]

theorem gridSum_add (F G A : ℝ → ℝ) : gridSum (fun θ => F θ + G θ) A = gridSum F A + gridSum G A := by
  simp only [gridSum, add_mul, Finset.sum_add_distrib]
  ring

theorem gridSum_zero (A : ℝ → ℝ) : gridSum (fun _ => 0) A = 0 := by
  simp [gridSum]

theorem sum_gridSum (s : Finset ℕ) (F : ℕ → ℝ → ℝ) (A : ℝ → ℝ) :
    ∑ n ∈ s, gridSum (F n) A = gridSum (fun θ => ∑ n ∈ s, F n θ) A := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (gridSum_zero A).symm
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, ih]
    simp only [Finset.sum_insert hk]
    exact (gridSum_add (F k) (fun θ => ∑ n ∈ s, F n θ) A).symm

/-- All grid weights are nonnegative when `A ≥ 0`, so `𝒟(·, A)` is monotone. -/
theorem gridSum_le_of_le {F F' A : ℝ → ℝ} (hA : ∀ θ, 5 / 4 ≤ θ → 0 ≤ A θ)
    (hF : ∀ θ, 5 / 4 ≤ θ → F θ ≤ F' θ) : gridSum F A ≤ gridSum F' A := by
  unfold gridSum
  have hramp : ∀ j ∈ Finset.range 8, F (gridA j) * (nsRamp (gridA (j + 1)) - nsRamp (gridA j)
      + A (gridA j) * nsRamp (gridA (j + 1)) / 32) ≤ F' (gridA j) * (nsRamp (gridA (j + 1)) - nsRamp (gridA j)
      + A (gridA j) * nsRamp (gridA (j + 1)) / 32) := by
    intro j hj
    have hj8 := Finset.mem_range.mp hj
    obtain ⟨h1, h2⟩ := gridA_bounds (j := j) (by omega)
    obtain ⟨h3, h4⟩ := gridA_bounds (j := j + 1) (by omega)
    have hm : nsRamp (gridA j) ≤ nsRamp (gridA (j + 1)) :=
      nsRamp_monotoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (gridA_mono j)
    have hw := nsRamp_nonneg (by linarith : (1 : ℝ) ≤ gridA (j + 1))
    have hA0 := hA _ h1
    apply mul_le_mul_of_nonneg_right (hF _ h1)
    have : 0 ≤ A (gridA j) * nsRamp (gridA (j + 1)) / 32 := by positivity
    linarith
  have htail : ∀ i ∈ Finset.range 6, F (gridB i) * gridB i ^ 2 * ((1 / gridB i ^ 2 - 1 / gridB (i + 1) ^ 2) / 2
      + A (gridB i) * gridB i * (L3 (gridB i) - L3 (gridB (i + 1)))) ≤ F' (gridB i) * gridB i ^ 2
        * ((1 / gridB i ^ 2 - 1 / gridB (i + 1) ^ 2) / 2
      + A (gridB i) * gridB i * (L3 (gridB i) - L3 (gridB (i + 1)))) := by
    intro i hi
    obtain ⟨h1, h2⟩ := gridB_bounds (Finset.mem_range.mp hi)
    have hu0 : 0 < gridB i := by linarith
    have hL := L3_anti (by linarith) h2
    have hA0 := hA (gridB i) (by linarith)
    have hsq : 1 / gridB (i + 1) ^ 2 ≤ 1 / gridB i ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hu0.le h2 2)
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hF _ (by linarith)) (by positivity))
    have : 0 ≤ A (gridB i) * gridB i * (L3 (gridB i) - L3 (gridB (i + 1))) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hlast : F 6 * 6 ^ 2 * (1 / 6 ^ 2 / 2 + A 6 * 6 * L3 6) ≤ F' 6 * 6 ^ 2 * (1 / 6 ^ 2 / 2 + A 6 * 6 * L3 6) := by
    have hA0 := hA 6 (by norm_num)
    have hL := L3_nonneg (by norm_num : (1 : ℝ) ≤ 6)
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hF 6 (by norm_num)) (by norm_num))
    positivity
  linarith [Finset.sum_le_sum hramp, Finset.sum_le_sum htail]

theorem gridSum_nonneg {F A : ℝ → ℝ} (hA : ∀ θ, 5 / 4 ≤ θ → 0 ≤ A θ) (hF : ∀ θ, 5 / 4 ≤ θ → 0 ≤ F θ) :
    0 ≤ gridSum F A := by
  have h := gridSum_le_of_le (F := fun _ => 0) (F' := F) hA hF
  rwa [gridSum_zero] at h

/-- **The grid lemma**: `∫_{5/4}^B f ≤ 𝒟(F, A)` for `0 ≤ f ≤ F(ω' + ωA)` with `θ²F` and `θA` nonincreasing. -/
theorem integral_le_gridSum {f F A : ℝ → ℝ} {B : ℝ} (hB : 5 / 4 ≤ B)
    (hfi : ∀ b, 5 / 4 ≤ b → IntervalIntegrable f volume (5 / 4) b)
    (hf0 : ∀ θ, 5 / 4 ≤ θ → 0 ≤ f θ)
    (hfle : ∀ θ, 5 / 4 ≤ θ → f θ ≤ F θ * (nsRamp' θ + nsRamp θ * A θ))
    (hF0 : ∀ θ, 5 / 4 ≤ θ → 0 ≤ F θ) (hA0 : ∀ θ, 5 / 4 ≤ θ → 0 ≤ A θ)
    (hFa : ∀ a θ, 5 / 4 ≤ a → a ≤ θ → θ ^ 2 * F θ ≤ a ^ 2 * F a)
    (hAa : ∀ a θ, 5 / 4 ≤ a → a ≤ θ → θ * A θ ≤ a * A a) :
    ∫ θ in (5 / 4 : ℝ)..B, f θ ≤ gridSum F A := by
  set B' := max B 6 with hB'
  have hBB' : B ≤ B' := le_max_left _ _
  have h6B' : (6 : ℝ) ≤ B' := le_max_right _ _
  have hsub : ∀ u v, 5 / 4 ≤ u → u ≤ v → v ≤ B' → IntervalIntegrable f volume u v := fun u v hu huv hv =>
    (hfi B' (by linarith)).mono_set (by
      rw [uIcc_of_le huv, uIcc_of_le (by linarith)]
      exact Icc_subset_Icc hu hv)
  have hFle : ∀ u θ, 5 / 4 ≤ u → u ≤ θ → F θ ≤ F u := by
    intro u θ hu huθ
    have h1 := hFa u θ hu huθ
    have h2 := hF0 u hu
    have hθ' : 0 < θ := by linarith
    have hθ0 : 0 < θ ^ 2 := by positivity
    have hθ2 : u ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (by linarith) huθ 2
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_left h hθ0, mul_le_mul_of_nonneg_right hθ2 h2]
  have hAle : ∀ u θ, 5 / 4 ≤ u → u ≤ θ → A θ ≤ A u := by
    intro u θ hu huθ
    have h1 := hAa u θ hu huθ
    have h2 := hA0 u hu
    have hθ0 : 0 < θ := by linarith
    by_contra h
    push Not at h
    nlinarith [mul_lt_mul_of_pos_left h hθ0, mul_le_mul_of_nonneg_right huθ h2]
  -- the ramp cells
  have hramp : ∀ j ∈ Finset.range 8, ∫ θ in gridA j..gridA (j + 1), f θ
      ≤ F (gridA j) * (nsRamp (gridA (j + 1)) - nsRamp (gridA j) + A (gridA j) * nsRamp (gridA (j + 1)) / 32) := by
    intro j hj
    have hj8 := Finset.mem_range.mp hj
    obtain ⟨h1, h2⟩ := gridA_bounds (j := j) (by omega)
    obtain ⟨h3, h4⟩ := gridA_bounds (j := j + 1) (by omega)
    have hmono := gridA_mono j
    have h := integral_le_ramp_cell (f := f) (F := F) (A := A) (by linarith) hmono
      (hsub _ _ h1 hmono (by linarith)) (fun θ hθ => hfle θ (by linarith [hθ.1]))
      (fun θ hθ => hF0 θ (by linarith [hθ.1])) (fun θ hθ => hA0 θ (by linarith [hθ.1]))
      (fun θ hθ => hFle _ θ h1 hθ.1) (fun θ hθ => hAle _ θ h1 hθ.1)
    rw [gridA_succ_sub] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  have hsA := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume) (a := gridA) (n := 8)
    fun k hk => hsub _ _ (gridA_bounds (j := k) (by omega)).1 (gridA_mono k)
      (by linarith [(gridA_bounds (j := k + 1) (by omega)).2])
  have hA0' : gridA 0 = 5 / 4 := by norm_num [gridA]
  have hA8 : gridA 8 = 3 / 2 := by norm_num [gridA]
  rw [hA0', hA8] at hsA
  -- the tail cells
  have htail : ∀ i ∈ Finset.range 6, ∫ θ in gridB i..gridB (i + 1), f θ
      ≤ F (gridB i) * gridB i ^ 2 * ((1 / gridB i ^ 2 - 1 / gridB (i + 1) ^ 2) / 2
        + A (gridB i) * gridB i * (L3 (gridB i) - L3 (gridB (i + 1)))) := by
    intro i hi
    have hi6 := Finset.mem_range.mp hi
    obtain ⟨h1, h2⟩ := gridB_bounds hi6
    have h3 := gridB_le_six (i := i + 1) (by omega)
    exact integral_le_tail_cell h1 h2 (hsub _ _ (by linarith) h2 (by linarith))
      (fun θ hθ => hfle θ (by linarith [hθ.1])) (fun θ hθ => hF0 θ (by linarith [hθ.1]))
      (fun θ hθ => hA0 θ (by linarith [hθ.1])) (fun θ hθ => hFa _ θ (by linarith) hθ.1)
      (fun θ hθ => hAa _ θ (by linarith) hθ.1)
  have hsB := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume) (a := gridB) (n := 6)
    fun k hk => hsub _ _ (by linarith [(gridB_bounds hk).1]) (gridB_bounds hk).2
      (by linarith [gridB_le_six (i := k + 1) (by omega)])
  have hB0 : gridB 0 = 3 / 2 := rfl
  have hB6 : gridB 6 = 6 := rfl
  rw [hB0, hB6] at hsB
  -- the last cell
  have hlast := integral_le_tail_cell (f := f) (F := F) (A := A) (u := 6) (v := B') (by norm_num) h6B'
    (hsub _ _ (by norm_num) h6B' le_rfl) (fun θ hθ => hfle θ (by linarith [hθ.1]))
    (fun θ hθ => hF0 θ (by linarith [hθ.1])) (fun θ hθ => hA0 θ (by linarith [hθ.1]))
    (fun θ hθ => hFa _ θ (by norm_num) hθ.1) (fun θ hθ => hAa _ θ (by norm_num) hθ.1)
  have hlast' : ∫ θ in (6 : ℝ)..B', f θ ≤ F 6 * 6 ^ 2 * (1 / 6 ^ 2 / 2 + A 6 * 6 * L3 6) := by
    refine hlast.trans ?_
    have hF6 := hF0 6 (by norm_num)
    have hA6 := hA0 6 (by norm_num)
    have hL : 0 ≤ L3 B' := L3_nonneg (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 0 ≤ 1 / B' ^ 2 := by positivity
    have : A 6 * 6 * (L3 6 - L3 B') ≤ A 6 * 6 * L3 6 := by nlinarith
    linarith
  have hmono : ∫ θ in (5 / 4 : ℝ)..B, f θ ≤ ∫ θ in (5 / 4 : ℝ)..B', f θ :=
    intervalIntegral.integral_mono_interval le_rfl hB hBB'
      (ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ => hf0 θ hθ.1.le)
      (hsub _ _ le_rfl (by linarith) le_rfl)
  have hsplit : ∫ θ in (5 / 4 : ℝ)..B', f θ
      = (∫ θ in (5 / 4 : ℝ)..3 / 2, f θ) + (∫ θ in (3 / 2 : ℝ)..6, f θ) + ∫ θ in (6 : ℝ)..B', f θ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hsub _ _ le_rfl (by norm_num) (by linarith))
        (hsub _ _ (by norm_num) (by norm_num) (by linarith)),
      intervalIntegral.integral_add_adjacent_intervals (hsub _ _ le_rfl (by norm_num) (by linarith))
        (hsub _ _ (by norm_num) h6B' le_rfl)]
  unfold gridSum
  linarith [Finset.sum_le_sum hramp, Finset.sum_le_sum htail]

theorem cutA_one_nonneg {n : ℝ} (hn : 2 ≤ n) {θ : ℝ} (hθ : 5 / 4 ≤ θ) : 0 ≤ cutA 1 n θ := by
  have hθ0 : 0 < θ := by linarith
  have hΓ := cutGamma_one_pos (θ := θ) hn (by nlinarith)
  have hB : 0 ≤ cutDeltaBound 1 n θ := by unfold cutDeltaBound; positivity
  unfold cutA
  exact add_nonneg (div_nonneg (by positivity) (by nlinarith)) (div_nonneg hB hΓ.le)

/-- `θA_1n(θ) = 2α(θ) + 2(α(nθ)² + α(θ)²)/(θ²Γ_1n(θ))`. -/
theorem mul_cutA_one_eq {n θ : ℝ} (hn : 2 ≤ n) (hθ : 5 / 4 ≤ θ) :
    θ * cutA 1 n θ = 2 * aU θ + 2 * (aU (n * θ) ^ 2 + aU θ ^ 2) / (θ ^ 2 * cutGamma 1 n θ) := by
  have hθ0 : 0 < θ := by linarith
  have hΓ := cutGamma_one_pos (θ := θ) hn (by nlinarith)
  have hp : θ ^ 2 - 1 ≠ 0 := by nlinarith
  have hnθ : 2 ≤ n * θ := by nlinarith
  have hpn : n ^ 2 * θ ^ 2 - 1 ≠ 0 := by nlinarith
  have hpn' : (n * θ) ^ 2 - 1 ≠ 0 := by rw [mul_pow]; exact hpn
  unfold cutA cutDeltaBound aU
  simp only [one_pow, one_mul]
  rw [mul_pow]
  field_simp

theorem mul_cutA_one_le {n : ℝ} (hn : 2 ≤ n) {a θ : ℝ} (ha : 5 / 4 ≤ a) (haθ : a ≤ θ) :
    θ * cutA 1 n θ ≤ a * cutA 1 n a := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 < a := by linarith
  rw [mul_cutA_one_eq hn (by linarith), mul_cutA_one_eq hn ha]
  have hΓa := cutGamma_one_pos hn (by nlinarith : 4 < 3 * a ^ 2)
  have hΓ := cutGamma_one_mono (n := n) ha1 haθ
  have h1 : aU θ ≤ aU a := aU_anti ha1 haθ
  have h2 : aU (n * θ) ≤ aU (n * a) := aU_anti (by nlinarith) (by nlinarith)
  have h0 : ∀ u : ℝ, 1 < u → 0 ≤ aU u := fun u hu => by rw [← kU_sq hu]; positivity
  have h1' := pow_le_pow_left₀ (h0 θ (by linarith)) h1 2
  have h2' := pow_le_pow_left₀ (h0 (n * θ) (by nlinarith)) h2 2
  have hsq : a ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ ha0.le haθ 2
  have hden : a ^ 2 * cutGamma 1 n a ≤ θ ^ 2 * cutGamma 1 n θ :=
    mul_le_mul hsq hΓ hΓa.le (by positivity)
  have hq : 2 * (aU (n * θ) ^ 2 + aU θ ^ 2) / (θ ^ 2 * cutGamma 1 n θ)
      ≤ 2 * (aU (n * a) ^ 2 + aU a ^ 2) / (a ^ 2 * cutGamma 1 n a) := by
    apply div_le_div₀ (by have := h0 (n * a) (by nlinarith); have := h0 a ha1; positivity) (by linarith)
      (by positivity) hden
  linarith

theorem cutA_one_le_three {n : ℕ} (hn : 3 ≤ n) {θ : ℝ} (hθ : 5 / 4 ≤ θ) : cutA 1 n θ ≤ cutA 1 3 θ := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hθ0 : 0 < θ := by linarith
  have hθ1 : 1 < θ := by linarith
  refine le_of_mul_le_mul_left ?_ hθ0
  rw [mul_cutA_one_eq (by linarith) hθ, mul_cutA_one_eq (by norm_num) hθ]
  have hΓ3 := cutGamma_one_pos (by norm_num : (2 : ℝ) ≤ 3) (by nlinarith : 4 < 3 * θ ^ 2)
  have hΓe : ∀ k : ℝ, cutGamma 1 k θ = k ^ 2 - aU θ := fun k => by rw [cutGamma_eq]; simp
  have hΓn : cutGamma 1 3 θ ≤ cutGamma 1 n θ := by rw [hΓe, hΓe]; nlinarith
  have h0 : ∀ u : ℝ, 1 < u → 0 ≤ aU u := fun u hu => by rw [← kU_sq hu]; positivity
  have h2 : aU (n * θ) ≤ aU (3 * θ) := aU_anti (by linarith) (by nlinarith)
  have h2' := pow_le_pow_left₀ (h0 (n * θ) (by nlinarith)) h2 2
  have hq : 2 * (aU (n * θ) ^ 2 + aU θ ^ 2) / (θ ^ 2 * cutGamma 1 n θ)
      ≤ 2 * (aU (3 * θ) ^ 2 + aU θ ^ 2) / (θ ^ 2 * cutGamma 1 3 θ) := by
    apply div_le_div₀ (by have := h0 (3 * θ) (by linarith); have := h0 θ hθ1; positivity) (by linarith)
      (by positivity) (mul_le_mul_of_nonneg_left hΓn (by positivity))
  linarith

theorem summable_inv_cube : Summable fun n : ℕ => 1 / (n : ℝ) ^ 3 :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

theorem sum_inv_cube_le (N : ℕ) : ∑ n ∈ Finset.Icc 3 N, 1 / (n : ℝ) ^ 3 ≤ zeta3 - 9 / 8 := by
  have hs := summable_inv_cube.sum_le_tsum (insert 1 (insert 2 (Finset.Icc 3 N))) (fun i _ => by positivity)
  have h2 : (2 : ℕ) ∉ Finset.Icc 3 N := by simp
  have h1 : (1 : ℕ) ∉ insert 2 (Finset.Icc 3 N) := by simp
  rw [Finset.sum_insert h1, Finset.sum_insert h2] at hs
  unfold zeta3
  norm_num at hs ⊢
  linarith

theorem sum_inv_sq_le (N : ℕ) : ∑ n ∈ Finset.Icc 3 N, 1 / (n : ℝ) ^ 2 ≤ π ^ 2 / 6 - 5 / 4 := by
  have hs := sum_le_hasSum (insert 1 (insert 2 (Finset.Icc 3 N))) (fun i _ => by positivity) hasSum_zeta_two
  have h2 : (2 : ℕ) ∉ Finset.Icc 3 N := by simp
  have h1 : (1 : ℕ) ∉ insert 2 (Finset.Icc 3 N) := by simp
  rw [Finset.sum_insert h1, Finset.sum_insert h2] at hs
  norm_num at hs ⊢
  linarith

/-- `Σ_{3 ≤ n ≤ N} g_1n(θ) ≤ G₃(θ)` on `θ ≥ 5/4`. -/
theorem sum_cutG_one_le_G3 (N : ℕ) {θ : ℝ} (hθ : 5 / 4 ≤ θ) : ∑ n ∈ Finset.Icc 3 N, cutG 1 n θ ≤ G3 θ := by
  have hθ0 : 0 < θ := by linarith
  have hθ1 : 1 < θ := by linarith
  have hp : 0 < θ ^ 2 - 1 := by nlinarith
  have hsp : 0 < √(θ ^ 2 - 1) := Real.sqrt_pos.2 hp
  have h0 : ∀ u : ℝ, 1 < u → 0 ≤ aU u := fun u hu => by rw [← kU_sq hu]; positivity
  have ha54 : aU θ ≤ 25 / 9 := by
    have := aU_anti (by norm_num : (1 : ℝ) < 5 / 4) hθ
    have e : aU (5 / 4) = 25 / 9 := by unfold aU; norm_num
    linarith
  have haθ := h0 θ hθ1
  have hD : 0 < 1 - aU θ / 9 := by linarith
  have hk3 : 0 ≤ kU (3 * θ) := (kU_pos (by linarith)).le
  have ha3 : 0 ≤ aU (3 * θ) := h0 _ (by linarith)
  have hΓe : ∀ k : ℝ, cutGamma 1 k θ = k ^ 2 - aU θ := fun k => by rw [cutGamma_eq]; simp
  have hterm : ∀ n ∈ Finset.Icc 3 N, cutG 1 n θ
      ≤ (kU (3 * θ) / (θ ^ 2 - 1) * (1 / (n : ℝ) ^ 3) + aU (3 * θ) / (θ * √(θ ^ 2 - 1)) * (1 / (n : ℝ) ^ 2))
        / (1 - aU θ / 9) := by
    intro n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    rw [cutG_one_eq hn0 hθ1 (by nlinarith), hΓe]
    have hk : kU (n * θ) ≤ kU (3 * θ) := kU_anti (by linarith) (by nlinarith)
    have ha : aU (n * θ) ≤ aU (3 * θ) := aU_anti (by linarith) (by nlinarith)
    have hk0 : 0 ≤ kU (n * θ) := (kU_pos (by nlinarith)).le
    have ha0 : 0 ≤ aU (n * θ) := h0 _ (by nlinarith)
    have hΓn : (n : ℝ) ^ 2 * (1 - aU θ / 9) ≤ (n : ℝ) ^ 2 - aU θ := by
      nlinarith [mul_nonneg haθ (by nlinarith : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 9)]
    have hnum : kU (n * θ) / (n * (θ ^ 2 - 1)) + aU (n * θ) / (θ * √(θ ^ 2 - 1))
        ≤ kU (3 * θ) / (n * (θ ^ 2 - 1)) + aU (3 * θ) / (θ * √(θ ^ 2 - 1)) := by
      gcongr
    calc (kU (n * θ) / (n * (θ ^ 2 - 1)) + aU (n * θ) / (θ * √(θ ^ 2 - 1))) / ((n : ℝ) ^ 2 - aU θ)
        ≤ (kU (3 * θ) / (n * (θ ^ 2 - 1)) + aU (3 * θ) / (θ * √(θ ^ 2 - 1)))
            / ((n : ℝ) ^ 2 * (1 - aU θ / 9)) := div_le_div₀ (by positivity) hnum (by positivity) hΓn
      _ = _ := by field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold G3
  apply div_le_div_of_nonneg_right _ hD.le
  have h3 := sum_inv_cube_le N
  have h2 := sum_inv_sq_le N
  have e1 : (zeta3 - 9 / 8) * kU (3 * θ) / (θ ^ 2 - 1) = kU (3 * θ) / (θ ^ 2 - 1) * (zeta3 - 9 / 8) := by ring
  have e2 : (π ^ 2 / 6 - 5 / 4) * aU (3 * θ) / (θ * √(θ ^ 2 - 1))
      = aU (3 * θ) / (θ * √(θ ^ 2 - 1)) * (π ^ 2 / 6 - 5 / 4) := by ring
  rw [e1, e2]
  gcongr

theorem G3_nonneg {θ : ℝ} (hθ : 5 / 4 ≤ θ) : 0 ≤ G3 θ := by
  simpa using sum_cutG_one_le_G3 0 hθ

/-- The row `m = 1`, one `n`: `∫_{5/4}^B ρ_1n ≤ 𝒟(g_1n, A)` for any `A ≥ A_1n` with `θA` nonincreasing. -/
theorem integral_remDensity_one_le {n : ℕ} (hn : 2 ≤ n) {A : ℝ → ℝ}
    (hA : ∀ θ, 5 / 4 ≤ θ → cutA 1 n θ ≤ A θ) (hAa : ∀ a θ, 5 / 4 ≤ a → a ≤ θ → θ * A θ ≤ a * A a)
    {B : ℝ} (hB : 5 / 4 ≤ B) :
    ∫ θ in (5 / 4 : ℝ)..B, remDensity nsRamp nsRamp' 1 n θ ≤ gridSum (cutG 1 n) A := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpm : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 < (1 : ℝ) ^ 2 * θ ^ 2 - 1 := fun θ hθ => by nlinarith
  have hpn : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 < (n : ℝ) ^ 2 * θ ^ 2 - 1 := fun θ hθ => by
    have h1 : 2 * (5 / 4) ≤ (n : ℝ) * θ := mul_le_mul hn2 hθ (by norm_num) (by linarith)
    nlinarith
  have hΓ : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 < cutGamma 1 n θ := fun θ hθ => cutGamma_one_pos hn2 (by nlinarith)
  refine integral_le_gridSum hB (fun b hb => ?_) (fun θ hθ => ?_) (fun θ hθ => ?_) (fun θ hθ => ?_)
    (fun θ hθ => ?_) (fun a θ ha haθ => ?_) hAa
  · apply ContinuousOn.intervalIntegrable_of_Icc hb
    exact continuousOn_remDensity (continuousOn_nsRamp.mono fun θ hθ => mem_Ioi.mpr (by linarith [hθ.1]))
      (continuousOn_nsRamp'.mono fun θ hθ => mem_Ioi.mpr (by linarith [hθ.1]))
      (fun θ hθ => hpm θ hθ.1) (fun θ hθ => hpn θ hθ.1) (fun θ hθ => hΓ θ hθ.1)
  · exact remDensity_nonneg (by linarith) (hpm θ hθ) (hpn θ hθ) (hΓ θ hθ)
  · have h := remDensity_le_cutG_mul (ω := nsRamp) (ω₁ := nsRamp') (m := 1) (n := n) (θ := θ) one_pos
      (by linarith) (by linarith) (hΓ θ hθ)
    have hw' := nsRamp'_nonneg (by linarith : (1 : ℝ) ≤ θ)
    have hw := nsRamp_nonneg (by linarith : (1 : ℝ) ≤ θ)
    have hG := cutG_nonneg (m := 1) (n := n) (θ := θ) one_pos (by linarith) (by linarith) (hΓ θ hθ)
    rw [abs_of_nonneg hw', Real.log_one, zero_sub, abs_neg, abs_of_nonneg hw] at h
    refine h.trans ?_
    have := hA θ hθ
    gcongr
  · exact cutG_nonneg one_pos (by linarith) (by linarith) (hΓ θ hθ)
  · exact (cutA_one_nonneg hn2 hθ).trans (hA θ hθ)
  · exact sq_mul_cutG_le one_pos (by linarith) (by linarith) haθ (hΓ a ha)

theorem kappaBar1_nonneg : 0 ≤ kappaBar1 := by
  have hA2 : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 ≤ cutA 1 2 θ := fun θ hθ => cutA_one_nonneg (by norm_num) hθ
  have hA3 : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 ≤ cutA 1 3 θ := fun θ hθ => cutA_one_nonneg (by norm_num) hθ
  unfold kappaBar1
  have h1 := gridSum_nonneg hA2 fun θ hθ => g12_nonneg hθ
  have h2 := gridSum_nonneg hA3 fun θ hθ => G3_nonneg hθ
  positivity

theorem kappaBar_nonneg : 0 ≤ kappaBar :=
  add_nonneg kappaBar1_nonneg kappaBar2_nonneg

/-- **The row `m = 1` of `κ(X)`**, uniformly in `X`: at most `κ̄₁`. -/
theorem kap_row_one_le (X : ℝ) :
    ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => 1 < n),
        2 * ∫ θ in cutLo (5 / 4) 1..cutHi (5 / 4) X 1 n, remDensity nsRamp nsRamp' 1 n θ
      ≤ kappaBar1 := by
  set N := ⌊X⌋₊ with hN
  have hlo : cutLo (5 / 4) 1 = 5 / 4 := if_pos rfl
  have hhi : ∀ n : ℕ, 5 / 4 ≤ cutHi (5 / 4) X 1 n := fun n => by
    unfold cutHi; rw [hlo]; exact le_max_left _ _
  have hA2 : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 ≤ cutA 1 2 θ := fun θ hθ => cutA_one_nonneg (by norm_num) hθ
  have hA3 : ∀ θ : ℝ, 5 / 4 ≤ θ → 0 ≤ cutA 1 3 θ := fun θ hθ => cutA_one_nonneg (by norm_num) hθ
  set b : ℕ → ℝ := fun n => 2 * gridSum (cutG 1 n) (if n = 2 then cutA 1 2 else cutA 1 3) with hb
  have hterm : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => 1 < n),
      2 * ∫ θ in cutLo (5 / 4) 1..cutHi (5 / 4) X 1 n, remDensity nsRamp nsRamp' 1 n θ ≤ b n := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_filter.mp hn).2
    rw [hlo]
    simp only [hb]
    gcongr
    split_ifs with h
    · subst h
      have := integral_remDensity_one_le (n := 2) le_rfl (A := cutA 1 2) (fun θ _ => by norm_num)
        (fun a θ ha haθ => mul_cutA_one_le (by norm_num) ha haθ) (hhi 2)
      simpa using this
    · exact integral_remDensity_one_le hn2 (fun θ hθ => cutA_one_le_three (by omega) hθ)
        (fun a θ ha haθ => mul_cutA_one_le (by norm_num) ha haθ) (hhi n)
  have hb0 : ∀ n ∈ insert 2 (Finset.Icc 3 N), 0 ≤ b n := by
    intro n hn
    have hn2 : 2 ≤ n := by
      rcases Finset.mem_insert.mp hn with h | h
      · omega
      · exact le_trans (by norm_num) (Finset.mem_Icc.mp h).1
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    simp only [hb]
    refine mul_nonneg (by norm_num) (gridSum_nonneg (fun θ hθ => ?_) fun θ hθ => ?_)
    · split_ifs
      · exact hA2 θ hθ
      · exact hA3 θ hθ
    · exact cutG_nonneg one_pos (by linarith) (by linarith) (cutGamma_one_pos hn2' (by nlinarith))
  have hsub : (Finset.Icc 1 N).filter (fun n => 1 < n) ⊆ insert 2 (Finset.Icc 3 N) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    rcases eq_or_lt_of_le (show 2 ≤ n from hn2) with h | h
    · exact Finset.mem_insert.mpr (Or.inl h.symm)
    · exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨h, (Finset.mem_Icc.mp hn1).2⟩)
  have h2 : b 2 ≤ 2 * gridSum g12 (cutA 1 2) := by
    simp only [hb]
    gcongr
    apply gridSum_le_of_le hA2
    intro θ hθ
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, cutG_one_two_eq (by linarith)]
  have h3 : ∑ n ∈ Finset.Icc 3 N, b n ≤ 2 * gridSum G3 (cutA 1 3) := by
    have e : ∑ n ∈ Finset.Icc 3 N, b n = 2 * gridSum (fun θ => ∑ n ∈ Finset.Icc 3 N, cutG 1 n θ) (cutA 1 3) := by
      rw [← sum_gridSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have : n ≠ 2 := by have := (Finset.mem_Icc.mp hn).1; omega
      simp only [hb, if_neg this]
    rw [e]
    gcongr
    exact gridSum_le_of_le hA3 fun θ hθ => sum_cutG_one_le_G3 N hθ
  have hn2 : (2 : ℕ) ∉ Finset.Icc 3 N := by simp
  calc _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => 1 < n), b n := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ insert 2 (Finset.Icc 3 N), b n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi _ => hb0 i hi
    _ = b 2 + ∑ n ∈ Finset.Icc 3 N, b n := Finset.sum_insert hn2
    _ ≤ kappaBar1 := by unfold kappaBar1; linarith

/-- **`κ(X)` uniformly in `X`**: `kapCount nsRamp nsRamp' (5/4) X ≤ κ̄ = κ̄₁ + 2Σ_{m≥2}σ_mΦ̄_m`. -/
theorem kapCount_nsRamp_le (X : ℝ) : kapCount nsRamp nsRamp' (5 / 4) X ≤ kappaBar := by
  unfold kapCount
  set N := ⌊X⌋₊ with hN
  have hrow : ∀ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m < n),
      2 * ∫ θ in cutLo (5 / 4) m..cutHi (5 / 4) X m n, remDensity nsRamp nsRamp' m n θ
      ≤ (if m = 1 then kappaBar1 else 0) + 2 * (if 2 ≤ m then sigma m * PhiBar m else 0) := by
    intro m hm
    obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
    rcases eq_or_lt_of_le hm1 with h | h
    · subst h
      rw [if_pos rfl, if_neg (by norm_num), Nat.cast_one]
      have := kap_row_one_le X
      linarith
    · rw [if_neg (show m ≠ 1 by omega), if_pos (show 2 ≤ m from h), zero_add]
      have := kap_row_le h X
      linarith
  refine (Finset.sum_le_sum hrow).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
  have hts : ∑ m ∈ Finset.Icc 1 N, (if 2 ≤ m then sigma m * PhiBar m else 0)
      ≤ ∑' m : ℕ, if 2 ≤ m then sigma m * PhiBar m else 0 :=
    summable_sigma_mul_PhiBar.sum_le_tsum _ fun m _ => by
      split_ifs with h
      · exact mul_nonneg (sigma_nonneg m) (PhiBar_nonneg h)
      · exact le_rfl
  have hk1 := kappaBar1_nonneg
  unfold kappaBar kappaBar2
  split_ifs <;> linarith

section NS

open Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.CutWeightResidual
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

variable {ι : Type} [Fintype ι]

/-- **hNS for the NS ramp with `X`-free constants**: `CutEstimateFrameFloor`'s floor form with `Λ̄ = Λ̄₀`, `κ̄ = κ̄₁ + κ̄_{≥2}`. -/
theorem NS_unif_nsRamp {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X κP : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (hκ : 0 < κP)
    (hFF : κP * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    cutNS nsRamp (fun ξ => ∑ i, a i * psi c (g i) ξ) X
      ≤ 0 * (-(cutW nsRamp (fun ξ => ∑ i, a i * psi c (g i) ξ) X))
        + 6 * (Fintype.card ι : ℝ) / c * (LambdaBar0 + kappaBar) / κP
          * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 :=
  NS_of_floor_unif a hg hg₁ hg₂c hang hc hχ0 hχc hX hM (t₁ := 5 / 4) (by norm_num)
    (fun θ hθ => nsRamp_of_le hθ.2) (fun θ hθ => hasDerivAt_nsRamp (by linarith [hθ.1]))
    (continuousOn_nsRamp'.mono fun θ hθ => mem_Ioi.mpr (by linarith [hθ.1])) hκ hFF
    (lamCount_nsRamp_le X) (kapCount_nsRamp_le X)

/-- `(6J/c)(Λ̄₀ + κ̄)/κ_P ≤ (63/40)(Λ̄₀ + κ̄)/κ_P` for `c ≥ 80`, `J ≤ c/4 + 1`. -/
theorem ns_const_le {c J κP : ℝ} (hc : 80 ≤ c) (hJ : J ≤ c / 4 + 1) (hκ : 0 < κP) :
    6 * J / c * (LambdaBar0 + kappaBar) / κP ≤ 63 / 40 * (LambdaBar0 + kappaBar) / κP := by
  have hS : 0 ≤ LambdaBar0 + kappaBar := add_nonneg LambdaBar0_nonneg kappaBar_nonneg
  have h1 : 6 * J / c ≤ 63 / 40 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hS) hκ.le

end NS

end Cvs.L2a.KappaUniformInX
