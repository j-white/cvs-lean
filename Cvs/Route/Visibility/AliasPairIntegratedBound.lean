import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.DilatedModeGreenIdentity
import Cvs.Prolate.ExteriorSpanBernstein
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Route.Visibility.AliasMomentMajorants
import Cvs.Route.Visibility.AliasPairPointwiseBound
import Cvs.Route.Visibility.AliasPairThetaKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The integrated bound for one alias pair

For a weight `w` with `|w| ≤ 1`, `|w′| ≤ 70`, vanishing at `α ≥ 12/25` and at `11/10`, and `q_{kl} ≤ 3/4` on
`[α, 11/10]`, Green's identity (Cvs.Prolate.DilatedModeGreenIdentity) and the pointwise bound (Cvs.Route.Visibility.AliasPairPointwiseBound) give
`∫_α^{11/10} w·h(kθ)h(lθ) ≤ ∫_α^{11/10} N₀ + Γ₀/(c(k − l)²)·∫Σ_N(N + 1)²(3/4)^N Z_N(kθ)Z_N(lθ) + O(M(3/4)^M)`.
-/

noncomputable section

namespace Cvs.Route.Visibility.AliasPairIntegratedBound
open Cvs.ZeroCounting

open Real Set MeasureTheory intervalIntegral
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.Gram.RungGramFloorAtInfinity (rungU)
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP)
open Cvs.Prolate.ExteriorSpanBernstein (IsRungFamily spanH spanU continuous_spanH continuous_spanU)
open Cvs.Route.Visibility.AliasPairThetaKernel (bet Lam qK bet_mem abs_Lam_sub_ge one_lt_of)
open Cvs.Prolate.DilatedModeGreenIdentity (Pk Vk Ak AkD gI Ak_eq green_sum one_lt_mul continuousOn_bet)
open Cvs.Route.Visibility.AliasPairPointwiseBound (eK Hn Dn Zf N0 Rf ω₀ L₀ Γ₀ pair_pointwise)
open Cvs.Route.Visibility.AliasMomentMajorants (continuousOn_Hn continuousOn_Dn)

variable {ι : Type*} [Fintype ι] {c : ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}

/-- `θ ↦ Z_N(kθ)` is continuous on `[12/25, 11/10]`. -/
theorem continuousOn_Zf (hF : IsRungFamily c g g₁ g₂ χ) (b : ι → ℝ) (N : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    ContinuousOn (fun θ => Zf c g χ b N (k * θ)) (Icc (12 / 25) (11 / 10)) := by
  unfold Zf
  exact continuousOn_finsetSum _ fun a _ => ((continuousOn_Hn hF b a k).abs).add ((continuousOn_Dn hF b a hk).abs)

/-- `θ ↦ ψ_i(kθ)` is continuous on `[12/25, 11/10]`. -/
theorem continuousOn_Pk (hF : IsRungFamily c g g₁ g₂ χ) (i : ι) (k : ℕ) :
    ContinuousOn (Pk c (g i) k) (Icc (12 / 25) (11 / 10)) :=
  ((hF.system i).2.2.1.comp (continuous_const.mul continuous_id)).continuousOn

/-- `θ ↦ ψ_i′(kθ)` is continuous on `[12/25, 11/10]` for `k ≥ 3`. -/
theorem continuousOn_Vk (hF : IsRungFamily c g g₁ g₂ χ) (i : ι) {k : ℕ} (hk : 3 ≤ k) :
    ContinuousOn (Vk c (g i) k) (Icc (12 / 25) (11 / 10)) := by
  unfold Vk
  refine ContinuousOn.div ?_ ?_ fun θ hθ => (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (one_lt_mul hk hθ.1)).ne'
  · exact ((hF.system i).2.2.2.comp (continuous_const.mul continuous_id)).continuousOn
  · exact (by unfold pP; fun_prop : Continuous fun θ : ℝ => pP (k * θ)).continuousOn

/-- The remainder mass is continuous on `[12/25, 11/10]`. -/
theorem continuousOn_Rf (hF : IsRungFamily c g g₁ g₂ χ) (b : ι → ℝ) {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) :
    ContinuousOn (fun θ => Rf c g b k l θ) (Icc (12 / 25) (11 / 10)) := by
  unfold Rf
  refine ContinuousOn.mul (continuousOn_finsetSum _ fun i _ => ?_) (continuousOn_finsetSum _ fun j _ => ?_)
  · exact ((continuousOn_const.mul (continuousOn_Vk hF i hk)).abs).add
      ((continuousOn_const.mul (continuousOn_Pk hF i k)).abs)
  · exact ((continuousOn_const.mul (continuousOn_Vk hF j hl)).abs).add
      ((continuousOn_const.mul (continuousOn_Pk hF j l)).abs)

omit [Fintype ι] in
/-- With `q_{kl} ≤ 3/4` the pair denominators `A_k − A_l` do not vanish. -/
theorem Ak_sub_ne_zero (hc : 0 < c) (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2) {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l)
    (hkl : k ≠ l) {θ : ℝ} (hθ : 12 / 25 ≤ θ) (hq : qK k l θ ≤ 3 / 4) (i j : ι) :
    Ak c (χ i) k θ - Ak c (χ j) l θ ≠ 0 := by
  have hk2 : (k : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0 := by have := one_lt_of hk hθ; intro h; linarith
  have hl2 : (l : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0 := by have := one_lt_of hl hθ; intro h; linarith
  have hbk := bet_mem hk hθ
  have hbl := bet_mem hl hθ
  have hd : 0 < |(k : ℝ) ^ 2 - (l : ℝ) ^ 2| := by
    refine abs_pos.mpr fun h => hkl ?_
    have : (k : ℝ) ^ 2 = (l : ℝ) ^ 2 := by linarith
    exact_mod_cast (sq_eq_sq₀ (Nat.cast_nonneg k) (Nat.cast_nonneg l)).mp this
  have hL : 0 < |Lam k θ - Lam l θ| := lt_of_lt_of_le (by positivity) (abs_Lam_sub_ge hk hl hθ)
  rw [Ak_eq _ hk2, Ak_eq _ hl2]
  have he : ∀ i, |c ^ 2 / 2 - χ i| ≤ c ^ 2 / 2 := fun i => by
    rw [abs_le]; constructor <;> linarith [(hχ i).1, (hχ i).2]
  have hpert : |bet k θ * (c ^ 2 / 2 - χ i) - bet l θ * (c ^ 2 / 2 - χ j)| ≤ c ^ 2 / 2 * (bet k θ + bet l θ) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hbk.1, abs_of_pos hbl.1]
    nlinarith [he i, he j, hbk.1, hbl.1]
  have hqq : c ^ 2 / 2 * (bet k θ + bet l θ) ≤ 3 / 4 * (c ^ 2 * |Lam k θ - Lam l θ|) := by
    have : (bet k θ + bet l θ) / (2 * |Lam k θ - Lam l θ|) ≤ 3 / 4 := hq
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith [sq_nonneg c]
  intro h0
  have : |c ^ 2 * (Lam k θ - Lam l θ)| ≤ |bet k θ * (c ^ 2 / 2 - χ i) - bet l θ * (c ^ 2 / 2 - χ j)| := by
    rw [show c ^ 2 * (Lam k θ - Lam l θ) = -(bet k θ * (c ^ 2 / 2 - χ i) - bet l θ * (c ^ 2 / 2 - χ j)) by
      linarith, abs_neg]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c ^ 2)] at this
  have hc2 : 0 < c ^ 2 * |Lam k θ - Lam l θ| := by positivity
  linarith

/-- The leading term of a pair is interval integrable against a continuous weight with integrable derivative. -/
theorem N0_intervalIntegrable (hF : IsRungFamily c g g₁ g₂ χ) (hc0 : 0 < c) (b : ι → ℝ) {k l : ℕ} (hk : 3 ≤ k)
    (hl : 3 ≤ l)
    (hkl : k ≠ l) {α : ℝ} (hα : 12 / 25 ≤ α) (hα1 : α ≤ 11 / 10) {w w' : ℝ → ℝ}
    (hwc : ContinuousOn w (Icc α (11 / 10))) (hw'i : IntervalIntegrable w' volume α (11 / 10)) :
    IntervalIntegrable (N0 c g b w w' k l) volume α (11 / 10) := by
  have hθI : ∀ θ ∈ Icc α (11 / 10), 12 / 25 ≤ θ := fun θ h => hα.trans h.1
  have hsub : Icc α (11 / 10) ⊆ Icc (12 / 25) (11 / 10) := Icc_subset_Icc hα le_rfl
  have hUc : ∀ m : ℕ, 3 ≤ m → ContinuousOn (fun θ => spanU c g b (m * θ) / pP (m * θ)) (Icc α (11 / 10)) :=
    fun m hm => (((continuous_spanU hF b).comp (continuous_const.mul continuous_id)).continuousOn.div
      (by unfold pP; fun_prop : Continuous fun θ : ℝ => pP (m * θ)).continuousOn
      fun θ h => (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (one_lt_mul hm (hθI θ h))).ne')
  have hHc : ∀ m : ℕ, ContinuousOn (fun θ => spanH c g b (m * θ)) (Icc α (11 / 10)) :=
    fun m => ((continuous_spanH hF b).comp (continuous_const.mul continuous_id)).continuousOn
  have hLc : ContinuousOn (fun θ => c ^ 2 * (Lam k θ - Lam l θ)) (Icc α (11 / 10)) := by
    unfold Lam
    exact continuousOn_const.mul ((continuousOn_const.add ((continuousOn_bet hk hθI).div_const _)).sub
      (continuousOn_const.add ((continuousOn_bet hl hθI).div_const _)))
  have hL0 : ∀ θ ∈ Icc α (11 / 10), c ^ 2 * (Lam k θ - Lam l θ) ≠ 0 := by
    intro θ h
    have hd : 0 < |(k : ℝ) ^ 2 - (l : ℝ) ^ 2| := by
      refine abs_pos.mpr fun h' => hkl ?_
      have : (k : ℝ) ^ 2 = (l : ℝ) ^ 2 := by linarith
      exact_mod_cast (sq_eq_sq₀ (Nat.cast_nonneg k) (Nat.cast_nonneg l)).mp this
    have := abs_Lam_sub_ge hk hl (hθI θ h)
    exact mul_ne_zero (by positivity) (abs_pos.mp (lt_of_lt_of_le (by positivity) this))
  have hP1 : ContinuousOn (fun θ => ((k : ℝ) * (spanU c g b (k * θ) / pP (k * θ) * spanH c g b (l * θ))
      - l * (spanH c g b (k * θ) * (spanU c g b (l * θ) / pP (l * θ)))) / (c ^ 2 * (Lam k θ - Lam l θ)))
      (Icc α (11 / 10)) :=
    ((continuousOn_const.mul ((hUc k hk).mul (hHc l))).sub
      (continuousOn_const.mul ((hHc k).mul (hUc l hl)))).div hLc hL0
  have hP2 : ContinuousOn (fun θ => ((-2 * w θ * θ * bet k θ) * k
        * (spanU c g b (k * θ) / pP (k * θ) * spanH c g b (l * θ))
      - (-2 * w θ * θ * bet l θ) * l * (spanH c g b (k * θ) * (spanU c g b (l * θ) / pP (l * θ))))
        / (c ^ 2 * (Lam k θ - Lam l θ))) (Icc α (11 / 10)) := by
    refine ContinuousOn.div (ContinuousOn.sub ?_ ?_) hLc hL0
    · exact ((((continuousOn_const.mul hwc).mul continuousOn_id).mul (continuousOn_bet hk hθI)).mul
        continuousOn_const).mul ((hUc k hk).mul (hHc l))
    · exact ((((continuousOn_const.mul hwc).mul continuousOn_id).mul (continuousOn_bet hl hθI)).mul
        continuousOn_const).mul ((hHc k).mul (hUc l hl))
  have h1 := hw'i.mul_continuousOn (by rw [uIcc_of_le hα1]; exact hP1)
  have h2 := hP2.intervalIntegrable_of_Icc (μ := volume) hα1
  refine (h1.add h2).congr fun θ _ => ?_
  simp only [N0]
  ring

/-- **The integrated pair bound**: the pair integral is its leading integral plus the integrated majorant of Cvs.Route.Visibility.AliasPairPointwiseBound. -/
theorem pair_integral_le (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2)
    (b : ι → ℝ) {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) (hkl : k ≠ l) {α : ℝ} (hα : 12 / 25 ≤ α) (hα1 : α ≤ 11 / 10)
    {E : Set ℝ} (hE : E.Countable) {w w' : ℝ → ℝ} (hwc : ContinuousOn w (Icc α (11 / 10)))
    (hwd : ∀ θ ∈ Ioo α (11 / 10) \ E, HasDerivAt w (w' θ) θ) (hwm : Measurable w') (hwα : w α = 0)
    (hwβ : w (11 / 10) = 0) (hwb : ∀ θ, |w θ| ≤ 1) (hw'b : ∀ θ, |w' θ| ≤ 70)
    (hq : ∀ θ ∈ Icc α (11 / 10), qK k l θ ≤ 3 / 4) {M : ℕ} (hM : 1 ≤ M) :
    ∫ θ in α..(11 / 10), w θ * (spanH c g b (k * θ) * spanH c g b (l * θ))
      ≤ (∫ θ in α..(11 / 10), N0 c g b w w' k l θ)
        + (Γ₀ / (c * ((k : ℝ) - l) ^ 2) * (∫ θ in (12 / 25 : ℝ)..(11 / 10), ∑ N ∈ Finset.range M,
            ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)))
          + (k + l) * (8 * ω₀ + 192 * L₀) / c ^ 2 * ((2 * M + 1) * (3 / 4) ^ M)
            * ∫ θ in (12 / 25 : ℝ)..(11 / 10), Rf c g b k l θ) := by
  have hc0 : 0 < c := by linarith
  have hθI : ∀ θ ∈ Icc α (11 / 10), 12 / 25 ≤ θ := fun θ h => hα.trans h.1
  have hw'i : IntervalIntegrable w' volume α (11 / 10) :=
    (intervalIntegrable_const (c := (70 : ℝ))).mono_fun' hwm.aestronglyMeasurable
      (ae_of_all _ fun θ => by simpa using hw'b θ)
  have hD0 : ∀ i j, ∀ θ ∈ Icc α (11 / 10), Ak c (χ i) k θ - Ak c (χ j) l θ ≠ 0 := fun i j θ h =>
    Ak_sub_ne_zero hc0 hχ hk hl hkl (hθI θ h) (hq θ h) i j
  have hG := green_sum hF b hk hl hα hα1 hE hwc hwd hw'i hwα hwβ hD0
  rw [hG.2]
  have hsub : Icc α (11 / 10) ⊆ Icc (12 / 25) (11 / 10) := Icc_subset_Icc hα le_rfl
  have hN0i := N0_intervalIntegrable hF hc0 b hk hl hkl hα hα1 hwc hw'i
  -- the deviation from the leading term
  set I := fun θ => ∑ i, ∑ j, b i * b j * gI c (g i) (g j) (χ i) (χ j) w w' k l θ with hIdef
  set S : ℝ → ℝ := fun θ => ∑ N ∈ Finset.range M,
    ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) with hSdef
  set C2 : ℝ := (k + l) * (8 * ω₀ + 192 * L₀) / c ^ 2 with hC2
  set T : ℝ := (2 * M + 1) * (3 / 4) ^ M with hT
  set maj : ℝ → ℝ := fun θ => Γ₀ / (c * ((k : ℝ) - l) ^ 2) * S θ + C2 * (T * Rf c g b k l θ) with hmaj
  have hSc : ContinuousOn S (Icc (12 / 25) (11 / 10)) :=
    continuousOn_finsetSum _ fun N _ => continuousOn_const.mul
      ((continuousOn_Zf hF b N hk).mul (continuousOn_Zf hF b N hl))
  have hmajc : ContinuousOn maj (Icc (12 / 25) (11 / 10)) :=
    (continuousOn_const.mul hSc).add (continuousOn_const.mul (continuousOn_const.mul (continuousOn_Rf hF b hk hl)))
  have hS0 : ∀ θ, 0 ≤ S θ := fun θ => Finset.sum_nonneg fun N _ => mul_nonneg (by positivity)
    (mul_nonneg (Finset.sum_nonneg fun a _ => by positivity) (Finset.sum_nonneg fun a _ => by positivity))
  have hR0 : ∀ θ, 0 ≤ Rf c g b k l θ := fun θ => by unfold Rf; positivity
  have hΓ0 : 0 ≤ Γ₀ := by simp only [Γ₀, ω₀, L₀, Cvs.Route.Visibility.AliasPairPointwiseBound.βb]; norm_num
  have hC20 : 0 ≤ C2 := by simp only [hC2, ω₀, L₀, Cvs.Route.Visibility.AliasPairPointwiseBound.βb]; positivity
  have hT0 : 0 ≤ T := by positivity
  have hmaj0 : ∀ θ, 0 ≤ maj θ := fun θ => add_nonneg (mul_nonneg (by positivity) (hS0 θ))
    (mul_nonneg hC20 (mul_nonneg hT0 (hR0 θ)))
  have hdev : ∫ θ in α..(11 / 10), (I θ - N0 c g b w w' k l θ) ≤ ∫ θ in α..(11 / 10), maj θ := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hα1 (ae_of_all _ fun θ hθ => ?_)
      ((hmajc.mono hsub).intervalIntegrable_of_Icc hα1)
    have hθ' : θ ∈ Icc α (11 / 10) := Ioc_subset_Icc_self hθ
    rw [Real.norm_eq_abs]
    exact pair_pointwise hc0 g hχ b hk hl hkl (hθI θ hθ') hθ'.2 (hq θ hθ') (hwb θ) (hw'b θ) hM
  have hext : ∫ θ in α..(11 / 10), maj θ ≤ ∫ θ in (12 / 25 : ℝ)..(11 / 10), maj θ :=
    intervalIntegral.integral_mono_interval hα hα1 le_rfl (ae_of_all _ fun θ => hmaj0 θ)
      (hmajc.intervalIntegrable_of_Icc (by norm_num))
  have hsplit : ∫ θ in (12 / 25 : ℝ)..(11 / 10), maj θ
      = Γ₀ / (c * ((k : ℝ) - l) ^ 2) * (∫ θ in (12 / 25 : ℝ)..(11 / 10), S θ)
        + C2 * T * ∫ θ in (12 / 25 : ℝ)..(11 / 10), Rf c g b k l θ := by
    have h1 : IntervalIntegrable (fun θ => Γ₀ / (c * ((k : ℝ) - l) ^ 2) * S θ) volume (12 / 25) (11 / 10) :=
      (continuousOn_const.mul hSc).intervalIntegrable_of_Icc (by norm_num)
    have h2 : IntervalIntegrable (fun θ => C2 * (T * Rf c g b k l θ)) volume (12 / 25) (11 / 10) :=
      (continuousOn_const.mul (continuousOn_const.mul (continuousOn_Rf hF b hk hl))).intervalIntegrable_of_Icc
        (by norm_num)
    simp only [hmaj]
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  have hsubI : ∫ θ in α..(11 / 10), (I θ - N0 c g b w w' k l θ)
      = (∫ θ in α..(11 / 10), I θ) - ∫ θ in α..(11 / 10), N0 c g b w w' k l θ :=
    intervalIntegral.integral_sub hG.1 hN0i
  have hfin := hdev.trans (hext.trans_eq hsplit)
  rw [hsubI] at hfin
  have e1 : (∫ θ in α..(11 / 10), I θ) = intervalIntegral I α (11 / 10) volume := rfl
  have e2 : (∫ θ in (12 / 25 : ℝ)..(11 / 10), S θ) = ∫ θ in (12 / 25 : ℝ)..(11 / 10), ∑ N ∈ Finset.range M,
      ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * (Zf c g χ b N (k * θ) * Zf c g χ b N (l * θ)) := rfl
  rw [e1, e2] at hfin
  linarith

end Cvs.Route.Visibility.AliasPairIntegratedBound
