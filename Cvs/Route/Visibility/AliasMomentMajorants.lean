import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.DilatedModeGreenIdentity
import Cvs.Prolate.ExteriorSpanBernstein
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Route.Visibility.AliasKernelHilbertInequality
import Cvs.Route.Visibility.AliasPairPointwiseBound
import Cvs.Route.Visibility.AliasPairThetaKernel
import Cvs.Upstream.PairSumPowerDecoupling

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The integrated moment majorants and the leading alias terms

Through Cvs.Prolate.ExteriorSpanBernstein every level moment has `Σ_k∫_{12/25}^{11/10}(H_a(kθ)² + D_a(kθ)²) ≤ 30∫_{(1,∞)}h²`, so
`∫Σ_kZ_N(kθ)² ≤ 60(N + 2)²∫h²`; Schur's test for `1/(k − l)²` costs `4`, `Σ(N + 1)²(N + 2)²(3/4)^N ≤ 24·4⁵`, a
single leading term is at most `(ω₀/c)(E₀(kθ) + E₀(lθ))`, and by Cvs.Route.Visibility.AliasKernelHilbertInequality all of them together at most `(C_H/c)Σ_kE₀(kθ)`.
-/

noncomputable section

namespace Cvs.Route.Visibility.AliasMomentMajorants
open Cvs.ZeroCounting

open Real Set Finset MeasureTheory intervalIntegral
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.Gram.RungGramFloorAtInfinity (rungU)
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP)
open Cvs.Prolate.ExteriorSpanBernstein (IsRungFamily spanH spanU continuous_spanH continuous_spanU sum_integral_energy_le integral_spanH_mul_sq_le)
open Cvs.Route.Visibility.AliasPairThetaKernel (bet Lam bet_mem abs_Lam_sub_ge)
open Cvs.Route.Visibility.AliasPairPointwiseBound (eK Hn Dn Zf N0 ω₀ βb)

variable {ι : Type*} [Fintype ι] {c : ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}

/-- `θ ↦ H_a(kθ)` is continuous on `[12/25, 11/10]`. -/
theorem continuousOn_Hn (hF : IsRungFamily c g g₁ g₂ χ) (b : ι → ℝ) (a k : ℕ) :
    ContinuousOn (fun θ => Hn c g χ b a (k * θ)) (Icc (12 / 25) (11 / 10)) :=
  (((continuous_spanH hF _).comp (continuous_const.mul continuous_id)).div_const _).continuousOn

/-- `θ ↦ D_a(kθ)` is continuous on `[12/25, 11/10]` for `k ≥ 3`. -/
theorem continuousOn_Dn (hF : IsRungFamily c g g₁ g₂ χ) (b : ι → ℝ) (a : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    ContinuousOn (fun θ => Dn c g χ b a (k * θ)) (Icc (12 / 25) (11 / 10)) := by
  unfold Dn
  refine ContinuousOn.div_const (ContinuousOn.div ?_ ?_ fun θ hθ => ?_) _
  · exact ((continuous_spanU hF _).comp (continuous_const.mul continuous_id)).continuousOn
  · exact (by unfold pP; fun_prop : Continuous fun θ : ℝ => pP (k * θ)).continuousOn
  · exact (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos (Cvs.Prolate.DilatedModeGreenIdentity.one_lt_mul hk hθ.1)).ne'

/-- **The level moments carry at most `30` times the exterior mass** through the dilations. -/
theorem sum_integral_moment_le (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2)
    (hinj : Function.Injective χ) (b : ι → ℝ) (a : ℕ) {K : ℕ} (hK : 3 ≤ K) :
    ∑ k ∈ Finset.Icc 3 K, ∫ θ in (12 / 25 : ℝ)..(11 / 10), (Hn c g χ b a (k * θ) ^ 2 + Dn c g χ b a (k * θ) ^ 2)
      ≤ 30 * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2 := by
  have hc0 : 0 < c := by linarith
  set r : ℝ := c ^ 2 / 2 with hr
  have hr0 : 0 < r := by positivity
  set f : ι → ℝ := fun i => b i * eK c χ i ^ a with hf
  have he : ∀ i, |eK c χ i ^ a| ≤ r ^ a := fun i => by
    rw [abs_pow]; refine pow_le_pow_left₀ (abs_nonneg _) ?_ a
    simp only [eK, hr]; rw [_root_.abs_le]; constructor <;> linarith [(hχ i).1, (hχ i).2]
  have hmass := integral_spanH_mul_sq_le hF hc0 hinj b (fun i => eK c χ i ^ a) he
  have hE := sum_integral_energy_le hF hc (fun i => (hχ i).1) (fun i => (hχ i).2) hinj f hK
  have hra : 0 < (r ^ a) ^ 2 := by positivity
  have e : ∀ k ∈ Finset.Icc 3 K, ∫ θ in (12 / 25 : ℝ)..(11 / 10), (Hn c g χ b a (k * θ) ^ 2 + Dn c g χ b a (k * θ) ^ 2)
      = (∫ θ in (12 / 25 : ℝ)..(11 / 10),
          (spanH c g f (k * θ) ^ 2 + (spanU c g f (k * θ) / pP (k * θ)) ^ 2 / c ^ 2)) / (r ^ a) ^ 2 := by
    intro k _
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Hn, Dn, hf, hr]
    field_simp
  rw [Finset.sum_congr rfl e, ← Finset.sum_div, div_le_iff₀ hra]
  calc _ ≤ 30 * ∫ ξ in Ioi 1, spanH c g f ξ ^ 2 := hE
    _ ≤ 30 * ((r ^ a) ^ 2 * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ = 30 * (∫ ξ in Ioi 1, spanH c g b ξ ^ 2) * (r ^ a) ^ 2 := by ring

/-- `Z_N(t)² ≤ 2(N + 2)Σ_{a ≤ N+1}(H_a(t)² + D_a(t)²)`. -/
theorem Zf_sq_le (b : ι → ℝ) (N : ℕ) (t : ℝ) :
    Zf c g χ b N t ^ 2 ≤ 2 * ((N : ℝ) + 2) * ∑ a ∈ range (N + 2), (Hn c g χ b a t ^ 2 + Dn c g χ b a t ^ 2) := by
  unfold Zf
  have h := sq_sum_le_card_mul_sum_sq (s := range (N + 2)) (f := fun a => |Hn c g χ b a t| + |Dn c g χ b a t|)
  rw [Finset.card_range] at h
  refine h.trans ?_
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have : (|Hn c g χ b a t| + |Dn c g χ b a t|) ^ 2 ≤ 2 * (Hn c g χ b a t ^ 2 + Dn c g χ b a t ^ 2) := by
    nlinarith [sq_abs (Hn c g χ b a t), sq_abs (Dn c g χ b a t), sq_nonneg (|Hn c g χ b a t| - |Dn c g χ b a t|)]
  nlinarith

/-- **The integrated moment majorant**: `∫_{12/25}^{11/10} Σ_k Z_N(kθ)² ≤ 60(N + 2)²∫_{(1,∞)} h²`. -/
theorem integral_sum_Zf_sq_le (hF : IsRungFamily c g g₁ g₂ χ) (hc : 3 ≤ c) (hχ : ∀ i, 0 ≤ χ i ∧ χ i ≤ c ^ 2)
    (hinj : Function.Injective χ) (b : ι → ℝ) (N : ℕ) {K : ℕ} (hK : 3 ≤ K) :
    ∫ θ in (12 / 25 : ℝ)..(11 / 10), ∑ k ∈ Finset.Icc 3 K, Zf c g χ b N (k * θ) ^ 2
      ≤ 60 * ((N : ℝ) + 2) ^ 2 * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2 := by
  have hcont : ∀ a, ∀ k ∈ Finset.Icc 3 K,
      ContinuousOn (fun θ => Hn c g χ b a (k * θ) ^ 2 + Dn c g χ b a (k * θ) ^ 2) (Icc (12 / 25) (11 / 10)) :=
    fun a k hk => ((continuousOn_Hn hF b a k).pow 2).add
      ((continuousOn_Dn hF b a (Finset.mem_Icc.mp hk).1).pow 2)
  have hint : ∀ a, ∀ k ∈ Finset.Icc 3 K, IntervalIntegrable
      (fun θ => Hn c g χ b a (k * θ) ^ 2 + Dn c g χ b a (k * θ) ^ 2) volume (12 / 25) (11 / 10) :=
    fun a k hk => (hcont a k hk).intervalIntegrable_of_Icc (by norm_num)
  have hZc : ∀ k ∈ Finset.Icc 3 K, ContinuousOn (fun θ => Zf c g χ b N (k * θ)) (Icc (12 / 25) (11 / 10)) := by
    intro k hk
    unfold Zf
    exact continuousOn_finsetSum _ fun a _ =>
      ((continuousOn_Hn hF b a k).abs).add ((continuousOn_Dn hF b a (Finset.mem_Icc.mp hk).1).abs)
  have hle : ∀ θ ∈ Icc (12 / 25 : ℝ) (11 / 10), ∑ k ∈ Finset.Icc 3 K, Zf c g χ b N (k * θ) ^ 2
      ≤ 2 * ((N : ℝ) + 2) * ∑ a ∈ range (N + 2), ∑ k ∈ Finset.Icc 3 K,
          (Hn c g χ b a (k * θ) ^ 2 + Dn c g χ b a (k * θ) ^ 2) := by
    intro θ _
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => Zf_sq_le b N (k * θ)
  refine (intervalIntegral.integral_mono_on (by norm_num)
    ((continuousOn_finsetSum _ fun k hk => (hZc k hk).pow 2).intervalIntegrable_of_Icc (by norm_num)) ?_ hle).trans ?_
  · refine ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (continuousOn_const.mul ?_)
    have hc2 : ContinuousOn (fun θ => ∑ a ∈ range (N + 2), ∑ k ∈ Finset.Icc 3 K,
        (Hn c g χ b a (k * θ) ^ 2 + Dn c g χ b a (k * θ) ^ 2)) (Icc (12 / 25) (11 / 10)) :=
      continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun k hk => hcont a k hk
    exact hc2
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun a _ =>
    IntervalIntegrable.sum _ (fun k hk => hint a k hk) |>.congr fun θ _ => by simp [Finset.sum_apply]]
  have hsum : ∀ a ∈ range (N + 2), ∫ θ in (12 / 25 : ℝ)..(11 / 10), ∑ k ∈ Finset.Icc 3 K,
      (Hn c g χ b a (k * θ) ^ 2 + Dn c g χ b a (k * θ) ^ 2) ≤ 30 * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2 := by
    intro a _
    rw [intervalIntegral.integral_finsetSum fun k hk => hint a k hk]
    exact sum_integral_moment_le hF hc hχ hinj b a hK
  have hN0 : 0 ≤ 2 * ((N : ℝ) + 2) := by positivity
  calc 2 * ((N : ℝ) + 2) * ∑ a ∈ range (N + 2), ∫ θ in (12 / 25 : ℝ)..(11 / 10), ∑ k ∈ Finset.Icc 3 K,
        (Hn c g χ b a (k * θ) ^ 2 + Dn c g χ b a (k * θ) ^ 2)
      ≤ 2 * ((N : ℝ) + 2) * ∑ _a ∈ range (N + 2), 30 * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsum) hN0
    _ = 60 * ((N : ℝ) + 2) ^ 2 * ∫ ξ in Ioi 1, spanH c g b ξ ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- **Schur's test for the kernel `1/(k − l)²`**: `Σ_{k≠l} z_kz_l/(k − l)² ≤ 4Σ_k z_k²`. -/
theorem schur_inv_sq (S : Finset ℕ) (z : ℕ → ℝ) :
    ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else z k * z l / ((k : ℝ) - l) ^ 2) ≤ 4 * ∑ k ∈ S, z k ^ 2 := by
  have hpt : ∀ k l : ℕ, (if k = l then 0 else z k * z l / ((k : ℝ) - l) ^ 2)
      ≤ z k ^ 2 / 2 * (if l = k then 0 else 1 / ((k : ℝ) - l) ^ 2)
        + z l ^ 2 / 2 * (if k = l then 0 else 1 / ((l : ℝ) - k) ^ 2) := by
    intro k l
    by_cases h : k = l
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), ite_eq_right h]
      have hne : (k : ℝ) - l ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
      have hd : 0 < ((k : ℝ) - l) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
      rw [show ((l : ℝ) - k) ^ 2 = ((k : ℝ) - l) ^ 2 by ring]
      have : z k * z l ≤ z k ^ 2 / 2 + z l ^ 2 / 2 := by nlinarith [sq_nonneg (z k - z l)]
      rw [show z k ^ 2 / 2 * (1 / ((k : ℝ) - l) ^ 2) + z l ^ 2 / 2 * (1 / ((k : ℝ) - l) ^ 2)
        = (z k ^ 2 / 2 + z l ^ 2 / 2) / ((k : ℝ) - l) ^ 2 by ring]
      exact div_le_div_of_nonneg_right this hd.le
  calc _ ≤ ∑ k ∈ S, ∑ l ∈ S, (z k ^ 2 / 2 * (if l = k then 0 else 1 / ((k : ℝ) - l) ^ 2)
        + z l ^ 2 / 2 * (if k = l then 0 else 1 / ((l : ℝ) - k) ^ 2)) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hpt k l
    _ = ∑ k ∈ S, z k ^ 2 / 2 * ∑ l ∈ S, (if l = k then 0 else 1 / ((k : ℝ) - l) ^ 2)
        + ∑ l ∈ S, z l ^ 2 / 2 * ∑ k ∈ S, (if k = l then 0 else 1 / ((l : ℝ) - k) ^ 2) := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · simp only [Finset.mul_sum]
        · rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ k ∈ S, z k ^ 2 / 2 * 4 + ∑ l ∈ S, z l ^ 2 / 2 * 4 := by
        gcongr with k _ l _
        · exact Cvs.Upstream.PairSumPowerDecoupling.sum_inv_sq_sub_le S k
        · exact Cvs.Upstream.PairSumPowerDecoupling.sum_inv_sq_sub_le S l
    _ = 4 * ∑ k ∈ S, z k ^ 2 := by rw [← Finset.sum_add_distrib, Finset.mul_sum]; ring_nf

/-- `Σ_{N<M}(N + 1)²(N + 2)²(3/4)^N ≤ 24·4⁵`. -/
theorem sum_series_le (M : ℕ) :
    ∑ N ∈ range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * ((N : ℝ) + 2) ^ 2 ≤ 24 * 4 ^ 5 := by
  have h := Cvs.Upstream.PairSumPowerDecoupling.sum_choose_mul_pow_le 4 (q := 3 / 4) (by norm_num) (by norm_num) M
  have hc : ∀ N : ℕ, ((N : ℝ) + 1) ^ 2 * ((N : ℝ) + 2) ^ 2 ≤ 24 * ((N + 4).choose 4 : ℝ) := by
    intro N
    have h1 := Nat.descFactorial_eq_factorial_mul_choose (N + 4) 4
    have h2 : ((N + 4).descFactorial 4 : ℝ) = ((N : ℝ) + 4) * (N + 3) * (N + 2) * (N + 1) := by
      simp [Nat.descFactorial_succ]; ring
    have h3 : ((N + 4).descFactorial 4 : ℝ) = 24 * ((N + 4).choose 4 : ℝ) := by
      rw [h1]; push_cast; simp [Nat.factorial]
    nlinarith [sq_nonneg ((N : ℝ) + 1), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  calc ∑ N ∈ range M, ((N : ℝ) + 1) ^ 2 * (3 / 4) ^ N * ((N : ℝ) + 2) ^ 2
      ≤ ∑ N ∈ range M, 24 * (((N + 4).choose 4 : ℝ) * (3 / 4) ^ N) := by
        refine Finset.sum_le_sum fun N _ => ?_
        have := hc N
        have hq : (0 : ℝ) ≤ (3 / 4) ^ N := by positivity
        nlinarith
    _ = 24 * ∑ N ∈ range M, ((N + 4).choose 4 : ℝ) * (3 / 4) ^ N := by rw [Finset.mul_sum]
    _ ≤ 24 * (1 / (1 - 3 / 4) ^ (4 + 1)) := by gcongr
    _ = 24 * 4 ^ 5 := by norm_num

/-- `H₀ = h`. -/
theorem Hn_zero (b : ι → ℝ) (t : ℝ) : Hn c g χ b 0 t = spanH c g b t := by
  simp [Hn, spanH]

/-- `cD₀ = h′ = U/(ξ² − 1)`. -/
theorem Dn_zero (hc : 0 < c) (b : ι → ℝ) (t : ℝ) : c * Dn c g χ b 0 t = spanU c g b t / pP t := by
  simp only [Dn, pow_zero, mul_one, spanU]
  field_simp

/-- `|ω̃| ≤ ω₀` for the window coefficient `w′ − 2wθβ_k`. -/
theorem abs_wcoef_le {k : ℕ} (hk : 3 ≤ k) {θ w w' : ℝ} (hθ : 12 / 25 ≤ θ) (hθ1 : θ ≤ 11 / 10) (hw : |w| ≤ 1)
    (hw' : |w'| ≤ 70) : |w' - 2 * w * θ * bet k θ| ≤ ω₀ := by
  have hb := bet_mem hk hθ
  have hθ0 : 0 ≤ θ := by linarith
  calc |w' - 2 * w * θ * bet k θ| ≤ |w'| + |2 * w * θ * bet k θ| := abs_sub _ _
    _ = |w'| + 2 * |w| * θ * bet k θ := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hθ0,
          abs_of_nonneg hb.1.le]
    _ ≤ 70 + 2 * 1 * (11 / 10) * (5625 / 671) := by
        have h1 : 2 * |w| ≤ 2 * 1 := mul_le_mul_of_nonneg_left hw (by norm_num)
        have h2 : 2 * |w| * θ ≤ 2 * 1 * (11 / 10) := mul_le_mul h1 hθ1 hθ0 (by norm_num)
        have h3 : 2 * |w| * θ * bet k θ ≤ 2 * 1 * (11 / 10) * (5625 / 671) :=
          mul_le_mul h2 hb.2 hb.1.le (by norm_num)
        linarith
    _ = ω₀ := by simp only [ω₀, βb]; norm_num

/-- **A single leading term**: `|N₀(k, l)| ≤ (ω₀/c)(E₀(kθ) + E₀(lθ))` with `E₀ = H₀² + D₀²`. -/
theorem abs_N0_le (hc : 0 < c) (b : ι → ℝ) {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) (hkl : k ≠ l) {θ : ℝ}
    (hθ : 12 / 25 ≤ θ) (hθ1 : θ ≤ 11 / 10) {w w' : ℝ → ℝ} (hw : |w θ| ≤ 1) (hw' : |w' θ| ≤ 70) :
    |N0 c g b w w' k l θ| ≤ ω₀ / c * ((Hn c g χ b 0 (k * θ) ^ 2 + Dn c g χ b 0 (k * θ) ^ 2)
      + (Hn c g χ b 0 (l * θ) ^ 2 + Dn c g χ b 0 (l * θ) ^ 2)) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  set Hk := Hn c g χ b 0 (k * θ)
  set Hl := Hn c g χ b 0 (l * θ)
  set Dk := Dn c g χ b 0 (k * θ)
  set Dl := Dn c g χ b 0 (l * θ)
  have hgap := abs_Lam_sub_ge hk hl hθ
  have hd : ((k : ℝ) + l) / 2 ≤ |Lam k θ - Lam l θ| := by
    refine le_trans ?_ hgap
    rw [show (k : ℝ) ^ 2 - (l : ℝ) ^ 2 = ((k : ℝ) - l) * (k + l) by ring, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ k + l)]
    have : (1 : ℝ) ≤ |(k : ℝ) - l| := by
      rcases lt_or_gt_of_ne hkl with h | h
      · have : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
      · have : (l : ℝ) + 1 ≤ k := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
    nlinarith
  have hpos : 0 < |Lam k θ - Lam l θ| := lt_of_lt_of_le (by linarith) hd
  have ha := abs_wcoef_le hk hθ hθ1 hw hw'
  have hb := abs_wcoef_le hl hθ hθ1 hw hw'
  have hω0 : 0 ≤ ω₀ := (abs_nonneg _).trans ha
  have eU : ∀ m : ℕ, spanU c g b (m * θ) / pP (m * θ) = c * Dn c g χ b 0 (m * θ) := fun m =>
    (Dn_zero hc b _).symm
  unfold N0
  rw [eU k, eU l, ← Hn_zero (χ := χ) b (k * θ), ← Hn_zero (χ := χ) b (l * θ), abs_div, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < c ^ 2)]
  rw [div_le_iff₀ (by positivity)]
  have hnum : |(w' θ - 2 * w θ * θ * bet k θ) * k * (c * Dk * Hl)
      - (w' θ - 2 * w θ * θ * bet l θ) * l * (Hk * (c * Dl))| ≤ ω₀ * (k + l) * c * (|Dk| * |Hl| + |Hk| * |Dl|) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast,
      abs_of_pos hc]
    have h1 : |w' θ - 2 * w θ * θ * bet k θ| * k * (c * |Dk| * |Hl|) ≤ ω₀ * (k + l) * c * (|Dk| * |Hl|) := by
      have := mul_le_mul ha (show (k : ℝ) ≤ k + l by linarith) (Nat.cast_nonneg k) hω0
      nlinarith [mul_nonneg (mul_nonneg hc.le (abs_nonneg Dk)) (abs_nonneg Hl)]
    have h2 : |w' θ - 2 * w θ * θ * bet l θ| * l * (|Hk| * (c * |Dl|)) ≤ ω₀ * (k + l) * c * (|Hk| * |Dl|) := by
      have := mul_le_mul hb (show (l : ℝ) ≤ k + l by linarith) (Nat.cast_nonneg l) hω0
      nlinarith [mul_nonneg (mul_nonneg hc.le (abs_nonneg Dl)) (abs_nonneg Hk)]
    nlinarith
  have hamgm : |Dk| * |Hl| + |Hk| * |Dl| ≤ ((Hk ^ 2 + Dk ^ 2) + (Hl ^ 2 + Dl ^ 2)) / 2 := by
    nlinarith [sq_abs Dk, sq_abs Hl, sq_abs Hk, sq_abs Dl, sq_nonneg (|Dk| - |Hl|), sq_nonneg (|Hk| - |Dl|)]
  calc _ ≤ ω₀ * (k + l) * c * (|Dk| * |Hl| + |Hk| * |Dl|) := hnum
    _ ≤ ω₀ * (k + l) * c * (((Hk ^ 2 + Dk ^ 2) + (Hl ^ 2 + Dl ^ 2)) / 2) :=
        mul_le_mul_of_nonneg_left hamgm (by positivity)
    _ = ω₀ / c * ((Hk ^ 2 + Dk ^ 2) + (Hl ^ 2 + Dl ^ 2)) * (c ^ 2 * (((k : ℝ) + l) / 2)) := by
        field_simp
    _ ≤ ω₀ / c * ((Hk ^ 2 + Dk ^ 2) + (Hl ^ 2 + Dl ^ 2)) * (c ^ 2 * |Lam k θ - Lam l θ|) := by
        gcongr

/-- `C_H = 2(3π(ω₀²/4 + 1) + ω₀/24)`. -/
def CH : ℝ := 2 * (3 * π * (ω₀ ^ 2 / 4 + 1) + ω₀ / 24)

/-- **The leading terms summed over all pairs**: Hilbert's inequality gives
`|Σ_{k≠l} N₀(k, l)| ≤ (C_H/c)Σ_k(H₀(kθ)² + D₀(kθ)²)`. -/
theorem abs_sum_N0_le (hc : 0 < c) (b : ι → ℝ) (K : ℕ) {θ : ℝ} (hθ : 12 / 25 ≤ θ) (hθ1 : θ ≤ 11 / 10)
    {w w' : ℝ → ℝ} (hw : |w θ| ≤ 1) (hw' : |w' θ| ≤ 70) :
    |∑ k ∈ Finset.Icc 3 K, ∑ l ∈ Finset.Icc 3 K, (if k = l then 0 else N0 c g b w w' k l θ)|
      ≤ CH / c * ∑ k ∈ Finset.Icc 3 K, (Hn c g χ b 0 (k * θ) ^ 2 + Dn c g χ b 0 (k * θ) ^ 2) := by
  set S := Finset.Icc 3 K
  set a : ℕ → ℝ := fun k => w' θ - 2 * w θ * θ * bet k θ
  set U : ℕ → ℝ := fun k => spanU c g b (k * θ) / pP (k * θ)
  set H : ℕ → ℝ := fun k => spanH c g b (k * θ)
  have hsplit : ∀ k l, (if k = l then 0 else N0 c g b w w' k l θ)
      = (1 / c ^ 2) * ((if k = l then 0 else a k * k * U k * H l / (Lam k θ - Lam l θ))
        + (if l = k then 0 else a l * l * U l * H k / (Lam l θ - Lam k θ))) := by
    intro k l
    by_cases h : k = l
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right (Ne.symm h)]
      simp only [N0, a, U, H]
      rw [show Lam l θ - Lam k θ = -(Lam k θ - Lam l θ) by ring]
      by_cases hz : Lam k θ - Lam l θ = 0
      · rw [hz]; simp
      · field_simp; ring
  have hT : ∑ k ∈ S, ∑ l ∈ S, (if l = k then 0 else a l * l * U l * H k / (Lam l θ - Lam k θ))
      = ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else a k * k * U k * H l / (Lam k θ - Lam l θ)) := Finset.sum_comm
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hsplit k l]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hT, ← two_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / c ^ 2), abs_two]
  have ha : ∀ k ∈ S, |a k| ≤ ω₀ := fun k hk =>
    abs_wcoef_le (Finset.mem_Icc.mp hk).1 hθ hθ1 hw hw'
  have hω0 : 0 ≤ ω₀ := by simp only [ω₀, βb]; norm_num
  set s : ℝ := (√c)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr hc)
  have hs2 : s ^ 2 = 1 / c := by rw [hs, inv_pow, Real.sq_sqrt hc.le, one_div]
  have hH := Cvs.Route.Visibility.AliasKernelHilbertInequality.hilbert_alias_le K hθ a U H hω0 ha hs0
  set T := ∑ k ∈ S, ∑ l ∈ S, (if k = l then 0 else a k * k * U k * H l / (Lam k θ - Lam l θ))
  have hU : ∀ k, U k = c * Dn c g χ b 0 (k * θ) := fun k => (Dn_zero hc b _).symm
  have hHk : ∀ k, H k = Hn c g χ b 0 (k * θ) := fun k => (Hn_zero b _).symm
  simp only [hU, hHk] at hH
  set D0 : ℕ → ℝ := fun k => Dn c g χ b 0 (k * θ)
  set H0 : ℕ → ℝ := fun k => Hn c g χ b 0 (k * θ)
  have hUU : ∑ k ∈ S, (c * D0 k) ^ 2 = c ^ 2 * ∑ k ∈ S, D0 k ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hUH : ∑ k ∈ S, |c * D0 k| * |H0 k| ≤ c / 2 * ∑ k ∈ S, (H0 k ^ 2 + D0 k ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul, abs_of_pos hc]
    nlinarith [sq_abs (D0 k), sq_abs (H0 k), sq_nonneg (|D0 k| - |H0 k|), abs_nonneg (D0 k), abs_nonneg (H0 k)]
  have hD2 : ∑ k ∈ S, D0 k ^ 2 ≤ ∑ k ∈ S, (H0 k ^ 2 + D0 k ^ 2) :=
    Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (H0 k)]
  have hH2 : ∑ k ∈ S, H0 k ^ 2 ≤ ∑ k ∈ S, (H0 k ^ 2 + D0 k ^ 2) :=
    Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (D0 k)]
  set E := ∑ k ∈ S, (H0 k ^ 2 + D0 k ^ 2) with hEdef
  rw [hUU, hs2] at hH
  have hT : |T| ≤ c * (3 * π * (ω₀ ^ 2 / 4 * ∑ k ∈ S, D0 k ^ 2 + ∑ k ∈ S, H0 k ^ 2) + ω₀ / 24 * E) := by
    refine hH.trans ?_
    have hπ := Real.pi_pos
    have e1 : 1 / c * (ω₀ ^ 2 / 4 * (c ^ 2 * ∑ k ∈ S, D0 k ^ 2)) + (∑ k ∈ S, H0 k ^ 2) / (1 / c)
        = c * (ω₀ ^ 2 / 4 * ∑ k ∈ S, D0 k ^ 2 + ∑ k ∈ S, H0 k ^ 2) := by field_simp
    rw [e1]
    have := mul_le_mul_of_nonneg_left hUH (by positivity : (0 : ℝ) ≤ ω₀ / 12)
    nlinarith
  have hfin : 2 * (1 / c ^ 2) * (c * (3 * π * (ω₀ ^ 2 / 4 * ∑ k ∈ S, D0 k ^ 2 + ∑ k ∈ S, H0 k ^ 2) + ω₀ / 24 * E))
      ≤ CH / c * E := by
    have hπ := Real.pi_pos
    have h1 : ω₀ ^ 2 / 4 * ∑ k ∈ S, D0 k ^ 2 + ∑ k ∈ S, H0 k ^ 2 ≤ (ω₀ ^ 2 / 4 + 1) * E := by
      nlinarith [sq_nonneg ω₀]
    have e : 2 * (1 / c ^ 2) * (c * (3 * π * (ω₀ ^ 2 / 4 * ∑ k ∈ S, D0 k ^ 2 + ∑ k ∈ S, H0 k ^ 2) + ω₀ / 24 * E))
        = 2 / c * (3 * π * (ω₀ ^ 2 / 4 * ∑ k ∈ S, D0 k ^ 2 + ∑ k ∈ S, H0 k ^ 2) + ω₀ / 24 * E) := by
      field_simp
    rw [e, CH]
    have h2 : 3 * π * (ω₀ ^ 2 / 4 * ∑ k ∈ S, D0 k ^ 2 + ∑ k ∈ S, H0 k ^ 2) ≤ 3 * π * ((ω₀ ^ 2 / 4 + 1) * E) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 0 ≤ 2 / c := by positivity
    calc 2 / c * (3 * π * (ω₀ ^ 2 / 4 * ∑ k ∈ S, D0 k ^ 2 + ∑ k ∈ S, H0 k ^ 2) + ω₀ / 24 * E)
        ≤ 2 / c * (3 * π * ((ω₀ ^ 2 / 4 + 1) * E) + ω₀ / 24 * E) := by gcongr
      _ = 2 * (3 * π * (ω₀ ^ 2 / 4 + 1) + ω₀ / 24) / c * E := by ring
  calc 1 / c ^ 2 * (2 * |T|) = 2 * (1 / c ^ 2) * |T| := by ring
    _ ≤ 2 * (1 / c ^ 2) * (c * (3 * π * (ω₀ ^ 2 / 4 * ∑ k ∈ S, D0 k ^ 2
        + ∑ k ∈ S, H0 k ^ 2) + ω₀ / 24 * E)) := mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ CH / c * E := hfin
    _ = _ := by rw [hEdef, Finset.sum_add_distrib]

end Cvs.Route.Visibility.AliasMomentMajorants
