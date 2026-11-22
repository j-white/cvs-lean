import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.WindowFormTailLimit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The primitive of the truncation remainder is `O((1 + log)/max(Q, y₁))`

`∫_{y₁}^{y₂} r_Q = Σ_m (I(m z_m) − I(m y₂))/m`, `z_m = max(y₁, min(y₂, Q/m))`, `I` a primitive of `−Φ`: only modes
with `m y₂ > Q` survive, so `|I(t)| ≤ K/t` gives `2K(3 + log(y₂/y₁))/max(Q, y₁)`. Integration by parts against it
bounds `∫_p^q w(θ) r_Q(nθ) dθ` by `(|w(q)| + ∫|w′|) 2K(3 + log(q/p))/(n max(Q, np))`.
-/

noncomputable section

namespace Cvs.L2a.TruncationRemainderPrimitive

open Real Set Filter Topology MeasureTheory
open scoped Interval
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.WindowFormTailLimit (tailRem)
open Cvs.L2a.AngularProlateTailPositive (psi)

/-! ### Two elementary sums -/

/-- `Σ_{a<m≤b} 1/m ≤ 1 + log(v/u)` for `0 < u < a + 1`, `b ≤ v` and `u ≤ v`. -/
theorem sum_Ioc_inv_le {a b : ℕ} {u v : ℝ} (hu : 0 < u) (hua : u < a + 1) (hbv : (b : ℝ) ≤ v)
    (huv : u ≤ v) : ∑ m ∈ Finset.Ioc a b, 1 / (m : ℝ) ≤ 1 + Real.log (v / u) := by
  have hlog : 0 ≤ Real.log (v / u) := Real.log_nonneg ((one_le_div hu).mpr huv)
  rcases le_or_gt b a with hba | hab
  · rw [Finset.Ioc_eq_empty (by omega)]; simp only [Finset.sum_empty]; linarith
  have hH : ∀ n : ℕ, ∑ m ∈ Finset.Icc 1 n, 1 / (m : ℝ) = (harmonic n : ℝ) := fun n => by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  have hI : ∀ n, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit : ∑ m ∈ Finset.Ioc a b, 1 / (m : ℝ)
      = ∑ m ∈ Finset.Icc 1 b, 1 / (m : ℝ) - ∑ m ∈ Finset.Icc 1 a, 1 / (m : ℝ) := by
    rw [hI, hI, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab.le]; ring
  rw [hsplit, hH, hH]
  have h1 := harmonic_le_one_add_log b
  have h2 := log_add_one_le_harmonic a
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have h3 : Real.log b - Real.log ((a : ℝ) + 1) ≤ Real.log (v / u) := by
    rw [← Real.log_div hb0.ne' ha1.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ ha1 hu]
    nlinarith [mul_le_mul_of_nonneg_right hbv hu.le, mul_le_mul_of_nonneg_left hua.le (hb0.le.trans hbv)]
  push_cast at h2
  linarith

/-- `Σ_{1≤m≤M, m>x} 1/m² ≤ 2/max(1, x)`. -/
theorem sum_inv_sq_gt_le (x : ℝ) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (if x < m then 1 / (m : ℝ) ^ 2 else 0) ≤ 2 / max 1 x := by
  have hle : ∀ m ∈ Finset.Icc 1 M, (if x < m then 1 / (m : ℝ) ^ 2 else 0) ≤ 1 / (m : ℝ) ^ 2 :=
    fun m _ => by split_ifs <;> [exact le_rfl; positivity]
  rcases lt_or_ge x 1 with hx | hx
  · rw [max_eq_left hx.le, div_one]
    refine (Finset.sum_le_sum hle).trans ((sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_two).trans ?_)
    have hp : π ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    linarith
  rw [max_eq_right hx]
  set n := ⌊x⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  rw [← Finset.sum_filter]
  have hsub : (Finset.Icc 1 M).filter (fun m : ℕ => x < m) ⊆ Finset.Ioc n M := fun m hm => by
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt (by linarith)).mpr hm.2, hm.1.2⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
    ((Cvs.L2a.FullTailConvergence.sum_Ioc_one_div_sq_le hn1 M).trans ?_)
  rw [div_le_div_iff₀ hn0 (by linarith)]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  linarith

/-! ### One mode of the remainder primitive -/

/-- One mode of `|∫ r_Q|`: `|I(m z) − I(m y₂)|/m` vanishes when `m y₂ ≤ Q` and is at most `2K/(m max(m y₁, Q))`
otherwise, for `z = max(y₁, min(y₂, Q/m))` and `|I(t)| ≤ K/t` on `[1, ∞)`. -/
theorem abs_mode_le {I : ℝ → ℝ} {K : ℝ} (hIb : ∀ t, 1 ≤ t → |I t| ≤ K / t) {m : ℕ} (hm : 1 ≤ m)
    {Q y₁ y₂ : ℝ} (hy₁ : 1 ≤ y₁) (hy : y₁ ≤ y₂) :
    |(I (m * max y₁ (min y₂ (Q / m))) - I (m * y₂)) / m|
      ≤ if Q < m * y₂ then 2 * K / (m * max (m * y₁) Q) else 0 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  split_ifs with hQ
  · have hmin : min y₂ (Q / m) = Q / m :=
      min_eq_right ((div_lt_iff₀ hm0).mpr (by linarith [mul_comm (m : ℝ) y₂])).le
    have hz : (m : ℝ) * max y₁ (Q / m) = max (m * y₁) Q := by
      rw [mul_max_of_nonneg _ _ hm0.le, mul_div_cancel₀ Q hm0.ne']
    rw [hmin, hz]
    have hD1 : 1 ≤ max ((m : ℝ) * y₁) Q := le_max_of_le_left (one_le_mul_of_one_le_of_one_le hm1 hy₁)
    have hD : 0 < max ((m : ℝ) * y₁) Q := by linarith
    have hy2 : 1 ≤ (m : ℝ) * y₂ := one_le_mul_of_one_le_of_one_le hm1 (hy₁.trans hy)
    have hDy : max ((m : ℝ) * y₁) Q ≤ m * y₂ := max_le (mul_le_mul_of_nonneg_left hy hm0.le) hQ.le
    have h1 := hIb _ hD1
    have h2 := hIb _ hy2
    have hK : 0 ≤ K := by
      by_contra hK
      have := div_neg_of_neg_of_pos (not_le.mp hK) hD
      linarith [abs_nonneg (I (max ((m : ℝ) * y₁) Q))]
    have h3 : K / (m * y₂) ≤ K / max ((m : ℝ) * y₁) Q := div_le_div_of_nonneg_left hK hD hDy
    rw [abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    calc |I (max ((m : ℝ) * y₁) Q) - I (m * y₂)| ≤ |I (max ((m : ℝ) * y₁) Q)| + |I (m * y₂)| := abs_sub _ _
      _ ≤ 2 * (K / max ((m : ℝ) * y₁) Q) := by linarith
      _ = 2 * K / (m * max ((m : ℝ) * y₁) Q) * m := by field_simp
  · push Not at hQ
    have hmin : min y₂ (Q / m) = y₂ :=
      min_eq_left ((le_div_iff₀ hm0).mpr (by linarith [mul_comm (m : ℝ) y₂]))
    rw [hmin, max_eq_right hy, sub_self, zero_div, abs_zero]

/-- The surviving modes sum to `Σ_{m ≤ M, m y₂ > Q} 2K/(m max(m y₁, Q)) ≤ 2K(3 + log(y₂/y₁))/max(Q, y₁)`. -/
theorem sum_mode_le {K : ℝ} (hK : 0 ≤ K) (M : ℕ) {Q y₁ y₂ : ℝ} (hy₁ : 1 ≤ y₁) (hy : y₁ ≤ y₂) :
    ∑ m ∈ Finset.Icc 1 M, (if Q < m * y₂ then 2 * K / (m * max (m * y₁) Q) else 0)
      ≤ 2 * K * (3 + Real.log (y₂ / y₁)) / max Q y₁ := by
  have hy0 : 0 < y₁ := by linarith
  have hlog : 0 ≤ Real.log (y₂ / y₁) := Real.log_nonneg ((one_le_div hy0).mpr hy)
  set t₁ : ℕ → ℝ := fun m => if Q < m * y₂ ∧ m * y₁ ≤ Q then 2 * K / Q * (1 / (m : ℝ)) else 0 with ht₁
  set t₂ : ℕ → ℝ := fun m => 2 * K / y₁ * (if Q / y₁ < m then 1 / (m : ℝ) ^ 2 else 0) with ht₂
  have hpt : ∀ m ∈ Finset.Icc 1 M,
      (if Q < m * y₂ then 2 * K / (m * max (m * y₁) Q) else 0) ≤ t₁ m + t₂ m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have h1 : 0 ≤ t₁ m := by
      simp only [ht₁]
      split_ifs with h
      · have : 0 < Q := lt_of_lt_of_le (mul_pos hm0 hy0) h.2
        positivity
      · exact le_rfl
    have h2 : 0 ≤ t₂ m := by simp only [ht₂]; split_ifs <;> positivity
    split_ifs with hQ
    · rcases le_or_gt ((m : ℝ) * y₁) Q with h | h
      · have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) h
        have e : t₁ m = 2 * K / (m * max ((m : ℝ) * y₁) Q) := by
          simp only [ht₁, if_pos (And.intro hQ h), max_eq_right h]; field_simp
        linarith
      · have hQy : Q / y₁ < m := (div_lt_iff₀ hy0).mpr h
        have e : t₂ m = 2 * K / (m * max ((m : ℝ) * y₁) Q) := by
          simp only [ht₂, if_pos hQy, max_eq_left h.le]; field_simp
        linarith
    · linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  have hS₂ : ∑ m ∈ Finset.Icc 1 M, t₂ m ≤ 4 * K / max Q y₁ := by
    simp only [ht₂]
    rw [← Finset.mul_sum]
    have hs := sum_inv_sq_gt_le (Q / y₁) M
    have hmax : y₁ * max 1 (Q / y₁) = max Q y₁ := by
      rw [mul_max_of_nonneg _ _ hy0.le, mul_one, mul_div_cancel₀ Q hy0.ne', max_comm]
    calc 2 * K / y₁ * ∑ m ∈ Finset.Icc 1 M, (if Q / y₁ < m then 1 / (m : ℝ) ^ 2 else 0)
        ≤ 2 * K / y₁ * (2 / max 1 (Q / y₁)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 4 * K / (y₁ * max 1 (Q / y₁)) := by
          have : 0 < max 1 (Q / y₁) := lt_of_lt_of_le one_pos (le_max_left _ _)
          field_simp; ring
      _ = 4 * K / max Q y₁ := by rw [hmax]
  rcases lt_or_ge Q y₁ with hQy | hQy
  · have hS₁ : ∑ m ∈ Finset.Icc 1 M, t₁ m = 0 := Finset.sum_eq_zero fun m hm => by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have : ¬ ((m : ℝ) * y₁ ≤ Q) := not_le.mpr (by nlinarith)
      simp only [ht₁, this, and_false, if_false]
    rw [hS₁, zero_add]
    refine hS₂.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    nlinarith
  · have hQ0 : 0 < Q := by linarith
    rw [max_eq_left hQy] at hS₂ ⊢
    set u := Q / y₂
    set v := Q / y₁
    have hy20 : 0 < y₂ := by linarith
    have hu : 0 < u := div_pos hQ0 hy20
    have huv : u ≤ v := div_le_div_of_nonneg_left hQ0.le hy0 hy
    have hvu : v / u = y₂ / y₁ := by
      simp only [u, v]; field_simp
    have hS₁ : ∑ m ∈ Finset.Icc 1 M, t₁ m ≤ 2 * K / Q * (1 + Real.log (y₂ / y₁)) := by
      have hsub : (Finset.Icc 1 M).filter (fun m : ℕ => Q < m * y₂ ∧ m * y₁ ≤ Q) ⊆ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊ := by
        intro m hm
        rw [Finset.mem_filter] at hm
        refine Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hu.le).mpr ?_, Nat.le_floor ?_⟩
        · exact (div_lt_iff₀ (by linarith)).mpr hm.2.1
        · exact (le_div_iff₀ hy0).mpr hm.2.2
      simp only [ht₁]
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
      rw [← hvu]
      exact sum_Ioc_inv_le hu (Nat.lt_floor_add_one u) (Nat.floor_le (hu.le.trans huv)) huv
    calc ∑ m ∈ Finset.Icc 1 M, t₁ m + ∑ m ∈ Finset.Icc 1 M, t₂ m
        ≤ 2 * K / Q * (1 + Real.log (y₂ / y₁)) + 4 * K / Q := add_le_add hS₁ hS₂
      _ = 2 * K * (3 + Real.log (y₂ / y₁)) / Q := by field_simp; ring

/-! ### The exact mode expansion of `∫ r_Q` -/

/-- Beyond `⌊Q⌋₊` the masks `(1, Q/m]` are empty, so `F_Q = Σ_{m ≤ M} 1_{(1, Q/m]} Φ(m·)` for `M ≥ ⌊Q⌋₊`. -/
theorem posTail_eq_sum_of_le (Φ : ℝ → ℝ) {Q : ℝ} {M : ℕ} (hM : ⌊Q⌋₊ ≤ M) (θ : ℝ) :
    posTail Φ Q θ = ∑ m ∈ Finset.Icc 1 M, (Ioc 1 (Q / m)).indicator (fun θ => Φ (m * θ)) θ := by
  rw [Cvs.L2a.PositionTruncatedTail.posTail_eq_sum]
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hM) fun m hm hm' =>
    indicator_of_notMem (fun h => ?_) _
  have hm1 := (Finset.mem_Icc.mp hm).1
  have hlt : ⌊Q⌋₊ < m := by
    by_contra h; exact hm' (Finset.mem_Icc.mpr ⟨hm1, not_lt.mp h⟩)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hQm : Q < m := by
    rcases le_or_gt 0 Q with hQ | hQ
    · exact (Nat.floor_lt hQ).mp hlt
    · linarith
  have : Q / m < 1 := (div_lt_one hm0).mpr hQm
  linarith [h.1, h.2]

/-- One mode `Φ(m·) − 1_{(1, Q/m]} Φ(m·)` is interval integrable. -/
theorem intervalIntegrable_mode {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (m : ℕ) (Q a b : ℝ) :
    IntervalIntegrable (fun θ => Φ (m * θ) - (Ioc 1 (Q / m)).indicator (fun θ => Φ (m * θ)) θ) volume a b := by
  have hc : Continuous fun θ : ℝ => Φ (m * θ) := hΦ.comp (continuous_const.mul continuous_id)
  exact (hc.intervalIntegrable a b).sub (intervalIntegrable_iff.mpr
    ((intervalIntegrable_iff.mp (hc.intervalIntegrable a b)).indicator measurableSet_Ioc))

/-- One mode of `F_M − F_Q` on `[y₁, y₂]`: `∫ (Φ(mθ) − 1_{(1,Q/m]}(θ) Φ(mθ)) dθ = (I(m z) − I(m y₂))/m` with
`z = max(y₁, min(y₂, Q/m))`, for `I` with `∫_t^u Φ = I(t) − I(u)` on `[1, ∞)`. -/
theorem integral_mode_eq {Φ I : ℝ → ℝ} (hΦ : Continuous Φ)
    (hI : ∀ t u, 1 ≤ t → 1 ≤ u → ∫ ξ in t..u, Φ ξ = I t - I u) {m : ℕ} (hm : 1 ≤ m)
    {Q y₁ y₂ : ℝ} (hy₁ : 1 ≤ y₁) (hy : y₁ ≤ y₂) :
    ∫ θ in y₁..y₂, (Φ (m * θ) - (Ioc 1 (Q / m)).indicator (fun θ => Φ (m * θ)) θ)
      = (I (m * max y₁ (min y₂ (Q / m))) - I (m * y₂)) / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set z := max y₁ (min y₂ (Q / m)) with hz
  have hz1 : y₁ ≤ z := le_max_left _ _
  have hz2 : z ≤ y₂ := max_le hy (min_le_left _ _)
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_mode hΦ m Q y₁ z)
    (intervalIntegrable_mode hΦ m Q z y₂)]
  have h1 : ∫ θ in y₁..z, (Φ (m * θ) - (Ioc 1 (Q / m)).indicator (fun θ => Φ (m * θ)) θ) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun θ hθ => ?_)]
    · simp
    rw [uIoc_of_le hz1] at hθ
    have hθQ : θ ≤ Q / m := by
      have hzle : z ≤ max y₁ (Q / m) := max_le_max le_rfl (min_le_right _ _)
      rcases le_total y₁ (Q / m) with h | h
      · rw [max_eq_right h] at hzle; linarith [hθ.2]
      · rw [max_eq_left h] at hzle; linarith [hθ.1, hθ.2]
    rw [indicator_of_mem (show θ ∈ Ioc 1 (Q / m) from ⟨by linarith [hθ.1], hθQ⟩), sub_self]
  have h2 : ∫ θ in z..y₂, (Φ (m * θ) - (Ioc 1 (Q / m)).indicator (fun θ => Φ (m * θ)) θ)
      = ∫ θ in z..y₂, Φ (m * θ) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun θ hθ => ?_)
    rw [uIoc_of_le hz2] at hθ
    have hθQ : Q / m < θ := by
      by_contra h
      push Not at h
      have : θ ≤ z := (le_min hθ.2 h).trans (le_max_right _ _)
      linarith [hθ.1]
    rw [indicator_of_notMem (show θ ∉ Ioc 1 (Q / m) from fun h' => absurd h'.2 (not_le.mpr hθQ)), sub_zero]
  rw [h1, h2, zero_add, intervalIntegral.integral_comp_mul_left (fun x => Φ x) hm0.ne', smul_eq_mul,
    hI _ _ (one_le_mul_of_one_le_of_one_le hm1 (hy₁.trans hz1))
      (one_le_mul_of_one_le_of_one_le hm1 (hy₁.trans hy))]
  ring

/-- A uniform bound on the Poisson partial sums bounds every truncation `F_Q`. -/
theorem abs_posTail_le_of_dom {Φ : ℝ → ℝ} {B : ℝ}
    (hdom : ∀ θ, 1 < θ → ∀ M : ℕ, |∑ m ∈ Finset.Icc 1 M, Φ (m * θ)| ≤ B) (Q θ : ℝ) :
    |posTail Φ Q θ| ≤ B := by
  rcases le_or_gt θ 1 with h1 | h1
  · rw [Cvs.L2a.PositionTruncatedTail.posTail_zero Φ Q h1, abs_zero]
    simpa using hdom 2 one_lt_two 0
  rcases le_or_gt θ Q with h | h
  · rw [Cvs.L2a.FullTailConvergence.posTail_eq_partial Φ h1 h]; exact hdom θ h1 _
  · rw [Cvs.L2a.PositionTruncatedTail.posTail_of_gt Φ h, abs_zero]; exact (abs_nonneg _).trans (hdom θ h1 0)

/-- A uniform bound on the Poisson partial sums bounds `F_∞`. -/
theorem abs_fullTail_le_of_dom {Φ : ℝ → ℝ} {B : ℝ}
    (hpart : ∀ θ, 1 < θ → Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)) atTop (𝓝 (fullTail Φ θ)))
    (hdom : ∀ θ, 1 < θ → ∀ M : ℕ, |∑ m ∈ Finset.Icc 1 M, Φ (m * θ)| ≤ B) (θ : ℝ) :
    |fullTail Φ θ| ≤ B := by
  rcases le_or_gt θ 1 with h1 | h1
  · rw [Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one Φ h1, abs_zero]
    simpa using hdom 2 one_lt_two 0
  exact le_of_tendsto' (hpart θ h1).abs (hdom θ h1)

/-- **The mode expansion of the remainder primitive**: for `1 ≤ y₁ ≤ y₂`,
`Σ_{m ≤ M} (I(m z_m) − I(m y₂))/m → ∫_{y₁}^{y₂} r_Q`, `z_m = max(y₁, min(y₂, Q/m))`, for any continuous profile
whose Poisson partial sums converge to `F_∞` with a uniform bound on `(1, ∞)`. -/
theorem tendsto_integral_tailRem {Φ I : ℝ → ℝ} {B : ℝ} (hΦ : Continuous Φ)
    (hpart : ∀ θ, 1 < θ → Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)) atTop (𝓝 (fullTail Φ θ)))
    (hdom : ∀ θ, 1 < θ → ∀ M : ℕ, |∑ m ∈ Finset.Icc 1 M, Φ (m * θ)| ≤ B)
    (hI : ∀ t u, 1 ≤ t → 1 ≤ u → ∫ ξ in t..u, Φ ξ = I t - I u) (Q : ℝ) {y₁ y₂ : ℝ} (hy₁ : 1 ≤ y₁)
    (hy : y₁ ≤ y₂) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, (I (m * max y₁ (min y₂ (Q / m))) - I (m * y₂)) / m) atTop
      (𝓝 (∫ θ in y₁..y₂, tailRem Φ Q θ)) := by
  have hc : ∀ m : ℕ, Continuous fun θ : ℝ => Φ (m * θ) := fun m =>
    hΦ.comp (continuous_const.mul continuous_id)
  have hpos : ∀ θ, 1 < θ → |posTail Φ Q θ| ≤ B := fun θ _ => abs_posTail_le_of_dom hdom Q θ
  have hlim : Tendsto (fun M : ℕ => ∫ θ in y₁..y₂, (∑ m ∈ Finset.Icc 1 M, Φ (m * θ) - posTail Φ Q θ))
      atTop (𝓝 (∫ θ in y₁..y₂, tailRem Φ Q θ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * B)
      (Eventually.of_forall fun M => ((continuous_finsetSum _ fun m _ => hc m).measurable.sub
        (Cvs.L2a.FullTailConvergence.measurable_posTail hΦ Q)).aestronglyMeasurable)
      (Eventually.of_forall fun M => ae_of_all _ fun θ hθ => ?_) intervalIntegrable_const
      (ae_of_all _ fun θ hθ => ?_)
    · rw [uIoc_of_le hy] at hθ
      have h1 : 1 < θ := by linarith [hθ.1]
      rw [Real.norm_eq_abs]
      calc |∑ m ∈ Finset.Icc 1 M, Φ (m * θ) - posTail Φ Q θ|
          ≤ |∑ m ∈ Finset.Icc 1 M, Φ (m * θ)| + |posTail Φ Q θ| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hdom θ h1 M, hpos θ h1]
    · rw [uIoc_of_le hy] at hθ
      exact (hpart θ (by linarith [hθ.1])).sub_const _
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop ⌊Q⌋₊] with M hM
  have hpt : (fun θ => ∑ m ∈ Finset.Icc 1 M, Φ (m * θ) - posTail Φ Q θ)
      = fun θ => ∑ m ∈ Finset.Icc 1 M, (Φ (m * θ) - (Ioc 1 (Q / m)).indicator (fun θ => Φ (m * θ)) θ) := by
    funext θ
    rw [posTail_eq_sum_of_le Φ hM θ, Finset.sum_sub_distrib]
  rw [hpt, intervalIntegral.integral_finsetSum fun m _ => intervalIntegrable_mode hΦ m Q y₁ y₂]
  exact Finset.sum_congr rfl fun m hm => integral_mode_eq hΦ hI (Finset.mem_Icc.mp hm).1 hy₁ hy

/-! ### The bound -/

/-- **The remainder primitive is small**: for `1 ≤ y₁ ≤ y₂` and any `Q`,
`|∫_{y₁}^{y₂} r_Q| ≤ 2K(3 + log(y₂/y₁))/max(Q, y₁)`, for any continuous profile with uniformly bounded Poisson
partial sums on `(1, ∞)` and a primitive `I` of `−Φ` with `|I(t)| ≤ K/t` on `[1, ∞)`. -/
theorem abs_integral_tailRem_le {Φ I : ℝ → ℝ} {B K : ℝ} (hΦ : Continuous Φ)
    (hpart : ∀ θ, 1 < θ → Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)) atTop (𝓝 (fullTail Φ θ)))
    (hdom : ∀ θ, 1 < θ → ∀ M : ℕ, |∑ m ∈ Finset.Icc 1 M, Φ (m * θ)| ≤ B)
    (hI : ∀ t u, 1 ≤ t → 1 ≤ u → ∫ ξ in t..u, Φ ξ = I t - I u) (hIb : ∀ t, 1 ≤ t → |I t| ≤ K / t)
    (Q : ℝ) {y₁ y₂ : ℝ} (hy₁ : 1 ≤ y₁) (hy : y₁ ≤ y₂) :
    |∫ θ in y₁..y₂, tailRem Φ Q θ| ≤ 2 * K * (3 + Real.log (y₂ / y₁)) / max Q y₁ := by
  have hK : 0 ≤ K := by
    have h := hIb 1 le_rfl
    rw [div_one] at h
    exact (abs_nonneg _).trans h
  refine le_of_tendsto (tendsto_integral_tailRem hΦ hpart hdom hI Q hy₁ hy).abs
    (Eventually.of_forall fun M => ?_)
  calc |∑ m ∈ Finset.Icc 1 M, (I (m * max y₁ (min y₂ (Q / m))) - I (m * y₂)) / m|
      ≤ ∑ m ∈ Finset.Icc 1 M, |(I (m * max y₁ (min y₂ (Q / m))) - I (m * y₂)) / m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, (if Q < m * y₂ then 2 * K / (m * max (m * y₁) Q) else 0) :=
        Finset.sum_le_sum fun m hm => abs_mode_le hIb (Finset.mem_Icc.mp hm).1 hy₁ hy
    _ ≤ 2 * K * (3 + Real.log (y₂ / y₁)) / max Q y₁ := sum_mode_le hK M hy₁ hy

/-- The remainder primitive bound for `0 < y₁ ≤ y₂`: `r_Q` vanishes on `θ ≤ 1`. -/
theorem abs_integral_tailRem_le_of_pos {Φ I : ℝ → ℝ} {B K : ℝ} (hΦ : Continuous Φ)
    (hpart : ∀ θ, 1 < θ → Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)) atTop (𝓝 (fullTail Φ θ)))
    (hdom : ∀ θ, 1 < θ → ∀ M : ℕ, |∑ m ∈ Finset.Icc 1 M, Φ (m * θ)| ≤ B)
    (hI : ∀ t u, 1 ≤ t → 1 ≤ u → ∫ ξ in t..u, Φ ξ = I t - I u) (hIb : ∀ t, 1 ≤ t → |I t| ≤ K / t)
    (Q : ℝ) {y₁ y₂ : ℝ} (hy₀ : 0 < y₁) (hy : y₁ ≤ y₂) :
    |∫ θ in y₁..y₂, tailRem Φ Q θ| ≤ 2 * K * (3 + Real.log (y₂ / y₁)) / max Q y₁ := by
  have hK : 0 ≤ K := by
    have h := hIb 1 le_rfl
    rw [div_one] at h
    exact (abs_nonneg _).trans h
  have hlog : 0 ≤ Real.log (y₂ / y₁) := Real.log_nonneg ((one_le_div hy₀).mpr hy)
  have hD : 0 < max Q y₁ := lt_of_lt_of_le hy₀ (le_max_right _ _)
  rcases le_or_gt 1 y₁ with h1 | h1
  · exact abs_integral_tailRem_le hΦ hpart hdom hI hIb Q h1 hy
  rcases lt_or_ge y₂ 1 with h2 | h2
  · have h0 : ∫ θ in y₁..y₂, tailRem Φ Q θ = 0 := by
      rw [intervalIntegral.integral_of_le hy]
      exact setIntegral_eq_zero_of_forall_eq_zero fun θ hθ =>
        Cvs.L2a.WindowFormTailLimit.tailRem_of_le_one Φ Q (by linarith [hθ.2])
    rw [h0, abs_zero]
    positivity
  have e : ∫ θ in y₁..y₂, tailRem Φ Q θ = ∫ θ in (1 : ℝ)..y₂, tailRem Φ Q θ := by
    rw [intervalIntegral.integral_of_le hy, intervalIntegral.integral_of_le h2]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Ioc_subset_Ioc_left h1.le) fun θ hθ => Cvs.L2a.WindowFormTailLimit.tailRem_of_le_one Φ Q ?_
    by_contra h
    exact hθ.2 ⟨not_le.mp h, hθ.1.2⟩
  rw [e]
  have hb := abs_integral_tailRem_le hΦ hpart hdom hI hIb Q le_rfl h2
  have hl : Real.log (y₂ / 1) ≤ Real.log (y₂ / y₁) :=
    Real.log_le_log (by linarith) (div_le_div_of_nonneg_left (by linarith) hy₀ h1.le)
  have hD1 : max Q y₁ ≤ max Q 1 := max_le_max le_rfl h1.le
  calc |∫ θ in (1 : ℝ)..y₂, tailRem Φ Q θ| ≤ 2 * K * (3 + Real.log (y₂ / 1)) / max Q 1 := hb
    _ ≤ 2 * K * (3 + Real.log (y₂ / y₁)) / max Q 1 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
          (hD.le.trans hD1)
    _ ≤ 2 * K * (3 + Real.log (y₂ / y₁)) / max Q y₁ :=
        div_le_div_of_nonneg_left (by positivity) hD hD1

/-! ### Integration by parts against the primitive -/

/-- **Integration by parts against a primitive**: for `f` integrable and `w` continuous on `[p, q]` with
derivative `w₁` on `(p, q)`, `∫_p^q w f = w(q) F(q) − ∫_p^q w₁ F` with `F(u) = ∫_p^u f`. -/
theorem integral_mul_eq_primitive {f w w₁ : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hf : IntervalIntegrable f volume p q) (hwc : ContinuousOn w (Icc p q))
    (hw : ∀ θ ∈ Ioo p q, HasDerivAt w (w₁ θ) θ) (hw₁ : IntervalIntegrable w₁ volume p q) :
    ∫ θ in p..q, w θ * f θ = w q * (∫ θ in p..q, f θ) - ∫ u in p..q, w₁ u * ∫ θ in p..u, f θ := by
  have hp : p ∈ uIcc p q := left_mem_uIcc
  have hWac : AbsolutelyContinuousOnInterval (fun x => ∫ t in p..x, w₁ t) p q :=
    hw₁.absolutelyContinuousOnInterval_intervalIntegral hp
  have hFac : AbsolutelyContinuousOnInterval (fun x => ∫ t in p..x, f t) p q :=
    hf.absolutelyContinuousOnInterval_intervalIntegral hp
  have hFTC : ∀ x ∈ Icc p q, w x = w p + ∫ t in p..x, w₁ t := fun x hx => by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (hwc.mono (Icc_subset_Icc_right hx.2)) (fun θ hθ => hw θ ⟨hθ.1, hθ.2.trans_le hx.2⟩)
      (hw₁.mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le hpq]; exact Icc_subset_Icc_right hx.2))
    linarith
  have hIBP := hWac.integral_mul_deriv_eq_deriv_mul hFac
  have hdF : ∀ᵐ x, x ∈ Ι p q → deriv (fun x => ∫ t in p..x, f t) x = f x := by
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hxI
    exact (hx (uIoc_subset_uIcc hxI) p hp).deriv
  have hdW : ∀ᵐ x, x ∈ Ι p q → deriv (fun x => ∫ t in p..x, w₁ t) x = w₁ x := by
    filter_upwards [hw₁.ae_hasDerivAt_integral] with x hx hxI
    exact (hx (uIoc_subset_uIcc hxI) p hp).deriv
  have h1 : ∫ x in p..q, (∫ t in p..x, w₁ t) * deriv (fun x => ∫ t in p..x, f t) x
      = ∫ x in p..q, (∫ t in p..x, w₁ t) * f x :=
    intervalIntegral.integral_congr_ae (hdF.mono fun x hx hxI => by rw [hx hxI])
  have h2 : ∫ x in p..q, deriv (fun x => ∫ t in p..x, w₁ t) x * ∫ t in p..x, f t
      = ∫ x in p..q, w₁ x * ∫ t in p..x, f t :=
    intervalIntegral.integral_congr_ae (hdW.mono fun x hx hxI => by rw [hx hxI])
  have h3 : ∫ θ in p..q, w θ * f θ = ∫ θ in p..q, (w p * f θ + (∫ t in p..θ, w₁ t) * f θ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hpq] at hx
    rw [hFTC x hx]
    ring
  rw [h3, intervalIntegral.integral_add (hf.const_mul _) (hf.continuousOn_mul hWac.continuousOn),
    intervalIntegral.integral_const_mul, ← h1, hIBP, h2, intervalIntegral.integral_same,
    hFTC q ⟨hpq, le_rfl⟩]
  ring

/-- `|∫_p^q w f| ≤ (|w(q)| + ∫_p^q |w₁|) E` when the primitive `∫_p^u f` is at most `E` on `[p, q]`. -/
theorem abs_integral_mul_le_of_primitive {f w w₁ : ℝ → ℝ} {p q E : ℝ} (hpq : p ≤ q)
    (hf : IntervalIntegrable f volume p q) (hwc : ContinuousOn w (Icc p q))
    (hw : ∀ θ ∈ Ioo p q, HasDerivAt w (w₁ θ) θ) (hw₁ : IntervalIntegrable w₁ volume p q)
    (hE : ∀ u ∈ Icc p q, |∫ θ in p..u, f θ| ≤ E) :
    |∫ θ in p..q, w θ * f θ| ≤ (|w q| + ∫ u in p..q, |w₁ u|) * E := by
  rw [integral_mul_eq_primitive hpq hf hwc hw hw₁]
  have hFc : ContinuousOn (fun u => ∫ θ in p..u, f θ) (uIcc p q) :=
    (hf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  have hint : |∫ u in p..q, w₁ u * ∫ θ in p..u, f θ| ≤ (∫ u in p..q, |w₁ u|) * E := by
    rw [← intervalIntegral.integral_mul_const]
    refine (intervalIntegral.abs_integral_le_integral_abs hpq).trans
      (intervalIntegral.integral_mono_on hpq (hw₁.mul_continuousOn hFc).abs (hw₁.abs.mul_const E)
        fun u hu => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hE u hu) (abs_nonneg _)
  have hq := hE q ⟨hpq, le_rfl⟩
  calc |w q * (∫ θ in p..q, f θ) - ∫ u in p..q, w₁ u * ∫ θ in p..u, f θ|
      ≤ |w q| * |∫ θ in p..q, f θ| + |∫ u in p..q, w₁ u * ∫ θ in p..u, f θ| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ |w q| * E + (∫ u in p..q, |w₁ u|) * E :=
        add_le_add (mul_le_mul_of_nonneg_left hq (abs_nonneg _)) hint
    _ = (|w q| + ∫ u in p..q, |w₁ u|) * E := by ring

/-- **One piece against a dilated remainder**: for `n ≥ 1`, `0 < p ≤ q` and `w` `C¹` on `[p, q]`,
`|∫_p^q w(θ) r_Q(nθ) dθ| ≤ (|w(q)| + ∫|w₁|) · 2K(3 + log(q/p))/(n max(Q, np))`. -/
theorem abs_integral_mul_tailRem_le {Φ I : ℝ → ℝ} {B K : ℝ} (hΦ : Continuous Φ)
    (hmeas : Measurable (fullTail Φ))
    (hpart : ∀ θ, 1 < θ → Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)) atTop (𝓝 (fullTail Φ θ)))
    (hdom : ∀ θ, 1 < θ → ∀ M : ℕ, |∑ m ∈ Finset.Icc 1 M, Φ (m * θ)| ≤ B)
    (hI : ∀ t u, 1 ≤ t → 1 ≤ u → ∫ ξ in t..u, Φ ξ = I t - I u) (hIb : ∀ t, 1 ≤ t → |I t| ≤ K / t)
    (Q : ℝ) {n : ℕ} (hn : 1 ≤ n) {w w₁ : ℝ → ℝ} {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hwc : ContinuousOn w (Icc p q)) (hw : ∀ θ ∈ Ioo p q, HasDerivAt w (w₁ θ) θ)
    (hw₁ : IntervalIntegrable w₁ volume p q) :
    |∫ θ in p..q, w θ * tailRem Φ Q (n * θ)|
      ≤ (|w q| + ∫ u in p..q, |w₁ u|) * (2 * K * (3 + Real.log (q / p)) / (n * max Q (n * p))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 ≤ K := by
    have h := hIb 1 le_rfl
    rw [div_one] at h
    exact (abs_nonneg _).trans h
  have hr : ∀ θ, |tailRem Φ Q θ| ≤ 2 * B := fun θ => by
    have h1 := abs_fullTail_le_of_dom hpart hdom θ
    have h2 := abs_posTail_le_of_dom hdom Q θ
    calc |tailRem Φ Q θ| ≤ |fullTail Φ θ| + |posTail Φ Q θ| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hrm : Measurable (tailRem Φ Q) := hmeas.sub (Cvs.L2a.FullTailConvergence.measurable_posTail hΦ Q)
  have hf : IntervalIntegrable (fun θ => tailRem Φ Q (n * θ)) volume p q :=
    IntervalIntegrable.mono_fun' (g := fun _ => 2 * B) intervalIntegrable_const
      (hrm.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun θ => by
        show ‖tailRem Φ Q (n * θ)‖ ≤ 2 * B; rw [Real.norm_eq_abs]; exact hr _)
  refine abs_integral_mul_le_of_primitive hpq hf hwc hw hw₁ fun u hu => ?_
  have hnp : 0 < (n : ℝ) * p := mul_pos hn0 hp
  have hu0 : 0 < u := hp.trans_le hu.1
  rw [intervalIntegral.integral_comp_mul_left (fun x => tailRem Φ Q x) hn0.ne', smul_eq_mul, abs_mul,
    abs_inv, abs_of_pos hn0]
  have hb := abs_integral_tailRem_le_of_pos hΦ hpart hdom hI hIb Q hnp
    (mul_le_mul_of_nonneg_left hu.1 hn0.le)
  have hl : Real.log ((n : ℝ) * u / (n * p)) ≤ Real.log (q / p) := by
    rw [mul_div_mul_left _ _ hn0.ne']
    exact Real.log_le_log (div_pos hu0 hp) (div_le_div_of_nonneg_right hu.2 hp.le)
  have hD : 0 < max Q ((n : ℝ) * p) := lt_of_lt_of_le hnp (le_max_right _ _)
  calc (n : ℝ)⁻¹ * |∫ x in (n : ℝ) * p..n * u, tailRem Φ Q x|
      ≤ (n : ℝ)⁻¹ * (2 * K * (3 + Real.log ((n : ℝ) * u / (n * p))) / max Q (n * p)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (n : ℝ)⁻¹ * (2 * K * (3 + Real.log (q / p)) / max Q (n * p)) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hD.le) (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 * K * (3 + Real.log (q / p)) / (n * max Q (n * p)) := by field_simp

section Psi

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

/-- **One piece against a dilated remainder, `Φ = psi c G`**: for `n ≥ 1`, `0 < p ≤ q` and `w` `C¹` on `[p, q]`,
`|∫_p^q w(θ) r_Q(nθ) dθ| ≤ (|w(q)| + ∫|w₁|) · 2 K_T (3 + log(q/p))/(n max(Q, np))`. -/
theorem abs_integral_mul_tailRem_psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) (Q : ℝ) {n : ℕ} (hn : 1 ≤ n) {w w₁ : ℝ → ℝ} {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hwc : ContinuousOn w (Icc p q)) (hw : ∀ θ ∈ Ioo p q, HasDerivAt w (w₁ θ) θ)
    (hw₁ : IntervalIntegrable w₁ volume p q) :
    |∫ θ in p..q, w θ * tailRem (psi c G) Q (n * θ)|
      ≤ (|w q| + ∫ u in p..q, |w₁ u|)
        * (2 * ((2 * |G 1 + G (-1)| + (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)) / c ^ 2)
          * (3 + Real.log (q / p)) / (n * max Q (n * p))) := by
  have hΦ : Continuous (psi c G) :=
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hB0 : 0 ≤ B := Cvs.L2a.FullTailConvergence.BG_nonneg hc _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  refine abs_integral_mul_tailRem_le (B := B) (I := Cvs.L2a.FullTailPoleChannel.tailInt (psi c G)) hΦ
    (Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc)
    (fun θ hθ => Cvs.L2a.FullTailConvergence.tendsto_partial hg hg₁ hg₂c hc hθ)
    (fun θ hθ M => (Cvs.L2a.FullTailConvergence.abs_partial_le hg hg₁ hg₂c hc hθ.le M).trans (div_le_self hB0 hθ.le))
    (fun t u ht hu => (Cvs.L2a.FullTailPoleChannel.tailInt_sub hg hg₁ hg₂c hc ht hu).symm)
    (fun t ht => ?_) Q hn hp hpq hwc hw hw₁
  have h := Cvs.L2a.FullTailPoleChannel.abs_tailInt_le hg hg₁ hg₂c hc ht
  rw [div_div]
  exact h

end Psi

end Cvs.L2a.TruncationRemainderPrimitive
