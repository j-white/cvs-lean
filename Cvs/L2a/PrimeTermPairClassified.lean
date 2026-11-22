import Mathlib
import Cvs.L2a.NonstationaryCrossPairClosed
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.ModeMellinDyadicPiece
import Cvs.Prolate.ModeSmoothWeightByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One mode pair of a prime term, classified

For `k ≥ 2` and the pair `ψ(mθ)ψ(m'kθ)` on `[1, b/k]`: the first mode (`m = 1`) is `StationaryPairsWeightedTotal`'s stationary pair after
`t = kθ`, `(1/k)|∫_k^b ψ(m't)ψ(t/k)|`; the resonant pair `m = m'k` is at most `G/(α(m'k)²)`; any other pair is at
most `4G√κ/(c² m (m'k)|m − m'k|)` (Cvs.L2a.NonstationaryCrossPairClosed), `α = (√3/2)√(c²−χ)`, `κ = 2c/(√3√(c²−χ))`.
-/

namespace Cvs.L2a.PrimeTermPairClassified

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- The first mode of `ψ₁` against the mode `m'` of `ψ₂` at `kθ` is `StationaryPairsWeightedTotal`'s pair. -/
theorem first_pair_eq (ψ₁ ψ₂ : ℝ → ℝ) {k m' b : ℝ} (hk : 0 < k) :
    ∫ θ in (1 : ℝ)..b / k, ψ₁ (1 * θ) * ψ₂ (m' * (k * θ))
      = (1 / k) * ∫ t in k..b, ψ₂ (m' * t) * ψ₁ (1 / k * t) := by
  have h := intervalIntegral.integral_comp_mul_left (a := 1) (b := b / k)
    (fun t => ψ₂ (m' * t) * ψ₁ (1 / k * t)) hk.ne'
  simp only [smul_eq_mul, mul_one] at h
  rw [show k * (b / k) = b by field_simp] at h
  rw [← one_div] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [show 1 / k * (k * θ) = 1 * θ by field_simp]; ring

/-- **The resonant pair** is at most `G/(α n²)`, `n = m'k ≥ 2`. -/
theorem resonant_le {c χ G n s : ℝ} {ψ u : ℝ → ℝ} (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hn : 2 ≤ n) (hs : 1 ≤ s)
    (hG : ∀ ξ ∈ Icc n (n * s), energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc n (n * s))) :
    |∫ θ in (1 : ℝ)..s, ψ (n * θ) * ψ (n * θ)| ≤ G / (√3 / 2 * √(c ^ 2 - χ) * n ^ 2) := by
  set α := √3 / 2 * √(c ^ 2 - χ) with hα
  have hd : 0 < c ^ 2 - χ := by linarith
  have hα0 : 0 < α := by positivity
  have hn0 : 0 < n := by linarith
  have hmem : ∀ θ ∈ Icc (1 : ℝ) s, n * θ ∈ Icc n (n * s) := fun θ hθ =>
    ⟨by nlinarith [hθ.1], mul_le_mul_of_nonneg_left hθ.2 hn0.le⟩
  have hpt : ∀ θ ∈ Icc (1 : ℝ) s, ψ (n * θ) * ψ (n * θ) ≤ G / (α * n ^ 2) * (1 / θ ^ 2) := fun θ hθ => by
    have hθ0 : 0 < θ := by linarith [hθ.1]
    have h := Cvs.Prolate.Mellin.ModeMellinDyadicPiece.abs_psi_le (u := u) hχ0 hχ (by nlinarith [hθ.1] : 2 ≤ n * θ)
      (hG _ (hmem θ hθ))
    have h2 : ψ (n * θ) ^ 2 ≤ G / (α * (n * θ) ^ 2) := by
      have := sq_abs (ψ (n * θ)) ▸ pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_sqrt (by positivity)] at this
    calc ψ (n * θ) * ψ (n * θ) = ψ (n * θ) ^ 2 := by ring
      _ ≤ G / (α * (n * θ) ^ 2) := h2
      _ = G / (α * n ^ 2) * (1 / θ ^ 2) := by field_simp
  have hnn : ∀ θ ∈ Icc (1 : ℝ) s, 0 ≤ ψ (n * θ) * ψ (n * θ) := fun θ _ => mul_self_nonneg _
  have hc2 : ContinuousOn (fun θ => ψ (n * θ) * ψ (n * θ)) (Icc 1 s) := by
    have h1 : ContinuousOn (fun θ => ψ (n * θ)) (Icc 1 s) :=
      hcont.comp (continuousOn_const.mul continuousOn_id) hmem
    exact h1.mul h1
  have hI0 : 0 ≤ ∫ θ in (1 : ℝ)..s, ψ (n * θ) * ψ (n * θ) := intervalIntegral.integral_nonneg hs hnn
  rw [abs_of_nonneg hI0]
  calc ∫ θ in (1 : ℝ)..s, ψ (n * θ) * ψ (n * θ) ≤ ∫ θ in (1 : ℝ)..s, G / (α * n ^ 2) * (1 / θ ^ 2) :=
        intervalIntegral.integral_mono_on hs (hc2.intervalIntegrable_of_Icc hs)
          ((continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2)
            (fun θ hθ => pow_ne_zero 2 (by linarith [hθ.1] : (0:ℝ) < θ).ne'))).intervalIntegrable_of_Icc hs) hpt
    _ = G / (α * n ^ 2) * (1 - 1 / s) := by
        rw [intervalIntegral.integral_const_mul, Cvs.Prolate.ModeSmoothWeightByParts.integral_inv_sq one_pos hs]; ring
    _ ≤ G / (α * n ^ 2) := by
        have hs0 : (0:ℝ) < s := by linarith
        have : 0 ≤ 1 / s := by positivity
        have hG' : 0 ≤ G / (α * n ^ 2) := by positivity
        nlinarith

/-- **A non-resonant pair**, `m, n ≥ 2`, `m ≠ n`, by Cvs.L2a.NonstationaryCrossPairClosed. -/
theorem nonres_le {c χ G Ξ m n T : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hmn : m ≠ n) (hT : 1 ≤ T) (hmT : m * T ≤ Ξ) (hnT : n * T ≤ Ξ)
    (hψ : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc 2 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Icc 2 Ξ, energy (aP c χ) ψ u ξ ≤ G) :
    |∫ θ in (1 : ℝ)..T, ψ (m * θ) * ψ (n * θ)|
      ≤ 4 * G * √(2 * c / (√3 * √(c ^ 2 - χ))) / (c ^ 2 * (m * n * |m - n|)) := by
  rcases lt_or_gt_of_ne hmn with h | h
  · have key := Cvs.L2a.NonstationaryCrossPairClosed.pair_le hc hχ0 hχ (by linarith : (0:ℝ) < m) h (by linarith) hT hnT hψ hu hG
    have e : ∫ θ in (1 : ℝ)..T, ψ (m * θ) * ψ (n * θ) = ∫ θ in (1 : ℝ)..T, ψ (n * θ) * ψ (m * θ) := by
      congr 1; funext θ; ring
    rw [e, abs_of_neg (by linarith : m - n < 0)]
    simp only [one_pow, mul_one] at key
    convert key using 3; ring
  · have key := Cvs.L2a.NonstationaryCrossPairClosed.pair_le hc hχ0 hχ (by linarith : (0:ℝ) < n) h (by linarith) hT hmT hψ hu hG
    rw [abs_of_pos (by linarith : 0 < m - n)]
    simp only [one_pow, mul_one] at key
    exact key

/-- **One column of a prime term**: the kθ-mode `m'` against every θ-mode. -/
theorem column_le {c χ G Ξ b : ℝ} {ψ u : ℝ → ℝ} {k M m' : ℕ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2)
    (hk : 2 ≤ k) (hm' : m' ∈ Finset.Icc 1 M) (hkb : (k : ℝ) ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) :
    ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b / k, ψ (m * θ) * ψ (m' * (k * θ))|
      ≤ 1 / k * |∫ t in (k : ℝ)..b, ψ (m' * t) * ψ (1 / k * t)|
        + G / (√3 / 2 * √(c ^ 2 - χ) * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
            4 * G * √(2 * c / (√3 * √(c ^ 2 - χ))) / c ^ 2
              * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|)) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hm1 : 1 ≤ m' := (Finset.mem_Icc.mp hm').1
  have hmM : m' ≤ M := (Finset.mem_Icc.mp hm').2
  have hm1' : (1 : ℝ) ≤ m' := by exact_mod_cast hm1
  have hmM' : (m' : ℝ) ≤ M := by exact_mod_cast hmM
  have hM1 : 1 ≤ M := hm1.trans hmM
  have hb0 : 0 ≤ b := by linarith
  have hbk : 1 ≤ b / k := by rw [le_div_iff₀ hk0]; linarith
  have hkm : (2 : ℝ) ≤ (k : ℝ) * m' := by nlinarith
  set κs := √(2 * c / (√3 * √(c ^ 2 - χ))) with hκs
  have hκ0 : 0 ≤ κs := sqrt_nonneg _
  have hsub2 : Icc (2 : ℝ) Ξ ⊆ Ioc 1 Ξ := fun ξ hξ => ⟨by linarith [hξ.1], hξ.2⟩
  -- split off the first mode
  have hsplit : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  conv_lhs => rw [hsplit, Finset.sum_insert (by simp)]
  have h1 : |∫ θ in (1 : ℝ)..b / k, ψ ((1 : ℕ) * θ) * ψ (m' * (k * θ))|
      = 1 / k * |∫ t in (k : ℝ)..b, ψ (m' * t) * ψ (1 / k * t)| := by
    rw [Nat.cast_one, first_pair_eq ψ ψ hk0, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / k)]
  rw [h1]
  -- the other modes
  have hterm : ∀ m ∈ Finset.Icc 2 M, |∫ θ in (1 : ℝ)..b / k, ψ (m * θ) * ψ (m' * (k * θ))|
      ≤ (if m = k * m' then G / (√3 / 2 * √(c ^ 2 - χ) * ((k : ℝ) * m') ^ 2) else 0)
        + (if m = k * m' then 0 else 1 / k * (4 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|)))) := by
    intro m hm
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM2 : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have e : ∀ θ : ℝ, (m' : ℝ) * (k * θ) = ((k : ℝ) * m') * θ := fun θ => by ring
    simp_rw [e]
    have hmT : (m : ℝ) * (b / k) ≤ Ξ := by
      have : (m : ℝ) * (b / k) ≤ M * b := by
        calc (m : ℝ) * (b / k) ≤ M * (b / k) := mul_le_mul_of_nonneg_right hmM2 (by positivity)
          _ ≤ M * b := mul_le_mul_of_nonneg_left (div_le_self hb0 (by linarith)) (by positivity)
      linarith
    have hnT : (k : ℝ) * m' * (b / k) ≤ Ξ := by
      have : (k : ℝ) * m' * (b / k) = m' * b := by field_simp
      rw [this]; nlinarith
    split_ifs with hr
    · have hmr : (m : ℝ) = (k : ℝ) * m' := by rw [hr]; push_cast; ring
      rw [hmr, add_zero]
      exact resonant_le (u := u) hχ0 hχ hkm hbk
        (fun ξ hξ => hG ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩) hG0
        (hcont.mono fun ξ hξ => ⟨by linarith [hξ.1], by linarith [hξ.2]⟩)
    · have hne : (m : ℝ) ≠ (k : ℝ) * m' := by
        intro h; apply hr; exact_mod_cast (show ((m : ℕ) : ℝ) = ((k * m' : ℕ) : ℝ) by push_cast; exact h)
      rw [zero_add]
      have key := nonres_le (u := u) hc hχ0 hχ hm2 hkm hne hbk hmT hnT
        (fun ξ hξ => hψ ξ (hsub2 hξ)) (fun ξ hξ => hu ξ (hsub2 hξ)) (fun ξ hξ => hG ξ (hsub2 hξ))
      refine key.trans (le_of_eq ?_)
      have habs : |(m : ℝ) - k * m'| = |((k * m' : ℕ) : ℝ) - m| := by
        push_cast; rw [abs_sub_comm]
      rw [habs]
      have hpos : 0 < |((k * m' : ℕ) : ℝ) - m| := by
        rw [abs_pos, sub_ne_zero]; push_cast; exact fun h => hne h.symm
      rw [hκs]
      field_simp
  have hrest : ∑ m ∈ Finset.Icc 2 M, |∫ θ in (1 : ℝ)..b / k, ψ (m * θ) * ψ (m' * (k * θ))|
      ≤ G / (√3 / 2 * √(c ^ 2 - χ) * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'), 4 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|)) := by
   calc ∑ m ∈ Finset.Icc 2 M, |∫ θ in (1 : ℝ)..b / k, ψ (m * θ) * ψ (m' * (k * θ))|
      ≤ ∑ m ∈ Finset.Icc 2 M, ((if m = k * m' then G / (√3 / 2 * √(c ^ 2 - χ) * ((k : ℝ) * m') ^ 2) else 0)
        + (if m = k * m' then 0 else 1 / k * (4 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|))))) := Finset.sum_le_sum hterm
    _ = (if k * m' ∈ Finset.Icc 2 M then G / (√3 / 2 * √(c ^ 2 - χ) * ((k : ℝ) * m') ^ 2) else 0)
        + ∑ m ∈ (Finset.Icc 2 M).filter (fun m => ¬ m = k * m'), 1 / k * (4 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|))) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite, Finset.sum_const_zero, zero_add]
    _ ≤ G / (√3 / 2 * √(c ^ 2 - χ) * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'), 4 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|)) := by
        apply add_le_add
        · split_ifs
          · exact le_rfl
          · positivity
        · rw [Finset.mul_sum]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            simp only [Finset.mem_filter, Finset.mem_Icc] at hm
            simp only [Finset.mem_erase, Finset.mem_Icc]
            exact ⟨hm.2, by omega, hm.1.2⟩
          · intro m _ _; positivity
  linarith

end Cvs.L2a.PrimeTermPairClassified
