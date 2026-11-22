import Mathlib
import Cvs.L2a.PrimeTermPairClassified
import Cvs.L2a.TwoProlateResonantPairs
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One cross column of a prime term

For `k ≥ 2`, the kθ-mode `m'` of `ψ_b` against the θ-modes of `ψ_a` on `[1, b/k]`: the first mode is the stationary
pair `(1/k)|∫_k^b ψ_b(m't)ψ_a(t/k)|`, the resonant mode `m = km'` is at most `G/(α_m(km')²)`, and every other mode is
at most `(1/k)·8G√κ_m/(c² m' m |km' − m|)`, with `α_m = (√3/2)σ_m`, `κ_m = 2c/(√3σ_m)`, `σ_m = √(c² − χ_m)`.
-/

namespace Cvs.L2a.TwoProlateCrossColumn

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- **One cross column of a prime term**: the kθ-mode `m'` of `ψ_b` against every θ-mode of `ψ_a`. -/
theorem column2_le {c χa χb χm G Ξ b : ℝ} {ψa ua ψb ub : ℝ → ℝ} {k M m' : ℕ} (hc : 0 < c)
    (hχa0 : 0 ≤ χa) (hχam : χa ≤ χm) (hχb0 : 0 ≤ χb) (hχbm : χb ≤ χm) (hχm : χm < c ^ 2)
    (hk : 2 ≤ k) (hm' : m' ∈ Finset.Icc 1 M) (hkb : (k : ℝ) ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψa : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hG0 : 0 ≤ G) :
    ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))|
      ≤ 1 / k * |∫ t in (k : ℝ)..b, ψb (m' * t) * ψa (1 / k * t)|
        + G / (√3 / 2 * √(c ^ 2 - χm) * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
            8 * G * √(2 * c / (√3 * √(c ^ 2 - χm))) / c ^ 2
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
  set κs := √(2 * c / (√3 * √(c ^ 2 - χm))) with hκs
  have hκ0 : 0 ≤ κs := sqrt_nonneg _
  have hsub2 : Icc (2 : ℝ) Ξ ⊆ Ioc 1 Ξ := fun ξ hξ => ⟨by linarith [hξ.1], hξ.2⟩
  -- split off the first mode
  have hsplit : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  conv_lhs => rw [hsplit, Finset.sum_insert (by simp)]
  have h1 : |∫ θ in (1 : ℝ)..b / k, ψa ((1 : ℕ) * θ) * ψb (m' * (k * θ))|
      = 1 / k * |∫ t in (k : ℝ)..b, ψb (m' * t) * ψa (1 / k * t)| := by
    rw [Nat.cast_one, Cvs.L2a.PrimeTermPairClassified.first_pair_eq ψa ψb hk0, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / k)]
  rw [h1]
  -- the other modes
  have hterm : ∀ m ∈ Finset.Icc 2 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))|
      ≤ (if m = k * m' then G / (√3 / 2 * √(c ^ 2 - χm) * ((k : ℝ) * m') ^ 2) else 0)
        + (if m = k * m' then 0 else 1 / k * (8 * G * κs / c ^ 2
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
      exact Cvs.L2a.TwoProlateResonantPairs.resonant2_le (ua := ua) (ub := ub) hχa0 hχam hχb0 hχbm hχm hkm hbk
        (fun ξ hξ => hGa ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩)
        (fun ξ hξ => hGb ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩) hG0
    · have hne : (m : ℝ) ≠ (k : ℝ) * m' := by
        intro h; apply hr; exact_mod_cast (show ((m : ℕ) : ℝ) = ((k * m' : ℕ) : ℝ) by push_cast; exact h)
      rw [zero_add]
      have hsep : (1 : ℝ) ≤ |(m : ℝ) - (k : ℝ) * m'| := by
        rcases Nat.lt_or_gt_of_ne hr with h | h
        · have h' : m + 1 ≤ k * m' := h
          have : (m : ℝ) + 1 ≤ (k : ℝ) * m' := by exact_mod_cast h'
          rw [abs_of_neg (by linarith)]; linarith
        · have h' : k * m' + 1 ≤ m := h
          have : (k : ℝ) * m' + 1 ≤ m := by exact_mod_cast h'
          rw [abs_of_pos (by linarith)]; linarith
      have key := Cvs.L2a.TwoProlateResonantPairs.nonres2_le hc hχa0 hχam hχb0 hχbm hχm hm2 hkm hsep hbk hmT hnT
        (fun ξ hξ => hψa ξ (hsub2 hξ)) (fun ξ hξ => hua ξ (hsub2 hξ))
        (fun ξ hξ => hψb ξ (hsub2 hξ)) (fun ξ hξ => hub ξ (hsub2 hξ))
        (fun ξ hξ => hGa ξ (hsub2 hξ)) (fun ξ hξ => hGb ξ (hsub2 hξ))
      refine key.trans (le_of_eq ?_)
      have habs : |(m : ℝ) - k * m'| = |((k * m' : ℕ) : ℝ) - m| := by
        push_cast; rw [abs_sub_comm]
      rw [habs]
      have hpos : 0 < |((k * m' : ℕ) : ℝ) - m| := by
        rw [abs_pos, sub_ne_zero]; push_cast; exact fun h => hne h.symm
      rw [hκs]
      field_simp
  have hrest : ∑ m ∈ Finset.Icc 2 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))|
      ≤ G / (√3 / 2 * √(c ^ 2 - χm) * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'), 8 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|)) := by
   calc ∑ m ∈ Finset.Icc 2 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))|
      ≤ ∑ m ∈ Finset.Icc 2 M, ((if m = k * m' then G / (√3 / 2 * √(c ^ 2 - χm) * ((k : ℝ) * m') ^ 2) else 0)
        + (if m = k * m' then 0 else 1 / k * (8 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|))))) := Finset.sum_le_sum hterm
    _ = (if k * m' ∈ Finset.Icc 2 M then G / (√3 / 2 * √(c ^ 2 - χm) * ((k : ℝ) * m') ^ 2) else 0)
        + ∑ m ∈ (Finset.Icc 2 M).filter (fun m => ¬ m = k * m'), 1 / k * (8 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|))) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite, Finset.sum_const_zero, zero_add]
    _ ≤ G / (√3 / 2 * √(c ^ 2 - χm) * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'), 8 * G * κs / c ^ 2
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

end Cvs.L2a.TwoProlateCrossColumn
