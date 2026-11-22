import Mathlib
import Cvs.L2a.ExactRootWeightedPairTotal
import Cvs.L2a.NonstationaryPairsAllShifts
import Cvs.L2a.NonstationaryPairsOneShift
import Cvs.L2a.PrimeResonanceSum
import Cvs.L2a.PrimeTermPairClassified
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesPrimeSideBound
import Cvs.L2a.TailOfModes
import Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prime side of the tail of `M` modes, for every `χ < c²`

The columns of Cvs.L2a.TwoProlateCrossColumn with `EnvelopeBeyondTwoSigmaFree`'s `σ`-free resonant and non-resonant pairs, and `ExactRootWeightedPairTotal`'s stationary sum: the prime
side of the tail is at most `2(S + (G/((3/4)c))(π²/6)Σ Λ(n)/n² + (8G(2/√3)/c²)·36(π²/6+6))`, `S` `ExactRootWeightedPairTotal`'s bound.
-/

namespace Cvs.L2a.ModeTailPrimeSideExactRoot

open Real Set ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailOfModes
open Cvs.L2a.TailModesPrimeSideBound (primeSide_eq_image)

/-- **One cross column of a prime term, `σ`-free**: the kθ-mode `m'` of `ψ_b` against every θ-mode of `ψ_a`. -/
theorem column_le {c χa χb G Ξ b : ℝ} {ψa ua ψb ub : ℝ → ℝ} {k M m' : ℕ} (hc : 0 < c)
    (hχa0 : 0 ≤ χa) (hχa : χa < c ^ 2) (hχb0 : 0 ≤ χb) (hχb : χb < c ^ 2)
    (hk : 2 ≤ k) (hm' : m' ∈ Finset.Icc 1 M) (hkb : (k : ℝ) ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψa : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χb) ψb ub ξ ≤ G)
    (hG0 : 0 ≤ G) :
    ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))|
      ≤ 1 / k * |∫ t in (k : ℝ)..b, ψb (m' * t) * ψa (1 / k * t)|
        + G / (3 / 4 * c * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
            8 * G * (2 / √3) / c ^ 2
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
  set κs := 2 / √3 with hκs
  have hκ0 : 0 ≤ κs := by positivity
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
      ≤ (if m = k * m' then G / (3 / 4 * c * ((k : ℝ) * m') ^ 2) else 0)
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
      exact Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree.resonant_c_le (ua := ua) (ub := ub) hc hχa.le hχb.le hkm hbk
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
      have key := Cvs.Prolate.Envelope.EnvelopeBeyondTwoSigmaFree.nonres_c_le hc hχa0 hχa hχb0 hχb hm2 hkm hsep hbk hmT hnT
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
      ≤ G / (3 / 4 * c * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'), 8 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|)) := by
   calc ∑ m ∈ Finset.Icc 2 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))|
      ≤ ∑ m ∈ Finset.Icc 2 M, ((if m = k * m' then G / (3 / 4 * c * ((k : ℝ) * m') ^ 2) else 0)
        + (if m = k * m' then 0 else 1 / k * (8 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|))))) := Finset.sum_le_sum hterm
    _ = (if k * m' ∈ Finset.Icc 2 M then G / (3 / 4 * c * ((k : ℝ) * m') ^ 2) else 0)
        + ∑ m ∈ (Finset.Icc 2 M).filter (fun m => ¬ m = k * m'), 1 / k * (8 * G * κs / c ^ 2
            * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|))) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite, Finset.sum_const_zero, zero_add]
    _ ≤ G / (3 / 4 * c * ((k : ℝ) * m') ^ 2)
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

/-- **One cross prime term, `σ`-free**, by columns. -/
theorem cross_term_le {c χa χb G Ξ b : ℝ} {ψa ua ψb ub : ℝ → ℝ} {k M : ℕ} (hc : 0 < c)
    (hχa0 : 0 ≤ χa) (hχa : χa < c ^ 2) (hχb0 : 0 ≤ χb) (hχb : χb < c ^ 2)
    (hk : 2 ≤ k) (hkb : (k : ℝ) ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψa : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψa (ua ξ / pP ξ) ξ)
    (hua : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψb (ub ξ / pP ξ) ξ)
    (hub : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hGa : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χa) ψa ua ξ ≤ G) (hGb : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χb) ψb ub ξ ≤ G) (hG0 : 0 ≤ G)
    (hconta : ContinuousOn ψa (Icc 1 Ξ)) (hcontb : ContinuousOn ψb (Icc 1 Ξ)) :
    |∫ θ in Ioi 1, tailF ψa M b θ * tailF ψb M b (k * θ)|
      ≤ ∑ m' ∈ Finset.Icc 1 M, (1 / k * |∫ t in (k : ℝ)..b, ψb (m' * t) * ψa (1 / k * t)|
        + G / (3 / 4 * c * ((k : ℝ) * m') ^ 2)
        + 1 / k * ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
            8 * G * (2 / √3) / c ^ 2
              * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|))) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hb1 : 1 ≤ b := hk'.trans hkb
  have hMb : (M : ℝ) * b ≤ Ξ := hΞ
  rw [integral_tailF_pair ψa ψb M hk' hkb (hconta.mono (Icc_subset_Icc le_rfl hMb)) (hcontb.mono (Icc_subset_Icc le_rfl hMb))]
  calc |∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))|
      ≤ ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ m' ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M, |∫ θ in (1 : ℝ)..b / k, ψa (m * θ) * ψb (m' * (k * θ))| :=
        Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun m' hm' =>
        column_le hc hχa0 hχa hχb0 hχb hk hm' hkb hΞ hψa hua hψb hub hGa hGb hG0

/-- **The prime side of the tail of `M` modes, for every `χ < c²`.** -/
theorem primeSide_tail_le {c χ G K Ξ b ℓ : ℝ} {ψ u : ℝ → ℝ} (P R N M : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ (c ^ 2 - χ) / c ^ 2)
    (hsℓ : 1 ≤ 3 / 5 * (√c * ℓ))
    (hidx : Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N)
    (hrb : (N : ℝ) + 2 ≤ b) (hΞ : (M : ℝ) * b ≤ Ξ)
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hcont : ContinuousOn ψ (Icc 1 Ξ)) (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G) :
    Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
        (Cvs.Zeta.Explicit.Weil.selfConvolution (Cvs.L2a.TailLogScaleTest.logScale (tailF ψ M b)))
      ≤ 2 * (G * (Cvs.L2a.ExactRootWeightedPairTotal.C1 c χ K ℓ * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
            + 3 * Cvs.L2a.ExactRootWeightedPairTotal.C3 c χ ℓ * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
            + Cvs.L2a.ExactRootWeightedPairTotal.Hc c χ K ℓ * (log (3 / 5 * (√c * ℓ)) * (1 + log (3 / 5 * (√c * ℓ))) ^ 2))
        + G / (3 / 4 * c) * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
        + 8 * G * (2 / √3) / c ^ 2 * (36 * (π ^ 2 / 6 + 6))) := by
  have hc0 : 0 < c := by linarith
  set α := 3 / 4 * c with hα
  have hα0 : 0 < α := by positivity
  set κs := 2 / √3 with hκs
  have hκ0 : 0 ≤ κs := by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [primeSide_eq_image _ (tailF_zero ψ M b)]
  set I : ℕ → ℝ := fun k => ∫ θ in Ioi 1, tailF ψ M b θ * tailF ψ M b (k * θ) with hI
  set S : ℕ → ℝ := fun k => ∑ m' ∈ Finset.Icc 1 M, |∫ t in (k : ℝ)..b, ψ (m' * t) * ψ (1 / k * t)| with hS
  set Nr : ℕ → ℝ := fun k => ∑ m' ∈ Finset.Icc 1 M, ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
    1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|) with hNr
  -- one prime term
  have hterm : ∀ k ∈ Finset.Icc 2 N, 2 * Λ k * |I k|
      ≤ 2 * (Λ k / k * S k + G / α * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2) + 8 * G * κs / c ^ 2 * (Λ k / k * Nr k)) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    have hk0 : (0 : ℝ) < k := by have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
                                 linarith
    have hΛ : 0 ≤ Λ k := vonMangoldt_nonneg
    have key := cross_term_le (k := k) (M := M) hc0 hχ0 hχ hχ0 hχ hk2 (by linarith) hΞ hψ hu hψ hu hG hG hG0 hcont hcont
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at key
    have hres : ∑ m' ∈ Finset.Icc 1 M, G / (α * ((k : ℝ) * m') ^ 2)
        ≤ G / α * (π ^ 2 / 6) * (1 / (k : ℝ) ^ 2) := by
      have e : ∀ m' ∈ Finset.Icc 1 M, G / (α * ((k : ℝ) * m') ^ 2) = G / α / (k : ℝ) ^ 2 * (1 / (m' : ℝ) ^ 2) := by
        intro m' hm'
        have : (0 : ℝ) < m' := by exact_mod_cast (Finset.mem_Icc.mp hm').1
        field_simp
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
      calc G / α / (k : ℝ) ^ 2 * ∑ m' ∈ Finset.Icc 1 M, 1 / (m' : ℝ) ^ 2
          ≤ G / α / (k : ℝ) ^ 2 * (π ^ 2 / 6) :=
            mul_le_mul_of_nonneg_left (Cvs.L2a.NonstationaryPairsOneShift.sum_inv_sq_le M) (by positivity)
        _ = _ := by field_simp
    have hnr : ∑ m' ∈ Finset.Icc 1 M, ∑ m ∈ (Finset.Icc 1 M).erase (k * m'),
        8 * G * κs / c ^ 2 * (1 / ((m' : ℝ) * m * |((k * m' : ℕ) : ℝ) - m|)) = 8 * G * κs / c ^ 2 * Nr k := by
      rw [hNr]; simp only; rw [Finset.mul_sum]; congr 1; funext m'; rw [Finset.mul_sum]
    rw [hnr] at key
    have hIk : |I k| ≤ 1 / k * S k + G / α * (π ^ 2 / 6) * (1 / (k : ℝ) ^ 2) + 1 / k * (8 * G * κs / c ^ 2 * Nr k) := by
      have := key; rw [hS]; linarith
    calc 2 * Λ k * |I k| ≤ 2 * Λ k * (1 / k * S k + G / α * (π ^ 2 / 6) * (1 / (k : ℝ) ^ 2)
          + 1 / k * (8 * G * κs / c ^ 2 * Nr k)) := mul_le_mul_of_nonneg_left hIk (by positivity)
      _ = _ := by field_simp
  -- the three sums
  have hstat := Cvs.L2a.ExactRootWeightedPairTotal.stationary_total_le (ψ := ψ) (u := u) N M hc hχ0 hχ hℓ0 hℓ hsℓ hrb hΞ
    hψ hu hG hG0 hK hcont hedge hedge1
  have hL2 := Cvs.L2a.PrimeResonanceSum.summable_vonMangoldt_div_sq.sum_le_tsum (Finset.Icc 2 N)
    (fun n _ => div_nonneg vonMangoldt_nonneg (by positivity))
  have hnon : ∑ k ∈ Finset.Icc 2 N, Λ k / k * Nr k ≤ 36 * (π ^ 2 / 6 + 6) := by
    refine le_trans ?_ (Cvs.L2a.NonstationaryPairsAllShifts.prime_pairs_le N M M)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k _ _
      apply mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      apply Finset.sum_nonneg; intro m' _; apply Finset.sum_nonneg; intro m _; positivity
  calc ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k * I k
      ≤ ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k * |I k| :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (le_abs_self _)
          (by have := (vonMangoldt_nonneg : 0 ≤ Λ k); positivity)
    _ ≤ ∑ k ∈ Finset.Icc 2 N, 2 * Λ k * |I k| :=
        Finset.sum_le_sum_of_subset_of_nonneg hidx fun k _ _ =>
          by have := (vonMangoldt_nonneg : 0 ≤ Λ k); positivity
    _ ≤ ∑ k ∈ Finset.Icc 2 N, 2 * (Λ k / k * S k + G / α * (π ^ 2 / 6) * (Λ k / (k : ℝ) ^ 2)
          + 8 * G * κs / c ^ 2 * (Λ k / k * Nr k)) := Finset.sum_le_sum hterm
    _ = 2 * (∑ k ∈ Finset.Icc 2 N, Λ k / k * S k + G / α * (π ^ 2 / 6) * ∑ k ∈ Finset.Icc 2 N, Λ k / (k : ℝ) ^ 2
          + 8 * G * κs / c ^ 2 * ∑ k ∈ Finset.Icc 2 N, Λ k / k * Nr k) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have h1 : ∑ k ∈ Finset.Icc 2 N, Λ k / k * S k ≤ _ := hstat
        exact add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left hL2 (by positivity)))
          (mul_le_mul_of_nonneg_left hnon (by positivity))

end Cvs.L2a.ModeTailPrimeSideExactRoot
