import Mathlib
import Cvs.L2a.TailOfModes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The resonant split of a tail's prime pairing

For a tail `F = tailF Φ M b` and `1 ≤ k ≤ b`, the pairing `∫F(θ)F(kθ)` is the sum over mode pairs `(m, m')`
(Cvs.L2a.TailOfModes), and the resonant pairs `m = k m'` integrate to the tail energies `(1/(k m')) ∫_{k m'}^{m' b} Φ²`: each is
nonnegative and at most the mode-`k m'` diagonal mass `∫_1^b Φ(k m' θ)² dθ` of the tail.
-/

namespace Cvs.L2a.PrimePairingResonantSplit

open Real Set MeasureTheory
open Cvs.L2a.TailOfModes

/-- The resonant mode pairs `(m, m')` with `m = k m'` among `M` modes. -/
def resPairs (M k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => p.1 = k * p.2)

/-- The non-resonant mode pairs, `m ≠ k m'`. -/
def nonresPairs (M k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => ¬ p.1 = k * p.2)

/-- The resonant part of the pairing at `k`: the tail energies `(1/(k m')) ∫_{k m'}^{m' b} Φ²`. -/
noncomputable def resPart (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ resPairs M k, (1 / ((k : ℝ) * p.2)) * ∫ ξ in ((k : ℝ) * p.2)..(p.2 * b), Φ ξ ^ 2

/-- The non-resonant part of the pairing at `k`. -/
noncomputable def nonresPart (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ nonresPairs M k, ∫ θ in (1 : ℝ)..b / k, Φ (p.1 * θ) * Φ (p.2 * (k * θ))

/-- A resonant pair integrates to a tail energy: `∫_1^{b/k} Φ(k m' θ)² dθ = (1/(k m')) ∫_{k m'}^{m' b} Φ²`. -/
theorem resonant_integral (Φ : ℝ → ℝ) {b : ℝ} {k m' : ℕ} (hk : 1 ≤ k) (hm' : 1 ≤ m') :
    ∫ θ in (1 : ℝ)..b / k, Φ ((k : ℝ) * m' * θ) * Φ (m' * (k * θ))
      = (1 / ((k : ℝ) * m')) * ∫ ξ in ((k : ℝ) * m')..(m' * b), Φ ξ ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hkm : ((k : ℝ) * m') ≠ 0 := by positivity
  have e : ∀ θ, Φ ((k : ℝ) * m' * θ) * Φ (m' * (k * θ)) = (fun ξ => Φ ξ ^ 2) ((k : ℝ) * m' * θ) := by
    intro θ; simp only; rw [show (m' : ℝ) * (k * θ) = k * m' * θ by ring]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_comp_mul_left (fun ξ => Φ ξ ^ 2) hkm, smul_eq_mul]
  congr 1
  · rw [one_div]
  · rw [mul_one]; congr 1; field_simp

/-- **The pairing splits into its resonant and non-resonant parts.** -/
theorem pairing_eq_res_add_nonres (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkb : (k : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    ∫ θ in Ioi 1, tailF Φ M b θ * tailF Φ M b (k * θ) = resPart Φ M b k + nonresPart Φ M b k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [integral_tailF_pair Φ Φ M hk1 hkb hcont hcont, ← Finset.sum_product']
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M ×ˢ Finset.Icc 1 M) (fun p => p.1 = k * p.2)]
  unfold resPart nonresPart resPairs nonresPairs
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨hm1, _⟩, ⟨hm'1, _⟩⟩, hres⟩ := hp
  have hcast : (p.1 : ℝ) = (k : ℝ) * p.2 := by rw [hres]; push_cast; ring
  rw [hcast]
  exact resonant_integral Φ hk hm'1

/-- A resonant tail energy is at most the diagonal mass of its mode: `(1/(k m')) ∫_{k m'}^{m' b} Φ² ≤ ∫_1^b Φ(k m' θ)² dθ`. -/
theorem resonant_le_mode_mass (Φ : ℝ → ℝ) {b : ℝ} {k m' : ℕ} (hk : 1 ≤ k) (hm' : 1 ≤ m') (hkb : (k : ℝ) ≤ b)
    (hint : IntervalIntegrable (fun ξ => Φ ξ ^ 2) volume ((k : ℝ) * m') ((k : ℝ) * m' * b)) :
    (1 / ((k : ℝ) * m')) * ∫ ξ in ((k : ℝ) * m')..(m' * b), Φ ξ ^ 2
      ≤ ∫ θ in (1 : ℝ)..b, Φ ((k : ℝ) * m' * θ) ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hkm : ((k : ℝ) * m') ≠ 0 := by positivity
  have hb : (1 : ℝ) ≤ b := le_trans (by exact_mod_cast hk) hkb
  rw [intervalIntegral.integral_comp_mul_left (fun ξ => Φ ξ ^ 2) hkm, smul_eq_mul, mul_one, one_div]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h1 : (k : ℝ) * m' ≤ m' * b := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hkb hm0.le
  have h2 : (m' : ℝ) * b ≤ k * m' * b := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hmb : 0 ≤ (m' : ℝ) * b := by positivity
    calc (m' : ℝ) * b = 1 * (m' * b) := by ring
      _ ≤ k * (m' * b) := mul_le_mul_of_nonneg_right this hmb
      _ = k * m' * b := by ring
  exact intervalIntegral.integral_mono_interval (le_refl _) h1 h2
    (Filter.Eventually.of_forall fun ξ => sq_nonneg (Φ ξ)) hint

end Cvs.L2a.PrimePairingResonantSplit
