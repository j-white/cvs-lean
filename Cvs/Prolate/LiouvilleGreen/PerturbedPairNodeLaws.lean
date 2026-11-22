import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Cvs.Upstream.PhaseAmplitudeZeroPerCell

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# From a perturbed Liouville–Green pair to the node and Neumann laws

If `V₀ = Ma(cos ϑ + ε₀)`, `V₀' = Mb(−sin ϑ + ε₁)` and `|e| ≤ ρMa`, `|e'| ≤ ρMb`, then `Y = V₀ + e` is again such a pair
with errors `|ε₀| + ρ`, `|ε₁| + ρ`; with the phase identity `ϑ = Φ − E − π/4 + D` a zero of `Y` puts `Φ/π + ¼ − E/π`
within `(arcsin(|ε₀| + ρ) + |D|)/π` of `ℤ`, a Robin point puts `Φ/π − ¼ − E/π` within the Robin analogue, and a
shift `δχ` of the spectral parameter enters the Liouville form as `δχ·q/ξ`, `q = (α − ξ)/(T₀ − t²)`.
-/

noncomputable section

open Real Set

namespace Cvs.Prolate.LiouvilleGreen.PerturbedPairNodeLaws

/-- `|cos θ| ≤ ρ` puts `θ` within `arcsin ρ` of `π/2 + πℤ`. -/
theorem exists_near_node_le {θ ρ : ℝ} (h : |cos θ| ≤ ρ) : ∃ n : ℤ, |θ - (π / 2 + n * π)| ≤ arcsin ρ := by
  refine ⟨⌊θ / π⌋, Cvs.Upstream.PhaseAmplitudeZeroPerCell.abs_le_arcsin_of_abs_sin_le
    (Cvs.Upstream.PhaseAmplitudeZeroPerCell.abs_sub_floor_le θ) ?_⟩
  rwa [Cvs.Upstream.PhaseAmplitudeZeroPerCell.cos_eq_neg_sign_mul_sin θ ⌊θ / π⌋, abs_neg, abs_mul,
    Cvs.Upstream.PhaseAmplitudeZeroPerCell.abs_neg_one_zpow, one_mul] at h

/-- **The phase identity at a node**: `ϑ = Φ − E − π/4 + D` within `δ` of `π/2 + nπ` puts `Φ/π + ¼ − E/π` within
`(δ + |D|)/π` of `n + 1`. -/
theorem abs_sub_int_le_of_node {ϑ Φ E D δ : ℝ} {n : ℤ} (hϑ : ϑ = Φ - E - π / 4 + D)
    (hn : |ϑ - (π / 2 + n * π)| ≤ δ) : |Φ / π + 1 / 4 - E / π - ((n + 1 : ℤ) : ℝ)| ≤ (δ + |D|) / π := by
  have hp := pi_pos
  have e : Φ / π + 1 / 4 - E / π - ((n + 1 : ℤ) : ℝ) = ((ϑ - (π / 2 + n * π)) - D) / π := by
    rw [hϑ]; push_cast; field_simp; ring
  rw [e, abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right (le_trans (abs_sub _ _) (add_le_add hn le_rfl)) hp.le

/-- **A perturbed pair**: `V₀ = Ma(cos ϑ + ε₀)` and `|e| ≤ ρMa` give `V₀ + e = Ma(cos ϑ + r)` with
`|r| ≤ |ε₀| + ρ`; the same holds for the derivative with `−sin ϑ`. -/
theorem exists_rep_add {V e M a c ε₀ ρ : ℝ} (hM : 0 < M) (ha : 0 < a) (hV : V = M * a * (c + ε₀))
    (he : |e| ≤ ρ * (M * a)) : ∃ r, V + e = M * a * (c + r) ∧ |r| ≤ |ε₀| + ρ := by
  refine ⟨ε₀ + e / (M * a), by rw [hV]; field_simp; ring, ?_⟩
  refine le_trans (abs_add_le _ _) (add_le_add le_rfl ?_)
  rw [abs_div, abs_of_pos (mul_pos hM ha), div_le_iff₀ (mul_pos hM ha)]
  exact he

/-- **The node law in the Liouville–Green frame**: if `V₀ = Ma(cos ϑ + ε₀)` with `|ε₀| ≤ η`, `|e| ≤ ρMa`,
`ϑ = Φ − E − π/4 + D` and `V₀ + e = 0`, then `Φ/π + ¼ − E/π` lies within `(arcsin(η + ρ) + |D|)/π` of `ℤ`. -/
theorem exists_int_of_zero {V e M a ϑ ε₀ ρ η Φ E D : ℝ} (hM : 0 < M) (ha : 0 < a)
    (hV : V = M * a * (cos ϑ + ε₀)) (hε₀ : |ε₀| ≤ η) (he : |e| ≤ ρ * (M * a))
    (hϑ : ϑ = Φ - E - π / 4 + D) (h0 : V + e = 0) :
    ∃ n : ℤ, |Φ / π + 1 / 4 - E / π - n| ≤ (arcsin (η + ρ) + |D|) / π := by
  obtain ⟨r, hr, hrb⟩ := exists_rep_add hM ha hV he
  rw [h0] at hr
  have hcos : cos ϑ = -r := by
    rcases mul_eq_zero.mp hr.symm with h | h
    · exact absurd h (mul_pos hM ha).ne'
    · linarith
  obtain ⟨n, hn⟩ := exists_near_node_le (θ := ϑ) (ρ := η + ρ) (by rw [hcos, abs_neg]; linarith)
  exact ⟨n + 1, abs_sub_int_le_of_node hϑ hn⟩

/-! ### Normalising a Volterra bound -/

/-- **Normalisation**: for `Q ≥ ¼` and `N > 0`, `|e| ≤ Q^{−1/2}B` gives `|e| ≤ (2B/N)·(N/√2)Q^{−1/4}`, and `|e'| ≤ B`
gives `|e'| ≤ (2B/N)·(N/√2)Q^{1/4}`. -/
theorem normalise_volterra {Q N B e e₁ : ℝ} (hQ : 1 / 4 ≤ Q) (hN : 0 < N) (hB : 0 ≤ B)
    (he : |e| ≤ B / √Q) (he₁ : |e₁| ≤ B) :
    |e| ≤ 2 * B / N * (N / √2 * (1 / √(√Q))) ∧ |e₁| ≤ 2 * B / N * (N / √2 * √(√Q)) := by
  have hQ0 : 0 < Q := by linarith
  have hs : 0 < √Q := sqrt_pos.mpr hQ0
  have hss : 0 < √(√Q) := sqrt_pos.mpr hs
  have h2 : 0 < √2 := by positivity
  have hsq : √(√Q) ^ 2 = √Q := sq_sqrt hs.le
  have hhalf : 1 / 2 ≤ √Q := by
    rw [show (1 : ℝ) / 2 = √(1 / 4) by rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hQ
  have h22 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  have hk : 1 ≤ √(√Q) * √2 := by
    have : (√(√Q) * √2) ^ 2 = 2 * √Q := by rw [mul_pow, hsq, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
    nlinarith [mul_pos hss h2]
  have hinv : 1 / √(√Q) ≤ √2 := by rw [div_le_iff₀ hss]; linarith
  constructor
  · have e1 : B / √Q = B / √(√Q) * (1 / √(√Q)) := by rw [div_mul_div_comm, mul_one, ← sq, hsq]
    have e2 : 2 * B / N * (N / √2 * (1 / √(√Q))) = B / √(√Q) * √2 := by
      field_simp; nlinarith [h22]
    rw [e2]
    calc |e| ≤ B / √Q := he
      _ = B / √(√Q) * (1 / √(√Q)) := e1
      _ ≤ B / √(√Q) * √2 := mul_le_mul_of_nonneg_left hinv (by positivity)
  · have e2 : 2 * B / N * (N / √2 * √(√Q)) = B * (√(√Q) * √2) := by
      field_simp; nlinarith [h22]
    rw [e2]
    nlinarith

/-! ### Complex forcing -/

end Cvs.Prolate.LiouvilleGreen.PerturbedPairNodeLaws
