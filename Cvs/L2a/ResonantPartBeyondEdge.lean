import Mathlib
import Cvs.L2a.PrimePairingResonantSplit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The resonant part at `k` is the mode masses beyond the edge, over `k`

The resonant pairs at `k` are `(k m′, m′)` with `k m′ ≤ M`, and each resonant tail energy
`(1/(k m′)) ∫_{k m′}^{m′ b} Φ²` is `(1/k) ∫_k^b Φ(m′ξ)² dξ`: so `resPart(k) = (1/k) Σ_{k m′ ≤ M} ∫_k^b Φ(m′ξ)² dξ`,
the mode masses of the sub-tail of `⌊M/k⌋` modes on `[k, b]`, over `k` — the edge `[1, k)` removed.
-/

namespace Cvs.L2a.ResonantPartBeyondEdge

open Real Set MeasureTheory
open Cvs.L2a.PrimePairingResonantSplit

/-- The resonant pairs at `k` are `(k m′, m′)` over the modes `m′` with `k m′ ≤ M`. -/
theorem resPairs_eq_image' (M : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    resPairs M k = ((Finset.Icc 1 M).filter (fun m' => k * m' ≤ M)).image (fun m' => (k * m', m')) := by
  ext ⟨m, m'⟩
  simp only [resPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hm1, hmM⟩, ⟨hm'1, hm'M⟩⟩, hres⟩
    exact ⟨m', ⟨⟨hm'1, hm'M⟩, by rw [← hres]; exact hmM⟩, hres.symm, rfl⟩
  · rintro ⟨n, ⟨⟨hn1, hnM⟩, hkn⟩, rfl, rfl⟩
    exact ⟨⟨⟨by nlinarith, hkn⟩, ⟨hn1, hnM⟩⟩, rfl⟩

/-- A resonant tail energy is a mode mass on `[k, b]` over `k`:
`(1/(k m′)) ∫_{k m′}^{m′ b} Φ² = (1/k) ∫_k^b Φ(m′ξ)² dξ`. -/
theorem tail_energy_eq (Φ : ℝ → ℝ) {b : ℝ} {k m' : ℕ} (hk : 1 ≤ k) (hm' : 1 ≤ m') :
    (1 / ((k : ℝ) * m')) * ∫ ξ in ((k : ℝ) * m')..(m' * b), Φ ξ ^ 2
      = (1 / (k : ℝ)) * ∫ ξ in (k : ℝ)..b, Φ (m' * ξ) ^ 2 := by
  have hm0 : (m' : ℝ) ≠ 0 := by exact_mod_cast (show m' ≠ 0 by omega)
  rw [intervalIntegral.integral_comp_mul_left (fun ξ => Φ ξ ^ 2) hm0, smul_eq_mul]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [show (m' : ℝ) * k = k * m' by ring]
  field_simp

/-- **The resonant part at `k` is the mode masses beyond the edge, over `k`.** -/
theorem resPart_eq_modes_beyond (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    resPart Φ M b k
      = (1 / (k : ℝ)) * ∑ m' ∈ (Finset.Icc 1 M).filter (fun m' => k * m' ≤ M),
          ∫ ξ in (k : ℝ)..b, Φ (m' * ξ) ^ 2 := by
  unfold resPart
  rw [resPairs_eq_image' M hk, Finset.sum_image (fun n _ n' _ h => ((Prod.mk.injEq _ _ _ _).mp h).2),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m' hm'
  rw [Finset.mem_filter, Finset.mem_Icc] at hm'
  have := tail_energy_eq Φ (b := b) hk hm'.1.1
  simp only [Nat.cast_mul] at this ⊢
  exact this

end Cvs.L2a.ResonantPartBeyondEdge
