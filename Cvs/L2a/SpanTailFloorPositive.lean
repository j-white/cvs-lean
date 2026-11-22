import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailFloorFromPairNodes
import Cvs.L2a.TreeBoundInverseScaling
import Cvs.Prolate.Gram.RungGramFloorAtInfinity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The span tail Gram floor with a positive constant

Under the large-`c` floor (Cvs.L2a.SpanTailFloorLargeC), if every tail bound is at most `τ` times every mass, `T_j ≤ τ ∫₁ᵇψ_i²`, with
`(R + 1)τ ≤ m₀/4` for `R` rungs, then `∫₁ᵇ (G + Σ_m G(m·))² ≥ (m₀/4) Σ_i a_i² ∫₁ᵇ ψ_i²`: a Gram floor `m₀/4` on the
whole span. The remainder `Λ` is nonnegative, so `m₀ < 1`.
-/

namespace Cvs.L2a.SpanTailFloorPositive

open Real Finset Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.TreeBoundInverseScaling Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The boundary constant at `c = 1` is nonnegative for `b ≥ 2`, `m ≥ 2`. -/
theorem Bd_unit_nonneg {m b q₁ q₂ : ℝ} (hm : 2 ≤ m) (hb : 2 ≤ b) : 0 ≤ Bd 1 m b q₁ q₂ := by
  unfold Bd κ₁R κ₂R
  have ht : (4:ℝ) ≤ m ^ 2 := by nlinarith
  have hb2 : (4:ℝ) ≤ b ^ 2 := by nlinarith
  have hden : 0 < (1:ℝ) ^ 2 * b ^ 2 * (m ^ 2 - 1) * (m ^ 2 * b ^ 2 - m ^ 2 - 1) := by
    apply mul_pos (mul_pos (by positivity) (by linarith))
    nlinarith [mul_le_mul ht hb2 (by norm_num) (by positivity)]
  have h1 : 0 ≤ (1 * b ^ 2 - 1) / ((1:ℝ) ^ 2 * b ^ 2 * (m ^ 2 - 1) * (1 * m ^ 2 * b ^ 2 - m ^ 2 - 1)) := by
    apply div_nonneg (by linarith); simpa using hden.le
  have h2 : 0 ≤ (m ^ 2 * b ^ 2 - 1) / ((1:ℝ) ^ 2 * b ^ 2 * (m ^ 2 - 1) * (1 * m ^ 2 * b ^ 2 - m ^ 2 - 1)) := by
    apply div_nonneg (by nlinarith [mul_le_mul ht hb2 (by norm_num) (by positivity)]); simpa using hden.le
  have hm0 : 0 < m := by linarith
  positivity

/-- The remainder `Λ` is nonnegative. -/
theorem Λpair_nonneg {s χm b q₁ q₂ : ℝ} (hs : 0 < s) (hχm : 0 ≤ χm) (hb : 2 ≤ b) (M N : ℕ) :
    0 ≤ Λpair s χm b q₁ q₂ M N := by
  unfold Λpair
  have hmem : ∀ n ∈ Finset.Icc 2 M, (2 : ℝ) ≤ n := fun n hn => by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
  apply add_nonneg
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro m hm
    apply Finset.sum_nonneg; intro m' hm'
    split_ifs with hmm
    · exact le_rfl
    · unfold Tsym
      have hm2 := hmem m hm
      have hm'2 := hmem m' hm'
      split_ifs with hlt
      · have h12 : (m : ℝ) + 1 ≤ m' := by exact_mod_cast hlt
        have := ρm_nonneg hm2 h12 hχm
        have hm0 : (0:ℝ) < m := by linarith
        have hm'0 : (0:ℝ) < m' := by linarith
        positivity
      · have hlt' : m' < m := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hmm)
        have h12 : (m' : ℝ) + 1 ≤ m := by exact_mod_cast hlt'
        have := ρm_nonneg hm'2 h12 hχm
        have hm0 : (0:ℝ) < m := by linarith
        have hm'0 : (0:ℝ) < m' := by linarith
        positivity
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg; intro m hm
    have hm2 := hmem m hm
    have hρ := ρf_nonneg hm2 hχm
    have hBd := Bd_unit_nonneg (q₁ := q₁) (q₂ := q₂) hm2 hb
    have hm0 : (0:ℝ) < m := by linarith
    positivity

set_option maxHeartbeats 800000 in
/-- **The span tail Gram floor with the constant `m₀/4`**, for every large `c` and tails small against the masses. -/
theorem span_floor_positive {c c₀ h h₂ hη b s ε δ μ₁ μ₂ τ : ℝ} {M : ℕ} (N : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hs : 0 < s) (hh : 0 < h) (hh' : h ≤ 1 / 5) (hh₂ : 0 < h₂)
    (hh₂' : h₂ ≤ 1 / 20) (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 2 ≤ b)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) b)
    (hm₀ : 0 < margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N)
    (hK : 2 * Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N
      / margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N ≤ c)
    (hτ0 : 0 ≤ τ)
    (hT : ∀ i j, tailBound c (χ j) (g j) b ≤ τ * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hτ : ((Fintype.card ι : ℝ) + 1) * τ ≤ margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N / 4) :
    margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N / 4
        * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2
      ≤ ∫ θ in (1 : ℝ)..b, (Gk a χ (fun i => psi c (g i)) 0 θ
          + ∑ m ∈ Finset.Icc 2 M, Gk a χ (fun i => psi c (g i)) 0 (m * θ)) ^ 2 := by
  have hfloor := span_floor_large_c (c₀ := c₀) (h := h) (h₂ := h₂) (hη := hη) (b := b) (s := s) (ε := ε) (δ := δ)
    (μ₁ := μ₁) (μ₂ := μ₂) N g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hs hh hh' hh₂ hh₂' hη0 hη' hb
    hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hm₀ hK
  set m₀ := margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N with hm₀def
  have hm₀1 : m₀ ≤ 1 := by
    have hΛ := Λpair_nonneg (s := s) (χm := 1) (q₁ := Qpsi c g g₁ g₂ χ b / c) (q₂ := Qu c g g₁ g₂ χ b / c ^ 3)
      hs zero_le_one hb M N
    have : s ≤ max s (5 / (6 * s)) := le_max_left _ _
    rw [hm₀def]; unfold margin; linarith
  have e : (∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) - ∑ j, tailBound c (χ j) (g j) b))
        - (∑ i, a i ^ 2 * massB c (χ i) (g i) b) * (1 - m₀ / 2)
      = ∑ i, (a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) - ∑ j, tailBound c (χ j) (g j) b)
          - a i ^ 2 * massB c (χ i) (g i) b * (1 - m₀ / 2)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  rw [e] at hfloor
  refine le_trans ?_ hfloor
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  set mass := ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 with hmass
  have hmass0 : 0 ≤ mass := (hMpos i).le
  have hsumT : ∑ j, tailBound c (χ j) (g j) b ≤ (Fintype.card ι : ℝ) * τ * mass := by
    calc ∑ j, tailBound c (χ j) (g j) b ≤ ∑ _j : ι, τ * mass := Finset.sum_le_sum fun j _ => hT i j
      _ = (Fintype.card ι : ℝ) * τ * mass := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hTi : tailBound c (χ i) (g i) b ≤ τ * mass := hT i i
  have hmB : massB c (χ i) (g i) b = mass + tailBound c (χ i) (g i) b := rfl
  rw [hmB]
  have h1 : 0 ≤ 1 - m₀ / 2 := by linarith
  have h2 : (1 - m₀ / 2) * tailBound c (χ i) (g i) b ≤ (1 - m₀ / 2) * (τ * mass) :=
    mul_le_mul_of_nonneg_left hTi h1
  have h3 : (1 - m₀ / 2) * (τ * mass) ≤ τ * mass := by
    have : 0 ≤ τ * mass := by positivity
    nlinarith
  have hτ' : ((Fintype.card ι : ℝ) + 1) * τ * mass ≤ m₀ / 4 * mass := mul_le_mul_of_nonneg_right hτ hmass0
  have ha : 0 ≤ a i ^ 2 := sq_nonneg _
  have key : m₀ / 4 * mass ≤ (mass - ∑ j, tailBound c (χ j) (g j) b)
      - (mass + tailBound c (χ i) (g i) b) * (1 - m₀ / 2) := by
    nlinarith [hsumT, h2, h3, hτ']
  have := mul_le_mul_of_nonneg_left key ha
  nlinarith [this]

end Cvs.L2a.SpanTailFloorPositive
