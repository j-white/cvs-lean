import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ExplicitTreeBoundPlateau
import Cvs.L2a.ExplicitTreeBoundRamp
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailFloorFromPairNodes
import Cvs.Prolate.Gram.RungGramFloorAtInfinity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The span tail Gram floor for every large `c`

With `χ̄ = c²/2`, `χ_max = c²`, spread `c²/2`, `μ_i = c μ̂_i`, `h ≤ 1/5`: the coefficient of `N₀` in the span floor
(Cvs.L2a.SpanTailFloorProlateRungs) is at most `1 − m₀/2`, `m₀ = 1 − max(s, 5/(6s)) − Λ`, as soon as `Λ < 1 − max(s, 5/(6s))` and
`c ≥ 2K/m₀` (Cvs.L2a.SpanFloorPairSums), `K` with the majorant `A` at the scale `c₀ ≤ c`; so for every `c` beyond an explicit threshold the
tail square is at least the rung masses less their tails, less `(1 − m₀/2) N₀`.
-/

namespace Cvs.L2a.SpanTailFloorLargeC

open Real Finset Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.TailFloorFromPairNodes Cvs.L2a.ExplicitTreeBoundPlateau Cvs.L2a.ExplicitTreeBoundRamp Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The rung sum `Q_ψ = Σ_i K_ψ,i²/mass_i`. -/
noncomputable def Qpsi (c : ℝ) (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ i, Kpsi c (g i) (g₁ i) (g₂ i) ^ 2 / massB c (χ i) (g i) b
/-- The rung sum `Q_u = Σ_i K_u,i²/mass_i`. -/
noncomputable def Qu (c : ℝ) (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ i, Ku c (g i) (g₁ i) (g₂ i) ^ 2 / massB c (χ i) (g i) b

/-- The margin of the span floor: `1 − max(s, 5/(6s)) − Λ`. -/
noncomputable def margin (s b q₁ q₂ : ℝ) (M N : ℕ) : ℝ := 1 - max s (5 / (6 * s)) - Λpair s 1 b q₁ q₂ M N

set_option maxHeartbeats 800000 in
/-- **The span tail Gram floor for every large `c`.** -/
theorem span_floor_large_c {c c₀ h h₂ hη b s ε δ μ₁ μ₂ : ℝ} {M : ℕ} (N : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hs : 0 < s) (hh : 0 < h) (hh' : h ≤ 1 / 5) (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20)
    (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 2 ≤ b)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) b)
    (hm₀ : 0 < margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N)
    (hK : 2 * Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N
      / margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N ≤ c) :
    (∑ i, a i ^ 2 * ((∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) - ∑ j, tailBound c (χ j) (g j) b))
        - (∑ i, a i ^ 2 * massB c (χ i) (g i) b)
          * (1 - margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N / 2)
      ≤ ∫ θ in (1 : ℝ)..b, (Gk a χ (fun i => psi c (g i)) 0 θ
          + ∑ m ∈ Finset.Icc 2 M, Gk a χ (fun i => psi c (g i)) 0 (m * θ)) ^ 2 := by
  have hc1 : 1 ≤ c := hc₀.trans hc
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hα : (3 / 4 : ℝ) ≤ 19 / 20 - h := by linarith
  have hχb : c ^ 2 * (1 / 2) < c ^ 2 * (19 / 20 - h) ^ 2 := by
    apply mul_lt_mul_of_pos_left _ hc2
    nlinarith
  have hS : ∀ i, |χ i - c ^ 2 * (1 / 2)| ≤ c ^ 2 * (1 / 2) := fun i => by
    rw [abs_le]; constructor <;> linarith [hχ0 i, hχc i]
  have hfloor := span_floor_prolate (χb := c ^ 2 * (1 / 2)) (χm := c ^ 2 * 1) (Sp := c ^ 2 * (1 / 2))
    (μ₁ := c * μ₁) (μ₂ := c * μ₂) (s := s) N g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc1 hs hh (by linarith) hh₂
    hh₂' hη0 hη' hb hχb (by positivity) (fun i => by linarith [hχc i]) (by positivity) hS hε hε2 hδ (by positivity)
    (by positivity) hMpos hN₀
  -- the pair sums
  have hq : ∀ m : ℝ, 1 ≤ m → 0 ≤ m ^ 2 - (1 / 2) / (19 / 20 - h) ^ 2 := fun m hm => by
    have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm
    have hα2 : (9 / 16 : ℝ) ≤ (19 / 20 - h) ^ 2 := by nlinarith
    have : (1 / 2 : ℝ) / (19 / 20 - h) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  have hq' : ∀ m : ℝ, 1 ≤ m → 0 ≤ m ^ 2 - (1 / 2) / (4 / 3 - h) ^ 2 := fun m hm => by
    have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm
    have hα2 : (1 : ℝ) ≤ (4 / 3 - h) ^ 2 := by nlinarith
    have : (1 / 2 : ℝ) / (4 / 3 - h) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  have hpair := pair_sums_le (c := c) (s := s) (χh := 1 / 2) (χm := 1) (Sh := 1 / 2) (h := h) (h₂ := h₂) (hη := hη)
    (b := b) (ε := ε) (δ := δ) (μ₁ := μ₁) (μ₂ := μ₂) (M := M) (N := N) (Qψ := Qpsi c g g₁ g₂ χ b)
    (Qu := Qu c g g₁ g₂ χ b) (q₁ := Qpsi c g g₁ g₂ χ b / c) (q₂ := Qu c g g₁ g₂ χ b / c ^ 3) (by linarith) hc hs zero_le_one hε hε2
    hδ hμ₁ hμ₂ hq hq'
    (by field_simp) (by field_simp)
  set m₀ := margin s b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N with hm₀def
  set K := Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N with hKdef
  set Λ := Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N with hΛdef
  have hKc : K / c ≤ m₀ / 2 := by
    rw [div_le_iff₀ hc0]
    have := (div_le_iff₀ hm₀).mp hK
    linarith
  have hbr : max s (5 / (6 * s))
      + 1 / s * ∑ m ∈ Icc 2 M, ∑ m' ∈ Icc 2 M,
          (if m = m' then 0
            else Tsym (fun m m' => Tm c m m' (c ^ 2 * (1 / 2)) (c ^ 2 * 1) (c ^ 2 * (1 / 2)) h h₂ ε δ (c * μ₁) (c * μ₂) N)
              m m')
      + 2 * ∑ m ∈ Icc 2 M, Tf c m (c ^ 2 * (1 / 2)) (c ^ 2 * 1) (c ^ 2 * (1 / 2)) h hη b ε δ (c * μ₁) (c * μ₂)
          (Qpsi c g g₁ g₂ χ b) (Qu c g g₁ g₂ χ b) N
      ≤ 1 - m₀ / 2 := by
    have e : m₀ = 1 - max s (5 / (6 * s)) - Λ := rfl
    linarith [hpair]
  unfold Qpsi Qu at hbr
  have hN₀' := mul_le_mul_of_nonneg_left hbr hN₀.le
  linarith [hfloor, hN₀']

end Cvs.L2a.SpanTailFloorLargeC
