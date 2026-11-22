import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorBandCoupling
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullSpanFrameFloor
import Cvs.L2a.FullSpanWiring
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.LocalisedConstants
import Cvs.L2a.MiddlePartQStep
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# THEOREM L2a-FULL: the full-tail L2a on the full span with (I) and (BC) as hypotheses

The strip constant depends on `σ̲` alone: `r_S(c, σ) ≤ rSig(min(σ, 5c))`, `rSig σ = 128(5/σ)^{1/4} + 2000(5/σ)^{3/4} + 500(5/σ)^{7/4} → 0`.
Any certified residual `ρ ≥ resLoc(c, J, M)` enters with the margin `θ + ρ + rSig < 153/1000`. At the index-law target
`σ̲ = 20c/(log(16c/5) + 1)` the strip term is antitone in `c`, so `c₀′` is any `c₁ ≥ 10¹⁶` meeting the margin; `c0Prime m = 25(129/m)⁸`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology

namespace Cvs.L2a.FullSpanConditional

open Cvs.L2a.MiddlePartQStep (rStrip KS₁ KS₂ KS₃ rStrip_eq)

/-! ### The strip constant as a function of `σ̲` alone -/

/-- `K₂(s) = (5/s)^{3/4}K₂(5)` for `s > 0`. -/
theorem KS₂_eq {s : ℝ} (hs : 0 < s) : KS₂ s = (5 / s) ^ (3 / 4 : ℝ) * KS₂ 5 := by
  have h5 : (1 / (5 : ℝ)) ^ (3 / 4 : ℝ) = (5 / (5 : ℝ)) ^ (3 / 4 : ℝ) * (1 / 5) ^ (3 / 4 : ℝ) := by norm_num
  unfold KS₂
  rw [Cvs.L2a.FullSpanFrameFloor.one_div_rpow_eq hs]
  ring

/-- `(5/s)^e·c^{−e} = (5/(sc))^e` for `s, c > 0`. -/
theorem rpow_scale {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (e : ℝ) :
    (5 / s) ^ e * c ^ (-e) = (5 / (s * c)) ^ e := by
  rw [Real.rpow_neg hc.le, ← div_eq_mul_inv, ← Real.div_rpow (by positivity) hc.le]
  congr 1
  field_simp

/-- **The strip constant in `σ̲`**: for `0 < σ ≤ 5c`,
`r_S(c, σ) ≤ K₁(5)(5/σ)^{1/4} + K₂(5)(5/σ)^{3/4} + K₃(5)(5/σ)^{7/4}`, with no `c` on the right. -/
theorem rStrip_le_KS {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσ5 : σ ≤ 5 * c) :
    rStrip c σ ≤ KS₁ 5 * (5 / σ) ^ (1 / 4 : ℝ) + KS₂ 5 * (5 / σ) ^ (3 / 4 : ℝ)
      + KS₃ 5 * (5 / σ) ^ (7 / 4 : ℝ) := by
  set s := σ / c with hsd
  have hs : 0 < s := div_pos hσ hc
  have hs5 : s ≤ 5 := by rw [hsd, div_le_iff₀ hc]; linarith
  have hσs : σ = s * c := by rw [hsd]; field_simp
  obtain ⟨e1, -, e3⟩ := Cvs.L2a.FullSpanFrameFloor.KS_le_scaled hs hs5
  rw [hσs, rStrip_eq hc hs, e1, KS₂_eq hs]
  have p7 : 0 ≤ c ^ (-(7 / 4 : ℝ)) := Real.rpow_nonneg hc.le _
  have t3 := mul_le_mul_of_nonneg_right e3 p7
  have r1 := rpow_scale hs hc (1 / 4)
  have r3 := rpow_scale hs hc (3 / 4)
  have r7 := rpow_scale hs hc (7 / 4)
  calc (5 / s) ^ (1 / 4 : ℝ) * KS₁ 5 * c ^ (-(1 / 4 : ℝ)) + (5 / s) ^ (3 / 4 : ℝ) * KS₂ 5 * c ^ (-(3 / 4 : ℝ))
        + KS₃ s * c ^ (-(7 / 4 : ℝ))
      ≤ KS₁ 5 * ((5 / s) ^ (1 / 4 : ℝ) * c ^ (-(1 / 4 : ℝ)))
        + KS₂ 5 * ((5 / s) ^ (3 / 4 : ℝ) * c ^ (-(3 / 4 : ℝ)))
        + KS₃ 5 * ((5 / s) ^ (7 / 4 : ℝ) * c ^ (-(7 / 4 : ℝ))) := by nlinarith
    _ = _ := by rw [r1, r3, r7]

/-- **The strip bound** `rSig σ = 128(5/σ)^{1/4} + 2000(5/σ)^{3/4} + 500(5/σ)^{7/4}`. -/
def rSig (σ : ℝ) : ℝ :=
  128 * (5 / σ) ^ (1 / 4 : ℝ) + 2000 * (5 / σ) ^ (3 / 4 : ℝ) + 500 * (5 / σ) ^ (7 / 4 : ℝ)

/-- **`r_S(c, σ) ≤ rSig σ`** for `0 < σ ≤ 5c`. -/
theorem rStrip_le_rSig {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσ5 : σ ≤ 5 * c) : rStrip c σ ≤ rSig σ := by
  refine (rStrip_le_KS hc hσ hσ5).trans ?_
  have b1 := Cvs.L2a.LocalisedConstants.KS1_le
  obtain ⟨b2, b3⟩ := Cvs.L2a.LocalisedConstants.KS23_le
  have l1 : 0 ≤ (5 / σ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have l3 : 0 ≤ (5 / σ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have l7 : 0 ≤ (5 / σ) ^ (7 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  unfold rSig
  nlinarith [mul_le_mul_of_nonneg_right b1 l1, mul_le_mul_of_nonneg_right b2 l3,
    mul_le_mul_of_nonneg_right b3 l7]

/-! ### The index-law target `σ̲ = 20c/(log(16c/5) + 1)` -/

/-! ### The strip term at `c = 10¹⁶` -/

/-! ### The threshold `c₀′`: monotonicity and a closed form -/

/-- `rSig` is antitone on `(0, ∞)`. -/
theorem rSig_anti {σ σ' : ℝ} (hσ : 0 < σ) (hσσ : σ ≤ σ') : rSig σ' ≤ rSig σ := by
  have hσ' : 0 < σ' := lt_of_lt_of_le hσ hσσ
  have h5 : 5 / σ' ≤ 5 / σ := div_le_div_of_nonneg_left (by norm_num) hσ hσσ
  have hp : ∀ e : ℝ, 0 ≤ e → (5 / σ') ^ e ≤ (5 / σ) ^ e := fun e he =>
    Real.rpow_le_rpow (by positivity) h5 he
  unfold rSig
  have := hp (1 / 4) (by norm_num)
  have := hp (3 / 4) (by norm_num)
  have := hp (7 / 4) (by norm_num)
  linarith

/-- **`r_S(c, σ) ≤ rSig(min(σ, 5c))`** for every `σ > 0`. -/
theorem rStrip_le_rSig_min {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) : rStrip c σ ≤ rSig (min σ (5 * c)) := by
  have hm : 0 < min σ (5 * c) := lt_min hσ (by linarith)
  exact (Cvs.L2a.FullSpanFrameFloor.rStrip_anti hc hm (min_le_left _ _)).trans
    (rStrip_le_rSig hc hm (min_le_right _ _))

/-- `rSig σ ≤ 129(5/σ)^{1/4}` once `(5/σ)^{1/4} ≤ 1/100`. -/
theorem rSig_le_of_small {σ : ℝ} (hσ : 0 < σ) (hy : (5 / σ) ^ (1 / 4 : ℝ) ≤ 1 / 100) :
    rSig σ ≤ 129 * (5 / σ) ^ (1 / 4 : ℝ) := by
  have ht0 : 0 ≤ 5 / σ := by positivity
  set y := (5 / σ) ^ (1 / 4 : ℝ) with hyd
  have hy0 : 0 ≤ y := Real.rpow_nonneg ht0 _
  have e3 : (5 / σ) ^ (3 / 4 : ℝ) = y ^ 3 := by
    rw [hyd, ← Real.rpow_natCast, ← Real.rpow_mul ht0]; norm_num
  have e7 : (5 / σ) ^ (7 / 4 : ℝ) = y ^ 7 := by
    rw [hyd, ← Real.rpow_natCast, ← Real.rpow_mul ht0]; norm_num
  unfold rSig
  rw [e3, e7, ← hyd]
  have h2 : y ^ 2 ≤ 1 / 10 ^ 4 := by
    calc y ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hy0 hy 2
      _ = 1 / 10 ^ 4 := by norm_num
  have h6 : y ^ 6 ≤ 1 / 10 ^ 4 := by
    have : y ^ 6 = y ^ 2 * (y ^ 2) ^ 2 := by ring
    rw [this]
    have hy2 : y ^ 2 ≤ 1 := h2.trans (by norm_num)
    nlinarith [pow_nonneg hy0 2, pow_le_one₀ (pow_nonneg hy0 2) hy2 (n := 2)]
  have t3 : 2000 * y ^ 3 ≤ y / 5 := by
    have := mul_le_mul_of_nonneg_left h2 hy0
    nlinarith
  have t7 : 500 * y ^ 7 ≤ y / 20 := by
    have := mul_le_mul_of_nonneg_left h6 hy0
    nlinarith
  linarith

/-! ### THEOREM L2a-FULL -/

section main

variable {ι : Type} [Fintype ι]

/-- **THEOREM L2a-FULL, any index floor and any residual**: with (I) `σ ≤ c² − χᵢ`, `ρ ≥ resLoc(c, J, M)` at every
`M ≥ 3`, (BC) on `𝓑` at `θ`, and `θ + ρ + rSig(min(σ, 5c)) < 153/1000`: `κ_full ≥ (√(153/1000 − ρ − rSig − θ + ε²) − ε)²`,
`κ_full > 0`, `b̄_full·N(M) ≤ W(M)` at every integer `M ≥ 3`, and `b̄_full·N_∞ ≤ W_∞`. -/
theorem L2a_fulltail_full_sigma {μ : ι → ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {κ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 16 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i)
    {σ : ℝ} (hσ0 : 0 < σ) (hI : ∀ i, σ ≤ c ^ 2 - χ i)
    (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, Cvs.L2a.AngularProlateTailPositive.psi c (g i) t ^ 2)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorIntegerM.resLoc c (Fintype.card ι) M ≤ ρ)
    {θ : ℝ} (hBC : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorBandCoupling.BandCoupling c g μ a
      (Cvs.L2a.FullSpanFrameFloor.bandSet c χ) Cvs.L2a.FarIntegrationByParts.wF M θ)
    (hm : θ + ρ + rSig (min σ (5 * c)) < 153 / 1000)
    (hκ1 : 1 ≤ κ) (hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c κ) :
    (√(153 / 1000 - ρ - rSig (min σ (5 * c)) - θ + Cvs.L2a.SpanPlungeBound.epsTauFlat 5 ^ 2)
          - Cvs.L2a.SpanPlungeBound.epsTauFlat 5) ^ 2
        ≤ Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ θ
      ∧ 0 < Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ θ
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullSpanWiring.bBarFull c κ (Fintype.card ι)
              (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ θ)
            * (∫ y in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail
                (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail
                (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull c κ (Fintype.card ι)
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ θ)
          * (∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail
              (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hJ0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hS := rStrip_le_rSig_min hc0 hσ0
  have hge := Cvs.L2a.FullSpanFrameFloor.aJAfull_ge (ρ := ρ) (σ₀ := σ) (θ := θ) hc hJ0 hJ
  have hS' : rStrip c σ < 153 / 1000 - ρ - θ := by linarith
  have hA : 0 < Cvs.L2a.FullSpanFrameFloor.aJAfull (10 ^ 16) c (Fintype.card ι) ρ σ θ :=
    lt_of_lt_of_le (by linarith) hge
  obtain ⟨h1, h2, h3⟩ := Cvs.L2a.FullSpanWiring.L2a_fulltail_band a hg hg₁ hg₂c hang hc hχ0 hσ0 hI hχi heven
    hg0 hμ hidx hJ hmass hρ hBC hA hκ1 hT
  exact ⟨Cvs.L2a.FullSpanFrameFloor.kappaFfull_ge (by linarith) (by linarith), h1, h2, h3⟩

end main

end Cvs.L2a.FullSpanConditional
