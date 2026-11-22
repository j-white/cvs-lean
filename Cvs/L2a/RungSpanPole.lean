import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungTiltedPole
import Cvs.L2a.SpanPoleMellinFromRungs
import Cvs.L2a.TiltFrameFreePole
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole on the rung span

For `Φ = Σ aᵢψᵢ` with rungs `ψᵢ = psi c gᵢ`, `c ≥ 80`, `5c ≤ c² − χᵢ`, at most `c/4 + 1` rungs and a frame floor
`κF Σ aᵢ²∫₁^X ψᵢ² ≤ ∫F²`, `2(∫F)(∫F/θ) ≥ −49(c/4 + 1)/(2c²κF)·∫F²` with `F = posTail Φ X`: the tilt `∫F(1 − 1/θ)` is
`Σ aᵢ` times `RungTiltedPole`'s rung tilts, bounded by `SpanPoleMellinFromRungs`'s mass Cauchy–Schwarz, and `2AB ≥ −(A − B)²/2` (Cvs.L2a.TiltFrameFreePole).
-/

namespace Cvs.L2a.RungSpanPole

open Real Set MeasureTheory Cvs.L2a.PositionTruncatedTail Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity

/-- **The pole on the span**: for `2 ≤ X`, `80 ≤ c`, `0 ≤ χᵢ`, `5c ≤ c² − χᵢ`, positive rung masses, at most `c/4 + 1`
rungs and the frame floor `κF Σ aᵢ²∫₁^X ψᵢ² ≤ ∫F²`, `−(49(c/4 + 1)/(2c²κF))∫F² ≤ 2(∫F)(∫F/θ)` with `F = posTail Φ X`. -/
theorem pole_span {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    {X κF : ℝ} (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
    (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    -((49 * (c / 4 + 1) / (2 * c ^ 2 * κF))
        * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ)
        * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ / θ) := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦ
  set F := posTail Φ X with hF
  set N := ∫ θ in Ioi 1, F θ ^ 2 with hN
  set m : ι → ℝ := fun i => ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 with hm
  have hc0 : 0 < c := by linarith
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hψo : ∀ i, ContinuousOn (psi c (g i)) (Icc 1 X) := fun i => (hψc i).continuousOn
  have hΦc : ContinuousOn Φ (Icc 1 X) := by
    rw [hΦ]; exact (continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)).continuousOn
  have hw : ContinuousOn (fun θ : ℝ => 1 - 1 / θ) (Icc 1 X) :=
    continuousOn_const.sub (continuousOn_const.div continuousOn_id fun θ hθ =>
      (lt_of_lt_of_le one_pos hθ.1).ne')
  have hinv : ContinuousOn (fun θ : ℝ => θ⁻¹) (Icc 1 X) :=
    continuousOn_inv₀.mono fun θ hθ => (lt_of_lt_of_le one_pos hθ.1).ne'
  have hI1 : IntegrableOn (fun θ => F θ * 1) (Ioi 1) := integrableOn_posTail_mul Φ hΦc continuousOn_const
  have hI2 : IntegrableOn (fun θ => F θ * θ⁻¹) (Ioi 1) := integrableOn_posTail_mul Φ hΦc hinv
  -- the difference `A - B` is the tilt `∫ F (1 - 1/θ)`
  have hdiff : (∫ θ in Ioi 1, F θ) - (∫ θ in Ioi 1, F θ / θ) = ∫ θ in Ioi 1, F θ * (1 - 1 / θ) := by
    have e1 : (∫ θ in Ioi 1, F θ) = ∫ θ in Ioi 1, F θ * 1 := by simp
    have e2 : (∫ θ in Ioi 1, F θ / θ) = ∫ θ in Ioi 1, F θ * θ⁻¹ := by simp [div_eq_mul_inv]
    rw [e1, e2, ← integral_sub hI1 hI2]
    congr 1; funext θ; ring
  -- the tilt splits over the rungs
  set T : ι → ℝ := fun i => ∫ θ in Ioi 1, posTail (psi c (g i)) X θ * (1 - 1 / θ) with hT
  have hsplit : (∫ θ in Ioi 1, F θ * (1 - 1 / θ)) = ∑ i, a i * T i := by
    have hpt : (fun θ => F θ * (1 - 1 / θ))
        = fun θ => ∑ i, a i * (posTail (psi c (g i)) X θ * (1 - 1 / θ)) := by
      funext θ
      rw [hF, hΦ, Cvs.L2a.PositionTailSpanAdapters.posTail_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hpt, integral_finsetSum _ fun i _ =>
      (integrableOn_posTail_mul (psi c (g i)) (hψo i) hw).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  -- each rung tilt is at most `7√mᵢ/c`
  have hTi : ∀ i, |T i| ≤ 7 * √(m i) / c := fun i =>
    Cvs.L2a.RungTiltedPole.tilt_le_rung (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hσ i) hX
  have hcs := Cvs.L2a.SpanPoleMellinFromRungs.abs_sum_le_mass a T (fun i => 7 * √(m i) / c) m hM hTi
  have hms : Cvs.L2a.SpanPoleMellinFromRungs.massSum (fun i => 7 * √(m i) / c) m
      = (Fintype.card ι : ℝ) * (49 / c ^ 2) := by
    unfold Cvs.L2a.SpanPoleMellinFromRungs.massSum
    have hterm : ∀ i, (7 * √(m i) / c) ^ 2 / m i = 49 / c ^ 2 := fun i => by
      have hmi : 0 < m i := hM i
      rw [div_pow, mul_pow, sq_sqrt hmi.le]
      field_simp
      ring
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hms] at hcs
  -- square the bound
  set S := ∑ i, a i ^ 2 * m i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  have hK0 : 0 ≤ (Fintype.card ι : ℝ) * (49 / c ^ 2) := by positivity
  have hsq : (∑ i, a i * T i) ^ 2 ≤ S * ((Fintype.card ι : ℝ) * (49 / c ^ 2)) := by
    have h0 : 0 ≤ √S * √((Fintype.card ι : ℝ) * (49 / c ^ 2)) := by positivity
    calc (∑ i, a i * T i) ^ 2 = |∑ i, a i * T i| ^ 2 := (sq_abs _).symm
      _ ≤ (√S * √((Fintype.card ι : ℝ) * (49 / c ^ 2))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = S * ((Fintype.card ι : ℝ) * (49 / c ^ 2)) := by
          rw [mul_pow, sq_sqrt hS0, sq_sqrt hK0]
  -- the frame floor and the rung count
  have hSN : S ≤ N / κF := by rw [le_div_iff₀ hκ]; linarith
  have hJ' : (Fintype.card ι : ℝ) * (49 / c ^ 2) ≤ (c / 4 + 1) * (49 / c ^ 2) :=
    mul_le_mul_of_nonneg_right hJ (by positivity)
  have hbound : (∑ i, a i * T i) ^ 2 ≤ N / κF * ((c / 4 + 1) * (49 / c ^ 2)) := by
    have hN0 : 0 ≤ N / κF := hS0.trans hSN
    calc (∑ i, a i * T i) ^ 2 ≤ S * ((Fintype.card ι : ℝ) * (49 / c ^ 2)) := hsq
      _ ≤ N / κF * ((c / 4 + 1) * (49 / c ^ 2)) := mul_le_mul hSN hJ' hK0 hN0
  have hkey := Cvs.L2a.TiltFrameFreePole.neg_sq_sub_le (∫ θ in Ioi 1, F θ) (∫ θ in Ioi 1, F θ / θ)
  rw [hdiff, hsplit] at hkey
  have heq : 49 * (c / 4 + 1) / (2 * c ^ 2 * κF) * N = N / κF * ((c / 4 + 1) * (49 / c ^ 2)) / 2 := by
    field_simp
  rw [heq]
  linarith

end Cvs.L2a.RungSpanPole
