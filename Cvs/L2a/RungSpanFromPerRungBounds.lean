import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.ProlateTailCombinationTerminal
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanFromLowMass
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailOfModes
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a on the prolate rung span, given per-rung Mellin and pole bounds

The combination's Mellin and pole integrals are the combinations of the rungs' (Cvs.L2a.ProlateTailCombinationTerminal), and by Cauchy–Schwarz
with the masses as weights `(Σ |a_j| B_j)² ≤ (Σ a_j² m_j)(Σ B_j²/m_j)`; so the low mass and the pole of Cvs.L2a.RungSpanFromLowMass are
`β = Σ_j B_j²/m_j` and `q = 2√(Σ P_j²/m_j)√(Σ P'_j²/m_j)/κ` for per-rung bounds `|∫F_j y_t| ≤ B_j`, `|∫F_j| ≤ P_j`,
`|∫F_j/θ| ≤ P'_j`, `m_j = ∫₁ᵇ ψ_j²`: L2a on the span rests on per-rung facts alone.
-/

namespace Cvs.L2a.RungSpanFromPerRungBounds

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanFromLowMass
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **An `l¹` combination against the masses**: `(Σ |a_i| B_i)² ≤ (Σ a_i² m_i)(Σ B_i²/m_i)` for `m_i > 0`. -/
theorem l1_sq_le (a B m : ι → ℝ) (hm : ∀ i, 0 < m i) :
    (∑ i, |a i| * B i) ^ 2 ≤ (∑ i, a i ^ 2 * m i) * ∑ i, B i ^ 2 / m i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a i| * √(m i)) (fun i => B i / √(m i))
  have e1 : ∀ i, |a i| * √(m i) * (B i / √(m i)) = |a i| * B i := fun i => by
    have := (Real.sqrt_pos.mpr (hm i)).ne'
    field_simp
  have e2 : ∀ i, (|a i| * √(m i)) ^ 2 = a i ^ 2 * m i := fun i => by
    rw [mul_pow, sq_abs, Real.sq_sqrt (hm i).le]
  have e3 : ∀ i, (B i / √(m i)) ^ 2 = B i ^ 2 / m i := fun i => by
    rw [div_pow, Real.sq_sqrt (hm i).le]
  simp only [e1, e2, e3] at h
  exact h

/-- `|Σ a_i x_i| ≤ Σ |a_i| |x_i|`. -/
theorem abs_sum_mul_le (a x : ι → ℝ) : |∑ i, a i * x i| ≤ ∑ i, |a i| * |x i| :=
  (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => abs_mul _ _))

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span, given per-rung Mellin and pole bounds.** -/
theorem L2a_span_of_per_rung {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' : ℝ} {M : ℕ} (N P R Kf : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ) (B Pj Pj' : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hc8 : 8 ≤ c) (hs : 0 < s) (hsmax : max s (5 / (6 * s)) ≤ 1)
    (hh : 0 < h) (hh' : h ≤ 1 / 5)
    (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20) (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 4 ≤ b)
    (hbM : 3 * M / 2 ≤ b)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) b)
    (hD : 0 < D) (hgap : ∀ i j, i ≠ j → D ≤ |χ i - χ j|)
    (hξ₀ : 1 < ξ₀) (hξ₀b : ξ₀ ≤ b) (hw : wbar c ξ₀ < 2) (hden : 0 < massCoeff c b ξ₀)
    (hκ : 0 < (1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b))
    (hx : 0 < x') (hKf : 1 ≤ Kf) (hfl : archSymbol 0 ≤ floorK x' Kf)
    (hBj : ∀ j, ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, tailF (psi c (g j)) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ| ≤ B j
      ∧ |∫ θ in Ioi 1, tailF (psi c (g j)) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ| ≤ B j)
    (hPj : ∀ j, |∫ θ in Ioi 1, tailF (psi c (g j)) M b θ| ≤ Pj j)
    (hPj' : ∀ j, |∫ θ in Ioi 1, tailF (psi c (g j)) M b θ / θ| ≤ Pj' j) :
    (floorK x' Kf
        - (floorK x' Kf - archSymbol 0)
          * (4 * x' * (∑ j, B j ^ 2 / ∫ ξ in (1 : ℝ)..b, psi c (g j) ξ ^ 2)
            / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
              - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
                  + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)))
        - (∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k / √(k : ℝ))
        - 2 * √(∑ j, Pj j ^ 2 / ∫ ξ in (1 : ℝ)..b, psi c (g j) ξ ^ 2)
            * √(∑ j, Pj' j ^ 2 / ∫ ξ in (1 : ℝ)..b, psi c (g j) ξ ^ 2)
            / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
              - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
                  + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)))
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  set m : ι → ℝ := fun j => ∫ ξ in (1 : ℝ)..b, psi c (g j) ξ ^ 2 with hmdef
  set S := ∑ i, a i ^ 2 * m i with hSdef
  set κ := (1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
    - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
        + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b) with hκdef
  set ψs : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hψs
  set F := tailF ψs M b with hFdef
  set Nn := ∫ θ in Ioi 1, F θ ^ 2 with hNn
  set β := ∑ j, B j ^ 2 / m j with hβdef
  set q := 2 * √(∑ j, Pj j ^ 2 / m j) * √(∑ j, Pj' j ^ 2 / m j) / κ with hqdef
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM1 : 1 ≤ M := by omega
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hmode : ∀ (w : ℝ → ℝ), ContinuousOn w (Icc 1 b) → ∀ j ∈ Finset.univ, ∀ n ∈ Finset.Icc 1 M,
      ContinuousOn (fun θ => psi c (g j) (n * θ) * w θ) (Icc 1 b) := fun w hw j _ n _ =>
    ((hcψ j).comp (continuous_const.mul continuous_id)).continuousOn.mul hw
  -- linearity of the tail integrals (Cvs.L2a.ProlateTailCombinationTerminal)
  have hlin : ∀ (w : ℝ → ℝ), ContinuousOn w (Icc 1 b) →
      ∫ θ in Ioi 1, F θ * w θ = ∑ j, a j * ∫ θ in Ioi 1, tailF (psi c (g j)) M b θ * w θ := fun w hw =>
    Cvs.L2a.ProlateTailCombinationTerminal.integral_tailF_sum_mul Finset.univ a (fun j => psi c (g j)) w M hb1 (hmode w hw)
  -- the floor, for the pole
  have hNeq : Nn = ∫ θ in (1 : ℝ)..b, (Gk a χ (fun i => psi c (g i)) 0 θ
      + ∑ n ∈ Finset.Icc 2 M, Gk a χ (fun i => psi c (g i)) 0 (n * θ)) ^ 2 :=
    integral_tailF_sq_eq (χ := χ) hM1 hb1 hcψ
  have hfloor := span_floor_prolate_explicit N g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax
    hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden
  rw [← hNeq] at hfloor
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hMpos i).le
  -- the Mellin bound of the combination
  have hkyc : ∀ t : ℝ, ContinuousOn (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t) (Icc 1 b) := fun t τ hτ =>
    (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_ky (by linarith [hτ.1] : (0 : ℝ) < τ)).continuousAt.continuousWithinAt
  have hkysc : ∀ t : ℝ, ContinuousOn (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t) (Icc 1 b) := fun t τ hτ =>
    (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_kys (by linarith [hτ.1] : (0 : ℝ) < τ)).continuousAt.continuousWithinAt
  set Bs := ∑ j, |a j| * B j with hBs
  have hB : ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ| ≤ Bs
      ∧ |∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ| ≤ Bs := fun t ht => by
    constructor
    · rw [hlin _ (hkyc t)]
      exact (abs_sum_mul_le _ _).trans (Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hBj j t ht).1 (abs_nonneg _))
    · rw [hlin _ (hkysc t)]
      exact (abs_sum_mul_le _ _).trans (Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hBj j t ht).2 (abs_nonneg _))
  have hβ : Bs ^ 2 ≤ β * S := by
    have := l1_sq_le a B m hMpos
    rw [hBs, hβdef, hSdef]; linarith
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hMpos j).le
  -- the pole of the combination
  have hF1 : ∫ θ in Ioi 1, F θ = ∑ j, a j * ∫ θ in Ioi 1, tailF (psi c (g j)) M b θ := by
    have := hlin (fun _ => 1) continuousOn_const
    simpa only [mul_one] using this
  have hFθ : ∫ θ in Ioi 1, F θ / θ = ∑ j, a j * ∫ θ in Ioi 1, tailF (psi c (g j)) M b θ / θ := by
    have hw : ContinuousOn (fun θ : ℝ => 1 / θ) (Icc 1 b) :=
      continuousOn_const.div continuousOn_id fun θ hθ => by linarith [hθ.1]
    have := hlin (fun θ => 1 / θ) hw
    simpa only [mul_one_div] using this
  have hP : |∫ θ in Ioi 1, F θ| ≤ ∑ j, |a j| * Pj j := by
    rw [hF1]
    exact (abs_sum_mul_le _ _).trans (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hPj j) (abs_nonneg _))
  have hP' : |∫ θ in Ioi 1, F θ / θ| ≤ ∑ j, |a j| * Pj' j := by
    rw [hFθ]
    exact (abs_sum_mul_le _ _).trans (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hPj' j) (abs_nonneg _))
  have hPsq : (∑ j, |a j| * Pj j) ^ 2 ≤ S * ∑ j, Pj j ^ 2 / m j := l1_sq_le a Pj m hMpos
  have hPsq' : (∑ j, |a j| * Pj' j) ^ 2 ≤ S * ∑ j, Pj' j ^ 2 / m j := l1_sq_le a Pj' m hMpos
  have hP0 : 0 ≤ ∑ j, |a j| * Pj j := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) ?_
    exact (abs_nonneg _).trans (hPj j)
  have hP0' : 0 ≤ ∑ j, |a j| * Pj' j := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) ?_
    exact (abs_nonneg _).trans (hPj' j)
  have hQ0 : 0 ≤ ∑ j, Pj j ^ 2 / m j := Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hMpos j).le
  have hQ0' : 0 ≤ ∑ j, Pj' j ^ 2 / m j := Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hMpos j).le
  have hPle : ∑ j, |a j| * Pj j ≤ √S * √(∑ j, Pj j ^ 2 / m j) := by
    rw [← Real.sqrt_mul hS0]; exact Real.le_sqrt_of_sq_le hPsq
  have hPle' : ∑ j, |a j| * Pj' j ≤ √S * √(∑ j, Pj' j ^ 2 / m j) := by
    rw [← Real.sqrt_mul hS0]; exact Real.le_sqrt_of_sq_le hPsq'
  have hprod : |∫ θ in Ioi 1, F θ| * |∫ θ in Ioi 1, F θ / θ|
      ≤ S * (√(∑ j, Pj j ^ 2 / m j) * √(∑ j, Pj' j ^ 2 / m j)) := by
    calc |∫ θ in Ioi 1, F θ| * |∫ θ in Ioi 1, F θ / θ| ≤ (∑ j, |a j| * Pj j) * (∑ j, |a j| * Pj' j) :=
          mul_le_mul hP hP' (abs_nonneg _) hP0
      _ ≤ (√S * √(∑ j, Pj j ^ 2 / m j)) * (√S * √(∑ j, Pj' j ^ 2 / m j)) :=
          mul_le_mul hPle hPle' hP0' (by positivity)
      _ = S * (√(∑ j, Pj j ^ 2 / m j) * √(∑ j, Pj' j ^ 2 / m j)) := by
          have : √S * √S = S := Real.mul_self_sqrt hS0
          calc _ = (√S * √S) * (√(∑ j, Pj j ^ 2 / m j) * √(∑ j, Pj' j ^ 2 / m j)) := by ring
            _ = _ := by rw [this]
  have hSN : S ≤ Nn / κ := by rw [le_div_iff₀ hκ]; linarith
  have hpole : -(q * Nn) ≤ 2 * (∫ θ in Ioi 1, F θ) * (∫ θ in Ioi 1, F θ / θ) := by
    have h1 : -(|∫ θ in Ioi 1, F θ| * |∫ θ in Ioi 1, F θ / θ|) ≤ (∫ θ in Ioi 1, F θ) * (∫ θ in Ioi 1, F θ / θ) := by
      rw [← abs_mul]; exact neg_abs_le _
    have hqN : q * Nn = 2 * (√(∑ j, Pj j ^ 2 / m j) * √(∑ j, Pj' j ^ 2 / m j)) * (Nn / κ) := by
      rw [hqdef]; field_simp
    have h2 : S * (√(∑ j, Pj j ^ 2 / m j) * √(∑ j, Pj' j ^ 2 / m j))
        ≤ Nn / κ * (√(∑ j, Pj j ^ 2 / m j) * √(∑ j, Pj' j ^ 2 / m j)) :=
      mul_le_mul_of_nonneg_right hSN (by positivity)
    nlinarith [h1, hprod, h2]
  -- assemble (Cvs.L2a.RungSpanFromLowMass)
  have := L2a_span_of_low_mass (B := Bs) (q := q) (β := β) N P R Kf g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM
    hc₀ hc hc8 hs hsmax hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden hκ
    hx hKf hfl hB hβ hβ0 hpole
  exact this

end Cvs.L2a.RungSpanFromPerRungBounds
