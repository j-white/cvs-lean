import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailBilinearBound
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.L1CutLevelExponent
import Cvs.L2a.L1SpineDeepSpanUpper
import Cvs.L2a.L1WindowFromFloor
import Cvs.L2a.PolarParameterBessel
import Cvs.L2a.PrimeTailLimitProfiles
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainFromInputs
import Cvs.L2a.WindowFormDeepSpan
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# SPINE-L1 from a `W_∞` bound: the window form from above

Under `L1WindowFromFloor`'s span hypotheses (floor `κ`, `λ_min`), with some `bᵢ ≠ 0` and `W_∞(Σ bᵢψᵢ) ≤ W`,
`QW(k_G) ≤ W + K_pol(λ_min, κ)·N`; and `N > 0`.
-/

namespace Cvs.L2a.L1WindowFromWinf

open Real Set MeasureTheory
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.FullTailConvergence (fullTail BG)
open Cvs.L2a.L1WindowFromFloor (tailN endV)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The tail norm is positive**: under a floor `κ > 0` on an even-index span with some `bᵢ ≠ 0`, `N > 0`. -/
theorem tailN_pos {h h₁ h₂ : ι → ℝ → ℝ} {c κF : ℝ} {χ μ : ι → ℝ} (b : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (hc : 1 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s) (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hκF : 0 < κF)
    (hfloor : κF * ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2) ≤ tailN c b h)
    (hb : ∃ i, b i ≠ 0) :
    0 < tailN c b h := by
  have hc0 : 0 < c := by linarith
  have hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, h i s ≠ 0 := fun i =>
    Cvs.L2a.PolarParameterBessel.exists_ne_zero_of_norm (hnorm i)
  have hμpos : ∀ i, 0 < μ i := fun i =>
    Cvs.Prolate.SlepianEvenOrdering.mu_pos_of_even_index hc0 (hg i) (hg₁ i) (hg₂c i) (hang i) (heven i) (hg0 i) (hμ i)
      (hidx i)
  have hV : 0 < endV c κF b μ := by
    obtain ⟨i, hi⟩ := hb
    have : 0 < ∑ j, b j ^ 2 * |μ j| ^ 3 :=
      lt_of_lt_of_le (mul_pos (pow_pos (abs_pos.mpr hi) 2 |>.trans_eq (sq_abs _))
        (pow_pos (abs_pos.mpr (hμpos i).ne') 3))
        (Finset.single_le_sum (f := fun j => b j ^ 2 * |μ j| ^ 3)
          (fun j _ => mul_nonneg (sq_nonneg _) (pow_nonneg (abs_nonneg _) 3)) (Finset.mem_univ i))
    unfold endV; positivity
  have hfl : exp (-(3 * π * c / 2)) * endV c κF b μ ≤ tailN c b h :=
    Cvs.L2a.L1CutLevelExponent.tail_ge_endpoint b hg hg₁ hg₂c hang hc hχ0 hχc heven hnorm
      (fun i => (hμpos i).ne') hμ hκF.le hfloor
  exact lt_of_lt_of_le (by positivity) hfl

/-- **SPINE-L1 from a `W_∞` bound**: under `L1WindowFromFloor`'s span hypotheses with `W_∞(Σ bᵢψᵢ) ≤ W`,
`QW(k_G) ≤ W + K_pol(λ_min, κ)·N`. -/
theorem L1_window_of_Winf (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ} {c κF lmin W : ℝ} {χ μ : ι → ℝ} (b : ι → ℝ)
    {P R : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s) (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hground : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i₀)).ncard = 0)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hlmin : 0 < lmin) (hlam : ∀ i, i ≠ i₀ → lmin ≤ (μ i * √(c / (2 * π))) ^ 2) (hκF : 0 < κF)
    (hfloor : κF * ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2) ≤ tailN c b h)
    (hpole : ∑ i, b i * ∫ s in (-1 : ℝ)..1, h i s = 0)
    (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2) (hb : ∃ i, b i ≠ 0)
    (hW : Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, b i * psi c (h i) ξ) ≤ W) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.L2a.TailLogScaleTest.logScale
        (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) fun s => ∑ i, b i * h i s))
      ≤ W + Cvs.L2a.WindowChainFromInputs.KpolL lmin κF * tailN c b h := by
  set G : ℝ → ℝ := fun s => ∑ i, b i * h i s with hGd
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (h i) ξ with hΦd
  set N := tailN c b h with hNd
  have hc0 : 0 < c := by linarith
  have hc2π : 2 * π ≤ c := by linarith [Real.pi_lt_four]
  have hcont : ∀ i, ContinuousOn (h i) (uIcc (-1) 1) := fun i s hs =>
    (hg i s hs).continuousAt.continuousWithinAt
  have hN0 : 0 ≤ N :=
    (tailN_pos b hg hg₁ hg₂c hang (by linarith) hχ0 (fun i => (hχc i).le) heven hnorm hμ hidx hκF hfloor
      hb).le
  -- the polar inputs (as in Cvs.L2a.WindowChainFromInputs)
  have hWB := Cvs.L2a.FullTailBilinearBound.polar_bil_le_of_floor b hg hg₁ hg₂c hang hc hχ0 hχc hχi hκF hfloor
  have hA2 := Cvs.L2a.FullTailBilinearBound.A2_le_A2bar hc hJ
  have hWB' : |Cvs.L2a.FullTailPolarisation.WinfBil Φ Cvs.L2a.BetaProfilePoissonTail.Psi|
      ≤ Cvs.L2a.WindowFormDeepSpan.w1Bar κF * √N := by
    refine hWB.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    unfold Cvs.L2a.WindowFormDeepSpan.w1Bar
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hA2 (Real.sqrt_nonneg _))
  have hε := Cvs.L2a.PolarParameterBessel.polar_eps_le_of_floor i₀ b hc0 hg hg₁ hg₂c hang heven hnorm hχi hμ
    hground hidx hlmin hlam hpole hκF hfloor
  have hx : |2 * π / c * G 0| ≤ Cvs.L2a.WindowChainFromInputs.epsBarL lmin κF * √N := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π / c)]; exact hε
  have hG : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (∑ i, b i * h₁ i s) s :=
    Cvs.L2a.FullTailBilinearChannels.hasDerivAt_span b hg
  have hG₁ := Cvs.L2a.FullTailBilinearChannels.hasDerivAt_span b hg₁
  have hG₂c : ContinuousOn (fun s => ∑ i, b i * h₂ i s) (uIcc (-1) 1) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hg₂c i)
  have hGeven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s := fun s hs =>
    Finset.sum_congr rfl fun i _ => by rw [heven i s hs]
  have hGi : ∫ s in (-1 : ℝ)..1, G s = 0 := by
    show ∫ s in (-1 : ℝ)..1, ∑ i, b i * h i s = 0
    rw [intervalIntegral.integral_finsetSum (f := fun i s => b i * h i s) fun i _ =>
      (ContinuousOn.mul continuousOn_const (hcont i)).intervalIntegrable]
    simp_rw [intervalIntegral.integral_const_mul]; exact hpole
  have hQW := Cvs.L2a.PrimeTailLimitProfiles.window_eq_polar' hc2π hG hG₁ hG₂c hGeven hGi hP hR
  rw [← Cvs.L2a.FullTailBilinearChannels.span_eq_psi b hg] at hQW
  rw [hQW]
  refine (Cvs.L2a.L1SpineDeepSpanUpper.polar_upper hN0 hx hWB' Cvs.L2a.WindowFormDeepSpan.abs_Winf_Psi_le
    (Cvs.L2a.WindowChainFromInputs.epsBarL_nonneg _ _)).trans ?_
  have hK : (2 * Cvs.L2a.WindowFormDeepSpan.w1Bar κF * Cvs.L2a.WindowChainFromInputs.epsBarL lmin κF
      + Cvs.L2a.WindowFormDeepSpan.WPsiBar * Cvs.L2a.WindowChainFromInputs.epsBarL lmin κF ^ 2) * N
      = Cvs.L2a.WindowChainFromInputs.KpolL lmin κF * N := rfl
  rw [hK]
  exact add_le_add hW le_rfl

end Cvs.L2a.L1WindowFromWinf
