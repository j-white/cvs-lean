import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailBilinearBound
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.L1CutLevelExponent
import Cvs.L2a.L1FullTailWinfBound
import Cvs.L2a.L1SpineDeepSpanUpper
import Cvs.L2a.PolarParameterBessel
import Cvs.L2a.PrimeTailLimitProfiles
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainFromInputs
import Cvs.L2a.WindowFormDeepSpan
import Cvs.Prolate.AngularBesselInequality
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
# SPINE-L1 from a floor: the window form from above at any `λ_min`

As Cvs.L2a.WindowChainFromInputs for L2a: with a floor `κP ≤ N`, `λ_min ≤ λᵢ` off the ground and `PrimeTailLimitProfiles`'s polar identity,
`QW(k_G) ≤ L1bound·N`, `L1bound = L1sym c κ J ℓ_K ℓ_Θ + K_pol(λ_min, κ)` at `L1CutLevelExponent`'s symbolic levels
`ℓ_K = 3πc + 2 log(D/V)`, `ℓ_Θ = 3πc/2 + log max(1, B_G²/V)`, `V = κΣbᵢ²|μᵢ|³/(64c)`.
-/

namespace Cvs.L2a.L1WindowFromFloor

open Real Set MeasureTheory
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.FullTailConvergence (fullTail BG)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The tail norm `N = ∫₁^∞ fullTail(Σ bᵢψᵢ)²`. -/
noncomputable def tailN (c : ℝ) (b : ι → ℝ) (h : ι → ℝ → ℝ) : ℝ :=
  ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (h i) ξ) θ ^ 2

/-- The endpoint floor scale `V = κ Σ bᵢ²|μᵢ|³/(64c)`. -/
noncomputable def endV (c κ : ℝ) (b μ : ι → ℝ) : ℝ := κ * (∑ i, b i ^ 2 * |μ i| ^ 3) / (64 * c)

/-- The level datum `D` of Cvs.L2a.L1FullTailWinfBound. -/
noncomputable def levD (c : ℝ) (b : ι → ℝ) (h h₁ h₂ : ι → ℝ → ℝ) : ℝ :=
  2 * Cvs.L2a.L1FullTailWinfBound.alphaS c b h ^ 2 / (2 * c)
    + 2 * (50 * Cvs.L2a.L1FullTailWinfBound.betaS c b h ^ 2 / (2 * c) + Cvs.L2a.L1FullTailWinfBound.K1bS c b h h₁ h₂)
    + Cvs.L2a.L1FullTailWinfBound.K1bS c b h h₁ h₂ + tailN c b h

/-- The position datum `B_G` of Cvs.L2a.L1FullTailWinfBound. -/
noncomputable def posB (c : ℝ) (b : ι → ℝ) (h h₁ h₂ : ι → ℝ → ℝ) : ℝ :=
  BG c ((fun t => ∑ i, b i * h i t) 1 + (fun t => ∑ i, b i * h i t) (-1))
    (|(fun t => ∑ i, b i * h₁ i t) 1 - (fun t => ∑ i, b i * h₁ i t) (-1)|
      + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, b i * h₂ i t) s|)

/-- **The `L1` constant**: `L1sym` at the symbolic levels plus `K_pol(λ_min, κ)`. -/
noncomputable def L1bound (c κ lmin : ℝ) (b μ : ι → ℝ) (h h₁ h₂ : ι → ℝ → ℝ) : ℝ :=
  Cvs.L2a.L1CutLevelExponent.L1sym c κ (Fintype.card ι)
      (3 * π * c + 2 * Real.log (levD c b h h₁ h₂ / endV c κ b μ))
      (3 * π * c / 2 + Real.log (max 1 (posB c b h h₁ h₂ ^ 2 / endV c κ b μ)))
    + Cvs.L2a.WindowChainFromInputs.KpolL lmin κ

/-- **SPINE-L1 from a floor**: under `WindowChainFromInputs`'s span hypotheses (floor `κ`, `λ_min`), with some `bᵢ ≠ 0`,
`QW(k_G) ≤ L1bound·N`. -/
theorem L1_window_of (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ} {c κF lmin : ℝ} {χ μ : ι → ℝ} (b : ι → ℝ) {P R : ℕ}
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
    (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2) (hb : ∃ i, b i ≠ 0) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.L2a.TailLogScaleTest.logScale
        (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) fun s => ∑ i, b i * h i s))
      ≤ L1bound c κF lmin b μ h h₁ h₂ * tailN c b h := by
  set G : ℝ → ℝ := fun s => ∑ i, b i * h i s with hGd
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (h i) ξ with hΦd
  set N := tailN c b h with hNd
  set J : ℝ := (Fintype.card ι : ℝ) with hJd
  have hc0 : 0 < c := by linarith
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hc2π : 2 * π ≤ c := by linarith [Real.pi_lt_four]
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  have hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, h i s ≠ 0 := fun i =>
    Cvs.L2a.PolarParameterBessel.exists_ne_zero_of_norm (hnorm i)
  have hcont : ∀ i, ContinuousOn (h i) (uIcc (-1) 1) := fun i s hs =>
    (hg i s hs).continuousAt.continuousWithinAt
  -- every `μᵢ > 0`
  have hμpos : ∀ i, 0 < μ i := fun i =>
    Cvs.Prolate.SlepianEvenOrdering.mu_pos_of_even_index hc0 (hg i) (hg₁ i) (hg₂c i) (hang i) (heven i) (hg0 i) (hμ i)
      (hidx i)
  -- the tail norm against the endpoint
  set V := endV c κF b μ with hVd
  have hV : 0 < V := by
    obtain ⟨i, hi⟩ := hb
    have : 0 < ∑ j, b j ^ 2 * |μ j| ^ 3 :=
      lt_of_lt_of_le (mul_pos (pow_pos (abs_pos.mpr hi) 2 |>.trans_eq (sq_abs _))
        (pow_pos (abs_pos.mpr (hμpos i).ne') 3))
        (Finset.single_le_sum (f := fun j => b j ^ 2 * |μ j| ^ 3)
          (fun j _ => mul_nonneg (sq_nonneg _) (pow_nonneg (abs_nonneg _) 3)) (Finset.mem_univ i))
    rw [hVd]; unfold endV; positivity
  have hfl : exp (-(3 * π * c / 2)) * V ≤ N :=
    Cvs.L2a.L1CutLevelExponent.tail_ge_endpoint b hg hg₁ hg₂c hang hc1 hχ0 (fun i => (hχc i).le) heven hnorm
      (fun i => (hμpos i).ne') hμ hκF.le hfloor
  have hN : 0 < N := lt_of_lt_of_le (by positivity) hfl
  have hN0 : 0 ≤ N := hN.le
  -- `W_∞ ≤ L1const·N` (Cvs.L2a.L1FullTailWinfBound)
  have hW := Cvs.L2a.L1FullTailWinfBound.L1_Winf b hg hg₁ hg₂c hang hc hχ0 hχc hχi
    (fun i X hX => Cvs.Prolate.AngularBesselInequality.hM_of_angular hg hg₁ hg₂c hang heven hg0 hc0 hχ0 (by linarith) i)
    hκF hN hfloor
  -- the two levels
  have hKb0 : 0 ≤ Cvs.L2a.L1FullTailWinfBound.K1bS c b h h₁ h₂ := by
    unfold Cvs.L2a.L1FullTailWinfBound.K1bS Cvs.L2a.FullTailConvergence.K1b; unfold BG; positivity
  have hND : N ≤ levD c b h h₁ h₂ := by
    have := Cvs.L2a.L1FullTailWinfBound.betaS_nonneg c b h
    have : 0 ≤ 2 * Cvs.L2a.L1FullTailWinfBound.alphaS c b h ^ 2 / (2 * c) := by positivity
    have : 0 ≤ 50 * Cvs.L2a.L1FullTailWinfBound.betaS c b h ^ 2 / (2 * c) := by positivity
    unfold levD; rw [← hNd]; linarith
  have hlK := Cvs.L2a.L1CutLevelExponent.log_cutK_le hN hV hND hfl
  have hlΘ := Cvs.L2a.L1CutLevelExponent.log_cutΘ_le (B := posB c b h h₁ h₂) hN hV (by positivity) hfl
  have hL := Cvs.L2a.L1CutLevelExponent.L1const_le (c := c)
    (ℓK := 3 * π * c + 2 * Real.log (levD c b h h₁ h₂ / V)) hκF hJ0 (le_max_left _ _)
    (le_trans hlK (le_of_eq (by ring))) hlΘ
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
  unfold L1bound
  rw [add_mul]
  exact add_le_add (hW.trans (mul_le_mul_of_nonneg_right hL hN0)) le_rfl

end Cvs.L2a.L1WindowFromFloor
