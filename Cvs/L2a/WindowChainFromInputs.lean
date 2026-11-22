import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailBilinearBound
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PolarParameterBessel
import Cvs.L2a.PrimeTailLimitProfiles
import Cvs.L2a.TailLogScaleTest
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
# SPINE-L2a(5)'s window chain from its four inputs, at any `λ_min`

E2 at a floor `κ_F P_∞ ≤ N_∞`, E3 with `λᵢ ≥ λ_min` off the ground (`ε ≤ 2/√(κ_Fλ_min)`), the polar identity of
Cvs.L2a.PrimeTailLimitProfiles and a full-tail bound `b̄N_∞ ≤ W_∞` give `QW(k_G) ≥ b′N_∞`, `b′ = b̄ − K_pol(λ_min, κ_F)`; `AngularBesselInequality`'s masses, ORD
and `EImageWindowPoisson`'s window norm then give `WindowFormDeepSpan`'s window form. `K_pol(λ, κ) = 2w̄₁(κ)ε̄(λ, κ) + W̄_Ψε̄(λ, κ)²`.
-/

noncomputable section

open Real Set Filter MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FullTailConvergence

namespace Cvs.L2a.WindowChainFromInputs

open Cvs.L2a.WindowFormDeepSpan (w1Bar WPsiBar Hx)

/-! ### The polar constants at `λ_min` -/

/-- `ε̄(λ, κ) = 2/√(κλ)`: E3's bound on the polar parameter under the floor `κ` and `λᵢ ≥ λ` off the ground. -/
def epsBarL (l κ : ℝ) : ℝ := 2 / √(κ * l)

/-- The polar correction `K_pol(λ, κ) = 2w̄₁(κ)ε̄(λ, κ) + W̄_Ψ ε̄(λ, κ)²`. -/
def KpolL (l κ : ℝ) : ℝ := 2 * w1Bar κ * epsBarL l κ + WPsiBar * epsBarL l κ ^ 2

theorem epsBarL_nonneg (l κ : ℝ) : 0 ≤ epsBarL l κ := div_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem epsBarL_anti {l κ κ' : ℝ} (hl : 0 < l) (hκ : 0 < κ) (h : κ ≤ κ') : epsBarL l κ' ≤ epsBarL l κ :=
  div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 (by positivity))
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h hl.le))

theorem KpolL_nonneg (l κ : ℝ) : 0 ≤ KpolL l κ := by
  unfold KpolL
  have := Cvs.L2a.WindowFormDeepSpan.w1Bar_nonneg κ
  have := epsBarL_nonneg l κ
  have := Cvs.L2a.WindowFormDeepSpan.WPsiBar_nonneg
  positivity

/-- `K_pol(λ, ·)` decreases in the floor. -/
theorem KpolL_anti {l κ κ' : ℝ} (hl : 0 < l) (hκ : 0 < κ) (h : κ ≤ κ') : KpolL l κ' ≤ KpolL l κ := by
  have he := epsBarL_anti hl hκ h
  have hw := Cvs.L2a.WindowFormDeepSpan.w1Bar_anti hκ h
  have he0 := epsBarL_nonneg l κ'
  have hw0 := Cvs.L2a.WindowFormDeepSpan.w1Bar_nonneg κ'
  unfold KpolL
  have h1 : w1Bar κ' * epsBarL l κ' ≤ w1Bar κ * epsBarL l κ :=
    mul_le_mul hw he he0 (Cvs.L2a.WindowFormDeepSpan.w1Bar_nonneg κ)
  have h2 : epsBarL l κ' ^ 2 ≤ epsBarL l κ ^ 2 := pow_le_pow_left₀ he0 he 2
  nlinarith [Cvs.L2a.WindowFormDeepSpan.WPsiBar_nonneg]

/-! ### The window bound from the four inputs -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A proved window-energy budget gives the margin bound from the four tail inputs. -/
theorem L2a_window_margin_budget_of (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ} {c κF bb lmin Λ H : ℝ} {χ μ : ι → ℝ}
    (b : ι → ℝ) {P R : ℕ}
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
    (hfloor : κF * ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (h i) ξ) θ ^ 2)
    (hW : bb * ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (h i) ξ) θ ^ 2
      ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, b i * psi c (h i) ξ))
    (hb : 0 ≤ bb - KpolL lmin κF) (hΛ : ∀ i, i ≠ i₀ → (μ i * √(c / (2 * π))) ^ 2 ≤ Λ)
    (hpole : ∑ i, b i * ∫ s in (-1 : ℝ)..1, h i s = 0)
    (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2)
    (hH : 0 < H)
    (hwindow : ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2
      ≤ H / 2 * ∫ s in (-1 : ℝ)..1, (∑ i, b i * h i s) ^ 2) :
    2 * π * (bb - KpolL lmin κF) * κF / (c * H * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2)))
        * (1 - Λ) * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) fun s => ∑ i, b i * h i s)) := by
  set G : ℝ → ℝ := fun s => ∑ i, b i * h i s with hGd
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (h i) ξ with hΦd
  set N := ∫ θ in Ioi 1, fullTail Φ θ ^ 2 with hNd
  set lam0 := (μ i₀ * √(c / (2 * π))) ^ 2 with hlam0
  have hc0 : 0 < c := by linarith
  have hc2π : 2 * π ≤ c := by linarith [Real.pi_lt_four]
  have hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, h i s ≠ 0 := fun i =>
    Cvs.L2a.PolarParameterBessel.exists_ne_zero_of_norm (hnorm i)
  have hcont : ∀ i, ContinuousOn (h i) (uIcc (-1) 1) := fun i s hs =>
    (hg i s hs).continuousAt.continuousWithinAt
  have hcontI : ∀ i, ContinuousOn (h i) (Icc (-1) 1) := fun i => by
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hcont i
  have hN0 : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  -- E2 at the floor
  have hWB := Cvs.L2a.FullTailBilinearBound.polar_bil_le_of_floor b hg hg₁ hg₂c hang hc hχ0 hχc hχi hκF hfloor
  have hA2 := Cvs.L2a.FullTailBilinearBound.A2_le_A2bar hc hJ
  have hWB' : |Cvs.L2a.FullTailPolarisation.WinfBil Φ Cvs.L2a.BetaProfilePoissonTail.Psi| ≤ w1Bar κF * √N := by
    refine hWB.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    unfold w1Bar
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hA2 (Real.sqrt_nonneg _))
  -- E3 at `λ_min`
  have hε := Cvs.L2a.PolarParameterBessel.polar_eps_le_of_floor i₀ b hc0 hg hg₁ hg₂c hang heven hnorm hχi hμ
    hground hidx hlmin hlam hpole hκF hfloor
  have hx : |2 * π / c * G 0| ≤ epsBarL lmin κF * √N := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π / c)]; exact hε
  -- the polar identity
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
  have hcore : (bb - KpolL lmin κF) * N ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
      (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G)) := by
    rw [hQW]
    have := Cvs.L2a.WindowFormDeepSpan.polar_lower hN0 hW hx hWB' Cvs.L2a.WindowFormDeepSpan.abs_Winf_Psi_le
      (epsBarL_nonneg _ _)
    unfold KpolL; exact this
  have hQW0 : 0 ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
      (Cvs.L2a.TailLogScaleTest.logScale (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G)) :=
    (mul_nonneg hb hN0).trans hcore
  -- the masses and the window norm
  set S := ∑ i ∈ Finset.univ.erase i₀, b i ^ 2 with hSd
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hM : ∀ i, ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 = π / c * (1 - (μ i * √(c / (2 * π))) ^ 2) := fun i =>
    Cvs.Prolate.AngularBesselInequality.mass_eq hc0 (hcontI i) (heven i) (hμ i) (hnorm i)
  have hPS : π / c * (1 - Λ) * S ≤ ∑ i, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hSd, Finset.mul_sum]
    have h0 : 0 ≤ b i₀ ^ 2 * ∫ ξ in Ioi 1, psi c (h i₀) ξ ^ 2 :=
      mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
    have hsum : ∑ i ∈ Finset.univ.erase i₀, π / c * (1 - Λ) * b i ^ 2
        ≤ ∑ i ∈ Finset.univ.erase i₀, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 :=
      Finset.sum_le_sum fun i hi => by
        rw [hM i]
        have hl := hΛ i (Finset.ne_of_mem_erase hi)
        have hπc : 0 < π / c := by positivity
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (b i)) hπc.le) (sub_nonneg.2 hl)]
    linarith
  have horth := Cvs.Prolate.AngularBesselInequality.orthonormal_of_angular Finset.univ hg hg₁ hang hχi.injOn
    (fun i _ => hnorm i)
  have hGsq : ∫ s in (-1 : ℝ)..1, G s ^ 2 = ∑ i, b i ^ 2 := by
    have hii : ∀ i j, ContinuousOn (fun s => b i * b j * (h i s * h j s)) (uIcc (-1) 1) := fun i j =>
      continuousOn_const.mul ((hcont i).mul (hcont j))
    calc ∫ s in (-1 : ℝ)..1, G s ^ 2 = ∫ s in (-1 : ℝ)..1, ∑ i, ∑ j, b i * b j * (h i s * h j s) := by
          congr 1; funext s; simp only [hGd, sq, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i, ∑ j, b i * b j * ∫ s in (-1 : ℝ)..1, h i s * h j s := by
          rw [intervalIntegral.integral_finsetSum fun i _ =>
            (continuousOn_finsetSum _ fun j _ => hii i j).intervalIntegrable]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [intervalIntegral.integral_finsetSum fun j _ => (hii i j).intervalIntegrable]
          exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
      _ = ∑ i, b i ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_congr rfl fun j _ => by rw [horth i (Finset.mem_univ i) j (Finset.mem_univ j)]]
          simp [sq]
  -- the ground coefficient
  set I : ι → ℝ := fun i => ∫ s in (-1 : ℝ)..1, h i s with hId
  have hI0 : I i₀ ≠ 0 := by
    have e : I i₀ = μ i₀ * h i₀ 0 := Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (hμ i₀)
    have hμ0 := Cvs.Prolate.SlepianEvenOrdering.mu_pos_of_even_index hc0 (hg i₀) (hg₁ i₀) (hg₂c i₀) (hang i₀)
      (heven i₀) (hg0 i₀) (hμ i₀) (hidx i₀)
    have hh0 := Cvs.Prolate.AngularBesselInequality.half_le_ground_sq (hg i₀) (hg₁ i₀) (hang i₀) (heven i₀) hground
      (hnorm i₀)
    have : h i₀ 0 ≠ 0 := fun h0 => by rw [h0] at hh0; norm_num at hh0
    rw [e]; exact mul_ne_zero hμ0.ne' this
  have hb0 : b i₀ = -∑ i ∈ Finset.univ.erase i₀, b i * (I i / I i₀) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hpole
    have e : ∑ i ∈ Finset.univ.erase i₀, b i * (I i / I i₀)
        = (∑ i ∈ Finset.univ.erase i₀, b i * I i) / I i₀ := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, show ∑ i ∈ Finset.univ.erase i₀, b i * I i = -(b i₀ * I i₀) by simp only [hId]; linarith]
    field_simp
  have halpha := Cvs.Xi.EImageWindowPoisson.sum_alpha_sq_le (Finset.univ.erase i₀) h (fun i _ => hcont i)
    (fun i hi j hj => horth i (Finset.mem_univ i) j (Finset.mem_univ j)) hc0 (hg i₀) (hg₁ i₀) (hang i₀)
    (heven i₀) hground (hnorm i₀) (hμ i₀)
  have hq0 : 0 ≤ 2 * c / (π * lam0) := by positivity
  have hb0sq : b i₀ ^ 2 ≤ 2 * c / (π * lam0) * S := by
    rw [hb0, neg_sq]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right halpha hS0
  have hGS : ∫ s in (-1 : ℝ)..1, G s ^ 2 ≤ (1 + 2 * c / (π * lam0)) * S := by
    have e : ∑ i, b i ^ 2 = b i₀ ^ 2 + S := (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
    rw [hGsq, e]; linarith [hb0sq]
  have hk := hwindow
  set q := 2 * c / (π * lam0) with hqd
  have hk' : ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G θ ^ 2 ≤ H / 2 * ((1 + q) * S) :=
    hk.trans (mul_le_mul_of_nonneg_left hGS (by positivity))
  have hk0 : 0 ≤ ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G θ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hc20 : 0 ≤ 2 * π * (bb - KpolL lmin κF) * κF / (c * H * (1 + q)) :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) hb) hκF.le)
      (mul_nonneg (mul_nonneg hc0.le hH.le) (by linarith))
  rcases le_or_gt Λ 1 with hΛ1 | hΛ1
  · calc 2 * π * (bb - KpolL lmin κF) * κF / (c * H * (1 + q)) * (1 - Λ)
          * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G θ ^ 2
        ≤ 2 * π * (bb - KpolL lmin κF) * κF / (c * H * (1 + q)) * (1 - Λ) * (H / 2 * ((1 + q) * S)) :=
          mul_le_mul_of_nonneg_left hk' (mul_nonneg hc20 (sub_nonneg.2 hΛ1))
      _ = (bb - KpolL lmin κF) * κF * (π / c * (1 - Λ) * S) := by
          have h1q : 1 + q ≠ 0 := by linarith
          field_simp
      _ ≤ (bb - KpolL lmin κF) * κF * ∑ i, b i ^ 2 * ∫ ξ in Ioi 1, psi c (h i) ξ ^ 2 :=
          mul_le_mul_of_nonneg_left hPS (mul_nonneg hb hκF.le)
      _ ≤ (bb - KpolL lmin κF) * N := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hfloor hb
      _ ≤ _ := hcore
  · have : 2 * π * (bb - KpolL lmin κF) * κF / (c * H * (1 + q)) * (1 - Λ)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) G θ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc20 (by linarith)) hk0
    linarith

/-- A proved window-energy budget gives the deep-level floor from the four tail inputs. -/
theorem L2a_window_deep_budget_of (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ} {g g₁ g₂ : ℝ → ℝ} {c χg μg κF bb lmin H : ℝ}
    {χ μ : ι → ℝ} (b : ι → ℝ) {m : ℕ} {P R : ℕ}
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
    (hm : 1 ≤ m) (hcount : ∀ i, i ≠ i₀ →
      m ≤ (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hgd : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hgd₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hgd₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hgang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χg * g s = 0)
    (hgeven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hgnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1)
    (hgμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μg * g s)
    (hgcount : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio χg).ncard = m)
    (hlmin : 0 < lmin) (hlam : ∀ i, i ≠ i₀ → lmin ≤ (μ i * √(c / (2 * π))) ^ 2) (hκF : 0 < κF)
    (hfloor : κF * ∑ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (h i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (h i) ξ) θ ^ 2)
    (hW : bb * ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (h i) ξ) θ ^ 2
      ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, b i * psi c (h i) ξ))
    (hbk : 1 / 16 ≤ (bb - KpolL lmin κF) * κF)
    (hpole : ∑ i, b i * ∫ s in (-1 : ℝ)..1, h i s = 0)
    (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2)
    (hH : 0 < H)
    (hwindow : ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2
      ≤ H / 2 * ∫ s in (-1 : ℝ)..1, (∑ i, b i * h i s) ^ 2) :
    π / (8 * c * H * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2))) * (1 - (μg * √(c / (2 * π))) ^ 2)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) fun s => ∑ i, b i * h i s)) := by
  have hc0 : 0 < c := by linarith
  have hb : 0 ≤ bb - KpolL lmin κF := by
    by_contra hneg
    push Not at hneg
    have : (bb - KpolL lmin κF) * κF < 0 := mul_neg_of_neg_of_pos hneg hκF
    linarith
  have hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, h i s ≠ 0 := fun i =>
    Cvs.L2a.PolarParameterBessel.exists_ne_zero_of_norm (hnorm i)
  have hgg0 := Cvs.L2a.PolarParameterBessel.exists_ne_zero_of_norm hgnorm
  have hΛ : ∀ i, i ≠ i₀ → (μ i * √(c / (2 * π))) ^ 2 ≤ (μg * √(c / (2 * π))) ^ 2 := fun i hi => by
    have hmem := Cvs.Prolate.EdgeCentreSign.mem_evenSpec_of_angular (hg i) (hg₁ i) (hang i) (heven i) (hg0 i)
    have hle := Cvs.L2a.WindowFormDeepSpan.le_of_ncard_le hm hgcount hmem (hcount i hi)
    exact Cvs.Prolate.SlepianEvenOrdering.lam_le_of_chi_le hc0 hgd hgd₁ hgd₂c hgang hgeven hgg0 (hg i) (hg₁ i) (hg₂c i)
      (hang i) (heven i) (hg0 i) hgμ (hμ i) hle
  have hmain := L2a_window_margin_budget_of i₀ b hg hg₁ hg₂c hang hc hχ0 hχc hχi heven hnorm hμ hground hidx hJ
    hlmin hlam hκF hfloor hW hb hΛ hpole hP hR hH hwindow
  -- `λ_m ≤ 1` from the nonnegative mass
  have hgc : ContinuousOn g (Icc (-1) 1) := by
    have : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hgd s hs).continuousAt.continuousWithinAt
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using this
  have hMg := Cvs.Prolate.AngularBesselInequality.mass_eq hc0 hgc hgeven hgμ hgnorm
  have hMg0 : 0 ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hlam1 : 0 ≤ 1 - (μg * √(c / (2 * π))) ^ 2 := by
    rw [hMg] at hMg0
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < π / c)
  have hk0 : 0 ≤ ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hq0 : 0 ≤ 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2) := by positivity
  have hc2 : π / (8 * c * H * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2)))
      ≤ 2 * π * (bb - KpolL lmin κF) * κF / (c * H * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2))) := by
    rw [show π / (8 * c * H * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2)))
        = 2 * π * (1 / 16) / (c * H * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2))) by
      field_simp; ring]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [mul_assoc (2 * π)]
    exact mul_le_mul_of_nonneg_left hbk (by positivity)
  exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hlam1) hk0) hmain

end Cvs.L2a.WindowChainFromInputs
