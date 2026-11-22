import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarPartDirichletSplit
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanLowMass
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.EdgeGreenIdentity
import Cvs.Prolate.Mellin.EdgeGreenMismatch
import Cvs.Prolate.Mellin.EdgeRemainderClosedForm
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.OrbitGapGreenIdentity
import Cvs.Prolate.ProlateWindowMassIdentity
import Cvs.Prolate.RungExactOrthogonality
import Cvs.WeilForm.OddPoleTermBound
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band edge low mass in Bessel form

Summing `EdgeGreenMismatch`'s mismatch identity over band rungs at `χ_i` against one multiplier at `χ_r`, the boundary terms take
`EdgeGreenIdentity`'s `ω₂/c` per rung and the two bulk terms are bounded by orthogonality on `(1, ∞)` (Cvs.Prolate.RungExactOrthogonality). The far fraction
`∫₁^∞ ψ² ≤ C_M(c, X)∫₁^X ψ²` turns the bulk mass into window mass, giving `specMass` of the band tail.
-/

namespace Cvs.L2a.BandEdgeLowMass

open scoped FourierTransform
open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Mellin.MellinKernelSturmLiouville Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.Mellin.OrbitGapGreenIdentity Cvs.Prolate.Mellin.EdgeGreenIdentity Cvs.Prolate.Mellin.EdgeGreenMismatch

/-- Cauchy–Schwarz on `[1, 2]` against a complex weight: `‖∫₁² (f:ℂ)ρ‖ ≤ √(∫₁² f²)·√(∫₁²‖ρ‖²)`. -/
theorem norm_integral_ofReal_mul_le {f : ℝ → ℝ} {ρ : ℝ → ℂ} (hf : ContinuousOn f (Icc 1 2))
    (hρ : ContinuousOn ρ (Icc 1 2)) :
    ‖∫ ξ in (1 : ℝ)..2, (f ξ : ℂ) * ρ ξ‖ ≤ √(∫ ξ in (1 : ℝ)..2, f ξ ^ 2) * √(∫ ξ in (1 : ℝ)..2, ‖ρ ξ‖ ^ 2) := by
  have hfa : ContinuousOn (fun ξ => |f ξ|) (Icc 1 2) := hf.abs
  have hρn : ContinuousOn (fun ξ => ‖ρ ξ‖) (Icc 1 2) := hρ.norm
  have hnorm : ‖∫ ξ in (1 : ℝ)..2, (f ξ : ℂ) * ρ ξ‖ ≤ ∫ ξ in (1 : ℝ)..2, |f ξ| * ‖ρ ξ‖ := by
    refine (norm_integral_le_integral_norm (by norm_num)).trans_eq ?_
    congr 1; funext ξ; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcs := Cvs.WeilForm.OddPoleTermBound.sq_integral_mul_le (a := 1) (b := 2) (by norm_num)
    (f := fun ξ => |f ξ|) (w := fun ξ => ‖ρ ξ‖)
    ((hfa.pow 2).intervalIntegrable_of_Icc (by norm_num))
    ((hρn.pow 2).intervalIntegrable_of_Icc (by norm_num))
    ((hfa.mul hρn).intervalIntegrable_of_Icc (by norm_num))
  simp only [sq_abs] at hcs
  have hf0 : 0 ≤ ∫ ξ in (1 : ℝ)..2, f ξ ^ 2 := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
  refine hnorm.trans ((le_abs_self _).trans ?_)
  rw [← Real.sqrt_mul hf0]
  exact Real.abs_le_sqrt hcs

/-- `∫₁² Φ² ≤ ∫_{(1,∞)} Φ²` when `Φ²` is integrable on `(1, ∞)`. -/
theorem integral_one_two_sq_le {Φ : ℝ → ℝ} (h : MeasureTheory.IntegrableOn (fun ξ => Φ ξ ^ 2) (Ioi 1)) :
    ∫ ξ in (1 : ℝ)..2, Φ ξ ^ 2 ≤ ∫ ξ in Ioi 1, Φ ξ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  exact MeasureTheory.setIntegral_mono_set h
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun _ _ => sq_nonneg _)
    (Filter.EventuallySubset.of_subset Ioc_subset_Ioi_self)

variable {ι : Type} [Fintype ι]

/-- The square of a rung combination is integrable on `(1, ∞)` (Cvs.Prolate.RungExactOrthogonality). -/
theorem integrableOn_span_sq {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (b : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0) (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun ξ => (∑ i, b i * psi c (g i) ξ) ^ 2) (Ioi 1) := by
  have e : (fun ξ => (∑ i, b i * psi c (g i) ξ) ^ 2)
      = fun ξ => ∑ i, ∑ j, b i * b j * (psi c (g i) ξ * psi c (g j) ξ) := by
    funext ξ; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact MeasureTheory.integrable_finsetSum _ fun i _ => MeasureTheory.integrable_finsetSum _ fun j _ =>
    (Cvs.Prolate.RungExactOrthogonality.integrableOn_psi_mul (hg i) (hg₁ i) (hg₂c i) (hang i) (hg j) (hg₁ j) (hg₂c j)
      (hang j) hc).const_mul _

/-- **The band edge in Bessel form**: for rungs at `χ_i ∈ [0, c²)` and the multiplier at `χ_r < c²` with
`|χ_r − χ_i| ≤ Δ`, `‖Σ aᵢ I_i(1, 2; t)‖ ≤ √P·√J ω₂/c + √(Σ aᵢ²Mᵢ)(√∫₁²|ρ_t|² + Δ‖h_t‖)`, with
`P = Σ aᵢ²∫₁^X ψᵢ²`, `Mᵢ = ∫₁^∞ ψᵢ²` and `‖h_t‖² ≤ 1/(2(c² − w)(c² − χ_r))`. -/
theorem norm_sum_mellinI_band_le (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {c χr r t Δ X : ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχr : χr < c ^ 2) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (hχinj : Function.Injective χ) (hX : 2 ≤ X) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
    (hr : r < 1) (hw : t ^ 2 + 1 / 4 ≤ r * c ^ 2) (hΔ0 : 0 ≤ Δ) (hΔ : ∀ i, |χr - χ i| ≤ Δ) :
    ‖∑ i, (a i : ℂ) * Cvs.L2a.FarPartDirichletSplit.mellinI (psi c (g i)) 1 2 t‖
      ≤ √(∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
          * (√(Fintype.card ι : ℝ) * √(omega2Sq c r) / c)
        + √(∑ i, a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2)
          * (√(∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χr t ξ‖ ^ 2)
            + Δ * √(1 / (2 * (c ^ 2 - (t ^ 2 + 1 / 4)) * (c ^ 2 - χr)))) := by
  classical
  have hc0 : 0 < c := by linarith
  have hr0 : 0 ≤ r := by
    have : 0 < t ^ 2 + 1 / 4 := by positivity
    by_contra h; push Not at h; nlinarith [sq_nonneg c]
  have hwc : t ^ 2 + 1 / 4 ≤ c ^ 2 := hw.trans (mul_le_of_le_one_left (sq_nonneg c) hr.le)
  have hwc' : t ^ 2 + 1 / 4 < c ^ 2 := by
    rcases eq_or_lt_of_le hr0 with h | h
    · rw [← h] at hw; nlinarith [sq_nonneg t]
    · exact lt_of_le_of_lt hw (by nlinarith [sq_nonneg c, sq_pos_of_pos hc0])
  set w := t ^ 2 + 1 / 4 with hwd
  set m : ι → ℝ := fun i => ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 with hmd
  set M : ι → ℝ := fun i => ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 with hMd
  have hsys := fun i => rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i => (hsys i).2.2.1
  -- the per-rung identity
  set W : ι → ℂ := fun i => greenWC c χr t (psi c (g i)) (rungU c (g i)) 2 with hWd
  have hid : ∀ i, Cvs.L2a.FarPartDirichletSplit.mellinI (psi c (g i)) 1 2 t
      = W i - (∫ ξ in (1 : ℝ)..2, (psi c (g i) ξ : ℂ) * rhoEdge c χr t ξ)
        - ((χr - χ i : ℝ) : ℂ) * ∫ ξ in (1 : ℝ)..2, (psi c (g i) ξ : ℂ) * hEdge c χr t ξ := fun i =>
    mellinI_one_eq_mis (hg i) (hg₁ i) (hg₂c i) (hang i) (by norm_num) hχr hwc
  -- continuity of the weights on `[1, 2]`
  have hpos : ∀ ξ ∈ Icc (1 : ℝ) 2, 0 < ξ := fun ξ hξ => by linarith [hξ.1]
  have hD : ∀ ξ ∈ Icc (1 : ℝ) 2, DM c χr w ξ ≠ 0 := fun ξ hξ => (DM_pos_of_le hχr hwc hξ.1).ne'
  have hDc : ContinuousOn (DM c χr w) (Icc 1 2) := (continuous_DM c χr w).continuousOn
  have cky : ContinuousOn (ky t) (Icc 1 2) := Cvs.L2a.FarPartDirichletSplit.continuousOn_ky t 2
  have ckys : ContinuousOn (kys t) (Icc 1 2) := Cvs.L2a.FarPartDirichletSplit.continuousOn_kys t 2
  have hHc : ContinuousOn (hEdge c χr t) (Icc 1 2) := by
    unfold hEdge
    refine (Complex.continuous_ofReal.comp_continuousOn ((((continuousOn_id.pow 2).div hDc hD)).mul cky)).sub
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
        ((((continuousOn_id.pow 2).div hDc hD)).mul ckys)))
  have hk : ∀ {y v : ℝ → ℝ}, (∀ ξ, 0 < ξ → HasDerivAt y (v ξ / ξ ^ 2) ξ) →
      (∀ ξ, 0 < ξ → HasDerivAt v (-((t ^ 2 + 1 / 4) * y ξ)) ξ) →
      ContinuousOn (fun ξ => (greenRho c χr (t ^ 2 + 1 / 4) y v ξ : ℂ)) (Icc 1 2) :=
    fun hy hv => Complex.continuous_ofReal.comp_continuousOn (continuousOn_greenRho hχr hwc
      (fun ξ hξ => (hy ξ (hpos ξ hξ)).continuousAt.continuousWithinAt)
      (fun ξ hξ => (hv ξ (hpos ξ hξ)).continuousAt.continuousWithinAt))
  have hRc : ContinuousOn (rhoEdge c χr t) (Icc 1 2) := by
    unfold rhoEdge
    exact (hk (fun ξ h => hasDerivAt_ky h) (fun ξ h => hasDerivAt_ku h)).sub
      (continuousOn_const.mul (hk (fun ξ h => hasDerivAt_kys h) (fun ξ h => hasDerivAt_kus h)))
  -- linearity: the band sum of the two bulk integrals is one integral of the combination
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦd
  set Ψ : ℝ → ℝ := fun ξ => ∑ i, (a i * (χr - χ i)) * psi c (g i) ξ with hΨd
  have hΦc : Continuous Φ := continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hΨc : Continuous Ψ := continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have linR : ∑ i, (a i : ℂ) * (∫ ξ in (1 : ℝ)..2, (psi c (g i) ξ : ℂ) * rhoEdge c χr t ξ)
      = ∫ ξ in (1 : ℝ)..2, (Φ ξ : ℂ) * rhoEdge c χr t ξ := by
    rw [intervalIntegral.integral_congr (g := fun ξ => ∑ i, (a i : ℂ) * ((psi c (g i) ξ : ℂ) * rhoEdge c χr t ξ))
      (fun ξ _ => by simp only [hΦd]; push_cast; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring)]
    have hint : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable
        (fun ξ => (a i : ℂ) * ((psi c (g i) ξ : ℂ) * rhoEdge c χr t ξ)) MeasureTheory.volume 1 2 := fun i _ =>
      ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
        (continuousOn_const.mul ((Complex.continuous_ofReal.comp (hψc i)).continuousOn.mul hRc))
    rw [intervalIntegral.integral_finsetSum hint]
    exact Finset.sum_congr rfl fun i _ => (intervalIntegral.integral_const_mul _ _).symm
  have linH : ∑ i, (a i : ℂ) * (((χr - χ i : ℝ) : ℂ) * ∫ ξ in (1 : ℝ)..2, (psi c (g i) ξ : ℂ) * hEdge c χr t ξ)
      = ∫ ξ in (1 : ℝ)..2, (Ψ ξ : ℂ) * hEdge c χr t ξ := by
    rw [intervalIntegral.integral_congr (g := fun ξ => ∑ i, ((a i * (χr - χ i) : ℝ) : ℂ)
        * ((psi c (g i) ξ : ℂ) * hEdge c χr t ξ))
      (fun ξ _ => by simp only [hΨd]; push_cast; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring)]
    have hint : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable
        (fun ξ => ((a i * (χr - χ i) : ℝ) : ℂ) * ((psi c (g i) ξ : ℂ) * hEdge c χr t ξ)) MeasureTheory.volume 1 2 :=
      fun i _ => ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
        (continuousOn_const.mul ((Complex.continuous_ofReal.comp (hψc i)).continuousOn.mul hHc))
    rw [intervalIntegral.integral_finsetSum hint]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul]; push_cast; ring
  have hsum : ∑ i, (a i : ℂ) * Cvs.L2a.FarPartDirichletSplit.mellinI (psi c (g i)) 1 2 t
      = ∑ i, (a i : ℂ) * W i - (∫ ξ in (1 : ℝ)..2, (Φ ξ : ℂ) * rhoEdge c χr t ξ)
        - ∫ ξ in (1 : ℝ)..2, (Ψ ξ : ℂ) * hEdge c χr t ξ := by
    rw [← linR, ← linH, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hid i]; ring
  -- the boundary terms, rung by rung: `‖W_i‖ ≤ √mᵢ ω₂/c`
  have hWi : ∀ i, ‖W i‖ ≤ √(m i) * √(omega2Sq c r) / c := fun i => by
    have hE := Cvs.Prolate.ProlateWindowMassIdentity.far_energy_le_rung (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχc i) hX 2
      ⟨by norm_num, hX⟩
    have hWsq := norm_greenWC_two_sq_le_mis (χ' := χ i) (psi c (g i)) (rungU c (g i)) hc0 hχr.le (hχ0 i)
      (hχc i).le (by linarith) hw
    have hm0 : 0 ≤ m i := (hM i).le
    have hω0 : 0 ≤ omega2Sq c r := by unfold omega2Sq; positivity
    have h2 : ‖W i‖ ^ 2 ≤ m i * omega2Sq c r / c ^ 2 := by
      refine hWsq.trans ?_
      calc energy (aP c (χ i)) (psi c (g i)) (rungU c (g i)) 2 * omega2Sq c r / (6 * c ^ 3)
          ≤ 6 * c * m i * omega2Sq c r / (6 * c ^ 3) := by gcongr
        _ = m i * omega2Sq c r / c ^ 2 := by field_simp
    have h := Real.abs_le_sqrt h2
    rw [abs_of_nonneg (norm_nonneg _), Real.sqrt_div (mul_nonneg hm0 hω0), Real.sqrt_mul hm0,
      Real.sqrt_sq hc0.le] at h
    exact h
  have hWsum : ‖∑ i, (a i : ℂ) * W i‖
      ≤ √(∑ i, a i ^ 2 * m i) * (√(Fintype.card ι : ℝ) * √(omega2Sq c r) / c) := by
    have h1 : ‖∑ i, (a i : ℂ) * W i‖ ≤ ∑ i, |a i| * √(m i) * (√(omega2Sq c r) / c) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      refine mul_le_mul_of_nonneg_left ((hWi i).trans_eq ?_) (abs_nonneg _)
      ring
    refine h1.trans ?_
    rw [← Finset.sum_mul]
    have hCS : ∑ i, |a i| * √(m i) ≤ √(∑ i, a i ^ 2 * m i) * √(Fintype.card ι : ℝ) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a i| * √(m i)) (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
      have e : ∑ i, (|a i| * √(m i)) ^ 2 = ∑ i, a i ^ 2 * m i :=
        Finset.sum_congr rfl fun i _ => by rw [mul_pow, sq_abs, Real.sq_sqrt (hM i).le]
      rw [e] at h
      rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le)]
      exact (le_abs_self _).trans (Real.abs_le_sqrt h)
    have hω : 0 ≤ √(omega2Sq c r) / c := by positivity
    calc (∑ i, |a i| * √(m i)) * (√(omega2Sq c r) / c)
        ≤ √(∑ i, a i ^ 2 * m i) * √(Fintype.card ι : ℝ) * (√(omega2Sq c r) / c) :=
          mul_le_mul_of_nonneg_right hCS hω
      _ = _ := by ring
  -- the bulk terms, by orthogonality on `(1, ∞)` (Cvs.Prolate.RungExactOrthogonality)
  have hΦ2 : ∫ ξ in (1 : ℝ)..2, Φ ξ ^ 2 ≤ ∑ i, a i ^ 2 * M i := by
    have h := integral_one_two_sq_le (integrableOn_span_sq a hg hg₁ hg₂c hang hc0)
    rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc0 hχinj] at h
    exact h
  have hΨ2 : ∫ ξ in (1 : ℝ)..2, Ψ ξ ^ 2 ≤ Δ ^ 2 * ∑ i, a i ^ 2 * M i := by
    have h := integral_one_two_sq_le (integrableOn_span_sq (fun i => a i * (χr - χ i)) hg hg₁ hg₂c hang hc0)
    rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq _ hg hg₁ hg₂c hang hc0 hχinj] at h
    refine h.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hM0 : 0 ≤ M i := MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
    have hd : (χr - χ i) ^ 2 ≤ Δ ^ 2 := by
      have := hΔ i
      have h0 : 0 ≤ Δ := (abs_nonneg _).trans this
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    calc (a i * (χr - χ i)) ^ 2 * M i = (χr - χ i) ^ 2 * (a i ^ 2 * M i) := by ring
      _ ≤ Δ ^ 2 * (a i ^ 2 * M i) := mul_le_mul_of_nonneg_right hd (by positivity)
  have hH2 : ∫ ξ in (1 : ℝ)..2, ‖hEdge c χr t ξ‖ ^ 2 ≤ 1 / (2 * (c ^ 2 - w) * (c ^ 2 - χr)) := by
    have e : ∫ ξ in (1 : ℝ)..2, ‖hEdge c χr t ξ‖ ^ 2
        = ∫ ξ in (1 : ℝ)..2, (ξ ^ 2 / DM c χr w ξ) ^ 2 / ξ := by
      refine intervalIntegral.integral_congr fun ξ hξ => ?_
      rw [uIcc_of_le (by norm_num)] at hξ
      exact norm_hEdge_sq c χr t (hpos ξ hξ)
    rw [e]
    exact integral_mult_sq_le hχr (by positivity) hwc'
  have hPM0 : 0 ≤ ∑ i, a i ^ 2 * M i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
      (MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
  have hR : ‖∫ ξ in (1 : ℝ)..2, (Φ ξ : ℂ) * rhoEdge c χr t ξ‖
      ≤ √(∑ i, a i ^ 2 * M i) * √(∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χr t ξ‖ ^ 2) :=
    (norm_integral_ofReal_mul_le hΦc.continuousOn hRc).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hΦ2) (Real.sqrt_nonneg _))
  have hH : ‖∫ ξ in (1 : ℝ)..2, (Ψ ξ : ℂ) * hEdge c χr t ξ‖
      ≤ √(∑ i, a i ^ 2 * M i) * (Δ * √(1 / (2 * (c ^ 2 - w) * (c ^ 2 - χr)))) := by
    refine (norm_integral_ofReal_mul_le hΨc.continuousOn hHc).trans ?_
    calc √(∫ ξ in (1 : ℝ)..2, Ψ ξ ^ 2) * √(∫ ξ in (1 : ℝ)..2, ‖hEdge c χr t ξ‖ ^ 2)
        ≤ √(Δ ^ 2 * ∑ i, a i ^ 2 * M i) * √(1 / (2 * (c ^ 2 - w) * (c ^ 2 - χr))) :=
          mul_le_mul (Real.sqrt_le_sqrt hΨ2) (Real.sqrt_le_sqrt hH2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = √(∑ i, a i ^ 2 * M i) * (Δ * √(1 / (2 * (c ^ 2 - w) * (c ^ 2 - χr)))) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΔ0]; ring
  rw [hsum]
  calc ‖∑ i, (a i : ℂ) * W i - (∫ ξ in (1 : ℝ)..2, (Φ ξ : ℂ) * rhoEdge c χr t ξ)
        - ∫ ξ in (1 : ℝ)..2, (Ψ ξ : ℂ) * hEdge c χr t ξ‖
      ≤ ‖∑ i, (a i : ℂ) * W i‖ + ‖∫ ξ in (1 : ℝ)..2, (Φ ξ : ℂ) * rhoEdge c χr t ξ‖
        + ‖∫ ξ in (1 : ℝ)..2, (Ψ ξ : ℂ) * hEdge c χr t ξ‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by
        have := add_le_add (add_le_add hWsum hR) hH
        refine this.trans_eq ?_
        ring

/-- The far-fraction constant `C_M(c, X) = 1 + 3((1 + W̄/2)/(1 − W̄)) log((X+1)/(X−1))`, `W̄ = 2X/(c(X² − 1))`. -/
noncomputable def CM (c X : ℝ) : ℝ :=
  1 + 3 * ((1 + X / (c * (X ^ 2 - 1))) / (1 - 2 * X / (c * (X ^ 2 - 1)))) * Real.log ((X + 1) / (X - 1))

/-- **The far fraction of a rung**: `∫₁^∞ ψ² ≤ C_M(c, X)∫₁^X ψ²` for `0 ≤ χ < c²`, `c ≥ 80`, `X ≥ 2`
(`ProlateWindowMassIdentity`'s far energy at `X`, `ProlateWindowMassIdentity`'s energy window beyond `X`, `RungGramFloorAtInfinity`'s tail mass). -/
theorem mass_Ioi_le_CM {g g₁ g₂ : ℝ → ℝ} {c χ X : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hX : 2 ≤ X) :
    ∫ ξ in Ioi 1, psi c g ξ ^ 2 ≤ CM c X * ∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2 := by
  obtain ⟨hψ, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hc0 : 0 < c := by linarith
  have hX1 : 1 < X := by linarith
  set m := ∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2 with hmd
  have hm0 : 0 ≤ m := intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
  set Wb := 2 * X / (c * (X ^ 2 - 1)) with hWb
  have hp : 0 < X ^ 2 - 1 := by nlinarith
  have hWb0 : 0 ≤ Wb := by positivity
  have hWb1 : Wb < 1 := by
    rw [hWb, div_lt_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ X), hc]
  have hW : wP c χ X ≤ Wb := Cvs.Prolate.Gram.RungGramFloorAtInfinity.wP_le_far hX1 hc0 hχ0 hχ |>.trans_eq (by unfold pP; ring)
  have hEX := Cvs.Prolate.ProlateWindowMassIdentity.far_energy_le_rung hg hg₁ hg₂c hang hc hχ0 hχ hX X ⟨by linarith, le_rfl⟩
  set F := (1 + Wb / 2) / (1 - Wb) with hF
  have hF0 : 0 ≤ F := div_nonneg (by linarith) (by linarith)
  have hL0 : 0 ≤ Real.log ((X + 1) / (X - 1)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  -- every partial tail beyond `X` is at most `3 F log(...) m`
  have htail : ∀ t, X ≤ t → ∫ ξ in X..t, psi c g ξ ^ 2 ≤ 3 * F * Real.log ((X + 1) / (X - 1)) * m := by
    intro t ht
    have hwin := Cvs.Prolate.ProlateWindowMassIdentity.energy_window (ξ₁ := t) hX1 hc0 hχ0 hχ
      (fun s hs => hψ s (by linarith [hs.1])) (fun s _ => hu s) hW hWb1
    have hG : ∀ ξ ∈ Icc X t, energy (aP c χ) (psi c g) (rungU c g) ξ ≤ 6 * c * m * F := fun ξ hξ =>
      (hwin ξ hξ).2.trans (by rw [hF]; exact mul_le_mul_of_nonneg_right hEX hF0)
    have h := Cvs.Prolate.Gram.RungGramFloorAtInfinity.tail_mass_le hc0 hχ hX1 ht hψc.continuousOn hG
    refine h.trans (le_of_eq ?_)
    field_simp
    ring
  have hint : MeasureTheory.IntegrableOn (fun ξ => psi c g ξ ^ 2) (Ioi 1) := by
    have := Cvs.Prolate.RungExactOrthogonality.integrableOn_psi_mul hg hg₁ hg₂c hang hg hg₁ hg₂c hang hc0
    exact (MeasureTheory.integrableOn_congr_fun (fun ξ _ => by ring) measurableSet_Ioi).mp this
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1 hint Filter.tendsto_id
  refine le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨X, fun t ht => ?_⟩)
  have hcont2 : Continuous (fun x => psi c g x ^ 2) := hψc.pow 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont2.intervalIntegrable 1 X) (hcont2.intervalIntegrable X t)
  simp only [id]
  rw [← hsplit]
  have := htail t ht
  have e : CM c X * m = m + 3 * F * Real.log ((X + 1) / (X - 1)) * m := by
    unfold CM; rw [hF, hWb]; ring
  rw [e]; linarith

/-- `mellinI` is linear in the profile. -/
theorem mellinI_sum (a : ι → ℝ) (ψ : ι → ℝ → ℝ) (hψ : ∀ i, Continuous (ψ i)) (t : ℝ) :
    Cvs.L2a.FarPartDirichletSplit.mellinI (fun ξ => ∑ i, a i * ψ i ξ) 1 2 t
      = ∑ i, (a i : ℂ) * Cvs.L2a.FarPartDirichletSplit.mellinI (ψ i) 1 2 t := by
  have cky := Cvs.L2a.FarPartDirichletSplit.continuousOn_ky t 2
  have ckys := Cvs.L2a.FarPartDirichletSplit.continuousOn_kys t 2
  have i1 : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable (fun ξ => a i * (ψ i ξ * ky t ξ))
      MeasureTheory.volume 1 2 := fun i _ =>
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (continuousOn_const.mul ((hψ i).continuousOn.mul cky))
  have i2 : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable (fun ξ => a i * (ψ i ξ * kys t ξ))
      MeasureTheory.volume 1 2 := fun i _ =>
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (continuousOn_const.mul ((hψ i).continuousOn.mul ckys))
  unfold Cvs.L2a.FarPartDirichletSplit.mellinI
  have e1 : ∫ ξ in (1 : ℝ)..2, (∑ i, a i * ψ i ξ) * ky t ξ = ∑ i, a i * ∫ ξ in (1 : ℝ)..2, ψ i ξ * ky t ξ := by
    rw [intervalIntegral.integral_congr (g := fun ξ => ∑ i, a i * (ψ i ξ * ky t ξ))
      (fun ξ _ => by simp only; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring),
      intervalIntegral.integral_finsetSum i1]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  have e2 : ∫ ξ in (1 : ℝ)..2, (∑ i, a i * ψ i ξ) * kys t ξ = ∑ i, a i * ∫ ξ in (1 : ℝ)..2, ψ i ξ * kys t ξ := by
    rw [intervalIntegral.integral_congr (g := fun ξ => ∑ i, a i * (ψ i ξ * kys t ξ))
      (fun ξ _ => by simp only; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring),
      intervalIntegral.integral_finsetSum i2]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  rw [e1, e2]; push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The band edge low mass (R1)**: for band rungs at `χ_i ∈ [0, c²)`, the multiplier at `χ_r = c² − s_r c`,
`s_r ≥ 5`, `|χ_r − χ_i| ≤ Δ`, `c ≥ 80`, `X ≥ 2`, `r = rLow c K0 < 1`:
`specMass (posTail Φ 2)(c/K0) ≤ (c/K0)/π · P(√J ω₂/c + √C_M(√LE(c, r, s_r) + Δ/√(2(1 − r)c²σ_r²)))²`. -/
theorem specMass_band_edge_le (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {c χr Δ X K0 : ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχr0 : 0 ≤ χr) (hχr : 5 * c ≤ c ^ 2 - χr) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (hχinj : Function.Injective χ) (hX : 2 ≤ X) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
    (hK0 : 0 < K0) (hr : Cvs.L2a.RungSpanLowMass.rLow c K0 < 1) (hΔ0 : 0 ≤ Δ) (hΔ : ∀ i, |χr - χ i| ≤ Δ) :
    Cvs.L2a.SpectralMassLevelLeak.specMass (Cvs.L2a.PositionTruncatedTail.posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) 2) (c / K0)
      ≤ c / K0 / π * ((∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
        * (√(Fintype.card ι : ℝ) * √(omega2Sq c (Cvs.L2a.RungSpanLowMass.rLow c K0)) / c
          + √(CM c X) * (√(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c (Cvs.L2a.RungSpanLowMass.rLow c K0) ((c ^ 2 - χr) / c))
            + Δ * √(1 / (2 * (1 - Cvs.L2a.RungSpanLowMass.rLow c K0) * c ^ 2 * (c ^ 2 - χr))))) ^ 2) := by
  classical
  set r := Cvs.L2a.RungSpanLowMass.rLow c K0 with hrd
  have hc0 : 0 < c := by linarith
  have hr0 : 0 ≤ r := by rw [hrd]; unfold Cvs.L2a.RungSpanLowMass.rLow; positivity
  have hrc := Cvs.L2a.RungSpanLowMass.rLow_mul_sq hc0.ne' hK0.ne'
  have hσr : 0 < c ^ 2 - χr := by nlinarith
  have hχrc : χr < c ^ 2 := by linarith
  set m : ι → ℝ := fun i => ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 with hmd
  set M : ι → ℝ := fun i => ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 with hMd
  set P := ∑ i, a i ^ 2 * m i with hPd
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  have hPM : ∑ i, a i ^ 2 * M i ≤ CM c X * P := by
    rw [hPd, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mass_Ioi_le_CM (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχc i) hX
    calc a i ^ 2 * M i ≤ a i ^ 2 * (CM c X * m i) := mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = CM c X * (a i ^ 2 * m i) := by ring
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hΦc : Continuous (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  set B := √P * (√(Fintype.card ι : ℝ) * √(omega2Sq c r) / c
      + √(CM c X) * (√(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r ((c ^ 2 - χr) / c))
        + Δ * √(1 / (2 * (1 - r) * c ^ 2 * (c ^ 2 - χr))))) with hBd
  have hlev : ∀ t, |t| < c / K0 →
      ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale
        (Cvs.L2a.PositionTruncatedTail.posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) 2))) (t / (2 * π))‖ ^ 2 ≤ B ^ 2 := by
    intro t ht
    have hw : t ^ 2 + 1 / 4 ≤ r * c ^ 2 := by
      rw [hrc]
      have : t ^ 2 ≤ (c / K0) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) ht.le 2
      linarith
    have e1 := Cvs.L2a.TailLogScaleTest.fourier_eq (Cvs.L2a.PositionTruncatedTail.posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) 2)
      (fun θ hθ => Cvs.L2a.PositionTruncatedTail.posTail_zero _ _ hθ) t
      (Cvs.L2a.PositionTruncatedTail.integrableOn_posTail_mul _ hΦc.continuousOn (Cvs.L2a.FarPartDirichletSplit.continuousOn_ky t 2))
      (Cvs.L2a.PositionTruncatedTail.integrableOn_posTail_mul _ hΦc.continuousOn (Cvs.L2a.FarPartDirichletSplit.continuousOn_kys t 2))
    have e2 := Cvs.L2a.FarPartDirichletSplit.mellin_posTail_eq (fun ξ => ∑ i, a i * psi c (g i) ξ) (by norm_num : (1 : ℝ) ≤ 2)
      hΦc.continuousOn t
    have hd1 : Cvs.L2a.FarPartDirichletSplit.dch 1 t = 1 := by simp [Cvs.L2a.FarPartDirichletSplit.dch]
    have hI2 : Cvs.L2a.FarPartDirichletSplit.mellinI (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 2 t = 0 := by
      simp [Cvs.L2a.FarPartDirichletSplit.mellinI]
    have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
    rw [hfl, show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)] at e2
    simp only [Nat.cast_one, Nat.cast_ofNat, hd1, hI2, one_mul, mul_zero, add_zero] at e2
    rw [e1, e2, mellinI_sum a (fun i => psi c (g i)) hψc t]
    have hN := norm_sum_mellinI_band_le a hg hg₁ hg₂c hang hc hχrc hχ0 hχc hχinj hX hM hr hw hΔ0 hΔ
    have hρ := Cvs.Prolate.Mellin.EdgeRemainderClosedForm.integral_norm_rhoEdge_sq_le (t := t) (by linarith) hχr0 hχr hr hw
    have hw' : 1 / (2 * (c ^ 2 - (t ^ 2 + 1 / 4)) * (c ^ 2 - χr)) ≤ 1 / (2 * (1 - r) * c ^ 2 * (c ^ 2 - χr)) := by
      have h1r : 0 < 1 - r := by linarith
      apply one_div_le_one_div_of_le (by positivity)
      have : (1 - r) * c ^ 2 ≤ c ^ 2 - (t ^ 2 + 1 / 4) := by linarith
      have h2 : 0 ≤ c ^ 2 - χr := hσr.le
      nlinarith
    have hbulk : √(∑ i, a i ^ 2 * M i)
          * (√(∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χr t ξ‖ ^ 2) + Δ * √(1 / (2 * (c ^ 2 - (t ^ 2 + 1 / 4)) * (c ^ 2 - χr))))
        ≤ √P * (√(CM c X) * (√(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r ((c ^ 2 - χr) / c))
          + Δ * √(1 / (2 * (1 - r) * c ^ 2 * (c ^ 2 - χr))))) := by
      have h1 : √(∑ i, a i ^ 2 * M i) ≤ √P * √(CM c X) := by
        rw [← Real.sqrt_mul hP0, mul_comm P]; exact Real.sqrt_le_sqrt hPM
      have h2 : √(∫ ξ in (1 : ℝ)..2, ‖rhoEdge c χr t ξ‖ ^ 2) + Δ * √(1 / (2 * (c ^ 2 - (t ^ 2 + 1 / 4)) * (c ^ 2 - χr)))
          ≤ √(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r ((c ^ 2 - χr) / c))
            + Δ * √(1 / (2 * (1 - r) * c ^ 2 * (c ^ 2 - χr))) :=
        add_le_add (Real.sqrt_le_sqrt hρ) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hw') hΔ0)
      calc _ ≤ √P * √(CM c X) * (√(Cvs.Prolate.Mellin.EdgeRemainderClosedForm.lemmaEBound c r ((c ^ 2 - χr) / c))
            + Δ * √(1 / (2 * (1 - r) * c ^ 2 * (c ^ 2 - χr)))) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
    have hB : ‖∑ i, (a i : ℂ) * Cvs.L2a.FarPartDirichletSplit.mellinI (psi c (g i)) 1 2 t‖ ≤ B := by
      refine hN.trans (le_of_le_of_eq (add_le_add le_rfl hbulk) ?_)
      rw [hBd]; ring
    exact pow_le_pow_left₀ (norm_nonneg _) hB 2
  refine (Cvs.L2a.FarPartDirichletSplit.specMass_le_sup_fourier _ (by positivity) hlev).trans (le_of_eq ?_)
  rw [hBd, mul_pow, Real.sq_sqrt hP0]

end Cvs.L2a.BandEdgeLowMass
