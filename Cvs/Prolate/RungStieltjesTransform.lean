import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BernsteinRieszSymbolBounds
import Cvs.L2a.FarIntegrationByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-! The z-Stieltjes transform `Fs(y, z) = ∫ g(s) e^{iczs}/(y + s) ds` of an even `g`: its
z-derivative `ic(ψ(z) − y·Fs)`, the derivative `ic e^{icyz}ψ(z)` of `e^{icyz}Fs`, its
Riemann–Lebesgue decay as `z → ∞`, and the reflection `Fs(−y, z) = −conj Fs(y, z)`. -/

noncomputable section
open Real Set Filter Topology MeasureTheory Complex Metric
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts
open scoped Interval

namespace Cvs.Prolate.RungStieltjesTransform

/-- `Fs(y, z) = ∫ g(s) e^{iczs}/(y + s) ds`, the Stieltjes transform `fStil` at frequency `cz`. -/
def fsZ (c : ℝ) (g : ℝ → ℝ) (y z : ℝ) : ℂ := Cvs.L2a.BandRungOutgoingWave.fStil (c * z) g y

/-- Differentiation under the integral in a real parameter, with the derivative bounded on a ball. -/
theorem hasDerivAt_rint_near {G : ℝ → ℂ} {k k' : ℝ → ℝ → ℂ} {z₀ r C : ℝ} (hr : 0 < r)
    (hG : ContinuousOn G (Icc (-1) 1)) (hkc : ∀ z ∈ ball z₀ r, ContinuousOn (k z) (Icc (-1) 1))
    (hk'c : ContinuousOn (k' z₀) (Icc (-1) 1))
    (hd : ∀ z ∈ ball z₀ r, ∀ s ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun z => k z s) (k' z s) z)
    (hb : ∀ z ∈ ball z₀ r, ∀ s ∈ Icc (-1 : ℝ) 1, ‖k' z s‖ ≤ C) :
    HasDerivAt (fun z => ∫ s in (-1 : ℝ)..1, G s * k z s) (∫ s in (-1 : ℝ)..1, G s * k' z₀ s) z₀ := by
  have hu : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hI : ∀ s ∈ Ι (-1 : ℝ) 1, s ∈ Icc (-1 : ℝ) 1 := by
    intro s hs
    rw [uIoc_of_le (by norm_num)] at hs
    exact ⟨hs.1.le, hs.2⟩
  have hint : ∀ f : ℝ → ℂ, ContinuousOn f (Icc (-1) 1) →
      IntervalIntegrable (fun s => G s * f s) volume (-1) 1 := fun f hf => by
    apply ContinuousOn.intervalIntegrable
    rw [hu]; exact hG.mul hf
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -1) (b := 1) (F := fun z s => G s * k z s) (F' := fun z s => G s * k' z s) (x₀ := z₀)
    (bound := fun s => ‖G s‖ * C) (s := ball z₀ r) (ball_mem_nhds z₀ hr)
    (Filter.eventually_of_mem (ball_mem_nhds z₀ hr) fun z hz =>
      ((hint _ (hkc z hz)).def').aestronglyMeasurable)
    (hint _ (hkc z₀ (mem_ball_self hr)))
    ((hint _ hk'c).def').aestronglyMeasurable
    (Filter.Eventually.of_forall fun s hs z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb z hz s (hI s hs)) (norm_nonneg _))
    (by
      apply ContinuousOn.intervalIntegrable
      rw [hu]; exact hG.norm.mul continuousOn_const)
    (Filter.Eventually.of_forall fun s hs z hz => (hd z hz s (hI s hs)).const_mul (G s))
  exact key.2

/-- The phase `e^{iczs}`. -/
def ph (c z s : ℝ) : ℂ := Complex.exp (((c * z * s : ℝ) : ℂ) * I)

/-- `Fs` as an interval integral against the phase `ph`. -/
theorem fsZ_eq (c : ℝ) (g : ℝ → ℝ) (y z : ℝ) :
    fsZ c g y z = ∫ s in (-1 : ℝ)..1, (g s : ℂ) * (ph c z s / ((y + s : ℝ) : ℂ)) := by
  unfold fsZ Cvs.L2a.BandRungOutgoingWave.fStil ph
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [mul_div_assoc]

/-- The z-derivative of the phase `e^{iczs}` is `e^{iczs}·ics`. -/
theorem hasDerivAt_ph (c s z : ℝ) : HasDerivAt (fun z => ph c z s) (ph c z s * (((c * s : ℝ) : ℂ) * I)) z := by
  have h1 : HasDerivAt (fun z : ℝ => c * z * s) (c * s) z := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using ((hasDerivAt_id z).const_mul c).mul_const s
  have := ((h1.ofReal_comp).mul_const I).cexp
  unfold ph
  refine this.congr_deriv ?_
  simp

/-- The phase has modulus one. -/
theorem norm_ph (c z s : ℝ) : ‖ph c z s‖ = 1 := by unfold ph; exact Complex.norm_exp_ofReal_mul_I _

/-- `∂_z Fs(y, z) = ic(ψ(z) − y·Fs(y, z))` for even `g` and `y > 1`. -/
theorem hasDerivAt_fsZ {g : ℝ → ℝ} {c y : ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hy : 1 < y) (z : ℝ) :
    HasDerivAt (fun z => fsZ c g y z) (I * c * ((psi c g z : ℂ) - y * fsZ c g y z)) z := by
  have hu : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hys : ∀ s ∈ Icc (-1 : ℝ) 1, (((y + s : ℝ)) : ℂ) ≠ 0 := fun s hs => by
    exact_mod_cast (show y + s ≠ 0 by linarith [hs.1])
  have hysr : ∀ s ∈ Icc (-1 : ℝ) 1, y - 1 ≤ y + s := fun s hs => by linarith [hs.1]
  have hGc : ContinuousOn (fun s => (g s : ℂ)) (Icc (-1) 1) := Complex.continuous_ofReal.comp_continuousOn hg
  have hden : ContinuousOn (fun s : ℝ => (((y + s : ℝ)) : ℂ)) (Icc (-1) 1) := by fun_prop
  have hphc : ∀ z, Continuous fun s => ph c z s := fun z => by unfold ph; fun_prop
  set k : ℝ → ℝ → ℂ := fun z s => ph c z s / ((y + s : ℝ) : ℂ) with hk
  set k' : ℝ → ℝ → ℂ := fun z s => ph c z s * (((c * s : ℝ) : ℂ) * I) / ((y + s : ℝ) : ℂ) with hk'
  have hkc : ∀ z, ContinuousOn (k z) (Icc (-1) 1) := fun z =>
    (hphc z).continuousOn.div hden hys
  have hk'c : ∀ z, ContinuousOn (k' z) (Icc (-1) 1) := fun z =>
    ((hphc z).continuousOn.mul (by fun_prop)).div hden hys
  have hD := hasDerivAt_rint_near (G := fun s => (g s : ℂ)) (k := k) (k' := k') (z₀ := z) (r := 1)
    (C := |c| / (y - 1)) one_pos hGc (fun z _ => hkc z) (hk'c z)
    (fun z _ s hs => (hasDerivAt_ph c s z).div_const _)
    (fun z _ s hs => by
      simp only [hk', norm_div, norm_mul, norm_ph, one_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      have hs1 : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
      have hpos : 0 < y + s := by linarith [hysr s hs]
      rw [abs_of_pos hpos, div_le_div_iff₀ hpos (by linarith)]
      have := mul_le_mul_of_nonneg_left hs1 (abs_nonneg c)
      nlinarith [abs_nonneg c, hysr s hs, abs_nonneg s])
  have he : (fun z => fsZ c g y z) = fun z => ∫ s in (-1 : ℝ)..1, (g s : ℂ) * k z s := by
    funext z; rw [fsZ_eq]
  rw [he]
  refine hD.congr_deriv ?_
  -- `∫ g k' = ic(∫ g e − y ∫ g e/(y + s))`
  have i1 : IntervalIntegrable (fun s => (g s : ℂ) * ph c z s) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable; rw [hu]; exact hGc.mul (hphc z).continuousOn
  have i2 : IntervalIntegrable (fun s => (g s : ℂ) * k z s) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable; rw [hu]; exact hGc.mul (hkc z)
  have hpt : ∀ s ∈ uIcc (-1 : ℝ) 1, (g s : ℂ) * k' z s
      = I * c * ((g s : ℂ) * ph c z s) - I * c * y * ((g s : ℂ) * k z s) := by
    intro s hs
    rw [hu] at hs
    have h0 := hys s hs
    simp only [hk, hk']
    field_simp
    push_cast
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hpsi : ∫ s in (-1 : ℝ)..1, (g s : ℂ) * ph c z s = (psi c g z : ℂ) := by
    rw [← Cvs.L2a.BernsteinRieszSymbolBounds.ek_integral_even hg heven c z]
    rfl
  rw [hpsi, show fsZ c g y z = ∫ s in (-1 : ℝ)..1, (g s : ℂ) * k z s from fsZ_eq c g y z]
  ring

/-- `∂_z[e^{icyz}Fs(y, z)] = ic e^{icyz}ψ(z)`. -/
theorem hasDerivAt_eF_mul_fsZ {g : ℝ → ℝ} {c y : ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hy : 1 < y) (z : ℝ) :
    HasDerivAt (fun z => eF c y z * fsZ c g y z) (I * c * eF c y z * (psi c g z : ℂ)) z := by
  have := (hasDerivAt_eF c y z).mul (hasDerivAt_fsZ (c := c) hg heven hy z)
  refine this.congr_deriv ?_
  push_cast
  ring

/-- Riemann–Lebesgue: `Fs(y, Z) → 0` as `Z → ∞`. -/
theorem tendsto_fsZ {g : ℝ → ℝ} {c y : ℝ} (hc : 0 < c) (hg : ContinuousOn g (Icc (-1) 1)) (hy : 1 < y) :
    Tendsto (fun Z => fsZ c g y Z) atTop (𝓝 0) := by
  set f : ℝ → ℂ := (Ioc (-1 : ℝ) 1).indicator (fun s => (g s : ℂ) / ((y + s : ℝ) : ℂ)) with hf
  have hcont : ContinuousOn (fun s => (g s : ℂ) / ((y + s : ℝ) : ℂ)) (Icc (-1) 1) :=
    (Complex.continuous_ofReal.comp_continuousOn hg).div (by fun_prop) fun s hs => by
      exact_mod_cast (show y + s ≠ 0 by linarith [hs.1])
  have hfi : Integrable f := by
    rw [hf, integrable_indicator_iff measurableSet_Ioc]
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have RL := Real.tendsto_integral_exp_smul_cocompact f
  have hw : Tendsto (fun Z : ℝ => -(c * Z) / (2 * π)) atTop (cocompact ℝ) := by
    apply Tendsto.mono_right _ atBot_le_cocompact
    have : Tendsto (fun Z : ℝ => -(c * Z)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc)
    exact this.atBot_div_const (by positivity)
  refine (RL.comp hw).congr fun Z => ?_
  simp only [Function.comp]
  rw [fsZ_eq, intervalIntegral.integral_of_le (by norm_num), hf]
  rw [← integral_indicator measurableSet_Ioc]
  congr 1
  funext v
  by_cases hv : v ∈ Ioc (-1 : ℝ) 1
  · rw [indicator_of_mem hv, indicator_of_mem hv, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    unfold ph
    have e : ((2 * π * -(v * (-(c * Z) / (2 * π))) : ℝ) : ℂ) = ((c * Z * v : ℝ) : ℂ) := by
      congr 1; field_simp
    rw [e]
    ring
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, smul_zero]

/-- `Fs(−y, z) = −conj Fs(y, z)` for even real `g`. -/
theorem fsZ_neg {g : ℝ → ℝ} {c y z : ℝ} (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    fsZ c g (-y) z = -(starRingEnd ℂ) (fsZ c g y z) := by
  rw [fsZ_eq, fsZ_eq]
  have hn := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun s => (g s : ℂ) * (ph c z s / ((-y + s : ℝ) : ℂ)))
  simp only [neg_neg] at hn
  rw [← hn, intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
    ← integral_conj, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  simp only [heven s hs', ph, map_mul, map_div₀, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have e1 : ((-y + -s : ℝ) : ℂ) = -((y + s : ℝ) : ℂ) := by push_cast; ring
  have e2 : (((c * z * -s : ℝ)) : ℂ) * I = ((c * z * s : ℝ) : ℂ) * -I := by push_cast; ring
  rw [e1, e2]
  ring

/-- `‖Fs(−y, z)‖ = ‖Fs(y, z)‖` for even real `g`. -/
theorem norm_fsZ_neg {g : ℝ → ℝ} {c y z : ℝ} (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) :
    ‖fsZ c g (-y) z‖ = ‖fsZ c g y z‖ := by
  rw [fsZ_neg heven, norm_neg, Complex.norm_conj]

end Cvs.Prolate.RungStieltjesTransform

end
