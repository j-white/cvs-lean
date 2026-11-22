import Mathlib
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.Envelope.EdgeValueSoninBound
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.RadialCutResolvent
import Cvs.Upstream.LevyConditionL1Modulus
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyEnergyTwoBounds
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge layer of a radial cut

For `1 ≤ M ≤ ξ₀` the edge piece `f_e = logScale(1_{(M,ξ₀]}ψ)` is a cut of `h(s) = ψ(eˢ)e^{s/2}` with
`|h| ≤ √ξ₀|ψ(1)|` and `|h'| ≤ √ξ₀|ψ(1)|(1 + c²ξ₀³)/2` (Sonin and the flux bound), so its `L¹` modulus is linear and
`archFull f_e ≤ HLu₀ + 4N_e log(1/u₀) + 16N_e` for `0 < u₀ ≤ 1`, `N_e = ∫_M^{ξ₀} ψ²`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology
open Cvs.Zeta.Explicit.Weil (selfConvolution)
open Cvs.L2a.TailLogScaleTest (logScale)

namespace Cvs.L2a.RadialCutEdgeLayer

/-- **The `L¹` modulus of a cut on `(a, b]`**: `∫|f − f(· + v)| ≤ (L_h(b − a) + 2H)v`. -/
theorem modulus_Ioc {h : ℝ → ℝ} {a b H Lh v : ℝ} (hab : a ≤ b) (hv : 0 ≤ v) (hLh : 0 ≤ Lh) (hH0 : 0 ≤ H)
    (hint : IntegrableOn h (Ioc a b)) (hbd : ∀ s ∈ Ioc a b, |h s| ≤ H)
    (hlip : ∀ s ∈ Ioc a b, ∀ t ∈ Ioc a b, |h s - h t| ≤ Lh * |s - t|) :
    Integrable (fun s => (Ioc a b).indicator h s - (Ioc a b).indicator h (s + v)) volume
      ∧ ∫ s, |(Ioc a b).indicator h s - (Ioc a b).indicator h (s + v)| ≤ (Lh * (b - a) + 2 * H) * v := by
  set g : ℝ → ℝ := fun t => h (t + a) with hg
  have hind : ∀ s, (Ioc a b).indicator h s = (Ioc 0 (b - a)).indicator g (s - a) := by
    intro s
    by_cases hs : s ∈ Ioc a b
    · have : s - a ∈ Ioc 0 (b - a) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [indicator_of_mem hs, indicator_of_mem this]; simp [hg]
    · have : s - a ∉ Ioc 0 (b - a) := fun h' => hs ⟨by linarith [h'.1], by linarith [h'.2]⟩
      rw [indicator_of_notMem hs, indicator_of_notMem this]
  have hgint : IntegrableOn g (Ioc 0 (b - a)) := by
    have h1 : Integrable ((Ioc a b).indicator h) volume := (integrable_indicator_iff measurableSet_Ioc).mpr hint
    have h2 := h1.comp_add_right a
    rw [← integrable_indicator_iff measurableSet_Ioc]
    refine h2.congr (Eventually.of_forall fun t => ?_)
    simp only; rw [hind]; simp
  have hgbd : ∀ t ∈ Ioc 0 (b - a), |g t| ≤ H := fun t ht => hbd (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hglip : ∀ s ∈ Ioc 0 (b - a), ∀ t ∈ Ioc 0 (b - a), |g s - g t| ≤ Lh * |s - t| := by
    intro s hs t ht
    have := hlip (s + a) ⟨by linarith [hs.1], by linarith [hs.2]⟩ (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa [hg] using this
  obtain ⟨hi, hm⟩ := Cvs.Upstream.LevyConditionL1Modulus.modulus_cut (sub_nonneg.mpr hab) hv hLh hH0 hgint hgbd hglip
  have e1 : (fun s => (Ioc a b).indicator h s - (Ioc a b).indicator h (s + v))
      = fun s => (fun t => (Ioc 0 (b - a)).indicator g t - (Ioc 0 (b - a)).indicator g (t + v)) (s - a) := by
    funext s; rw [hind, hind]; simp only; congr 2; ring
  refine ⟨?_, ?_⟩
  · rw [e1]; exact hi.comp_sub_right a
  · have e2 : (fun s => |(Ioc a b).indicator h s - (Ioc a b).indicator h (s + v)|)
        = fun s => (fun t => |(Ioc 0 (b - a)).indicator g t - (Ioc 0 (b - a)).indicator g (t + v)|) (s - a) := by
      funext s; rw [hind, hind]; simp only; congr 3; ring
    rw [e2, integral_sub_right_eq_self (μ := volume)
      (fun t => |(Ioc 0 (b - a)).indicator g t - (Ioc 0 (b - a)).indicator g (t + v)|) a]
    exact hm

/-- The edge piece is a cut on the log scale. -/
theorem logScale_Ioc (ψ : ℝ → ℝ) {M ξ : ℝ} (hM : 0 < M) (hξ : 0 < ξ) :
    logScale ((Ioc M ξ).indicator ψ) = (Ioc (Real.log M) (Real.log ξ)).indicator (fun s => ψ (exp s) * exp (s / 2)) := by
  funext s
  unfold logScale
  by_cases hs : s ∈ Ioc (Real.log M) (Real.log ξ)
  · have : exp s ∈ Ioc M ξ := ⟨by rw [← exp_log hM]; exact exp_lt_exp.mpr hs.1,
      by rw [← exp_log hξ]; exact exp_le_exp.mpr hs.2⟩
    rw [indicator_of_mem this, indicator_of_mem hs]
  · have : exp s ∉ Ioc M ξ := by
      intro h; apply hs
      exact ⟨by rw [← exp_lt_exp, exp_log hM]; exact h.1, by rw [← exp_le_exp, exp_log hξ]; exact h.2⟩
    rw [indicator_of_notMem this, indicator_of_notMem hs, zero_mul]

section Radial

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)

include hψ hv hode in
/-- **The edge piece is bounded and Lipschitz**: on `(log M, log ξ₀]`, `|h| ≤ √ξ₀|ψ(1)|` and
`|h(s) − h(t)| ≤ √ξ₀|ψ(1)|(1 + c²ξ₀³)/2 · |s − t|`. -/
theorem edge_bounds (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {M ξ₀ : ℝ} (hM : 1 ≤ M) (hMξ : M ≤ ξ₀) :
    (∀ s ∈ Ioc (Real.log M) (Real.log ξ₀), |ψ (exp s) * exp (s / 2)| ≤ √ξ₀ * |ψ 1|) ∧
      (∀ s ∈ Ioc (Real.log M) (Real.log ξ₀), ∀ t ∈ Ioc (Real.log M) (Real.log ξ₀),
        |ψ (exp s) * exp (s / 2) - ψ (exp t) * exp (t / 2)|
          ≤ √ξ₀ * |ψ 1| * (1 + c ^ 2 * ξ₀ ^ 3) / 2 * |s - t|) := by
  have hM0 : 0 < M := by linarith
  have hξ0 : 0 < ξ₀ := by linarith
  have hψ' : ∀ r ∈ Icc 1 ξ₀, HasDerivAt ψ (v r) r := fun r hr => hψ r hr.1
  have hv' : ∀ r ∈ Icc 1 ξ₀, HasDerivAt v (v' r) r := fun r hr => hv r hr.1
  have hode' : ∀ r ∈ Icc 1 ξ₀, (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0 :=
    fun r hr => hode r hr.1
  set a := Real.log M
  set b := Real.log ξ₀
  have hab : a ≤ b := Real.log_le_log hM0 hMξ
  have hmem : ∀ s ∈ Icc a b, exp s ∈ Icc 1 ξ₀ := fun s hs =>
    ⟨le_trans hM (by rw [← exp_log hM0]; exact exp_le_exp.mpr hs.1), by rw [← exp_log hξ0]; exact exp_le_exp.mpr hs.2⟩
  have hsq : ∀ s ∈ Icc a b, |ψ (exp s)| ≤ |ψ 1| := fun s hs =>
    sq_le_sq.mp (Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge hχ (hmem s hs) hψ' hv' hode')
  have hexp : ∀ s ∈ Icc a b, exp (s / 2) ≤ √ξ₀ := fun s hs => by
    rw [show √ξ₀ = exp (b / 2) by rw [sqrt_eq_rpow, rpow_def_of_pos hξ0]; ring_nf; rfl]
    exact exp_le_exp.mpr (by linarith [hs.2])
  have hexp1 : ∀ s ∈ Icc a b, exp s ≤ ξ₀ := fun s hs => (hmem s hs).2
  have hvb : ∀ s ∈ Icc a b, |v (exp s)| ≤ c ^ 2 * ξ₀ ^ 2 * |ψ 1| / 2 := fun s hs => by
    have h := Cvs.Prolate.Envelope.EdgeValueSoninBound.deriv_le hχ hψ' hv' hode' (hmem s hs)
    refine h.trans ?_
    have : c ^ 2 * exp s ^ 2 - χ ≤ c ^ 2 * ξ₀ ^ 2 := by
      have := pow_le_pow_left₀ (exp_pos s).le (hexp1 s hs) 2
      nlinarith [sq_nonneg c]
    gcongr
  refine ⟨fun s hs => ?_, fun s hs t ht => ?_⟩
  · rw [abs_mul, abs_of_pos (exp_pos _), mul_comm]
    exact mul_le_mul (hexp s ⟨hs.1.le, hs.2⟩) (hsq s ⟨hs.1.le, hs.2⟩) (abs_nonneg _) (sqrt_nonneg _)
  · set C := √ξ₀ * |ψ 1| * (1 + c ^ 2 * ξ₀ ^ 3) / 2
    have hd : ∀ x ∈ Icc a b, HasDerivWithinAt (fun s => ψ (exp s) * exp (s / 2))
        (v (exp x) * exp x * exp (x / 2) + ψ (exp x) * (exp (x / 2) * (1 / 2))) (Icc a b) x := by
      intro x hx
      have h1 := (hψ (exp x) (hmem x hx).1).comp x (hasDerivAt_exp x)
      have h2 : HasDerivAt (fun y => exp (y / 2)) (exp (x / 2) * (1 / 2)) x := by
        simpa using ((hasDerivAt_id x).div_const 2).exp
      exact (h1.mul h2).hasDerivWithinAt
    have hbd : ∀ x ∈ Icc a b, ‖v (exp x) * exp x * exp (x / 2) + ψ (exp x) * (exp (x / 2) * (1 / 2))‖ ≤ C := by
      intro x hx
      rw [Real.norm_eq_abs]
      have e1 := exp_pos x
      have e2 := exp_pos (x / 2)
      have hs0 : 0 ≤ √ξ₀ := sqrt_nonneg _
      calc |v (exp x) * exp x * exp (x / 2) + ψ (exp x) * (exp (x / 2) * (1 / 2))|
          ≤ |v (exp x)| * exp x * exp (x / 2) + |ψ (exp x)| * (exp (x / 2) * (1 / 2)) := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos e1, abs_of_pos e2]; norm_num
        _ ≤ c ^ 2 * ξ₀ ^ 2 * |ψ 1| / 2 * ξ₀ * √ξ₀ + |ψ 1| * (√ξ₀ * (1 / 2)) := by
            have k1 : |v (exp x)| * exp x * exp (x / 2) ≤ c ^ 2 * ξ₀ ^ 2 * |ψ 1| / 2 * ξ₀ * √ξ₀ :=
              mul_le_mul (mul_le_mul (hvb x hx) (hexp1 x hx) e1.le (by positivity)) (hexp x hx) e2.le (by positivity)
            have k2 : |ψ (exp x)| * (exp (x / 2) * (1 / 2)) ≤ |ψ 1| * (√ξ₀ * (1 / 2)) :=
              mul_le_mul (hsq x hx) (by linarith [hexp x hx]) (by positivity) (abs_nonneg _)
            linarith
        _ = C := by ring
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hd hbd ⟨ht.1.le, ht.2⟩ ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact h

include hψ hv hode in
/-- **The Lévy energy of the edge piece**: with `H = √ξ₀|ψ(1)|`, `L_h = H(1 + c²ξ₀³)/2` and `0 < u₀ ≤ 1`:
`archFull f_e ≤ H(L_h log(ξ₀/M) + 2H)u₀ + 4N_e log(1/u₀) + 16N_e`. -/
theorem archFull_edge_le (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {M ξ₀ u₀ : ℝ} (hM : 1 ≤ M) (hMξ : M ≤ ξ₀)
    (hu₀ : 0 < u₀) (hu₀1 : u₀ ≤ 1) :
    MemLp (logScale ((Ioc M ξ₀).indicator ψ)) 2 volume ∧
      Integrable (logScale ((Ioc M ξ₀).indicator ψ)) volume ∧
      IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale ((Ioc M ξ₀).indicator ψ))) (Ioi 0) ∧
      Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale ((Ioc M ξ₀).indicator ψ))
        ≤ √ξ₀ * |ψ 1| * (√ξ₀ * |ψ 1| * (1 + c ^ 2 * ξ₀ ^ 3) / 2 * (Real.log ξ₀ - Real.log M) + 2 * (√ξ₀ * |ψ 1|))
            * u₀
          + 4 * (∫ s, logScale ((Ioc M ξ₀).indicator ψ) s ^ 2) * Real.log (1 / u₀)
          + 16 * (∫ s, logScale ((Ioc M ξ₀).indicator ψ) s ^ 2) := by
  have hM0 : 0 < M := by linarith
  have hξ0 : 0 < ξ₀ := by linarith
  set a := Real.log M
  set b := Real.log ξ₀
  have hab : a ≤ b := Real.log_le_log hM0 hMξ
  set h : ℝ → ℝ := fun s => ψ (exp s) * exp (s / 2) with hh
  set H := √ξ₀ * |ψ 1| with hH
  set Lh := √ξ₀ * |ψ 1| * (1 + c ^ 2 * ξ₀ ^ 3) / 2 with hLh
  have hH0 : 0 ≤ H := by positivity
  have hLh0 : 0 ≤ Lh := by positivity
  obtain ⟨hbd, hlip⟩ := edge_bounds hψ hv hode hχ0 hχ hM hMξ
  have hf : logScale ((Ioc M ξ₀).indicator ψ) = (Ioc a b).indicator h := logScale_Ioc ψ hM0 hξ0
  rw [hf]
  have hcont : ContinuousOn h (Icc a b) := by
    have ha0 : 0 ≤ a := Real.log_nonneg hM
    exact ((Cvs.Prolate.RadialCutResolvent.continuousOn_comp_exp hψ ha0).mono (Icc_subset_Ici_self)).mul (by fun_prop)
  have hint : IntegrableOn h (Ioc a b) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hi1 : Integrable ((Ioc a b).indicator h) volume := (integrable_indicator_iff measurableSet_Ioc).mpr hint
  have hbd' : ∀ s, |(Ioc a b).indicator h s| ≤ H := by
    intro s; by_cases hs : s ∈ Ioc a b
    · rw [indicator_of_mem hs]; exact hbd s hs
    · rw [indicator_of_notMem hs, abs_zero]; exact hH0
  have h2 : MemLp ((Ioc a b).indicator h) 2 volume := by
    rw [memLp_two_iff_integrable_sq hi1.aestronglyMeasurable]
    refine Integrable.mono' (hi1.abs.const_mul H) (hi1.aestronglyMeasurable.pow 2) (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_pow, sq]
    exact mul_le_mul_of_nonneg_right (hbd' s) (abs_nonneg _) |>.trans (by rw [mul_comm])
  have hmod := fun v (hv : 0 ≤ v) => modulus_Ioc hab hv hLh0 hH0 hint hbd hlip
  have hlevy := Cvs.Upstream.LevyConditionL1Modulus.integrableOn_levy h2 hbd' (fun v hv => (hmod v hv).1) (fun v hv => (hmod v hv).2)
  refine ⟨h2, hi1, hlevy, ?_⟩
  have := Cvs.WeilForm.Archimedean.LevyEnergyTwoBounds.archFull_le_of_modulus h2 hbd' (fun v hv => (hmod v hv).1) (fun v hv => (hmod v hv).2)
    hu₀ hu₀1
  refine this.trans (le_of_eq ?_)
  ring

end Radial

end Cvs.L2a.RadialCutEdgeLayer
