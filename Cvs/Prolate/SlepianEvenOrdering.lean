import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularEdgeValueNonzero
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.CosineTransformEigenRelation
import Cvs.Prolate.CosineTransformSignLaw
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelPositiveCoupling
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionChiVariation
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Slepian ordering on the even spectrum

For consecutive even levels `χ < χ'`, `CosineChristoffelDarboux`'s identity `c²(μ'² − μ²)∫s²gh = (χ' − χ)μμ'g(1)h(1)` with `μμ' < 0`
(`CosineTransformSignLaw`'s sign law, `EdgeCentreSign`'s centre alternation) and `EvenLevelPositiveCoupling`'s `∫₀¹ s² f_χ f_χ' > 0` gives `μ'² < μ²`; induction over the
finitely many even levels in between extends it to all `χ < χ'`. So `λ = (c/2π)μ² = τ²` decreases along the even
spectrum, and at equal levels `g ∝ h` gives `μ = μ'`.
-/

noncomputable section

open Real Set Filter Topology intervalIntegral MeasureTheory Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.RegularSolutionChiVariation Cvs.Prolate.EdgeCentreSign Cvs.Prolate.CosineChristoffelDarboux Cvs.Prolate.EvenLevelPositiveCoupling
open scoped Interval

namespace Cvs.Prolate.SlepianEvenOrdering

/-- **`regV₂` is continuous on `(−1, ∞)`**: off `1` a quotient with nonzero denominator; at `1` the numerator
`N = (Q − χ)f + 2rV` vanishes and `−N/(r² − 1) = −slope N 1 r/(r + 1) → −N'(1)/2 = regV₂ 1`. -/
theorem continuousAt_regV₂ (Q : C(ℝ, ℝ)) (χ : ℝ) {Q₁ : ℝ} (hQ : HasDerivAt Q Q₁ 1) {r : ℝ} (hr : -1 < r) :
    ContinuousAt (regV₂ Q Q₁ χ) r := by
  have hVd : ∀ x, -1 < x → HasDerivAt (regV Q χ) (regV₂ Q Q₁ χ x) x := fun x hx => (regSol_ode Q χ hQ x hx).1
  by_cases h1 : r = 1
  · subst h1
    set N : ℝ → ℝ := fun x => (Q x - χ) * regSol Q χ x + 2 * x * regV Q χ x with hN
    have hNd : HasDerivAt N (Q₁ * regSol Q χ 1 + (Q 1 - χ) * regV Q χ 1
        + (2 * regV Q χ 1 + 2 * 1 * regV₂ Q Q₁ χ 1)) 1 := by
      have e1 := (hQ.sub_const χ).mul (hasDerivAt_regSol Q χ (by norm_num : (-1:ℝ) < 1))
      have e2 := ((hasDerivAt_id (1:ℝ)).const_mul 2).mul (hVd 1 (by norm_num))
      refine (e1.add e2).congr_deriv ?_
      simp only [id, mul_one]
    have hN1 : N 1 = 0 := by
      simp only [hN, regSol_one, regV_one]; ring
    have hslope := hasDerivAt_iff_tendsto_slope.mp hNd
    rw [continuousAt_iff_punctured_nhds]
    have hden : Tendsto (fun x : ℝ => x + 1) (𝓝[≠] (1:ℝ)) (𝓝 (1 + 1)) :=
      ((continuous_id.add continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
    have hlim := hslope.neg.div hden (by norm_num)
    have hval : regV₂ Q Q₁ χ 1 = -(Q₁ * regSol Q χ 1 + (Q 1 - χ) * regV Q χ 1
        + (2 * regV Q χ 1 + 2 * 1 * regV₂ Q Q₁ χ 1)) / (1 + 1) := by
      rw [regSol_one, regV_one]
      simp only [regV₂, ite_true]
      ring
    rw [hval]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (show (-1:ℝ) < 1 by norm_num))] with x hx hx'
    have hx1 : x ≠ 1 := hx
    have hxm : -1 < x := hx'
    show -slope N 1 x / (x + 1) = regV₂ Q Q₁ χ x
    rw [slope_def_field, hN1, sub_zero]
    simp only [regV₂, ite_eq_right hx1]
    have hp : pP x = (x - 1) * (x + 1) := by unfold pP; ring
    have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hx2 : x + 1 ≠ 0 := by linarith
    rw [hp, hN]
    field_simp
  · have hev : regV₂ Q Q₁ χ =ᶠ[𝓝 r] fun x => -((Q x - χ) * regSol Q χ x + 2 * x * regV Q χ x) / pP x := by
      filter_upwards [isOpen_ne.mem_nhds h1] with x hx
      simp only [regV₂, ite_eq_right hx]
    refine ContinuousAt.congr ?_ hev.symm
    have hp : pP r ≠ 0 := pP_ne_zero hr h1
    refine ContinuousAt.div ?_ ?_ hp
    · exact (((Q.continuous.continuousAt.sub continuousAt_const).mul
        (hasDerivAt_regSol Q χ hr).continuousAt).add
        ((continuousAt_const.mul continuousAt_id).mul (hVd r hr).continuousAt)).neg
    · have hc : Continuous (fun x : ℝ => x ^ 2 - 1) := by fun_prop
      exact hc.continuousAt

/-- **Every even level carries a `C²` even eigenfunction with continuous second derivative** (the construction of
`EdgeCentreSign`'s `isEvenLevel_iff`, `g = f_χ(|s|)`, with `g'' = regV₂(|s|)` continuous by `continuousAt_regV₂`). -/
theorem exists_regular_even (c χ : ℝ) (hχ : χ ∈ evenSpec (sqC c)) :
    ∃ g g₁ g₂ : ℝ → ℝ, (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) ∧ ContinuousOn g₂ (uIcc (-1) 1) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) ∧ ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0 := by
  have hU : regU (sqC c) χ 0 = 0 := hχ
  have hV0 : regV (sqC c) χ 0 = 0 := by
    have := pP_mul_regV (sqC c) χ (show (-1:ℝ) < 0 by norm_num)
    rw [hU] at this
    unfold pP at this
    linarith
  have hode := regSol_ode (sqC c) χ (by simpa using hasDerivAt_sqC c 1)
  have hsq : ∀ x : ℝ, sqC c x = c ^ 2 * x ^ 2 := fun x => rfl
  refine ⟨fun s => regSol (sqC c) χ |s|,
    fun s => if 0 ≤ s then regV (sqC c) χ s else -regV (sqC c) χ (-s),
    fun s => regV₂ (sqC c) (2 * c ^ 2) χ |s|, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    dsimp only
    rcases lt_trichotomy s 0 with h | h | h
    · rw [ite_eq_right (not_le.mpr h)]
      have hd := HasDerivAt.comp_of_eq s
        (hasDerivAt_regSol (sqC c) χ (by linarith [hs.2] : (-1:ℝ) < -s)) (hasDerivAt_neg' s) rfl
      refine (hd.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with t ht
      simp [abs_of_neg (show t < 0 from ht)]
    · subst h
      rw [ite_eq_left le_rfl, hV0]
      have hR : HasDerivWithinAt (fun t => regSol (sqC c) χ |t|) 0 (Ici 0) 0 := by
        have := (hasDerivAt_regSol (sqC c) χ (by norm_num : (-1:ℝ) < 0)).hasDerivWithinAt (s := Ici 0)
        rw [hV0] at this
        exact this.congr (fun t ht => by simp [abs_of_nonneg (show (0:ℝ) ≤ t from ht)]) (by simp)
      have hL : HasDerivWithinAt (fun t => regSol (sqC c) χ |t|) 0 (Iic 0) 0 := by
        have := (HasDerivAt.comp_of_eq (0:ℝ) (hasDerivAt_regSol (sqC c) χ (by norm_num : (-1:ℝ) < 0))
          (hasDerivAt_neg' (0:ℝ)) (by simp)).hasDerivWithinAt (s := Iic 0)
        rw [hV0, zero_mul] at this
        exact this.congr (fun t ht => by simp [abs_of_nonpos (show t ≤ (0:ℝ) from ht)]) (by simp)
      have := hL.union hR
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · rw [ite_eq_left h.le]
      refine (hasDerivAt_regSol (sqC c) χ (by linarith)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with t ht
      simp [abs_of_pos (show (0:ℝ) < t from ht)]
  · intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    dsimp only
    rcases lt_trichotomy s 0 with h | h | h
    · have hd := (HasDerivAt.comp_of_eq s (hode (-s) (by linarith [hs.2])).1 (hasDerivAt_neg' s) rfl).neg
      rw [abs_of_neg h]
      refine (hd.congr_deriv (by simp)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with t ht
      simp [ite_eq_right (not_le.mpr (show t < 0 from ht))]
    · subst h
      rw [abs_zero]
      have hR : HasDerivWithinAt (fun t => if 0 ≤ t then regV (sqC c) χ t else -regV (sqC c) χ (-t))
          (regV₂ (sqC c) (2 * c ^ 2) χ 0) (Ici 0) 0 :=
        ((hode 0 (by norm_num)).1.hasDerivWithinAt).congr
          (fun t ht => ite_eq_left (show (0:ℝ) ≤ t from ht)) (ite_eq_left le_rfl)
      have hneg : HasDerivAt (fun t => -regV (sqC c) χ (-t)) (regV₂ (sqC c) (2 * c ^ 2) χ 0) 0 := by
        have := (HasDerivAt.comp_of_eq (0:ℝ) (hode 0 (by norm_num)).1 (hasDerivAt_neg' (0:ℝ))
          (by simp)).neg
        exact this.congr_deriv (by ring)
      have hL : HasDerivWithinAt (fun t => if 0 ≤ t then regV (sqC c) χ t else -regV (sqC c) χ (-t))
          (regV₂ (sqC c) (2 * c ^ 2) χ 0) (Iic 0) 0 := by
        refine hneg.hasDerivWithinAt.congr (fun t ht => ?_) ?_
        · rcases eq_or_lt_of_le (show t ≤ (0:ℝ) from ht) with h0 | h0
          · subst h0; simp [hV0]
          · exact ite_eq_right (not_le.mpr h0)
        · simp [hV0]
      have := hL.union hR
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · rw [abs_of_pos h]
      refine (hode s (by linarith)).1.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with t ht
      simp [ite_eq_left (show (0:ℝ) ≤ t from (show (0:ℝ) < t from ht).le)]
  · intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    have hQ : HasDerivAt (sqC c) (2 * c ^ 2) 1 := by simpa using hasDerivAt_sqC c 1
    have habs : -1 < |s| := lt_of_lt_of_le (by norm_num) (abs_nonneg s)
    exact ((continuousAt_regV₂ (sqC c) χ hQ habs).comp continuous_abs.continuousAt).continuousWithinAt
  · intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    dsimp only
    rcases le_or_gt 0 s with h | h
    · have := (hode s (by linarith)).2
      rw [hsq] at this
      simp only [ite_eq_left h, abs_of_nonneg h]
      linear_combination -this
    · have := (hode (-s) (by linarith [hs.2])).2
      rw [hsq] at this
      simp only [ite_eq_right (not_le.mpr h), abs_of_neg h]
      linear_combination -this
  · intro s _
    simp [abs_neg]
  · exact ⟨1, ⟨by norm_num, le_rfl⟩, by simp [regSol_one]⟩

/-- **Centre alternation**: consecutive even levels have centre values of opposite sign (`EdgeCentreSign`'s rotation). -/
theorem centre_alternates (Q : C(ℝ, ℝ)) {χ χ' : ℝ} (hlt : χ < χ') (hχ : regU Q χ 0 = 0)
    (hχ' : regU Q χ' 0 = 0) (hcons : ∀ t ∈ Ioo χ χ', regU Q t 0 ≠ 0) :
    regSol Q χ 0 * regSol Q χ' 0 < 0 := by
  have hW : ∀ t, regSol Q t 0 * regUDot Q t 0 - regU Q t 0 * regDot Q t 0 < 0 :=
    fun t => wronskian_neg Q t (by norm_num) (by norm_num)
  have hWx := hW χ
  have hWy := hW χ'
  rw [hχ, zero_mul, sub_zero] at hWx
  rw [hχ', zero_mul, sub_zero] at hWy
  exact rotation_alternates (A := fun χ => regSol Q χ 0) (B := fun χ => regU Q χ 0) hlt
    (fun t _ => hasDerivAt_regU_chi Q t (by norm_num)) hχ hχ' hcons hWx hWy

/-- Every even level of `c²s²` is nonnegative. -/
theorem nonneg_of_mem_evenSpec (c : ℝ) {χ : ℝ} (hχ : χ ∈ evenSpec (sqC c)) : 0 ≤ χ :=
  le_of_mem_evenSpec (sqC c) (fun χ hχ s _ => by
    show χ < c ^ 2 * s ^ 2
    nlinarith [sq_nonneg (c * s)]) hχ

/-- An even integrand on `[−1, 1]` integrates to twice its integral on `[0, 1]`. -/
theorem integral_even_fold {F : ℝ → ℝ} (hF : ContinuousOn F (Icc (-1) 1))
    (hev : ∀ s ∈ Icc (0:ℝ) 1, F (-s) = F s) :
    ∫ s in (-1:ℝ)..1, F s = 2 * ∫ s in (0:ℝ)..1, F s := by
  have hi1 : IntervalIntegrable F volume (-1) 0 :=
    (hF.mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable
  have hi2 : IntervalIntegrable F volume 0 1 :=
    (hF.mono (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hneg : ∫ s in (-1:ℝ)..0, F s = ∫ s in (0:ℝ)..1, F s := by
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1) F
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    exact hev s hs
  rw [hneg]; ring

/-- **ORD, consecutive step.** Even angular eigenfunctions `g` (level `χ`), `h` (level `χ'`) of the finite cosine
transform, `psi c g = μ g`, `psi c h = μ' h` on `[−1, 1]`, with `χ < χ'` consecutive in the even spectrum: `μ'² < μ²`.
CD identity + `μμ' < 0` (sign law and centre alternation) + `∫₀¹ s² f_χ f_χ' > 0`. -/
theorem mu_sq_lt_of_consecutive {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ χ' μ μ' : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ' * h s = 0)
    (heven' : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ' : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s)
    (hlt : χ < χ') (hcons : ∀ t ∈ Ioo χ χ', t ∉ evenSpec (sqC c)) : μ' ^ 2 < μ ^ 2 := by
  have hχm := mem_evenSpec_of_angular hg hg₁ hang heven hg0
  have hχm' := mem_evenSpec_of_angular hh hh₁ hang' heven' hh0
  have hχ0 := nonneg_of_mem_evenSpec c hχm
  have hχ0' := nonneg_of_mem_evenSpec c hχm'
  have hconsU : ∀ t ∈ Ioo χ χ', regU (sqC c) t 0 ≠ 0 := fun t ht hU => hcons t ht hU
  have hcd := cd_identity hg hg₁ hg₂c hang hh hh₁ hh₂c hang' hμ hμ'
  have hgm1 : g (-1) = g 1 := heven 1 ⟨by norm_num, le_rfl⟩
  have hhm1 : h (-1) = h 1 := heven' 1 ⟨by norm_num, le_rfl⟩
  rw [hgm1, hhm1] at hcd
  have hrg := angular_eq_mul_regSol hg hg₁ hang
  have hrh := angular_eq_mul_regSol hh hh₁ hang'
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  obtain ⟨s₁, hs₁, hhs₁⟩ := hh0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hgs₀
  have hh1 : h 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hh hh₁ hang' hs₁ hhs₁
  have hgc := continuousOn_of_hasDerivAt hg
  have hhc := continuousOn_of_hasDerivAt hh
  have hfold : ∫ s in (-1:ℝ)..1, s ^ 2 * g s * h s = 2 * ∫ s in (0:ℝ)..1, s ^ 2 * g s * h s := by
    refine integral_even_fold (((continuousOn_id.pow 2).mul hgc).mul hhc) (fun s hs => ?_)
    have hs' : s ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
    simp only [neg_sq, heven s hs', heven' s hs']
  have hrep : ∫ s in (0:ℝ)..1, s ^ 2 * g s * h s
      = g 1 * h 1 * ∫ s in (0:ℝ)..1, s ^ 2 * (regSol (sqC c) χ s * regSol (sqC c) χ' s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hs' : s ∈ Ioc (-1:ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
    rw [hrg s hs', hrh s hs']
    ring
  have hM := moment_pos (sqC c) hlt hχm hconsU
  set M := ∫ s in (0:ℝ)..1, s ^ 2 * (regSol (sqC c) χ s * regSol (sqC c) χ' s) with hMdef
  have hms := Cvs.Prolate.CosineTransformSignLaw.mu_sign hc hχ0 hg hg₁ hg₂c hang heven ⟨s₀, hs₀, hgs₀⟩ hμ
  have hms' := Cvs.Prolate.CosineTransformSignLaw.mu_sign hc hχ0' hh hh₁ hh₂c hang' heven' ⟨s₁, hs₁, hhs₁⟩ hμ'
  have halt := centre_alternates (sqC c) hlt hχm hχm' hconsU
  have hg0r : g 0 = g 1 * regSol (sqC c) χ 0 := hrg 0 ⟨by norm_num, by norm_num⟩
  have hh0r : h 0 = h 1 * regSol (sqC c) χ' 0 := hrh 0 ⟨by norm_num, by norm_num⟩
  rw [hg0r] at hms
  rw [hh0r] at hms'
  have hA : 0 < μ * regSol (sqC c) χ 0 := by
    have e : μ * (g 1 * regSol (sqC c) χ 0 * g 1) = (μ * regSol (sqC c) χ 0) * (g 1 * g 1) := by ring
    rw [e] at hms
    exact (mul_pos_iff_of_pos_right (mul_self_pos.mpr hg1)).mp hms
  have hB : 0 < μ' * regSol (sqC c) χ' 0 := by
    have e : μ' * (h 1 * regSol (sqC c) χ' 0 * h 1) = (μ' * regSol (sqC c) χ' 0) * (h 1 * h 1) := by ring
    rw [e] at hms'
    exact (mul_pos_iff_of_pos_right (mul_self_pos.mpr hh1)).mp hms'
  have hmm : μ * μ' < 0 := by
    have hAB := mul_pos hA hB
    have e : μ * regSol (sqC c) χ 0 * (μ' * regSol (sqC c) χ' 0)
        = (μ * μ') * (regSol (sqC c) χ 0 * regSol (sqC c) χ' 0) := by ring
    rw [e] at hAB
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hcon halt.le]
  -- assemble
  rw [hfold, hrep] at hcd
  have hgh : g 1 * h 1 ≠ 0 := mul_ne_zero hg1 hh1
  have hkey : c ^ 2 * (μ' ^ 2 - μ ^ 2) * (2 * M) = (χ' - χ) * (μ * μ') := by
    have e1 : c ^ 2 * (μ' ^ 2 - μ ^ 2) * (2 * (g 1 * h 1 * M))
        = (g 1 * h 1) * (c ^ 2 * (μ' ^ 2 - μ ^ 2) * (2 * M)) := by ring
    have e2 : (χ' - χ) * μ * μ' * (g 1 * h 1 + g 1 * h 1) / 2 = (g 1 * h 1) * ((χ' - χ) * (μ * μ')) := by ring
    rw [e1, e2] at hcd
    exact mul_left_cancel₀ hgh hcd
  have hrhs : (χ' - χ) * (μ * μ') < 0 := mul_neg_of_pos_of_neg (by linarith) hmm
  have hpos : 0 < c ^ 2 * (2 * M) := by positivity
  by_contra hcon
  push Not at hcon
  have : 0 ≤ c ^ 2 * (μ' ^ 2 - μ ^ 2) * (2 * M) := by
    have h0 : 0 ≤ μ' ^ 2 - μ ^ 2 := by linarith
    have := mul_nonneg h0 hpos.le
    linarith [show c ^ 2 * (μ' ^ 2 - μ ^ 2) * (2 * M) = (μ' ^ 2 - μ ^ 2) * (c ^ 2 * (2 * M)) by ring]
  linarith

/-- **ORD: the Slepian ordering on the even spectrum.** For even angular eigenfunctions `g` (level `χ`) and `h` (level
`χ'`) of the finite cosine transform with `χ < χ'`: `μ'² < μ²`. Induction over the finitely many even levels in
`(χ, χ')` (Cvs.Prolate.EdgeCentreSign), each carrying a regular eigenfunction (`exists_regular_even`, Cvs.Prolate.CosineTransformEigenRelation). -/
theorem mu_sq_lt {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ χ' μ μ' : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ' * h s = 0)
    (heven' : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ' : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s)
    (hlt : χ < χ') : μ' ^ 2 < μ ^ 2 := by
  suffices H : ∀ n : ℕ, ∀ (χ' μ' : ℝ) (h h₁ h₂ : ℝ → ℝ),
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) → (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s) →
      ContinuousOn h₂ (uIcc (-1) 1) →
      (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ' * h s = 0) →
      (∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) → (∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0) →
      (∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s) → χ < χ' →
      (evenSpec (sqC c) ∩ Ioo χ χ').ncard = n → μ' ^ 2 < μ ^ 2 from
    H _ χ' μ' h h₁ h₂ hh hh₁ hh₂c hang' heven' hh0 hμ' hlt rfl
  intro n
  induction n with
  | zero =>
    intro χ' μ' h h₁ h₂ hh hh₁ hh₂c hang' heven' hh0 hμ' hlt hn
    have hfin : (evenSpec (sqC c) ∩ Ioo χ χ').Finite :=
      (finite_evenSpec_Iio (sqC c) χ').subset (fun x hx => ⟨hx.1, hx.2.2⟩)
    have hemp := (Set.ncard_eq_zero hfin).mp hn
    exact mu_sq_lt_of_consecutive hc hg hg₁ hg₂c hang heven hg0 hh hh₁ hh₂c hang' heven' hh0 hμ hμ' hlt
      (fun t ht hmem => by
        have : t ∈ evenSpec (sqC c) ∩ Ioo χ χ' := ⟨hmem, ht⟩
        rw [hemp] at this; exact this)
  | succ k ih =>
    intro χ' μ' h h₁ h₂ hh hh₁ hh₂c hang' heven' hh0 hμ' hlt hn
    set S := evenSpec (sqC c) ∩ Ioo χ χ' with hSdef
    have hfin : S.Finite := (finite_evenSpec_Iio (sqC c) χ').subset (fun x hx => ⟨hx.1, hx.2.2⟩)
    have hne : S.Nonempty := by rw [← Set.ncard_pos hfin]; omega
    obtain ⟨χm, hχmS, hmax⟩ := Set.exists_max_image S id hfin hne
    have hS' : evenSpec (sqC c) ∩ Ioo χ χm = S \ {χm} := by
      ext z
      constructor
      · rintro ⟨hz, hz1, hz2⟩
        exact ⟨⟨hz, hz1, lt_trans hz2 hχmS.2.2⟩, ne_of_lt hz2⟩
      · rintro ⟨⟨hz, hz1, hz2⟩, hzm⟩
        exact ⟨hz, hz1, lt_of_le_of_ne (hmax z ⟨hz, hz1, hz2⟩) hzm⟩
    have hk : (evenSpec (sqC c) ∩ Ioo χ χm).ncard = k := by
      rw [hS', Set.ncard_sdiff_singleton_of_mem hχmS]; omega
    obtain ⟨gm, gm₁, gm₂, hgm, hgm₁, hgm₂c, hangm, hevenm, hgm0⟩ := exists_regular_even c χm hχmS.1
    obtain ⟨μm, hμm⟩ := Cvs.Prolate.CosineTransformEigenRelation.eigen_relation hgm hgm₁ hgm₂c hangm
    have h1 := ih χm μm gm gm₁ gm₂ hgm hgm₁ hgm₂c hangm hevenm hgm0 hμm hχmS.2.1 hk
    have h2 := mu_sq_lt_of_consecutive hc hgm hgm₁ hgm₂c hangm hevenm hgm0 hh hh₁ hh₂c hang' heven' hh0 hμm hμ'
      hχmS.2.2 (fun t ht hmem => by
        have := hmax t ⟨hmem, lt_trans hχmS.2.1 ht.1, ht.2⟩
        simp only [id] at this
        linarith [ht.1])
    linarith

/-- **ORD in concentration form**: `λ' = (c/2π)μ'² < λ = (c/2π)μ²` along the even spectrum. -/
theorem lam_lt {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ χ' μ μ' : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ' * h s = 0)
    (heven' : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ' : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s)
    (hlt : χ < χ') : (μ' * √(c / (2 * π))) ^ 2 < (μ * √(c / (2 * π))) ^ 2 := by
  have h := mu_sq_lt hc hg hg₁ hg₂c hang heven hg0 hh hh₁ hh₂c hang' heven' hh0 hμ hμ' hlt
  have hk : 0 < √(c / (2 * π)) ^ 2 := by positivity
  rw [mul_pow, mul_pow]
  exact mul_lt_mul_of_pos_right h hk

/-- **ORD on positive eigenvalues** (even-index rungs, `μ > 0` by Cvs.Prolate.EdgeCentreSign/Cvs.Prolate.CosineTransformSignLaw): `τ' = μ'√(c/2π) < τ = μ√(c/2π)`. -/
theorem tau_lt {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ χ' μ μ' : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ' * h s = 0)
    (heven' : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ' : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s)
    (hμpos : 0 < μ) (hμpos' : 0 < μ') (hlt : χ < χ') :
    μ' * √(c / (2 * π)) < μ * √(c / (2 * π)) := by
  have h := mu_sq_lt hc hg hg₁ hg₂c hang heven hg0 hh hh₁ hh₂c hang' heven' hh0 hμ hμ' hlt
  have hlt' : μ' < μ := by nlinarith
  exact mul_lt_mul_of_pos_right hlt' (Real.sqrt_pos.2 (by positivity))

/-- **Equal levels, equal eigenvalues**: nonzero even angular eigenfunctions `g`, `h` of `psi c` at the same level are
proportional on `[−1, 1]` (Cvs.Prolate.RegularSolutionEdge: both are edge multiples of `f_χ`), so their eigenvalues agree. -/
theorem mu_eq_of_same_level {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ μ μ' : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ * h s = 0)
    (heven' : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ' : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s) :
    μ = μ' := by
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  obtain ⟨s₁, hs₁, hhs₁⟩ := hh0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hgs₀
  have hh1 : h 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hh hh₁ hang' hs₁ hhs₁
  have hrg := angular_eq_mul_regSol hg hg₁ hang
  have hrh := angular_eq_mul_regSol hh hh₁ hang'
  set k := h 1 / g 1 with hk
  have hprop : ∀ s ∈ Icc (-1 : ℝ) 1, h s = k * g s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · subst h1
      rw [heven 1 ⟨by norm_num, le_rfl⟩, heven' 1 ⟨by norm_num, le_rfl⟩, hk]
      field_simp
    · rw [hrg s ⟨h1, hs.2⟩, hrh s ⟨h1, hs.2⟩, hk]
      field_simp
  have hpsi : psi c h 1 = k * psi c g 1 := by
    unfold psi Cvs.Prolate.SlepianCommutingRelation.kint
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [hprop s hs]
    ring
  have h1m : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  rw [hμ' 1 h1m, hμ 1 h1m, hprop 1 h1m] at hpsi
  have hk0 : k ≠ 0 := div_ne_zero hh1 hg1
  have : (μ' - μ) * (k * g 1) = 0 := by linear_combination hpsi
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h (mul_ne_zero hk0 hg1)

/-- **ORD, non-strict**: for even angular eigenfunctions at levels `χ ≤ χ'`, `μ'² ≤ μ²` (`mu_sq_lt` off the diagonal,
`mu_eq_of_same_level` on it). -/
theorem mu_sq_le {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ χ' μ μ' : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ' * h s = 0)
    (heven' : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ' : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s)
    (hle : χ ≤ χ') : μ' ^ 2 ≤ μ ^ 2 := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    rw [mu_eq_of_same_level hg hg₁ hang heven hg0 hh hh₁ hang' heven' hh0 hμ hμ']
  · exact (mu_sq_lt hc hg hg₁ hg₂c hang heven hg0 hh hh₁ hh₂c hang' heven' hh0 hμ hμ' hlt).le

/-- **`λ_i ≤ λ₈` whenever `χ₈ ≤ χ_i`**: with `λ = (c/2π)μ²`, the concentration eigenvalue is antitone along the even
spectrum, equality included. -/
theorem lam_le_of_chi_le {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ χ' μ μ' : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ' * h s = 0)
    (heven' : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hμ' : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ' * h s)
    (hle : χ ≤ χ') : (μ' * √(c / (2 * π))) ^ 2 ≤ (μ * √(c / (2 * π))) ^ 2 := by
  have h := mu_sq_le hc hg hg₁ hg₂c hang heven hg0 hh hh₁ hh₂c hang' heven' hh0 hμ hμ' hle
  rw [mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

/-- **The sign by index**: an even angular eigenfunction whose level has an even number of even levels below it has
`μ > 0` (`EdgeCentreSign`'s edge–centre sign with `CosineTransformSignLaw`'s `0 < μ g(0) g(1)`). -/
theorem mu_pos_of_even_index {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hidx : Even (evenSpec (sqC c) ∩ Iio χ).ncard) :
    0 < μ := by
  have hχ0 := nonneg_of_mem_evenSpec c (mem_evenSpec_of_angular hg hg₁ hang heven hg0)
  have hm := Cvs.Prolate.CosineTransformSignLaw.mu_sign hc hχ0 hg hg₁ hg₂c hang heven hg0 hμ
  have he := (edge_centre_pos_iff hg hg₁ hang heven hg0).mpr hidx
  exact (pos_iff_pos_of_mul_pos hm).mpr he

/-- **`0 < τ ≤ τ₀ ≤ 1`**: for the ground state `g` (no even level below `χ₀`) and an even-index even eigenfunction `h`,
with `τ = μ√(c/2π)`: `0 < τ_h`, `τ_h ≤ τ₀` (ORD) and `τ₀ ≤ 1` (Cvs.Prolate.RungMirrorIdentity). -/
theorem tau_le_tau_zero {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ₀ χ μ₀ μ : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ₀ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ * h s = 0)
    (heven' : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ₀ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ₀ * g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ * h s)
    (hground : (evenSpec (sqC c) ∩ Iio χ₀).ncard = 0) (hidx : Even (evenSpec (sqC c) ∩ Iio χ).ncard) :
    0 < μ * √(c / (2 * π)) ∧ μ * √(c / (2 * π)) ≤ μ₀ * √(c / (2 * π)) ∧ μ₀ * √(c / (2 * π)) ≤ 1 := by
  have hsq : 0 < √(c / (2 * π)) := Real.sqrt_pos.2 (by positivity)
  have hμpos := mu_pos_of_even_index hc hh hh₁ hh₂c hang' heven' hh0 hμ hidx
  have hμ₀pos := mu_pos_of_even_index hc hg hg₁ hg₂c hang heven hg0 hμ₀ (by rw [hground]; exact ⟨0, rfl⟩)
  have hχ : χ₀ ≤ χ := le_of_ncard_eq_zero hground χ (mem_evenSpec_of_angular hh hh₁ hang' heven' hh0)
  have hle := mu_sq_le hc hg hg₁ hg₂c hang heven hg0 hh hh₁ hh₂c hang' heven' hh0 hμ₀ hμ hχ
  have hμle : μ ≤ μ₀ := by nlinarith
  have hgc : ContinuousOn g (Icc (-1 : ℝ) 1) := continuousOn_of_hasDerivAt hg
  have h1 := Cvs.Prolate.RungMirrorIdentity.abs_tau_le_one hc hgc heven hμ₀ hg0
  exact ⟨mul_pos hμpos hsq, mul_le_mul_of_nonneg_right hμle hsq.le, (le_abs_self _).trans h1⟩

/-- **E3's step 5**: for `0 < τ ≤ τ₀ ≤ 1`, `(1 − τ/τ₀)² ≤ (1 − τ)² ≤ 1 − τ²`, and `τ² = λ` (Cvs.Prolate.RungMirrorIdentity). -/
theorem one_sub_div_sq_le {τ τ₀ : ℝ} (hτ : 0 < τ) (hle : τ ≤ τ₀) (h1 : τ₀ ≤ 1) :
    (1 - τ / τ₀) ^ 2 ≤ (1 - τ) ^ 2 ∧ (1 - τ) ^ 2 ≤ 1 - τ ^ 2 := by
  have hτ₀ : 0 < τ₀ := hτ.trans_le hle
  have hdiv : τ / τ₀ ≤ 1 := (div_le_one hτ₀).2 hle
  have hge : τ ≤ τ / τ₀ := by
    rw [le_div_iff₀ hτ₀]; nlinarith
  refine ⟨pow_le_pow_left₀ (by linarith) (by linarith) 2, by nlinarith⟩

/-- **E3's step 5 on the spectrum**: ground `g`, even-index `h`, `τ = μ√(c/2π)`: `(1 − τ_h/τ₀)² ≤ 1 − τ_h²`. -/
theorem one_sub_tau_div_sq_le {g g₁ g₂ h h₁ h₂ : ℝ → ℝ} {c χ₀ χ μ₀ μ : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ₀ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hh : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h (h₁ s) s) (hh₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt h₁ (h₂ s) s)
    (hh₂c : ContinuousOn h₂ (uIcc (-1) 1))
    (hang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * h₂ s - 2 * s * h₁ s - c ^ 2 * s ^ 2 * h s + χ * h s = 0)
    (heven' : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (hh0 : ∃ s ∈ Icc (-1 : ℝ) 1, h s ≠ 0)
    (hμ₀ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ₀ * g s) (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c h s = μ * h s)
    (hground : (evenSpec (sqC c) ∩ Iio χ₀).ncard = 0) (hidx : Even (evenSpec (sqC c) ∩ Iio χ).ncard) :
    (1 - μ * √(c / (2 * π)) / (μ₀ * √(c / (2 * π)))) ^ 2 ≤ 1 - (μ * √(c / (2 * π))) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := tau_le_tau_zero hc hg hg₁ hg₂c hang heven hg0 hh hh₁ hh₂c hang' heven' hh0 hμ₀ hμ
    hground hidx
  obtain ⟨e1, e2⟩ := one_sub_div_sq_le h1 h2 h3
  exact e1.trans e2

end Cvs.Prolate.SlepianEvenOrdering
