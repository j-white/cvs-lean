import Mathlib
import Cvs.Prolate.CorrectedEnergyPairAngular
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy
import Cvs.Prolate.PlungeLawIntegral
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The angular virial and the angular form of `K`

On `[0, t₁]` in the angular zone `c²t² < χ`, with `u(0) = 0` and `0 < R ≤ R(w t₁)`, `SturmLiouvilleMassEnergy`'s L² identity and `CorrectedEnergyPairAngular`'s
transport give `∫₀^{t₁} ψ² ≥ (R E/2)(∫₀^{t₁} 1/a − (1 + R)/(2R²(χ − c²t₁²)))`, `E = E(t₁)`. For `χ = c²a²` the
substitution `ξ = a/s` gives `K = c∫₀^a 1/a`, and the window `[a − h, a]` carries at most `2√h/(√(1 − a²)√(2a − h))`.
-/

namespace Cvs.Prolate.AngularVirial

open Real Set Filter Topology MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Prolate.PlungeLawIntegral Cvs.Prolate.CorrectedEnergyPairAngular

/-- `u(0) = 0` for the rung: the kernel `−c s sin(c·0·s)` vanishes. -/
theorem rungU_zero (c : ℝ) (g : ℝ → ℝ) : rungU c g 0 = 0 := by
  simp [rungU, kint]

/-- **The angular virial**: on `[0, t₁]` with `c²t₁² < χ < c²`, `u(0) = 0` and `0 < R ≤ R(w t₁)`,
`∫₀^{t₁} ψ² ≥ (R E/2)(∫₀^{t₁} 1/a − (1 + R)/(2R²(χ − c²t₁²)))`, `E` the energy at `t₁`. -/
theorem angular_virial {ψ u : ℝ → ℝ} {c χ t₁ R : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (ht₁ : 0 ≤ t₁)
    (ht₁χ : c ^ 2 * t₁ ^ 2 < χ)
    (hψ : ∀ t ∈ Icc 0 t₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc 0 t₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hu0 : u 0 = 0)
    (hw2 : wP c χ t₁ < 2) (hR0 : 0 < R) (hR : R ≤ Rcorr (wP c χ t₁)) :
    R * energy (aP c χ) ψ u t₁ / 2
        * ((∫ t in (0 : ℝ)..t₁, 1 / aP c χ t) - (1 + R) / (2 * R ^ 2 * (χ - c ^ 2 * t₁ ^ 2)))
      ≤ ∫ t in (0 : ℝ)..t₁, ψ t ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hχ0 : 0 < χ := by nlinarith [sq_nonneg t₁]
  have hq : ∀ t ∈ Icc 0 t₁, qP c χ t < 0 := fun t ht => by
    have h1 : t ^ 2 ≤ t₁ ^ 2 := pow_le_pow_left₀ ht.1 ht.2 2
    unfold qP; nlinarith
  have hp : ∀ t ∈ Icc 0 t₁, pP t < 0 := fun t ht => by
    have h1 : t ^ 2 ≤ t₁ ^ 2 := pow_le_pow_left₀ ht.1 ht.2 2
    have h2 : c ^ 2 * t ^ 2 < c ^ 2 * 1 := by nlinarith
    have h3 : t ^ 2 < 1 := lt_of_mul_lt_mul_left h2 hc2.le
    unfold pP; linarith
  have ha : ∀ t ∈ Icc 0 t₁, 0 < aP c χ t := fun t ht => aP_pos_of_neg (hp t ht) (hq t ht)
  have hmem : t₁ ∈ Icc 0 t₁ := right_mem_Icc.mpr ht₁
  have hmem0 : (0 : ℝ) ∈ Icc 0 t₁ := left_mem_Icc.mpr ht₁
  obtain ⟨E₁, hE₁⟩ : ∃ E, E = energy (aP c χ) ψ u t₁ := ⟨_, rfl⟩
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q, Q = χ - c ^ 2 * t₁ ^ 2 := ⟨_, rfl⟩
  rw [← hE₁, ← hQ₁]
  have hQ : 0 < Q₁ := by rw [hQ₁]; linarith
  have hE0 : 0 ≤ E₁ := by
    have := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t₁ hmem)
    have := abs_nonneg (ψ t₁ * u t₁)
    rw [← hE₁] at *; linarith
  -- the transport bounds
  have htr : ∀ t ∈ Icc 0 t₁, R * E₁ ≤ energy (aP c χ) ψ u t ∧ R * energy (aP c χ) ψ u t ≤ E₁ := by
    intro t ht
    have hsub : Icc t t₁ ⊆ Icc 0 t₁ := Icc_subset_Icc_left ht.1
    have tr := angular_transport hc hχc ht.1 ht.2 ht₁χ (fun s hs => hψ s (hsub hs))
      (fun s hs => hu s (hsub hs)) hw2
    rw [← hE₁] at tr
    have hEt : 0 ≤ energy (aP c χ) ψ u t := by
      have := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht)
      have := abs_nonneg (ψ t * u t)
      linarith
    exact ⟨le_trans (mul_le_mul_of_nonneg_right hR hE0) tr.1,
      le_trans (mul_le_mul_of_nonneg_right hR hEt) tr.2⟩
  -- the L² identity
  have hqd : ∀ t ∈ Icc 0 t₁, HasDerivAt (qP c χ) (2 * c ^ 2 * t) t := fun t _ => by
    have h := ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).sub_const χ
    exact h.congr_deriv (by ring)
  have hac' : Continuous (aP c χ) := by unfold aP pP qP; fun_prop
  have hqc' : Continuous (qP c χ) := by unfold qP; fun_prop
  have hac : ContinuousOn (aP c χ) (Icc 0 t₁) := hac'.continuousOn
  have hqc : ContinuousOn (qP c χ) (Icc 0 t₁) := hqc'.continuousOn
  have hpc : ContinuousOn pP (Icc 0 t₁) := by unfold pP; fun_prop
  have hψc : ContinuousOn ψ (Icc 0 t₁) := fun t ht => (hψ t ht).continuousAt.continuousWithinAt
  have huc : ContinuousOn u (Icc 0 t₁) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hid := Cvs.Prolate.LiouvilleGreen.SturmLiouvilleMassEnergy.integral_sq_eq (q' := fun t => 2 * c ^ 2 * t) ht₁ ha
    (fun t ht => (hp t ht).ne) (fun t ht => (hq t ht).ne)
    (fun t ht => aP_sq_of_neg (hp t ht) (hq t ht)) hψ hu hqd (by fun_prop) hac hpc
  rw [hu0, mul_zero, zero_div, zero_div, add_zero] at hid
  -- the pointwise lower bound
  have hpt : ∀ t ∈ Icc 0 t₁, R * E₁ / 2 * (1 / aP c χ t) - E₁ / (4 * R) * (2 * c ^ 2 * t / qP c χ t ^ 2)
      ≤ energy (aP c χ) ψ u t / (2 * aP c χ t) - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2) := by
    intro t ht
    have hat := ha t ht
    have hqt := (hq t ht).ne
    obtain ⟨hlo, hhi⟩ := htr t ht
    have h1 : R * E₁ / 2 * (1 / aP c χ t) ≤ energy (aP c χ) ψ u t / (2 * aP c χ t) := by
      rw [show R * E₁ / 2 * (1 / aP c χ t) = R * E₁ / (2 * aP c χ t) by field_simp]
      exact div_le_div_of_nonneg_right hlo (by positivity)
    have hk : 0 ≤ 2 * c ^ 2 * t / qP c χ t ^ 2 :=
      div_nonneg (by have := ht.1; positivity) (sq_nonneg _)
    have hψu : ψ t * u t ≤ E₁ / (2 * R) := by
      rw [le_div_iff₀ (by positivity)]
      have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) hat
      have := mul_le_mul_of_nonneg_right (le_abs_self (ψ t * u t)) (by positivity : (0 : ℝ) ≤ 2 * R)
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right hψu hk
    have e1 : ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)
        = ψ t * u t * (2 * c ^ 2 * t / qP c χ t ^ 2) / 2 := by ring
    have e2 : E₁ / (4 * R) * (2 * c ^ 2 * t / qP c χ t ^ 2)
        = E₁ / (2 * R) * (2 * c ^ 2 * t / qP c χ t ^ 2) / 2 := by ring
    rw [e1, e2]
    linarith
  -- integrability
  have hF : ContinuousOn (fun t => energy (aP c χ) ψ u t / (2 * aP c χ t)
      - ψ t * u t * (2 * c ^ 2 * t) / (2 * qP c χ t ^ 2)) (Icc 0 t₁) := by
    unfold energy
    refine ContinuousOn.sub ?_ ?_
    · have h2a : ContinuousOn (fun t => 2 * aP c χ t) (Icc 0 t₁) := continuousOn_const.mul hac
      have hnum : ContinuousOn (fun t => aP c χ t * ψ t ^ 2 + u t ^ 2 / aP c χ t) (Icc 0 t₁) :=
        (hac.mul (hψc.pow 2)).add ((huc.pow 2).div₀ hac fun t ht => (ha t ht).ne')
      exact hnum.div₀ h2a fun t ht => (mul_pos two_pos (ha t ht)).ne'
    · have hlin : ContinuousOn (fun t : ℝ => 2 * c ^ 2 * t) (Icc 0 t₁) := by fun_prop
      have hden : ContinuousOn (fun t => 2 * qP c χ t ^ 2) (Icc 0 t₁) :=
        continuousOn_const.mul (hqc.pow 2)
      have hnum : ContinuousOn (fun t => ψ t * u t * (2 * c ^ 2 * t)) (Icc 0 t₁) :=
        (hψc.mul huc).mul hlin
      exact hnum.div₀ hden fun t ht =>
        mul_ne_zero two_ne_zero (pow_ne_zero 2 (hq t ht).ne)
  have hainv : ContinuousOn (fun t => 1 / aP c χ t) (Icc 0 t₁) :=
    continuousOn_const.div hac fun t ht => (ha t ht).ne'
  have hqq' : ContinuousOn (fun t => 2 * c ^ 2 * t / qP c χ t ^ 2) (Icc 0 t₁) :=
    (continuousOn_const.mul continuousOn_id).div₀ (hqc.pow 2) fun t ht =>
      pow_ne_zero 2 (hq t ht).ne
  have iA := hainv.intervalIntegrable_of_Icc (μ := volume) ht₁
  have iQ := hqq'.intervalIntegrable_of_Icc (μ := volume) ht₁
  have iF := hF.intervalIntegrable_of_Icc (μ := volume) ht₁
  have iU := integral_mono_on ht₁ ((iA.const_mul (R * E₁ / 2)).sub (iQ.const_mul (E₁ / (4 * R)))) iF hpt
  rw [intervalIntegral.integral_sub (iA.const_mul _) (iQ.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at iU
  -- `∫₀^{t₁} q'/q² = 1/q(0) − 1/q(t₁) ≤ 1/(χ − c²t₁²)`
  have hI : uIcc 0 t₁ = Icc 0 t₁ := uIcc_of_le ht₁
  have hqq : ∫ t in (0 : ℝ)..t₁, 2 * c ^ 2 * t / qP c χ t ^ 2 = 1 / qP c χ 0 - 1 / qP c χ t₁ := by
    have hd : ∀ t ∈ uIcc 0 t₁, HasDerivAt (fun s => -(1 / qP c χ s))
        (2 * c ^ 2 * t / qP c χ t ^ 2) t := fun t ht => by
      have := ((hqd t (hI ▸ ht)).inv (hq t (hI ▸ ht)).ne).neg
      refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with s; simp [one_div]
    rw [integral_eq_sub_of_hasDerivAt hd iQ]
    ring
  have hq0 : qP c χ 0 = -χ := by unfold qP; ring
  have hqt₁ : qP c χ t₁ = -Q₁ := by unfold qP; rw [hQ₁]; ring
  have hqq_le : ∫ t in (0 : ℝ)..t₁, 2 * c ^ 2 * t / qP c χ t ^ 2 ≤ 1 / Q₁ := by
    rw [hqq, hq0, hqt₁]
    have : 0 < 1 / χ := by positivity
    rw [div_neg, div_neg]; linarith
  have hQq := mul_le_mul_of_nonneg_left hqq_le (by positivity : (0 : ℝ) ≤ E₁ / (4 * R))
  -- the boundary term at `t₁`
  have hbd : -(E₁ / (4 * Q₁)) ≤ -(ψ t₁ * u t₁ / qP c χ t₁ / 2) := by
    have e : -(ψ t₁ * u t₁ / qP c χ t₁ / 2) = ψ t₁ * u t₁ / (2 * Q₁) := by
      rw [hqt₁]; field_simp
    have e2 : -(E₁ / (4 * Q₁)) = -(E₁ / 2) / (2 * Q₁) := by ring
    rw [e, e2]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hG := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t₁ hmem)
    rw [← hE₁] at hG
    have := neg_abs_le (ψ t₁ * u t₁)
    linarith
  have halg : R * E₁ / 2 * ((∫ t in (0 : ℝ)..t₁, 1 / aP c χ t) - (1 + R) / (2 * R ^ 2 * Q₁))
      = R * E₁ / 2 * (∫ t in (0 : ℝ)..t₁, 1 / aP c χ t) - E₁ / (4 * R) * (1 / Q₁) - E₁ / (4 * Q₁) := by
    field_simp; ring
  rw [halg, hid]
  linarith

/-- **The inversion `s ↦ a/s`** for `χ = c²a²`: `a(a/s) = (a/s²) a(s)` on `(0, a)`. -/
theorem aP_div_eq {c χ a s : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) (hχ : χ = c ^ 2 * a ^ 2)
    (hs : s ∈ Ioo 0 a) : aP c χ (a / s) = a / s ^ 2 * aP c χ s := by
  obtain ⟨hs0, hsa⟩ := hs
  have hs0' : s ≠ 0 := hs0.ne'
  have hA : 0 ≤ a ^ 2 - s ^ 2 := by nlinarith
  have hB : 0 ≤ 1 - s ^ 2 := by nlinarith
  have h1 : aP c χ s = c * √((a ^ 2 - s ^ 2) * (1 - s ^ 2)) := by
    unfold aP pP qP
    rw [hχ, show (s ^ 2 - 1) * (c ^ 2 * s ^ 2 - c ^ 2 * a ^ 2) = c ^ 2 * ((a ^ 2 - s ^ 2) * (1 - s ^ 2)) by ring,
      sqrt_mul (sq_nonneg c), sqrt_sq hc.le]
  have h2 : aP c χ (a / s) = c * a / s ^ 2 * √((a ^ 2 - s ^ 2) * (1 - s ^ 2)) := by
    unfold aP pP qP
    rw [hχ, show ((a / s) ^ 2 - 1) * (c ^ 2 * (a / s) ^ 2 - c ^ 2 * a ^ 2)
        = (c * a / s ^ 2) ^ 2 * ((a ^ 2 - s ^ 2) * (1 - s ^ 2)) by field_simp,
      sqrt_mul (sq_nonneg _), sqrt_sq (by positivity)]
  rw [h1, h2]; ring

/-- `s ↦ a/s` maps `(0, a)` onto `(1, ∞)`. -/
theorem image_div_Ioo {a : ℝ} (ha : 0 < a) : (fun s => a / s) '' Ioo 0 a = Ioi 1 := by
  ext ξ
  constructor
  · rintro ⟨s, ⟨hs0, hsa⟩, rfl⟩
    exact (one_lt_div hs0).mpr hsa
  · intro hξ
    have hξ0 : 0 < ξ := lt_trans one_pos hξ
    refine ⟨a / ξ, ⟨div_pos ha hξ0, div_lt_self ha hξ⟩, ?_⟩
    have := hξ0.ne'
    have := ha.ne'
    field_simp

/-- **The angular form of `∫₁^∞ 1/a`**: for `χ = c²a²`, `∫_{(0,a)} 1/a = ∫_{(1,∞)} 1/a` by `ξ = a/s`. -/
theorem integral_inv_aP_angular {c χ a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) (hχ : χ = c ^ 2 * a ^ 2) :
    ∫ s in Ioo 0 a, 1 / aP c χ s = ∫ ξ in Ioi 1, 1 / aP c χ ξ := by
  have hd : ∀ s ∈ Ioo 0 a, HasDerivWithinAt (fun s => a / s) (-(a / s ^ 2)) (Ioo 0 a) s := fun s hs => by
    have h := (hasDerivAt_inv hs.1.ne').const_mul a
    refine HasDerivAt.hasDerivWithinAt ?_
    simpa only [div_eq_mul_inv, mul_neg] using h
  have hinj : InjOn (fun s => a / s) (Ioo 0 a) := fun x hx y hy hxy =>
    (mul_left_cancel₀ ha.ne' ((div_eq_div_iff hx.1.ne' hy.1.ne').mp hxy)).symm
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj (fun ξ => 1 / aP c χ ξ)
  rw [image_div_Ioo ha] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  have hp : pP s < 0 := by unfold pP; nlinarith [hs.1, hs.2]
  have hq : qP c χ s < 0 := by
    have hsa2 : s ^ 2 < a ^ 2 := by nlinarith [hs.1, hs.2]
    have := mul_lt_mul_of_pos_left hsa2 (sq_pos_of_pos hc)
    unfold qP; rw [hχ]; linarith
  have haP := aP_pos_of_neg hp hq
  have hs0 := hs.1
  simp only [smul_eq_mul]
  rw [aP_div_eq hc ha ha1 hχ hs, abs_neg, abs_of_pos (by positivity)]
  field_simp

/-- `1/a` is integrable on `(0, a)` for `χ = c²a²`, by the substitution `ξ = a/s` and Cvs.Prolate.PlungeLawIntegral. -/
theorem integrableOn_inv_aP_angular {c χ a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1)
    (hχ : χ = c ^ 2 * a ^ 2) : IntegrableOn (fun s => 1 / aP c χ s) (Ioo 0 a) := by
  have hd : ∀ s ∈ Ioo 0 a, HasDerivWithinAt (fun s => a / s) (-(a / s ^ 2)) (Ioo 0 a) s := fun s hs => by
    have h := (hasDerivAt_inv hs.1.ne').const_mul a
    refine HasDerivAt.hasDerivWithinAt ?_
    simpa only [div_eq_mul_inv, mul_neg] using h
  have hinj : InjOn (fun s => a / s) (Ioo 0 a) := fun x hx y hy hxy =>
    (mul_left_cancel₀ ha.ne' ((div_eq_div_iff hx.1.ne' hy.1.ne').mp hxy)).symm
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj
    (fun ξ => 1 / aP c χ ξ)
  rw [image_div_Ioo ha] at hiff
  have hc2 : 0 < c ^ 2 := by positivity
  have ha2 : a ^ 2 < 1 := by nlinarith
  have hI := hiff.mp (integrableOn_inv_aP hc (by rw [hχ]; positivity)
    (by rw [hχ]; exact mul_lt_of_lt_one_right hc2 ha2))
  refine hI.congr_fun (fun s hs => ?_) measurableSet_Ioo
  have hp : pP s < 0 := by unfold pP; nlinarith [hs.1, hs.2]
  have hq : qP c χ s < 0 := by
    have hsa2 : s ^ 2 < a ^ 2 := by nlinarith [hs.1, hs.2]
    have := mul_lt_mul_of_pos_left hsa2 (sq_pos_of_pos hc)
    unfold qP; rw [hχ]; linarith
  have haP := aP_pos_of_neg hp hq
  have hs0 := hs.1
  simp only [smul_eq_mul]
  rw [aP_div_eq hc ha ha1 hχ hs, abs_neg, abs_of_pos (by positivity)]
  field_simp

/-- **`K` in angular time**: for `χ = c²a²`, `K = c∫₀^a ds/a(s)`. -/
theorem ellK_eq_angular {c χ a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) (hχ : χ = c ^ 2 * a ^ 2) :
    ellK c χ = c * ∫ s in (0 : ℝ)..a, 1 / aP c χ s := by
  unfold ellK
  rw [← integral_inv_aP_angular hc ha ha1 hχ, intervalIntegral.integral_of_le ha.le,
    integral_Ioc_eq_integral_Ioo]

/-- **The top window of `K`**: for `χ = c²a²` and `0 < h ≤ a`,
`c∫_{a−h}^a ds/a(s) ≤ 2√h/(√(1 − a²)√(2a − h))`, from `a(s) ≥ c√(1 − a²)√(2a − h)√(a − s)`. -/
theorem inv_aP_top_le {c χ a h : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) (hχ : χ = c ^ 2 * a ^ 2)
    (hh : 0 < h) (hha : h ≤ a) :
    c * ∫ s in (a - h)..a, 1 / aP c χ s ≤ 2 * √h / (√(1 - a ^ 2) * √(2 * a - h)) := by
  have hah : 0 ≤ a - h := by linarith
  have hle : a - h ≤ a := by linarith
  have h2a : 0 < 2 * a - h := by linarith
  have hA1 : 0 < 1 - a ^ 2 := by nlinarith
  have hpt : ∀ s ∈ Ioo (a - h) a,
      1 / aP c χ s ≤ 1 / (c * √(1 - a ^ 2) * √(2 * a - h)) * (1 / √(a - s)) := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hah hs.1
    have hsa : s < a := hs.2
    have hA : 0 ≤ a ^ 2 - s ^ 2 := by nlinarith
    have hform : aP c χ s = c * √(a ^ 2 - s ^ 2) * √(1 - s ^ 2) := by
      unfold aP pP qP
      rw [hχ, show (s ^ 2 - 1) * (c ^ 2 * s ^ 2 - c ^ 2 * a ^ 2) = c ^ 2 * (a ^ 2 - s ^ 2) * (1 - s ^ 2) by ring,
        sqrt_mul (mul_nonneg (sq_nonneg c) hA), sqrt_mul (sq_nonneg c), sqrt_sq hc.le]
    have hlow : c * √(1 - a ^ 2) * √(2 * a - h) * √(a - s) ≤ aP c χ s := by
      rw [hform]
      have e1 : √(1 - a ^ 2) ≤ √(1 - s ^ 2) := sqrt_le_sqrt (by nlinarith)
      have e2 : √(2 * a - h) * √(a - s) ≤ √(a ^ 2 - s ^ 2) := by
        rw [← sqrt_mul h2a.le]
        exact sqrt_le_sqrt (by nlinarith [mul_nonneg (sub_nonneg.mpr hsa.le) (by linarith [hs.1] : (0 : ℝ) ≤ s - (a - h))])
      calc c * √(1 - a ^ 2) * √(2 * a - h) * √(a - s)
          = c * √(1 - a ^ 2) * (√(2 * a - h) * √(a - s)) := by ring
        _ ≤ c * √(1 - s ^ 2) * √(a ^ 2 - s ^ 2) := by gcongr
        _ = c * √(a ^ 2 - s ^ 2) * √(1 - s ^ 2) := by ring
    have hpos : 0 < c * √(1 - a ^ 2) * √(2 * a - h) * √(a - s) := by
      have : 0 < a - s := by linarith
      positivity
    calc 1 / aP c χ s ≤ 1 / (c * √(1 - a ^ 2) * √(2 * a - h) * √(a - s)) :=
          one_div_le_one_div_of_le hpos hlow
      _ = _ := by rw [one_div_mul_one_div]
  -- `∫_{a−h}^a 1/√(a − s) = 2√h`
  have hF : ∀ s ∈ Ioo (a - h) a, HasDerivAt (fun s => -2 * √(a - s)) (1 / √(a - s)) s := fun s hs => by
    have hpos : 0 < a - s := by linarith [hs.2]
    have hspos : 0 < √(a - s) := sqrt_pos.mpr hpos
    have := (((hasDerivAt_id' s).const_sub a).sqrt hpos.ne').const_mul (-2)
    refine this.congr_deriv ?_
    field_simp
  have hFc : ContinuousOn (fun s => -2 * √(a - s)) (Icc (a - h) a) :=
    (continuous_const.mul (continuous_const.sub continuous_id).sqrt).continuousOn
  have hint : IntervalIntegrable (fun s => 1 / √(a - s)) volume (a - h) a := by
    refine intervalIntegrable_deriv_of_nonneg (g := fun s => -2 * √(a - s)) ?_ ?_ ?_
    · rw [uIcc_of_le hle]; exact hFc
    · rw [min_eq_left hle, max_eq_right hle]; exact hF
    · rw [min_eq_left hle, max_eq_right hle]
      exact fun s _ => div_nonneg zero_le_one (sqrt_nonneg _)
  have hval : ∫ s in (a - h)..a, 1 / √(a - s) = 2 * √h := by
    rw [integral_eq_sub_of_hasDerivAt_of_le hle hFc hF hint]
    simp
  -- integrability of `1/a`
  have hIA : IntervalIntegrable (fun s => 1 / aP c χ s) volume (a - h) a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    have := (integrableOn_Ioc_iff_integrableOn_Ioo).mpr (integrableOn_inv_aP_angular hc ha ha1 hχ)
    exact this.mono_set (Ioc_subset_Ioc_left hah)
  have hmono := integral_mono_on_of_le_Ioo hle hIA (hint.const_mul _) hpt
  rw [intervalIntegral.integral_const_mul, hval] at hmono
  have hsA := sqrt_pos.mpr hA1
  have hs2 := sqrt_pos.mpr h2a
  calc c * ∫ s in (a - h)..a, 1 / aP c χ s
      ≤ c * (1 / (c * √(1 - a ^ 2) * √(2 * a - h)) * (2 * √h)) := mul_le_mul_of_nonneg_left hmono hc.le
    _ = 2 * √h / (√(1 - a ^ 2) * √(2 * a - h)) := by field_simp

/-- **`K` minus its top window**: for `χ = c²a²` and `0 < h ≤ a`,
`K − 2√h/(√(1 − a²)√(2a − h)) ≤ c∫₀^{a−h} ds/a(s)`. -/
theorem ellK_sub_le {c χ a h : ℝ} (hc : 0 < c) (ha : 0 < a) (ha1 : a < 1) (hχ : χ = c ^ 2 * a ^ 2)
    (hh : 0 < h) (hha : h ≤ a) :
    ellK c χ - 2 * √h / (√(1 - a ^ 2) * √(2 * a - h)) ≤ c * ∫ s in (0 : ℝ)..(a - h), 1 / aP c χ s := by
  have hah : 0 ≤ a - h := by linarith
  have hle : a - h ≤ a := by linarith
  have hIoc : IntegrableOn (fun s => 1 / aP c χ s) (Ioc 0 a) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).mpr (integrableOn_inv_aP_angular hc ha ha1 hχ)
  have hI1 : IntervalIntegrable (fun s => 1 / aP c χ s) volume 0 (a - h) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hah).mpr (hIoc.mono_set (Ioc_subset_Ioc_right hle))
  have hI2 : IntervalIntegrable (fun s => 1 / aP c χ s) volume (a - h) a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr (hIoc.mono_set (Ioc_subset_Ioc_left hah))
  rw [ellK_eq_angular hc ha ha1 hχ, ← integral_add_adjacent_intervals hI1 hI2, mul_add]
  linarith [inv_aP_top_le hc ha ha1 hχ hh hha]

end Cvs.Prolate.AngularVirial
