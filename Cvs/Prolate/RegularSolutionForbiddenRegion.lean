import Mathlib
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RegularSolutionEnergyComparability
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The regular solution in the forbidden region: `y ≥ 1`, `0 ≤ U ≤ (c/2)y` and the Agmon bound

On `[τ, 1]`, `c²τ² ≥ σ ≥ 0`, `y² ≥ y(1)² = 1` and `U = ∫_t^1 (c²s² − σ)y ≥ 0`; the Riccati variable `v = −U/y` has
`v' = (pw − v²)/p`, `w = c²t² − σ`, so `v + c/2` and, where `c⁴ ≤ ε²w³`, `v + (1 + ε)√(pw) + 1` stay nonnegative
(eq-cpb Lemmas 6(iii) and 9(i)).
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC hasDerivAt_regSol hasDerivAt_regU)

namespace Cvs.Prolate.RegularSolutionForbiddenRegion
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-! ### No return to zero -/

/-- **No return**: if `D` is continuous on `[α, β]`, differentiable on `[α, β)` with `D' < 0` wherever `D < 0`, and
`D(β) ≥ 0`, then `D ≥ 0` on `[α, β]`. -/
theorem nonneg_of_deriv_neg {D D' : ℝ → ℝ} {α β : ℝ} (hc : ContinuousOn D (Icc α β))
    (hd : ∀ t ∈ Ico α β, HasDerivAt D (D' t) t) (hneg : ∀ t ∈ Ico α β, D t < 0 → D' t < 0)
    (hβ : 0 ≤ D β) : ∀ t ∈ Icc α β, 0 ≤ D t := by
  intro t₀ ht₀
  by_contra hlt
  push Not at hlt
  have htβ : t₀ < β := lt_of_le_of_ne ht₀.2 fun h => by rw [h] at hlt; linarith
  set Z := {t ∈ Icc t₀ β | 0 ≤ D t} with hZ
  have hZc : IsClosed Z :=
    (hc.mono (Icc_subset_Icc ht₀.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hZne : Z.Nonempty := ⟨β, ⟨htβ.le, le_rfl⟩, hβ⟩
  have hZb : BddBelow Z := ⟨t₀, fun t ht => ht.1.1⟩
  set τ := sInf Z
  have hτZ : τ ∈ Z := hZc.csInf_mem hZne hZb
  have hτ0 : t₀ < τ := lt_of_le_of_ne hτZ.1.1 fun h => by have := hτZ.2; rw [← h] at this; linarith
  have hneg' : ∀ t ∈ Ico t₀ τ, D t < 0 := fun t ht => by
    by_contra h
    push Not at h
    exact absurd (csInf_le hZb ⟨⟨ht.1, ht.2.le.trans hτZ.1.2⟩, h⟩) (not_le.mpr ht.2)
  have hanti : AntitoneOn D (Icc t₀ τ) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := D') (convex_Icc t₀ τ)
      (hc.mono (Icc_subset_Icc ht₀.1 hτZ.1.2)) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t ⟨ht₀.1.trans ht.1.le, ht.2.trans_le hτZ.1.2⟩).hasDerivWithinAt
    · rw [interior_Icc] at ht
      exact (hneg t ⟨ht₀.1.trans ht.1.le, ht.2.trans_le hτZ.1.2⟩ (hneg' t ⟨ht.1.le, ht.2⟩)).le
  have := hanti ⟨le_rfl, hτ0.le⟩ ⟨hτ0.le, le_rfl⟩ hτ0.le
  linarith [hτZ.2]

/-! ### Sign and size in the forbidden region -/

/-- `y ≥ 1` on the forbidden region `[τ, 1]`, `0 ≤ τ`, `σ ≤ c²τ²`. -/
theorem one_le_forbidden {τ : ℝ} (hτ : 0 ≤ τ) (hτσ : σ ≤ c ^ 2 * τ ^ 2) :
    ∀ t ∈ Icc τ 1, 1 ≤ regSol (sqC c) σ t := by
  have hanti := Cvs.Prolate.RegularSolutionEnergyComparability.sq_anti_forbidden (c := c) (σ := σ) hτ hτσ
  have hsq : ∀ t ∈ Icc τ 1, 1 ≤ regSol (sqC c) σ t ^ 2 := fun t ht => by
    have := hanti ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2
    simpa [Cvs.Prolate.RegularSolutionEdge.regSol_one] using this
  intro t ht
  have hcont : ContinuousOn (regSol (sqC c) σ) (Icc t 1) :=
    (Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).mono fun s hs => show (-1 : ℝ) < s by linarith [hs.1, ht.1]
  by_contra hlt
  push Not at hlt
  have hneg : regSol (sqC c) σ t < 0 := by
    have := hsq t ht
    nlinarith [sq_nonneg (regSol (sqC c) σ t + 1)]
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht.2 hcont
    ⟨hneg.le, by rw [Cvs.Prolate.RegularSolutionEdge.regSol_one]; norm_num⟩
  have := hsq s ⟨ht.1.trans hs.1, hs.2⟩
  rw [hs0] at this; norm_num at this

/-- `U(t) = ∫_t^1 (c²s² − σ)y(s) ds`. -/
theorem regU_eq_integral (t : ℝ) :
    regU (sqC c) σ t = ∫ s in t..1, (c ^ 2 * s ^ 2 - σ) * regSol (sqC c) σ s := by
  unfold regU
  rw [intervalIntegral.integral_symm, neg_neg]
  rfl

/-- `U ≥ 0` on the forbidden region. -/
theorem regU_nonneg_forbidden {τ : ℝ} (hτ : 0 ≤ τ) (hτσ : σ ≤ c ^ 2 * τ ^ 2) {t : ℝ} (ht : t ∈ Icc τ 1) :
    0 ≤ regU (sqC c) σ t := by
  rw [regU_eq_integral]
  refine intervalIntegral.integral_nonneg ht.2 fun s hs => ?_
  have hy := one_le_forbidden hτ hτσ s ⟨ht.1.trans hs.1, hs.2⟩
  have : σ ≤ c ^ 2 * s ^ 2 := hτσ.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hτ (ht.1.trans hs.1) 2) (sq_nonneg c))
  exact mul_nonneg (by linarith) (by linarith)

/-! ### The Riccati variable -/

/-- On the forbidden region, `(−U/y)' = w − (U/y)²/p` with `w = c²t² − σ`, `p = 1 − t²`. -/
theorem hasDerivAt_ric {τ : ℝ} (hτ : 0 ≤ τ) (hτσ : σ ≤ c ^ 2 * τ ^ 2) {t : ℝ} (ht : t ∈ Ico τ 1) :
    HasDerivAt (fun t => -regU (sqC c) σ t / regSol (sqC c) σ t)
      ((c ^ 2 * t ^ 2 - σ) - (regU (sqC c) σ t / regSol (sqC c) σ t) ^ 2 / (1 - t ^ 2)) t := by
  have ht1 : -1 < t := by linarith [ht.1]
  have hy := one_le_forbidden hτ hτσ t ⟨ht.1, ht.2.le⟩
  have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have d := (hasDerivAt_regU (sqC c) σ ht1).neg.div (hasDerivAt_regSol (sqC c) σ ht1) (by linarith)
  refine d.congr_deriv ?_
  have hpd := Cvs.Prolate.RegularSolutionEnergyComparability.p_mul_deriv (c := c) (σ := σ) ht1
  have hv : Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t = -regU (sqC c) σ t / (1 - t ^ 2) := by
    rw [eq_div_iff hp.ne', mul_comm]; exact hpd
  rw [hv, Cvs.Prolate.TopRungDepthBound.sqC_apply]
  have : regSol (sqC c) σ t ≠ 0 := by linarith
  simp only [Pi.neg_apply]
  field_simp

/-- `(1 − t²)(c²t² − σ) ≤ c²/4` for `σ ≥ 0`, `t² ≤ 1`. -/
theorem pw_le {t : ℝ} (hσ : 0 ≤ σ) (ht : t ^ 2 ≤ 1) : (1 - t ^ 2) * (c ^ 2 * t ^ 2 - σ) ≤ c ^ 2 / 4 := by
  have h1 : (1 - t ^ 2) * (c ^ 2 * t ^ 2 - σ) ≤ (1 - t ^ 2) * (c ^ 2 * t ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith [sq_nonneg (2 * t ^ 2 - 1), sq_nonneg c, mul_nonneg (sq_nonneg c) (sq_nonneg (2 * t ^ 2 - 1))]

/-- **The crude Riccati bound** (eq-cpb Lemma 6(iii)): `U ≤ (c/2)y` on the forbidden region, `c ≥ 0`, `σ ≥ 0`. -/
theorem regU_le_half {τ : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hτσ : σ ≤ c ^ 2 * τ ^ 2) :
    ∀ t ∈ Icc τ 1, regU (sqC c) σ t ≤ c / 2 * regSol (sqC c) σ t := by
  have hcont : ContinuousOn (fun t => -regU (sqC c) σ t / regSol (sqC c) σ t + c / 2) (Icc τ 1) := by
    refine (ContinuousOn.div (f := fun t => -regU (sqC c) σ t) (g := fun t => regSol (sqC c) σ t) ?_ ?_ fun t ht => ?_).add continuousOn_const
    · exact (fun t ht => ((hasDerivAt_regU (sqC c) σ (by linarith [ht.1] : (-1 : ℝ) < t)).continuousAt.neg
        ).continuousWithinAt)
    · exact (Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).mono fun t ht => show (-1 : ℝ) < t by linarith [ht.1]
    · linarith [one_le_forbidden hτ hτσ t ht]
  have h := nonneg_of_deriv_neg hcont (fun t ht => (hasDerivAt_ric hτ hτσ ht).add_const (c / 2))
    (fun t ht hD => by
      have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have hpw := pw_le (c := c) hσ (show t ^ 2 ≤ 1 by nlinarith [ht.1, ht.2])
      set v := regU (sqC c) σ t / regSol (sqC c) σ t
      have hv : c / 2 < v := by
        have : -regU (sqC c) σ t / regSol (sqC c) σ t = -v := by rw [neg_div]
        linarith
      have hv2 : c ^ 2 / 4 < v ^ 2 := by nlinarith
      have : (c ^ 2 * t ^ 2 - σ) - v ^ 2 / (1 - t ^ 2) < 0 := by
        rw [sub_neg, lt_div_iff₀ hp]; nlinarith
      exact this)
    (by simp only [regU, intervalIntegral.integral_same, neg_zero, zero_div]; linarith)
  intro t ht
  have hD := h t ht
  have hy := one_le_forbidden hτ hτσ t ht
  have e : (-regU (sqC c) σ t / regSol (sqC c) σ t + c / 2) * regSol (sqC c) σ t =
      -regU (sqC c) σ t + c / 2 * regSol (sqC c) σ t := by
    have : regSol (sqC c) σ t ≠ 0 := by linarith
    field_simp
  nlinarith [mul_nonneg hD (show 0 ≤ regSol (sqC c) σ t by linarith)]

/-- The algebra of the Agmon step: with `F² = PW`, `c⁴ ≤ ε²W³` and `V > (1 + ε)F + 1`, the Riccati drift
`(W − V²/P) + (1 + ε)(−2tW + 2c²tP)/(2F)` is negative. -/
theorem agmon_alg {P W F V ε c t : ℝ} (hp : 0 < P) (hp1 : P ≤ 1) (hW0 : 0 < W) (hF2 : F ^ 2 = P * W)
    (hF0 : 0 < F) (hε : 0 < ε) (hε1 : ε ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hw : c ^ 4 ≤ ε ^ 2 * W ^ 3)
    (hV : (1 + ε) * F + 1 < V) :
    (W - V ^ 2 / P) + (1 + ε) * ((-(2 * t) * W + P * (c ^ 2 * (2 * t))) / (2 * F)) < 0 := by
  have ha : (1 + ε) * ((-(2 * t) * W + P * (c ^ 2 * (2 * t))) / (2 * F)) ≤ (1 + ε) * (c ^ 2 * P / F) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [div_le_div_iff₀ (by positivity) hF0]
    have : (-(2 * t) * W + P * (c ^ 2 * (2 * t))) ≤ 2 * (c ^ 2 * P) := by
      nlinarith [mul_nonneg ht0 hW0.le, mul_nonneg (mul_nonneg (sq_nonneg c) hp.le) (sub_nonneg.mpr ht1)]
    nlinarith
  have hb : (1 + 2 * ε) * (P * W) + 1 < V ^ 2 := by
    have h0 : 0 ≤ (1 + ε) * F + 1 := by positivity
    have h1 : ((1 + ε) * F + 1) ^ 2 < V ^ 2 := by nlinarith
    nlinarith [sq_nonneg ε, hF0.le]
  have hc' : W - V ^ 2 / P < -(2 * ε * W) - 1 / P := by
    have h1 : ((1 + 2 * ε) * (P * W) + 1) / P < V ^ 2 / P := div_lt_div_of_pos_right hb hp
    have e : ((1 + 2 * ε) * (P * W) + 1) / P = (1 + 2 * ε) * W + 1 / P := by field_simp
    linarith
  have hd : (1 + ε) * (c ^ 2 * P / F) ≤ 2 * ε * W := by
    rw [mul_div_assoc', div_le_iff₀ hF0]
    have hsq : ((1 + ε) * (c ^ 2 * P)) ^ 2 ≤ (2 * ε * W * F) ^ 2 := by
      have e1 : (2 * ε * W * F) ^ 2 = 4 * ε ^ 2 * W ^ 3 * P := by rw [mul_pow, hF2]; ring
      have h4 : (1 + ε) ^ 2 ≤ 4 := by nlinarith
      have h5 : P ^ 2 ≤ P := by nlinarith
      have hc4 : 0 ≤ c ^ 4 := by positivity
      rw [e1]
      have i1 : (1 + ε) ^ 2 * c ^ 4 * P ^ 2 ≤ 4 * c ^ 4 * P := by
        have := mul_le_mul h4 (mul_le_mul_of_nonneg_left h5 hc4) (by positivity) (by norm_num)
        nlinarith
      have i2 : 4 * c ^ 4 * P ≤ 4 * (ε ^ 2 * W ^ 3) * P := by
        have := mul_le_mul_of_nonneg_right hw hp.le; nlinarith
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have : 0 < 1 / P := by positivity
  linarith

/-- **The Agmon bound** (eq-cpb Lemma 9(i)): on `[t₀, 1]`, `t₀ ≥ 0`, if `c⁴ ≤ ε²w(t₀)³` with `w = c²t² − σ` and
`0 < ε ≤ 1`, then `U ≤ ((1 + ε)√(pw) + 1)y`. -/
theorem regU_le_agmon {t₀ ε : ℝ} (hc : 0 < c) (hτ' : 0 ≤ t₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hw : c ^ 4 ≤ ε ^ 2 * (c ^ 2 * t₀ ^ 2 - σ) ^ 3) :
    ∀ t ∈ Icc t₀ 1, regU (sqC c) σ t ≤
      ((1 + ε) * √((1 - t ^ 2) * (c ^ 2 * t ^ 2 - σ)) + 1) * regSol (sqC c) σ t := by
  have hw0 : 0 < c ^ 2 * t₀ ^ 2 - σ := by
    by_contra h
    push Not at h
    have h3 : (c ^ 2 * t₀ ^ 2 - σ) ^ 3 ≤ 0 := by
      have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ -(c ^ 2 * t₀ ^ 2 - σ)) (le_refl _) 3
      nlinarith [sq_nonneg (c ^ 2 * t₀ ^ 2 - σ)]
    have : 0 < c ^ 4 := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ε) h3]
  have hτσ' : σ ≤ c ^ 2 * t₀ ^ 2 := by linarith
  set φ : ℝ → ℝ := fun t => √((1 - t ^ 2) * (c ^ 2 * t ^ 2 - σ)) with hφ
  have hcont : ContinuousOn (fun t => -regU (sqC c) σ t / regSol (sqC c) σ t + ((1 + ε) * φ t + 1))
      (Icc t₀ 1) := by
    refine (ContinuousOn.div (f := fun t => -regU (sqC c) σ t) (g := fun t => regSol (sqC c) σ t) ?_ ?_ fun t ht => ?_).add (by fun_prop)
    · exact (fun t ht => ((hasDerivAt_regU (sqC c) σ (by linarith [ht.1] : (-1 : ℝ) < t)).continuousAt.neg
        ).continuousWithinAt)
    · exact (Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).mono fun t ht => show (-1 : ℝ) < t by linarith [ht.1]
    · linarith [one_le_forbidden hτ' hτσ' t ht]
  have hwt : ∀ t ∈ Ico t₀ 1, c ^ 2 * t₀ ^ 2 - σ ≤ c ^ 2 * t ^ 2 - σ := fun t ht => by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ' ht.1 2) (sq_nonneg c)]
  have hderφ : ∀ t ∈ Ico t₀ 1, HasDerivAt φ ((-(2 * t) * (c ^ 2 * t ^ 2 - σ) + (1 - t ^ 2) * (c ^ 2 * (2 * t))) /
      (2 * φ t)) t := by
    intro t ht
    have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hpw : 0 < (1 - t ^ 2) * (c ^ 2 * t ^ 2 - σ) := mul_pos hp (lt_of_lt_of_le hw0 (hwt t ht))
    have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_sub 1)
    have h2 : HasDerivAt (fun t : ℝ => c ^ 2 * t ^ 2 - σ) (c ^ 2 * (2 * t)) t := by
      simpa using (((hasDerivAt_pow 2 t).const_mul (c ^ 2)).sub_const σ)
    exact (h1.mul h2).sqrt hpw.ne'
  have h := nonneg_of_deriv_neg hcont
    (fun t ht => ((hasDerivAt_ric hτ' hτσ' ⟨ht.1, ht.2⟩).add (((hderφ t ht).const_mul (1 + ε)).add_const 1)))
    (fun t ht hD => by
      have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have hW0 : 0 < c ^ 2 * t ^ 2 - σ := lt_of_lt_of_le hw0 (hwt t ht)
      have hF2 : φ t ^ 2 = (1 - t ^ 2) * (c ^ 2 * t ^ 2 - σ) := Real.sq_sqrt (mul_pos hp hW0).le
      have hF0 : 0 < φ t := Real.sqrt_pos.mpr (mul_pos hp hW0)
      have hV : (1 + ε) * φ t + 1 < regU (sqC c) σ t / regSol (sqC c) σ t := by
        have : -regU (sqC c) σ t / regSol (sqC c) σ t = -(regU (sqC c) σ t / regSol (sqC c) σ t) := by
          rw [neg_div]
        linarith
      have hw' : c ^ 4 ≤ ε ^ 2 * (c ^ 2 * t ^ 2 - σ) ^ 3 :=
        hw.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0.le (hwt t ht) 3) (sq_nonneg ε))
      have := agmon_alg hp (by nlinarith) hW0 hF2 hF0 hε hε1 (hτ'.trans ht.1) ht.2.le hw' hV
      linarith)
    (by simp [regU, hφ])
  intro t ht
  have hD := h t ht
  have hy := one_le_forbidden hτ' hτσ' t ht
  have e : (-regU (sqC c) σ t / regSol (sqC c) σ t + ((1 + ε) * φ t + 1)) * regSol (sqC c) σ t =
      -regU (sqC c) σ t + ((1 + ε) * φ t + 1) * regSol (sqC c) σ t := by
    have : regSol (sqC c) σ t ≠ 0 := by linarith
    field_simp
  nlinarith [mul_nonneg hD (show 0 ≤ regSol (sqC c) σ t by linarith)]

/-! ### Integrating the Riccati bound -/

/-- **The log-integration step**: on `[α, β] ⊆ [τ, 1)` in the forbidden region, `U ≤ By` gives
`log y(α) ≤ log y(β) + ∫_α^β B/(1 − t²)`. -/
theorem log_le_of_regU_le {τ α β : ℝ} {B : ℝ → ℝ} (hτ : 0 ≤ τ) (hτσ : σ ≤ c ^ 2 * τ ^ 2) (hα : τ ≤ α)
    (hαβ : α ≤ β) (hβ : β < 1) (hB : ContinuousOn B (Icc α β))
    (hU : ∀ t ∈ Icc α β, regU (sqC c) σ t ≤ B t * regSol (sqC c) σ t) :
    log (regSol (sqC c) σ α) ≤ log (regSol (sqC c) σ β) + ∫ t in α..β, B t / (1 - t ^ 2) := by
  have hy : ∀ t ∈ Icc α β, 1 ≤ regSol (sqC c) σ t := fun t ht =>
    one_le_forbidden hτ hτσ t ⟨hα.trans ht.1, ht.2.trans hβ.le⟩
  have hp : ∀ t ∈ Icc α β, 0 < 1 - t ^ 2 := fun t ht => by nlinarith [ht.1, ht.2, hτ.trans (hα.trans ht.1)]
  have hgc : ContinuousOn (fun t => B t / (1 - t ^ 2)) (Icc α β) :=
    hB.div (by fun_prop) fun t ht => (hp t ht).ne'
  have hint : ∀ t ∈ Icc α β, IntervalIntegrable (fun t => B t / (1 - t ^ 2)) volume α t := fun t ht =>
    (hgc.mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)).intervalIntegrable
  have hcI : ContinuousOn (fun t => log (regSol (sqC c) σ t) + ∫ s in α..t, B s / (1 - s ^ 2)) (Icc α β) := by
    refine ContinuousOn.add (ContinuousOn.log ((Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).mono fun t ht =>
      show (-1 : ℝ) < t by linarith [hτ.trans (hα.trans ht.1)]) fun t ht => by linarith [hy t ht]) ?_
    have := intervalIntegral.continuousOn_primitive_interval' (hint β ⟨hαβ, le_rfl⟩) (left_mem_uIcc)
    rwa [uIcc_of_le hαβ] at this
  have hG : ∀ t ∈ Ioo α β, HasDerivAt (fun t => log (regSol (sqC c) σ t) + ∫ s in α..t, B s / (1 - s ^ 2))
      (Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t / regSol (sqC c) σ t + B t / (1 - t ^ 2)) t := by
    intro t ht
    have ht' : t ∈ Icc α β := Ioo_subset_Icc_self ht
    have h1 : HasDerivAt (fun t => log (regSol (sqC c) σ t)) (Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t / regSol (sqC c) σ t) t :=
      (hasDerivAt_regSol (sqC c) σ (by linarith [hτ.trans (hα.trans ht'.1)])).log (by linarith [hy t ht'])
    have h2 : HasDerivAt (fun t => ∫ s in α..t, B s / (1 - s ^ 2)) (B t / (1 - t ^ 2)) t :=
      intervalIntegral.integral_hasDerivAt_right (hint t ht')
        ((hgc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
        (hgc.continuousAt (Icc_mem_nhds ht.1 ht.2))
    exact h1.add h2
  have hmono : MonotoneOn (fun t => log (regSol (sqC c) σ t) + ∫ s in α..t, B s / (1 - s ^ 2)) (Icc α β) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc α β) hcI
      (fun t ht => by rw [interior_Icc] at ht; exact (hG t ht).hasDerivWithinAt) fun t ht => ?_
    rw [interior_Icc] at ht
    have ht' := Ioo_subset_Icc_self ht
    have hpd := Cvs.Prolate.RegularSolutionEnergyComparability.p_mul_deriv (c := c) (σ := σ) (t := t) (by linarith [hτ.trans (hα.trans ht'.1)])
    have hpt := hp t ht'
    have hv : Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t = -regU (sqC c) σ t / (1 - t ^ 2) := by
      rw [eq_div_iff hpt.ne', mul_comm]; exact hpd
    have hyt := hy t ht'
    have hUt := hU t ht'
    rw [hv]
    have e : -regU (sqC c) σ t / (1 - t ^ 2) / regSol (sqC c) σ t + B t / (1 - t ^ 2) =
        (B t * regSol (sqC c) σ t - regU (sqC c) σ t) / ((1 - t ^ 2) * regSol (sqC c) σ t) := by
      field_simp; ring
    rw [e]
    exact div_nonneg (by linarith) (by positivity)
  have := hmono ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩ hαβ
  simpa using this

/-- **The tunnelling bound**: for `σ = c²θ²`, `0 ≤ θ ≤ a ≤ 3/5`, `η > 0`, `0 < ε ≤ 1` with `c⁴ ≤ ε²(c²η)³`,
`log y(θ) ≤ log y(a) + c√η + (1 + ε)c∫_θ^a √(t² − θ²)/√(1 − t²) dt + 2`. -/
theorem log_le_tunnel {θ a η ε : ℝ} (hc : 0 < c) (hθ : 0 ≤ θ) (hθσ : σ = c ^ 2 * θ ^ 2) (hθa : θ ≤ a)
    (ha : a ≤ 3 / 5) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1) (hw : c ^ 4 ≤ ε ^ 2 * (c ^ 2 * η) ^ 3) :
    log (regSol (sqC c) σ θ) ≤ log (regSol (sqC c) σ a) + c * √η +
      (1 + ε) * c * (∫ t in θ..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) + 2 := by
  have hσ0 : 0 ≤ σ := by rw [hθσ]; positivity
  have hτσ : σ ≤ c ^ 2 * θ ^ 2 := hθσ.le
  have ha1 : a < 1 := by linarith
  have hp : ∀ t ∈ Icc θ a, 16 / 25 ≤ 1 - t ^ 2 := fun t ht => by nlinarith [ht.1, ht.2, hθ.trans ht.1]
  have hAg : ∀ α, θ ≤ α → α ≤ a → ∫ t in α..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2) ≤
      ∫ t in θ..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2) := by
    intro α h1 h2
    have hi : ∀ u v, θ ≤ u → u ≤ v → v ≤ a →
        IntervalIntegrable (fun t => √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) volume u v := fun u v h1 h2 h3 =>
      (ContinuousOn.div (f := fun t => √(t ^ 2 - θ ^ 2)) (g := fun t => √(1 - t ^ 2)) (by fun_prop) (by fun_prop) fun t ht => by
        rw [uIcc_of_le h2] at ht
        exact (Real.sqrt_pos.mpr (by nlinarith [ht.1, ht.2, hθ.trans (h1.trans ht.1)])).ne').intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi θ α le_rfl h1 h2) (hi α a h1 h2 le_rfl)]
    have : 0 ≤ ∫ t in θ..α, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2) :=
      intervalIntegral.integral_nonneg h1 fun t _ => by positivity
    linarith
  have hAg0 : 0 ≤ ∫ t in θ..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2) :=
    intervalIntegral.integral_nonneg hθa fun t _ => by positivity
  set t₀ := √(θ ^ 2 + η) with ht₀
  have ht₀2 : t₀ ^ 2 = θ ^ 2 + η := Real.sq_sqrt (by positivity)
  have hθt₀ : θ ≤ t₀ := by rw [ht₀]; exact Real.le_sqrt_of_sq_le (by linarith)
  have ht₀θ : t₀ - θ ≤ √η := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ t₀ - θ)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- the crude step on `[θ, β]`
  have crude : ∀ β, θ ≤ β → β ≤ a → log (regSol (sqC c) σ θ) ≤ log (regSol (sqC c) σ β) + c * (β - θ) := by
    intro β h1 h2
    have h := log_le_of_regU_le (B := fun _ => c / 2) hθ hτσ le_rfl h1 (by linarith) continuousOn_const
      (fun t ht => regU_le_half hc.le hσ0 hθ hτσ t ⟨ht.1, ht.2.trans (by linarith)⟩)
    have hb : ∫ t in θ..β, c / 2 / (1 - t ^ 2) ≤ ∫ t in θ..β, c := by
      refine intervalIntegral.integral_mono_on h1 ?_ intervalIntegrable_const fun t ht => ?_
      · exact (ContinuousOn.div (f := fun _ => c / 2) (g := fun t => 1 - t ^ 2) continuousOn_const (by fun_prop) fun t ht => by
          rw [uIcc_of_le h1] at ht
          linarith [hp t ⟨ht.1, ht.2.trans h2⟩]).intervalIntegrable
      · rw [div_le_iff₀ (by linarith [hp t ⟨ht.1, ht.2.trans h2⟩])]
        nlinarith [hp t ⟨ht.1, ht.2.trans h2⟩]
    rw [intervalIntegral.integral_const, smul_eq_mul] at hb
    nlinarith
  rcases le_or_gt a t₀ with hat | hat
  · have := crude a hθa le_rfl
    have : c * (a - θ) ≤ c * √η := mul_le_mul_of_nonneg_left (by linarith) hc.le
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) (mul_nonneg hc.le hAg0)]
  · have h1 := crude t₀ hθt₀ hat.le
    have hw' : c ^ 4 ≤ ε ^ 2 * (c ^ 2 * t₀ ^ 2 - σ) ^ 3 := by
      rw [ht₀2, hθσ]; convert hw using 3; ring
    have hag := regU_le_agmon (c := c) (σ := σ) hc (hθ.trans hθt₀) hε hε1 hw'
    set φ : ℝ → ℝ := fun t => √((1 - t ^ 2) * (c ^ 2 * t ^ 2 - σ))
    have h2 := log_le_of_regU_le (B := fun t => (1 + ε) * φ t + 1) hθ hτσ hθt₀ hat.le ha1 (by fun_prop)
      (fun t ht => hag t ⟨ht.1, ht.2.trans ha1.le⟩)
    have hsplit : ∫ t in t₀..a, ((1 + ε) * φ t + 1) / (1 - t ^ 2) ≤
        (1 + ε) * c * (∫ t in t₀..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) + 2 := by
      have hpt : ∀ t ∈ Icc t₀ a, ((1 + ε) * φ t + 1) / (1 - t ^ 2) ≤
          (1 + ε) * c * (√(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) + 25 / 16 := by
        intro t ht
        have hpt := hp t ⟨hθt₀.trans ht.1, ht.2⟩
        have hpos : 0 < 1 - t ^ 2 := by linarith
        have hφ : φ t / (1 - t ^ 2) = c * (√(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) := by
          have hs : 0 < √(1 - t ^ 2) := Real.sqrt_pos.mpr hpos
          have hss : √(1 - t ^ 2) * √(1 - t ^ 2) = 1 - t ^ 2 := Real.mul_self_sqrt hpos.le
          have e1 : φ t = √(1 - t ^ 2) * (c * √(t ^ 2 - θ ^ 2)) := by
            simp only [φ]
            rw [hθσ, show c ^ 2 * t ^ 2 - c ^ 2 * θ ^ 2 = c ^ 2 * (t ^ 2 - θ ^ 2) by ring,
              Real.sqrt_mul hpos.le, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
          rw [e1, mul_div_assoc', div_eq_div_iff hpos.ne' hs.ne']
          calc √(1 - t ^ 2) * (c * √(t ^ 2 - θ ^ 2)) * √(1 - t ^ 2)
              = c * √(t ^ 2 - θ ^ 2) * (√(1 - t ^ 2) * √(1 - t ^ 2)) := by ring
            _ = _ := by rw [hss]
        have e : ((1 + ε) * φ t + 1) / (1 - t ^ 2) = (1 + ε) * (φ t / (1 - t ^ 2)) + 1 / (1 - t ^ 2) := by
          field_simp
        rw [e, hφ]
        have : 1 / (1 - t ^ 2) ≤ 25 / 16 := by rw [div_le_iff₀ hpos]; linarith
        linarith
      have hint1 : IntervalIntegrable (fun t => ((1 + ε) * φ t + 1) / (1 - t ^ 2)) volume t₀ a :=
        (ContinuousOn.div (f := fun t => (1 + ε) * φ t + 1) (g := fun t => 1 - t ^ 2) (by fun_prop) (by fun_prop) fun t ht => by
          rw [uIcc_of_le hat.le] at ht; linarith [hp t ⟨hθt₀.trans ht.1, ht.2⟩]).intervalIntegrable
      have hg : IntervalIntegrable (fun t => √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) volume t₀ a :=
        (ContinuousOn.div (f := fun t => √(t ^ 2 - θ ^ 2)) (g := fun t => √(1 - t ^ 2)) (by fun_prop) (by fun_prop) fun t ht => by
          rw [uIcc_of_le hat.le] at ht
          exact (Real.sqrt_pos.mpr (by linarith [hp t ⟨hθt₀.trans ht.1, ht.2⟩])).ne').intervalIntegrable
      have hint2 := (hg.const_mul ((1 + ε) * c)).add (intervalIntegrable_const (c := (25 / 16 : ℝ)))
      have := intervalIntegral.integral_mono_on hat.le hint1 hint2 hpt
      rw [intervalIntegral.integral_add (hg.const_mul _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at this
      have hlen : (a - t₀) * (25 / 16) ≤ 2 := by nlinarith [hθ.trans hθt₀]
      linarith
    have h3 := hAg t₀ hθt₀ hat.le
    have h4 : (1 + ε) * c * (∫ t in t₀..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) ≤
        (1 + ε) * c * (∫ t in θ..a, √(t ^ 2 - θ ^ 2) / √(1 - t ^ 2)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : c * (t₀ - θ) ≤ c * √η := mul_le_mul_of_nonneg_left ht₀θ hc.le
    linarith

end Cvs.Prolate.RegularSolutionForbiddenRegion

end
