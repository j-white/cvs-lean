import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Gram.DirichletDualFloorShifted
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionDepthBound
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Energy comparability: `∫_b^1 y_σ² ≤ 4(U(b)² + (1 + σ)y(b)²)` for `σ ≥ c²b²` (eq-cpb Lemmas 6, 7, 8(i))

`E = U² + (1 − t²)(σ − c²t²)y²` has `E' = −2t(σ + c² − 2c²t²)y²`, so it decreases on the allowed region, where
`|y'| ≤ √E(b)/(1 − t²)` gives `|y(t) − y(b)| ≤ √E(b)·artanh t`; `y²` decreases on the forbidden region, and
`∫_0^1 log²(2/v) dv < 4`. At a Dirichlet node `y(a) = 0` this is `g_a(σ)² ≥ 1/4`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC hasDerivAt_regSol hasDerivAt_regU pP_mul_regV)

namespace Cvs.Prolate.RegularSolutionEnergyComparability
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-- The Liouville energy `E = U² + (1 − t²)(σ − c²t²)y²`. -/
def energy (c σ t : ℝ) : ℝ :=
  regU (sqC c) σ t ^ 2 + (1 - t ^ 2) * (σ - c ^ 2 * t ^ 2) * regSol (sqC c) σ t ^ 2

/-- `y' = −U/(1 − t²)` in the form `(1 − t²)y' = −U`. -/
theorem p_mul_deriv {t : ℝ} (ht : -1 < t) :
    (1 - t ^ 2) * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t = -regU (sqC c) σ t := by
  have := pP_mul_regV (sqC c) σ ht
  unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP at this
  linarith

/-- `E' = −2t(σ + c² − 2c²t²)y²`. -/
theorem hasDerivAt_energy {t : ℝ} (ht : -1 < t) :
    HasDerivAt (energy c σ) (-(2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2)) * regSol (sqC c) σ t ^ 2) t := by
  have hy := hasDerivAt_regSol (sqC c) σ ht
  have hU := hasDerivAt_regU (sqC c) σ ht
  have hp : HasDerivAt (fun t : ℝ => (1 - t ^ 2) * (σ - c ^ 2 * t ^ 2))
      (-(2 * t) * (σ - c ^ 2 * t ^ 2) + (1 - t ^ 2) * (-(c ^ 2 * (2 * t)))) t := by
    have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_sub 1)
    have h2 : HasDerivAt (fun t : ℝ => σ - c ^ 2 * t ^ 2) (-(c ^ 2 * (2 * t))) t := by
      simpa using (((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_sub σ)
    exact h1.mul h2
  have d := (hU.pow 2).add (hp.mul (hy.pow 2))
  unfold energy
  refine d.congr_deriv ?_
  have hpd := p_mul_deriv (c := c) (σ := σ) ht
  rw [Cvs.Prolate.TopRungDepthBound.sqC_apply]
  simp only [Nat.cast_ofNat, Pi.pow_apply]
  linear_combination (2 * (σ - c ^ 2 * t ^ 2) * regSol (sqC c) σ t) * hpd

/-- **The energy decreases** on `[α, β] ⊆ (−1, ∞)` wherever `0 ≤ t` and `2c²t² ≤ σ + c²`. -/
theorem energy_anti {α β : ℝ} (hα : 0 ≤ α) (hβ : ∀ t ∈ Icc α β, 2 * c ^ 2 * t ^ 2 ≤ σ + c ^ 2) :
    AntitoneOn (energy c σ) (Icc α β) := by
  have hm := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv (a := α) (b := β) (f := fun t => -energy c σ t)
    (fun t ht => (hasDerivAt_energy (c := c) (σ := σ) (show -1 < t by linarith [ht.1])).neg) (fun t ht => by
      have h1 := hβ t ht
      have h2 : 0 ≤ t := hα.trans ht.1
      have : 0 ≤ 2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2) * regSol (sqC c) σ t ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
      linarith)
  exact fun s hs t ht hst => by simpa using hm hs ht hst

/-! ### The forbidden region -/

/-- **`y²` decreases on the forbidden region** `[τ, 1]`, `c²τ² ≥ σ` (eq-cpb Lemma 6(ii)). -/
theorem sq_anti_forbidden {τ : ℝ} (hτ : 0 ≤ τ) (hτσ : σ ≤ c ^ 2 * τ ^ 2) :
    AntitoneOn (fun t => regSol (sqC c) σ t ^ 2) (Icc τ 1) := by
  set g : ℝ → ℝ := fun t => -2 * regSol (sqC c) σ t * regU (sqC c) σ t with hg
  have hgd : ∀ t ∈ Icc τ 1, HasDerivAt g (2 * (1 - t ^ 2) * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t ^ 2
      - 2 * (σ - c ^ 2 * t ^ 2) * regSol (sqC c) σ t ^ 2) t := by
    intro t ht
    have ht1 : -1 < t := by linarith [ht.1]
    have d := ((hasDerivAt_regSol (sqC c) σ ht1).const_mul (-2)).mul (hasDerivAt_regU (sqC c) σ ht1)
    refine d.congr_deriv ?_
    have hpd := p_mul_deriv (c := c) (σ := σ) ht1
    rw [Cvs.Prolate.TopRungDepthBound.sqC_apply]
    linear_combination (-2 * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t) * hpd
  have hgm : MonotoneOn g (Icc τ 1) := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv hgd fun t ht => by
    have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have h2 : σ - c ^ 2 * t ^ 2 ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ ht.1 2) (sq_nonneg c)]
    nlinarith [sq_nonneg (Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t), sq_nonneg (regSol (sqC c) σ t),
      mul_nonneg h1 (sq_nonneg (Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t)),
      mul_nonneg (neg_nonneg.mpr h2) (sq_nonneg (regSol (sqC c) σ t))]
  have hg1 : g 1 = 0 := by simp [hg, regU]
  have hd : ∀ t ∈ Icc τ 1, HasDerivAt (fun t => regSol (sqC c) σ t ^ 2)
      (2 * regSol (sqC c) σ t * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t) t := fun t ht => by
    exact ((hasDerivAt_regSol (sqC c) σ (show -1 < t by linarith [ht.1])).pow 2).congr_deriv (by norm_num)
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc τ 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt) fun t ht => ?_
  rw [interior_Icc] at ht
  have hgt : g t ≤ 0 := hg1 ▸ hgm ⟨ht.1.le, ht.2.le⟩ ⟨by linarith [ht.1, ht.2], le_rfl⟩ ht.2.le
  have hp : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hpd := p_mul_deriv (c := c) (σ := σ) (show -1 < t by linarith [ht.1])
  have e : (1 - t ^ 2) * (2 * regSol (sqC c) σ t * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t) = g t := by
    simp only [hg]; linear_combination (2 * regSol (sqC c) σ t) * hpd
  by_contra hc
  push Not at hc
  have := mul_pos hp hc
  linarith

/-! ### `∫ log²(2/(1 − t)) ≤ 4` -/

/-- `F(v) = vL² + 2vL + 2v`, `L = log(2/v)`, an antiderivative of `L²` in `v`. -/
def logSqAnti (v : ℝ) : ℝ := v * log (2 / v) ^ 2 + 2 * v * log (2 / v) + 2 * v

theorem hasDerivAt_logSqAnti {v : ℝ} (hv : 0 < v) : HasDerivAt logSqAnti (log (2 / v) ^ 2) v := by
  have hl : HasDerivAt (fun w => log 2 - log w) (-v⁻¹) v := (Real.hasDerivAt_log hv.ne').const_sub _
  have d := (((hasDerivAt_id' v).mul (hl.mul hl)).add (((hasDerivAt_id' v).const_mul 2).mul hl)).add
    ((hasDerivAt_id' v).const_mul 2)
  have e : (fun w => w * ((log 2 - log w) * (log 2 - log w)) + 2 * w * (log 2 - log w) + 2 * w) =ᶠ[𝓝 v]
      logSqAnti := by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    simp only [logSqAnti]
    rw [Real.log_div (by norm_num) (ne_of_gt hw)]
    ring
  refine (d.congr_of_eventuallyEq e.symm).congr_deriv ?_
  rw [Real.log_div (by norm_num) hv.ne']
  simp only [Pi.mul_apply]
  field_simp
  ring

theorem log_two_lt : log 2 < 7 / 10 := by
  have := Real.log_two_lt_d9; norm_num at this; linarith

theorem log_two_div_pos {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) : 0 < log (2 / v) :=
  Real.log_pos (by rw [lt_div_iff₀ hv]; linarith)

/-- `0 ≤ F(v) ≤ 4` and `vL(v)² ≤ F(v)` on `(0, 1]`. -/
theorem logSqAnti_bounds {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    v * log (2 / v) ^ 2 ≤ logSqAnti v ∧ logSqAnti v ≤ 4 := by
  have hL := log_two_div_pos hv hv1
  refine ⟨by unfold logSqAnti; nlinarith, ?_⟩
  have hmono : MonotoneOn logSqAnti (Icc v 1) := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv
    (fun w hw => hasDerivAt_logSqAnti (hv.trans_le hw.1)) fun w _ => sq_nonneg _
  have h1 := hmono ⟨le_rfl, hv1⟩ ⟨hv1, le_rfl⟩ hv1
  have hF1 : logSqAnti 1 ≤ 4 := by
    unfold logSqAnti
    rw [div_one]
    have h0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith [log_two_lt]
  linarith

/-- `∫_α^β log²(2/(1 − t)) dt ≤ 4` for `0 ≤ α ≤ β < 1`. -/
theorem integral_logSq_le {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β < 1) :
    ∫ t in α..β, log (2 / (1 - t)) ^ 2 ≤ 4 := by
  have hd : ∀ t ∈ uIcc α β, HasDerivAt (fun t => -logSqAnti (1 - t)) (log (2 / (1 - t)) ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hαβ] at ht
    have h := (hasDerivAt_logSqAnti (show 0 < 1 - t by linarith [ht.2])).comp t ((hasDerivAt_id t).const_sub 1)
    exact h.neg.congr_deriv (by simp)
  have hc : ContinuousOn (fun t => log (2 / (1 - t)) ^ 2) (uIcc α β) := by
    rw [uIcc_of_le hαβ]
    refine ContinuousOn.pow (ContinuousOn.log (by fun_prop (disch := intro t ht; linarith [ht.2]))
      fun t ht => ?_) 2
    exact (div_pos two_pos (by linarith [ht.2])).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have h1 := logSqAnti_bounds (show 0 < 1 - β by linarith) (by linarith)
  have h2 := logSqAnti_bounds (show 0 < 1 - α by linarith) (by linarith)
  have h0 : 0 ≤ (1 - β) * log (2 / (1 - β)) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith [h1.1, h2.2]

/-- `0 ≤ artanh t ≤ ½ log(2/(1 − t))` on `[0, 1)`. -/
theorem Lf_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 ≤ Cvs.Prolate.TopRungDepthBound.Lf t ∧ Cvs.Prolate.TopRungDepthBound.Lf t ≤ log (2 / (1 - t)) / 2 := by
  unfold Cvs.Prolate.TopRungDepthBound.Lf
  have h1 : 0 < 1 - t := by linarith
  constructor
  · have := Real.log_le_log h1 (by linarith : 1 - t ≤ 1 + t); linarith
  · rw [Real.log_div (by norm_num) h1.ne']
    have := Real.log_le_log (by linarith) (by linarith : 1 + t ≤ 2); linarith

/-! ### The allowed region -/

/-- **The allowed-region bound**: on `[b, r] ⊆ [0, 1)` with `2c²t² ≤ σ + c²` and `c²t² ≤ σ`,
`|y(t) − y(b)| ≤ √E(b)(artanh t − artanh b)`. -/
theorem abs_sub_le_allowed {b r : ℝ} (hb : 0 ≤ b) (hr : r < 1)
    (hq : ∀ t ∈ Icc b r, 2 * c ^ 2 * t ^ 2 ≤ σ + c ^ 2 ∧ c ^ 2 * t ^ 2 ≤ σ) {t : ℝ} (ht : t ∈ Icc b r) :
    |regSol (sqC c) σ t - regSol (sqC c) σ b| ≤ √(energy c σ b) * (Cvs.Prolate.TopRungDepthBound.Lf t - Cvs.Prolate.TopRungDepthBound.Lf b) := by
  have hanti := energy_anti (c := c) (σ := σ) hb (fun t ht => (hq t ht).1)
  have hb' : b ∈ Icc b r := ⟨le_rfl, ht.1.trans ht.2⟩
  have hU : ∀ s ∈ Icc b r, |regU (sqC c) σ s| ≤ √(energy c σ b) := by
    intro s hs
    have h1 : 0 ≤ (1 - s ^ 2) * (σ - c ^ 2 * s ^ 2) * regSol (sqC c) σ s ^ 2 :=
      mul_nonneg (mul_nonneg (by nlinarith [hs.1, hs.2]) (by linarith [(hq s hs).2])) (sq_nonneg _)
    have h2 : regU (sqC c) σ s ^ 2 ≤ energy c σ b := by
      have := hanti hb' hs hs.1; unfold energy at this ⊢; linarith
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h2
  have hreg : ∀ s ∈ Icc b r, s ^ 2 < 1 := fun s hs => by nlinarith [hs.1, hs.2]
  have hy' : ∀ s ∈ Icc b r, |Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s| ≤ √(energy c σ b) * (1 / (1 - s ^ 2)) := by
    intro s hs
    have hp : 0 < 1 - s ^ 2 := by linarith [hreg s hs]
    have e : Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s = -regU (sqC c) σ s / (1 - s ^ 2) := by
      rw [eq_div_iff hp.ne', mul_comm]; exact p_mul_deriv (by linarith [hs.1])
    rw [e, abs_div, abs_neg, abs_of_pos hp, mul_one_div]
    exact div_le_div_of_nonneg_right (hU s hs) hp.le
  set M := √(energy c σ b)
  have hd1 : ∀ s ∈ Icc b r, HasDerivAt (fun s => M * Cvs.Prolate.TopRungDepthBound.Lf s - regSol (sqC c) σ s)
      (M * (1 / (1 - s ^ 2)) - Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s) s := fun s hs =>
    ((Cvs.Prolate.TopRungDepthBound.hasDerivAt_Lf (hreg s hs)).const_mul M).sub (hasDerivAt_regSol (sqC c) σ (by linarith [hs.1]))
  have hd2 : ∀ s ∈ Icc b r, HasDerivAt (fun s => M * Cvs.Prolate.TopRungDepthBound.Lf s + regSol (sqC c) σ s)
      (M * (1 / (1 - s ^ 2)) + Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s) s := fun s hs =>
    ((Cvs.Prolate.TopRungDepthBound.hasDerivAt_Lf (hreg s hs)).const_mul M).add (hasDerivAt_regSol (sqC c) σ (by linarith [hs.1]))
  have m1 := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv hd1 fun s hs => by linarith [(abs_le.mp (hy' s hs)).2]
  have m2 := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv hd2 fun s hs => by linarith [(abs_le.mp (hy' s hs)).1]
  have i1 := m1 hb' ht ht.1
  have i2 := m2 hb' ht ht.1
  simp only at i1 i2
  rw [abs_le]; constructor <;> nlinarith

/-- The pointwise allowed bound `y(t)² ≤ 2y(b)² + ½E(b)log²(2/(1 − t))`. -/
theorem sq_le_allowed {b r : ℝ} (hb : 0 ≤ b) (hr : r < 1)
    (hq : ∀ t ∈ Icc b r, 2 * c ^ 2 * t ^ 2 ≤ σ + c ^ 2 ∧ c ^ 2 * t ^ 2 ≤ σ) {t : ℝ} (ht : t ∈ Icc b r) :
    regSol (sqC c) σ t ^ 2 ≤ 2 * regSol (sqC c) σ b ^ 2 + energy c σ b / 2 * log (2 / (1 - t)) ^ 2 := by
  have hb' : b ∈ Icc b r := ⟨le_rfl, ht.1.trans ht.2⟩
  have hE : 0 ≤ energy c σ b := by
    unfold energy
    have := mul_nonneg (mul_nonneg (by nlinarith [ht.1, ht.2] : (0 : ℝ) ≤ 1 - b ^ 2)
      (by linarith [(hq b hb').2] : (0 : ℝ) ≤ σ - c ^ 2 * b ^ 2)) (sq_nonneg (regSol (sqC c) σ b))
    positivity
  have h := abs_sub_le_allowed hb hr hq ht
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 hr
  obtain ⟨hL0, hL1⟩ := Lf_bounds (hb.trans ht.1) ht1
  obtain ⟨hb0, -⟩ := Lf_bounds hb (lt_of_le_of_lt hb'.2 hr)
  set M := √(energy c σ b)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hM2 : M ^ 2 = energy c σ b := Real.sq_sqrt hE
  have h1 : |regSol (sqC c) σ t - regSol (sqC c) σ b| ≤ M * Cvs.Prolate.TopRungDepthBound.Lf t := h.trans (by nlinarith)
  have h2 : regSol (sqC c) σ t ^ 2 ≤ 2 * regSol (sqC c) σ b ^ 2 + 2 * (M * Cvs.Prolate.TopRungDepthBound.Lf t) ^ 2 := by
    have := abs_le.mp h1
    nlinarith [sq_nonneg (regSol (sqC c) σ t - 2 * regSol (sqC c) σ b),
      sq_nonneg (regSol (sqC c) σ t - regSol (sqC c) σ b - M * Cvs.Prolate.TopRungDepthBound.Lf t)]
  have h3 : Cvs.Prolate.TopRungDepthBound.Lf t ^ 2 ≤ log (2 / (1 - t)) ^ 2 / 4 := by nlinarith
  rw [mul_pow, hM2] at h2
  nlinarith

/-- `∫_b^r y² ≤ 2y(b)² + 2E(b)` on an allowed `[b, r] ⊆ [0, 1)`. -/
theorem integral_sq_le_allowed {b r : ℝ} (hb : 0 ≤ b) (hbr : b ≤ r) (hr : r < 1)
    (hq : ∀ t ∈ Icc b r, 2 * c ^ 2 * t ^ 2 ≤ σ + c ^ 2 ∧ c ^ 2 * t ^ 2 ≤ σ) :
    ∫ t in b..r, regSol (sqC c) σ t ^ 2 ≤ 2 * regSol (sqC c) σ b ^ 2 + 2 * energy c σ b := by
  have hE : 0 ≤ energy c σ b := by
    unfold energy
    have := mul_nonneg (mul_nonneg (by nlinarith : (0 : ℝ) ≤ 1 - b ^ 2)
      (by linarith [(hq b ⟨le_rfl, hbr⟩).2] : (0 : ℝ) ≤ σ - c ^ 2 * b ^ 2)) (sq_nonneg (regSol (sqC c) σ b))
    positivity
  have hcL : ContinuousOn (fun t => log (2 / (1 - t)) ^ 2) (Icc b r) := by
    refine ContinuousOn.pow (ContinuousOn.log (by fun_prop (disch := intro t ht; linarith [ht.2]))
      fun t ht => ?_) 2
    exact (div_pos two_pos (by linarith [ht.2])).ne'
  have hiL : IntervalIntegrable (fun t => log (2 / (1 - t)) ^ 2) volume b r := by
    refine ContinuousOn.intervalIntegrable ?_; rwa [uIcc_of_le hbr]
  have hiy : IntervalIntegrable (fun t => regSol (sqC c) σ t ^ 2) volume b r :=
    (((Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).pow 2).mono fun t ht => by
      rw [uIcc_of_le hbr] at ht; exact show (-1 : ℝ) < t by linarith [ht.1]).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hbr hiy
    ((intervalIntegrable_const (c := 2 * regSol (sqC c) σ b ^ 2)).add (hiL.const_mul (energy c σ b / 2)))
    fun t ht => sq_le_allowed hb hr hq ht
  rw [intervalIntegral.integral_add intervalIntegrable_const (hiL.const_mul _), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, smul_eq_mul] at hmono
  have hI := integral_logSq_le hb hbr hr
  have hrb : r - b ≤ 1 := by linarith
  nlinarith [sq_nonneg (regSol (sqC c) σ b)]

/-- **Energy comparability** (eq-cpb Lemma 7): for `0 ≤ b < 1` and `σ ≥ c²b²`,
`∫_b^1 y_σ² ≤ 4(U(b)² + (1 + σ)y(b)²)`. -/
theorem integral_sq_le {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) (hσ : c ^ 2 * b ^ 2 ≤ σ) :
    ∫ t in b..1, regSol (sqC c) σ t ^ 2 ≤
      4 * (regU (sqC c) σ b ^ 2 + (1 + σ) * regSol (sqC c) σ b ^ 2) := by
  have hσ0 : 0 ≤ σ := (mul_nonneg (sq_nonneg c) (sq_nonneg b)).trans hσ
  have hEb : energy c σ b ≤ regU (sqC c) σ b ^ 2 + σ * regSol (sqC c) σ b ^ 2 := by
    unfold energy
    have h1 : (1 - b ^ 2) * (σ - c ^ 2 * b ^ 2) ≤ σ := by nlinarith [sq_nonneg b, sq_nonneg c]
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg (regSol (sqC c) σ b))]
  have hiy : ∀ α β, b ≤ α → α ≤ β → β ≤ 1 →
      IntervalIntegrable (fun t => regSol (sqC c) σ t ^ 2) volume α β := fun α β h1 h2 h3 =>
    (((Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).pow 2).mono fun t ht => by
      rw [uIcc_of_le h2] at ht; exact show (-1 : ℝ) < t by linarith [ht.1]).intervalIntegrable
  suffices h : ∫ t in b..1, regSol (sqC c) σ t ^ 2 ≤ 4 * regSol (sqC c) σ b ^ 2 + 4 * energy c σ b by
    nlinarith
  rcases le_or_gt (c ^ 2) σ with hcσ | hcσ
  · -- the whole cell is allowed
    have hq : ∀ r, r ≤ 1 → ∀ t ∈ Icc b r, 2 * c ^ 2 * t ^ 2 ≤ σ + c ^ 2 ∧ c ^ 2 * t ^ 2 ≤ σ :=
      fun r hr t ht => by
        have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
        constructor <;> nlinarith [sq_nonneg c]
    have hcont : ContinuousWithinAt (fun r => ∫ t in b..r, regSol (sqC c) σ t ^ 2) (Iio 1) 1 := by
      have h := intervalIntegral.continuousOn_primitive_interval' (hiy b 1 le_rfl hb1.le le_rfl)
        (left_mem_uIcc (a := b) (b := 1))
      rw [uIcc_of_le hb1.le] at h
      have h1 := h 1 ⟨hb1.le, le_rfl⟩
      exact (h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hb1)).mono_left
        (nhdsWithin_mono _ (fun r hr => mem_Iic.mpr (le_of_lt hr)))
    refine le_of_tendsto hcont ?_
    filter_upwards [Ioo_mem_nhdsLT hb1] with r hr
    have := integral_sq_le_allowed hb hr.1.le hr.2 (hq r hr.2.le)
    have hE : 0 ≤ energy c σ b := by
      unfold energy
      have := mul_nonneg (mul_nonneg (by nlinarith : (0 : ℝ) ≤ 1 - b ^ 2)
        (by linarith [(hq b hb1.le b ⟨le_rfl, le_rfl⟩).2] : (0 : ℝ) ≤ σ - c ^ 2 * b ^ 2))
        (sq_nonneg (regSol (sqC c) σ b))
      positivity
    nlinarith [sq_nonneg (regSol (sqC c) σ b)]
  · -- allowed on `[b, τ]`, forbidden on `[τ, 1]`
    have hc2 : 0 < c ^ 2 := by nlinarith [sq_nonneg b]
    set τ := √(σ / c ^ 2) with hτ
    have hτ2 : τ ^ 2 = σ / c ^ 2 := Real.sq_sqrt (div_nonneg hσ0 hc2.le)
    have hcτ : c ^ 2 * τ ^ 2 = σ := by rw [hτ2, mul_div_cancel₀ _ hc2.ne']
    have hτ0 : 0 ≤ τ := Real.sqrt_nonneg _
    have hbτ : b ≤ τ := by
      rw [hτ, Real.le_sqrt hb (div_nonneg hσ0 hc2.le), le_div_iff₀ hc2]; linarith
    have hτ1 : τ < 1 := by
      rw [hτ, Real.sqrt_lt' one_pos, one_pow, div_lt_one hc2]; exact hcσ
    have hq : ∀ t ∈ Icc b τ, 2 * c ^ 2 * t ^ 2 ≤ σ + c ^ 2 ∧ c ^ 2 * t ^ 2 ≤ σ := fun t ht => by
      have : c ^ 2 * t ^ 2 ≤ σ := by
        rw [← hcτ]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hb.trans ht.1) ht.2 2) hc2.le
      constructor <;> linarith
    have h1 := integral_sq_le_allowed hb hbτ hτ1 hq
    have hanti := sq_anti_forbidden (c := c) (σ := σ) hτ0 hcτ.ge
    have h2 : ∫ t in τ..1, regSol (sqC c) σ t ^ 2 ≤ (1 - τ) * regSol (sqC c) σ τ ^ 2 := by
      have := intervalIntegral.integral_mono_on hτ1.le (hiy τ 1 hbτ hτ1.le le_rfl) intervalIntegrable_const
        fun t ht => hanti ⟨le_rfl, hτ1.le⟩ ht ht.1
      rwa [intervalIntegral.integral_const, smul_eq_mul] at this
    have h3 := sq_le_allowed hb hτ1 hq ⟨hbτ, le_rfl⟩
    have h4 := logSqAnti_bounds (show 0 < 1 - τ by linarith) (by linarith)
    have hE : 0 ≤ energy c σ b := by
      unfold energy
      have := mul_nonneg (mul_nonneg (by nlinarith : (0 : ℝ) ≤ 1 - b ^ 2)
        (by linarith [(hq b ⟨le_rfl, hbτ⟩).2] : (0 : ℝ) ≤ σ - c ^ 2 * b ^ 2)) (sq_nonneg (regSol (sqC c) σ b))
      positivity
    rw [← intervalIntegral.integral_add_adjacent_intervals (hiy b τ le_rfl hbτ hτ1.le)
      (hiy τ 1 hbτ hτ1.le le_rfl)]
    have h5 : (1 - τ) * regSol (sqC c) σ τ ^ 2 ≤ 2 * regSol (sqC c) σ b ^ 2 + 2 * energy c σ b := by
      have h6 : (1 - τ) * regSol (sqC c) σ τ ^ 2 ≤
          (1 - τ) * (2 * regSol (sqC c) σ b ^ 2) + energy c σ b / 2 * ((1 - τ) * log (2 / (1 - τ)) ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ 1 - τ by linarith)]
      nlinarith [sq_nonneg (regSol (sqC c) σ b)]
    linarith

/-! ### Dirichlet nodes -/

/-- A Dirichlet node `y_σ(a) = 0` with `0 ≤ a ≤ 1` lies above the turning level: `c²a² < σ`. -/
theorem lt_of_regSol_eq_zero {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (h : regSol (sqC c) σ a = 0) : c ^ 2 * a ^ 2 < σ := by
  by_contra hc
  push Not at hc
  have := sq_anti_forbidden (c := c) (σ := σ) ha hc ⟨le_rfl, ha1⟩ ⟨ha1, le_rfl⟩ ha1
  simp [h, Cvs.Prolate.RegularSolutionEdge.regSol_one] at this
  linarith

/-- `N_a(σ) ≤ 4U(a)²` at a Dirichlet node with `0 ≤ a < 1`. -/
theorem dirMass_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (h : regSol (sqC c) σ a = 0) :
    Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass c a σ ≤ 4 * regU (sqC c) σ a ^ 2 := by
  have := integral_sq_le ha ha1 (lt_of_regSol_eq_zero ha ha1.le h).le
  rw [h] at this
  unfold Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass
  linarith

/-- **The Dirichlet weights are bounded below** (eq-cpb Lemma 8(i)): `g_a(σ)² ≥ ¼` at every node, `0 ≤ a < 1`. -/
theorem quarter_le_dirG_sq {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (h : regSol (sqC c) σ a = 0) :
    1 / 4 ≤ Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG c a σ ^ 2 := by
  have hN := Cvs.Prolate.Gram.DirichletDualFloorShifted.dirMass_pos c σ (by linarith) ha1
  have hU := Cvs.Prolate.EdgeCentreSign.regU_ne_zero_of_regSol_eq_zero (sqC c) σ (by linarith) ha1 h
  have hle := dirMass_le ha ha1 h
  unfold Cvs.Prolate.Gram.DirichletDualFloorShifted.dirG
  rw [div_pow, Real.sq_sqrt hN.le, le_div_iff₀ hN]
  linarith

end Cvs.Prolate.RegularSolutionEnergyComparability

end
