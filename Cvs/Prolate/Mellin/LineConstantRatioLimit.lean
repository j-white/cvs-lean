import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningRatioComplex
import Cvs.Prolate.Mellin.PastTurningStepErrors
import Cvs.Prolate.Mellin.RungThreeTermRecurrence
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.TrueRatioMatchesFrozen
import Cvs.Prolate.Mellin.TwoLinesAgreeComplex
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Prolate.Mellin.WkbPhaseVerticalFar
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ratio of the two line constants tends to one

For `s₀ = ½ + iz` past the turning point and the real line `½`, with `K = n + 1`,
`Q_K = P(s₀ + 2K)/P(½ + 2K) · exp(Ψ(½ + 2K) − Ψ(s₀ + 2K)) → 1`: it factors exactly into the `mel` ratio, `TwoLinesAgreeComplex`'s
main factor, `exp(a·corr − R/2)`, `exp(½(ĝ(x + iz) − ĝ(x)))` and the `log p`, `log(1 + r)` factors, each tending to `1`.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.LineConstantRatioLimit

open Cvs.Prolate.Mellin.RungThreeTermRecurrence (mel)
open Cvs.Prolate.Mellin.LawRatioRecurrence (mg lawRatio)
open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (rhoStar)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Prolate.Mellin.TrueRatioDownwardStep (Pk)
open Cvs.Upstream.ComplexArsinhStrip (ash)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Sq Gh gh)
open Cvs.Prolate.Mellin.FrozenForcingIdentities (rr pp)
open Cvs.Prolate.Mellin.PastTurningContraction (Up)
open Cvs.Prolate.Mellin.PastTurningRatioComplex (Psi)

/-- `x_n = 2 + 2(n + 1)` tends to infinity. -/
theorem tendsto_xn : Tendsto (fun n : ℕ => (2 + 2 * (n + 1 : ℕ) : ℝ)) atTop atTop := by
  have : Tendsto (fun n : ℕ => (2 : ℝ) * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_mul_atTop (by norm_num)
  exact tendsto_atTop_add_const_left _ _ this

theorem tendsto_bound (C z : ℝ) : Tendsto (fun n : ℕ => C / (2 * ((2 + 2 * (n + 1 : ℕ) : ℝ) - z))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (2 + 2 * (n + 1 : ℕ) : ℝ) - z) atTop atTop :=
    tendsto_atTop_add_const_right _ (-z) tendsto_xn
  exact tendsto_const_nhds.div_atTop (h1.const_mul_atTop (by norm_num))

/-- The line points tend to infinity in norm. -/
theorem tendsto_norm_line (s₀ : ℂ) : Tendsto (fun n : ℕ => ‖s₀ + 2 * ((n + 1 : ℕ) : ℂ)‖) atTop atTop := by
  have h : Tendsto (fun n : ℕ => s₀.re + 2 * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_mul_atTop (by norm_num))
  refine tendsto_atTop_mono (fun n => ?_) h
  have := Complex.re_le_norm (s₀ + 2 * ((n + 1 : ℕ) : ℂ)); simp at this ⊢; linarith

theorem line_ne {s₀ : ℂ} (hre : 0 < s₀.re) (n : ℕ) (a : ℝ) (ha : 0 ≤ a) : s₀ + 2 * ((n + 1 : ℕ) : ℂ) + a ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this
  have := n.cast_nonneg (α := ℝ)
  linarith

theorem line_ne0 {s₀ : ℂ} (hre : 0 < s₀.re) (n : ℕ) : s₀ + 2 * ((n + 1 : ℕ) : ℂ) ≠ 0 := by
  intro h0; have := congrArg Complex.re h0; simp at this; have := n.cast_nonneg (α := ℝ); linarith

theorem line_ne1 {s₀ : ℂ} (hre : 0 < s₀.re) (n : ℕ) : s₀ + 2 * ((n + 1 : ℕ) : ℂ) + 1 ≠ 0 := by
  intro h0; have := congrArg Complex.re h0; simp at this; have := n.cast_nonneg (α := ℝ); linarith

/-- `ρ*(s_K) → 0` from `y_K → 1`. -/
theorem tendsto_rho {c χ : ℝ} (hc : 0 < c) {s₀ : ℂ} (hre : 0 < s₀.re)
    (hy : Tendsto (fun k : ℕ => rhoStar c χ (s₀ + 2 * k) * (s₀ + 2 * k + 2) / c) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => rhoStar c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ))) atTop (𝓝 0) := by
  have hy' := hy.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : ℕ => (c : ℂ) / (s₀ + 2 * ((n + 1 : ℕ) : ℂ) + 2)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 := tendsto_norm_line (s₀ + 2)
    have := (tendsto_const_nhds (x := c)).div_atTop h2
    refine this.congr fun n => ?_
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le]; congr 2; ring
  have := hy'.mul hinv
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  have hne := line_ne hre n 2 (by norm_num)
  push_cast at hne
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [Function.comp]
  push_cast
  field_simp

/-- `log p(s_K) → 0` and `log(1 + r(s_K)) → log 2`. -/
theorem tendsto_logs {c χ : ℝ} (hc : 0 < c) {s₀ : ℂ} (hre : 0 < s₀.re)
    (hy : Tendsto (fun k : ℕ => rhoStar c χ (s₀ + 2 * k) * (s₀ + 2 * k + 2) / c) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => Complex.log (pp c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ)))) atTop (𝓝 0)
      ∧ Tendsto (fun n : ℕ => Complex.log (1 + rr (s₀ + 2 * ((n + 1 : ℕ) : ℂ)))) atTop (𝓝 (Complex.log 2)) := by
  have hρ := tendsto_rho hc hre hy
  -- `r → 1`
  have hr : Tendsto (fun n : ℕ => rr (s₀ + 2 * ((n + 1 : ℕ) : ℂ))) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℂ) / (s₀ + 2 * ((n + 1 : ℕ) : ℂ) + 1)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_norm_line (s₀ + 1))
      refine this.congr fun n => ?_
      rw [norm_div, norm_one]; congr 2; ring
    have := (tendsto_const_nhds (x := (1 : ℂ))).add hinv
    rw [add_zero] at this
    refine this.congr fun n => ?_
    have hne := line_ne1 hre n
    unfold rr
    rw [show s₀ + 2 * ((n + 1 : ℕ) : ℂ) + 2 = (s₀ + 2 * ((n + 1 : ℕ) : ℂ) + 1) + 1 by ring, add_div,
      div_self hne]
  have hp : Tendsto (fun n : ℕ => pp c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ))) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ))).add (hr.mul (hρ.pow 2))
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at this
    exact this
  constructor
  · have hl := (continuousAt_clog (x := (1 : ℂ)) (by simp [mem_slitPlane_iff])).tendsto.comp hp
    rwa [Complex.log_one] at hl
  · have h2 := (tendsto_const_nhds (x := (1 : ℂ))).add hr
    rw [show (1 : ℂ) + 1 = 2 by norm_num] at h2
    exact (continuousAt_clog (x := (2 : ℂ)) (by simp [mem_slitPlane_iff])).tendsto.comp h2

/-- `s mel(s)` ratio: `mel(s₀ + 2K)/mel(s₀′ + 2K) → 1` when `s₀ − s₀′` is fixed. -/
theorem tendsto_mel_ratio (c : ℝ) {s₀ s₀' : ℂ} (hs : 0 < s₀.re) (hs' : 0 < s₀'.re) :
    Tendsto (fun n : ℕ => mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * ((n + 1 : ℕ) : ℂ))
      / mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀' + 2 * ((n + 1 : ℕ) : ℂ))) atTop (𝓝 1) := by
  have hne : (Cvs.Prolate.EvenRungsByIndex.rung c 0 1 : ℂ) ≠ 0 := by
    exact_mod_cast Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)
  have h1 := (Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c hs).comp (tendsto_add_atTop_nat 1)
  have h2 := (Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c hs').comp (tendsto_add_atTop_nat 1)
  -- `s′/s → 1`
  have hq : Tendsto (fun n : ℕ => (s₀' + 2 * ((n + 1 : ℕ) : ℂ)) / (s₀ + 2 * ((n + 1 : ℕ) : ℂ))) atTop (𝓝 1) := by
    have hd : Tendsto (fun n : ℕ => (s₀' - s₀) / (s₀ + 2 * ((n + 1 : ℕ) : ℂ))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have := (tendsto_const_nhds (x := ‖s₀' - s₀‖)).div_atTop (tendsto_norm_line s₀)
      exact this.congr fun n => by rw [norm_div]
    have := (tendsto_const_nhds (x := (1 : ℂ))).add hd
    rw [add_zero] at this
    refine this.congr fun n => ?_
    have hn := line_ne0 hs n
    field_simp; ring
  have := ((h1.div h2 hne).mul hq)
  rw [div_self hne, one_mul] at this
  refine this.congr' ?_
  have hev : ∀ᶠ n : ℕ in atTop, mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀' + 2 * ((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    filter_upwards [h2.eventually_ne hne] with n hn h0
    simp only [Function.comp] at hn
    exact hn (by rw [h0, mul_zero])
  filter_upwards [hev] with n hn
  have hs0 := line_ne0 hs n
  have hs0' := line_ne0 hs' n
  simp only [Pi.div_apply, Function.comp_apply]
  field_simp

/-- **`Q_K → 1`.** -/
theorem tendsto_Q {ε ε' c z : ℝ} (hz : 0 ≤ z) (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + I * z))
    (h' : Hyp ε' c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2 : ℂ)) :
    Tendsto (fun n : ℕ => Pk c ((1 / 2 : ℂ) + I * z) (n + 1) / Pk c (1 / 2 : ℂ) (n + 1)
      * Complex.exp (Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ))
        - Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + I * z + 2 * ((n + 1 : ℕ) : ℂ)))) atTop (𝓝 1) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  set s₀ : ℂ := (1 / 2 : ℂ) + I * z
  have hc := h.c_pos
  have hre : 0 < s₀.re := by simp [s₀]
  have hre' : 0 < (1 / 2 : ℂ).re := by norm_num
  set A : ℂ := I * z / 2
  set x : ℕ → ℝ := fun n => 2 + 2 * (n + 1 : ℕ)
  -- the six factors
  have F1 := tendsto_mel_ratio c hre hre'
  have F2 := Cvs.Prolate.Mellin.TwoLinesAgreeComplex.tendsto_main hc z
  set corr : ℕ → ℂ := fun n => ((x n : ℝ) : ℂ) / (2 * Sq c (x n) * (Sq c (x n) + 2 * c))
  set R : ℕ → ℂ := fun n => Gh c ((x n : ℂ) + I * z) - Gh c (x n) - I * z * gh c (x n)
  have hcorr : Tendsto corr atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun n : ℕ => 1 / (2 * x n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_xn.const_mul_atTop (by norm_num))
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
    exact Cvs.Prolate.Mellin.WkbPhaseVerticalFar.norm_corr_le hc (by simp only [x]; positivity)
  have hev : ∀ᶠ n : ℕ in atTop, z + c + 1 ≤ x n := tendsto_xn.eventually_ge_atTop _
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ (tendsto_bound (13 * z ^ 2) z)
    filter_upwards [hev] with n hn
    have := (Cvs.Prolate.Mellin.WkbPhaseVerticalFar.vertical hc hz hn).2
    simp only [R]
    refine this.trans (le_of_eq ?_)
    ring
  have hgh : Tendsto (fun n : ℕ => gh c ((x n : ℂ) + I * z) - gh c (x n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ (tendsto_bound (13 * z) z)
    filter_upwards [hev] with n hn
    have := (Cvs.Prolate.Mellin.WkbPhaseVerticalFar.vertical hc hz hn).1
    refine this.trans (le_of_eq ?_)
    ring
  have F3 : Tendsto (fun n => Complex.exp (A * corr n - 1 / 2 * R n)) atTop (𝓝 1) := by
    have := ((hcorr.const_mul A).sub (hR.const_mul (1 / 2 : ℂ))).cexp
    simpa using this
  have F4 : Tendsto (fun n => Complex.exp (1 / 2 * (gh c ((x n : ℂ) + I * z) - gh c (x n)))) atTop (𝓝 1) := by
    have := (hgh.const_mul (1 / 2 : ℂ)).cexp
    simpa using this
  obtain ⟨hpA, hrA⟩ := tendsto_logs hc hre (Cvs.Prolate.Mellin.PastTurningStepErrors.tendsto_y h)
  obtain ⟨hpB, hrB⟩ := tendsto_logs hc hre' (Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_y h')
  have F5 : Tendsto (fun n : ℕ => Complex.exp (1 / 2 * (Complex.log (pp c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ)))
      - Complex.log (pp c χ ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)))))) atTop (𝓝 1) := by
    have := ((hpA.sub hpB).const_mul (1 / 2 : ℂ)).cexp
    simpa using this
  have F6 : Tendsto (fun n : ℕ => Complex.exp (1 / 2 * (Complex.log (1 + rr ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)))
      - Complex.log (1 + rr (s₀ + 2 * ((n + 1 : ℕ) : ℂ)))))) atTop (𝓝 1) := by
    have := ((hrB.sub hrA).const_mul (1 / 2 : ℂ)).cexp
    simpa using this
  have hall := ((((F1.mul F2).mul F3).mul F4).mul F5).mul F6
  simp only [mul_one] at hall
  refine hall.congr fun n => ?_
  -- the exact factorisation
  have hu' : (1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ) + 3 / 2 = ((x n : ℝ) : ℂ) := by simp only [x]; push_cast; ring
  have hu : s₀ + 2 * ((n + 1 : ℕ) : ℂ) + 3 / 2 = ((x n : ℝ) : ℂ) + I * z := by simp only [x, s₀]; push_cast; ring
  have hxa : (((2 + 2 * (n + 1 : ℕ) : ℝ) : ℂ)) / (2 * c) = ((x n : ℝ) : ℂ) / (2 * c) := rfl
  have hgx : gh c (x n) = -ash (((x n : ℝ) : ℂ) / (2 * c)) - corr n := by simp only [corr]; unfold gh; ring
  have hGh : Gh c ((x n : ℂ) + I * z) = Gh c (x n) + I * z * gh c (x n) + R n := by simp only [R]; ring
  set lpA := Complex.log (pp c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ)))
  set lpB := Complex.log (pp c χ ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)))
  set lrA := Complex.log (1 + rr (s₀ + 2 * ((n + 1 : ℕ) : ℂ)))
  set lrB := Complex.log (1 + rr ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)))
  have key : Complex.exp (I * z / 2 * ash (((2 + 2 * (n + 1 : ℕ) : ℝ) : ℂ) / (2 * c)))
      * Complex.exp (A * corr n - 1 / 2 * R n) * Complex.exp (1 / 2 * (gh c ((x n : ℂ) + I * z) - gh c (x n)))
      * Complex.exp (1 / 2 * (lpA - lpB)) * Complex.exp (1 / 2 * (lrB - lrA))
      = Complex.exp (Psi c χ ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)) - Psi c χ (s₀ + 2 * ((n + 1 : ℕ) : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold Psi
    rw [hu', hu, hGh, hxa, hgx]
    simp only [A]
    ring
  have hmel : Pk c s₀ (n + 1) / Pk c (1 / 2 : ℂ) (n + 1)
      = mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * ((n + 1 : ℕ) : ℂ)) / mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ))
        * (mg c ((1 / 2 : ℂ) + 2 * ((n + 1 : ℕ) : ℂ)) / mg c (s₀ + 2 * ((n + 1 : ℕ) : ℂ))) := by
    unfold Pk lawRatio; simp only [div_eq_mul_inv, mul_inv, inv_inv]; ring
  rw [hmel, ← key]
  ring

end Cvs.Prolate.Mellin.LineConstantRatioLimit
