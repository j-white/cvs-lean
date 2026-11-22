import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.GroundRatioLineModulus
import Cvs.Prolate.Mellin.GroundXiLawModulus
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningForcingStart
import Cvs.Prolate.Mellin.PastTurningLineConstants
import Cvs.Prolate.Mellin.PastTurningRatioComplex
import Cvs.Prolate.Mellin.PastTurningStartTaylor
import Cvs.Prolate.Mellin.RealLineRatioComplex
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis
import Cvs.Prolate.Mellin.WkbPhaseLineStart
import Cvs.Upstream.ArsinhLipschitzStrip
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The complex Ξ law past the turning point

With `w = z/(2c) = cosh φ`, `s = √(w² − 1) = sinh φ`, `φ = arcosh w`:
`L(c, z) = c(πw/2 − 1) − ½ log s + i(c(s − wφ) − π/4) − ¼ log((1 + is)/2)`. Under `GroundXiLawModulus`'s largeness
conditions, `z ≥ (2 + ε)c`, `c ≥ 108/ε`, `εc² ≥ 2`: `Ψ(½ + iz) − Ψ(½) = L(c, z) + δ` with `|δ| ≤ E_s(ε, c)`,
and by Cvs.Prolate.Mellin.PastTurningLineConstants `|P(½ + iz)/P(½) · e^{−L(c, z)} − 1| ≤ 2E + (1 + 2E)·2E_s`, `E = E_U + E`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.ComplexXiLawPastTurning
open Cvs.ZeroCounting

open Cvs.Prolate.Mellin.LawRatioRecurrence (lawRatio)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)
open Cvs.Upstream.ComplexArsinhStrip (ash)
open Cvs.Prolate.Mellin.WkbPhaseAntiderivative (Sq Gh gh)
open Cvs.Prolate.Mellin.FrozenForcingIdentities (rr pp)
open Cvs.Prolate.Mellin.GroundXiLawModulus (Large)
open Cvs.Prolate.Mellin.PastTurningRatioComplex (Psi EU)

/-- **The complex law past the turning point.** -/
def lawU (c z : ℝ) : ℂ :=
  ((c * (Real.pi / 2 * (z / (2 * c)) - 1) - 1 / 2 * Real.log (Real.sqrt ((z / (2 * c)) ^ 2 - 1)) : ℝ) : ℂ)
    + I * ((c * (Real.sqrt ((z / (2 * c)) ^ 2 - 1) - z / (2 * c) * Real.arcosh (z / (2 * c))) - Real.pi / 4 : ℝ) : ℂ)
    - 1 / 4 * Complex.log ((1 + I * Real.sqrt ((z / (2 * c)) ^ 2 - 1)) / 2)

variable {ε c : ℝ}

/-- **`Ψ(½) ≈ c − ¼ log 4c`.** -/
theorem psi_half (L : Large ε c) :
    ‖Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2) - ((c - 1 / 4 * Real.log (4 * c) : ℝ) : ℂ)‖
      ≤ 3 * Cvs.Prolate.Mellin.WkbPhaseLineStart.G1 ε c + 3 * (2 * Cvs.Prolate.Mellin.WkbPhaseLineStart.gam ε c + 2 / c) / (2 * ε) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hε := L.hε
  have hc0 : 0 < c := by linarith [L.hc7]
  have hc1 : 1 ≤ c := by linarith [L.hc7]
  have h0 : Hyp ε c χ ((1 / 2 : ℂ) + I * ((0 : ℝ) : ℂ)) := L.hyp (z := 0) (by simp; nlinarith [L.hε16])
  obtain ⟨t1, t2⟩ := Cvs.Prolate.Mellin.WkbPhaseLineStart.taylor_start hε (by linarith [L.hε16]) hc1 (z := 0)
    (by simp; nlinarith [L.hε16])
  have hp := Cvs.Prolate.Mellin.WkbPhaseLineStart.log_pp_start (by linarith [L.hε16]) h0 L.hγ L.hη
  simp only [Complex.ofReal_zero, mul_zero, add_zero, zero_div, Real.arcsin_zero, Real.cos_zero,
    Real.log_one, sub_zero] at hp t1 t2
  -- the values at `0`
  have hG0 : Gh c 0 = ((2 * c - 1 / 2 * Real.log (4 * c) : ℝ) : ℂ) := by
    have := Cvs.Prolate.Mellin.WkbPhaseAntiderivative.Gh_I_mul hc0 (z := 0) (by simp; linarith)
    simp only [Complex.ofReal_zero, mul_zero, zero_div, Real.arcsin_zero, Real.cos_zero] at this
    rw [this]; congr 1; ring_nf
  have hg0 : gh c 0 = 0 := by
    unfold gh; rw [zero_div, Cvs.Upstream.ArsinhLipschitzStrip.ash_zero]; simp
  -- the forcing constant at `½` is real
  obtain ⟨y, hy1, hyp⟩ := Cvs.Prolate.Mellin.RealLineRatioComplex.pp_eq (χ := χ) hc0 (x := 1 / 2) (by norm_num)
  have hyp' : pp c χ (1 / 2 : ℂ) = (y : ℂ) := by simpa using hyp
  have hr : 1 + rr (1 / 2 : ℂ) = ((1 + (1 / 2 + 2) / (1 / 2 + 1) : ℝ) : ℂ) := by unfold rr; push_cast; ring
  have hlog : Complex.log (pp c χ (1 / 2 : ℂ)) - Complex.log (1 + rr (1 / 2 : ℂ))
      = ((Real.log ‖pp c χ (1 / 2 : ℂ)‖ - Real.log ‖1 + rr (1 / 2 : ℂ)‖ : ℝ) : ℂ) := by
    rw [hyp', hr, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      Real.norm_of_nonneg (by positivity), Complex.ofReal_sub, Complex.ofReal_log (by linarith),
      Complex.ofReal_log (by positivity)]
  have hlogn : ‖Complex.log (pp c χ (1 / 2 : ℂ)) - Complex.log (1 + rr (1 / 2 : ℂ))‖
      ≤ 3 * (2 * Cvs.Prolate.Mellin.WkbPhaseLineStart.gam ε c + 2 / c) / ε := by
    rw [hlog, Complex.norm_real, Real.norm_eq_abs]; simpa using hp
  -- assemble
  have hu : (1 / 2 : ℂ) + 3 / 2 = I * ((0 : ℝ) : ℂ) + 2 := by simp; norm_num
  have e : Psi c χ (1 / 2) - ((c - 1 / 4 * Real.log (4 * c) : ℝ) : ℂ)
      = 1 / 2 * (Gh c (I * ((0 : ℝ) : ℂ) + 2) - Gh c (I * ((0 : ℝ) : ℂ)) - 2 * gh c (I * ((0 : ℝ) : ℂ)))
        - 1 / 2 * (gh c (I * ((0 : ℝ) : ℂ) + 2) - gh c (I * ((0 : ℝ) : ℂ)))
        - 1 / 2 * (Complex.log (pp c χ (1 / 2 : ℂ)) - Complex.log (1 + rr (1 / 2 : ℂ))) := by
    unfold Psi
    rw [hu]
    simp only [Complex.ofReal_zero, mul_zero, zero_add]
    rw [hG0, hg0]
    push_cast; ring
  rw [e]
  simp only [Complex.ofReal_zero, mul_zero, zero_add] at t1 t2 ⊢
  have n1 : ‖1 / 2 * (Gh c 2 - Gh c 0 - 2 * gh c 0)‖ ≤ 2 * Cvs.Prolate.Mellin.WkbPhaseLineStart.G1 ε c := by
    rw [norm_mul]; norm_num; linarith
  have n2 : ‖1 / 2 * (gh c 2 - gh c 0)‖ ≤ Cvs.Prolate.Mellin.WkbPhaseLineStart.G1 ε c := by
    rw [norm_mul]; norm_num; linarith
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have n3 : ‖1 / 2 * (Complex.log (pp c χ (1 / 2 : ℂ)) - Complex.log (1 + rr (1 / 2 : ℂ)))‖
      ≤ 3 * (2 * Cvs.Prolate.Mellin.WkbPhaseLineStart.gam ε c + 2 / c) / (2 * ε) := by
    rw [norm_mul, hhalf]
    calc 1 / 2 * ‖Complex.log (pp c χ (1 / 2 : ℂ)) - Complex.log (1 + rr (1 / 2 : ℂ))‖
        ≤ 1 / 2 * (3 * (2 * Cvs.Prolate.Mellin.WkbPhaseLineStart.gam ε c + 2 / c) / ε) := by gcongr
      _ = _ := by field_simp
  have := norm_sub_le (1 / 2 * (Gh c 2 - Gh c 0 - 2 * gh c 0) - 1 / 2 * (gh c 2 - gh c 0))
    (1 / 2 * (Complex.log (pp c χ (1 / 2 : ℂ)) - Complex.log (1 + rr (1 / 2 : ℂ))))
  have := norm_sub_le (1 / 2 * (Gh c 2 - Gh c 0 - 2 * gh c 0)) (1 / 2 * (gh c 2 - gh c 0))
  linarith

/-- The closed form of `Ψ(½ + iz)`. -/
def psiUp (c z : ℝ) : ℂ :=
  1 / 2 * (-(I * z) * ((Real.arcosh (z / (2 * c)) : ℂ) + I * (Real.pi / 2))
      + I * ((2 * c * Real.sqrt ((z / (2 * c)) ^ 2 - 1) : ℝ) : ℂ)
      - 1 / 2 * ((Real.log (2 * c) : ℝ) + Complex.log (1 + I * Real.sqrt ((z / (2 * c)) ^ 2 - 1))))
    + 1 / 2 * (-((Real.arcosh (z / (2 * c)) : ℂ) + I * (Real.pi / 2)))
    - 1 / 2 * ((Real.log (Real.sqrt ((z / (2 * c)) ^ 2 - 1)) : ℂ) - Real.arcosh (z / (2 * c)))

/-- **`Ψ(½ + iz) ≈ psiUp`.** -/
theorem psi_up (L : Large ε c) {z : ℝ} (hz : (2 + ε) * c ≤ z) (hcε : 108 / ε ≤ c) (hεc : 2 ≤ ε * c ^ 2) :
    ‖Psi c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + I * z) - psiUp c z‖
      ≤ 3 * (13 / (2 * ε * Real.sqrt ε * c)) + 1 / (8 * Real.sqrt ε * c) + 41 / (ε * c) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hε := L.hε
  have hε1 : ε ≤ 1 := by linarith [L.hε16]
  have hc0 : 0 < c := by linarith [L.hc7]
  have h := Cvs.Prolate.Mellin.PastTurningLineConstants.Large.up L hz
  have hz2 : 2 * c < z := by nlinarith
  obtain ⟨t1, t2⟩ := Cvs.Prolate.Mellin.PastTurningStartTaylor.start hε hε1 hc0 hεc hz
  have hG := Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis.Gh_I_mul hc0 hz2.le
  have hg := Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis.gh_I_mul hc0 hz2.le
  have hcorr := Cvs.Prolate.Mellin.WkbPhaseImaginaryAxis.norm_corr_I hc0 hz2
  have hp := Cvs.Prolate.Mellin.PastTurningForcingStart.log_pp_start h hcε
  set corr := I * (z : ℂ) / (2 * Sq c (I * z) * (Sq c (I * z) + 2 * c))
  set e1 := Gh c (I * z + 2) - Gh c (I * z) - 2 * gh c (I * z)
  set e2 := gh c (I * z + 2) - gh c (I * z)
  set e3 := Complex.log (pp c χ ((1 / 2 : ℂ) + I * z)) - Complex.log (1 + rr ((1 / 2 : ℂ) + I * z))
    - ((Real.log (Real.sqrt ((z / (2 * c)) ^ 2 - 1)) : ℂ) - Real.arcosh (z / (2 * c)))
  have hu : (1 / 2 : ℂ) + I * z + 3 / 2 = I * z + 2 := by ring
  have e : Psi c χ ((1 / 2 : ℂ) + I * z) - psiUp c z = 1 / 2 * e1 - 1 / 2 * e2 - 1 / 2 * corr - 1 / 2 * e3 := by
    have hGI : Gh c (I * z + 2) = e1 + Gh c (I * z) + 2 * gh c (I * z) := by simp only [e1]; ring
    have hgI : gh c (I * z + 2) = e2 + gh c (I * z) := by simp only [e2]; ring
    have hpI : Complex.log (pp c χ ((1 / 2 : ℂ) + I * z)) = e3 + Complex.log (1 + rr ((1 / 2 : ℂ) + I * z))
        + ((Real.log (Real.sqrt ((z / (2 * c)) ^ 2 - 1)) : ℂ) - Real.arcosh (z / (2 * c))) := by simp only [e3]; ring
    unfold Psi psiUp
    rw [hu, hGI, hgI, hpI, hG, hg]
    ring
  rw [e]
  -- sizes
  have hw : 1 + ε / 2 ≤ z / (2 * c) := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have hsq : Real.sqrt ε ≤ Real.sqrt ((z / (2 * c)) ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
  have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hc1 : ‖corr‖ ≤ 1 / (4 * Real.sqrt ε * c) := by
    rw [hcorr]; apply one_div_le_one_div_of_le (by positivity)
    have := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * c by positivity); nlinarith
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have n1 : ‖1 / 2 * e1‖ ≤ 2 * (13 / (2 * ε * Real.sqrt ε * c)) := by rw [norm_mul, hhalf]; linarith
  have n2 : ‖1 / 2 * e2‖ ≤ 13 / (2 * ε * Real.sqrt ε * c) := by rw [norm_mul, hhalf]; linarith
  have n3 : ‖1 / 2 * corr‖ ≤ 1 / (8 * Real.sqrt ε * c) := by
    rw [norm_mul, hhalf]
    calc 1 / 2 * ‖corr‖ ≤ 1 / 2 * (1 / (4 * Real.sqrt ε * c)) := by gcongr
      _ = 1 / (8 * Real.sqrt ε * c) := by field_simp; ring
  have n4 : ‖1 / 2 * e3‖ ≤ 41 / (ε * c) := by
    rw [norm_mul, hhalf]
    calc 1 / 2 * ‖e3‖ ≤ 1 / 2 * (82 / (ε * c)) := by gcongr
      _ = 41 / (ε * c) := by field_simp; ring
  have := norm_sub_le (1 / 2 * e1 - 1 / 2 * e2 - 1 / 2 * corr) (1 / 2 * e3)
  have := norm_sub_le (1 / 2 * e1 - 1 / 2 * e2) (1 / 2 * corr)
  have := norm_sub_le (1 / 2 * e1) (1 / 2 * e2)
  linarith

/-- **The closed form**: `psiUp − (c − ¼ log 4c) = L(c, z)`. -/
theorem psiUp_sub (hc : 0 < c) {z : ℝ} :
    psiUp c z - ((c - 1 / 4 * Real.log (4 * c) : ℝ) : ℂ) = lawU c z := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  obtain ⟨w, rfl⟩ : ∃ w : ℝ, z = 2 * c * w := ⟨z / (2 * c), by field_simp⟩
  have hwz : 2 * c * w / (2 * c) = w := by field_simp
  set q := Real.sqrt (w ^ 2 - 1)
  have hne : (1 : ℂ) + I * q ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp at this
  have hlog2 : Complex.log ((1 + I * q) / 2) = (Real.log (1 / 2) : ℂ) + Complex.log (1 + I * q) := by
    rw [show (1 + I * (q : ℂ)) / 2 = (1 + I * q) * ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.log_mul_ofReal _ (by norm_num) _ hne]
  have h4c : Real.log (4 * c) = Real.log 2 + Real.log (2 * c) := by
    rw [show (4 : ℝ) * c = 2 * (2 * c) by ring, Real.log_mul (by norm_num) (by positivity)]
  have hhalf : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  unfold psiUp lawU
  rw [hwz, hlog2, hhalf, h4c]
  push_cast
  linear_combination (-(2 * (c : ℂ) * w) * Real.pi / 4) * I_sq

/-- The start-of-line budget. -/
def Es (ε c : ℝ) : ℝ :=
  3 * (13 / (2 * ε * Real.sqrt ε * c)) + 1 / (8 * Real.sqrt ε * c) + 41 / (ε * c)
    + (3 * Cvs.Prolate.Mellin.WkbPhaseLineStart.G1 ε c + 3 * (2 * Cvs.Prolate.Mellin.WkbPhaseLineStart.gam ε c + 2 / c) / (2 * ε))

/-- **The complex Ξ law past the turning point, with explicit error.** -/
theorem law_bound (L : Large ε c) {z : ℝ} (hz : (2 + ε) * c ≤ z) (hcε : 108 / ε ≤ c) (hεc : 2 ≤ ε * c ^ 2)
    (hE : EU ε c + Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c ≤ 1 / 2) (hS : Es ε c ≤ 1) :
    ‖lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + I * z) / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (1 / 2)
        * Complex.exp (-lawU c z) - 1‖
      ≤ 2 * (EU ε c + Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c)
        + (1 + 2 * (EU ε c + Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c)) * (2 * Es ε c) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hc0 : 0 < c := by linarith [L.hc7]
  set E := EU ε c + Cvs.Prolate.Mellin.GroundRatioLineModulus.Etot ε c
  set Ψ₀ := Psi c χ ((1 / 2 : ℂ) + I * z)
  set Ψh := Psi c χ (1 / 2)
  set W := lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + I * z) / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (1 / 2)
    * Complex.exp (-(Ψ₀ - Ψh))
  have hW : ‖W - 1‖ ≤ 2 * E := Cvs.Prolate.Mellin.PastTurningLineConstants.ratio_bound L hz hE
  set δ := (Ψ₀ - Ψh) - lawU c z
  have hδ : ‖δ‖ ≤ Es ε c := by
    have e : δ = (Ψ₀ - psiUp c z) - (Ψh - ((c - 1 / 4 * Real.log (4 * c) : ℝ) : ℂ)) := by
      simp only [δ]; rw [← psiUp_sub hc0 (z := z)]; ring
    rw [e]
    have a := psi_up L hz hcε hεc
    have b := psi_half L
    have := norm_sub_le (Ψ₀ - psiUp c z) (Ψh - ((c - 1 / 4 * Real.log (4 * c) : ℝ) : ℂ))
    unfold Es; linarith
  have hT : lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + I * z) / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (1 / 2)
      * Complex.exp (-lawU c z) = W * Complex.exp δ := by
    simp only [W, δ]; rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
  rw [hT]
  have hexp := Complex.norm_exp_sub_one_le (hδ.trans hS)
  have hWn : ‖W‖ ≤ 1 + 2 * E := by
    have := norm_le_norm_add_norm_sub' W 1
    rw [norm_one] at this; linarith
  calc ‖W * Complex.exp δ - 1‖ = ‖W * (Complex.exp δ - 1) + (W - 1)‖ := by ring_nf
    _ ≤ ‖W‖ * ‖Complex.exp δ - 1‖ + ‖W - 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ (1 + 2 * E) * (2 * Es ε c) + 2 * E := by
        have h2 : ‖Complex.exp δ - 1‖ ≤ 2 * Es ε c := hexp.trans (by linarith)
        have hE0 : 0 ≤ 1 + 2 * E := (norm_nonneg W).trans hWn
        exact add_le_add (mul_le_mul hWn h2 (norm_nonneg _) hE0) hW
    _ = _ := by ring

end Cvs.Prolate.Mellin.ComplexXiLawPastTurning
