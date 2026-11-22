import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenForcingLineSum
import Cvs.Prolate.Mellin.FrozenRootCanonicalLog
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootLogErrorSum
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.GroundRatioStepErrors
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.NearRegionForcingSize
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ground law ratio along one line, in modulus

Under the bootstrap conditions and `c ≥ 10⁵/ε²`, for `K > J`, with `u = s + 3/2`:
`log‖P(s₀)‖ = log‖P(s_K)‖ − ½ log‖p(s₀)/(1 + r(s₀))‖ + ½ log‖p(s_K)/(1 + r(s_K))‖
  + ½ Re(Ĝ(u₀) − ĝ(u₀)) − ½ Re(Ĝ(u_K) − ĝ(u_K)) + R` with `|R| ≤ E(ε, c) + (1 + 12/√ε)‖v_K‖`.
-/

noncomputable section

open Finset

namespace Cvs.Prolate.Mellin.GroundRatioLineModulus

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.NearRegionBetaStep Cvs.Prolate.Mellin.TrueRatioDownwardStep Cvs.Prolate.Mellin.NearRegionForcingSize Cvs.Prolate.Mellin.GroundRatioStepErrors Cvs.Prolate.Mellin.WkbPhaseAntiderivative Cvs.Prolate.Mellin.FrozenRootCanonicalLog Cvs.Prolate.Mellin.FrozenForcingIdentities Cvs.Prolate.Mellin.FrozenForcingLineSum

/-- The total one-line budget. -/
def Etot (ε c : ℝ) : ℝ :=
  E1 ε c + E2 ε c + 42 * (1 + 2 / Real.sqrt (3 * ε)) / (Real.sqrt (3 * ε) * c)
    + 160 / (ε / 4) ^ 5 * ((1 + Real.log (1 + c / 2)) / (2 * c))

variable {ε c : ℝ} {s₀ : ℂ}

/-- **The exact telescope in modulus.** -/
theorem Std.log_telescope (S : Std ε c s₀) (K : ℕ) :
    Real.log ‖Pk c s₀ 0‖ = Real.log ‖Pk c s₀ K‖
      + ∑ k ∈ range K, (Real.log ‖1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖
        - (gL c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k)).re) := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  induction K with
  | zero => simp
  | succ K ih =>
    rw [ih, Finset.sum_range_succ]
    have hP := (S.profile K).1
    have hP1 := (S.profile (K + 1)).1
    have hl := Cvs.Prolate.Mellin.StepAmplification.hyp_line S.h K
    have hρ := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.rho_ne hl
    have he := Hyp.exp_gL hl
    -- `P_K = (1 + v_K) P_{K+1}/ρ_K`
    have hv : 1 + vk c χ s₀ K = rhoStar c χ (s₀ + 2 * K) * Pk c s₀ K / Pk c s₀ (K + 1) := by
      unfold vk; ring
    have hv0 : 1 + vk c χ s₀ K ≠ 0 := by rw [hv]; exact div_ne_zero (mul_ne_zero hρ hP) hP1
    have hn : ‖Pk c s₀ K‖ = ‖Pk c s₀ (K + 1)‖ * ‖1 + vk c χ s₀ K‖ / Real.exp (gL c χ (s₀ + 2 * K)).re := by
      rw [← Complex.norm_exp, he, hv, norm_div, norm_mul]
      field_simp
      rfl
    rw [hn, Real.log_div (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul (norm_ne_zero_iff.mpr hP1) (norm_ne_zero_iff.mpr hv0)]
    ring

/-- **The one-line formula.** -/
theorem Std.line_formula (S : Std ε c s₀) (hc5 : 100000 / ε ^ 2 ≤ c) (K : ℕ) (hK : Jn c s₀ + 1 ≤ K) :
    |Real.log ‖Pk c s₀ 0‖ - Real.log ‖Pk c s₀ K‖
      - (-(1 / 2) * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀‖ - Real.log ‖1 + rr s₀‖)
        + 1 / 2 * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * K)‖ - Real.log ‖1 + rr (s₀ + 2 * K)‖)
        + 1 / 2 * (Gh c (s₀ + 3 / 2) - gh c (s₀ + 3 / 2)).re
        - 1 / 2 * (Gh c (s₀ + 3 / 2 + 2 * K) - gh c (s₀ + 3 / 2 + 2 * K)).re)|
      ≤ Etot ε c + (1 + 12 / Real.sqrt ε) * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ K‖ := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have h := S.h
  have hε := h.hε
  have hε4 : ε ≤ 1 / 4 := by linarith [S.hε16]
  have hc := h.c_pos
  rw [Std.log_telescope S K]
  -- (i) the step errors
  have i1 := S.sum_log_sub_le K hK
  have i1' : |∑ k ∈ range K, Real.log ‖1 + vk c χ s₀ k‖ - ∑ k ∈ range K, (betaf c χ (s₀ + 2 * k)).re|
      ≤ E1 ε c + (1 + 12 / Real.sqrt ε) * ‖vk c χ s₀ K‖ := by
    have e : ∑ k ∈ range K, Real.log ‖1 + vk c χ s₀ k‖ - ∑ k ∈ range K, (betaf c χ (s₀ + 2 * k)).re
        = (∑ k ∈ Ico 0 K, (Complex.log (1 + vk c χ s₀ k) - betaf c χ (s₀ + 2 * (k : ℂ)))).re := by
      rw [Finset.range_eq_Ico, Complex.re_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [Complex.sub_re, Complex.log_re]
    rw [e]; exact (Complex.abs_re_le_norm _).trans i1
  -- (ii) the forcing
  have i2 := Hyp.sum_re_betaf h hε4 hc5 K
  simp only [Nat.cast_zero, mul_zero, add_zero] at i2
  -- (iii) the frozen-root logarithms
  have i3 := Cvs.Prolate.Mellin.FrozenRootLogErrorSum.Hyp.sum_gL_sub_gh_le h hε4 K
  have i3' : |∑ k ∈ range K, (gL c χ (s₀ + 2 * k)).re - ∑ k ∈ range K, (gh c (s₀ + 3 / 2 + 2 * k)).re|
      ≤ 160 / (ε / 4) ^ 5 * ((1 + Real.log (1 + c / 2)) / (2 * c)) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun k _ => ?_) i3)
    rw [← Complex.sub_re, show s₀ + 3 / 2 + 2 * (k : ℂ) = s₀ + 2 * k + 3 / 2 by ring]
    exact Complex.abs_re_le_norm _
  have i4 := Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum.norm_sum_gh_sub_le hε h.hε1 h.hc (u₀ := s₀ + 3 / 2)
    (by simp; linarith [h.hre]) (by simpa using h.him) K
  have i4' : |∑ k ∈ range K, (gh c (s₀ + 3 / 2 + 2 * k)).re
      - (1 / 2 * (Gh c (s₀ + 3 / 2 + 2 * K) - Gh c (s₀ + 3 / 2))
        + 1 / 2 * (gh c (s₀ + 3 / 2) - gh c (s₀ + 3 / 2 + 2 * K))).re|
      ≤ 42 * (1 + 2 / Real.sqrt (3 * ε)) / (Real.sqrt (3 * ε) * c) := by
    rw [← Complex.re_sum, ← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans i4
  have hre : (1 / 2 * (Gh c (s₀ + 3 / 2 + 2 * K) - Gh c (s₀ + 3 / 2))
        + 1 / 2 * (gh c (s₀ + 3 / 2) - gh c (s₀ + 3 / 2 + 2 * K))).re
      = 1 / 2 * (Gh c (s₀ + 3 / 2 + 2 * K) - gh c (s₀ + 3 / 2 + 2 * K)).re
        - 1 / 2 * (Gh c (s₀ + 3 / 2) - gh c (s₀ + 3 / 2)).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re]; norm_num; ring
  rw [hre] at i4'
  rw [Finset.sum_sub_distrib]
  unfold Etot
  set X := ∑ k ∈ range K, Real.log ‖1 + vk c χ s₀ k‖
  set Y := ∑ k ∈ range K, (betaf c χ (s₀ + 2 * k)).re
  set Z := ∑ k ∈ range K, (gL c χ (s₀ + 2 * k)).re
  set W := ∑ k ∈ range K, (gh c (s₀ + 3 / 2 + 2 * k)).re
  rw [abs_le] at i1' i2 i3' i4' ⊢
  constructor <;> nlinarith [i1'.1, i1'.2, i2.1, i2.2, i3'.1, i3'.2, i4'.1, i4'.2]

end Cvs.Prolate.Mellin.GroundRatioLineModulus
