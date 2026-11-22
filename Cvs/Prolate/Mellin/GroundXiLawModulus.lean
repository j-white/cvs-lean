import Mathlib
import Cvs.Prolate.EvenRungKatoTemple
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.HermiteTrialResiduals
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.GroundRatioLineModulus
import Cvs.Prolate.Mellin.GroundRatioStepErrors
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.NearRegionBootstrap
import Cvs.Prolate.Mellin.NearRegionForcingSize
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.TwoLinesAgreeModulus
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Prolate.Mellin.WkbPhaseLineStart

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Ξ law for the ground prolate, in modulus

For `0 < ε ≤ 1/16`, under explicit largeness conditions on `c`, and `|z| ≤ (2 − ε)c` with `sin θ = z/(2c)`:
`|log‖P₀(½ + iz)‖ − log‖P₀(½)‖ − (c(θ sin θ + cos θ − 1) − ½ log cos θ − ¼ log((1 + cos θ)/2))|
  ≤ 2E(ε, c) + 3(2γ + 2/c)/ε + 6G₁`.
-/

noncomputable section

open Filter Topology Complex

namespace Cvs.Prolate.Mellin.GroundXiLawModulus
open Cvs.ZeroCounting

open Cvs.Prolate.Mellin.LawRatioRecurrence Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.TrueRatioDownwardStep Cvs.Prolate.Mellin.NearRegionForcingSize Cvs.Prolate.Mellin.NearRegionBootstrap Cvs.Prolate.Mellin.GroundRatioStepErrors Cvs.Prolate.Mellin.WkbPhaseAntiderivative Cvs.Prolate.Mellin.FrozenForcingIdentities Cvs.Prolate.Mellin.GroundRatioLineModulus Cvs.Prolate.Mellin.TwoLinesAgreeModulus Cvs.Prolate.Mellin.WkbPhaseLineStart

/-- The law. -/
def law (c z : ℝ) : ℝ :=
  c * (Real.arcsin (z / (2 * c)) * Real.sin (Real.arcsin (z / (2 * c))) + Real.cos (Real.arcsin (z / (2 * c))) - 1)
    - 1 / 2 * Real.log (Real.cos (Real.arcsin (z / (2 * c))))
    - 1 / 4 * Real.log ((1 + Real.cos (Real.arcsin (z / (2 * c)))) / 2)

/-- The largeness conditions on `c`. -/
structure Large (ε c : ℝ) : Prop where
  hε : 0 < ε
  hε16 : ε ≤ 1 / 16
  hc : 64 / ε ^ 2 ≤ c
  hc7 : 7500 ≤ c
  hc5 : 100000 / ε ^ 2 ≤ c
  hs1 : 40 / 9 * Λc ε c * Γc c * Tc c ≤ 1
  hs2 : 2 * Γc c * Λc ε c ≤ 1 / 10
  hγ : 2 * gam ε c ≤ 1
  hη : 2 * gam ε c + 2 / c ≤ ε / 4

/-- The region hypothesis on the critical line. -/
theorem Large.hyp {ε c : ℝ} (L : Large ε c) {z : ℝ} (hz : |z| ≤ (2 - ε) * c) :
    Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + I * z) := by
  have h200 : 200 ≤ c := by linarith [L.hc7]
  have hl := Cvs.Prolate.EvenRungKatoTemple.abs_lev_zero_sub_le h200
  have hmu : Cvs.Prolate.HermiteTrialResiduals.mu c 0 = c - 3 / 4 := by unfold Cvs.Prolate.HermiteTrialResiduals.mu; norm_num
  rw [hmu] at hl
  have hc0 : 0 < c := by linarith
  have h1c : 1 / c ≤ 1 / 4 := by rw [div_le_div_iff₀ hc0 (by norm_num)]; linarith
  have := abs_le.mp hl
  exact
    { hε := L.hε
      hε1 := by linarith [L.hε16]
      hc := L.hc
      hχ0 := by linarith
      hχ1 := by linarith
      hre := by simp
      him := by simpa using hz }

set_option maxHeartbeats 1000000 in
/-- **The Ξ law for the ground prolate, in modulus, with explicit error.** -/
theorem xi_law_bound {ε c : ℝ} (L : Large ε c) {z : ℝ} (hz : |z| ≤ (2 - ε) * c) :
    |Real.log ‖lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + I * z)‖ - Real.log ‖lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (1 / 2)‖
      - law c z| ≤ 2 * Etot ε c + 3 * (2 * gam ε c + 2 / c) / ε + 6 * G1 ε c := by
  have hε := L.hε
  have hc0 : 0 < c := by linarith [L.hc7]
  have hc1 : 1 ≤ c := by linarith [L.hc7]
  have h := L.hyp hz
  have h' : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2 : ℂ) := by simpa using L.hyp (z := 0) (by simp; nlinarith [L.hε16])
  have S : Std ε c ((1 / 2 : ℂ) + I * z) := ⟨h, L.hε16, L.hc7, L.hs1, L.hs2⟩
  have S' : Std ε c (1 / 2 : ℂ) := ⟨h', L.hε16, L.hc7, L.hs1, L.hs2⟩
  set s₀ : ℂ := (1 / 2 : ℂ) + I * z
  set s₀' : ℂ := (1 / 2 : ℂ)
  -- the constant quantity
  set Q := Real.log ‖Pk c s₀ 0‖ - Real.log ‖Pk c s₀' 0‖
    - ((-(1 / 2) * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀‖ - Real.log ‖1 + rr s₀‖) + 1 / 2 * (Gh c (s₀ + 3 / 2) - gh c (s₀ + 3 / 2)).re)
      - (-(1 / 2) * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀'‖ - Real.log ‖1 + rr s₀'‖)
        + 1 / 2 * (Gh c (s₀' + 3 / 2) - gh c (s₀' + 3 / 2)).re)) with hQd
  -- for every large `K`
  have hK : ∀ K : ℕ, Jn c s₀ + 1 ≤ K → Jn c s₀' + 1 ≤ K →
      |Q - ((Real.log ‖Pk c s₀ K‖ + 1 / 2 * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * K)‖ - Real.log ‖1 + rr (s₀ + 2 * K)‖)
          - 1 / 2 * (Gh c (s₀ + 3 / 2 + 2 * K) - gh c (s₀ + 3 / 2 + 2 * K)).re)
        - (Real.log ‖Pk c s₀' K‖ + 1 / 2 * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀' + 2 * K)‖ - Real.log ‖1 + rr (s₀' + 2 * K)‖)
          - 1 / 2 * (Gh c (s₀' + 3 / 2 + 2 * K) - gh c (s₀' + 3 / 2 + 2 * K)).re))|
        ≤ 2 * Etot ε c + (1 + 12 / Real.sqrt ε) * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ K‖ + (1 + 12 / Real.sqrt ε) * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀' K‖ := by
    intro K h1 h2
    rw [hQd]
    have f1 := Std.line_formula S L.hc5 K h1
    have f2 := Std.line_formula S' L.hc5 K h2
    rw [abs_le] at f1 f2 ⊢
    constructor <;> nlinarith [f1.1, f1.2, f2.1, f2.2]
  -- pass to the limit
  set TD := fun K : ℕ => (Real.log ‖Pk c s₀ K‖ + 1 / 2 * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * K)‖ - Real.log ‖1 + rr (s₀ + 2 * K)‖)
          - 1 / 2 * (Gh c (s₀ + 3 / 2 + 2 * K) - gh c (s₀ + 3 / 2 + 2 * K)).re)
        - (Real.log ‖Pk c s₀' K‖ + 1 / 2 * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀' + 2 * K)‖ - Real.log ‖1 + rr (s₀' + 2 * K)‖)
          - 1 / 2 * (Gh c (s₀' + 3 / 2 + 2 * K) - gh c (s₀' + 3 / 2 + 2 * K)).re)
  have hT : Tendsto TD atTop (𝓝 0) := tendsto_TK_sub h h'
  have hv1 : Tendsto (fun K => ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ K‖) atTop (𝓝 0) := by simpa using (tendsto_vk h).norm
  have hv2 : Tendsto (fun K => ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀' K‖) atTop (𝓝 0) := by simpa using (tendsto_vk h').norm
  have hlim : Tendsto (fun K : ℕ => 2 * Etot ε c + (1 + 12 / Real.sqrt ε) * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ K‖
      + (1 + 12 / Real.sqrt ε) * ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀' K‖ + |TD K|) atTop (𝓝 (2 * Etot ε c)) := by
    have := (((tendsto_const_nhds (x := 2 * Etot ε c)).add (hv1.const_mul (1 + 12 / Real.sqrt ε))).add
      (hv2.const_mul (1 + 12 / Real.sqrt ε))).add hT.abs
    simpa using this
  have hQ : |Q| ≤ 2 * Etot ε c := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (Jn c s₀ + 1), eventually_ge_atTop (Jn c s₀' + 1)] with K h1 h2
    have a1 : |Q - TD K| ≤ _ := hK K h1 h2
    have a2 := abs_sub_abs_le_abs_sub Q (TD K)
    have a3 := abs_nonneg (TD K)
    have : |Q| ≤ |Q - TD K| + |TD K| := by linarith
    linarith
  -- the start-of-line closed forms
  have hph := phase_start hε (by linarith [L.hε16]) hc1 hz
  have hp1 := log_pp_start (by linarith [L.hε16]) h L.hγ L.hη
  have h0' : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + I * ((0 : ℝ) : ℂ)) := by
    have e : ((1 / 2 : ℂ) + I * ((0 : ℝ) : ℂ)) = 1 / 2 := by simp
    rw [e]; exact h'
  have hp0 := log_pp_start (z := 0) (by linarith [L.hε16]) h0' L.hγ L.hη
  simp only [Complex.ofReal_zero, mul_zero, add_zero, zero_div, Real.arcsin_zero, Real.cos_zero, Real.log_one,
    sub_zero] at hp0
  have hP0 : Pk c s₀ 0 = lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) s₀ := by unfold Pk; simp
  have hP0' : Pk c s₀' 0 = lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) s₀' := by unfold Pk; simp
  rw [hQd, hP0, hP0'] at hQ
  unfold law
  rw [abs_le] at hQ hph hp1 hp0 ⊢
  have e3 : 3 * (2 * gam ε c + 2 / c) / ε = 1 / 2 * (3 * (2 * gam ε c + 2 / c) / ε)
      + 1 / 2 * (3 * (2 * gam ε c + 2 / c) / ε) := by ring
  constructor <;> nlinarith [hQ.1, hQ.2, hph.1, hph.2, hp1.1, hp1.2, hp0.1, hp0.2]

end Cvs.Prolate.Mellin.GroundXiLawModulus
