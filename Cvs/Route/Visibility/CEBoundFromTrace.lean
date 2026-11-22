import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.ConditionBWithoutCut
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Route.Visibility.ScalarTraceBudget
import Cvs.Upstream.InverseExcessPencilTop

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `CEBound` from the trace comparison, the trace limit and the top ceiling

The three analytic inputs as named Props: the comparison `cE ≤ μ* + 2a_tT_c/(1 − μ*T_c)`, an eventual bound
`T_c ≤ τ`, and the top ceiling `λ_t ≤ 3/4`, which follows from the even-index form of Landau's transition theorem.
`CEBound W̃` follows whenever `C₀∞(W̃)(μ* + 2ατ/(1 − μ*τ)) < 2` with `a_t ≤ α`; at `τ = 9/50`, `α = 5/3`, `W̃ = 57/60`.
-/

noncomputable section

open Real Set Filter Topology

namespace Cvs.Route.Visibility.CEBoundFromTrace
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (lam lamTop)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (muStar C0inf cE)
open Cvs.Prolate.Gram.CentralResolventTrace (Tc WellPosed aTop)

/-! ### The analytic inputs -/

/-- The trace comparison (B): eventually, when `T_c` is well posed and `μ*T_c < 1`,
`cE ≤ μ* + 2a_tT_c/(1 − μ*T_c)`. -/
def TraceComparison : Prop :=
  ∀ᶠ x : ℕ in atTop, WellPosed (2 * π * x) → muStar * Tc x < 1 →
    cE x ≤ muStar + 2 * aTop x * Tc x / (1 - muStar * Tc x)

/-- The excess form of (B): eventually `R ≤ 2a_tT_c/(1 − μ*T_c)` when `T_c` is well posed and `μ*T_c < 1`. -/
def ExcessComparison : Prop :=
  ∀ᶠ x : ℕ in atTop, WellPosed (2 * π * x) → muStar * Tc x < 1 →
    Cvs.Upstream.InverseExcessPencilTop.prolateExcess x ≤ 2 * aTop x * Tc x / (1 - muStar * Tc x)

/-- The trace limit (D) at level `τ`: eventually `T_c` is well posed and `T_c ≤ τ`. -/
def TraceBound (τ : ℝ) : Prop := ∀ᶠ x : ℕ in atTop, WellPosed (2 * π * x) ∧ Tc x ≤ τ

/-- The trace limit (D) used here: eventually `T_c` is well posed and `T_c ≤ 9/50`. -/
def TraceLimit : Prop := TraceBound (9 / 50)

/-- The top ceiling: eventually `λ_t ≤ 3/4`. -/
def TopCeiling : Prop := ∀ᶠ x : ℕ in atTop, lamTop x ≤ 3 / 4

/-- Landau's transition theorem (Landau 1985 overview, p. 211; Landau–Widom,
J. Math. Anal. Appl. 77 (1980) 469–481, Theorem 1) at even index `2k`, `T = c/π`:
`λ_{2⌊(2T + (b/π)log T)/2⌋} → 1/(1 + e^{πb})` for every fixed `b`. -/
def LandauTransition : Prop :=
  ∀ b : ℝ, Tendsto (fun c : ℝ => lamR c ⌊(2 * (c / π) + b / π * Real.log (c / π)) / 2⌋₊) atTop
    (𝓝 (1 / (1 + Real.exp (π * b))))

/-! ### The adapters -/

/-- The excess form of (B) gives (B). -/
theorem traceComparison_of_excess (h : ExcessComparison) : TraceComparison := by
  filter_upwards [h, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hR hx hW hT
  exact (Cvs.Upstream.InverseExcessPencilTop.cE_le_muTop_add_excess hx).trans (add_le_add (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_top_le hx) (hR hW hT))

/-- `2aT/(1 − mT) ≤ 2ατ/(1 − mτ)` for `0 ≤ a ≤ α`, `T ≤ τ`, `0 ≤ τ`, `0 < m` and `mτ < 1`. -/
theorem budget_mono {m a α T τ : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (haα : a ≤ α) (hT : T ≤ τ) (hτ0 : 0 ≤ τ)
    (hτ1 : m * τ < 1) : 2 * a * T / (1 - m * T) ≤ 2 * α * τ / (1 - m * τ) := by
  have hd : 0 < 1 - m * τ := by linarith
  have hdT : 1 - m * τ ≤ 1 - m * T := by nlinarith
  have hR : 0 ≤ 2 * α * τ / (1 - m * τ) := div_nonneg (by nlinarith) hd.le
  rcases le_or_gt T 0 with hT0 | hT0
  · exact (div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by linarith)).trans hR
  · exact div_le_div₀ (by nlinarith) (by nlinarith) hd hdT

/-- The top ceiling from Landau's transition theorem at `b = −log 2/π`, where the limit is `2/3`. -/
theorem topCeiling_of_landau (hL : LandauTransition) : TopCeiling := by
  set b : ℝ := -Real.log 2 / π
  have hlim : 1 / (1 + Real.exp (π * b)) = 2 / 3 := by
    have : π * b = -Real.log 2 := by simp only [b]; field_simp
    rw [this, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hev := (hL b).eventually (gt_mem_nhds (show 1 / (1 + Real.exp (π * b)) < 3 / 4 by rw [hlim]; norm_num))
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hlog : Tendsto (fun x : ℕ => Real.log (2 * (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbig := hlog.eventually_ge_atTop (4 * π ^ 2 / Real.log 2)
  filter_upwards [hc.eventually hev, hbig, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hx hbx hs
  have h2 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hs
  have hcπ : 2 * π * (x : ℝ) / π = 2 * x := by field_simp
  have hk : ⌊(2 * (2 * π * (x : ℝ) / π) + b / π * Real.log (2 * π * x / π)) / 2⌋₊ ≤ 2 * (x - 1) := by
    apply Nat.floor_le_of_le
    rw [hcπ]
    have hb : b / π * Real.log (2 * x) ≤ -4 := by
      have e : b / π * Real.log (2 * x) = -(Real.log 2 * Real.log (2 * x)) / π ^ 2 := by
        simp only [b]; field_simp
      rw [e, div_le_iff₀ (by positivity)]
      have := (div_le_iff₀ hl2).1 hbx
      nlinarith
    push_cast [Nat.cast_sub (by omega : 1 ≤ x)]
    linarith
  have hanti := Cvs.Prolate.EvenRungsByIndex.lamR_anti (by positivity) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hs ⟨x - 1, by omega⟩) hk
  rw [lamTop, Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam]
  linarith

/-- `CEBound W̃` from (B), `T_c ≤ τ` and `a_t ≤ α` eventually, when `C₀∞(W̃)(μ* + 2ατ/(1 − μ*τ)) < 2`. -/
theorem ceBound_of_trace_le {Wt τ α : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : muStar * τ < 1)
    (hm : C0inf Wt * (muStar + 2 * α * τ / (1 - muStar * τ)) < 2) (hB : TraceComparison) (hD : TraceBound τ)
    (hA : ∀ᶠ x : ℕ in atTop, aTop x ≤ α) : Cvs.Route.Visibility.ConditionBWithoutCut.CEBound Wt := by
  refine ⟨_, hm, ?_⟩
  filter_upwards [hB, hD, hA, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hb ⟨hw, ht⟩ ha hx
  have hμ := Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos
  have hT1 : muStar * Tc x < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht hμ.le) hτ1
  refine mul_le_mul_of_nonneg_left ((hb hw hT1).trans (add_le_add le_rfl ?_)) (Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf_pos Wt).le
  exact budget_mono hμ (Cvs.Prolate.Gram.CentralResolventTrace.aTop_nonneg hx) ha ht hτ0 hτ1

/-- The margin `C₀∞(57/60)(μ* + 2·(5/3)·(9/50)/(1 − μ*·9/50)) < 2`. -/
theorem margin_57_60 :
    C0inf (57 / 60) * (muStar + 2 * (5 / 3) * (9 / 50) / (1 - muStar * (9 / 50))) < 2 := by
  have h := Cvs.Route.Visibility.ScalarTraceBudget.prolate_excess_lt_seven_tenths (a := 5 / 3) (t := 9 / 50) le_rfl (by norm_num) le_rfl
  have hm := Cvs.Upstream.InverseExcessPencilTop.excess_seven_tenths_margin
  calc _ ≤ C0inf (57 / 60) * (muStar + 7 / 10) :=
        mul_le_mul_of_nonneg_left (by linarith) (Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf_pos _).le
    _ < 2 := hm

/-- **`CEBound (57/60)`** from the trace comparison (B), the trace limit `T_c ≤ 9/50` and the top ceiling. -/
theorem ceBound_57_60_of_trace (hB : TraceComparison) (hD : TraceLimit) (hT : TopCeiling) :
    Cvs.Route.Visibility.ConditionBWithoutCut.CEBound (57 / 60) := by
  have hτ1 : muStar * (9 / 50) < 1 := by
    have := Cvs.Route.Visibility.ScalarTraceBudget.muStar_le_seven_tenths; nlinarith
  refine ceBound_of_trace_le (by norm_num) hτ1 margin_57_60 hB hD ?_
  filter_upwards [hT, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x h hx
  exact Cvs.Prolate.Gram.CentralResolventTrace.aTop_le hx h

/-- `CEBound (57/60)` from (B), the trace limit and Landau's transition theorem. -/
theorem ceBound_57_60_of_landau (hB : TraceComparison) (hD : TraceLimit) (hL : LandauTransition) :
    Cvs.Route.Visibility.ConditionBWithoutCut.CEBound (57 / 60) :=
  ceBound_57_60_of_trace hB hD (topCeiling_of_landau hL)

end Cvs.Route.Visibility.CEBoundFromTrace

end
