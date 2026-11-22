import Mathlib
import Cvs.Approximant.SingletonRegularisationColumn
import Cvs.Prolate.BandwidthSpectrumFlow
import Cvs.Prolate.EigenvalueExponentialRate
import Cvs.Prolate.EvenRungsByIndex
import Cvs.WeilForm.Archimedean.ArchPsiClosedForm
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaCriticalAsymptotic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window edge's two scales: the density crossing at `2πx`, and the leakage as edge mass

`Ψ(2πx) = log x` up to `57/(2πx)`, so `γ = 2πx` is where the zeros' mean density `Ψ(γ)/2π` meets the window's
density `log x/2π`. Along a `C¹` branch of the finite cosine transform the concentration `λ = (c/2π)μ²` flows by
`λ' = (2λ/c)G(1)²`, so for the rungs `j = 0, 2, 4` the leakage is `1 − λ_j(c) = ∫_c^∞ (2λ_j(s)/s)·rung_j(s)(1)² ds`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.WeilForm.WindowEdgeTwoScales
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex Cvs.Prolate.BandwidthSpectrumFlow

/-- The archimedean symbol is `log (t/2π)` up to `57/t`. -/
theorem abs_archSymbol_sub_log_le {t : ℝ} (ht : 2 ≤ t) :
    |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Real.log (t / (2 * π))| ≤ 57 / t := by
  have h := DigammaAsym.abs_re_digamma_sub_log_le t ht
  have ht2 : (0 : ℝ) < t / 2 := by linarith
  have hlog : Real.log (t / (2 * π)) = Real.log (t / 2) - Real.log π := by
    rw [show t / (2 * π) = t / 2 / π by ring, Real.log_div ht2.ne' Real.pi_pos.ne']
  have heq : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t - Real.log (t / (2 * π)) =
      (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re - Real.log (t / 2) := by
    rw [hlog, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol]
    ring
  rw [heq]
  exact h

/-- **The density crossing**: `Ψ(2πx) = log x` up to `57/(2πx)`. -/
theorem abs_archSymbol_two_pi_mul_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * x) - Real.log x| ≤ 57 / (2 * π * x) := by
  have h2 : 2 ≤ 2 * π * x := by nlinarith [Real.pi_gt_three]
  have h := abs_archSymbol_sub_log_le h2
  rwa [show 2 * π * x / (2 * π) = x by field_simp] at h

/-- **Slepian's flow for the concentration**: along a `C¹` branch, `λ(c) = (c/2π)μ(c)²` has derivative
`(2λ/c)G(1)²`. -/
theorem hasDerivAt_conc {G G' : ℝ → ℝ → ℝ} {μ : ℝ → ℝ} {c₀ M μ' : ℝ} {U : Set ℝ} {g₁ : ℝ → ℝ}
    (hB : Branch G G' μ c₀ U M) (hμ : HasDerivAt μ μ' c₀) (hc : c₀ ≠ 0)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (G c₀) (g₁ s) s) (hg₁ : ContinuousOn g₁ (uIcc (-1) 1))
    (hsym : G c₀ (-1) = G c₀ 1) (hnorm : ∫ ξ in (-1 : ℝ)..1, G c₀ ξ ^ 2 = 1) :
    HasDerivAt (fun c => c / (2 * π) * μ c ^ 2) (2 * (c₀ / (2 * π) * μ c₀ ^ 2) / c₀ * G c₀ 1 ^ 2) c₀ := by
  have hflow := flow_eigenvalue hB hμ hc hg hg₁ hsym hnorm
  have h1 : HasDerivAt (fun c : ℝ => c / (2 * π)) (1 / (2 * π)) c₀ := (hasDerivAt_id' c₀).div_const _
  have h2 : HasDerivAt (fun c => μ c ^ 2) (2 * μ c₀ * μ') c₀ := by
    simpa using hμ.fun_pow 2
  refine (h1.mul h2).congr_deriv ?_
  rw [hflow]
  field_simp
  ring

/-- `λ_k = (c/2π)μ_k²` for `c ≥ 0`. -/
theorem lamR_eq {c : ℝ} (hc : 0 ≤ c) (k : ℕ) : lamR c k = c / (2 * π) * muR c k ^ 2 := by
  rw [lamR, mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- **The rung flow**: if a `C¹` branch with eigenvalue `μ_k` passes through the rung of index `k` at `c₀ > 0`, then
`λ_k' = (2λ_k/c₀)·rung(1)²`. -/
theorem hasDerivAt_lamR {c₀ M μ' : ℝ} {U : Set ℝ} {G G' : ℝ → ℝ → ℝ} {k : ℕ} (hc : 0 < c₀)
    (h : ∃ χ, IsLevelIdx c₀ k χ) (hB : Branch G G' (fun c => muR c k) c₀ U M) (hG : G c₀ = rung c₀ k)
    (hμ : HasDerivAt (fun c => muR c k) μ' c₀) :
    HasDerivAt (fun c => lamR c k) (2 * lamR c₀ k / c₀ * rung c₀ k 1 ^ 2) c₀ := by
  obtain ⟨hg, hg₁, -, -, heven, hnorm⟩ := rung_spec h
  have hg₁c : ContinuousOn (rung₁ c₀ k) (uIcc (-1) 1) :=
    fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  have hev : rung c₀ k (-1) = rung c₀ k 1 := heven 1 ⟨by norm_num, le_rfl⟩
  rw [← hG] at hg hev hnorm
  have hd := hasDerivAt_conc hB hμ hc.ne' hg hg₁c hev hnorm
  rw [lamR_eq hc.le, ← hG]
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hc] with c hc' using lamR_eq hc'.le k

/-- **The leakage is the integrated squared endpoint value**: for `j ∈ {0, 2, 4}`, if at every `s ≥ c > 0` a `C¹`
branch with eigenvalue `μ_j` passes through the rung of index `j`, then
`1 − λ_j(c) = ∫_{s > c} (2λ_j(s)/s)·rung_j(s)(1)²`. -/
theorem one_sub_lamR_eq_integral {c : ℝ} {j : ℕ} (hj : j = 0 ∨ j = 2 ∨ j = 4) (hc : 0 < c)
    (hbr : ∀ s ∈ Ici c, (∃ χ, IsLevelIdx s j χ) ∧ ∃ (G G' : ℝ → ℝ → ℝ) (U : Set ℝ) (M μ' : ℝ),
      Branch G G' (fun c => muR c j) s U M ∧ G s = rung s j ∧ HasDerivAt (fun c => muR c j) μ' s) :
    1 - lamR c j = ∫ s in Ioi c, 2 * lamR s j / s * rung s j 1 ^ 2 := by
  have hd : ∀ s ∈ Ici c, HasDerivAt (fun c => lamR c j) (2 * lamR s j / s * rung s j 1 ^ 2) s := by
    intro s hs
    obtain ⟨hlev, G, G', U, M, μ', hB, hG, hμ⟩ := hbr s hs
    exact hasDerivAt_lamR (lt_of_lt_of_le hc hs) hlev hB hG hμ
  have hnn : ∀ s ∈ Ici c, 0 ≤ 2 * lamR s j / s * rung s j 1 ^ 2 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hc hs
    have : 0 ≤ lamR s j := by rw [lamR]; positivity
    positivity
  have hle : ∀ s ∈ Ici c, lamR s j ≤ 1 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hc hs
    rcases hj with rfl | rfl | rfl
    · exact lamR_zero_le_one hs0
    · exact (lamR_lt_one hs0 (hbr s hs).1 (by norm_num)).le
    · exact (lamR_lt_one hs0 (hbr s hs).1 (by norm_num)).le
  have hmono : MonotoneOn (fun s => lamR s j) (Ici c) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici c) ?_ ?_ ?_
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      exact (hd s (mem_Ici_of_Ioi hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s (mem_Ici_of_Ioi hs)).deriv]
      exact hnn s (mem_Ici_of_Ioi hs)
  have hseq := Cvs.Prolate.EigenvalueExponentialRate.tendsto_lamR_nat hj
  have hlim : Tendsto (fun s => lamR s j) atTop (𝓝 1) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨n, hn⟩ := ((hseq.eventually (lt_mem_nhds ha)).and
        (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (c / (2 * π))))).exists
      have hcn : c ≤ 2 * π * n := by
        have := hn.2
        rwa [div_le_iff₀ (by positivity), mul_comm] at this
      filter_upwards [eventually_ge_atTop (2 * π * n)] with s hs
      exact lt_of_lt_of_le hn.1 (hmono hcn (le_trans hcn hs) hs)
    · filter_upwards [eventually_ge_atTop c] with s hs
      exact lt_of_le_of_lt (hle s hs) ha
  exact (integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun s hs => hnn s (mem_Ici_of_Ioi hs)) hlim).symm

end Cvs.WeilForm.WindowEdgeTwoScales
