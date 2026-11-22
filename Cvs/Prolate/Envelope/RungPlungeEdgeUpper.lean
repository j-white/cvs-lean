import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.Prolate.CorrectedEnergyAntitone
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Envelope.RungEdgePlungeLower
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.PlungeLawIntegral
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungEdgeCorrectedEnergy
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plunge of a rung is at most `P♯(c)` times its squared edge value

With `ξ₀ = 1 + 4/c`, `a₀ = a(ξ₀)`, `D = c² − χ`: `w(ξ₀) ≤ 2ξ₀/(c p(ξ₀)) ≤ 1/2`, so `CorrectedEnergyAntitone`'s corrected energy, `RungEdgeCorrectedEnergy`'s
edge energy and `2|ψu| ≤ E` give `E ≤ (5/3)a₀ψ(1)²` beyond the edge; `PlungeLawIntegral`'s radial mass law then gives
`1 − λ ≤ (10/3)a₀(K̄(c, D/c)/(2c) + 1/(4D))·λh(1)²` for every rung. With Cvs.Prolate.EdgeBesselCount on `D ≥ 5c` this is
`1 − λ ≤ P♯(c)·λh(1)²` on every rung with `D ≥ 4c/log c`, where `P♯(c) ≤ 30` at `c ≥ 80`.
-/

noncomputable section

open Real Set MeasureTheory
open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact (energy)
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP qP dP aP wP)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.Gram.RungGramFloorAtInfinity (rungU rung_system)
open Cvs.Prolate.EvenRungsByIndex (rung lev lamR muR IsLevelIdx)

namespace Cvs.Prolate.Envelope.RungPlungeEdgeUpper
open Cvs.ZeroCounting

/-- `2|ψu| ≤ aψ² + u²/a` for `a > 0`. -/
theorem two_abs_mul_le_energy {a ψ u : ℝ} (ha : 0 < a) : 2 * |ψ * u| ≤ a * ψ ^ 2 + u ^ 2 / a := by
  have h : 0 ≤ (a * |ψ| - |u|) ^ 2 := sq_nonneg _
  have e : a * (a * ψ ^ 2 + u ^ 2 / a) = (a * |ψ|) ^ 2 + |u| ^ 2 := by
    rw [mul_pow, sq_abs, sq_abs]; field_simp
  have key : a * (2 * |ψ * u|) ≤ a * (a * ψ ^ 2 + u ^ 2 / a) := by
    rw [e, abs_mul]; nlinarith
  exact le_of_mul_le_mul_left key ha

/-- `a` is monotone beyond the edge. -/
theorem aP_le_aP {c χ ξ ξ' : ℝ} (hχc : χ < c ^ 2) (h1 : 1 < ξ) (hle : ξ ≤ ξ') : aP c χ ξ ≤ aP c χ ξ' := by
  unfold aP
  apply Real.sqrt_le_sqrt
  have hp : 0 ≤ pP ξ := by unfold pP; nlinarith
  have hpp : pP ξ ≤ pP ξ' := by unfold pP; nlinarith
  have hq : 0 ≤ qP c χ ξ := by
    unfold qP; nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ ξ ^ 2 by nlinarith) (sq_nonneg c)]
  have hqq : qP c χ ξ ≤ qP c χ ξ' := by
    unfold qP; nlinarith [mul_le_mul_of_nonneg_left (show ξ ^ 2 ≤ ξ' ^ 2 by nlinarith) (sq_nonneg c)]
  exact mul_le_mul hpp hqq hq (hp.trans hpp)

/-- **The rate at `ξ₀ = 1 + 4/c`**: `0 ≤ w(ξ₀) ≤ 1/2` for `c ≥ 4` and `0 ≤ χ < c²`. -/
theorem wP_top_le {c χ : ℝ} (hc : 4 ≤ c) (hχc : χ < c ^ 2) :
    0 ≤ wP c χ (1 + 4 / c) ∧ wP c χ (1 + 4 / c) ≤ 1 / 2 := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  set ξ₀ := 1 + 4 / c with hξ₀
  have h1 : 1 < ξ₀ := by have : 0 < 4 / c := by positivity
                         linarith
  have hq := Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.qP_pos h1 hc2 hχc
  have ha := Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.aP_pos h1 hc2 hχc
  have hp := Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos h1
  have hd := Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.dP_pos h1 hc2 hχc
  refine ⟨(Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.wP_pos h1 hc2 hχc).le, ?_⟩
  -- `(pq)′ ≤ 4ξq` and `a ≥ cp`
  have hdq : dP c χ ξ₀ ≤ 4 * ξ₀ * qP c χ ξ₀ := by
    unfold dP qP; nlinarith
  have hqp : c ^ 2 * pP ξ₀ ≤ qP c χ ξ₀ := by unfold pP qP; nlinarith
  have hap : c * pP ξ₀ ≤ aP c χ ξ₀ := by
    unfold aP
    rw [show c * pP ξ₀ = √((c * pP ξ₀) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hpc : 8 ≤ c * pP ξ₀ := by
    have e : c * pP ξ₀ = 8 + 16 / c := by rw [hξ₀]; unfold pP; field_simp; ring
    rw [e]; have : 0 < 16 / c := by positivity
    linarith
  have hξle : ξ₀ ≤ 2 := by
    have : 4 / c ≤ 1 := by rw [div_le_one hc0]; linarith
    linarith
  unfold wP
  rw [div_le_iff₀ (by positivity)]
  have h8 : 8 * qP c χ ξ₀ ≤ qP c χ ξ₀ * aP c χ ξ₀ := by nlinarith
  nlinarith

/-- **The energy of a rung beyond the edge**: for `c ≥ 4`, `0 ≤ χ < c²` and every `ξ > 1`,
`E(ξ) ≤ (5/3)a(1 + 4/c)ψ(1)²`. -/
theorem energy_le_top {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) {ξ : ℝ} (hξ : 1 < ξ) :
    energy (aP c χ) (psi c g) (rungU c g) ξ ≤ 5 / 3 * aP c χ (1 + 4 / c) * psi c g 1 ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  set ξ₀ := 1 + 4 / c with hξ₀
  have h1 : 1 < ξ₀ := by have : 0 < 4 / c := by positivity
                         linarith
  have ha₀ := Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.aP_pos h1 hc2 hχc
  have hP : 0 ≤ psi c g 1 ^ 2 := sq_nonneg _
  rcases le_or_gt ξ ξ₀ with hle | hlt
  · have hE := Cvs.Prolate.RungEdgeCorrectedEnergy.energy_le_edge hc0 hχc hg hg₁ hg₂c hang hξ
    have ha := aP_le_aP hχc hξ hle
    have : aP c χ ξ * psi c g 1 ^ 2 ≤ aP c χ ξ₀ * psi c g 1 ^ 2 := mul_le_mul_of_nonneg_right ha hP
    nlinarith
  · obtain ⟨hW0, hW⟩ := wP_top_le hc hχc
    obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
    have hE := Cvs.Prolate.CorrectedEnergyAntitone.prolate_energy_le_corrected h1 hlt.le hc2 hχ0 hχc
      (fun t ht => hψ t (lt_of_lt_of_le h1 ht.1)) (fun t _ => hu t) (by linarith)
    have hE₀ := Cvs.Prolate.RungEdgeCorrectedEnergy.energy_le_edge hc0 hχc hg hg₁ hg₂c hang h1
    set E₀ := energy (aP c χ) (psi c g) (rungU c g) ξ₀ with hE₀def
    have hmul : 2 * |psi c g ξ₀ * rungU c g ξ₀| ≤ E₀ := two_abs_mul_le_energy ha₀
    set W := wP c χ ξ₀
    have hnum : E₀ + W * (psi c g ξ₀ * rungU c g ξ₀) ≤ E₀ * (1 + W / 2) := by
      have : W * (psi c g ξ₀ * rungU c g ξ₀) ≤ W * |psi c g ξ₀ * rungU c g ξ₀| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hW0
      nlinarith
    have hden : 0 < 1 - W / 2 := by linarith
    have hE₀0 : 0 ≤ E₀ := le_trans (by positivity) hmul
    refine hE.trans ?_
    rw [div_le_iff₀ hden]
    have hr : 1 + W / 2 ≤ 5 / 3 * (1 - W / 2) := by linarith
    calc E₀ + W * (psi c g ξ₀ * rungU c g ξ₀) ≤ E₀ * (1 + W / 2) := hnum
      _ ≤ aP c χ ξ₀ * psi c g 1 ^ 2 * (5 / 3 * (1 - W / 2)) :=
          mul_le_mul hE₀ hr (by linarith) (by positivity)
      _ = 5 / 3 * aP c χ ξ₀ * psi c g 1 ^ 2 * (1 - W / 2) := by ring

/-- **The exterior mass of a rung against its edge value**: for `c ≥ 4`, `0 ≤ χ < c²`, `D = c² − χ`,
`∫₁^∞ψ² ≤ (5/3)a(1 + 4/c)ψ(1)²(K̄(c, D/c)/(2c) + 1/(4D))`. -/
theorem mass_le_top {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 4 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    ∫ ξ in Ioi 1, psi c g ξ ^ 2 ≤ 5 / 3 * aP c χ (1 + 4 / c) * psi c g 1 ^ 2
      * (Cvs.Prolate.EdgeBesselCount.Kbar c ((c ^ 2 - χ) / c) / (2 * c) + 1 / (4 * (c ^ 2 - χ))) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hψ, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  obtain ⟨-, hM⟩ := Cvs.Prolate.PlungeLawIntegral.radial_mass_le hc0 hχ0 hχc hψ hu hψc (Cvs.L2a.PositionTailSpanAdapters.rungU_one c g)
    fun ξ hξ => energy_le_top hg hg₁ hg₂c hang hc hχ0 hχc hξ
  set E := 5 / 3 * aP c χ (1 + 4 / c) * psi c g 1 ^ 2 with hE
  have hE0 : 0 ≤ E := by
    have : 0 ≤ aP c χ (1 + 4 / c) := Real.sqrt_nonneg _
    positivity
  have hK := Cvs.Prolate.EdgeBesselCount.ellK_le_Kbar hc0 hχ0 hχc
  unfold Cvs.Prolate.PlungeLawIntegral.ellK at hK
  have h1 : E / 2 * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ ≤ E * (Cvs.Prolate.EdgeBesselCount.Kbar c ((c ^ 2 - χ) / c) / (2 * c)) := by
    rw [show E / 2 * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ = E / (2 * c) * (c * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ) by
      field_simp]
    calc E / (2 * c) * (c * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ) ≤ E / (2 * c) * Cvs.Prolate.EdgeBesselCount.Kbar c ((c ^ 2 - χ) / c) :=
          mul_le_mul_of_nonneg_left hK (by positivity)
      _ = _ := by ring
  have e : E / (4 * (c ^ 2 - χ)) = E * (1 / (4 * (c ^ 2 - χ))) := by ring
  rw [mul_add]
  linarith

/-- **The plunge of a rung against its edge value**: for `c ≥ 4`, `D = c² − χ_k`,
`1 − λ ≤ (10/3)a(1 + 4/c)(K̄(c, D/c)/(2c) + 1/(4D))·λh(1)²`. -/
theorem one_sub_lamR_le_top {c : ℝ} {k : ℕ} (hc : 4 ≤ c) (h : ∃ χ, IsLevelIdx c k χ) (hχc : lev c k < c ^ 2) :
    1 - lamR c k ≤ 10 / 3 * aP c (lev c k) (1 + 4 / c)
      * (Cvs.Prolate.EdgeBesselCount.Kbar c ((c ^ 2 - lev c k) / c) / (2 * c) + 1 / (4 * (c ^ 2 - lev c k)))
      * (lamR c k * rung c k 1 ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hχ0 : 0 ≤ lev c k := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (Cvs.Prolate.EvenRungsByIndex.lev_spec h).1
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
  have hm := mass_le_top hg hg₁ hg₂c hang hc hχ0 hχc
  rw [Cvs.Prolate.Envelope.RungExteriorLaw.mass_eq hc0 h, Cvs.Prolate.EvenRungsByIndex.psi_rung h 1 ⟨by norm_num, le_rfl⟩] at hm
  have hmu : muR c k ^ 2 = 2 * π / c * lamR c k := by
    rw [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq hc0]; field_simp
  rw [mul_pow, hmu] at hm
  set R := Cvs.Prolate.EdgeBesselCount.Kbar c ((c ^ 2 - lev c k) / c) / (2 * c) + 1 / (4 * (c ^ 2 - lev c k))
  set a₀ := aP c (lev c k) (1 + 4 / c)
  have e : 5 / 3 * a₀ * (2 * π / c * lamR c k * rung c k 1 ^ 2) * R
      = π / c * (10 / 3 * a₀ * R * (lamR c k * rung c k 1 ^ 2)) := by field_simp; ring
  rw [e] at hm
  exact le_of_mul_le_mul_left hm (by positivity)

/-- `a(1 + 4/c) ≤ 11` for `c ≥ 80` and `c² − χ ≤ 5c`. -/
theorem aP_top_le {c χ : ℝ} (hc : 80 ≤ c) (hD : c ^ 2 - χ ≤ 5 * c) :
    aP c χ (1 + 4 / c) ≤ 11 := by
  have hc0 : 0 < c := by linarith
  unfold aP
  rw [show (11 : ℝ) = √(11 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_le_sqrt
  have ep : pP (1 + 4 / c) = 8 / c + 16 / c ^ 2 := by unfold pP; field_simp; ring
  have eq : qP c χ (1 + 4 / c) = (c ^ 2 - χ) + 8 * c + 16 := by unfold qP; field_simp; ring
  rw [ep, eq]
  have hp0 : 0 ≤ 8 / c + 16 / c ^ 2 := by positivity
  have hq : (c ^ 2 - χ) + 8 * c + 16 ≤ 13 * c + 16 := by linarith
  have h1 : (8 / c + 16 / c ^ 2) * ((c ^ 2 - χ) + 8 * c + 16) ≤ (8 / c + 16 / c ^ 2) * (13 * c + 16) :=
    mul_le_mul_of_nonneg_left hq hp0
  have e2 : (8 / c + 16 / c ^ 2) * (13 * c + 16) = 104 + 336 / c + 256 / c ^ 2 := by field_simp; ring
  have h3 : 336 / c ≤ 336 / 80 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc
  have h4 : 256 / c ^ 2 ≤ 256 / 80 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  nlinarith

/-- The majorant `K♯(c) = (log 3 + 2 log c)/2 + 5/(12c) + 2/3` of `K̄(c, s)` on `4/log c ≤ s ≤ 5`. -/
def topK (c : ℝ) : ℝ := (Real.log 3 + 2 * Real.log c) / 2 + 5 / (12 * c) + 2 / 3

/-- `K̄(c, s) ≤ K♯(c)` for `c ≥ 80` and `4/log c ≤ s ≤ 5`. -/
theorem Kbar_le_topK {c s : ℝ} (hc : 80 ≤ c) (hs : 4 / Real.log c ≤ s) (hs5 : s ≤ 5) :
    Cvs.Prolate.EdgeBesselCount.Kbar c s ≤ topK c := by
  have hc0 : 0 < c := by linarith
  have hlc : 0 < Real.log c := Real.log_pos (by linarith)
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hr : 12 * c / s ≤ 3 * c * Real.log c := by
    rw [div_le_iff₀ hs0]
    rw [div_le_iff₀ hlc] at hs
    nlinarith
  have hl1 : Real.log (12 * c / s) ≤ Real.log (3 * c * Real.log c) :=
    Real.log_le_log (by positivity) hr
  have hl2 : Real.log (3 * c * Real.log c) = Real.log 3 + Real.log c + Real.log (Real.log c) := by
    rw [Real.log_mul (by positivity) hlc.ne', Real.log_mul (by norm_num) hc0.ne']
  have hl3 : Real.log (Real.log c) ≤ Real.log c := by
    have := Real.log_le_sub_one_of_pos hlc; linarith
  have h5 : s / (12 * c) ≤ 5 / (12 * c) := div_le_div_of_nonneg_right hs5 (by positivity)
  unfold Cvs.Prolate.EdgeBesselCount.Kbar topK
  linarith

/-- The top-layer factor `(110/3)(K♯(c)/(2c) + log c/(16c))`. -/
def topP (c : ℝ) : ℝ := 110 / 3 * (topK c / (2 * c) + Real.log c / (16 * c))

/-- **The sharp edge floor** `P♯(c) = (11/10)(K̄(c, 5) + 1/10)/c + (110/3)(K♯(c)/(2c) + log c/(16c))`. -/
def sharpP (c : ℝ) : ℝ := 11 / 10 * (Cvs.Prolate.EdgeBesselCount.Kbar c 5 + 1 / 10) / c + topP c

theorem topP_nonneg {c : ℝ} (hc : 80 ≤ c) : 0 ≤ topP c := by
  have hc0 : 0 < c := by linarith
  have hlc : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  unfold topP topK
  positivity

/-- **The plunge in the top layer**: `1 − λ ≤ topP(c)·λh(1)²` for a rung at `c ≥ 80` with
`4c/log c ≤ D ≤ 5c`. -/
theorem one_sub_lamR_le_topP {c : ℝ} {k : ℕ} (hc : 80 ≤ c) (h : ∃ χ, IsLevelIdx c k χ)
    (hDl : 4 * c / Real.log c ≤ c ^ 2 - lev c k) (hDu : c ^ 2 - lev c k ≤ 5 * c) :
    1 - lamR c k ≤ topP c * (lamR c k * rung c k 1 ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hlc : 0 < Real.log c := Real.log_pos (by linarith)
  have hD0 : 0 < c ^ 2 - lev c k := lt_of_lt_of_le (by positivity) hDl
  have hχc : lev c k < c ^ 2 := by linarith
  have hmain := one_sub_lamR_le_top (by linarith) h hχc
  have hl0 : 0 ≤ lamR c k := by unfold lamR; positivity
  have hx : 0 ≤ lamR c k * rung c k 1 ^ 2 := by positivity
  set D := c ^ 2 - lev c k with hDdef
  have ha := aP_top_le hc hDu
  have ha0 : 0 ≤ aP c (lev c k) (1 + 4 / c) := Real.sqrt_nonneg _
  have hs : 4 / Real.log c ≤ D / c := by
    rw [div_le_iff₀ hlc] at hDl
    rw [div_le_div_iff₀ hlc hc0]; linarith
  have hs5 : D / c ≤ 5 := by rw [div_le_iff₀ hc0]; linarith
  have hK := Kbar_le_topK hc hs hs5
  have hK0 : 0 ≤ Cvs.Prolate.EdgeBesselCount.Kbar c (D / c) := by
    unfold Cvs.Prolate.EdgeBesselCount.Kbar
    have : 1 ≤ 12 * c / (D / c) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    have := Real.log_nonneg this
    positivity
  have hinv : 1 / (4 * D) ≤ Real.log c / (16 * c) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ hlc] at hDl
    nlinarith
  have hR : Cvs.Prolate.EdgeBesselCount.Kbar c (D / c) / (2 * c) + 1 / (4 * D) ≤ topK c / (2 * c) + Real.log c / (16 * c) :=
    add_le_add (div_le_div_of_nonneg_right hK (by positivity)) hinv
  have hR0 : 0 ≤ Cvs.Prolate.EdgeBesselCount.Kbar c (D / c) / (2 * c) + 1 / (4 * D) := by positivity
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hx)
  unfold topP
  calc 10 / 3 * aP c (lev c k) (1 + 4 / c) * (Cvs.Prolate.EdgeBesselCount.Kbar c (D / c) / (2 * c) + 1 / (4 * D))
      ≤ 10 / 3 * 11 * (topK c / (2 * c) + Real.log c / (16 * c)) := by
        have := mul_le_mul ha hR hR0 (by norm_num)
        nlinarith
    _ = 110 / 3 * (topK c / (2 * c) + Real.log c / (16 * c)) := by ring

/-- **The sharp plunge law**: `1 − λ ≤ P♯(c)·λh(1)²` for a rung at `c ≥ 80` with `D ≥ 4c/log c`. -/
theorem one_sub_lamR_le_sharp {c : ℝ} {k : ℕ} (hc : 80 ≤ c) (h : ∃ χ, IsLevelIdx c k χ)
    (hDl : 4 * c / Real.log c ≤ c ^ 2 - lev c k) :
    1 - lamR c k ≤ sharpP c * (lamR c k * rung c k 1 ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hχ0 : 0 ≤ lev c k := Cvs.Prolate.SlepianEvenOrdering.nonneg_of_mem_evenSpec c (Cvs.Prolate.EvenRungsByIndex.lev_spec h).1
  have hK := Cvs.Prolate.Envelope.RungEdgePlungeLower.Kbar_nonneg hc
  have hl0 : 0 ≤ lamR c k := by unfold lamR; positivity
  have hx : 0 ≤ lamR c k * rung c k 1 ^ 2 := by positivity
  have hA : 0 ≤ 11 / 10 * (Cvs.Prolate.EdgeBesselCount.Kbar c 5 + 1 / 10) / c * (lamR c k * rung c k 1 ^ 2) := by positivity
  have hB : 0 ≤ topP c * (lamR c k * rung c k 1 ^ 2) := mul_nonneg (topP_nonneg hc) hx
  have hsplit : sharpP c * (lamR c k * rung c k 1 ^ 2)
      = 11 / 10 * (Cvs.Prolate.EdgeBesselCount.Kbar c 5 + 1 / 10) / c * (lamR c k * rung c k 1 ^ 2)
        + topP c * (lamR c k * rung c k 1 ^ 2) := by
    unfold sharpP; ring
  rw [hsplit]
  rcases le_or_gt (5 * c) (c ^ 2 - lev c k) with hD | hD
  · obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
    have hm := Cvs.Prolate.EdgeBesselCount.mass_le_edge hg hg₁ hg₂c hang hc hχ0 hD
    rw [Cvs.Prolate.Envelope.RungExteriorLaw.mass_eq hc0 h, Cvs.Prolate.EvenRungsByIndex.psi_rung h 1 ⟨by norm_num, le_rfl⟩] at hm
    have hmu : muR c k ^ 2 = 2 * π / c * lamR c k := by
      rw [Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq hc0]; field_simp
    rw [mul_pow, hmu] at hm
    have e : 11 / 10 * (2 * π / c * lamR c k * rung c k 1 ^ 2) * (Cvs.Prolate.EdgeBesselCount.Kbar c 5 + 1 / 10) / (2 * c)
        = π / c * (11 / 10 * (Cvs.Prolate.EdgeBesselCount.Kbar c 5 + 1 / 10) / c * (lamR c k * rung c k 1 ^ 2)) := by
      field_simp
    rw [e] at hm
    have := le_of_mul_le_mul_left hm (by positivity)
    linarith
  · have := one_sub_lamR_le_topP hc h hDl hD.le
    linarith

/-- `P♯(c) ≤ 30` for `c ≥ 80`. -/
theorem sharpP_le {c : ℝ} (hc : 80 ≤ c) : sharpP c ≤ 30 := by
  have hc0 : 0 < c := by linarith
  have hlc : Real.log c ≤ c := (Real.log_le_sub_one_of_pos hc0).trans (by linarith)
  have hl12 : Real.log (12 * c / 5) ≤ 12 * c / 5 := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hl3 : Real.log 3 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have i1 : Real.log (12 * c / 5) / 2 / c ≤ 6 / 5 := by
    rw [div_div, div_le_iff₀ (by positivity)]; linarith
  have i2 : (5 / (12 * c) + 2 / 3 + 1 / 10) / c ≤ 1 / 80 := by
    rw [div_le_iff₀ hc0]
    have : 5 / (12 * c) ≤ 1 / 100 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have i3 : (Real.log 3 + 2 * Real.log c) / 2 / (2 * c) ≤ 3 / 5 := by
    rw [div_div, div_le_iff₀ (by positivity)]; linarith
  have i4 : (5 / (12 * c) + 2 / 3) / (2 * c) ≤ 1 / 80 := by
    rw [div_le_iff₀ (by positivity)]
    have : 5 / (12 * c) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have i5 : Real.log c / (16 * c) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have e1 : 11 / 10 * (Cvs.Prolate.EdgeBesselCount.Kbar c 5 + 1 / 10) / c
      = 11 / 10 * (Real.log (12 * c / 5) / 2 / c + (5 / (12 * c) + 2 / 3 + 1 / 10) / c) := by
    unfold Cvs.Prolate.EdgeBesselCount.Kbar; field_simp; ring
  have e2 : topK c / (2 * c) = (Real.log 3 + 2 * Real.log c) / 2 / (2 * c) + (5 / (12 * c) + 2 / 3) / (2 * c) := by
    unfold topK; field_simp; ring
  unfold sharpP topP
  rw [e1, e2]
  nlinarith

end Cvs.Prolate.Envelope.RungPlungeEdgeUpper

end
