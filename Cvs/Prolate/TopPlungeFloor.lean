import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.RegularSolutionDepthBound
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungEqRegularSolution
import Cvs.Prolate.RungFarMassFloor
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The top plunge floor: `1 − λ_t ≥ 1/(224e⁵²c⁶)` at `c = 2πx`, `x ≥ 31`

The top rung is `h(1)·y` with `y` the regular solution at depth `D = c² − χ_t ∈ [4c/log c, 5c]` (Cvs.Prolate.RungFarMassFloor, Cvs.Prolate.TopRungDepthBound); Cvs.Prolate.RegularSolutionDepthBound
at `σ = τ − D/c³` gives `y² ≤ 2e⁵²c⁵` on `[0, 1]`, so `h(1)² ≥ 1/(4e⁵²c⁵)` from `‖h‖ = 1`, and the edge mass
`ψ(1)² ≤ 8(D + 2c)∫₁^∞ψ²` with `∫₁^∞ψ² = (π/c)(1 − λ)` gives `1 − λ_t ≥ h(1)²/(56c)`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.Prolate.TopPlungeFloor
open Cvs.ZeroCounting

open Cvs.Prolate.RegularSolutionEdge (regSol regV regU sqC)
open Cvs.Prolate.EvenRungsByIndex (rung lev lamR muR IsLevelIdx)
open Cvs.L2a.AngularProlateTailPositive (psi)

/-- The regular solution of the radial prolate equation solves `RegularSolutionDepthBound`'s system on `[0, 1]`. -/
theorem isSys_regSol (c χ : ℝ) : Cvs.Prolate.RegularSolutionDepthBound.IsSys c χ (regSol (sqC c) χ) (regV (sqC c) χ) (regU (sqC c) χ) := by
  intro t ht
  have ht1 : (-1 : ℝ) < t := by linarith [ht.1]
  refine ⟨Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regSol _ _ ht1, Cvs.Prolate.RegularSolutionEdge.pP_mul_regV _ _ ht1, ?_⟩
  refine (Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regU (sqC c) χ ht1).congr_deriv ?_
  rw [Cvs.Prolate.TopRungDepthBound.sqC_apply]; ring

/-- The four factors of `RegularSolutionDepthBound`'s bound at `σ = τ − D/c³`, `4 ≤ D ≤ 5c`, `c ≥ 80`, multiply to at most `2e⁵²c⁵`. -/
theorem factor_le {c D τ χ σ : ℝ} (hc : 80 ≤ c) (hD0 : 0 < D) (hD5 : D ≤ 5 * c) (hD4 : 4 ≤ D) (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) (hτsq : τ ^ 2 = 1 - D / c ^ 2) (hτχ : c ^ 2 * τ ^ 2 = χ) (hσ : σ = τ - D / c ^ 3)
    (hσ0 : 0 ≤ σ) :
    Real.exp (2 * (D * (1 - τ))) * (1 + (D * (1 - τ)) ^ 2 / c ^ 2)
        * Real.exp (c * (1 + c ^ 2 / D) * (τ - σ)) * (1 + c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2)))
      ≤ 2 * Real.exp 52 * c ^ 5 := by
  have hc0 : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have h1τ : 1 - τ ≤ D / c ^ 2 := by
    have : τ ^ 2 ≤ τ := by nlinarith
    linarith
  have h1τ0 : 0 ≤ 1 - τ := by linarith
  have hDD : D * (D / c ^ 2) ≤ 25 := by
    have h : D ^ 2 ≤ (5 * c) ^ 2 := pow_le_pow_left₀ hD0.le hD5 2
    rw [mul_div_assoc', div_le_iff₀ hc2]
    nlinarith
  have hDτ : D * (1 - τ) ≤ 25 := (mul_le_mul_of_nonneg_left h1τ hD0.le).trans hDD
  have hDτ0 : 0 ≤ D * (1 - τ) := mul_nonneg hD0.le h1τ0
  have hY : Real.exp (2 * (D * (1 - τ))) ≤ Real.exp 50 := Real.exp_le_exp.mpr (by linarith)
  have hB : 1 + (D * (1 - τ)) ^ 2 / c ^ 2 ≤ 2 := by
    have h : (D * (1 - τ)) ^ 2 ≤ 25 ^ 2 := pow_le_pow_left₀ hDτ0 hDτ 2
    have h2 : (25 : ℝ) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have : (D * (1 - τ)) ^ 2 / c ^ 2 ≤ 1 := by rw [div_le_one hc2]; linarith
    linarith
  have hDc2 : D / c ^ 2 ≤ 1 := by
    rw [div_le_one hc2]; nlinarith
  have hE : Real.exp (c * (1 + c ^ 2 / D) * (τ - σ)) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    have e : c * (1 + c ^ 2 / D) * (τ - σ) = D / c ^ 2 + 1 := by
      rw [hσ]; field_simp; ring
    rw [e]; linarith
  have hσ1 : σ ≤ τ := by
    have : 0 ≤ D / c ^ 3 := by positivity
    rw [hσ]; linarith
  have hτhalf : 1 / 2 ≤ τ := by
    have h5c : D / c ^ 2 ≤ 1 / 16 := by
      rw [div_le_div_iff₀ hc2 (by norm_num)]; nlinarith
    have : (1 / 2 : ℝ) ^ 2 ≤ τ ^ 2 := by rw [hτsq]; linarith
    exact (pow_le_pow_iff_left₀ (by norm_num) hτ0 two_ne_zero).1 this
  have hp : D / c ^ 2 ≤ 1 - σ ^ 2 := by
    have : σ ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hσ0 hσ1 2
    linarith
  have hq : D / c * (1 / 2) ≤ χ - c ^ 2 * σ ^ 2 := by
    have e : χ - c ^ 2 * σ ^ 2 = D / c * (τ + σ) := by
      rw [← hτχ, hσ]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hR : 1 + c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2)) ≤ c ^ 5 := by
    have hP : D ^ 2 / (2 * c ^ 3) ≤ (1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2) := by
      calc D ^ 2 / (2 * c ^ 3) = D / c ^ 2 * (D / c * (1 / 2)) := by field_simp
        _ ≤ _ := mul_le_mul hp hq (by positivity) ((by positivity : 0 ≤ D / c ^ 2).trans hp)
    have hP0 : 0 < D ^ 2 / (2 * c ^ 3) := by positivity
    have h1 : c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2)) ≤ c ^ 2 / (D ^ 2 / (2 * c ^ 3)) :=
      div_le_div_of_nonneg_left hc2.le hP0 hP
    have h2 : c ^ 2 / (D ^ 2 / (2 * c ^ 3)) = 2 * c ^ 5 / D ^ 2 := by field_simp
    have hD2 : 16 ≤ D ^ 2 := by nlinarith
    have hc5 : 0 < c ^ 5 := by positivity
    have h3 : 2 * c ^ 5 / D ^ 2 ≤ c ^ 5 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h4 : (80 : ℝ) ^ 5 ≤ c ^ 5 := pow_le_pow_left₀ (by norm_num) hc 5
    linarith
  calc Real.exp (2 * (D * (1 - τ))) * (1 + (D * (1 - τ)) ^ 2 / c ^ 2)
        * Real.exp (c * (1 + c ^ 2 / D) * (τ - σ)) * (1 + c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2)))
      ≤ Real.exp 50 * 2 * Real.exp 2 * c ^ 5 := by
        have : 0 ≤ 1 + (D * (1 - τ)) ^ 2 / c ^ 2 := by positivity
        have : 0 ≤ 1 + c ^ 2 / ((1 - σ ^ 2) * (χ - c ^ 2 * σ ^ 2)) := by
          have : 0 < 1 - σ ^ 2 := lt_of_lt_of_le (by positivity) hp
          have : 0 < χ - c ^ 2 * σ ^ 2 := lt_of_lt_of_le (by positivity) hq
          positivity
        gcongr
    _ = 2 * Real.exp 52 * c ^ 5 := by
        rw [show (52 : ℝ) = 50 + 2 by norm_num, Real.exp_add]; ring

/-- **The regular solution at depth `D ≤ 5c`, `D ≥ 4c/log c`, `c ≥ 80` is at most `2e⁵²c⁵` in square on `[0, 1]`.** -/
theorem regSol_sq_le {c χ : ℝ} (hc : 80 ≤ c) (hD5 : c ^ 2 - χ ≤ 5 * c) (hDl : 4 * c / Real.log c ≤ c ^ 2 - χ) :
    ∀ t ∈ Icc (0 : ℝ) 1, regSol (sqC c) χ t ^ 2 ≤ 2 * Real.exp 52 * c ^ 5 := by
  have hc0 : 0 < c := by linarith
  set D := c ^ 2 - χ with hDdef
  have hlog0 : 0 < Real.log c := Real.log_pos (by linarith)
  have hlogc : Real.log c ≤ c := (Real.log_le_sub_one_of_pos hc0).trans (by linarith)
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDl
  have hDc : D < c ^ 2 := by nlinarith
  set K := D / c with hK
  have hK0 : 0 < K := by positivity
  have hKc : K < c := by rw [hK, div_lt_iff₀ hc0]; nlinarith
  obtain ⟨hτ0, hτ2, hτ1⟩ := Cvs.Prolate.TopRungDepthBound.tau_spec hc0 hK0 hKc
  set τ := √(1 - K / c) with hτ
  have hχK : c ^ 2 - K * c = χ := by rw [hK, div_mul_cancel₀ _ hc0.ne']; ring
  have hKc2 : K / c = D / c ^ 2 := by rw [hK, div_div, sq]
  have hτχ : c ^ 2 * τ ^ 2 = χ := by
    rw [hτ2, hKc2]; field_simp; ring
  have hτsq : τ ^ 2 = 1 - D / c ^ 2 := by rw [hτ2, hKc2]
  have hDc2 : D / c ^ 2 ≤ 5 / c := by
    rw [div_le_div_iff₀ (by positivity) hc0]; nlinarith
  have h5c : 5 / c ≤ 1 / 16 := by rw [div_le_div_iff₀ hc0 (by norm_num)]; linarith
  have hτhalf : 1 / 2 ≤ τ := by
    have : (1 / 2 : ℝ) ^ 2 ≤ τ ^ 2 := by rw [hτsq]; nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) hτ0 two_ne_zero).1 this
  obtain ⟨hy1e, hu1e⟩ := Cvs.Prolate.TopRungDepthBound.edge_one hc0 hK0 hKc
  rw [hχK] at hy1e hu1e
  set ℓ := D / c ^ 3 with hℓ
  have hℓ0 : 0 < ℓ := by positivity
  have hℓs : ℓ ≤ 1 / 4 := by
    rw [hℓ, div_le_iff₀ (by positivity)]
    have : (80 : ℝ) ^ 2 ≤ c ^ 2 := by nlinarith
    nlinarith
  set σ := τ - ℓ with hσ
  have hσ0 : 0 ≤ σ := by linarith
  have hστ : σ < τ := by linarith
  have hy0 : ∀ t ∈ Icc τ 1, 0 ≤ regSol (sqC c) χ t := fun t ht => by linarith [hy1e t ht]
  have hu0 : ∀ t ∈ Icc τ 1, 0 ≤ regU (sqC c) χ t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact hu1e
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h']; simp [regU]
    refine (Cvs.Prolate.EdgeCentreSign.regU_pos_of_lt (sqC c) (by linarith) h' fun s hs => ?_).le
    rw [Cvs.Prolate.TopRungDepthBound.sqC_apply, ← hτχ]
    have : τ ^ 2 < s ^ 2 := pow_lt_pow_left₀ (h.trans_le hs.1) hτ0 two_ne_zero
    exact mul_lt_mul_of_pos_left this (by positivity)
  have hv1 : regV (sqC c) χ 1 = -(c ^ 2 - χ) / 2 := by rw [Cvs.Prolate.RegularSolutionEdge.regV_one, Cvs.Prolate.TopRungDepthBound.sqC_apply]; ring
  have hmain := Cvs.Prolate.RegularSolutionDepthBound.sq_le (isSys_regSol c χ) hc0 hσ0 hστ hτ1 hτχ hD0 hy0 hu0 (Cvs.Prolate.RegularSolutionEdge.regSol_one _ _)
    (by simp [regU]) hv1
  have hD4 : 4 ≤ D := by
    have : 4 ≤ 4 * c / Real.log c := by rw [le_div_iff₀ hlog0]; linarith
    linarith
  intro t ht
  exact (hmain t ht).trans (factor_le hc hD0 hD5 hD4 hτ0 hτ1.le hτsq hτχ rfl hσ0)

/-- **The endpoint value of a normalised even rung**: if `rung² ≤ A·rung(1)²` on `[0, 1]`, then `1 ≤ 2A·rung(1)²`. -/
theorem one_le_of_sq_le {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) {A : ℝ}
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, regSol (sqC c) (lev c k) t ^ 2 ≤ A) : 1 ≤ 2 * A * rung c k 1 ^ 2 := by
  obtain ⟨-, -, -, -, heven, hnorm⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
  obtain ⟨-, hmul⟩ := Cvs.Prolate.RungEqRegularSolution.rung_eq_mul_regSol h
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, rung c k s ^ 2 ≤ A * rung c k 1 ^ 2 := by
    intro s hs
    rw [hmul s ⟨by linarith [hs.1], hs.2⟩, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hA s hs) (sq_nonneg _)
  have hall : ∀ s ∈ Icc (-1 : ℝ) 1, rung c k s ^ 2 ≤ A * rung c k 1 ^ 2 := by
    intro s hs
    rcases le_or_gt 0 s with h0 | h0
    · exact hpt s ⟨h0, hs.2⟩
    · have := heven (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      rw [neg_neg] at this
      rw [this]
      exact hpt (-s) ⟨by linarith, by linarith [hs.1]⟩
  have hi1 : IntervalIntegrable (fun s => rung c k s ^ 2) volume (-1) 1 :=
    ((Cvs.Prolate.EvenRungsByIndex.continuousOn_rung h).pow 2).intervalIntegrable_of_Icc (by norm_num)
  have hi2 : IntervalIntegrable (fun _ : ℝ => A * rung c k 1 ^ 2) volume (-1) 1 := intervalIntegrable_const
  have hint := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hi1 hi2 hall
  rw [hnorm, intervalIntegral.integral_const] at hint
  simp only [sub_neg_eq_add, smul_eq_mul] at hint
  linarith

/-- **The plunge from the endpoint**: a rung of level `χ < c²` at `c ≥ 1` with `λ ≥ ½` has
`rung(1)²/(8(D + 2c)) ≤ 1 − λ`, `D = c² − χ`. -/
theorem rung_one_sq_le {c : ℝ} {k : ℕ} (hc : 1 ≤ c) (h : ∃ χ, IsLevelIdx c k χ) (hχ : lev c k < c ^ 2)
    (hhalf : 1 / 2 ≤ lamR c k) :
    rung c k 1 ^ 2 / (8 * (c ^ 2 - lev c k + 2 * c)) ≤ 1 - lamR c k := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
  have hedge := Cvs.Prolate.RungFarMassFloor.edge_mass_ge hc hχ hg hg₁ hg₂c hang
  rw [Cvs.Prolate.Envelope.RungExteriorLaw.mass_eq hc0 h, Cvs.Prolate.EvenRungsByIndex.psi_rung h 1 ⟨by norm_num, le_rfl⟩] at hedge
  have hlam : lamR c k = muR c k ^ 2 * (c / (2 * π)) := by
    unfold lamR; rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hD : 0 < 8 * (c ^ 2 - lev c k + 2 * c) := by nlinarith
  rw [div_le_iff₀ hD] at hedge ⊢
  -- `μ²h(1)² = (2π/c)λh(1)²`
  have hmu : muR c k ^ 2 = 2 * π / c * lamR c k := by
    rw [hlam]; field_simp
  have hπc : 0 < π / c := by positivity
  have e : (muR c k * rung c k 1) ^ 2 = 2 * (π / c) * lamR c k * rung c k 1 ^ 2 := by
    rw [mul_pow, hmu]; ring
  rw [e] at hedge
  have h1 : 2 * lamR c k * rung c k 1 ^ 2 ≤ (1 - lamR c k) * (8 * (c ^ 2 - lev c k + 2 * c)) := by
    have : π / c * (2 * lamR c k * rung c k 1 ^ 2) ≤ π / c * ((1 - lamR c k) * (8 * (c ^ 2 - lev c k + 2 * c))) := by
      nlinarith
    exact le_of_mul_le_mul_left this hπc
  nlinarith [sq_nonneg (rung c k 1)]

/-- **The top plunge floor at every `x ≥ 31`**: `1/(224e⁵²c⁶) ≤ 1 − λ_t`, `c = 2πx`. -/
theorem one_sub_lamTop_ge {x : ℕ} (hx : 31 ≤ x) :
    1 / (224 * Real.exp 52 * (2 * π * x) ^ 6) ≤ 1 - Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x := by
  have hx80 := Cvs.Prolate.RungEqRegularSolution.scale_of_31 hx
  set c := 2 * π * (x : ℝ) with hcdef
  have hc0 : 0 < c := by linarith
  have hx1 : 1 ≤ x := by omega
  have hex := Cvs.Prolate.RungEqRegularSolution.exists_top hx80 hx1
  obtain ⟨hDl, -⟩ := Cvs.Prolate.RungFarMassFloor.rung_edge_mass hx80 (j := x - 1) (by omega)
  have hD5 := Cvs.Prolate.TopRungDepthBound.top_depth_le_five hx
  have hsq := regSol_sq_le hx80 hD5 hDl
  have hone := one_le_of_sq_le hex hsq
  have hhalf : 1 / 2 ≤ lamR c (2 * (x - 1)) := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx80 (by omega)
  have hlog0 : 0 < Real.log c := Real.log_pos (by linarith)
  have hD0 : 0 < c ^ 2 - lev c (2 * (x - 1)) := lt_of_lt_of_le (by positivity) hDl
  have hplunge := rung_one_sq_le (by linarith) hex (by linarith) hhalf
  have htop : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lamTop x = lamR c (2 * (x - 1)) := rfl
  rw [htop]
  refine le_trans ?_ hplunge
  set h1 := rung c (2 * (x - 1)) 1 ^ 2
  set D := c ^ 2 - lev c (2 * (x - 1))
  have hDc : 8 * (D + 2 * c) ≤ 56 * c := by linarith
  have hK : 0 < 2 * Real.exp 52 * c ^ 5 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * (8 * (D + 2 * c)) ≤ 56 * c := by linarith
    _ ≤ 56 * c * (2 * (2 * Real.exp 52 * c ^ 5) * h1) := by
        have : 0 ≤ 56 * c := by positivity
        nlinarith
    _ = h1 * (224 * Real.exp 52 * c ^ 6) := by ring

/-- `c⁶e^{−εc} → 0` along `c = 2πx`. -/
theorem tendsto_pow_six_exp {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    Tendsto (fun x : ℕ => K * (2 * π * x) ^ 6 * Real.exp (-(ε * (2 * π * x)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℕ => ε * (2 * π * (x : ℝ))) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)).const_mul_atTop hε
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).comp h1).const_mul (K / ε ^ 6)
  rw [mul_zero] at h2
  refine h2.congr fun x => ?_
  simp only [Function.comp]
  field_simp

/-- **The top plunge floor** (w-kstar Lemma W): `Cvs.Prolate.Gram.DeepRemainderCellFloors.TopPlungeFloor`. -/
theorem topPlungeFloor : Cvs.Prolate.Gram.DeepRemainderCellFloors.TopPlungeFloor := by
  intro ε hε
  have hev := (tendsto_pow_six_exp hε (224 * Real.exp 52)).eventually (gt_mem_nhds one_pos)
  filter_upwards [hev, eventually_ge_atTop 31] with x hx h31
  refine le_trans ?_ (one_sub_lamTop_ge h31)
  have hc : 0 < 2 * π * (x : ℝ) := by have := Cvs.Prolate.RungEqRegularSolution.scale_of_31 h31; linarith
  rw [le_div_iff₀ (by positivity)]
  calc Real.exp (-(ε * (2 * π * x))) * (224 * Real.exp 52 * (2 * π * x) ^ 6)
      = 224 * Real.exp 52 * (2 * π * x) ^ 6 * Real.exp (-(ε * (2 * π * x))) := by ring
    _ ≤ 1 := hx.le

end Cvs.Prolate.TopPlungeFloor
