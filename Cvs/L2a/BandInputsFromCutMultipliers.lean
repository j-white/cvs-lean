import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandInputsClauseSixResidual
import Cvs.L2a.BandRungData
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.CutMultiplierBand
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.OrbitGapIntegerM
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.Envelope.AngularEdgeEnvelope
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungFamilyRangePartners

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung of `BandInputs x a 1` with the cut multipliers of Cvs.L2a.CutMultiplierBand
For `c = 2πx ≥ c₀^F` and `F_j = K_A|ψ_j(1)|`: the cut multipliers `ν_m^{(k)}`, norms `Ncut`, `K₀^c = 23‖g_j‖₁/c²` and
`K_b = KbCut` satisfy clauses (1)–(3) of `BandInputs` at `δ = c^{−1/3} ≤ 1/4`; with a top bound `T ≤ 10⁶F_jc^{−3/4}`
and the bulk bound at `η_B = 700F_j/c`, the residual (Cvs.L2a.BandInputsClauseSixResidual) gives the rung body at `K_r = 1`. Monotone in `K_r`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive

namespace Cvs.L2a.BandInputsFromCutMultipliers

open Cvs.L2a.BandRungOutgoingWave (gL1 nuCut topE bulkE)
open Cvs.L2a.BandECouplingCollar (bandSetG deltaS mainA K0si gX chiX BandInputs)
open Cvs.L2a.CutMultiplierBand (nuCutC Ncut KbCut)

/-- **`BandInputs` is monotone in `K_r`**: the last clause's right side `K_r c^{−1/8}·mainA` is monotone. -/
theorem bandInputs_mono {x : ℕ} {a : Finset.range x → ℝ} {Kr Kr' : ℝ} (hK : Kr ≤ Kr')
    (hin : BandInputs x a Kr) : BandInputs x a Kr' := by
  intro M hM j hj
  obtain ⟨N, ν₁, ν₂, ν₃, K0c, Kb, T, ηB, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hin M hM j hj
  refine ⟨N, ν₁, ν₂, ν₃, K0c, Kb, T, ηB, h0, h1, h2, h3, h4, h5, h6, h7.trans ?_⟩
  have hc : (0 : ℝ) ≤ 2 * π * x := by positivity
  have hA : 0 ≤ mainA (2 * π * x) (gX x j) := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hc _)) hA

/-! ### The scale and the collar -/

/-- Past `c₀^F`, `c = 2πx` is at least `e¹³⁶⁰` and at least `80`. -/
theorem scale_ge {x : ℕ} (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x) :
    exp 1360 ≤ 2 * π * (x : ℝ) ∧ 80 ≤ 2 * π * (x : ℝ) := by
  have hc : exp 1360 ≤ 2 * π * (x : ℝ) := Cvs.L2a.FullSpanThreshold.c0F_bounds.1.trans hx
  exact ⟨hc, by linarith [Real.add_one_le_exp (1360 : ℝ)]⟩

/-- The collar width `δ = c^{−1/3}` is at most `1/4` for `c ≥ 64`. -/
theorem deltaS_le_quarter {c : ℝ} (hc : 64 ≤ c) : deltaS c ≤ 1 / 4 := by
  unfold deltaS
  rw [Real.rpow_neg (by linarith), inv_le_comm₀ (Real.rpow_pos_of_pos (by linarith) _) (by norm_num)]
  calc (1 / 4 : ℝ)⁻¹ = (64 : ℝ) ^ (1 / 3 : ℝ) := by
        rw [show (64 : ℝ) = 4 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    _ ≤ c ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) hc (by norm_num)

/-! ### The rung -/

/-- The edge bound `F_j = K_A|ψ_j(1)|` of band rung `j` at `c = 2πx`, an upper bound for `sup|ψ_j|` (Cvs.Prolate.Envelope.AngularEdgeEnvelope). -/
def fJ (x : ℕ) (j : Finset.range x) : ℝ := Cvs.Prolate.Envelope.AngularEdgeEnvelope.KA * |psi (2 * π * x) (gX x j) 1|

/-- **Clauses (1)–(3) at a band rung**: past `c₀^F`, the cut multipliers with norms `Ncut` at `F_j` are band
multipliers on the collar `c^{−1/3}`, with `N_{m,0} = (K₀^si + 23‖g_j‖₁/c²)/m` and `N_{m,i} ≤ (K_b/m)i!4^i`. -/
theorem mult_rung {x : ℕ} (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x) {M : ℕ}
    {j : Finset.range x} (hj : j ∈ bandSetG (2 * π * x) 10 (chiX x)) :
    0 ≤ KbCut (2 * π * x) (gX x j) (fJ x j) ∧
      (∀ m ∈ Finset.Ico 2 M, Cvs.L2a.BandTransferBandForm.IsBandMult
        (fun η => nuCut (2 * π * x) (gX x j) m m ((2 * π * x) * η))
        (fun η => iteratedDeriv 1 (nuCutC (2 * π * x) (gX x j) m m) (η : ℂ))
        (fun η => iteratedDeriv 2 (nuCutC (2 * π * x) (gX x j) m m) (η : ℂ))
        (fun η => iteratedDeriv 3 (nuCutC (2 * π * x) (gX x j) m m) (η : ℂ))
        (deltaS (2 * π * x)) (Cvs.L2a.OrbitGapIntegerM.Ymax m) (Ncut (2 * π * x) (gX x j) (fJ x j) m)) ∧
      (∀ m ∈ Finset.Ico 2 M, Ncut (2 * π * x) (gX x j) (fJ x j) m 0
        ≤ (K0si (2 * π * x) (gX x j) + 23 * gL1 (gX x j) / (2 * π * x) ^ 2) / m) ∧
      (∀ m ∈ Finset.Ico 2 M, ∀ i ≤ 3, Ncut (2 * π * x) (gX x j) (fJ x j) m i
        ≤ KbCut (2 * π * x) (gX x j) (fJ x j) / m * ((i.factorial : ℝ) / (1 / 4) ^ i)) := by
  obtain ⟨-, hc80⟩ := scale_ge hx
  have hspec := Cvs.Prolate.EvenRungsByIndex.rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)
  obtain ⟨hχ0, hσ, -, -, henv, -⟩ := Cvs.L2a.BandRungData.band_rung_data x hc80 j hj
  have hF1 : |psi (2 * π * x) (gX x j) 1| ≤ fJ x j := henv 1
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  refine ⟨?_, fun m hm => ?_, fun m _ => ?_, fun m hm i _ => ?_⟩
  · unfold KbCut
    have := (abs_nonneg _).trans hF1
    have := Cvs.L2a.CutMultiplierBand.gL1_nonneg (gX x j)
    positivity
  · exact Cvs.L2a.CutMultiplierBand.cut_isBandMult hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1
      hspec.2.2.2.2.1 hc80 hχ0 (by unfold chiX at hσ; linarith) henv (Finset.mem_Ico.1 hm).1
      (deltaS_le_quarter (by linarith))
  · simp [Ncut, Cvs.L2a.CutMultiplierBand.K0c]
  · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ico.1 hm).1
    exact Cvs.L2a.CutMultiplierBand.Ncut_le_band (by linarith) (by linarith) hF1 i

/-- **The rung body of `BandInputs x a 1`**: past `c₀^F`, at `M ≥ 3` and a band rung `j`, a top bound
`|topE| ≤ T√P` with `T ≤ 10⁶F_jc^{−3/4}` and the bulk bound `|bulkE| ≤ (700F_j/c)√P` give the body, witnessed by
`Ncut`, `ν^{(k)}_m`, `K₀^c = 23‖g_j‖₁/c²`, `K_b = KbCut`, `T` and `η_B = 700F_j/c`. -/
theorem bandInputs_rung {x : ℕ} (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x) (a : Finset.range x → ℝ)
    (M : ℕ) {j : Finset.range x} (hj : j ∈ bandSetG (2 * π * x) 10 (chiX x)) {T : ℝ}
    (hT : T ≤ 10 ^ 6 * fJ x j * (2 * π * x) ^ (-(3 / 4 : ℝ)))
    (htop : |topE (2 * π * x) (gX x j) a (chiX x) (gX x) M|
      ≤ T * √(∫ ξ in Ioi 1, (∑ i, a i * psi (2 * π * x) (gX x i) ξ) ^ 2))
    (hbulk : |bulkE (2 * π * x) (gX x j) a (chiX x) (gX x) M|
      ≤ 700 * fJ x j / (2 * π * x) * √(∫ ξ in Ioi 1, (∑ i, a i * psi (2 * π * x) (gX x i) ξ) ^ 2)) :
    ∃ (N : ℕ → ℕ → ℝ) (ν₁ ν₂ ν₃ : ℕ → ℝ → ℂ) (K0c Kb T ηB : ℝ), 0 ≤ K0c ∧ 0 ≤ Kb ∧
      (∀ m ∈ Finset.Ico 2 M, Cvs.L2a.BandTransferBandForm.IsBandMult
        (fun η => nuCut (2 * π * x) (gX x j) m m ((2 * π * x) * η))
        (ν₁ m) (ν₂ m) (ν₃ m) (deltaS (2 * π * x)) (Cvs.L2a.OrbitGapIntegerM.Ymax m) (N m)) ∧
      (∀ m ∈ Finset.Ico 2 M, N m 0 ≤ (K0si (2 * π * x) (gX x j) + K0c) / m) ∧
      (∀ m ∈ Finset.Ico 2 M, ∀ i ≤ 3, N m i ≤ Kb / m * ((i.factorial : ℝ) / (1 / 4) ^ i)) ∧
      |topE (2 * π * x) (gX x j) a (chiX x) (gX x) M|
        ≤ T * √(∫ ξ in Ioi 1, (∑ i, a i * psi (2 * π * x) (gX x i) ξ) ^ 2) ∧
      |bulkE (2 * π * x) (gX x j) a (chiX x) (gX x) M|
        ≤ ηB * √(∫ ξ in Ioi 1, (∑ i, a i * psi (2 * π * x) (gX x i) ξ) ^ 2) ∧
      gL1 (gX x j) * √(54 * (π ^ 2 / 12 - 11 / 16) / (π * (2 * π * x) ^ 3))
          + K0c * √((2 * π * x) * Cvs.L2a.BandRungOutgoingWave.collarK (deltaS (2 * π * x)) (deltaS (2 * π * x)))
          + Kb * Cvs.L2a.BandRungOutgoingWave.tauBar (2 * π * x) (1 / 2) (deltaS (2 * π * x)) (1 / 4)
            * √(8 * (1 + 1 / deltaS (2 * π * x)) * (Fintype.card (Finset.range x) : ℝ))
          + T + ηB
        ≤ 1 * (2 * π * x) ^ (-(1 / 8 : ℝ)) * mainA (2 * π * x) (gX x j) := by
  obtain ⟨hc, hc80⟩ := scale_ge hx
  obtain ⟨hKb0, hIs, hN0, hN⟩ := mult_rung (M := M) hx hj
  have hG := (Cvs.L2a.BandRungData.band_rung_data x hc80 j hj).2.2.2.2.2
  have hF0 : 0 ≤ fJ x j :=
    mul_nonneg (by linarith [Cvs.Prolate.Envelope.AngularEdgeEnvelope.one_le_KA]) (abs_nonneg _)
  have hη0 : 0 ≤ 700 * fJ x j / (2 * π * x) := by positivity
  have hK0c : 0 ≤ 23 * gL1 (gX x j) / (2 * π * x) ^ 2 := by
    have := Cvs.L2a.CutMultiplierBand.gL1_nonneg (gX x j); positivity
  have hres := Cvs.L2a.BandInputsClauseSixResidual.residual_span (g := gX x j) (KA := Cvs.Prolate.Envelope.AngularEdgeEnvelope.KA)
    (K0c := 23 * gL1 (gX x j) / (2 * π * x) ^ 2) hc le_rfl hG le_rfl hKb0 le_rfl
    (by simpa only [fJ, mul_assoc] using hT) hη0 le_rfl
  exact ⟨fun m => Ncut (2 * π * x) (gX x j) (fJ x j) m,
    fun m η => iteratedDeriv 1 (nuCutC (2 * π * x) (gX x j) m m) (η : ℂ),
    fun m η => iteratedDeriv 2 (nuCutC (2 * π * x) (gX x j) m m) (η : ℂ),
    fun m η => iteratedDeriv 3 (nuCutC (2 * π * x) (gX x j) m m) (η : ℂ),
    23 * gL1 (gX x j) / (2 * π * x) ^ 2, KbCut (2 * π * x) (gX x j) (fJ x j), T, 700 * fJ x j / (2 * π * x),
    hK0c, hKb0, hIs, hN0, hN, htop, hbulk, hres⟩

/-! ### Assembly over the band -/

/-- The top-cut input: at every `M ≥ 3` and band rung `j`, `|topE| ≤ T√P` for some `T ≤ 10⁶F_jc^{−3/4}`. -/
def TopInput (x : ℕ) (a : Finset.range x → ℝ) : Prop :=
  ∀ M : ℕ, 3 ≤ M → ∀ j ∈ bandSetG (2 * π * x) 10 (chiX x), ∃ T : ℝ,
    T ≤ 10 ^ 6 * fJ x j * (2 * π * x) ^ (-(3 / 4 : ℝ)) ∧
    |topE (2 * π * x) (gX x j) a (chiX x) (gX x) M|
      ≤ T * √(∫ ξ in Ioi 1, (∑ i, a i * psi (2 * π * x) (gX x i) ξ) ^ 2)

/-- The bulk input: at every `M ≥ 3` and band rung `j`, `|bulkE| ≤ (700F_j/c)√P`. -/
def BulkInput (x : ℕ) (a : Finset.range x → ℝ) : Prop :=
  ∀ M : ℕ, 3 ≤ M → ∀ j ∈ bandSetG (2 * π * x) 10 (chiX x),
    |bulkE (2 * π * x) (gX x j) a (chiX x) (gX x) M|
      ≤ 700 * fJ x j / (2 * π * x) * √(∫ ξ in Ioi 1, (∑ i, a i * psi (2 * π * x) (gX x i) ξ) ^ 2)

/-- **`BandInputs x a 1` from the top and bulk inputs** past `c₀^F`; the multiplier clauses come from Cvs.L2a.CutMultiplierBand. -/
theorem bandInputs_of_cuts {x : ℕ} (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x) {a : Finset.range x → ℝ}
    (htop : TopInput x a) (hbulk : BulkInput x a) : BandInputs x a 1 := by
  intro M hM j hj
  obtain ⟨T, hT, htb⟩ := htop M hM j hj
  exact bandInputs_rung hx a M hj hT htb (hbulk M hM j hj)

end Cvs.L2a.BandInputsFromCutMultipliers
