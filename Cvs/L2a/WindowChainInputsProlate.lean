import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandCouplingDischarged
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandSumThreshold
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorBandCoupling
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullSpanConditional
import Cvs.L2a.FullSpanFromScale
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.FullSpanInstance
import Cvs.L2a.FullSpanLowConstant
import Cvs.L2a.FullSpanProlateFamily
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullSpanWiring
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.JointMainTerm
import Cvs.L2a.MiddlePartQStep
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainFromInputs
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LandauHalfEvenSpectrum
import Cvs.Prolate.LandauLowerPivot
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window chain's four inputs on `Finset.range x` of the prolate family

`FullSpanInstance`'s integer floors with `FullSpanFromScale`'s band inputs pass to `M → ∞` (Cvs.L2a.FullTailFloorLimit): `κ_F P_∞ ≤ N_∞` with `κ_F ≥ 1/38`, `FullSpanFromScale`'s
`b̄N_∞ ≤ W_∞` at the same `κ_F`, Landau's pivot (Cvs.Prolate.LandauLowerPivot) gives `λ_{4j} ≥ ½` on every rung of the span, band included,
and past `c₀^W = max(c₀^F, 16(κ⋆^F)²e^{4B₀^W+4})`, `B₀^W = B₀^F + K_pol(½, 1/38) + 2`, `b̄ − K_pol(½, κ_F) ≥ 3`.
-/

noncomputable section

open MeasureTheory Set Real Filter Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail

namespace Cvs.L2a.WindowChainInputsProlate

open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev muR lamR rung_spec rung_ne_zero psi_rung)
open Cvs.L2a.FrameFloorIntegerM (resLoc)
open Cvs.L2a.FrameFloorBandCoupling (BandCoupling)
open Cvs.L2a.WindowChainFromInputs (KpolL KpolL_anti)

/-! ### The floor at infinity -/

/-- `FullSpanFromScale`'s floor at `c = 2πx`: `kappaFfullG` at `ρ = 7c^{−1/8}`, `σ̲(c)`, `θ̄(κ̄(c, 10, ē_main(1 + ω(1, c))²), D̄)`,
`ε_τ(10)` and `R̄_J`. -/
def kapFX (x : ℕ) : ℝ :=
  Cvs.L2a.FullSpanInstance.kappaFfullG (10 ^ 16) (2 * π * x) x (7 * (2 * π * x) ^ (-(1 / 8 : ℝ)))
    (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow (2 * π * x))
    (Cvs.L2a.BandCouplingDischarged.thetaBar
      (Cvs.L2a.BandSumThreshold.kapBarG (2 * π * x) 10
        (Cvs.L2a.BandECouplingCollar.eMain (2 * π * x) 10 * (1 + Cvs.L2a.BandECouplingCollar.omegaE 1 (2 * π * x)) ^ 2))
      (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))
    (Cvs.L2a.SpanPlungeBound.epsTauFlat 10) Cvs.L2a.JointMainTerm.RbarJ

/-- **The floor at infinity on `Finset.range x`**: past `c₀^F`, for every `a`, `κ_F ≥ 1/38` and
`κ_F Σ_j a_j²∫₁^∞ψ_j² ≤ ∫₁^∞ F_∞(Φ)²`: `FullSpanInstance`'s integer floors at `FullSpanFromScale`'s band inputs, through `FullTailFloorLimit`'s limit. -/
theorem floor_full_span (x : ℕ) (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x) (a : Finset.range x → ℝ) :
    1 / 38 ≤ kapFX x ∧
      kapFX x * ∑ j, a j ^ 2 * (∫ ξ in Ioi 1, psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) ξ ^ 2)
        ≤ ∫ θ in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail
            (fun ξ => ∑ j, a j * psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) ξ) θ ^ 2 := by
  classical
  unfold kapFX
  set c : ℝ := 2 * π * x with hcdef
  set ω := Cvs.L2a.BandECouplingCollar.omegaE 1 c with hωdef
  set e := Cvs.L2a.BandECouplingCollar.eMain c 10 * (1 + ω) ^ 2 with hedef
  set θ := Cvs.L2a.BandCouplingDischarged.thetaBar (Cvs.L2a.BandSumThreshold.kapBarG c 10 e)
    (Cvs.Prolate.PlungeMassTrace.plungeBound c) with hθdef
  set S := Cvs.L2a.BandECouplingCollar.bandSetG c 10 (fun j : Finset.range x => lev c (2 * (j : ℕ))) with hSdef
  -- the scale
  have hc80' := Cvs.L2a.FullSpanProlateFamily.c80_le_exp.trans (Cvs.L2a.FullSpanThreshold.c0F_bounds.1.trans hx)
  have hc16 : (10 : ℝ) ^ 16 ≤ c := le_trans (by norm_num) hc80'
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  have hc1 : (1 : ℝ) ≤ c := le_trans (by norm_num) hc16
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc16
  have hL := Cvs.Prolate.LandauLowerPivot.landau_lower_pivot x hc80
  have hspec := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)
  have hspec' := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_partner hL j)
  have hJx : ((x : ℕ) : ℝ) ≤ c / 4 + 1 := Cvs.L2a.FullSpanProlateFamily.x_le x
  have hJ : (Fintype.card (Finset.range x) : ℝ) ≤ c / 4 + 1 := by
    rw [Cvs.L2a.FullSpanProlateFamily.card_range]; exact hJx
  have hρ : ∀ M : ℕ, 3 ≤ M →
      resLoc c (Fintype.card (Finset.range x)) M ≤ 7 * c ^ (-(1 / 8 : ℝ)) := by
    rw [Cvs.L2a.FullSpanProlateFamily.card_range]; exact Cvs.L2a.FullSpanProlateFamily.resLoc_le_rhoX hc16
  have hσ0 := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (c := c) (by linarith)
  have hσ := Cvs.Prolate.RungFamilyRangePartners.sigmaLow_le_main hc80
  have hχ0 := Cvs.Prolate.RungFamilyRangePartners.lev_main_nonneg hc80
  have hχc : ∀ j : Finset.range x, lev c (2 * (j : ℕ)) < c ^ 2 := fun j => by linarith [hσ j]
  have hχi := Cvs.Prolate.RungFamilyRangePartners.lev_main_injective hc80
  -- the E-coupling and the rung coupling on the band at edge `10`, at `K_r = 1`
  have hω0 : 0 ≤ ω := Cvs.L2a.BandECouplingCollar.omegaE_nonneg zero_le_one hc0.le
  have hω1 : ω ≤ 1 / 1000 := Cvs.L2a.BandECouplingCollar.omegaE_le (by norm_num) hx
  have he : 0 ≤ e := mul_nonneg (Cvs.L2a.BandECouplingCollar.eMain_nonneg hc80) (sq_nonneg _)
  have hE : Cvs.L2a.BandCouplingDischarged.ECoupling c (fun j : Finset.range x => rung c (2 * (j : ℕ))) a S e :=
    Cvs.L2a.BandECouplingCollar.eCoupling_band x hc80 a zero_le_one (Cvs.L2a.FullSpanFromScale.bandInputs_closed x hx a)
  have hband : ∀ j ∈ S, c ^ 2 - lev c (2 * (j : ℕ)) ≤ 10 * c := fun j hj => by
    rw [hSdef] at hj
    unfold Cvs.L2a.BandECouplingCollar.bandSetG at hj
    exact (Finset.mem_filter.1 hj).2.le
  have hdeep : ∀ j ∉ S, 10 * c ≤ c ^ 2 - lev c (2 * (j : ℕ)) := fun j hj => by
    by_contra hlt
    exact hj (by rw [hSdef]; unfold Cvs.L2a.BandECouplingCollar.bandSetG; simpa using lt_of_not_ge hlt)
  have hRC := Cvs.L2a.FullSpanInstance.rungCoupling_of_eCouplingG (ι := Finset.range x) a S
    (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
    (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (χ := fun j => lev c (2 * (j : ℕ)))
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    hc80 (Cvs.L2a.BandECouplingCollar.eMain_den_pos hc80) (fun j _ => hχ0 j) (fun j _ => hχc j) hband he hE
  -- the paired deficit on the band
  have hD := Cvs.L2a.BandCouplingDischarged.sum_one_sub_le_plunge_paired (ι := Finset.range x) S hc1
    (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
    (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (h := fun j : Finset.range x => rung c (2 * (j : ℕ) + 1))
    (h₁ := fun j => rung₁ c (2 * (j : ℕ) + 1)) (h₂ := fun j => rung₂ c (2 * (j : ℕ) + 1))
    (χ := fun j => lev c (2 * (j : ℕ))) (χ' := fun j => lev c (2 * (j : ℕ) + 1))
    (μ := fun j => muR c (2 * (j : ℕ))) (μ' := fun j => muR c (2 * (j : ℕ) + 1))
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    (fun j => (hspec' j).1) (fun j => (hspec' j).2.1) (fun j => (hspec' j).2.2.1)
    (fun j => (hspec' j).2.2.2.1)
    hχi.injOn ((Cvs.Prolate.RungFamilyRangePartners.lev_partner_injective hL).injOn)
    (fun i _ j _ => Cvs.Prolate.RungFamilyRangePartners.lev_main_ne_partner hc80 hL i j)
    (fun j _ => (hspec j).2.2.2.2.1) (fun j _ => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j _ => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j _ => (hspec' j).2.2.2.2.1) (fun j _ => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_partner hL j))
    (fun j _ => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_partner hL j))
    (fun j _ => Cvs.Prolate.RungFamilyRangePartners.lev_le_partner hL j)
    (fun j _ => Cvs.Prolate.RungFamilyRangePartners.half_le_lam_partner hc80 hL j)
  -- (BC) on the band
  have hBC : ∀ M : ℕ, 3 ≤ M → BandCoupling c (fun j : Finset.range x => rung c (2 * (j : ℕ)))
      (fun j => muR c (2 * (j : ℕ))) a S Cvs.L2a.FarIntegrationByParts.wF M θ := fun M hM =>
    Cvs.L2a.BandCouplingDischarged.bandCoupling_routeT (ι := Finset.range x) a S
      (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
      (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (χ := fun j => lev c (2 * (j : ℕ)))
      (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
      hc0 hχi (fun j => (hspec j).2.2.2.2.1)
      (fun j => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
      (fun j _ => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
      (fun j _ => Cvs.L2a.BandCouplingDischarged.mass_Ioi_pos
        (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hspec j).1 (hspec j).2.1 (hspec j).2.2.1 (hspec j).2.2.2.1
          hc0).integrable_sq (Cvs.Prolate.RungFamilyRangePartners.mass_main hc80 j))
      (fun j _ => (mul_pos (Cvs.Prolate.SlepianEvenOrdering.mu_pos_of_even_index hc0 (hspec j).1 (hspec j).2.1
        (hspec j).2.2.1 (hspec j).2.2.2.1 (hspec j).2.2.2.2.1
        (rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
        (psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)) (Cvs.Prolate.RungFamilyRangePartners.even_ncard_main hc80 j))
        (Real.sqrt_pos.2 (by positivity))).le)
      (fun j _ => Cvs.Prolate.LandauHalfEvenSpectrum.half_le_lam_of_lower hc0 hL (hspec j).1 (hspec j).2.1 (hspec j).2.2.1
        (hspec j).2.2.2.1 (hspec j).2.2.2.2.1 (rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
        (psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)) (Cvs.Prolate.RungFamilyRangePartners.ncard_main_le hc80 j))
      Cvs.L2a.FarIntegrationByParts.wF M (by unfold Cvs.L2a.BandSumThreshold.kapBarG; positivity) (hRC M hM) hD
  -- the margin
  have hrS : Cvs.L2a.MiddlePartQStep.rStrip c (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      ≤ Cvs.L2a.FullSpanConditional.rSig (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c) :=
    Cvs.L2a.FullSpanConditional.rStrip_le_rSig hc0 hσ0 (Cvs.L2a.FullSpanIndexFloor.sigmaLow_le_five hc80)
  have hm := Cvs.L2a.BandSumThreshold.hm_full hx hω0 hω1
  obtain ⟨hA, h38⟩ := Cvs.L2a.FullSpanInstance.floor_ge_of_margin (J := (x : ℝ))
    (σ₀ := Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c) (θ := θ) hx (Nat.cast_nonneg _) hJx hrS hm
  have hA' : 0 < Cvs.L2a.FullSpanInstance.aJAfullG (10 ^ 16) c (Fintype.card (Finset.range x))
      (7 * c ^ (-(1 / 8 : ℝ))) (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c) θ (Cvs.L2a.SpanPlungeBound.epsTauFlat 10)
      Cvs.L2a.JointMainTerm.RbarJ := by
    rw [Cvs.L2a.FullSpanProlateFamily.card_range]; exact hA
  -- the integer floors
  obtain ⟨-, hFF⟩ := Cvs.L2a.FullSpanInstance.JA_integer_floor_G (ι := Finset.range x) a
    (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
    (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (χ := fun j => lev c (2 * (j : ℕ))) (μ := fun j => muR c (2 * (j : ℕ)))
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    hc16 hχ0 hσ0 hσ hχi (fun j => (hspec j).2.2.2.2.1)
    (fun j => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (Cvs.Prolate.RungFamilyRangePartners.even_ncard_main hc80) hJ (Cvs.Prolate.RungFamilyRangePartners.mass_main hc80) S
    (by norm_num : (5 : ℝ) ≤ 10) hdeep (fun κ hκ M hM => Cvs.L2a.JointMainTerm.main_le_RbarJ hκ hM) hρ hBC hA'
  rw [Cvs.L2a.FullSpanProlateFamily.card_range] at hFF
  -- the limit `M → ∞`
  have hM : ∀ M : ℕ, 3 ≤ M → ∀ j : Finset.range x, 0 < ∫ t in (1 : ℝ)..M, psi c (rung c (2 * (j : ℕ))) t ^ 2 :=
    fun M hM3 j => (Cvs.Prolate.RungFamilyRangePartners.mass_main hc80 j).trans_le
      (Cvs.L2a.FullTailDeepSpan.mass_mono (hspec j).1 (by exact_mod_cast hM3))
  refine ⟨h38, Cvs.L2a.FullTailFloorLimit.floor_limit a (fun j => (hspec j).1) (fun j => (hspec j).2.1)
    (fun j => (hspec j).2.2.1) hc0 ?_⟩
  refine frequently_atTop.2 fun X₀ => ⟨((max 3 ⌈X₀⌉₊ : ℕ) : ℝ), ?_, ?_⟩
  · exact (Nat.le_ceil X₀).trans (by exact_mod_cast le_max_right 3 ⌈X₀⌉₊)
  · exact hFF _ (le_max_left _ _) (hM _ (le_max_left _ _))

/-- **The full-tail bound on `Finset.range x`** past `c₀^F`, at `κ_F = kapFX x` (Cvs.L2a.FullSpanFromScale). -/
theorem fulltail_full_span (x : ℕ) (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x) (a : Finset.range x → ℝ) :
    Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) Cvs.L2a.FullSpanThreshold.kapStarF x (kapFX x)
        * ∫ θ in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail
            (fun ξ => ∑ j, a j * psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) ξ) θ ^ 2
      ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ j, a j * psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) ξ) :=
  (Cvs.L2a.FullSpanFromScale.L2a_full_span_closed x hx a).2.2.2

/-! ### Landau's half on the span -/

/-- **`λ_{4j} ≥ ½` on every rung of the span**, band included: Landau's pivot at `2x − 1` (Cvs.Prolate.LandauLowerPivot) and ORD (Cvs.Prolate.LandauHalfEvenSpectrum). -/
theorem half_le_lamR {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) : 1 / 2 ≤ lamR (2 * π * x) (2 * j) := by
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hex := Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨j, Finset.mem_range.2 hj⟩
  obtain ⟨hh, hh₁, hh₂c, hang, heven, -⟩ := rung_spec hex
  exact Cvs.Prolate.LandauHalfEvenSpectrum.half_le_lam_of_lower hc0 (Cvs.Prolate.LandauLowerPivot.landau_lower_pivot x hx) hh hh₁
    hh₂c hang heven (rung_ne_zero hex) (psi_rung hex)
    (Cvs.Prolate.RungFamilyRangePartners.ncard_main_le hx ⟨j, Finset.mem_range.2 hj⟩)

/-! ### The window threshold -/

/-- `B₀^W = B₀^F + K_pol(½, 1/38) + 2`. -/
def B0W : ℝ := Cvs.L2a.FullSpanThreshold.B0F + KpolL (1 / 2) (1 / 38) + 2

/-- **The window threshold** `c₀^W = max(c₀^F, 16(κ⋆^F)²e^{4B₀^W+4})`. -/
def c0W : ℝ :=
  max Cvs.L2a.FullSpanThreshold.c0F (16 * Cvs.L2a.FullSpanThreshold.kapStarF ^ 2 * exp (4 * B0W + 4))

theorem c0F_le_c0W : Cvs.L2a.FullSpanThreshold.c0F ≤ c0W := le_max_left _ _

/-- **`b′ ≥ 3` past `c₀^W`**: for `0 ≤ J ≤ c/4 + 1` and `κ_F ≥ 1/38`, `bBarFull(c, κ⋆^F, J, κ_F) − K_pol(½, κ_F) ≥ 3`;
`½log(T/2) − B₀^F ≤ b̄` (Cvs.L2a.FullSpanThreshold), `T ≥ √c/(2κ⋆^F) ≥ 2e^{2B₀^W+2}`, and `K_pol(½, ·)` decreases. -/
theorem bPrimeW_ge {c J κF : ℝ} (hc : c0W ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) (hκF : 1 / 38 ≤ κF) :
    3 ≤ Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF J κF - KpolL (1 / 2) κF := by
  have hcF : Cvs.L2a.FullSpanThreshold.c0F ≤ c := le_trans c0F_le_c0W hc
  have hc16 : (10 : ℝ) ^ 16 ≤ c := le_trans (le_max_left _ _) hcF
  have hcB : 16 * Cvs.L2a.FullSpanThreshold.kapStarF ^ 2 * exp (4 * B0W + 4) ≤ c := le_trans (le_max_right _ _) hc
  obtain ⟨hT, -⟩ := Cvs.L2a.FullSpanThreshold.bBarFull_ge_one hcF hJ0 hJ hκF
  have hκ2 : (2 : ℝ) ≤ Cvs.L2a.FullSpanThreshold.kapStarF := le_max_left _ _
  have hκE : 76 * Cvs.L2a.FullSpanLowConstant.EbarFull ≤ Cvs.L2a.FullSpanThreshold.kapStarF := le_max_right _ _
  have hb := Cvs.L2a.FullSpanThreshold.bBarFull_ge_log hc16 hκ2 hκE hJ hκF hT
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  have hκ0 : 0 < Cvs.L2a.FullSpanThreshold.kapStarF := by linarith
  have hsc := Real.sqrt_pos.2 hc0
  have hlog : 1 + Real.log c ≤ 2 * √c := by
    have h1 := Real.log_le_sub_one_of_pos hsc
    rw [Real.log_sqrt hc0.le] at h1
    linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hTge : √c / (2 * Cvs.L2a.FullSpanThreshold.kapStarF)
      ≤ Cvs.L2a.FullTailDeepSpan.TL c Cvs.L2a.FullSpanThreshold.kapStarF := by
    unfold Cvs.L2a.FullTailDeepSpan.TL
    have e : √c / (2 * Cvs.L2a.FullSpanThreshold.kapStarF)
        = c / (Cvs.L2a.FullSpanThreshold.kapStarF * (2 * √c)) := by
      rw [show c = √c * √c from (Real.mul_self_sqrt hc0.le).symm]
      rw [Real.sqrt_mul_self hsc.le]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left hc0.le (by positivity) (mul_le_mul_of_nonneg_left hlog hκ0.le)
  have hE := exp_pos (2 * B0W + 2)
  have hsq : 4 * Cvs.L2a.FullSpanThreshold.kapStarF * exp (2 * B0W + 2) ≤ √c := by
    have e : 16 * Cvs.L2a.FullSpanThreshold.kapStarF ^ 2 * exp (4 * B0W + 4)
        = (4 * Cvs.L2a.FullSpanThreshold.kapStarF * exp (2 * B0W + 2)) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e] at hcB
    calc 4 * Cvs.L2a.FullSpanThreshold.kapStarF * exp (2 * B0W + 2)
        = √((4 * Cvs.L2a.FullSpanThreshold.kapStarF * exp (2 * B0W + 2)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √c := Real.sqrt_le_sqrt hcB
  have hT2 : 2 * exp (2 * B0W + 2) ≤ Cvs.L2a.FullTailDeepSpan.TL c Cvs.L2a.FullSpanThreshold.kapStarF := by
    refine le_trans ?_ hTge
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hl : 2 * B0W + 2 ≤ Real.log (Cvs.L2a.FullTailDeepSpan.TL c Cvs.L2a.FullSpanThreshold.kapStarF / 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have hK := KpolL_anti (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 38) hκF
  unfold B0W at hl
  linarith

/-- **`b′κ_F ≥ 1/16` past `c₀^W`**: `b′ ≥ 3`, `κ_F ≥ 1/38`. -/
theorem margin_W {c J κF : ℝ} (hc : c0W ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) (hκF : 1 / 38 ≤ κF) :
    1 / 16 ≤ (Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF J κF - KpolL (1 / 2) κF) * κF := by
  have h3 := bPrimeW_ge hc hJ0 hJ hκF
  nlinarith

end Cvs.L2a.WindowChainInputsProlate
