import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Gram.BulkFloorFromFullTwist
import Cvs.Prolate.Gram.DeepCellFloorAmplitude
import Cvs.Prolate.Gram.DeepRemainderCellFloors
import Cvs.Prolate.Gram.EndpointAmplitudeFloor
import Cvs.Prolate.Gram.FarBandResidueWindow
import Cvs.Prolate.Gram.FarTwistResidue
import Cvs.Prolate.Gram.FullTwistOuterCell
import Cvs.Prolate.Gram.PlungeLawBandCellFloor
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.TunnellingFloorSumPlunge
import Cvs.Prolate.TopPlungeFloor
import Cvs.Route.Visibility.LayerFloorDeepRemainderB

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV from central-square exclusion alone at the cut

The far residue holds at every `ρ > 0` once PotFloor and BandFloor give the cell floors, so
`CentralSquareFloor T₀ ε ρ` follows from central-square exclusion at the cut, `CentralSquareCut T₀ ε`, and hV
follows from it at any `ε < √2(½ − μ*C₀∞(57/60)/2)`, with no sign condition on `ε` and no residue.
-/

noncomputable section

open Real Filter Finset
open Cvs.ZeroCounting
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (levT)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (C0inf muStar)
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open scoped InnerProductSpace

namespace Cvs.Route.Visibility.VisibilityCentralSquareCut
open Cvs.ZeroCounting

/-- **Central-square exclusion at the cut `T₀`**: eventually the first rung `k₀` of `{T ≥ T₀}` exists and the
central-square exclusion `1 − ε` holds on its layer. -/
def CentralSquareCut (T₀ ε : ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ k₀ : Fin x, T₀ ≤ levT x k₀ ∧ (∀ j < k₀, levT x j < T₀) ∧ Cvs.Prolate.Gram.FullTwistOuterCell.CentralSquarePair x k₀ ε

/-- Central-square exclusion is monotone in `ε`. -/
theorem centralSquarePair_mono {x : ℕ} {k : Fin x} {ε ε' : ℝ} (h : Cvs.Prolate.Gram.FullTwistOuterCell.CentralSquarePair x k ε)
    (hε : ε ≤ ε') : Cvs.Prolate.Gram.FullTwistOuterCell.CentralSquarePair x k ε' := fun v =>
  le_trans (mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (h v)

/-- `CentralSquareCut` is monotone in `ε`. -/
theorem CentralSquareCut.mono {T₀ ε ε' : ℝ} (h : CentralSquareCut T₀ ε) (hε : ε ≤ ε') : CentralSquareCut T₀ ε' := by
  filter_upwards [h] with x ⟨k₀, h1, h2, h3⟩
  exact ⟨k₀, h1, h2, centralSquarePair_mono h3 hε⟩

/-- (EF′) at `T₀` and `ρ > 0` turn central-square exclusion at the cut into `CentralSquareBandFloor T₀ ε ρ`. -/
theorem centralSquareBandFloor_of_cut {T₀ ε ρ : ℝ} (hE : Cvs.Route.Visibility.LayerFloorDeepRemainderB.EFprime T₀) (hρ : 0 < ρ)
    (h : CentralSquareCut T₀ ε) : Cvs.Prolate.Gram.FarTwistResidue.CentralSquareBandFloor T₀ ε ρ := by
  filter_upwards [h, Cvs.Prolate.Gram.FarBandResidueWindow.farBandRes_of_efprime hE hρ] with x ⟨k₀, h1, h2, h3⟩ hF
  exact ⟨k₀, h1, h2, h3, hF k₀ h1 h2⟩

/-- **`CentralSquareFloor` from central-square exclusion at the cut**: with (EF′) at `T₀`, every `ρ > 0`. -/
theorem centralSquareFloor_of_cut {T₀ ε ρ : ℝ} (hE : Cvs.Route.Visibility.LayerFloorDeepRemainderB.EFprime T₀) (hρ : 0 < ρ)
    (h : CentralSquareCut T₀ ε) : Cvs.Prolate.Gram.FullTwistOuterCell.CentralSquareFloor T₀ ε ρ := by
  filter_upwards [centralSquareBandFloor_of_cut hE hρ h, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x ⟨k₀, h1, h2, h3, h4⟩ hx
  exact ⟨k₀, h1, h2, h3, Cvs.Prolate.Gram.FarTwistResidue.farTwistRes_of_farBandRes hx h4⟩

/-- (EF′) at every cut `T₀ < 1` from the discrete potential and the band floor. -/
theorem efprime_of_pot_band (hPot : Cvs.Prolate.Gram.DeepCellFloorAmplitude.PotFloor) (hBF : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor) {T₀ : ℝ} (hT₀ : T₀ < 1) :
    Cvs.Route.Visibility.LayerFloorDeepRemainderB.EFprime T₀ :=
  have hD := Cvs.Prolate.Gram.EndpointAmplitudeFloor.deepCellFloor_of_potFloor hPot
  Cvs.Prolate.Gram.DeepRemainderCellFloors.efprime_of_cellFloors hD (Cvs.Prolate.Gram.PlungeLawBandCellFloor.bandCellFloor_of_bandFloor hBF hD) Cvs.Prolate.TopPlungeFloor.topPlungeFloor hT₀

/-- **`CentralSquareFloor T₀ ε ρ` from `CentralSquareCut T₀ ε`**, PotFloor and BandFloor, for `T₀ < 1`, `ρ > 0`. -/
theorem centralSquareFloor_of_cut_pot_band {T₀ ε ρ : ℝ} (hT₀ : T₀ < 1) (hρ : 0 < ρ) (hPot : Cvs.Prolate.Gram.DeepCellFloorAmplitude.PotFloor)
    (hBF : Cvs.Prolate.Gram.TunnellingFloorSumPlunge.BandFloor) (h : CentralSquareCut T₀ ε) : Cvs.Prolate.Gram.FullTwistOuterCell.CentralSquareFloor T₀ ε ρ :=
  centralSquareFloor_of_cut (efprime_of_pot_band hPot hBF hT₀) hρ h

/-- Below the threshold `θ > 0`, `ε` splits as `ε' = max ε 0` and `ρ = (θ − ε')/2` with `0 ≤ ε' + ρ < θ`. -/
theorem split_threshold {ε θ : ℝ} (hθ : 0 < θ) (hε : ε < θ) :
    ε ≤ max ε 0 ∧ 0 < (θ - max ε 0) / 2 ∧ 0 ≤ max ε 0 + (θ - max ε 0) / 2 ∧
      max ε 0 + (θ - max ε 0) / 2 < θ := by
  have h1 : max ε 0 < θ := max_lt hε hθ
  have h2 : 0 ≤ max ε 0 := le_max_right _ _
  exact ⟨le_max_left _ _, by linarith, by linarith, by linarith⟩

end Cvs.Route.Visibility.VisibilityCentralSquareCut

end
