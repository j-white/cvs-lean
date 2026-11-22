import Mathlib
import Cvs.Approximant.ConnesTailWeightedEnergy
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.ConnesWindowCosineComplete
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Finite.SymmetricModeSet
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormNormFloor

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The form truncation passage for the actual Connes window

The unconditional Weil floor makes the floor-shifted form nonnegative.
Its Cauchy–Schwarz inequality controls fixed-test pairings by the shifted error energy.
-/

noncomputable section

open Real Filter MeasureTheory
open scoped InnerProductSpace

namespace Cvs.Approximant.ConnesFormTruncation
open Cvs.ZeroCounting

/-- The window Weil bilinear form shifted by its unconditional floor. -/
def shiftedWeil {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) :
    LinearMap.BilinForm ℝ (Cvs.WeilForm.FormDomain.formDomain hL) :=
  Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R - Cvs.WeilForm.WindowFormNormFloor.floorConst L P R •
    (((innerₗ (Cvs.WeilForm.WeilFormOnWindowL2.window L)).compl₂ (Cvs.WeilForm.FormDomain.formDomain hL).subtype).comp
      (Cvs.WeilForm.FormDomain.formDomain hL).subtype)

theorem shiftedWeil_apply {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (u v : Cvs.WeilForm.FormDomain.formDomain hL) :
    shiftedWeil hL P R u v = Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R u v
      - Cvs.WeilForm.WindowFormNormFloor.floorConst L P R * ⟪(u : Cvs.WeilForm.WeilFormOnWindowL2.window L), (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)⟫_ℝ := by
  simp [shiftedWeil]

/-- The shifted Weil diagonal is its quadratic energy minus the floor energy. -/
theorem shiftedWeil_self {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (u : Cvs.WeilForm.FormDomain.formDomain hL) :
    shiftedWeil hL P R u u = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R u - Cvs.WeilForm.WindowFormNormFloor.floorConst L P R * ‖u‖ ^ 2 := by
  rw [shiftedWeil_apply, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, real_inner_self_eq_norm_sq]
  rfl

/-- The unconditional floor makes the shifted Weil form nonnegative on its whole domain. -/
theorem shiftedWeil_nonneg {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (u : Cvs.WeilForm.FormDomain.formDomain hL) : 0 ≤ shiftedWeil hL P R u u := by
  rw [shiftedWeil_self]
  exact sub_nonneg.mpr (Cvs.WeilForm.FormDomain.weilQW_ge_floor hL P R u)

/-- Cauchy–Schwarz for the Weil form shifted by its unconditional floor. -/
theorem shiftedWeil_cross_sq_le {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (u v : Cvs.WeilForm.FormDomain.formDomain hL) :
    shiftedWeil hL P R u v ^ 2 ≤ shiftedWeil hL P R u u * shiftedWeil hL P R v v := by
  exact (shiftedWeil hL P R).apply_sq_le_of_symm (shiftedWeil_nonneg hL P R)
    ⟨fun u v => by
      simp only [shiftedWeil_apply, (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm hL P R).eq u v,
        real_inner_comm (u : Cvs.WeilForm.WeilFormOnWindowL2.window L) (v : Cvs.WeilForm.WeilFormOnWindowL2.window L), RingHom.id_apply]⟩ u v

/-- Vanishing squared real values imply vanishing values. -/
theorem tendsto_zero_of_sq {f : ℕ → ℝ} (hf : Tendsto (fun n => f n ^ 2) atTop (nhds 0)) :
    Tendsto f atTop (nhds 0) := by
  have hnorm : Tendsto (fun n => ‖f n‖) atTop (nhds 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using hf.sqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Vanishing norm and Weil energy imply vanishing pairing against every fixed domain test. -/
theorem tendsto_QWbil_zero {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (u : ℕ → Cvs.WeilForm.FormDomain.formDomain hL) (v : Cvs.WeilForm.FormDomain.formDomain hL)
    (hu : Tendsto (fun n => ‖u n‖) atTop (nhds 0))
    (hQ : Tendsto (fun n => Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (u n)) atTop (nhds 0)) :
    Tendsto (fun n => Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R (u n) v) atTop (nhds 0) := by
  have hnorm2 : Tendsto (fun n => ‖u n‖ ^ 2) atTop (nhds 0) := by
    simpa using hu.pow 2
  have hs : Tendsto (fun n => shiftedWeil hL P R (u n) (u n)) atTop (nhds 0) := by
    simpa only [shiftedWeil_self, mul_zero, sub_zero] using
      hQ.sub (hnorm2.const_mul (Cvs.WeilForm.WindowFormNormFloor.floorConst L P R))
  have hprod : Tendsto (fun n => shiftedWeil hL P R (u n) (u n) * shiftedWeil hL P R v v)
      atTop (nhds 0) := by simpa only [zero_mul] using hs.mul_const (shiftedWeil hL P R v v)
  have hcross2 : Tendsto (fun n => shiftedWeil hL P R (u n) v ^ 2) atTop (nhds 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun n => shiftedWeil_cross_sq_le hL P R (u n) v) hprod
  have hcross := tendsto_zero_of_sq hcross2
  have hu0 : Tendsto u atTop (nhds 0) := (tendsto_zero_iff_norm_tendsto_zero (f := u)).mpr hu
  have huw : Tendsto (fun n => (u n : Cvs.WeilForm.WeilFormOnWindowL2.window L)) atTop (nhds 0) :=
    ((Cvs.WeilForm.FormDomain.formDomain hL).subtypeₗᵢ.continuous.tendsto _).comp hu0
  have hi : Tendsto (fun n => ⟪(u n : Cvs.WeilForm.WeilFormOnWindowL2.window L), (v : Cvs.WeilForm.WeilFormOnWindowL2.window L)⟫_ℝ)
      atTop (nhds 0) := by
    simpa only [inner_zero_left] using huw.inner tendsto_const_nhds
  have ht := hcross.add (hi.const_mul (Cvs.WeilForm.WindowFormNormFloor.floorConst L P R))
  simpa only [shiftedWeil_apply, sub_add_cancel, mul_zero, add_zero] using ht

/-- The actual cosine class retained through frequency `N`. -/
def connesTrunc {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) :
    Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N)

/-- The actual reflection-even Connes class minus its retained cosine class. -/
def connesError {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
    - connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N

/-- The actual Connes truncation errors vanish in physical `L²` norm. -/
theorem tendsto_connesError_norm {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N => ‖connesError hx N‖) atTop (nhds 0) := by
  have h2 : Tendsto (fun N => ‖connesError hx N‖ ^ 2) atTop (nhds 0) :=
    Cvs.Approximant.ConnesWindowCosineComplete.tendsto_norm_even_connes_error_sq hx
  have h := h2.sqrt
  simp only [Real.sqrt_zero] at h
  exact h.congr fun N => Real.sqrt_sq (norm_nonneg (connesError hx N))

/-- An upper bound on all finite tails passes to the actual omitted Connes class. -/
theorem Q_connesError_le_of_finite_tails {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (P R N : ℕ) (c : ℝ)
    (hfinite : ∀ J, N ≤ J →
      Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R
        (connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) J - connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N) ≤ c) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R (connesError hx N) ≤ c := by
  let E := Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
  have ht : Tendsto (fun J => ‖connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) J - E‖)
      atTop (nhds 0) := by
    refine (tendsto_connesError_norm hx).congr fun J => ?_
    exact norm_sub_rev E (connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) J)
  have hs := ht.comp (tendsto_add_atTop_nat N)
  have hconv : Tendsto (fun J => ‖(connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (J + N)
      - connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N) - connesError hx N‖) atTop (nhds 0) := by
    refine hs.congr fun J => ?_
    apply congrArg norm
    unfold connesError
    dsimp [E]
    abel
  exact Cvs.WeilForm.InfimumAttainedSphere.lsc_sphere (Real.log_natCast_nonneg x) P R
    (fun J => connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (J + N)
      - connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N) (connesError hx N) hconv c
    (fun J => hfinite (J + N) (by omega))

/-- The actual omitted Connes class has the concrete summable tail energy ceiling. -/
theorem Q_connesError_le_majorant {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (connesError hx N)
      ≤ Cvs.Approximant.ConnesTailWeightedEnergy.majorant x N := by
  apply Q_connesError_le_of_finite_tails hx x (Nat.clog 2 x) N (Cvs.Approximant.ConnesTailWeightedEnergy.majorant x N)
  intro J hNJ
  exact Cvs.Approximant.ConnesTailWeightedEnergy.Q_trunc_sub_le hx hNJ

/-- The actual omitted cosine class vanishes in Weil quadratic energy. -/
theorem tendsto_Q_connesError_zero {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N => Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (connesError hx N)) atTop (nhds 0) := by
  have hnorm2 : Tendsto (fun N => ‖connesError hx N‖ ^ 2) atTop (nhds 0) :=
    Cvs.Approximant.ConnesWindowCosineComplete.tendsto_norm_even_connes_error_sq hx
  have hfloor := hnorm2.const_mul (Cvs.WeilForm.WindowFormNormFloor.floorConst (Real.log x) x (Nat.clog 2 x))
  simp only [mul_zero] at hfloor
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hfloor (Cvs.Approximant.ConnesTailWeightedEnergy.tendsto_majorant_zero hx)
    (fun N => Cvs.WeilForm.FormDomain.weilQW_ge_floor (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (connesError hx N))
    (Q_connesError_le_majorant hx)

/-- The actual omitted cosine class has vanishing Weil pairing against every fixed domain test. -/
theorem tendsto_QWbil_connesError_zero {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (v : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) :
    Tendsto (fun N => Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (connesError hx N) v) atTop (nhds 0) :=
  tendsto_QWbil_zero (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
    (connesError hx) v (tendsto_connesError_norm hx) (tendsto_Q_connesError_zero hx)

/-- Finite omitted-tail pairings converge to the actual omitted class against a fixed cosine test. -/
theorem tendsto_QWbil_finite_tail {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (N : ℕ) (f : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) :
    Tendsto (fun J => Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) J - connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N)
      (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)) atTop
      (nhds (Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (connesError hx N) (Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f))) := by
  let B := Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
  let v := Cvs.Approximant.CosineColumnTailPairing.modeMap (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f
  have h := (tendsto_const_nhds (x := B (connesError hx N) v) (f := atTop (α := ℕ))).sub
    (tendsto_QWbil_connesError_zero hx v)
  simp only [sub_zero] at h
  refine h.congr fun J => ?_
  change B (connesError hx N) v - B (connesError hx J) v = _
  have he : connesError hx N - connesError hx J
      = connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) J - connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N := by
    unfold connesError
    abel
  calc B (connesError hx N) v - B (connesError hx J) v
      = B (connesError hx N - connesError hx J) v := by
        exact (LinearMap.map_sub₂ B (connesError hx N) (connesError hx J) v).symm
    _ = _ := by rw [he]

end Cvs.Approximant.ConnesFormTruncation
