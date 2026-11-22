import Mathlib
import Cvs.StepA.ConstantTrialFloorAtTwo
import Cvs.StepA.DirichletCosineTrial
import Cvs.StepA.EvenMultiplierAtTwo
import Cvs.StepA.OddSectorClearsTrialAtTwo
import Cvs.StepA.StepAAtTwoAssembled
import Cvs.StepA.StepAFromTwoGaps
import Cvs.StepA.StepAPredicate
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.BottomAttained
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.PlaneHyperplaneTraceCap
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# The even plane gap at `x = 2`, and step (a) unconditionally

`Cvs.WeilForm.PlaneHyperplaneTraceCap.even_plane_bound` on `evenW`, the `reflW`-even window subspace at `L = log 2`: the constant
trial `enorm` lives there outright, the plane `V ≤ evenSub` is carried in through `formDomain ↪ window`,
and `hpair` applies verbatim. The output is `hplane` in `Cvs.StepA.StepAAtTwoAssembled.stepA_x2`'s shape; step (a) follows.
-/

noncomputable section

open MeasureTheory
open Cvs.StepA.EvenMultiplierAtTwo Cvs.StepA.ConstantTrialFloorAtTwo

namespace Cvs.StepA.EvenPlaneGapAtTwo

theorem reflW_add {L : ℝ} (u v : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflW (u + v)
      = Cvs.WeilForm.WindowReflectionSymmetry.reflW u + Cvs.WeilForm.WindowReflectionSymmetry.reflW v := by
  apply Subtype.ext
  show Cvs.WeilForm.WindowReflectionSymmetry.refl L ((u + v : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 volume)
      = ((Cvs.WeilForm.WindowReflectionSymmetry.reflW u + Cvs.WeilForm.WindowReflectionSymmetry.reflW v : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 volume)
  rw [Submodule.coe_add, Submodule.coe_add]
  exact Cvs.WeilForm.EvenOddSplitForm.refl_add L _ _

/-- The reflW-even window subspace at `L = log 2`. -/
def evenW : Submodule ℝ (Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) where
  carrier := {v | Cvs.WeilForm.WindowReflectionSymmetry.reflW v = v}
  add_mem' := by
    intro a b ha hb
    show Cvs.WeilForm.WindowReflectionSymmetry.reflW (a + b) = a + b
    rw [reflW_add, ha, hb]
  zero_mem' := by
    show Cvs.WeilForm.WindowReflectionSymmetry.reflW 0 = 0
    have := reflW_smul (L := Real.log 2) 0 (0 : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
    simpa using this
  smul_mem' := by
    intro c a ha
    show Cvs.WeilForm.WindowReflectionSymmetry.reflW (c • a) = c • a
    rw [reflW_smul, ha]

/-- reflD-fixed on the form domain ⇒ reflW-fixed as a window element. -/
theorem reflW_of_mem_evenSub {v : Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le}
    (hv : v ∈ Cvs.StepA.StepAFromTwoGaps.evenSub Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflW (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
      = (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := by
  have h : Cvs.WeilForm.WindowReflectionSymmetry.reflD Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le v = v := hv
  exact congrArg Subtype.val h

/-- The plane, carried into `evenW`. -/
noncomputable def planeW (V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le)) :
    Submodule ℝ ↥evenW :=
  Submodule.comap evenW.subtype
    (Submodule.map (Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le).subtype V)

theorem map_le_evenW {V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le)}
    (hV : V ≤ Cvs.StepA.StepAFromTwoGaps.evenSub Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le) :
    Submodule.map (Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le).subtype V ≤ evenW := by
  rintro _ ⟨v, hvV, rfl⟩
  exact reflW_of_mem_evenSub (hV hvV)

theorem finrank_planeW {V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le)}
    (h2 : Module.finrank ℝ V = 2)
    (hV : V ≤ Cvs.StepA.StepAFromTwoGaps.evenSub Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le) :
    Module.finrank ℝ (planeW V) = 2 := by
  have hmap : Submodule.map evenW.subtype (planeW V)
      = Submodule.map (Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le).subtype V := by
    unfold planeW
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (map_le_evenW hV)]
  have h1 := Submodule.finrank_map_subtype_eq evenW (planeW V)
  have h3 := Submodule.finrank_map_subtype_eq
    (Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le) V
  rw [hmap, h3] at h1
  omega

theorem enorm_mem_evenW : enorm ∈ evenW := reflW_enorm

set_option synthInstance.maxHeartbeats 200000 in
/-- **The even plane gap at `x = 2`**, in the shape `Cvs.StepA.StepAAtTwoAssembled.stepA_x2` consumes. -/
theorem hplane (V : Submodule ℝ (Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le))
    (h2 : Module.finrank ℝ V = 2)
    (hV : V ≤ Cvs.StepA.StepAFromTwoGaps.evenSub Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le) :
    ∃ v ∈ V, v ≠ 0 ∧ (1/40 : ℝ) * ‖v‖ ^ 2 ≤ Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc 100 2 1
      (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := by
  let e : ↥evenW := ⟨enorm, enorm_mem_evenW⟩
  have hQ : ∀ w : ↥evenW, Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc 100 2 1 (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
      = Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * ‖w‖ ^ 2 + Dsym (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
        + poleForm (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := by
    intro w; rw [weilQWTrunc_decomp, Submodule.coe_norm w]; ring
  have hpole : ∀ w : ↥evenW, 0 ≤ poleForm (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) :=
    fun w => poleForm_nonneg (even_rep w.2)
  have hcap : ∀ w : ↥evenW, lamstar * (‖w‖ ^ 2 - Msym (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
      ≤ Dsym (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := by
    intro w; rw [Submodule.coe_norm w]; exact cap _
  have hpairW : ∀ u v : ↥evenW, ‖u‖ = 1 → ‖v‖ = 1 → (inner ℝ u v : ℝ) = 0 →
      Msym (u : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) + Msym (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
        ≤ (315/1000 : ℝ) := by
    intro u v hu hv huv
    refine Cvs.StepA.EvenMultiplierAtTwo.hpair u.2 v.2 ?_ ?_ ?_
    · rw [Submodule.coe_norm u, Submodule.coe_norm] at hu; exact hu
    · rw [Submodule.coe_norm v, Submodule.coe_norm] at hv; exact hv
    · rw [Submodule.coe_inner, Submodule.coe_inner] at huv; exact huv
  have he1 : ‖e‖ = 1 := by
    rw [Submodule.coe_norm e, Submodule.coe_norm]; exact norm_enorm
  have heaW : (274/1000 : ℝ) ≤ Msym (e : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := hea
  have hsmul : ∀ (c : ℝ) (w : ↥evenW), Msym ((c • w : ↥evenW) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
      = c ^ 2 * Msym (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := by
    intro c w; rw [Submodule.coe_smul]; exact Msym_smul c _
  letI instN : NormedAddCommGroup ↥evenW := inferInstance
  letI instI : InnerProductSpace ℝ ↥evenW := inferInstance
  obtain ⟨v', hv'V, hv'0, hbound⟩ := Cvs.WeilForm.PlaneHyperplaneTraceCap.even_plane_bound (E := ↥evenW)
    (Q := fun w : ↥evenW => Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc 100 2 1 (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
    (D := fun w : ↥evenW => Dsym (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
    (M := fun w : ↥evenW => Msym (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
    (pole := fun w : ↥evenW => poleForm (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
    (A0 := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) (lamstar := lamstar) (T := 315/1000) (a := 274/1000) (e := e)
    hQ hpole hcap lamstar_pos.le hpairW he1 heaW hsmul (finrank_planeW h2 hV)
  -- pull back: v' ∈ planeW V ⟹ ∃ v ∈ V with coercions equal
  obtain ⟨v, hvV, hveq⟩ : ∃ v ∈ V, ((v : Cvs.WeilForm.FormDomain.formDomain _) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
      = (v' : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := by
    have h := hv'V
    simp only [planeW, Submodule.mem_comap, Submodule.mem_map, Submodule.coe_subtype] at h
    obtain ⟨v, hvV, hveq⟩ := h
    exact ⟨v, hvV, hveq⟩
  have hnorm : ‖v‖ = ‖v'‖ := by
    rw [Submodule.coe_norm v, Submodule.coe_norm v', Submodule.coe_norm, Submodule.coe_norm, hveq]
  have hA0 := Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.archSymbol_zero_lower'
  refine ⟨v, hvV, ?_, ?_⟩
  · intro h0
    apply hv'0
    apply Subtype.ext
    rw [← hveq, h0]; rfl
  · rw [hveq, hnorm]
    have hcoef : (1/40 : ℝ) ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + lamstar * (1 - (315/1000 - 274/1000)) := by
      rw [lamstar]; norm_num; linarith
    calc (1/40 : ℝ) * ‖v'‖ ^ 2
        ≤ (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + lamstar * (1 - (315/1000 - 274/1000))) * ‖v'‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ ≤ _ := hbound

theorem hgap : (1/100 : ℝ) < 1/40 := by norm_num

/-- **Step (a) at `x = 2`, unconditionally.** -/
theorem stepA_x2_unconditional :
    ∃ η : Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le,
      Cvs.StepA.StepAPredicate.StepA
        (fun v : Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le =>
          Cvs.WeilForm.WindowRepresentative.weilQW 2 1 (v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
        (Cvs.WeilForm.WindowReflectionSymmetry.reflD Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le)
        (Cvs.WeilForm.BottomAttained.lam Cvs.StepA.StepAAtTwoAssembled.log_two_pos 2 1) η :=
  Cvs.StepA.StepAAtTwoAssembled.stepA_x2 (w := Cvs.StepA.DirichletCosineTrial.waveD Cvs.StepA.StepAAtTwoAssembled.log_two_pos)
    (Cvs.StepA.DirichletCosineTrial.waveD_ne_zero _) (β := 1/100)
    (Cvs.StepA.DirichletCosineTrial.trial_beta Cvs.StepA.StepAAtTwoAssembled.log_two_pos)
    (fun o hodd ho => lt_of_le_of_lt (by nlinarith [sq_nonneg ‖o‖])
      (Cvs.StepA.OddSectorClearsTrialAtTwo.odd_bottom hodd ho))
    hgap hplane

end Cvs.StepA.EvenPlaneGapAtTwo
