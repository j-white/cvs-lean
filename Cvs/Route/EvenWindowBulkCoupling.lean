import Mathlib
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.CoreSchurForm
import Cvs.Route.CouplingBoundGivesCore
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.Upstream.FormPositivitySumCoupling
import Cvs.Upstream.MergedBoundSchurForm
import Cvs.Upstream.MergedLowerBoundPositivity
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.NestedWindowsMonotoneBottom
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TwoIndependentClasses
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.WeilForm.WindowSetNonempty

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Even-sector window positivity from a bulk floor and a form coupling against `R₁`

On the even classes `Ev x` against `R₁ = evenPart(R_F)`, `Q ≥ 0` on `R₁`, `EvenBulkFloor x b` and `EvenFormCoupling x δ`
with `b, δ ≥ 0` give `Q ≥ 0` on `Ev x`, so RH when they hold at infinitely many `x` (Cvs.WeilForm.ReflectionEvenPositivityRH); RH gives them at `b = δ = 0`.
At `δ < 1` the coupling carries one strict sign across the split: `b > 0` (the even bulk is nonzero) gives `Q ≥ 0` on `R₁`,
and `ReflBound x 1 δ_R` with `δ_R < 1` gives the floor `b = 0`, so either one with the coupling gives RH. Likewise for `D₀`.
-/

noncomputable section

open Real Filter MeasureTheory
open scoped InnerProductSpace

namespace Cvs.Route.EvenWindowBulkCoupling
open Cvs.ZeroCounting

open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx D0)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1 ReflBound)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)

section abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A finite-dimensional `K` leaves room in a larger orthogonal span**: nonzero pairwise orthogonal
`v : ι → E` with `finrank K < |ι|` give a nonzero `w ∈ span(range v) ∩ Kᗮ`. -/
theorem exists_mem_span_orthogonal_ne_zero {ι : Type*} [Fintype ι] {v : ι → E} (hz : ∀ i, v i ≠ 0)
    (ho : Pairwise fun i j => ⟪v i, v j⟫_ℝ = 0) {K : Submodule ℝ E} [FiniteDimensional ℝ K]
    [K.HasOrthogonalProjection] (hK : Module.finrank ℝ K < Fintype.card ι) :
    ∃ w ∈ Submodule.span ℝ (Set.range v), w ∈ Kᗮ ∧ w ≠ 0 := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range v)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  have hV : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = Fintype.card ι :=
    finrank_span_eq_card (linearIndependent_of_ne_zero_of_inner_eq_zero hz ho)
  let f : Submodule.span ℝ (Set.range v) →ₗ[ℝ] K :=
    K.orthogonalProjectionOnto.toLinearMap ∘ₗ (Submodule.span ℝ (Set.range v)).subtype
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by rw [hV]; exact hK)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨u, u.2, Submodule.orthogonalProjectionOnto_eq_zero_iff.1 hu, fun h => hu0 (Subtype.ext h)⟩

/-- `0 ≤ p` from `c² ≤ (1−δ)·p·q` with `δ < 1` and `0 < q`. -/
theorem nonneg_of_sq_le_mul {c p q δ : ℝ} (hδ : δ < 1) (hq : 0 < q) (h : c ^ 2 ≤ (1 - δ) * p * q) :
    0 ≤ p := by
  have h1 : 0 ≤ ((1 - δ) * q) * p := by
    have e : ((1 - δ) * q) * p = (1 - δ) * p * q := by ring
    rw [e]; exact (sq_nonneg c).trans h
  exact nonneg_of_mul_nonneg_right h1 (mul_pos (by linarith) hq)

/-- **The coupling carries a positive bulk value to `R`**: `Coupling B H R δ` with `δ < 1` and one
`w₀ ∈ H ∩ Rᗮ` with `B(w₀,w₀) > 0` give `B ≥ 0` on `R`. -/
theorem nonneg_on_of_coupling {B : LinearMap.BilinForm ℝ E} {H R : Submodule ℝ E} {δ : ℝ} (hδ : δ < 1)
    (hC : Cvs.Upstream.MergedBoundSchurForm.Coupling B H R δ) {w₀ : E} (hw₀H : w₀ ∈ H) (hw₀ : w₀ ∈ Rᗮ) (hpos : 0 < B w₀ w₀) :
    ∀ r ∈ R, 0 ≤ B r r := fun r hr => nonneg_of_sq_le_mul hδ hpos (hC r hr w₀ hw₀H hw₀)

/-- **Orthogonal shells of a min-covariance path**: if `⟪c a, c b⟫ = a` for `0 ≤ a ≤ b ≤ L`, then
`⟪c b − c a, c d − c c'⟫ = 0` for `0 ≤ a ≤ b ≤ c' ≤ d ≤ L`. -/
theorem inner_shell_eq_zero {c : ℝ → E} {L : ℝ}
    (hc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ L → ⟪c a, c b⟫_ℝ = a) {a b c' d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c') (hcd : c' ≤ d) (hd : d ≤ L) : ⟪c b - c a, c d - c c'⟫_ℝ = 0 := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    hc b d (ha.trans hab) (hbc.trans hcd) hd, hc b c' (ha.trans hab) hbc (hcd.trans hd),
    hc a d ha (hab.trans (hbc.trans hcd)) hd, hc a c' ha (hab.trans hbc) (hcd.trans hd)]
  ring

/-- **Shell norms of a min-covariance path**: if `⟪c a, c b⟫ = a` for `0 ≤ a ≤ b ≤ L`, then
`‖c b − c a‖² = b − a` for `0 ≤ a ≤ b ≤ L`. -/
theorem norm_sq_shell {c : ℝ → E} {L : ℝ} (hc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ L → ⟪c a, c b⟫_ℝ = a)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) : ‖c b - c a‖ ^ 2 = b - a := by
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    hc b b (ha.trans hab) le_rfl hb, real_inner_comm (c a) (c b), hc a b ha hab hb,
    hc a a ha le_rfl (hab.trans hb)]
  ring

/-- **A min-covariance path escapes every finite-dimensional subspace**: if `⟪c a, c b⟫ = a` for
`0 ≤ a ≤ b ≤ L`, `L > 0`, and every `c l` lies in `S`, then `S ∩ Kᗮ ≠ 0` for every finite-dimensional `K`. -/
theorem exists_mem_orthogonal_ne_zero_of_minCov {c : ℝ → E} {L : ℝ} (hL : 0 < L)
    (hc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ L → ⟪c a, c b⟫_ℝ = a) {S : Submodule ℝ E} (hS : ∀ l, c l ∈ S)
    (K : Submodule ℝ E) [FiniteDimensional ℝ K] [K.HasOrthogonalProjection] :
    ∃ w ∈ S, w ∈ Kᗮ ∧ w ≠ 0 := by
  set n := Module.finrank ℝ K + 1 with hn_def
  have hn : (0 : ℝ) < n := by positivity
  set h := L / n with hh_def
  have hh : 0 < h := div_pos hL hn
  have hnh : (n : ℝ) * h = L := by rw [hh_def]; field_simp
  have hle : ∀ k : Fin n, (((k : ℕ) + 1 : ℝ) * h) ≤ L := by
    intro k
    have hk : ((k : ℕ) + 1 : ℝ) ≤ n := by exact_mod_cast k.isLt
    rw [← hnh]; exact mul_le_mul_of_nonneg_right hk hh.le
  have h0 : ∀ k : Fin n, (0 : ℝ) ≤ (k : ℕ) * h := fun k => by positivity
  have hstep : ∀ k : Fin n, ((k : ℕ) : ℝ) * h ≤ ((k : ℕ) + 1 : ℝ) * h :=
    fun k => mul_le_mul_of_nonneg_right (by linarith) hh.le
  have hlt : ∀ i j : Fin n, i < j → (((i : ℕ) + 1 : ℝ) * h) ≤ (j : ℕ) * h := by
    intro i j hij
    have : ((i : ℕ) + 1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast hij
    exact mul_le_mul_of_nonneg_right this hh.le
  have hz : ∀ k : Fin n, c (((k : ℕ) + 1 : ℝ) * h) - c ((k : ℕ) * h) ≠ 0 := by
    intro k hk
    have h1 := norm_sq_shell hc (h0 k) (hstep k) (hle k)
    rw [hk, norm_zero] at h1
    nlinarith
  have ho : Pairwise fun i j : Fin n => ⟪c (((i : ℕ) + 1 : ℝ) * h) - c ((i : ℕ) * h),
      c (((j : ℕ) + 1 : ℝ) * h) - c ((j : ℕ) * h)⟫_ℝ = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact inner_shell_eq_zero hc (h0 i) (hstep i) (hlt i j hij) (hstep j) (hle j)
    · rw [real_inner_comm]
      exact inner_shell_eq_zero hc (h0 j) (hstep j) (hlt j i hij) (hstep i) (hle i)
  obtain ⟨w, hw, hwK, hw0⟩ := exists_mem_span_orthogonal_ne_zero hz ho (K := K)
    (by rw [Fintype.card_fin]; omega)
  refine ⟨w, Submodule.span_le.2 ?_ hw, hwK, hw0⟩
  rintro _ ⟨k, rfl⟩
  exact Submodule.sub_mem _ (hS _) (hS _)

end abstract

/-! ### `R₁` inside the even classes -/

instance R1.hasOrthogonalProjection (x : ℕ) : (R1 x).HasOrthogonalProjection :=
  haveI : CompleteSpace (R1 x) := FiniteDimensional.complete ℝ _
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- `R₁` lies in the even classes. -/
theorem R1_le_Ev (x : ℕ) : R1 x ≤ Ev x :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Cvs.Route.L1FloorFromBulkD0.rung_mem_evenSub x j)

/-- `D₀` lies in the even classes. -/
theorem D0_le_Ev (x : ℕ) : D0 x ≤ Ev x :=
  (Cvs.L2a.EvenSectorReflectionBound.D0_le_R1 x).trans (R1_le_Ev x)

/-- The even part of every spine class lies in `R₁`. -/
theorem evenPart_spineMap_mem_R1 (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a) ∈ R1 x := by
  show Cvs.Approximant.D0FloorEvenRungShare.evenPartL (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a) ∈ R1 x
  conv => enter [2, 2]; rw [← Cvs.Approximant.SpineCoefficientMatrix.sum_single x a]
  rw [map_sum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- An even class is orthogonal to the odd part of every class. -/
theorem inner_oddPart_eq_zero {x : ℕ} {w : Dom x} (hw : w ∈ Ev x) (v : Dom x) :
    ⟪w, Cvs.WeilForm.EvenOddSplitForm.oddPart (Real.log_natCast_nonneg x) v⟫_ℝ = 0 := by
  have h := Cvs.WeilForm.EvenOddSplitForm.inner_reflD (Real.log_natCast_nonneg x) w (Cvs.WeilForm.EvenOddSplitForm.oddPart _ v)
  have hw' : Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) w = w := hw
  rw [hw', Cvs.WeilForm.EvenOddSplitForm.reflD_oddPart, Cvs.WeilForm.TwoIndependentClasses.inner_coe, Submodule.coe_neg, Submodule.coe_neg, inner_neg_right,
    ← Cvs.WeilForm.TwoIndependentClasses.inner_coe] at h
  linarith

/-! ### A nonzero even bulk vector -/

/-- The centred box `1_(0,l]` at scale `x` (Cvs.WeilForm.ReflectionEvenPositivityRH), and `0` unless `0 < l ≤ log x`. -/
def cbox (x : ℕ) (l : ℝ) : Dom x :=
  if h : 0 < l ∧ l ≤ Real.log x then Cvs.WeilForm.ReflectionEvenPositivityRH.cboxD h.1 h.2 else 0

/-- The centred box is reflection-even. -/
theorem cbox_mem_Ev (x : ℕ) (l : ℝ) : cbox x l ∈ Ev x := by
  unfold cbox
  split_ifs with h
  · exact Cvs.WeilForm.ReflectionEvenPositivityRH.cboxD_mem_Ev h.1 h.2
  · exact zero_mem _

/-- The centred box is a.e. `1_(0,l]` translated by `(log x − l)/2`. -/
theorem coe_cboxD_ae {l : ℝ} (hl : 0 < l) {x : ℕ} (hlx : l ≤ Real.log x) :
    (((Cvs.WeilForm.ReflectionEvenPositivityRH.cboxD hl hlx : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun s => Cvs.WeilForm.WindowSetNonempty.flat l (s - Cvs.WeilForm.NestedWindowsMonotoneBottom.shift l (Real.log x)) := by
  have h1 := Cvs.WeilForm.NestedWindowsMonotoneBottom.embed_ae hl.le hlx (Cvs.WeilForm.ReflectionEvenPositivityRH.boxD hl : Cvs.WeilForm.WeilFormOnWindowL2.window l)
  have h2 : Cvs.WeilForm.WindowRepresentative.rep (Cvs.WeilForm.ReflectionEvenPositivityRH.boxD hl : Cvs.WeilForm.WeilFormOnWindowL2.window l) =ᵐ[volume] Cvs.WeilForm.WindowSetNonempty.flat l :=
    (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.WeilForm.ReflectionEvenPositivityRH.coe_boxD_ae hl)
  have h3 := (measurePreserving_sub_right volume
    (Cvs.WeilForm.NestedWindowsMonotoneBottom.shift l (Real.log x))).quasiMeasurePreserving.ae_eq_comp h2
  exact h1.trans h3

/-- **Nested centred boxes**: `⟪1_l, 1_l'⟫ = l` for the centred boxes with `0 < l ≤ l' ≤ log x`. -/
theorem inner_cboxD {l l' : ℝ} (hl : 0 < l) (hl' : 0 < l') (hll : l ≤ l') {x : ℕ}
    (hlx : l ≤ Real.log x) (hl'x : l' ≤ Real.log x) :
    ⟪Cvs.WeilForm.ReflectionEvenPositivityRH.cboxD hl hlx, Cvs.WeilForm.ReflectionEvenPositivityRH.cboxD hl' hl'x⟫_ℝ = l := by
  rw [Cvs.WeilForm.TwoIndependentClasses.inner_coe]
  show ⟪(((Cvs.WeilForm.ReflectionEvenPositivityRH.cboxD hl hlx : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ)),
    (((Cvs.WeilForm.ReflectionEvenPositivityRH.cboxD hl' hl'x : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))⟫_ℝ = l
  rw [Cvs.L2a.PlaneCorrelationL2.inner_eq_integral]
  have hpt : ∀ s, Cvs.WeilForm.WindowSetNonempty.flat l (s - Cvs.WeilForm.NestedWindowsMonotoneBottom.shift l (Real.log x))
      * Cvs.WeilForm.WindowSetNonempty.flat l' (s - Cvs.WeilForm.NestedWindowsMonotoneBottom.shift l' (Real.log x)) = Cvs.WeilForm.WindowSetNonempty.flat l (s - Cvs.WeilForm.NestedWindowsMonotoneBottom.shift l (Real.log x)) := by
    intro s
    unfold Cvs.WeilForm.WindowSetNonempty.flat Cvs.WeilForm.NestedWindowsMonotoneBottom.shift
    by_cases hs : s - (Real.log x - l) / 2 ∈ Set.Ioc (0 : ℝ) l
    · have hs' : s - (Real.log x - l') / 2 ∈ Set.Ioc (0 : ℝ) l' :=
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs', mul_one]
    · rw [Set.indicator_of_notMem hs, zero_mul]
  have hae : (fun s => (((Cvs.WeilForm.ReflectionEvenPositivityRH.cboxD hl hlx : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) :
        Lp ℝ 2 (volume : Measure ℝ)) s * (((Cvs.WeilForm.ReflectionEvenPositivityRH.cboxD hl' hl'x : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) :
        Lp ℝ 2 (volume : Measure ℝ)) s) =ᵐ[volume] fun s => Cvs.WeilForm.WindowSetNonempty.flat l (s - Cvs.WeilForm.NestedWindowsMonotoneBottom.shift l (Real.log x)) := by
    filter_upwards [coe_cboxD_ae hl hlx, coe_cboxD_ae hl' hl'x] with s h1 h2
    rw [h1, h2, hpt]
  rw [integral_congr_ae hae, integral_sub_right_eq_self (fun s => Cvs.WeilForm.WindowSetNonempty.flat l s)]
  unfold Cvs.WeilForm.WindowSetNonempty.flat
  rw [integral_indicator_const _ measurableSet_Ioc]
  simp [hl.le]

/-- `⟪box_x(l), box_x(l')⟫ = l` for `0 ≤ l ≤ l' ≤ log x`. -/
theorem inner_cbox {x : ℕ} {l l' : ℝ} (hl : 0 ≤ l) (hll : l ≤ l') (hl'x : l' ≤ Real.log x) :
    ⟪cbox x l, cbox x l'⟫_ℝ = l := by
  rcases hl.eq_or_lt with rfl | hl
  · rw [cbox, dif_neg (fun h => lt_irrefl _ h.1), Cvs.WeilForm.TwoIndependentClasses.inner_coe, Submodule.coe_zero,
      Submodule.coe_zero, inner_zero_left]
  · have hl' := hl.trans_le hll
    rw [cbox, cbox, dif_pos ⟨hl, hll.trans hl'x⟩, dif_pos ⟨hl', hl'x⟩]
    exact inner_cboxD hl hl' hll _ hl'x

/-- **The even bulk is nonzero** at `x ≥ 2`: some reflection-even `w ≠ 0` is `L²`-orthogonal to `R₁`. -/
theorem exists_evenBulk_ne_zero {x : ℕ} (hx : 2 ≤ x) : ∃ w ∈ Ev x, w ∈ (R1 x)ᗮ ∧ w ≠ 0 :=
  exists_mem_orthogonal_ne_zero_of_minCov (Real.log_pos (by exact_mod_cast hx))
    (fun _ _ ha hab hb => inner_cbox ha hab hb) (cbox_mem_Ev x) (R1 x)

/-! ### The even-sector hypotheses -/

/-- **The even bulk floor at `x`**: `b‖w‖² ≤ Q(w)` for every even class `w` `L²`-orthogonal to `R₁`. -/
def EvenBulkFloor (x : ℕ) (b : ℝ) : Prop :=
  ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ → b * ‖w‖ ^ 2 ≤ Qx x w

/-- **The even form coupling at `x`**: `Q(r,w)² ≤ (1−δ)Q(r)Q(w)` for `r ∈ R₁` and every even class `w`
`L²`-orthogonal to `R₁`. -/
def EvenFormCoupling (x : ℕ) (δ : ℝ) : Prop :=
  ∀ r ∈ R1 x, ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) r w ^ 2 ≤ (1 - δ) * Qx x r * Qx x w

/-- **Even rung positivity at `x`**: `Q ≥ 0` on `R₁`. -/
def EvenRungPos (x : ℕ) : Prop :=
  ∀ r ∈ R1 x, 0 ≤ Qx x r

/-- `EvenBulkFloor x b` is `MergedBoundSchurForm`'s bulk floor of `QWbil` on the even classes against `R₁`. -/
theorem evenBulkFloor_iff (x : ℕ) (b : ℝ) :
    EvenBulkFloor x b ↔ Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (R1 x) b := by
  unfold EvenBulkFloor Cvs.Upstream.MergedBoundSchurForm.BulkFloor Bx
  simp only [Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]

/-- `EvenFormCoupling x δ` is `MergedBoundSchurForm`'s coupling of `QWbil` on the even classes against `R₁`. -/
theorem evenFormCoupling_iff (x : ℕ) (δ : ℝ) :
    EvenFormCoupling x δ ↔ Cvs.Upstream.MergedBoundSchurForm.Coupling (Bx x) (Ev x) (R1 x) δ := by
  unfold EvenFormCoupling Cvs.Upstream.MergedBoundSchurForm.Coupling Bx
  simp only [Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]

/-! ### Even rung positivity and the reflection bound -/

/-- **The reflection bound is an even share**: at `80 ≤ 2πx`, `ReflBound x k δ` iff
`((1−δ)/2)·Q(v_a) ≤ Q(e_a)` for every `a` vanishing on `j < k`, `e_a` the even part of `v_a`. -/
theorem reflBound_iff_share {x : ℕ} (hx : 80 ≤ 2 * π * x) (k : ℕ) (δ : ℝ) :
    ReflBound x k δ ↔ ∀ a : Cvs.Approximant.SpineSubspace.SF x → ℝ, (∀ j : Cvs.Approximant.SpineSubspace.SF x, (j : ℕ) < k → a j = 0) →
      (1 - δ) / 2 * Qx x (Cvs.Approximant.SpineSubspace.spineMap x a)
        ≤ Qx x (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)) := by
  refine forall_congr' fun a => imp_congr_right fun _ => ?_
  have h1 : Qx x (Cvs.Approximant.SpineSubspace.spineMap x a) = Cvs.L2a.EvenSectorReflectionBound.tailQ x a := Cvs.L2a.EvenSectorReflectionBound.Q_spineMap_eq_tailQ hx a
  have h2 : Qx x (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a))
      = (Cvs.L2a.EvenSectorReflectionBound.tailQ x a + Cvs.L2a.EvenSectorReflectionBound.reflQ x a) / 2 := Cvs.L2a.EvenSectorReflectionBound.Q_evenPart_eq hx a
  rw [h1, h2]
  constructor <;> intro h <;> linarith

/-- **Even rung positivity is the reflection bound at level `1` with `δ = 1`**, at `80 ≤ 2πx`. -/
theorem evenRungPos_iff_reflBound {x : ℕ} (hx : 80 ≤ 2 * π * x) : EvenRungPos x ↔ ReflBound x 1 1 := by
  rw [reflBound_iff_share hx]
  constructor
  · intro h a _
    simpa using h _ (evenPart_spineMap_mem_R1 x a)
  · intro h r hr
    obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
    simpa using h a (Cvs.L2a.EvenSectorReflectionBound.vanish_one x a)

/-- **The reflection bound with `δ ≤ 1` gives even rung positivity** past `c₀W ≤ 2πx`, through `EvenSectorReflectionBound`'s
`((1−δ)/2)·b_R(x)‖r‖² ≤ Q(r)` on `R₁`. -/
theorem evenRungPos_of_reflBound {x : ℕ} (hx : c0W ≤ 2 * π * x) {δ : ℝ} (hδ : δ ≤ 1)
    (hR : ReflBound x 1 δ) : EvenRungPos x := by
  intro r hr
  have h := Cvs.L2a.EvenSectorReflectionBound.L2a_even_R1 x hx hδ hR r hr
  have e : Cvs.L2a.EvenSectorReflectionBound.kappaE x δ * (1 - Cvs.Prolate.EvenRungsByIndex.lamR (2 * π * x) 2) = (1 - δ) / 2 * Cvs.L2a.EvenSectorReflectionBound.bR x := by
    unfold Cvs.L2a.EvenSectorReflectionBound.kappaE Cvs.L2a.EvenSectorReflectionBound.bR; ring
  rw [e] at h
  have h0 : 0 ≤ (1 - δ) / 2 * Cvs.L2a.EvenSectorReflectionBound.bR x * ‖r‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (Cvs.L2a.EvenSectorReflectionBound.bR_pos x hx).le) (sq_nonneg _)
  exact h0.trans h

/-! ### Positivity on a subspace from a bulk floor and a coupling -/

/-- **Positivity on `H`**: for `R ≤ H` with `Q ≥ 0` on `R`, `MergedBoundSchurForm`'s bulk floor `b ≥ 0` and coupling
`δ ≥ 0` of `QWbil` on `H` against `R` give `Q ≥ 0` on `H`. -/
theorem Q_nonneg_of_floor_coupling_sub {x : ℕ} {H R : Submodule ℝ (Dom x)} [R.HasOrthogonalProjection]
    (hRH : R ≤ H) (hR : ∀ r ∈ R, 0 ≤ Qx x r) {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hF : Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) H R b) (hC : Cvs.Upstream.MergedBoundSchurForm.Coupling (Bx x) H R δ) :
    ∀ φ ∈ H, 0 ≤ Qx x φ := by
  intro φ hφ
  obtain ⟨r, hr, w, hwH, hw, rfl, -⟩ := Cvs.Upstream.MergedLowerBoundPositivity.exists_split hRH hφ
  have hB : (Bx x).IsSymm := Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _
  have hQr : 0 ≤ Bx x r r := by rw [Bx, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]; exact hR r hr
  have hQw : 0 ≤ Bx x w w := (mul_nonneg hb (sq_nonneg _)).trans (hF w hwH hw)
  have h := (mul_nonneg (Cvs.Upstream.FormPositivitySumCoupling.one_sub_sqrt_nonneg hδ) (add_nonneg hQr hQw)).trans
    (Cvs.Upstream.FormPositivitySumCoupling.margin_le_apply_add hB hQr hQw (hC r hr w hwH hw))
  rwa [Bx, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self] at h

/-! ### The even sector against `R₁` -/

/-- **Even window positivity at `x`**: even rung positivity, `EvenBulkFloor x b` and `EvenFormCoupling x δ`
with `b, δ ≥ 0` give `Q ≥ 0` on the even classes. -/
theorem Q_nonneg_of_even_floor_coupling {x : ℕ} (hR : EvenRungPos x) {b δ : ℝ} (hb : 0 ≤ b)
    (hδ : 0 ≤ δ) (hF : EvenBulkFloor x b) (hC : EvenFormCoupling x δ) : ∀ φ ∈ Ev x, 0 ≤ Qx x φ :=
  Q_nonneg_of_floor_coupling_sub (R1_le_Ev x) hR hb hδ ((evenBulkFloor_iff x b).1 hF)
    ((evenFormCoupling_iff x δ).1 hC)

/-- **RH gives even rung positivity, the zero-margin even bulk floor and even form coupling** at every
`x ≥ 2`. -/
theorem even_floor_coupling_zero_of_rh (hRH : RiemannHypothesis) {x : ℕ} (hx : 2 ≤ x) :
    EvenRungPos x ∧ EvenBulkFloor x 0 ∧ EvenFormCoupling x 0 := by
  have hnn := Cvs.Route.CoreSchurForm.nonneg_of_rh hRH x hx
  refine ⟨fun r _ => hnn r, fun w _ _ => by simpa using hnn w,
    (evenFormCoupling_iff x 0).2 fun r hr w _ hw => ?_⟩
  exact Cvs.Route.CouplingBoundGivesCore.coupling_zero_of_nonneg (B := Bx x) (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) (fun f => by
    show 0 ≤ Bx x f f
    rw [Bx, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]; exact hnn f) r hr w Submodule.mem_top hw

/-! ### With the reflection bound in place of even rung positivity -/

/-! ### The even sector against `D₀`, with the even share -/

/-! ### One strict sign through the coupling -/

/-- **A positive even bulk floor has a positive bulk value** at `x ≥ 2`. -/
theorem exists_Q_pos_of_evenBulkFloor {x : ℕ} (hx : 2 ≤ x) {b : ℝ} (hb : 0 < b)
    (hF : EvenBulkFloor x b) : ∃ w₀ ∈ Ev x, w₀ ∈ (R1 x)ᗮ ∧ 0 < Qx x w₀ := by
  obtain ⟨w, hwe, hw, hw0⟩ := exists_evenBulk_ne_zero hx
  exact ⟨w, hwe, hw, (mul_pos hb (pow_pos (norm_pos_iff.2 hw0) 2)).trans_le (hF w hwe hw)⟩

/-- **The even coupling carries a positive bulk value to `R₁`**: `EvenFormCoupling x δ` with `δ < 1` and one
even `w₀ ⊥ R₁` with `Q(w₀) > 0` give even rung positivity. -/
theorem evenRungPos_of_coupling {x : ℕ} {δ : ℝ} (hδ : δ < 1) (hC : EvenFormCoupling x δ)
    (h0 : ∃ w₀ ∈ Ev x, w₀ ∈ (R1 x)ᗮ ∧ 0 < Qx x w₀) : EvenRungPos x := by
  obtain ⟨w₀, hwe, hw, hpos⟩ := h0
  exact fun r hr => nonneg_of_sq_le_mul hδ hpos (hC r hr w₀ hwe hw)

/-- **The even coupling carries a positive value on `R₁` to the bulk**: `EvenFormCoupling x δ` with `δ < 1`
and one `r₀ ∈ R₁` with `Q(r₀) > 0` give the even bulk floor `0`. -/
theorem evenBulkFloor_zero_of_coupling {x : ℕ} {δ : ℝ} (hδ : δ < 1) (hC : EvenFormCoupling x δ)
    (h0 : ∃ r₀ ∈ R1 x, 0 < Qx x r₀) : EvenBulkFloor x 0 := by
  obtain ⟨r₀, hr₀, hpos⟩ := h0
  intro w hwe hw
  rw [zero_mul]
  exact nonneg_of_sq_le_mul hδ hpos ((hC r₀ hr₀ w hwe hw).trans_eq (mul_right_comm _ _ _))

/-- **Even window positivity from a positive even bulk floor and the even form coupling** at `x ≥ 2`, with
`b > 0` and `0 ≤ δ < 1`. -/
theorem Q_nonneg_of_even_floor_pos_coupling {x : ℕ} (hx : 2 ≤ x) {b δ : ℝ} (hb : 0 < b) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hF : EvenBulkFloor x b) (hC : EvenFormCoupling x δ) : ∀ φ ∈ Ev x, 0 ≤ Qx x φ :=
  Q_nonneg_of_even_floor_coupling (evenRungPos_of_coupling hδ1 hC (exists_Q_pos_of_evenBulkFloor hx hb hF))
    hb.le hδ0 hF hC

/-- **RH from a positive even bulk floor and the even form coupling** at infinitely many `x`, with `b > 0`
and `0 ≤ δ < 1`. -/
theorem riemannHypothesis_of_even_floor_pos_coupling
    (h : ∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧ EvenBulkFloor x b ∧ EvenFormCoupling x δ) :
    RiemannHypothesis :=
  Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos ((h.and_eventually (eventually_ge_atTop 2)).mono
    fun _ ⟨⟨_, _, hb, hδ0, hδ1, hF, hC⟩, hx⟩ => Q_nonneg_of_even_floor_pos_coupling hx hb hδ0 hδ1 hF hC)

/-- **RH from a positive even bulk floor and the even coupling against `D₀`** at infinitely many `x`, with
`b > 0` and `0 ≤ δ < 1`. -/
theorem riemannHypothesis_of_floor_pos_coupling_D0
    (h : ∃ᶠ x : ℕ in atTop, ∃ b δ : ℝ, 0 < b ∧ 0 ≤ δ ∧ δ < 1 ∧
      Cvs.Upstream.MergedBoundSchurForm.BulkFloor (Bx x) (Ev x) (D0 x) b ∧ Cvs.Upstream.MergedBoundSchurForm.Coupling (Bx x) (Ev x) (D0 x) δ) :
    RiemannHypothesis := by
  refine Cvs.WeilForm.ReflectionEvenPositivityRH.rh_of_frequently_evenWindowPos
    ((h.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨⟨b, δ, hb, hδ0, hδ1, hF, hC⟩, hx⟩ => ?_)
  obtain ⟨w, hwe, hw, hw0⟩ := exists_evenBulk_ne_zero hx
  have hwD : w ∈ (D0 x)ᗮ := Submodule.orthogonal_le (Cvs.L2a.EvenSectorReflectionBound.D0_le_R1 x) hw
  have hpos : 0 < Bx x w w :=
    (mul_pos hb (pow_pos (norm_pos_iff.2 hw0) 2)).trans_le (hF w hwe hwD)
  have hD := nonneg_on_of_coupling hδ1 hC hwe hwD hpos
  exact Q_nonneg_of_floor_coupling_sub (D0_le_Ev x)
    (fun r hr => by have := hD r hr; rwa [Bx, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self] at this) hb.le hδ0 hF hC

end Cvs.Route.EvenWindowBulkCoupling
