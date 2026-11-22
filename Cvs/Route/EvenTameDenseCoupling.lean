import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.EvenChannelSplitPrime
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.LowEigenvalueCountSpine
import Cvs.Upstream.MergedBoundSchurForm
import Cvs.WeilForm.CouplingFiniteSchur
import Cvs.WeilForm.CouplingFromTameDensity
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TameClassesFormDense
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even tame classes are dense in the even sector, and the even coupling is its prime form

Along `CouplingFromTameDensity`'s approximants in `Rᗮ`, any `0 ≤ M ≤ B` on `H ∩ Rᗮ` converges on the diagonal, so a weighted channel
bound or a floor on a dense difference-closed `T ⊆ H` holds on `H`. `TameClassesFormDense`'s window approximants `g_n` of an even `w`
reflect-average to `(g_n + g_n(log x − ·))/2`, whose tame tests have even classes `e(t_n) → w`: at `80 ≤ 2πx`,
`EvenFormCoupling x δ ↔ EvenTameCoupling x δ`, and the even bulk floor is its restriction to even tame classes.
-/

noncomputable section

open MeasureTheory Real Filter Topology Set
open scoped InnerProductSpace

namespace Cvs.Route.EvenTameDenseCoupling
open Cvs.ZeroCounting

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A floor from a dense difference-closed set, relative to `H`**: with `T` as in `Cvs.WeilForm.CouplingFromTameDensity.coupling_of_dense`,
`b‖w‖² ≤ B(w, w)` on `T ∩ Rᗮ` holds on `H ∩ Rᗮ`. -/
theorem floor_of_dense {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) {H R : Submodule ℝ E} [FiniteDimensional ℝ R]
    [R.HasOrthogonalProjection] {T : Set E} (hT : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ T) (hRT : ∀ r ∈ R, r ∈ T)
    (hD : ∀ w ∈ H, ∃ t : ℕ → E, (∀ n, t n ∈ T) ∧ Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => B (t n - w) (t n - w)) atTop (𝓝 0)) {b : ℝ}
    (h : ∀ w ∈ T, w ∈ Rᗮ → b * ‖w‖ ^ 2 ≤ B w w) : ∀ w ∈ H, w ∈ Rᗮ → b * ‖w‖ ^ 2 ≤ B w w := by
  intro w hwH hw
  obtain ⟨t, htT, htn, htB⟩ := hD w hwH
  obtain ⟨s, hsT, hsR, hsn, hsB⟩ := Cvs.WeilForm.CouplingFromTameDensity.exists_orthogonal_approx hB hc hT hRT hw htT htn htB
  obtain ⟨-, hss⟩ := Cvs.WeilForm.CouplingFromTameDensity.tendsto_apply_of_approx hB hc hsn hsB w
  have hns : Tendsto (fun n => ‖s n‖) atTop (𝓝 ‖w‖) :=
    ((tendsto_iff_norm_sub_tendsto_zero).2 hsn).norm
  exact le_of_tendsto_of_tendsto' ((hns.pow 2).const_mul b) hss fun n => h (s n) (hsT n) (hsR n)

end Generic

/-! ### The even part along approximants -/

open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)

/-- **The even part preserves vanishing in norm and form**: `‖d_n‖ → 0` and `Q(d_n) → 0` give `‖e(d_n)‖ → 0` and
`Q(e(d_n)) → 0`. -/
theorem tendsto_evenPart {x : ℕ} {d : ℕ → Dom x} (hn : Tendsto (fun n => ‖d n‖) atTop (𝓝 0))
    (hQ : Tendsto (fun n => Qx x (d n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (d n)‖) atTop (𝓝 0) ∧
      Tendsto (fun n => Qx x (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (d n))) atTop (𝓝 0) := by
  set hL := Real.log_natCast_nonneg x
  constructor
  · refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hn
    have h := Cvs.WeilForm.EvenOddSplitForm.norm_sq_split hL (d n)
    have ho := sq_nonneg ‖Cvs.WeilForm.EvenOddSplitForm.oddPart hL (d n)‖
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      ((le_add_of_nonneg_right ho).trans_eq h.symm)
  · have hB : (Bx x).IsSymm := Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm hL x (Nat.clog 2 x)
    have hBd : Tendsto (fun n => Bx x (d n) (d n)) atTop (𝓝 0) := by
      simpa only [Cvs.WeilForm.CouplingFiniteSchur.Bx_self] using hQ
    have hRn : Tendsto (fun n => ‖Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (d n)‖) atTop (𝓝 0) := by
      simpa only [Cvs.WeilForm.WindowReflectionSymmetry.norm_reflD] using hn
    have hRB : Tendsto (fun n => Bx x (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (d n)) (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (d n))) atTop (𝓝 0) := by
      simpa only [Bx, Cvs.Approximant.CosineColumnTailPairing.QWbil_reflD] using hBd
    have hx := Cvs.WeilForm.CouplingFromTameDensity.tendsto_cross_zero hB (Cvs.WeilForm.CouplingFromTameDensity.floor_Bx x) hn hBd hRn hRB
    have e : ∀ n, Qx x (Cvs.WeilForm.EvenOddSplitForm.evenPart hL (d n)) = (Qx x (d n) + Bx x (d n) (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL (d n))) / 2 :=
      fun n => Cvs.Approximant.D0FloorEvenRungShare.Q_evenPart hL x (Nat.clog 2 x) (d n)
    simp_rw [e]
    simpa using (hQ.add hx).div_const 2

/-! ### Reflect-and-average -/

/-- The reflection average `s ↦ (g(s) + g(L − s))/2`. -/
def evenSym (L : ℝ) (g : ℝ → ℝ) (s : ℝ) : ℝ := (g s + g (L - s)) / 2

/-- The reflection average of a `C¹` function is `C¹`. -/
theorem contDiff_evenSym (L : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (evenSym L g) :=
  (hg.add (hg.comp (contDiff_const.sub contDiff_id))).div_const 2

/-- The reflection average of a continuous `g` vanishing off `(0, L]` vanishes off `(0, L]`. -/
theorem evenSym_supp {L : ℝ} {g : ℝ → ℝ} (hg : Continuous g) (hgs : ∀ s ∉ Ioc (0 : ℝ) L, g s = 0) :
    ∀ s ∉ Ioc (0 : ℝ) L, evenSym L g s = 0 := by
  have hcl : ∀ s, L ≤ s → g s = 0 := by
    have hsub : closure (Ioi L) ⊆ {s | g s = 0} :=
      (isClosed_eq hg continuous_const).closure_subset_iff.2 fun s hs => hgs s fun h => (not_le.2 hs) h.2
    intro s hs
    exact hsub (by rw [closure_Ioi]; exact hs)
  have hle : ∀ s ≤ 0, g s = 0 := fun s hs => hgs s fun h => (not_lt.2 hs) h.1
  intro s hs
  unfold evenSym
  rcases not_and_or.1 hs with h | h
  · rw [hle s (not_lt.1 h), hcl (L - s) (by linarith [not_lt.1 h])]; norm_num
  · rw [hcl s (not_le.1 h).le, hle (L - s) (by linarith [not_le.1 h])]; norm_num

/-- **The even part of a smooth window class is the class of its reflection average**:
`e(w_{ofWin g}) = w_{ofWin((g + g(log x − ·))/2)}` for `g ∈ C¹` vanishing off `(0, log x]`. -/
theorem evenPart_wv_ofWin {x : ℕ} (hx0 : (0 : ℝ) < x) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgs : ∀ s ∉ Ioc (0 : ℝ) (Real.log x), g s = 0) :
    Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 hg))
      = Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_evenSym (Real.log x) hg)) := by
  set φ := Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 hg) with hφdef
  set k : Lp ℝ 2 (volume : Measure ℝ) := φ.val.val with hk
  have hφ : (k : ℝ → ℝ) =ᵐ[volume] g := (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 _).trans (Cvs.WeilForm.TameClassesFormDense.fv_ofWin_ae hx0 hgs)
  have hr := (Measure.measurePreserving_sub_left volume (Real.log x)).quasiMeasurePreserving.ae_eq_comp hφ
  simp only [Function.comp_def] at hr
  have he := (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_evenSym (Real.log x) hg))).trans
    (Cvs.WeilForm.TameClassesFormDense.fv_ofWin_ae hx0 (evenSym_supp hg.continuous hgs))
  unfold Cvs.WeilForm.EvenOddSplitForm.evenPart
  apply Subtype.ext; apply Subtype.ext; apply Lp.ext
  change (((1 / 2 : ℝ) • (k + Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) k) : Lp ℝ 2 volume) : ℝ → ℝ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (k + Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) k),
    Lp.coeFn_add k (Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) k), Cvs.WeilForm.WindowReflectionSymmetry.refl_ae (Real.log x) k, hφ, hr, he]
    with s h1 h2 h3 h4 h5 h6
  rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, h5, h6, smul_eq_mul, evenSym]
  ring

/-! ### Density of the even tame classes -/

/-- **The even tame classes are dense in the even sector for the norm and the form jointly.** -/
theorem evenTameDense {x : ℕ} (hx0 : (0 : ℝ) < x) {w : Dom x} (hw : w ∈ Ev x) :
    ∃ (u : ℕ → ℝ → ℝ) (hu : ∀ n, Tame (u n) (1 / x) 1), (∀ n, Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (hu n) ∈ Ev x) ∧
      Tendsto (fun n => ‖Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (hu n) - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => Qx x (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (hu n) - w)) atTop (𝓝 0) := by
  set hL := Real.log_natCast_nonneg x
  obtain ⟨g, hg, hgs, hn, hQ⟩ := Cvs.WeilForm.TameClassesFormDense.exists_ofWin_approx hx0 w
  have he : ∀ n, Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_evenSym (Real.log x) (hg n))) - w
      = Cvs.WeilForm.EvenOddSplitForm.evenPart hL (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (hg n)) - w) := fun n => by
    rw [← evenPart_wv_ofWin hx0 (hg n) (hgs n)]
    have h := (Cvs.Approximant.D0FloorEvenRungShare.evenPartL hL).map_sub (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (hg n))) w
    have hw' : Cvs.Approximant.D0FloorEvenRungShare.evenPartL hL w = w := Cvs.Route.EvenChannelSplitPrime.evenPart_eq_self hL hw
    rw [hw'] at h
    exact h.symm
  obtain ⟨h1, h2⟩ := tendsto_evenPart hn hQ
  refine ⟨fun n => Cvs.WeilForm.TameClassesFormDense.ofWin x (evenSym (Real.log x) (g n)),
    fun n => Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_evenSym _ (hg n)), fun n => ?_, ?_, ?_⟩
  · show Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (contDiff_evenSym (Real.log x) (hg n))) ∈ Ev x
    rw [← evenPart_wv_ofWin hx0 (hg n) (hgs n)]
    exact Cvs.WeilForm.EvenOddSplitForm.reflD_evenPart hL _
  · simp_rw [he]; exact h1
  · simp_rw [he]; exact h2

/-! ### The even form coupling is the even tame coupling -/

/-- **`R₁` consists of even tame classes**, at `80 ≤ 2πx`. -/
theorem R1_subset_evenTame {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    ∀ r ∈ R1 x, r ∈ Cvs.WeilForm.CouplingFromTameDensity.tameSet (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) ∩ (Ev x : Set (Dom x)) := by
  intro r hr
  obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
  exact ⟨⟨_, Cvs.StepA.LowEigenvalueCountSpine.tame_evenWin hx a, (Cvs.StepA.LowEigenvalueCountSpine.evenPart_spineMap_eq_wv hx a).symm⟩, Cvs.Route.EvenWindowBulkCoupling.R1_le_Ev x hr⟩

/-- Differences of even tame classes are even tame classes. -/
theorem sub_mem_evenTame {x : ℕ} (hx0 : (0 : ℝ) < x) :
    ∀ a ∈ Cvs.WeilForm.CouplingFromTameDensity.tameSet hx0 ∩ (Ev x : Set (Dom x)), ∀ b ∈ Cvs.WeilForm.CouplingFromTameDensity.tameSet hx0 ∩ (Ev x : Set (Dom x)),
      a - b ∈ Cvs.WeilForm.CouplingFromTameDensity.tameSet hx0 ∩ (Ev x : Set (Dom x)) :=
  fun a ha b hb => ⟨Cvs.WeilForm.CouplingFromTameDensity.sub_mem_tameSet hx0 a ha.1 b hb.1, Submodule.sub_mem _ ha.2 hb.2⟩

/-- Every even class is a limit of even tame classes in norm and form, at `80 ≤ 2πx`. -/
theorem evenTame_approx {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    ∀ w ∈ Ev x, ∃ t : ℕ → Dom x, (∀ n, t n ∈ Cvs.WeilForm.CouplingFromTameDensity.tameSet (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) ∩ (Ev x : Set (Dom x))) ∧
      Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0) ∧ Tendsto (fun n => Bx x (t n - w) (t n - w)) atTop (𝓝 0) := by
  intro w hw
  obtain ⟨u, hu, he, hn, hQ⟩ := evenTameDense (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) hw
  exact ⟨fun n => Cvs.Approximant.SpineCouplingTailPairing.wv _ (hu n), fun n => ⟨⟨u n, hu n, rfl⟩, he n⟩, hn,
    by simpa only [Cvs.WeilForm.CouplingFiniteSchur.Bx_self] using hQ⟩

/-- **`EvenFormCoupling` from `EvenTameCoupling`**, at `80 ≤ 2πx`. -/
theorem evenFormCoupling_of_evenTameCoupling {x : ℕ} (hx : 80 ≤ 2 * π * x) {δ : ℝ}
    (h : Cvs.Route.EvenChannelSplitPrime.EvenTameCoupling x δ) : Cvs.Route.EvenWindowBulkCoupling.EvenFormCoupling x δ := by
  rw [Cvs.Route.EvenWindowBulkCoupling.evenFormCoupling_iff]
  refine Cvs.WeilForm.CouplingFromTameDensity.coupling_of_dense (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) (Cvs.WeilForm.CouplingFromTameDensity.floor_Bx x) (sub_mem_evenTame _)
    (R1_subset_evenTame hx) (evenTame_approx hx) ?_
  rintro r hr _ ⟨⟨u, hu, rfl⟩, he⟩ hw
  obtain ⟨a, rfl⟩ := Cvs.L2a.EvenSectorReflectionBound.exists_of_mem_R1 x hr
  rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self, Cvs.WeilForm.CouplingFiniteSchur.Bx_self]
  exact h a u _ hu he hw

/-- **The even bulk floor from the even tame classes**, at `80 ≤ 2πx`: `b‖w_u‖² ≤ Q(w_u)` for every `u` tame on
`[1/x, 1]` with `w_u` even and `L²`-orthogonal to `R₁` gives `EvenBulkFloor x b`. -/
theorem evenBulkFloor_of_tame {x : ℕ} (hx : 80 ≤ 2 * π * x) {b : ℝ}
    (h : ∀ (u : ℝ → ℝ) (hx0 : (0 : ℝ) < x) (hu : Tame u (1 / x) 1), Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ Ev x →
      Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu ∈ (R1 x)ᗮ → b * ‖Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu‖ ^ 2 ≤ Qx x (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b := by
  intro w hw hwR
  have hf := floor_of_dense (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) (Cvs.WeilForm.CouplingFromTameDensity.floor_Bx x) (H := Ev x) (R := R1 x)
    (sub_mem_evenTame _) (R1_subset_evenTame hx) (evenTame_approx hx) (b := b) ?_ w hw hwR
  · rwa [Cvs.WeilForm.CouplingFiniteSchur.Bx_self] at hf
  · rintro _ ⟨⟨u, hu, rfl⟩, he⟩ hwR'
    rw [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]
    exact h u _ hu he hwR'

end Cvs.Route.EvenTameDenseCoupling
