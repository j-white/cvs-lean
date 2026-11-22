import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Finite.EvenCosineVectorEmbedding
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowedModeSumDomain
import Cvs.Finite.WindowedPartialSumsConverge
import Cvs.Route.EvenChannelSplitPrime
import Cvs.Route.EvenTameDenseCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.Upstream.MergedBoundSchurForm
import Cvs.WeilForm.CouplingFiniteSchur
import Cvs.WeilForm.CouplingFromTameDensity
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.TameClassesFormDense
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WeilFormSurvivesTruncation
import Cvs.WeilForm.WindowFormNormFloor
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Even mode sums are form-dense in the even window classes

Approximants of `w ∈ Rᗮ` from a `T` approximating the finite-dimensional `R` in norm move into `T ∩ Rᗮ`, so
`MergedBoundSchurForm`'s bulk floor and coupling against `R ≤ H` are those on any jointly dense `T ≤ H`. At `1 < x` cosine partial
sums of an even `C¹` window function converge to its class in norm and form, so the even mode sums are dense in
`Ev x` for the norm and the form jointly, also inside `Rᗮ` for every finite-dimensional `R ≤ Ev x`.
-/

noncomputable section

open MeasureTheory Real Filter Topology Set

namespace Cvs.Finite.EvenModeSumsFormDense
open Cvs.ZeroCounting

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Joint approximation is transitive**: if `S` approximates `w` and `T` approximates every point of `S` in norm
and form, for `B ≥ c‖·‖²`, then `T` approximates `w` in norm and form. -/
theorem exists_approx_trans {B : LinearMap.BilinForm ℝ E} {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) {S T : Set E} {w : E}
    (hS : ∃ s : ℕ → E, (∀ n, s n ∈ S) ∧ Tendsto (fun n => ‖s n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => B (s n - w) (s n - w)) atTop (𝓝 0))
    (hT : ∀ v ∈ S, ∃ t : ℕ → E, (∀ n, t n ∈ T) ∧ Tendsto (fun n => ‖t n - v‖) atTop (𝓝 0) ∧
      Tendsto (fun n => B (t n - v) (t n - v)) atTop (𝓝 0)) :
    ∃ t : ℕ → E, (∀ n, t n ∈ T) ∧ Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => B (t n - w) (t n - w)) atTop (𝓝 0) := by
  obtain ⟨s, hsS, hsn, hsB⟩ := hS
  set q : E → ℝ := fun u => B u u - c * ‖u‖ ^ 2 with hq
  have hq0 : ∀ u, 0 ≤ q u := fun u => by simp only [hq]; linarith [hc u]
  have hpar : ∀ a b, q (a + b) ≤ 2 * q a + 2 * q b := fun a b => by
    have h1 := hq0 (a - b)
    simp only [hq] at h1 ⊢
    have e : B (a + b) (a + b) + B (a - b) (a - b) = 2 * B a a + 2 * B b b := by
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]; ring
    have e2 : ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      have := parallelogram_law_with_norm ℝ a b
      rw [sq, sq, sq, sq]; linarith
    have e3 : c * ‖a + b‖ ^ 2 + c * ‖a - b‖ ^ 2 = 2 * (c * ‖a‖ ^ 2) + 2 * (c * ‖b‖ ^ 2) := by
      rw [← mul_add, e2]; ring
    linarith
  have hqs : Tendsto (fun n => q (s n - w)) atTop (𝓝 0) := by
    simpa [hq] using hsB.sub ((hsn.pow 2).const_mul c)
  have hev : ∀ n : ℕ, ∃ v ∈ T, ‖v - s n‖ < 1 / ((n : ℝ) + 1) ∧ q (v - s n) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨t, htT, htn, htB⟩ := hT (s n) (hsS n)
    have hqt : Tendsto (fun k => q (t k - s n)) atTop (𝓝 0) := by
      simpa [hq] using htB.sub ((htn.pow 2).const_mul c)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨k, hk1, hk2⟩ :=
      ((htn.eventually (gt_mem_nhds hpos)).and (hqt.eventually (gt_mem_nhds hpos))).exists
    exact ⟨t k, htT k, hk1, hk2⟩
  choose t htT ht1 ht2 using hev
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htn : Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hε.add hsn)
    exact (norm_sub_le_norm_sub_add_norm_sub (t n) (s n) w).trans
      (by linarith [ht1 n, one_div ((n : ℝ) + 1)])
  have htq : Tendsto (fun n => q (t n - w)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => hq0 _) (fun n => ?_)
      (by simpa using (hε.const_mul 2).add (hqs.const_mul 2))
    have e : t n - w = (t n - s n) + (s n - w) := by abel
    rw [e]
    exact (hpar _ _).trans (by linarith [ht2 n, one_div ((n : ℝ) + 1)])
  refine ⟨t, htT, htn, ?_⟩
  have := htq.add ((htn.pow 2).const_mul c)
  simpa [hq] using this

/-- **Approximants inside `T ∩ Rᗮ`**: for symmetric `B ≥ c‖·‖²`, finite-dimensional `R` and a submodule `T` that
approximates every `r ∈ R` in norm, approximants `t_n ∈ T` of `w ∈ Rᗮ` in norm and form give approximants in
`T ∩ Rᗮ` in norm and form. -/
theorem exists_perp_approx {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) {R T : Submodule ℝ E} [FiniteDimensional ℝ R]
    (hRT : ∀ r ∈ R, ∃ t : ℕ → E, (∀ n, t n ∈ T) ∧ Tendsto (fun n => ‖t n - r‖) atTop (𝓝 0))
    {w : E} (hw : w ∈ Rᗮ) {t : ℕ → E} (htT : ∀ n, t n ∈ T)
    (htn : Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0))
    (htB : Tendsto (fun n => B (t n - w) (t n - w)) atTop (𝓝 0)) :
    ∃ s : ℕ → E, (∀ n, s n ∈ T) ∧ (∀ n, s n ∈ Rᗮ) ∧ Tendsto (fun n => ‖s n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => B (s n - w) (s n - w)) atTop (𝓝 0) := by
  have : CompleteSpace R := FiniteDimensional.complete ℝ _
  let P : E →L[ℝ] R := R.orthogonalProjectionOnto
  let πT : T →ₗ[ℝ] R := P.toLinearMap ∘ₗ T.subtype
  have hsurj : LinearMap.range πT = ⊤ := by
    rw [eq_top_iff]
    rintro r -
    obtain ⟨u, huT, hun⟩ := hRT r r.2
    have hlim : Tendsto (fun n => πT ⟨u n, huT n⟩) atTop (𝓝 r) := by
      have h1 : Tendsto u atTop (𝓝 (r : E)) := (tendsto_iff_norm_sub_tendsto_zero).2 hun
      have h2 := (P.continuous.tendsto (r : E)).comp h1
      have hPr : P (r : E) = r := R.orthogonalProjectionOnto_mem_subspace_eq_self r
      rw [hPr] at h2
      exact h2
    exact (LinearMap.range πT).closed_of_finiteDimensional.mem_of_tendsto hlim
      (Eventually.of_forall fun n => LinearMap.mem_range_self πT _)
  obtain ⟨σ, hσ⟩ := πT.exists_rightInverse_of_surjective hsurj
  let φ : R →ₗ[ℝ] E := T.subtype ∘ₗ σ
  let p : ℕ → E := fun n => φ (P (t n))
  have hpT : ∀ n, p n ∈ T := fun n => (σ (P (t n))).2
  have hPp : ∀ n, P (p n) = P (t n) := fun n => LinearMap.congr_fun hσ (P (t n))
  have hPt : Tendsto (fun n => P (t n)) atTop (𝓝 0) := by
    have hPw : P w = 0 := (Submodule.orthogonalProjectionOnto_eq_zero_iff).2 hw
    have h1 : Tendsto t atTop (𝓝 w) := (tendsto_iff_norm_sub_tendsto_zero).2 htn
    have h2 := (P.continuous.tendsto w).comp h1
    rwa [hPw] at h2
  have hφc : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  have hp0 : Tendsto p atTop (𝓝 0) := by
    have := (hφc.tendsto 0).comp hPt
    simpa [p, Function.comp_def] using this
  have hpnorm : Tendsto (fun n => ‖p n‖) atTop (𝓝 0) := by
    simpa using hp0.norm
  have hpB : Tendsto (fun n => B (p n) (p n)) atTop (𝓝 0) := by
    have hcont : Continuous fun q : R => B (φ q) (φ q) := by
      let B' : R →ₗ[ℝ] R →ₗ[ℝ] ℝ := B.compl₁₂ φ φ
      let f : R →L[ℝ] R →L[ℝ] ℝ :=
        LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B')
      have h : (fun q : R => B (φ q) (φ q)) = fun q => f q q := rfl
      rw [h]
      exact f.continuous₂.comp (continuous_id.prodMk continuous_id)
    have := (hcont.tendsto 0).comp hPt
    simpa [p, Function.comp_def] using this
  have he : ∀ n, (t n - p n) - w = (t n - w) - p n := fun n => by abel
  have hen : Tendsto (fun n => ‖(t n - p n) - w‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => (he n).symm ▸ norm_sub_le _ _) ?_
    simpa using htn.add hpnorm
  have hdp : Tendsto (fun n => B (t n - w) (p n)) atTop (𝓝 0) := by
    have h := Cvs.WeilForm.CouplingFromTameDensity.tendsto_cross_zero hB hc hpnorm hpB htn htB
    exact h.congr fun n => hB.eq _ _
  have heB : Tendsto (fun n => B ((t n - p n) - w) ((t n - p n) - w)) atTop (𝓝 0) := by
    have hexp : ∀ n, B ((t n - p n) - w) ((t n - p n) - w)
        = B (t n - w) (t n - w) - 2 * B (t n - w) (p n) + B (p n) (p n) := fun n => by
      simp only [he n, map_sub, LinearMap.sub_apply]
      rw [hB.eq (p n) (t n), hB.eq (p n) w]
      ring
    simp_rw [hexp]
    simpa using (htB.sub (hdp.const_mul 2)).add hpB
  refine ⟨fun n => t n - p n, fun n => T.sub_mem (htT n) (hpT n), fun n => ?_, hen, heB⟩
  show t n - p n ∈ Rᗮ
  rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
  change P (t n - p n) = 0
  rw [map_sub, hPp n, sub_self]

/-- **The bulk floor transfers through a jointly dense submodule**: for symmetric `B ≥ c‖·‖²`, finite-dimensional
`R ≤ H` and `T ≤ H` approximating every point of `H` in norm and form, `BulkFloor B H R b ↔ BulkFloor B T R b`. -/
theorem bulkFloor_iff_of_dense {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) {H R T : Submodule ℝ E} [FiniteDimensional ℝ R]
    (hTH : T ≤ H) (hRH : R ≤ H)
    (hD : ∀ w ∈ H, ∃ t : ℕ → E, (∀ n, t n ∈ T) ∧ Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => B (t n - w) (t n - w)) atTop (𝓝 0)) (b : ℝ) :
    Cvs.Upstream.MergedBoundSchurForm.BulkFloor B H R b ↔ Cvs.Upstream.MergedBoundSchurForm.BulkFloor B T R b := by
  refine ⟨fun h w hw hwR => h w (hTH hw) hwR, fun h w hw hwR => ?_⟩
  obtain ⟨t, ht, htn, htB⟩ := hD w hw
  obtain ⟨s, hsT, hsR, hsn, hsB⟩ := exists_perp_approx hB hc (T := T)
    (fun r hr => by obtain ⟨u, hu, hun, -⟩ := hD r (hRH hr); exact ⟨u, hu, hun⟩) hwR ht htn htB
  obtain ⟨-, hss⟩ := Cvs.WeilForm.CouplingFromTameDensity.tendsto_apply_of_approx hB hc hsn hsB w
  have hns : Tendsto (fun n => ‖s n‖) atTop (𝓝 ‖w‖) := ((tendsto_iff_norm_sub_tendsto_zero).2 hsn).norm
  exact le_of_tendsto_of_tendsto' ((hns.pow 2).const_mul b) hss fun n => h _ (hsT n) (hsR n)

/-- **The coupling transfers through a jointly dense submodule**: for symmetric `B ≥ c‖·‖²`, finite-dimensional
`R ≤ H` and `T ≤ H` approximating every point of `H` in norm and form, `Coupling B H R δ ↔ Coupling B T R δ`. -/
theorem coupling_iff_of_dense {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {c : ℝ}
    (hc : ∀ u, c * ‖u‖ ^ 2 ≤ B u u) {H R T : Submodule ℝ E} [FiniteDimensional ℝ R]
    (hTH : T ≤ H) (hRH : R ≤ H)
    (hD : ∀ w ∈ H, ∃ t : ℕ → E, (∀ n, t n ∈ T) ∧ Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => B (t n - w) (t n - w)) atTop (𝓝 0)) (δ : ℝ) :
    Cvs.Upstream.MergedBoundSchurForm.Coupling B H R δ ↔ Cvs.Upstream.MergedBoundSchurForm.Coupling B T R δ := by
  refine ⟨fun h r hr w hw hwR => h r hr w (hTH hw) hwR, fun h r hr w hw hwR => ?_⟩
  obtain ⟨t, ht, htn, htB⟩ := hD w hw
  obtain ⟨s, hsT, hsR, hsn, hsB⟩ := exists_perp_approx hB hc (T := T)
    (fun r hr => by obtain ⟨u, hu, hun, -⟩ := hD r (hRH hr); exact ⟨u, hu, hun⟩) hwR ht htn htB
  obtain ⟨hrs, hss⟩ := Cvs.WeilForm.CouplingFromTameDensity.tendsto_apply_of_approx hB hc hsn hsB r
  exact le_of_tendsto_of_tendsto' (hrs.pow 2) (hss.const_mul ((1 - δ) * B r r))
    fun n => h r hr _ (hsT n) (hsR n)

end Generic

/-! ### Even mode sums at scale `x` -/

open Cvs.Finite.SymmetricModeSet (Idx negI)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)

/-- **Cosine partial sums converge in norm and form**: at `1 < x`, the order-`N` cosine sums of an even `C¹`
function `h` supported in `(0, log x]` converge to the class of `h` in norm and in the form. -/
theorem tendsto_modeMap_ofWin {x : ℕ} (hx1 : (1 : ℝ) < x) {h : ℝ → ℝ}
    (hh : ContDiff ℝ 1 h) (hhs : ∀ s ∉ Ioc (0 : ℝ) (Real.log x), h s = 0)
    (hsym : ∀ s, h (Real.log x - s) = h s) :
    Tendsto (fun N => ‖Cvs.Approximant.CosineColumnTailPairing.modeMap (zero_lt_one.trans hx1) N
        (Cvs.Finite.SymmetricModeSet.coeff N (Finset.range N) (Cvs.Finite.WindowCosineBessel.coef (Real.log x) h))
        - Cvs.Approximant.SpineCouplingTailPairing.wv (zero_lt_one.trans hx1) (Cvs.WeilForm.TameClassesFormDense.tame_ofWin (zero_lt_one.trans hx1) hh)‖) atTop (𝓝 0) ∧
    Tendsto (fun N =>
      Bx x (Cvs.Approximant.CosineColumnTailPairing.modeMap (zero_lt_one.trans hx1) N
          (Cvs.Finite.SymmetricModeSet.coeff N (Finset.range N) (Cvs.Finite.WindowCosineBessel.coef (Real.log x) h))
          - Cvs.Approximant.SpineCouplingTailPairing.wv (zero_lt_one.trans hx1) (Cvs.WeilForm.TameClassesFormDense.tame_ofWin (zero_lt_one.trans hx1) hh))
        (Cvs.Approximant.CosineColumnTailPairing.modeMap (zero_lt_one.trans hx1) N
          (Cvs.Finite.SymmetricModeSet.coeff N (Finset.range N) (Cvs.Finite.WindowCosineBessel.coef (Real.log x) h))
          - Cvs.Approximant.SpineCouplingTailPairing.wv (zero_lt_one.trans hx1) (Cvs.WeilForm.TameClassesFormDense.tame_ofWin (zero_lt_one.trans hx1) hh)))
      atTop (𝓝 0) := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx1
  set L := Real.log x with hLdef
  have hL : 0 < L := Real.log_pos hx1
  set a := Cvs.Finite.WindowCosineBessel.coef L h with ha
  set S : ℕ → Dom x := fun N => Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N (Cvs.Finite.SymmetricModeSet.coeff N (Finset.range N) a) with hS
  set g : Dom x := Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 hh) with hg
  have hSae : ∀ N, (((S N : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
      =ᵐ[volume] Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N) a := fun N => by
    have h1 := Cvs.Approximant.CosineColumnTailPairing.coe_modeClass_ae hx0 N (Cvs.Finite.SymmetricModeSet.coeff N (Finset.range N) a)
    rw [← Cvs.Finite.SymmetricModeSet.windowMode_eq_modeSum L N (Finset.range N) a
      (Finset.range_mono (Nat.le_succ N))] at h1
    exact h1
  have hgae : (((g : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) =ᵐ[volume] h :=
    (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 _).trans (Cvs.WeilForm.TameClassesFormDense.fv_ofWin_ae hx0 hhs)
  have hnorm_sq : ∀ N, ‖S N - g‖ ^ 2
      = ∫ t, (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N) a t - h t) ^ 2 := fun N => by
    have hae : ((((S N - g : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L)) : Lp ℝ 2 (volume : Measure ℝ))
        =ᵐ[volume] fun t => Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N) a t - h t := by
      have hc : ((((S N - g : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L)) : Lp ℝ 2 (volume : Measure ℝ))
          = (((S N : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
            - (((g : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)) := rfl
      rw [hc]
      filter_upwards [Lp.coeFn_sub (((S N : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ))
        (((g : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 (volume : Measure ℝ)), hSae N, hgae]
        with t h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    rw [show ‖S N - g‖ = ‖((S N - g : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window L)‖ from rfl, Cvs.WeilForm.TameClassesFormDense.norm_sq_eq _ hae]
  have hnorm : Tendsto (fun N => ‖S N - g‖) atTop (𝓝 0) := by
    have h2 : Tendsto (fun N => ‖S N - g‖ ^ 2) atTop (𝓝 0) := by
      simp_rw [hnorm_sq]
      exact Cvs.Finite.WindowedPartialSumsConverge.tendsto_integral_sub hL hh.continuous hhs hsym
    have := h2.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hQS : ∀ N, Cvs.Route.WindowPositivityBulkCoupling.Qx x (S N)
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N) a) :=
    fun N => Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (hSae N)
  have hQg : Cvs.Route.WindowPositivityBulkCoupling.Qx x g = Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) h := Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq hgae
  have hQ : Tendsto (fun N => Bx x (S N) (S N)) atTop (𝓝 (Bx x g g)) := by
    simp only [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]
    simp_rw [hQS, hQg]
    exact Cvs.WeilForm.WeilFormSurvivesTruncation.tendsto_weilForm_modeSum hL x (Nat.clog 2 x)
      (fun t => ((hh.differentiable one_ne_zero).differentiableAt).hasDerivAt)
      (hh.continuous_deriv le_rfl) hhs hsym
  have hSw : Tendsto S atTop (𝓝 g) := (tendsto_iff_norm_sub_tendsto_zero).2 hnorm
  have hlsc : ∀ (y : ℕ → Dom x) (y₀ : Dom x), Tendsto y atTop (𝓝 y₀) → ∀ ε > 0,
      ∀ᶠ n in atTop, Bx x y₀ y₀ - ε ≤ Bx x (y n) (y n) := fun y y₀ hy ε hε => by
    simp only [Cvs.WeilForm.CouplingFiniteSchur.Bx_self]
    exact Cvs.WeilForm.TameClassesFormDense.lsc_Qx y y₀ hy ε hε
  exact ⟨hnorm, Cvs.WeilForm.TameClassesFormDense.tendsto_sub_of_lsc (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm _ _ _) (Cvs.WeilForm.CouplingFromTameDensity.floor_Bx x) hlsc hSw hQ⟩

/-- The classes at `x` of the even `C¹` functions supported in `(0, log x]`. -/
def smoothEvenClasses {x : ℕ} (hx0 : (0 : ℝ) < x) : Set (Dom x) :=
  {v | ∃ (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h), (∀ s ∉ Ioc (0 : ℝ) (Real.log x), h s = 0) ∧
    (∀ s, h (Real.log x - s) = h s) ∧ Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 hh) = v}

/-- **Even `C¹` classes approximate every even class in norm and form.** -/
theorem smoothEven_approx {x : ℕ} (hx0 : (0 : ℝ) < x) {w : Dom x} (hw : w ∈ Ev x) :
    ∃ s : ℕ → Dom x, (∀ n, s n ∈ smoothEvenClasses hx0) ∧ Tendsto (fun n => ‖s n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => Bx x (s n - w) (s n - w)) atTop (𝓝 0) := by
  set hL := Real.log_natCast_nonneg x
  obtain ⟨g, hg, hgs, hn, hQ⟩ := Cvs.WeilForm.TameClassesFormDense.exists_ofWin_approx hx0 w
  have he : ∀ n, Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (Cvs.Route.EvenTameDenseCoupling.contDiff_evenSym (Real.log x) (hg n))) - w
      = Cvs.WeilForm.EvenOddSplitForm.evenPart hL (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (hg n)) - w) := fun n => by
    rw [← Cvs.Route.EvenTameDenseCoupling.evenPart_wv_ofWin hx0 (hg n) (hgs n)]
    have h := (Cvs.Approximant.D0FloorEvenRungShare.evenPartL hL).map_sub (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (hg n))) w
    have hw' : Cvs.Approximant.D0FloorEvenRungShare.evenPartL hL w = w := Cvs.Route.EvenChannelSplitPrime.evenPart_eq_self hL hw
    rw [hw'] at h
    exact h.symm
  obtain ⟨h1, h2⟩ := Cvs.Route.EvenTameDenseCoupling.tendsto_evenPart hn hQ
  refine ⟨fun n => Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.TameClassesFormDense.tame_ofWin hx0 (Cvs.Route.EvenTameDenseCoupling.contDiff_evenSym (Real.log x) (hg n))),
    fun n => ⟨_, Cvs.Route.EvenTameDenseCoupling.contDiff_evenSym _ (hg n), Cvs.Route.EvenTameDenseCoupling.evenSym_supp (hg n).continuous (hgs n),
      fun s => by simp only [Cvs.Route.EvenTameDenseCoupling.evenSym, sub_sub_cancel]; ring, rfl⟩, ?_, ?_⟩
  · simp_rw [he]; exact h1
  · simp_rw [he, Cvs.WeilForm.CouplingFiniteSchur.Bx_self]; exact h2

/-- The even mode sums at `x`: the classes `modeMap f` of reflection-even coefficient vectors `f`, a submodule. -/
def evenModes {x : ℕ} (hx0 : (0 : ℝ) < x) : Submodule ℝ (Dom x) where
  carrier := {v | ∃ (N : ℕ) (f : Idx N → ℝ), (∀ i, f (negI N i) = f i) ∧ Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f = v}
  zero_mem' := ⟨0, 0, fun _ => rfl, map_zero _⟩
  add_mem' {a b} ha hb := by
    obtain ⟨N, f, hf, rfl⟩ := ha
    obtain ⟨M, g, hg, rfl⟩ := hb
    refine ⟨max N M, Cvs.Finite.EvenCosineVectorEmbedding.embed N (max N M) f + Cvs.Finite.EvenCosineVectorEmbedding.embed M (max N M) g,
      fun i => by simp only [Pi.add_apply, Cvs.Finite.EvenCosineVectorEmbedding.embed_even], ?_⟩
    rw [map_add, Cvs.Finite.EvenCosineVectorEmbedding.modeMap_embed hx0 (le_max_left N M) f hf,
      Cvs.Finite.EvenCosineVectorEmbedding.modeMap_embed hx0 (le_max_right N M) g hg]
  smul_mem' c a ha := by
    obtain ⟨N, f, hf, rfl⟩ := ha
    exact ⟨N, c • f, fun i => by simp [hf i], map_smul _ c f⟩

/-- The even mode sums are reflection-even classes. -/
theorem evenModes_le_Ev {x : ℕ} (hx0 : (0 : ℝ) < x) : evenModes hx0 ≤ Ev x := by
  rintro _ ⟨N, f, -, rfl⟩
  exact Cvs.Approximant.CosineColumnTailPairing.reflD_modeMap hx0 N f

/-- **The even mode sums are dense in `Ev x` for the norm and the form jointly**, at `1 < x`. -/
theorem evenModeDense {x : ℕ} (hx1 : (1 : ℝ) < x) {w : Dom x} (hw : w ∈ Ev x) :
    ∃ t : ℕ → Dom x, (∀ n, t n ∈ evenModes (zero_lt_one.trans hx1)) ∧
      Tendsto (fun n => ‖t n - w‖) atTop (𝓝 0) ∧
      Tendsto (fun n => Bx x (t n - w) (t n - w)) atTop (𝓝 0) := by
  refine exists_approx_trans (Cvs.WeilForm.CouplingFromTameDensity.floor_Bx x) (smoothEven_approx (zero_lt_one.trans hx1) hw) ?_
  rintro _ ⟨h, hh, hhs, hsym, rfl⟩
  obtain ⟨hn, hQ⟩ := tendsto_modeMap_ofWin hx1 hh hhs hsym
  exact ⟨_, fun N => ⟨N, _, Cvs.Finite.SymmetricModeSet.coeff_even N _ _, rfl⟩, hn, hQ⟩

end Cvs.Finite.EvenModeSumsFormDense
