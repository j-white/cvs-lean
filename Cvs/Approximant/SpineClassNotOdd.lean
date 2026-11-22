import Mathlib
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineFormOwnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.ReflectedSpineTame
import Cvs.L2a.SpineProfileWindowNormPos
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.CosineTransformAnalytic
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# No nonzero spine class is odd under the reflection

On `((x−1)/x, 1)` the reflected window `R_{1/x}k_G` is `√a·G`, `a = 1/x`, while `k_G` sums `x − 1` samples. If
`k_G + R_{1/x}k_G = 0` and `G` has a real-analytic extension `H` (Cvs.Prolate.CosineTransformAnalytic), the analytic
`(a/θ)Σ_{n≤x−2} H(na/θ) + √a·H(θ)` vanishes on the cell before, hence on `θ > 0`, and the last sample gives
`H = 0` on `((x−1)/x, 1)`. So `a ↦ e_a`, the even part of `spineMap x a`, is injective.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology

namespace Cvs.Approximant.SpineClassNotOdd
open Cvs.ZeroCounting

open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.Xi.PhysicalReciprocalReflection (reciprocal)

/-! ### From almost everywhere in `log θ` to everywhere on an interval -/

/-- **An a.e. identity in `s` is pointwise on an interval** where it is a continuous function of
`θ = e^{s − log r}`. -/
theorem eqOn_zero_of_ae {r : ℝ} {f g : ℝ → ℝ} (hf : ∀ᵐ s, f (exp (s - Real.log r)) = 0) {p q : ℝ}
    (hp : 0 ≤ p) (hfg : ∀ θ ∈ Ioo p q, f θ = g θ) (hg : ContinuousOn g (Ioo p q)) :
    ∀ θ ∈ Ioo p q, g θ = 0 := by
  set e : ℝ → ℝ := fun s => exp (s - Real.log r) with he_def
  have he : Continuous e := by fun_prop
  set U := e ⁻¹' Ioo p q with hU_def
  have hU : IsOpen U := isOpen_Ioo.preimage he
  have hae : (g ∘ e) =ᵐ[volume.restrict U] 0 := by
    rw [EventuallyEq, ae_restrict_iff' hU.measurableSet]
    filter_upwards [hf] with s hs hsU
    simp only [Function.comp_apply, Pi.zero_apply]
    rw [← hfg _ hsU]
    exact hs
  have hEq := Measure.eqOn_open_of_ae_eq hae hU (hg.comp he.continuousOn fun s hs => hs) continuousOn_const
  intro θ hθ
  have hθ0 : 0 < θ := lt_of_le_of_lt hp hθ.1
  have hs : e (Real.log θ + Real.log r) = θ := by
    simp only [he_def, add_sub_cancel_right, exp_log hθ0]
  have hmem : Real.log θ + Real.log r ∈ U := by
    simp only [hU_def, mem_preimage, hs]; exact hθ
  have := hEq hmem
  simpa only [Function.comp_apply, hs, Pi.zero_apply] using this

/-! ### The window on a cell and its reflection on `(1/2, 1)` -/

/-- **The window on the cell `θ/a ∈ [N, N+1)`**: `k_G(θ) = (a/θ)Σ_{n=1}^{N} G(na/θ)`. -/
theorem window_cell {A θ : ℝ} (hA : 0 < A) (hθ : θ ∈ Icc A 1) {N : ℕ} (h1 : (N : ℝ) ≤ θ / A)
    (h2 : θ / A < N + 1) (G : ℝ → ℝ) :
    window A G θ = A / θ * ∑ n ∈ Finset.Icc 1 N, G (n * A / θ) := by
  have hθ0 : 0 < θ := hA.trans_le hθ.1
  unfold window
  rw [indicator_of_mem hθ]
  unfold Cvs.Xi.EImageWindowPoisson.eimage
  rw [(Nat.floor_eq_iff (div_nonneg hθ0.le hA.le)).2 ⟨h1, h2⟩]

/-- **The reflected window on `(1/2, 1)`** is `√a·G(θ)`, for `0 < a ≤ 1/2`. -/
theorem reciprocal_window_of_half {A θ : ℝ} (hA : 0 < A) (hA2 : A ≤ 1 / 2) (hθ : θ ∈ Ioo (1 / 2 : ℝ) 1)
    (G : ℝ → ℝ) : reciprocal A (window A G) θ = √A * G θ := by
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hθI : θ ∈ Icc A 1 := ⟨by linarith [hθ.1], hθ.2.le⟩
  have hcell : A / θ ∈ Ico A (2 * A) := by
    refine ⟨(le_div_iff₀ hθ0).2 (by nlinarith [hθ.2]), (div_lt_iff₀ hθ0).2 (by nlinarith [hθ.1])⟩
  rw [Cvs.Xi.PhysicalReciprocalReflection.reciprocal_apply hA hθI, Cvs.L2a.SpineProfileWindowNormPos.window_first_cell hA hA2 hcell G,
    div_div_cancel₀ hA.ne']
  field_simp

/-! ### An odd window with an analytic profile vanishes near `1` -/

/-- `na/θ ∈ (0, 1)` when `0 < n < θ/a`. -/
theorem mem_Ioo_of_lt {A θ : ℝ} (hA : 0 < A) (hθ : 0 < θ) {n : ℝ} (hn0 : 0 < n) (hn : n < θ / A) :
    n * A / θ ∈ Ioo (0 : ℝ) 1 :=
  ⟨by positivity, (div_lt_one hθ).2 (by rwa [lt_div_iff₀ hA] at hn)⟩

/-- **An odd window with an analytic profile vanishes near `1`**: for `x ≥ 4`, `G = H` on `(0, 1)` with `H` real
analytic, and `k_G + R_{1/x}k_G = 0` almost everywhere in `log θ`, `H = 0` on `((x−1)/x, 1)`. -/
theorem eq_zero_of_odd_window {x : ℕ} (hx : 4 ≤ x) {G H : ℝ → ℝ} (hH : ∀ θ, AnalyticAt ℝ H θ)
    (hGH : ∀ u ∈ Ioo (0 : ℝ) 1, G u = H u)
    (hodd : ∀ᵐ s, window (1 / x) G (exp (s - Real.log x))
      + reciprocal (1 / x) (window (1 / x) G) (exp (s - Real.log x)) = 0) :
    ∀ u ∈ Ioo (((x : ℝ) - 1) / x) 1, H u = 0 := by
  set r : ℝ := (x : ℝ) with hr_def
  have hr4 : (4 : ℝ) ≤ r := by simp only [hr_def]; exact_mod_cast hx
  have hr0 : 0 < r := by linarith
  set A : ℝ := 1 / r with hA_def
  have hA : 0 < A := by positivity
  have hA2 : A ≤ 1 / 2 := by rw [hA_def, div_le_div_iff₀ hr0 (by norm_num)]; linarith
  have hdiv : ∀ θ, θ / A = θ * r := fun θ => by rw [hA_def]; field_simp
  have hN : (((x - 2 : ℕ)) : ℝ) = r - 2 := by rw [Nat.cast_sub (by omega), hr_def]; norm_num
  have hN1 : (((x - 2 : ℕ)) : ℝ) + 1 = r - 1 := by rw [hN]; ring
  -- the analytic comparison function
  set F : ℝ → ℝ := fun θ => A / θ * ∑ n ∈ Finset.Icc 1 (x - 2), H (n * A / θ) + √A * H θ with hF_def
  have hFa : ∀ θ ∈ Ioi (0 : ℝ), AnalyticAt ℝ F θ := by
    intro θ hθ
    have hθ0 : θ ≠ 0 := (mem_Ioi.1 hθ).ne'
    refine ((analyticAt_const.div analyticAt_id hθ0).mul (Finset.analyticAt_fun_sum _ fun n _ => ?_)).add
      (analyticAt_const.mul (hH θ))
    exact (hH _).comp (analyticAt_const.div analyticAt_id hθ0)
  -- the left cell
  have hp : (0 : ℝ) ≤ (r - 2) / r := div_nonneg (by linarith) hr0.le
  have hleft : ∀ θ ∈ Ioo ((r - 2) / r) ((r - 1) / r), F θ = 0 := by
    refine eqOn_zero_of_ae (f := fun θ => window A G θ + reciprocal A (window A G) θ) hodd hp (fun θ hθ => ?_) (fun θ hθ => ?_)
    · have hθ0 : 0 < θ := lt_of_le_of_lt hp hθ.1
      have h1 : r - 2 < θ * r := by have := hθ.1; rw [div_lt_iff₀ hr0] at this; linarith
      have h2 : θ * r < r - 1 := by have := hθ.2; rw [lt_div_iff₀ hr0] at this; linarith
      have hθ1 : θ < 1 := by nlinarith
      have hhalf : 1 / 2 < θ := by nlinarith
      have hθI : θ ∈ Icc A 1 := ⟨by linarith, hθ1.le⟩
      rw [window_cell hA hθI (N := x - 2) (by rw [hdiv, hN]; linarith) (by rw [hdiv, hN1]; linarith),
        reciprocal_window_of_half hA hA2 ⟨hhalf, hθ1⟩, hF_def, hGH θ ⟨hθ0, hθ1⟩]
      congr 2
      refine Finset.sum_congr rfl fun n hn => hGH _ (mem_Ioo_of_lt hA hθ0 ?_ ?_)
      · have := (Finset.mem_Icc.1 hn).1; exact_mod_cast this
      · have := (Finset.mem_Icc.1 hn).2
        have : (n : ℝ) ≤ r - 2 := by rw [← hN]; exact_mod_cast this
        rw [hdiv]; linarith
    · exact (hFa θ (lt_of_le_of_lt hp hθ.1)).continuousAt.continuousWithinAt
  -- `F` vanishes on `θ > 0`
  have hF0 : EqOn F 0 (Ioi 0) := by
    have hmid : (r - 3 / 2) / r ∈ Ioo ((r - 2) / r) ((r - 1) / r) :=
      ⟨div_lt_div_of_pos_right (by linarith) hr0, div_lt_div_of_pos_right (by linarith) hr0⟩
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hFa isPreconnected_Ioi
      (lt_of_le_of_lt hp hmid.1) ?_
    filter_upwards [Ioo_mem_nhds hmid.1 hmid.2] with θ hθ
    exact hleft θ hθ
  -- the last cell
  have hp' : (0 : ℝ) ≤ (r - 1) / r := div_nonneg (by linarith) hr0.le
  have hright : ∀ θ ∈ Ioo ((r - 1) / r) 1, A / θ * H ((((x - 2 : ℕ) + 1 : ℕ) : ℝ) * A / θ) = 0 := by
    refine eqOn_zero_of_ae (f := fun θ => window A G θ + reciprocal A (window A G) θ) hodd hp' (fun θ hθ => ?_) (fun θ hθ => ?_)
    · have hθ0 : 0 < θ := lt_of_le_of_lt hp' hθ.1
      have h1 : r - 1 < θ * r := by have := hθ.1; rw [div_lt_iff₀ hr0] at this; linarith
      have hθ1 := hθ.2
      have hhalf : 1 / 2 < θ := by nlinarith
      have hθI : θ ∈ Icc A 1 := ⟨by linarith, hθ1.le⟩
      have hx1 : x - 1 = (x - 2) + 1 := by omega
      rw [window_cell hA hθI (N := x - 1) (by rw [hdiv, hx1]; push_cast; rw [hN]; linarith)
          (by rw [hdiv, hx1]; push_cast; rw [hN]; nlinarith),
        reciprocal_window_of_half hA hA2 ⟨hhalf, hθ1⟩, hx1,
        Finset.sum_Icc_succ_top (by omega), hGH θ ⟨hθ0, hθ1⟩]
      have hF := hF0 (mem_Ioi.2 hθ0)
      simp only [hF_def, Pi.zero_apply] at hF
      have hlast : G ((((x - 2 : ℕ) + 1 : ℕ) : ℝ) * A / θ) = H ((((x - 2 : ℕ) + 1 : ℕ) : ℝ) * A / θ) := by
        refine hGH _ ⟨by positivity, (div_lt_one hθ0).2 ?_⟩
        push_cast; rw [hN]; rw [hA_def]
        rw [show (r - 2 + 1) * (1 / r) = (r - 1) / r by field_simp; ring]
        exact hθ.1
      have hsum : ∑ n ∈ Finset.Icc 1 (x - 2), G (n * A / θ) = ∑ n ∈ Finset.Icc 1 (x - 2), H (n * A / θ) := by
        refine Finset.sum_congr rfl fun n hn => hGH _ (mem_Ioo_of_lt hA hθ0 ?_ ?_)
        · have := (Finset.mem_Icc.1 hn).1; exact_mod_cast this
        · have := (Finset.mem_Icc.1 hn).2
          have : (n : ℝ) ≤ r - 2 := by rw [← hN]; exact_mod_cast this
          rw [hdiv]; linarith
      rw [hlast, hsum]
      linear_combination hF
    · exact ((analyticAt_const.div analyticAt_id (lt_of_le_of_lt hp' hθ.1).ne').mul
        ((hH _).comp (analyticAt_const.div analyticAt_id (lt_of_le_of_lt hp' hθ.1).ne'))).continuousAt.continuousWithinAt
  -- read off `H` on `((x−1)/x, 1)`
  intro u hu
  have hu0 : 0 < u := lt_of_le_of_lt hp' hu.1
  have h1 : r - 1 < u * r := by have := hu.1; rw [div_lt_iff₀ hr0] at this; linarith
  have hu1 := hu.2
  set θ : ℝ := (r - 1) * A / u with hθ_def
  have hθ0 : 0 < θ := by rw [hθ_def]; exact div_pos (mul_pos (by linarith) hA) hu0
  have hθmem : θ ∈ Ioo ((r - 1) / r) 1 := by
    rw [hθ_def, hA_def]
    constructor
    · have hq : 0 < (r - 1) / r := div_pos (by linarith) hr0
      rw [show (r - 1) * (1 / r) / u = ((r - 1) / r) / u by ring, lt_div_iff₀ hu0]; nlinarith
    · rw [div_lt_one hu0]; rw [show (r - 1) * (1 / r) = (r - 1) / r by ring, div_lt_iff₀ hr0]; linarith
  have h := hright θ hθmem
  have hcast : ((((x - 2 : ℕ) + 1 : ℕ)) : ℝ) = r - 1 := by push_cast; rw [hN]; ring
  rw [hcast, hθ_def, div_div_cancel₀ (mul_pos (by linarith) hA).ne'] at h
  exact (mul_eq_zero.1 h).resolve_left (div_pos hA hθ0).ne'

/-! ### The even part of a spine class -/

/-- **An odd spine class vanishes**: at `80 ≤ 2πx`, `e_a = 0` (the even part of `spineMap x a`) forces `a = 0`. -/
theorem eq_zero_of_evenPart_eq_zero {x : ℕ} (hx : 80 ≤ 2 * π * x) {a : Cvs.Approximant.SpineSubspace.SF x → ℝ}
    (h : Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a) = 0) : a = 0 := by
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hx4 : 4 ≤ x := by
    have : (10 : ℝ) < x := by nlinarith [Real.pi_lt_four]
    exact_mod_cast (show (4 : ℝ) ≤ x by linarith)
  have hc : 0 < 2 * π * (x : ℝ) := by positivity
  have hex : ∀ j ∈ Cvs.Approximant.SpineSubspace.SF x, ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * j) χ := fun j hj =>
    Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨j, Finset.mem_range.2 (Cvs.Approximant.SpineSubspace.SF_lt x j hj)⟩
  -- the class and its reflection add to zero
  have hsum : Cvs.Approximant.SpineSubspace.spineMap x a + Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a) = 0 := by
    have h2 := congrArg (fun v => (2 : ℝ) • v) h
    simp only [Cvs.WeilForm.EvenOddSplitForm.evenPart, smul_zero, smul_smul] at h2
    norm_num at h2
    exact h2
  rw [Cvs.L2a.ReflectedSpineTame.reflD_spineMap hx a, Cvs.Approximant.SpineFormOwnTailPairing.spineMap_eq_wv hx a] at hsum
  have hL := congrArg (fun v : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) =>
    ((v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))) hsum
  simp only [Submodule.coe_add, ZeroMemClass.coe_zero] at hL
  have hae : ∀ᵐ s, window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) (exp (s - Real.log x))
      + reciprocal (1 / x) (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (exp (s - Real.log x)) = 0 := by
    filter_upwards [Lp.coeFn_add (((Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.Approximant.SpineFormOwnTailPairing.tame_spineWindow hx a)) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) :
        Lp ℝ 2 volume) ((Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.L2a.ReflectedSpineTame.tame_reciprocal_spineWindow hx a) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) :
        Lp ℝ 2 volume),
      Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (Cvs.Approximant.SpineFormOwnTailPairing.tame_spineWindow hx a), Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (Cvs.L2a.ReflectedSpineTame.tame_reciprocal_spineWindow hx a),
      Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with s h1 h2 h3 h4
    rw [hL] at h1
    rw [h4, Pi.add_apply, h2, h3] at h1
    simp only [Cvs.Approximant.SpineCouplingTailPairing.fv, Cvs.L2a.TailLogScaleTest.logScale, Pi.zero_apply] at h1
    have he : exp ((s - Real.log x) / 2) ≠ 0 := (exp_pos _).ne'
    have h1' : (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a) (exp (s - Real.log x))
        + reciprocal (1 / x) (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)) (exp (s - Real.log x)))
          * exp ((s - Real.log x) / 2) = 0 := by rw [add_mul]; exact h1.symm
    exact (mul_eq_zero.1 h1').resolve_right he
  have hGH : ∀ u ∈ Ioo (0 : ℝ) 1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a u = Cvs.Prolate.CosineTransformAnalytic.spineExt (2 * π * x) a u := fun u hu =>
    Cvs.Prolate.CosineTransformAnalytic.spineG_eq_spineExt hc hex a u ⟨by linarith [hu.1], hu.2.le⟩
  have hz := eq_zero_of_odd_window hx4 (Cvs.Prolate.CosineTransformAnalytic.analyticAt_spineExt hex a) hGH hae
  by_contra hne
  have hx4r : (4 : ℝ) ≤ x := by exact_mod_cast hx4
  have hpos : (0 : ℝ) < ((x : ℝ) - 1) / x := div_pos (by linarith) hx0
  obtain ⟨u, hu, hne'⟩ := Cvs.L2a.SpineProfileWindowNormPos.exists_spineG_ne_zero (fun j hj => (Finset.mem_filter.1 hj).2) hex hne
    isOpen_Ioo (fun u hu => ⟨by linarith [hu.1], hu.2⟩)
    (nonempty_Ioo.2 ((div_lt_one hx0).2 (by linarith)))
  exact hne' ((hGH u ⟨hpos.trans hu.1, hu.2⟩).trans (hz u hu))

/-- **The even part of the spine is injective** at `80 ≤ 2πx`: `a ↦ e_a` has trivial kernel. -/
theorem evenSpine_injective {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Function.Injective ((Cvs.Approximant.D0FloorEvenRungShare.evenPartL (Real.log_natCast_nonneg x)).comp (Cvs.Approximant.SpineSubspace.spineMap x)) :=
  (injective_iff_map_eq_zero _).2 fun _ ha => eq_zero_of_evenPart_eq_zero hx ha

end Cvs.Approximant.SpineClassNotOdd
