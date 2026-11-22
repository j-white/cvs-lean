import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.BandInputsFromCutMultipliers
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFormDeepSpan
import Cvs.L2a.WindowFullSpanProlate
import Cvs.Prolate.CosineTransformEigenRelation
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.WeilForm.EImageRadical
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window norm of a nonzero spine profile is positive

On the first cell `[a, 2a)` the window is `(a/θ)G(a/θ)`, so `‖k_G‖² ≥ a∫_{(1/2,1]} G²`. Solutions of
`p y'' + q y' + r y + χ y = 0` at distinct `χ` summing to `0` on an open `U` vanish termwise there, and an angular
solution vanishing on an open `U ⊆ (−1, 1)` vanishes (Cvs.Prolate.CosineTransformEigenRelation), so a nonzero spine profile has `‖k_G‖² > 0` and `WindowFullSpanProlate`'s
bounds give `weilForm > 0` on both halves of the full span.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan

namespace Cvs.L2a.SpineProfileWindowNormPos

open Cvs.Xi.EImageWindowPoisson (window eimage window_of_notMem mem_Ioc_of_mem)
open Cvs.L2a.ProlateFamilySpine (kOf bOf sum_option_eq_spineG)
open Cvs.L2a.WindowChainInputsProlate (c0W)

/-! ### The first cell of the window -/

/-- **The window is bounded by `G`**: `|k_G| ≤ M` when `|G| ≤ M` on `(0, 1]` and `M ≥ 0`. -/
theorem abs_window_le {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u ∈ Ioc (0 : ℝ) 1, |G u| ≤ M) (θ : ℝ) : |window a G θ| ≤ M := by
  by_cases h : θ ∈ Icc a 1
  · have hθ0 : 0 < θ := ha.trans_le h.1
    unfold window eimage
    rw [indicator_of_mem h, abs_mul, abs_of_pos (div_pos ha hθ0)]
    have hsum : |∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ)| ≤ ⌊θ / a⌋₊ * M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun n hn => hM _ (mem_Ioc_of_mem ha hn).2).trans ?_
      simp
    have hfl : (⌊θ / a⌋₊ : ℝ) ≤ θ / a := Nat.floor_le (by positivity)
    calc a / θ * |∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ)| ≤ a / θ * (⌊θ / a⌋₊ * M) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ a / θ * (θ / a * M) := by gcongr
      _ = M := by field_simp
  · rw [window_of_notMem G h, abs_zero]
    exact hM0

/-- **`k_G²` is integrable** for `a > 0` and `G` continuous on `[0, 1]`. -/
theorem integrable_window_sq {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hGc : ContinuousOn G (Icc 0 1)) :
    Integrable (fun θ => window a G θ ^ 2) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hmeas : Measurable (window a G) :=
    (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc).indicator measurableSet_Icc
  refine Cvs.WeilForm.EImageRadical.integrable_of_bound_support (hmeas.pow_const 2) (K := M ^ 2) (p := a) (q := 1)
    (fun θ => ?_) (fun θ hθ => by rw [window_of_notMem G hθ]; norm_num)
  have hw := abs_window_le ha hM0 (fun u hu => by
    simpa [Real.norm_eq_abs] using hM u (Ioc_subset_Icc_self hu)) θ
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hw 2

/-- **On the first cell** `[a, 2a)`, `0 < a ≤ 1/2`, the window is the single term `(a/θ)G(a/θ)`. -/
theorem window_first_cell {a θ : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hθ : θ ∈ Ico a (2 * a)) (G : ℝ → ℝ) :
    window a G θ = a / θ * G (a / θ) := by
  have hθ1 : θ ∈ Icc a 1 := ⟨hθ.1, by linarith [hθ.2]⟩
  have hfl : ⌊θ / a⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (div_nonneg (ha.le.trans hθ.1) ha.le)]
    constructor
    · rw [Nat.cast_one, le_div_iff₀ ha]; linarith [hθ.1]
    · rw [div_lt_iff₀ ha]; push_cast; linarith [hθ.2]
  unfold window eimage
  rw [indicator_of_mem hθ1, hfl]
  simp

/-- **The first cell's energy**: `∫_{[a,2a)} (a/θ)²G(a/θ)² = a∫_{(1/2,1]} G²`, by `u = a/θ`. -/
theorem integral_first_cell {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) :
    ∫ θ in Ico a (2 * a), (a / θ) ^ 2 * G (a / θ) ^ 2 = a * ∫ u in Ioc (1 / 2 : ℝ) 1, G u ^ 2 := by
  have hderiv : ∀ θ ∈ Ico a (2 * a),
      HasDerivWithinAt (fun θ => a / θ) (-a / θ ^ 2) (Ico a (2 * a)) θ := by
    intro θ hθ
    have hθ0 : θ ≠ 0 := (ha.trans_le hθ.1).ne'
    have := (hasDerivAt_inv hθ0).const_mul a
    refine (this.congr_deriv (by field_simp)).hasDerivWithinAt.congr_of_mem (fun x _ => ?_) hθ
    simp [div_eq_mul_inv]
  have hinj : InjOn (fun θ => a / θ) (Ico a (2 * a)) := by
    intro x hx y hy hxy
    have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
    have hy0 : y ≠ 0 := (ha.trans_le hy.1).ne'
    simp only at hxy
    rw [div_eq_div_iff hx0 hy0] at hxy
    exact (mul_left_cancel₀ ha.ne' hxy).symm
  have himg : (fun θ => a / θ) '' Ico a (2 * a) = Ioc (1 / 2) 1 := by
    ext u
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      have hθ0 : 0 < θ := ha.trans_le hθ.1
      refine ⟨?_, ?_⟩
      · rw [lt_div_iff₀ hθ0]; linarith [hθ.2]
      · rw [div_le_one hθ0]; exact hθ.1
    · rintro ⟨hu1, hu2⟩
      have hu0 : 0 < u := by linarith
      refine ⟨a / u, ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff₀ hu0]; nlinarith
      · rw [div_lt_iff₀ hu0]; nlinarith
      · simp only; field_simp
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ico hderiv hinj (fun u => G u ^ 2),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ico fun θ hθ => ?_
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  simp only [smul_eq_mul]
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))]
  field_simp

/-- **The first-cell bound**: `a∫_{(1/2,1]} G² ≤ ∫ k_G²` for `0 < a ≤ 1/2` and `G` continuous on `[0, 1]`. -/
theorem first_cell_le {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {G : ℝ → ℝ} (hGc : ContinuousOn G (Icc 0 1)) :
    a * ∫ u in Ioc (1 / 2 : ℝ) 1, G u ^ 2 ≤ ∫ θ, window a G θ ^ 2 := by
  rw [← integral_first_cell ha G]
  have hcongr : ∫ θ in Ico a (2 * a), (a / θ) ^ 2 * G (a / θ) ^ 2 = ∫ θ in Ico a (2 * a), window a G θ ^ 2 :=
    setIntegral_congr_fun measurableSet_Ico fun θ hθ => by
      rw [window_first_cell ha ha2 hθ, mul_pow]
  rw [hcongr]
  exact setIntegral_le_integral (integrable_window_sq ha hGc) (ae_of_all _ fun _ => sq_nonneg _)

/-! ### Independence at distinct levels -/

/-- A function vanishing on an open set has derivative `0` there. -/
theorem deriv_eq_zero_of_eqOn_zero {U : Set ℝ} (hU : IsOpen U) {f f' : ℝ → ℝ}
    (hf : ∀ s ∈ U, HasDerivAt f (f' s) s) (h0 : ∀ s ∈ U, f s = 0) : ∀ s ∈ U, f' s = 0 := by
  intro s hs
  have hev : f =ᶠ[𝓝 s] fun _ => (0 : ℝ) := Filter.eventually_of_mem (hU.mem_nhds hs) h0
  exact (hf s hs).unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev)

/-- **Independence at distinct eigenvalues**: if `p hᵢ'' + q hᵢ' + r hᵢ + χᵢhᵢ = 0` on an open `U` with the `χᵢ`
distinct on `T`, and `Σ_{i∈T} bᵢhᵢ = 0` on `U`, then every `bᵢhᵢ = 0` on `U`. -/
theorem smul_eq_zero_of_sum_eq_zero {ι : Type*} [DecidableEq ι] {U : Set ℝ} (hU : IsOpen U)
    {p q r : ℝ → ℝ} {h h₁ h₂ : ι → ℝ → ℝ} {χ : ι → ℝ} (T : Finset ι) (hχ : InjOn χ T)
    (hh : ∀ i ∈ T, ∀ s ∈ U, HasDerivAt (h i) (h₁ i s) s)
    (hh₁ : ∀ i ∈ T, ∀ s ∈ U, HasDerivAt (h₁ i) (h₂ i s) s)
    (he : ∀ i ∈ T, ∀ s ∈ U, p s * h₂ i s + q s * h₁ i s + r s * h i s + χ i * h i s = 0)
    (b : ι → ℝ) (hz : ∀ s ∈ U, ∑ i ∈ T, b i * h i s = 0) :
    ∀ i ∈ T, ∀ s ∈ U, b i * h i s = 0 := by
  induction T using Finset.induction_on generalizing b with
  | empty => simp
  | insert m T hm ih =>
    -- the combination's derivatives vanish on `U`
    have hG₁ : ∀ s ∈ U, ∑ i ∈ insert m T, b i * h₁ i s = 0 :=
      deriv_eq_zero_of_eqOn_zero hU (fun s hs => HasDerivAt.fun_sum fun i hi => (hh i hi s hs).const_mul (b i)) hz
    have hG₂ : ∀ s ∈ U, ∑ i ∈ insert m T, b i * h₂ i s = 0 :=
      deriv_eq_zero_of_eqOn_zero hU (fun s hs => HasDerivAt.fun_sum fun i hi => (hh₁ i hi s hs).const_mul (b i)) hG₁
    -- so does the eigenvalue-weighted combination
    have hGχ : ∀ s ∈ U, ∑ i ∈ insert m T, b i * χ i * h i s = 0 := by
      intro s hs
      calc ∑ i ∈ insert m T, b i * χ i * h i s
          = ∑ i ∈ insert m T, -(p s * (b i * h₂ i s) + q s * (b i * h₁ i s) + r s * (b i * h i s)) :=
            Finset.sum_congr rfl fun i hi => by linear_combination (b i) * he i hi s hs
        _ = -(p s * ∑ i ∈ insert m T, b i * h₂ i s + q s * ∑ i ∈ insert m T, b i * h₁ i s
              + r s * ∑ i ∈ insert m T, b i * h i s) := by
            rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
              Finset.mul_sum, Finset.mul_sum]
        _ = 0 := by rw [hG₂ s hs, hG₁ s hs, hz s hs]; ring
    -- remove the `m` term with `χ − χ_m`
    have hz' : ∀ s ∈ U, ∑ i ∈ T, b i * (χ i - χ m) * h i s = 0 := by
      intro s hs
      have hsum : ∑ i ∈ insert m T, b i * (χ i - χ m) * h i s = 0 := by
        have : ∑ i ∈ insert m T, b i * (χ i - χ m) * h i s
            = ∑ i ∈ insert m T, b i * χ i * h i s - χ m * ∑ i ∈ insert m T, b i * h i s := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this, hGχ s hs, hz s hs]; ring
      rw [Finset.sum_insert hm, sub_self, mul_zero, zero_mul, zero_add] at hsum
      exact hsum
    have hT := ih (hχ.mono (by simp)) (fun i hi => hh i (Finset.mem_insert_of_mem hi))
      (fun i hi => hh₁ i (Finset.mem_insert_of_mem hi)) (fun i hi => he i (Finset.mem_insert_of_mem hi))
      (fun i => b i * (χ i - χ m)) hz'
    have hrest : ∀ i ∈ T, ∀ s ∈ U, b i * h i s = 0 := by
      intro i hi s hs
      have hne : χ i - χ m ≠ 0 := by
        refine sub_ne_zero.2 fun he' => ?_
        have : i = m := hχ (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self m T) he'
        exact hm (this ▸ hi)
      have := hT i hi s hs
      have : (χ i - χ m) * (b i * h i s) = 0 := by linear_combination this
      exact (mul_eq_zero.1 this).resolve_left hne
    intro i hi s hs
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · have h0 := hz s hs
      rw [Finset.sum_insert hm, Finset.sum_eq_zero fun j hj => hrest j hj s hs, add_zero] at h0
      exact h0
    · exact hrest i hi' s hs

/-- **An angular solution vanishing on a nonempty open subset of `(−1, 1)` vanishes on `[−1, 1]`.** -/
theorem eq_zero_of_eqOn_open {c χ : ℝ} {g g₁ g₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (he : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {U : Set ℝ} (hU : IsOpen U) (hUsub : U ⊆ Ioo (-1) 1) (hUne : U.Nonempty) (hz : ∀ s ∈ U, g s = 0) :
    ∀ s ∈ Icc (-1 : ℝ) 1, g s = 0 := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  rw [hI] at hg hg₁ he
  obtain ⟨s₀, hs₀⟩ := hUne
  have h10 := deriv_eq_zero_of_eqOn_zero hU (fun s hs => hg s (Ioo_subset_Icc_self (hUsub hs))) hz s₀ hs₀
  have hz' := Cvs.Prolate.CosineTransformEigenRelation.eq_zero_of_initial (fun s hs => hg s (Ioo_subset_Icc_self hs))
    (fun s hs => hg₁ s (Ioo_subset_Icc_self hs)) (fun s hs => he s (Ioo_subset_Icc_self hs)) (hUsub hs₀)
    (hz s₀ hs₀) h10
  have hcont : ContinuousOn g (Icc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have heq : EqOn g (fun _ => (0 : ℝ)) (Icc (-1) 1) :=
    EqOn.of_subset_closure hz' hcont continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo (by norm_num)])
  exact fun s hs => heq hs

/-- **A rung does not vanish on a nonempty open subset of `(−1, 1)`.** -/
theorem exists_rung_ne_zero_of_open {c : ℝ} {k : ℕ} (h : ∃ χ, IsLevelIdx c k χ) {U : Set ℝ} (hU : IsOpen U)
    (hUsub : U ⊆ Ioo (-1) 1) (hUne : U.Nonempty) : ∃ s ∈ U, rung c k s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hg, hg₁, -, hang, -, -⟩ := rung_spec h
  obtain ⟨s₀, hs₀, hne⟩ := rung_ne_zero h
  exact hne (eq_zero_of_eqOn_open hg hg₁ hang hU hUsub hUne hcon s₀ hs₀)

/-- **Rungs of distinct indices are independent on every nonempty open subset of `(−1, 1)`**:
`Σ_{i∈T} bᵢ h_{k(i)} = 0` there, with `k` injective on `T`, forces every `bᵢ = 0`. -/
theorem coeff_eq_zero_of_sum_rung {ι : Type*} [DecidableEq ι] {c : ℝ} (T : Finset ι) {k : ι → ℕ}
    (hk : InjOn k T) (hex : ∀ i ∈ T, ∃ χ, IsLevelIdx c (k i) χ) {U : Set ℝ} (hU : IsOpen U)
    (hUsub : U ⊆ Ioo (-1) 1) (hUne : U.Nonempty) (b : ι → ℝ)
    (hz : ∀ s ∈ U, ∑ i ∈ T, b i * rung c (k i) s = 0) : ∀ i ∈ T, b i = 0 := by
  have hIcc : ∀ s ∈ U, s ∈ uIcc (-1 : ℝ) 1 := fun s hs => by
    rw [uIcc_of_le (by norm_num)]; exact Ioo_subset_Icc_self (hUsub hs)
  have hχ : InjOn (fun i => lev c (k i)) T := by
    intro i hi i' hi' he
    apply hk hi hi'
    have h1 := (lev_spec (hex i hi)).2
    have h2 := (lev_spec (hex i' hi')).2
    simp only at he
    rw [he] at h1
    exact h1.symm.trans h2
  have hall := smul_eq_zero_of_sum_eq_zero hU (p := fun s => 1 - s ^ 2) (q := fun s => -(2 * s))
    (r := fun s => -(c ^ 2 * s ^ 2)) (h := fun i => rung c (k i)) (h₁ := fun i => rung₁ c (k i))
    (h₂ := fun i => rung₂ c (k i)) T hχ
    (fun i hi s hs => (rung_spec (hex i hi)).1 s (hIcc s hs))
    (fun i hi s hs => (rung_spec (hex i hi)).2.1 s (hIcc s hs))
    (fun i hi s hs => by
      linear_combination (rung_spec (hex i hi)).2.2.2.1 s (hIcc s hs)) b hz
  intro i hi
  obtain ⟨s, hsU, hs⟩ := exists_rung_ne_zero_of_open (hex i hi) hU hUsub hUne
  exact (mul_eq_zero.1 (hall i hi s hsU)).resolve_right hs

/-! ### The spine profile -/

/-- The spine profile is continuous on `[−1, 1]`. -/
theorem continuousOn_spineG (c : ℝ) {S : Finset ℕ} (a : S → ℝ) : ContinuousOn (spineG c a) (Icc (-1) 1) := by
  have hr : ∀ k, ContinuousOn (rung c k) (Icc (-1) 1) := fun k =>
    (continuousOn_rawRung c (lev c k)).div_const _
  show ContinuousOn (fun s => ∑ j, a j * (rung c (2 * (j : ℕ)) s - alpha c j * rung c 0 s)) _
  exact continuousOn_finsetSum _ fun j _ =>
    continuousOn_const.mul ((hr _).sub (continuousOn_const.mul (hr 0)))

/-- **A nonzero spine profile does not vanish on a nonempty open subset of `(−1, 1)`**, for `S ⊆ [1, ∞)` with the
levels of index `2j` present. -/
theorem exists_spineG_ne_zero {c : ℝ} {S : Finset ℕ} (hS : ∀ j ∈ S, 1 ≤ j)
    (hex : ∀ j ∈ S, ∃ χ, IsLevelIdx c (2 * j) χ) {a : S → ℝ} (ha : a ≠ 0) {U : Set ℝ} (hU : IsOpen U)
    (hUsub : U ⊆ Ioo (-1) 1) (hUne : U.Nonempty) : ∃ s ∈ U, spineG c a s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz : ∀ s ∈ U, ∑ i ∈ (Finset.univ : Finset (Option S)), bOf c a i * rung c (kOf i) s = 0 := by
    intro s hs
    have := congrFun (sum_option_eq_spineG c a) s
    rw [this]
    exact hcon s hs
  have hinj : InjOn (kOf (S := S)) (Finset.univ : Finset (Option S)) := by
    intro i _ i' _ he
    rcases i with _ | j <;> rcases i' with _ | j'
    · rfl
    · have := hS j' j'.2; simp only [kOf, Option.elim] at he; omega
    · have := hS j j.2; simp only [kOf, Option.elim] at he; omega
    · simp only [kOf, Option.elim] at he
      exact congrArg some (Subtype.ext (by omega))
  have hexi : ∀ i ∈ (Finset.univ : Finset (Option S)), ∃ χ, IsLevelIdx c (kOf i) χ := by
    rintro (_ | j) -
    · exact exists_isLevelIdx_zero c
    · exact hex j j.2
  have hb := coeff_eq_zero_of_sum_rung Finset.univ hinj hexi hU hUsub hUne (bOf c a) hz
  exact ha (funext fun j => hb (some j) (Finset.mem_univ _))

/-- **A nonzero spine profile has positive energy on `(1/2, 1]`.** -/
theorem integral_spineG_sq_pos {c : ℝ} {S : Finset ℕ} (hS : ∀ j ∈ S, 1 ≤ j)
    (hex : ∀ j ∈ S, ∃ χ, IsLevelIdx c (2 * j) χ) {a : S → ℝ} (ha : a ≠ 0) :
    0 < ∫ u in Ioc (1 / 2 : ℝ) 1, spineG c a u ^ 2 := by
  obtain ⟨s₀, hs₀, hne⟩ := exists_spineG_ne_zero hS hex ha isOpen_Ioo
    (Ioo_subset_Ioo (by norm_num) le_rfl) (nonempty_Ioo.2 (by norm_num : (1 / 2 : ℝ) < 1))
  have hc : ContinuousOn (fun u => spineG c a u ^ 2) (Icc (1 / 2 : ℝ) 1) :=
    ((continuousOn_spineG c a).mono (Icc_subset_Icc (by norm_num) le_rfl)).pow 2
  rw [← intervalIntegral.integral_of_le (by norm_num)]
  exact intervalIntegral.integral_pos (by norm_num) hc (fun u _ => sq_nonneg _)
    ⟨s₀, Ioo_subset_Icc_self hs₀, by positivity⟩

/-! ### The window norm on the full span -/

/-- **The window norm of a nonzero spine profile is positive** at `c = 2πx ≥ 80`, for `S ⊆ [1, x)`. -/
theorem window_norm_pos (x : ℕ) (hx : 80 ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, 1 ≤ j ∧ j < x)
    (a : S → ℝ) (ha : a ≠ 0) :
    0 < ∫ θ, window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2 := by
  have hx0' : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hx2 : (2 : ℝ) ≤ x := by nlinarith [Real.pi_lt_four]
  have hx0 : (0 : ℝ) < x := by linarith
  have hw : 2 * π / (2 * π * x) = 1 / x := by field_simp
  have hw0 : 0 < 2 * π / (2 * π * x) := by rw [hw]; positivity
  have hw2 : 2 * π / (2 * π * x) ≤ 1 / 2 := by
    rw [hw, div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have hex : ∀ j ∈ S, ∃ χ, IsLevelIdx (2 * π * x) (2 * j) χ := fun j hj =>
    Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨j, Finset.mem_range.2 (hS j hj).2⟩
  have hpos := integral_spineG_sq_pos (fun j hj => (hS j hj).1) hex ha
  have hGc : ContinuousOn (spineG (2 * π * x) a) (Icc 0 1) :=
    (continuousOn_spineG _ a).mono (Icc_subset_Icc (by norm_num) le_rfl)
  exact lt_of_lt_of_le (mul_pos hw0 hpos) (first_cell_le hw0 hw2 hGc)

/-- **`weilForm > 0` on the full span of the prolate family at `c = 2πx`**: every nonzero profile of the `D₀` and
`R_D` halves has positive Weil form, for every `x` with `c₀^W ≤ 2πx`. -/
theorem L2a_window_full_strict (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    (∀ a : ((Finset.range x).filter (2 ≤ ·)) → ℝ, a ≠ 0 →
      0 < Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
            (window (2 * π / (2 * π * x)) (spineG (2 * π * x) a)))) ∧
    (∀ a : ((Finset.range x).filter (1 ≤ ·)) → ℝ, a ≠ 0 →
      0 < Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
            (window (2 * π / (2 * π * x)) (spineG (2 * π * x) a)))) := by
  have h80 := (Cvs.L2a.BandInputsFromCutMultipliers.scale_ge (le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx)).2
  obtain ⟨hD, hR⟩ := Cvs.L2a.WindowFullSpanProlate.L2a_window_full_instance x hx
  obtain ⟨hfD, hfR⟩ := Cvs.L2a.WindowFullSpanProlate.full_factors_pos x hx
  refine ⟨fun a ha => lt_of_lt_of_le (mul_pos hfD (window_norm_pos x h80 (fun j hj => ?_) a ha)) (hD a),
    fun a ha => lt_of_lt_of_le (mul_pos hfR (window_norm_pos x h80 (fun j hj => ?_) a ha)) (hR a)⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hj
    exact ⟨by omega, Finset.mem_range.1 h1⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hj
    exact ⟨h2, Finset.mem_range.1 h1⟩

end Cvs.L2a.SpineProfileWindowNormPos
