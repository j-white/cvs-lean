import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineFormOwnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MellinProfileStrips
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.EWindowReciprocalContraction
import Cvs.Xi.PhysicalReciprocalReflection

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The reflected spine window is tame, and the even rung form in tail form

The window reflection `s ↦ log x − s` is the reciprocal map `R_a v(θ) = (√a/θ)v(a/θ)`, `a = 1/x`, with Mellin
transform `a^{s−½}·Mv(1 − s)`; a window with decay on `−1 ≤ Re s ≤ 3/2` reflects to a tame test. `SpineCouplingTailPairing`'s coupling
then gives `Q(v_a, Rv_b) = −weilθ(τ_a, R_a W_b)` and, on even parts `e = (v + Rv)/2`,
`Q(e_a, e_b) = −(weilθ(τ_a, W_b) + weilθ(τ_a, R_a W_b))/2`, `τ_a` the regularised tail, `W_b` the spine window.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.L2a.ReflectedSpineTame
open Cvs.ZeroCounting

open Cvs.WeilForm.ThetaSpaceParseval (mellinR weilθ)
open Cvs.L2a.WindowFormTailLimit (Tame regProfile)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Xi.PhysicalReciprocalReflection (reciprocal)

/-! ### Mellin decay on a strip -/

/-- Mellin decay `‖Mv(s)‖ ≤ C/|Im s|` on the strip `σ₁ ≤ Re s ≤ σ₂`, `|Im s| ≥ 1`. -/
def StripDecay (v : ℝ → ℝ) (σ₁ σ₂ : ℝ) : Prop :=
  ∃ C, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|

/-- Strip decay from a piecewise-`C¹` representative almost everywhere, on any strip. -/
theorem stripDecay_of_pieces {ι : Type*} {v : ℝ → ℝ} (J : Finset ι) (p q : ι → ℝ) (w w₁ : ι → ℝ → ℝ)
    (hp : ∀ j ∈ J, 0 < p j) (hwc : ∀ j ∈ J, ContinuousOn (w j) (Icc (p j) (q j)))
    (hw : ∀ j ∈ J, ∀ θ ∈ Ioo (p j) (q j), HasDerivAt (w j) (w₁ j θ) θ)
    (hw₁ : ∀ j ∈ J, IntervalIntegrable (w₁ j) volume (p j) (q j))
    (hv : v =ᵐ[volume] fun θ => ∑ j ∈ J, (Ico (p j) (q j)).indicator (w j) θ) (σ₁ σ₂ : ℝ) :
    StripDecay v σ₁ σ₂ := by
  obtain ⟨C, hC⟩ := Cvs.WeilForm.MellinProfileStrips.norm_mellinR_le_of_pieces J p q w w₁ hp hwc hw hw₁ rfl σ₁ σ₂
  refine ⟨max C 0, fun s h1 h2 h3 => ?_⟩
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at h3
  have him : 0 < |s.im| := by linarith
  rw [Cvs.L2a.WindowFormTailLimit.mellinR_congr hv]
  calc ‖mellinR _ s‖ ≤ C / ‖s‖ := hC s h1 h2 hs0
    _ ≤ max C 0 / ‖s‖ := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 / |s.im| :=
        div_le_div_of_nonneg_left (le_max_right _ _) him (Complex.abs_im_le_norm s)

/-- **The window `k_G` has Mellin decay on every strip**, for `G ∈ C¹[0, 1]`. -/
theorem stripDecay_window {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1)) (σ₁ σ₂ : ℝ) :
    StripDecay (window a G) σ₁ σ₂ := by
  have hGc : ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt
  have hmaps : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, ∀ θ, (n : ℝ) * a ≤ θ → ∀ j ∈ Finset.Icc 1 n,
      (j : ℝ) * a / θ ∈ Icc (0 : ℝ) 1 := by
    intro n hn θ hθ j hj
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hθ0]
    exact (mul_le_mul_of_nonneg_right hjn ha.le).trans hθ
  have hpq : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, (n : ℝ) * a ≤ min ((n + 1) * a) 1 := by
    intro n hn
    refine le_min (by nlinarith) ?_
    have := (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
    rwa [le_div_iff₀ ha] at this
  have hpos : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, 0 < (n : ℝ) * a := fun n hn => by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    positivity
  have hcont : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, ∀ F : ℝ → ℝ, ContinuousOn F (Icc 0 1) →
      ContinuousOn (fun θ => ∑ j ∈ Finset.Icc 1 n, F (j * a / θ))
        (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) := by
    intro n hn F hF
    refine continuousOn_finsetSum _ fun j hj => hF.comp
      (continuousOn_const.div continuousOn_id fun θ hθ => (lt_of_lt_of_le (hpos n hn) hθ.1).ne')
      fun θ hθ => hmaps n hn θ hθ.1 j hj
  have hinv : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, ∀ b : ℝ,
      ContinuousOn (fun θ : ℝ => b / θ) (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) := fun n hn b =>
    continuousOn_const.div continuousOn_id fun θ hθ => (lt_of_lt_of_le (hpos n hn) hθ.1).ne'
  refine stripDecay_of_pieces (Finset.Icc 1 ⌊1 / a⌋₊) (fun n => n * a) (fun n => min ((n + 1) * a) 1)
    (fun n θ => a / θ * ∑ j ∈ Finset.Icc 1 n, G (j * a / θ))
    (fun n θ => a * -(θ ^ 2)⁻¹ * ∑ j ∈ Finset.Icc 1 n, G (j * a / θ)
      + a / θ * ∑ j ∈ Finset.Icc 1 n, G₁ (j * a / θ) * ((j : ℝ) * a * -(θ ^ 2)⁻¹))
    hpos (fun n hn => (hinv n hn a).mul (hcont n hn G hGc)) (fun n hn θ hθ => ?_) (fun n hn => ?_)
    (Cvs.L2a.WindowFormTailLimit.window_ae_eq_pieces ha G) σ₁ σ₂
  · have hθ0 : 0 < θ := (hpos n hn).trans hθ.1
    have hdiv : ∀ b : ℝ, HasDerivAt (fun y : ℝ => b / y) (b * -(θ ^ 2)⁻¹) θ := fun b => by
      simpa only [div_eq_mul_inv] using (hasDerivAt_inv hθ0.ne').const_mul b
    have hsum : HasDerivAt (fun y => ∑ j ∈ Finset.Icc 1 n, G (j * a / y))
        (∑ j ∈ Finset.Icc 1 n, G₁ (j * a / θ) * ((j : ℝ) * a * -(θ ^ 2)⁻¹)) θ :=
      HasDerivAt.fun_sum fun j hj => (hG _ (hmaps n hn θ hθ.1.le j hj)).comp θ (hdiv ((j : ℝ) * a))
    exact (hdiv a).mul hsum
  · refine ContinuousOn.intervalIntegrable_of_Icc (hpq n hn) ?_
    have hsq : ContinuousOn (fun θ : ℝ => -(θ ^ 2)⁻¹) (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) :=
      ((continuousOn_id.pow 2).fun_inv₀ fun (θ : ℝ) (hθ : θ ∈ Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) =>
        pow_ne_zero 2 (lt_of_lt_of_le (hpos n hn) hθ.1).ne').fun_neg
    refine ContinuousOn.fun_add (ContinuousOn.fun_mul (continuousOn_const.fun_mul hsq) (hcont n hn G hGc))
      (ContinuousOn.fun_mul (hinv n hn a) (continuousOn_finsetSum _ fun j hj => ?_))
    exact (hG₁.comp (hinv n hn ((j : ℝ) * a)) fun θ hθ => hmaps n hn θ hθ.1 j hj).fun_mul
      (continuousOn_const.fun_mul hsq)

/-! ### The reciprocal reflection and its Mellin transform -/

/-- On `θ > 0` the reciprocal reflection of a function supported in `[a, 1]` is `(√a/θ)F(a/θ)`. -/
theorem reciprocal_eq_of_pos {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (hF : ∀ θ ∉ Icc a 1, F θ = 0)
    {θ : ℝ} (hθ : 0 < θ) : reciprocal a F θ = √a / θ * F (a / θ) := by
  by_cases h : θ ∈ Icc a 1
  · exact Cvs.Xi.PhysicalReciprocalReflection.reciprocal_apply ha h F
  · rw [Cvs.Xi.PhysicalReciprocalReflection.reciprocal_of_notMem h F,
      hF _ fun hm => h ((Cvs.Xi.PhysicalReciprocalReflection.recip_mem_Icc_iff ha hθ).mp hm), mul_zero]

/-- **The Mellin transform of the reciprocal reflection**: `M(R_a F)(s) = a^{s−½}·MF(1 − s)` for `F`
supported in `[a, 1]`. -/
theorem mellinR_reciprocal {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (hF : ∀ θ ∉ Icc a 1, F θ = 0) (s : ℂ) :
    mellinR (reciprocal a F) s = (a : ℂ) ^ (s - 1 / 2) * mellinR F (1 - s) := by
  have h1 : mellinR (reciprocal a F) s = mellin (fun t : ℝ => ((√a : ℝ) : ℂ) •
      ((t : ℂ) ^ (-1 : ℂ) • (fun u : ℝ => (fun w : ℝ => (F w : ℂ)) (a * u)) t⁻¹)) s := by
    unfold mellinR mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [smul_eq_mul]
    rw [reciprocal_eq_of_pos ha hF ht, Complex.cpow_neg_one]
    push_cast
    rw [div_eq_mul_inv a t]
    ring
  rw [h1, mellin_const_smul, mellin_cpow_smul,
    mellin_comp_inv (fun u : ℝ => (fun w : ℝ => (F w : ℂ)) (a * u)),
    mellin_comp_mul_left (fun w : ℝ => (F w : ℂ)) _ ha]
  unfold mellinR
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc]
  have hs : ((√a : ℝ) : ℂ) = (a : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
  have e1 : -(s + -1) = 1 - s := by ring
  have e2 : ((1 / 2 : ℝ) : ℂ) + -(1 - s) = s - 1 / 2 := by push_cast; ring
  rw [e1, hs, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne'), e2]

/-- `a^t ≤ a^{−1} + a^{3/2}` for `a > 0` and `−1 ≤ t ≤ 3/2`. -/
theorem rpow_le_of_mem {a t : ℝ} (ha : 0 < a) (h1 : -1 ≤ t) (h2 : t ≤ 3 / 2) :
    a ^ t ≤ a ^ (-1 : ℝ) + a ^ (3 / 2 : ℝ) := by
  have p1 := Real.rpow_pos_of_pos ha (-1 : ℝ)
  have p2 := Real.rpow_pos_of_pos ha (3 / 2 : ℝ)
  rcases le_or_gt a 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge ha h h1
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h.le h2
    linarith

/-- **The reciprocal reflection of a tame test is tame** when its Mellin decay reaches the reflected strip
`−1 ≤ Re s ≤ 3/2`. -/
theorem tame_reciprocal {a : ℝ} {v : ℝ → ℝ} (hv : Tame v a 1) (hdec : StripDecay v (-1) (3 / 2)) :
    Tame (reciprocal a v) a 1 where
  pos := hv.pos
  supp θ hθ := Cvs.Xi.PhysicalReciprocalReflection.reciprocal_of_notMem hθ v
  meas := by
    unfold reciprocal Cvs.Xi.EWindowReciprocalContraction.branch
    refine (Measurable.indicator ?_ measurableSet_Icc).div_const _
    exact (measurable_const.div measurable_id).mul
      (hv.meas.comp (measurable_const.div measurable_id))
  bdd := by
    obtain ⟨M, hM⟩ := hv.bdd
    have ha := hv.pos
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have hsa : 0 < √a := Real.sqrt_pos.mpr ha
    refine ⟨M / √a, fun θ => ?_⟩
    by_cases hθ : θ ∈ Icc a 1
    · rw [Cvs.Xi.PhysicalReciprocalReflection.reciprocal_apply ha hθ, abs_mul]
      have hθ0 : 0 < θ := ha.trans_le hθ.1
      have hc : |√a / θ| ≤ 1 / √a := by
        rw [abs_of_pos (div_pos hsa hθ0), div_le_div_iff₀ hθ0 hsa]
        rw [one_mul, Real.mul_self_sqrt ha.le]
        exact hθ.1
      calc |√a / θ| * |v (a / θ)| ≤ 1 / √a * M :=
            mul_le_mul hc (hM _) (abs_nonneg _) (by positivity)
        _ = M / √a := by ring
    · rw [Cvs.Xi.PhysicalReciprocalReflection.reciprocal_of_notMem hθ, abs_zero]
      positivity
  dec := by
    obtain ⟨C, hC⟩ := hdec
    have ha := hv.pos
    set K := a ^ (-1 : ℝ) + a ^ (3 / 2 : ℝ) with hK
    have hK0 : 0 ≤ K := by positivity
    refine ⟨K * max C 0, fun s h1 h2 h3 => ?_⟩
    rw [mellinR_reciprocal ha hv.supp, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha]
    have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    have him : (1 - s).im = -s.im := by simp
    have hre' : (1 - s).re = 1 - s.re := by simp
    have hd := hC (1 - s) (by rw [hre']; linarith) (by rw [hre']; linarith)
      (by rw [him, abs_neg]; exact h3)
    rw [him, abs_neg] at hd
    have hpow : a ^ (s - 1 / 2).re ≤ K := by
      rw [hre]; exact rpow_le_of_mem ha (by linarith) (by linarith)
    have hims : 0 < |s.im| := by linarith
    have hmax : C / |s.im| ≤ max C 0 / |s.im| := by gcongr; exact le_max_left _ _
    calc a ^ (s - 1 / 2).re * ‖mellinR v (1 - s)‖ ≤ K * (max C 0 / |s.im|) :=
          mul_le_mul hpow (hd.trans hmax) (norm_nonneg _) hK0
      _ = K * max C 0 / |s.im| := by ring

/-- **The reflected window `R_a k_G` is tame on `[a, 1]`** for `G ∈ C¹[0, 1]` with `∫₀¹ G = 0`. -/
theorem tame_reciprocal_window {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) : Tame (reciprocal a (window a G)) a 1 :=
  tame_reciprocal (Cvs.L2a.WindowFormTailLimit.tame_window ha hG hG₁ hGi)
    (stripDecay_window ha hG hG₁ (-1) (3 / 2))

/-- **The reflected spine window is tame on `[1/x, 1]`**, at `80 ≤ 2πx`. -/
theorem tame_reciprocal_spineWindow {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Tame (reciprocal (1 / x) (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))) (1 / x) 1 := by
  obtain ⟨G₁, G₂, hg, hg₁, -, heven, hGi⟩ := Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.SpineSubspace.SF_lt x) a
  obtain ⟨h01, h01c, h01i⟩ := Cvs.L2a.WindowFormTailLimit.std_of_even hg hg₁ heven hGi
  exact tame_reciprocal_window (one_div_pos.mpr (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx)) h01 h01c h01i

/-! ### The form-domain reflection of a tame class -/

/-- The log-scaled reflected test is the reflected log-scaled test: `f_{R v}(s) = f_v(log x − s)`. -/
theorem fv_reciprocal {x : ℕ} (hx0 : (0 : ℝ) < x) {v : ℝ → ℝ} (hv : ∀ θ ∉ Icc (1 / (x : ℝ)) 1, v θ = 0)
    (s : ℝ) : Cvs.Approximant.SpineCouplingTailPairing.fv x (reciprocal (1 / x) v) s = Cvs.Approximant.SpineCouplingTailPairing.fv x v (Real.log x - s) := by
  unfold Cvs.Approximant.SpineCouplingTailPairing.fv
  rw [Cvs.Xi.PhysicalReciprocalReflection.logScale_reciprocal (one_div_pos.mpr hx0) v hv]
  congr 1
  rw [one_div, Real.log_inv]
  ring

/-- **The window reflection of the class of `v` is the class of `R_{1/x} v`.** -/
theorem reflD_wv {x : ℕ} (hx0 : (0 : ℝ) < x) {v : ℝ → ℝ} (hv : Tame v (1 / x) 1)
    (hv' : Tame (reciprocal (1 / x) v) (1 / x) 1) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv) = Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv' := by
  apply Subtype.ext; apply Subtype.ext; apply Lp.ext
  set k : Lp ℝ 2 volume := (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv).val.val with hk
  have hkv : (k : ℝ → ℝ) =ᵐ[volume] Cvs.Approximant.SpineCouplingTailPairing.fv x v := Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 hv
  have hr := (Measure.measurePreserving_sub_left volume (Real.log x)).quasiMeasurePreserving.ae_eq_comp hkv
  change ((Cvs.WeilForm.WindowReflectionSymmetry.refl (Real.log x) k : Lp ℝ 2 volume) : ℝ → ℝ) =ᵐ[volume] _
  filter_upwards [Cvs.WeilForm.WindowReflectionSymmetry.refl_ae (Real.log x) k, hr, Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 hv'] with s h1 h2 h3
  simp only [Function.comp_def] at h2
  rw [h1, h2, h3, fv_reciprocal hx0 hv.supp]

/-- The spine class reflected is the class of the reflected spine window. -/
theorem reflD_spineMap {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)
      = Cvs.Approximant.SpineCouplingTailPairing.wv (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (tame_reciprocal_spineWindow hx a) := by
  rw [Cvs.Approximant.SpineFormOwnTailPairing.spineMap_eq_wv hx a]
  exact reflD_wv _ _ _

/-! ### The even rung form in tail form -/

/-- **The spine pairing in tail form**: `Q(v_a, v_b) = −weilθ(τ_a, W_b)` at `80 ≤ 2πx`, `τ_a` the
regularised full tail of the spine profile of `a`, `W_b` the spine window of `b`. -/
theorem QWbil_spineMap_spineMap {x : ℕ} (hx : 80 ≤ 2 * π * x) (a b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a) (Cvs.Approximant.SpineSubspace.spineMap x b)
      = -weilθ (fullTail (psi (2 * π * x) (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))))
          (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)) := by
  rw [Cvs.Approximant.SpineFormOwnTailPairing.spineMap_eq_wv hx b]
  exact Cvs.Approximant.SpineCouplingTailPairing.QWbil_spineMap_eq_neg_tail hx a _

/-- **The reflection pairing in tail form**: `Q(v_a, Rv_b) = −weilθ(τ_a, R_{1/x}W_b)` at `80 ≤ 2πx`. -/
theorem QWbil_spineMap_reflD {x : ℕ} (hx : 80 ≤ 2 * π * x) (a b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineSubspace.spineMap x a)
        (Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x b))
      = -weilθ (fullTail (psi (2 * π * x) (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))))
          (reciprocal (1 / x) (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b))) := by
  rw [reflD_spineMap hx b]
  exact Cvs.Approximant.SpineCouplingTailPairing.QWbil_spineMap_eq_neg_tail hx a _

/-- The form on even parts is the average of the direct and reflected pairings,
`Q(e_u, e_w) = (Q(u, w) + Q(u, Rw))/2`, on any form domain. -/
theorem QWbil_evenPart {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (u w : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R (Cvs.WeilForm.EvenOddSplitForm.evenPart hL u) (Cvs.WeilForm.EvenOddSplitForm.evenPart hL w)
      = (Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R u w + Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R u (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL w)) / 2 := by
  set B := Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R with hB
  have hRR : B (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL u) (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL w) = B u w := Cvs.Approximant.CosineColumnTailPairing.QWbil_reflD hL P R u w
  have hRw : B (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL u) w = B u (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL w) := by
    conv_lhs => rw [← Cvs.WeilForm.WindowReflectionSymmetry.reflD_reflD hL w]
    exact Cvs.Approximant.CosineColumnTailPairing.QWbil_reflD hL P R u (Cvs.WeilForm.WindowReflectionSymmetry.reflD hL w)
  unfold Cvs.WeilForm.EvenOddSplitForm.evenPart
  simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  rw [hRR, hRw]
  ring

/-- **The even spine pairing in tail form**: for the even parts `e_a, e_b` of the spine classes,
`Q(e_a, e_b) = −(weilθ(τ_a, W_b) + weilθ(τ_a, R_{1/x}W_b))/2` at `80 ≤ 2πx`. -/
theorem QWbil_evenPart_spineMap {x : ℕ} (hx : 80 ≤ 2 * π * x) (a b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a))
        (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x b))
      = -(weilθ (fullTail (psi (2 * π * x) (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))))
            (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b))
          + weilθ (fullTail (psi (2 * π * x) (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))))
            (reciprocal (1 / x) (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) b)))) / 2 := by
  rw [QWbil_evenPart, QWbil_spineMap_spineMap hx, QWbil_spineMap_reflD hx]
  ring

/-- **The even spine form in tail form**: `Q(e_a) = −(weilθ(τ_a, W_a) + weilθ(τ_a, R_{1/x}W_a))/2`. -/
theorem Q_evenPart_spineMap {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a))
      = -(weilθ (fullTail (psi (2 * π * x) (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))))
            (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))
          + weilθ (fullTail (psi (2 * π * x) (regProfile (2 * π * x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))))
            (reciprocal (1 / x) (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)))) / 2 := by
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self]
  exact QWbil_evenPart_spineMap hx a a

end Cvs.L2a.ReflectedSpineTame
