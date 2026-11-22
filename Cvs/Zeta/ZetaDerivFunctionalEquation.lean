import Mathlib
import Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolTwiceScore
import Cvs.Zeta.Digamma.ArchimedeanScoreChannel
import Cvs.Zeta.DigammaStrip
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrandDiff
import Cvs.Zeta.GammaRLogDeriv
import Cvs.Zeta.XiZetaBridge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The functional equation for `ζ'`, multiplied out

    ζ'(s) + 𝒜(s) ζ(s) = −(Γ_ℝ(1−s)/Γ_ℝ(s)) ζ'(1−s),   𝒜(s) = (Γ_ℝ'/Γ_ℝ)(s) + (Γ_ℝ'/Γ_ℝ)(1−s),

off the trivial zeros and their reflections; `𝒜 = −1/s + 𝒜₀` with `𝒜₀` holomorphic and
`O(log(2+|t|))` on vertical strips inside `−2 < Re s < 1`, and `𝒜(½+it)` is the archimedean symbol.
-/

namespace Cvs.Zeta.ZetaDerivFunctionalEquation

open Complex
open scoped Real

/-- The archimedean factor `𝒜(s) = (Γ_ℝ'/Γ_ℝ)(s) + (Γ_ℝ'/Γ_ℝ)(1−s)`. -/
noncomputable def archA (s : ℂ) : ℂ := logDeriv Gammaℝ s + logDeriv Gammaℝ (1 - s)

/-- The regular part `𝒜₀(s) = −log π + ψ(s/2+1)/2 + ψ((1−s)/2)/2` of `𝒜`. -/
noncomputable def archA₀ (s : ℂ) : ℂ :=
  -Complex.log π + digamma (s / 2 + 1) / 2 + digamma ((1 - s) / 2) / 2

/-- `Γ_ℝ` vanishes only at `0, −2, −4, …`. -/
theorem gammaR_ne_zero_of_forall {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n)) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  exact hs

/-- `Λ = Γ_ℝ · ζ` wherever `Γ_ℝ` does not vanish. -/
theorem completed_eq_gammaR_mul {z : ℂ} (hz : Gammaℝ z ≠ 0) :
    completedRiemannZeta z = Gammaℝ z * riemannZeta z := by
  have h0 : z ≠ 0 := by
    rintro rfl
    exact hz (Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩)
  rw [riemannZeta_def_of_ne_zero h0, mul_div_cancel₀ _ hz]

/-- **The functional equation in `Γ_ℝ` form**: `ζ(s) = Γ_ℝ(1−s)/Γ_ℝ(s) · ζ(1−s)`. -/
theorem zeta_eq_gammaR_ratio_mul {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n))
    (hs' : ∀ n : ℕ, 1 - s ≠ -(2 * n)) :
    riemannZeta s = Gammaℝ (1 - s) / Gammaℝ s * riemannZeta (1 - s) := by
  have hG := gammaR_ne_zero_of_forall hs
  have hG' := gammaR_ne_zero_of_forall hs'
  have h := completedRiemannZeta_one_sub s
  rw [completed_eq_gammaR_mul hG', completed_eq_gammaR_mul hG] at h
  field_simp
  linear_combination -h

/-- **`ζ' + 𝒜ζ = −(Γ_ℝ(1−s)/Γ_ℝ(s)) ζ'(1−s)`**, the derivative of the functional equation, with no
division by `ζ`. -/
theorem deriv_zeta_add_archA_mul {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n))
    (hs' : ∀ n : ℕ, 1 - s ≠ -(2 * n)) :
    deriv riemannZeta s + archA s * riemannZeta s
      = -(Gammaℝ (1 - s) / Gammaℝ s) * deriv riemannZeta (1 - s) := by
  have hG := gammaR_ne_zero_of_forall hs
  have hG' := gammaR_ne_zero_of_forall hs'
  have hs1 : s ≠ 1 := by
    intro h
    exact hs' 0 (by simp [h])
  have hs1' : 1 - s ≠ 1 := by
    intro h
    have : s = 0 := by linear_combination -h
    exact hs 0 (by simp [this])
  have hdG : DifferentiableAt ℂ Gammaℝ s := Cvs.Zeta.differentiableAt_gammaR hG
  have hdG' : DifferentiableAt ℂ Gammaℝ (1 - s) := Cvs.Zeta.differentiableAt_gammaR hG'
  have hdz : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hdz' : DifferentiableAt ℂ riemannZeta (1 - s) := differentiableAt_riemannZeta hs1'
  have hf : HasDerivAt (fun z => Gammaℝ z * riemannZeta z)
      (deriv Gammaℝ s * riemannZeta s + Gammaℝ s * deriv riemannZeta s) s :=
    hdG.hasDerivAt.mul hdz.hasDerivAt
  have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hg0 := (hdG'.hasDerivAt.mul hdz'.hasDerivAt).comp s hinner
  have hg : HasDerivAt (fun z => Gammaℝ (1 - z) * riemannZeta (1 - z))
      (-(deriv Gammaℝ (1 - s) * riemannZeta (1 - s)
        + Gammaℝ (1 - s) * deriv riemannZeta (1 - s))) s := by
    exact hg0.congr_deriv (by ring)
  have hc1 : ∀ᶠ z in nhds s, Gammaℝ z ≠ 0 := hdG.continuousAt.eventually_ne hG
  have hc2 : ∀ᶠ z in nhds s, Gammaℝ (1 - z) ≠ 0 :=
    (ContinuousAt.comp (f := fun z : ℂ => 1 - z) hdG'.continuousAt (by fun_prop)).eventually_ne hG'
  have heq : (fun z => Gammaℝ z * riemannZeta z)
      =ᶠ[nhds s] (fun z => Gammaℝ (1 - z) * riemannZeta (1 - z)) := by
    filter_upwards [hc1, hc2] with z h1 h2
    rw [← completed_eq_gammaR_mul h1, ← completed_eq_gammaR_mul h2, completedRiemannZeta_one_sub]
  have hval : Gammaℝ s * riemannZeta s = Gammaℝ (1 - s) * riemannZeta (1 - s) := heq.eq_of_nhds
  have hder := hf.unique (hg.congr_of_eventuallyEq heq)
  unfold archA
  rw [logDeriv_apply, logDeriv_apply]
  field_simp
  linear_combination Gammaℝ (1 - s) * hder + deriv Gammaℝ (1 - s) * hval

/-- **`ζ(s)·(−ζ'/ζ)(1−s) = ζ'(s) + 𝒜(s)ζ(s)`** wherever `ζ(1−s) ≠ 0`. -/
theorem zeta_mul_neg_logDeriv_one_sub_of_ne_zero {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n))
    (hs' : ∀ n : ℕ, 1 - s ≠ -(2 * n)) (hz : riemannZeta (1 - s) ≠ 0) :
    riemannZeta s * (-deriv riemannZeta (1 - s) / riemannZeta (1 - s))
      = deriv riemannZeta s + archA s * riemannZeta s := by
  rw [deriv_zeta_add_archA_mul hs hs', zeta_eq_gammaR_ratio_mul hs hs']
  field_simp

/-- **`ζ(s)·(−ζ'/ζ)(1−s) = ζ'(s) + 𝒜(s)ζ(s)` left of the critical strip**, off the trivial zeros. -/
theorem zeta_mul_neg_logDeriv_one_sub {s : ℂ} (hs : s.re < 0) (hs' : ∀ n : ℕ, s ≠ -(2 * n)) :
    riemannZeta s * (-deriv riemannZeta (1 - s) / riemannZeta (1 - s))
      = deriv riemannZeta s + archA s * riemannZeta s := by
  have hre : 1 < (1 - s).re := by simp; linarith
  refine zeta_mul_neg_logDeriv_one_sub_of_ne_zero hs' (fun n h => ?_)
    (riemannZeta_ne_zero_of_one_le_re hre.le)
  have := congrArg Complex.re h
  simp at this
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- **`𝒜(½+it)` is the archimedean symbol.** -/
theorem archA_cl (t : ℝ) : archA (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t) = (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t : ℂ) := by
  unfold archA
  rw [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.one_sub_cl, Cvs.Zeta.Explicit.Venue.logDeriv_GammaR_star, Complex.add_conj,
    Cvs.WeilForm.Archimedean.SymbolTwiceScore.archSymbol_eq_two_mul_logDeriv]
  have hcl : Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t = (1 / 2 : ℂ) + (t : ℂ) * I := by
    rw [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl, mul_comm]
  rw [hcl]

/-- **`𝒜 = −1/s + 𝒜₀`** off the trivial zeros and their reflections. -/
theorem archA_eq_of_forall {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n))
    (hs' : ∀ n : ℕ, 1 - s ≠ -(2 * n)) : archA s = -s⁻¹ + archA₀ s := by
  have hh : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    exact hs m (by linear_combination 2 * h)
  have hh' : ∀ m : ℕ, (1 - s) / 2 ≠ -m := by
    intro m h
    exact hs' m (by linear_combination 2 * h)
  unfold archA archA₀
  rw [Cvs.Zeta.logDeriv_gammaR hh, Cvs.Zeta.logDeriv_gammaR hh', digamma_apply_add_one _ hh]
  ring

/-- **`𝒜 = −1/s + 𝒜₀` on `−2 < Re s < 1`**, away from `s = 0`. -/
theorem archA_eq {s : ℂ} (h1 : -2 < s.re) (h2 : s.re < 1) (h0 : s ≠ 0) :
    archA s = -s⁻¹ + archA₀ s := by
  refine archA_eq_of_forall (fun n h => ?_) (fun n h => ?_)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact h0 (by simpa using h)
    · have := congrArg Complex.re h
      simp at this
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  · have := congrArg Complex.re h
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- `𝒜₀` is holomorphic on `−2 < Re s < 1`. -/
theorem differentiableOn_archA₀ : DifferentiableOn ℂ archA₀ {s | -2 < s.re ∧ s.re < 1} := by
  intro s hs
  obtain ⟨h1, h2⟩ := hs
  have ha : 0 < (s / 2 + 1).re := by simp; linarith
  have hb : 0 < ((1 - s) / 2).re := by simp; linarith
  have d1 : DifferentiableAt ℂ (fun z : ℂ => digamma (z / 2 + 1)) s :=
    (Cvs.Detection.differentiableAt_digamma ha).comp s (by fun_prop)
  have d2 : DifferentiableAt ℂ (fun z : ℂ => digamma ((1 - z) / 2)) s :=
    (Cvs.Detection.differentiableAt_digamma hb).comp s (by fun_prop)
  unfold archA₀
  exact (((differentiableAt_const _).add (d1.div_const 2)).add (d2.div_const 2)).differentiableWithinAt

/-- **`𝒜₀ = O(log(2+|t|))`** on any closed vertical strip inside `−2 < Re s < 1`. -/
theorem norm_archA₀_le_strip {a b : ℝ} (ha : -2 < a) (hb : b < 1) :
    ∃ C, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖archA₀ s‖ ≤ C * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Cvs.Zeta.exists_norm_digamma_le_strip (a / 2 + 1) (b / 2 + 1)
  obtain ⟨C₂, hC₂0, hC₂⟩ := Cvs.Zeta.exists_norm_digamma_le_strip ((1 - b) / 2) ((1 - a) / 2)
  have hK : IsCompact (Set.Icc a b ×ℂ Set.Icc (-2 : ℝ) 2) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn archA₀ (Set.Icc a b ×ℂ Set.Icc (-2 : ℝ) 2) := by
    refine differentiableOn_archA₀.continuousOn.mono fun z hz => ?_
    simp only [Complex.mem_reProdIm, Set.mem_Icc] at hz
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max M 0 + ‖Complex.log π‖ + C₁ / 2 + C₂ / 2, fun s h1 h2 => ?_⟩
  set L := 1 + Real.log (2 + |s.im|) with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Real.log (2 + |s.im|) := Real.log_nonneg (by linarith [abs_nonneg s.im])
    linarith
  rcases le_or_gt |s.im| 2 with him | him
  · have hmem : s ∈ Set.Icc a b ×ℂ Set.Icc (-2 : ℝ) 2 := by
      simp only [Complex.mem_reProdIm, Set.mem_Icc]
      exact ⟨⟨h1, h2⟩, abs_le.mp him⟩
    have hb' : ‖archA₀ s‖ ≤ max M 0 := (hM s hmem).trans (le_max_left _ _)
    have h0 : 0 ≤ ‖Complex.log π‖ + C₁ / 2 + C₂ / 2 := by positivity
    nlinarith [le_max_right M 0]
  · have hlogmono : Real.log (2 + |s.im| / 2) ≤ Real.log (2 + |s.im|) :=
      Real.log_le_log (by positivity) (by linarith [abs_nonneg s.im])
    have e1 := hC₁ (s / 2 + 1) (by simp; linarith) (by simp; linarith)
      (by simp [abs_div]; linarith)
    have e2 := hC₂ ((1 - s) / 2) (by simp; linarith) (by simp; linarith)
      (by simp [abs_div]; linarith)
    have him1 : (s / 2 + 1).im = s.im / 2 := by simp
    have him2 : |((1 - s) / 2).im| = |s.im| / 2 := by simp [abs_div]
    rw [him1, abs_div, abs_two] at e1
    rw [him2] at e2
    have e1' : ‖digamma (s / 2 + 1)‖ ≤ C₁ * L := e1.trans (by
      rw [hL]; exact mul_le_mul_of_nonneg_left (by linarith) hC₁0)
    have e2' : ‖digamma ((1 - s) / 2)‖ ≤ C₂ * L := e2.trans (by
      rw [hL]; exact mul_le_mul_of_nonneg_left (by linarith) hC₂0)
    have htri : ‖archA₀ s‖ ≤ ‖Complex.log π‖ + ‖digamma (s / 2 + 1)‖ / 2
        + ‖digamma ((1 - s) / 2)‖ / 2 := by
      unfold archA₀
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans ?_) ?_
      · rw [norm_neg, norm_div, Complex.norm_two]
      · rw [norm_div, Complex.norm_two]
    have hlogπ : ‖Complex.log π‖ ≤ ‖Complex.log π‖ * L := le_mul_of_one_le_right (norm_nonneg _) hL1
    nlinarith [le_max_right M 0]

/-- **`𝒜₀ = O(log(2+|t|))`** on `−½ ≤ Re s ≤ ½`, `|Im s| ≥ 2`. -/
theorem norm_archA₀_le : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 1 / 2 → 2 ≤ |s.im| →
    ‖archA₀ s‖ ≤ C * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨C, hC⟩ := norm_archA₀_le_strip (a := -1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨C, fun s h1 h2 _ => hC s h1 h2⟩

/-- **The archimedean symbol is `O(log(2+|t|))`.** -/
theorem abs_archSymbol_le : ∃ C, ∀ t : ℝ, |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t| ≤ C * (1 + Real.log (2 + |t|)) := by
  obtain ⟨C, hC⟩ := norm_archA₀_le_strip (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨2 + C, fun t => ?_⟩
  have hre : (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t).re = 1 / 2 := Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_re t
  have hA : archA (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t) = -(Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t)⁻¹ + archA₀ (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t) :=
    archA_eq (by rw [hre]; norm_num) (by rw [hre]; norm_num) (fun h => by
      have := congrArg Complex.re h; rw [hre] at this; simp at this)
  have hinv : ‖(Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have : (1 / 2 : ℝ) ≤ ‖Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t‖ := by
      have := Complex.abs_re_le_norm (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t)
      rw [hre] at this
      simpa using this
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have h0 := hC (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t) (by rw [hre]) (by rw [hre])
  rw [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_im] at h0
  have hL1 : 1 ≤ 1 + Real.log (2 + |t|) := by
    have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have key : |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t| = ‖archA (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t)‖ := by
    rw [archA_cl, Complex.norm_real, Real.norm_eq_abs]
  rw [key, hA]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  nlinarith

end Cvs.Zeta.ZetaDerivFunctionalEquation
