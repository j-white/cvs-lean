import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.MellinProfileStrips
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImagePoleFunctionals
import Cvs.Xi.EImageWindowPoisson
import Cvs.Zeta.VerticalLineShift
import Cvs.Zeta.XiVertical
import Cvs.Zeta.ZetaDerivFunctionalEquation
import Cvs.Zeta.ZetaDerivStripGrowth

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The radical lemma `weilθ(E_G, v) = 0`

Each channel of `weilθ(E, v)` is a line integral of `ζ₁H`: the left primes via `Re s = 2` and the pole
of `−ζ'` at `1`, the right primes via `Re s = −¼`, the functional equation, and the pole of `𝒜` at `0`.
On `Re s = ½` the integrands cancel because `ζ₁ = (s − 1)ζ`.
-/

namespace Cvs.WeilForm.EImageRadical

open Real Set Filter Topology MeasureTheory
open Complex (I)
open scoped ArithmeticFunction
open Cvs.Xi.EImageWindowPoisson (eimage eimage_of_lt)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR poleP poleM dil weilθ integral_mul_eq_mellin crossSpec_logScale)
open Cvs.WeilForm.MellinProfileStrips (gM Hfun differentiableOn_Hfun norm_Hfun_le Hfun_one Hfun_zero)
open Cvs.Xi.EImageMellin (mellinR_eimage mellinR_eimage_dil integrable_logScale_eimage)
open Cvs.Zeta.ZetaDerivFunctionalEquation (archA archA₀ archA_eq archA_cl differentiableOn_archA₀ zeta_mul_neg_logDeriv_one_sub)
open Cvs.Zeta.VerticalLineShift (integrable_of_decay integral_vline_eq integral_vline_sub_of_pole integral_LSeries_vonMangoldt_vline vline_re vline_im)
open Cvs.Xi.EImagePoleFunctionals (mellinR_zero mellinR_one poleM_eq_mellinR poleP_of_support poleM_eimage poleP_eimage riemannZeta₁_zero)
open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.FullTailPolarisation (crossSpec)
open Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv (cl)

/-! ### Lines, integrability and dilates -/

theorem cl_eq (t : ℝ) : cl t = ((1 / 2 : ℝ) : ℂ) + t * I := by
  simp only [cl]; push_cast; ring

theorem continuous_vline {f : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U) {σ : ℝ}
    (hU : ∀ y : ℝ, (σ : ℂ) + y * I ∈ U) : Continuous fun y : ℝ => f (σ + y * I) :=
  hf.continuousOn.comp_continuous (by fun_prop) hU

/-- A continuous function on `Re s = σ` decaying like `(1 + |Im s|)^{−κ}`, `κ > 1`, is integrable. -/
theorem integrable_vline {f : ℂ → ℂ} {σ T₀ B κ : ℝ} (hc : Continuous fun y : ℝ => f (σ + y * I))
    (hκ : 1 < κ) (hd : ∀ s : ℂ, s.re = σ → T₀ ≤ |s.im| → ‖f s‖ ≤ B * (1 + |s.im|) ^ (-κ)) :
    Integrable fun y : ℝ => f (σ + y * I) :=
  integrable_of_decay hc hκ fun y hy => by
    have := hd ((σ : ℂ) + y * I) (vline_re σ y) (by rw [vline_im]; exact hy)
    rwa [vline_im] at this

/-- A bounded measurable function vanishing off `[p, q]` is integrable. -/
theorem integrable_of_bound_support {f : ℝ → ℝ} (hf : Measurable f) {K p q : ℝ}
    (hK : ∀ x, |f x| ≤ K) (hs : ∀ x ∉ Icc p q, f x = 0) : Integrable f := by
  have hi : IntegrableOn f (Icc p q) :=
    Measure.integrableOn_of_bounded (M := K) measure_Icc_lt_top.ne hf.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hK x)
  refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).1 hi
  by_contra h
  exact hx (hs x h)

/-- `logScale F` is integrable and square-integrable for bounded measurable `F` vanishing off
`[α, β] ⊂ (0, ∞)`. -/
theorem integrable_logScale_of_support {F : ℝ → ℝ} (hFm : Measurable F) {M : ℝ}
    (hM : ∀ θ, |F θ| ≤ M) {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, F θ = 0) :
    Integrable (logScale F) ∧ MemLp (logScale F) 2 volume := by
  have hm : Measurable (logScale F) := by
    unfold logScale; exact (hFm.comp measurable_exp).mul (by fun_prop)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set K := M * exp (Real.log β / 2)
  have hsupp' : ∀ x ∉ Icc (Real.log α) (Real.log β), logScale F x = 0 := by
    intro x hx
    unfold logScale
    rw [hsupp (exp x) fun h => hx ⟨(Real.log_le_iff_le_exp hα).2 h.1,
      (Real.le_log_iff_exp_le (hα.trans_le (h.1.trans h.2))).2 h.2⟩, zero_mul]
  have hK : ∀ x, |logScale F x| ≤ K := by
    intro x
    by_cases hx : exp x ∈ Icc α β
    · have hβ : 0 < β := hα.trans_le (hx.1.trans hx.2)
      have hxl : x ≤ Real.log β := (Real.le_log_iff_exp_le hβ).2 hx.2
      unfold logScale
      rw [abs_mul, abs_of_pos (exp_pos _)]
      exact mul_le_mul (hM _) (exp_le_exp.2 (by linarith)) (exp_pos _).le hM0
    · unfold logScale
      rw [hsupp _ hx, zero_mul, abs_zero]
      positivity
  refine ⟨integrable_of_bound_support hm hK hsupp', ?_⟩
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  refine integrable_of_bound_support (hm.pow_const 2) (K := K ^ 2) (fun x => ?_)
    (fun x hx => by rw [hsupp' x hx]; ring)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2

/-- `logScale F(c·)(x) = e^{−(log c)/2} logScale F(x + log c)`. -/
theorem logScale_comp_mul (F : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    logScale (fun θ => F (c * θ)) x = (exp (Real.log c / 2))⁻¹ * logScale F (x + Real.log c) := by
  unfold logScale
  rw [exp_add, exp_log hc, show (x + Real.log c) / 2 = x / 2 + Real.log c / 2 by ring, exp_add,
    mul_comm (exp x) c]
  field_simp

/-- Integrability of `logScale` passes to dilates. -/
theorem integrable_logScale_comp_mul {F : ℝ → ℝ}
    (h : Integrable (logScale F) ∧ MemLp (logScale F) 2 volume) {c : ℝ} (hc : 0 < c) :
    Integrable (logScale fun θ => F (c * θ)) ∧ MemLp (logScale fun θ => F (c * θ)) 2 volume := by
  have e : logScale (fun θ => F (c * θ))
      = fun x => (exp (Real.log c / 2))⁻¹ * logScale F (x + Real.log c) :=
    funext (logScale_comp_mul F hc)
  rw [e]
  exact ⟨(h.1.comp_add_right _).const_mul _,
    (h.2.comp_measurePreserving (measurePreserving_add_right volume _)).const_mul _⟩

/-- `M[F(c·)](s) = c^{−s} MF(s)`. -/
theorem mellinR_comp_mul (F : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (s : ℂ) :
    mellinR (fun θ => F (c * θ)) s = (c : ℂ) ^ (-s) * mellinR F s := by
  unfold mellinR
  rw [← smul_eq_mul]
  exact mellin_comp_mul_left (fun θ => (F θ : ℂ)) s hc

/-- `‖n^{w}‖ = n^{Re w}` for `n ≥ 1`. -/
theorem norm_natCast_cpow {n : ℕ} (hn : 1 ≤ n) (w : ℂ) : ‖(n : ℂ) ^ w‖ = (n : ℝ) ^ w.re :=
  Complex.norm_natCast_cpow_of_pos (by omega) w

/-- `‖n^{w}‖ ≤ 1` for `n ≥ 1`, `Re w ≤ 0`. -/
theorem norm_natCast_cpow_le_one {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : w.re ≤ 0) :
    ‖(n : ℂ) ^ w‖ ≤ 1 := by
  rw [norm_natCast_cpow hn]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) hw

/-- The von Mangoldt series of line integrals on `Re s = σ > 1` is summable. -/
theorem summable_vonMangoldt_vline {φ : ℂ → ℂ} {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => (Λ n : ℂ) * ∫ y : ℝ, (n : ℂ) ^ (-((σ : ℂ) + y * I)) * φ (σ + y * I) := by
  have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
  refine Summable.of_norm_bounded
    ((Cvs.Zeta.summable_norm_term_vonMangoldt hσ').mul_right (∫ y : ℝ, ‖φ (σ + y * I)‖))
    fun n => ?_
  have e : (Λ n : ℂ) * ∫ y : ℝ, (n : ℂ) ^ (-((σ : ℂ) + y * I)) * φ (σ + y * I)
      = ∫ y : ℝ, LSeries.term (fun k => (Λ k : ℂ)) ((σ : ℂ) + y * I) n * φ (σ + y * I) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Cvs.Zeta.VerticalLineShift.term_vline_eq]; ring
  rw [e]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp_rw [norm_mul, Cvs.Zeta.VerticalLineShift.norm_term_vline]
  exact integral_const_mul _ _

/-! ### `ζ`-identities off the poles -/

/-- `ζ₁(s) = (s − 1) ζ(s)` for `s ≠ 1`. -/
theorem riemannZeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

/-- `−ζ'(s)(s − 1) = (ζ₁(s) − (s − 1)ζ₁'(s))/(s − 1)` for `s ≠ 1`. -/
theorem neg_deriv_zeta_mul_eq {s : ℂ} (hs : s ≠ 1) :
    -deriv riemannZeta s * (s - 1)
      = (riemannZeta₁ s - (s - 1) * deriv riemannZeta₁ s) / (s - 1) := by
  have h := sub_ne_zero.mpr hs
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs]
  field_simp
  ring

/-- `(−ζ'/ζ)(s) ζ₁(s) = −ζ'(s)(s − 1)` where `ζ(s) ≠ 0`, `s ≠ 1`. -/
theorem neg_logDeriv_mul_zeta₁ {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s * riemannZeta₁ s = -deriv riemannZeta s * (s - 1) := by
  rw [riemannZeta₁_eq hs]
  field_simp

/-- A point with `−2 < Re s < 0` is not a trivial zero. -/
theorem ne_neg_two_mul {s : ℂ} (h1 : -2 < s.re) (h2 : s.re < 0) : ∀ n : ℕ, s ≠ -(2 * n) := by
  intro n hn
  have h := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero] at h
  norm_num at h
  rcases n with _ | n
  · simp at h; linarith
  · push_cast at h; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- `(−ζ'/ζ)(1 − s) ζ₁(s) h = (ζ'(s) + 𝒜(s)ζ(s))(s − 1) h` for `Re s < 0` off the trivial zeros. -/
theorem neg_logDeriv_one_sub_mul_zeta₁ {s : ℂ} (hs : s.re < 0) (hs' : ∀ n : ℕ, s ≠ -(2 * n))
    (h : ℂ) :
    -deriv riemannZeta (1 - s) / riemannZeta (1 - s) * (riemannZeta₁ s * h)
      = (deriv riemannZeta s + archA s * riemannZeta s) * (s - 1) * h := by
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [riemannZeta₁_eq hs1, ← zeta_mul_neg_logDeriv_one_sub hs hs']
  ring

/-- Splitting off the pole of `𝒜` at `0`: `(ζ' + 𝒜ζ)(s − 1)h = (ζ' + 𝒜₀ζ)(s − 1)h − ζ₁(s)h/s`. -/
theorem deriv_zeta_add_archA_mul_eq {s : ℂ} (h1 : -2 < s.re) (h2 : s.re < 1) (h0 : s ≠ 0)
    (h : ℂ) :
    (deriv riemannZeta s + archA s * riemannZeta s) * (s - 1) * h
      = (deriv riemannZeta s + archA₀ s * riemannZeta s) * (s - 1) * h
        - riemannZeta₁ s * h / s := by
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at h2
  rw [archA_eq h1 h2 h0, riemannZeta₁_eq hs1]
  field_simp
  ring

/-! ### The left prime channel `Σ Λ(n)⟨E, v(n·)⟩` -/

/-- `ME(1 − s) M[v(n·)](s) = n^{−s} ζ₁(s) H(s)` for `Re s > 0`. -/
theorem mellinR_eimage_mul_dil {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) (v : ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    {s : ℂ} (hs : 0 < s.re) :
    mellinR (eimage a G) (1 - s) * mellinR (fun θ => v (n * θ)) s
      = (n : ℂ) ^ (-s) * riemannZeta₁ s * Hfun a G v s := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mellinR_comp_mul v hn0, mellinR_eimage ha hG hG₁ hG0 hGi
    (by rw [Complex.sub_re, Complex.one_re]; linarith), sub_sub_cancel]
  simp only [Hfun, Complex.ofReal_natCast]
  ring

/-- **The left dilate on `Re s = 2`**: `⟨E, v(n·)⟩ = (1/2π) Re ∫ n^{−s} ζ₁(s) H(s) dy`, `s = 2 + iy`. -/
theorem dil_left_eq {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v)
    (hvb : ∃ M, ∀ θ, |v θ| ≤ M)
    (hvdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|)
    {n : ℕ} (hn : 1 ≤ n) :
    dil (eimage a G) v n = (1 / (2 * π)) *
      (∫ y : ℝ, (n : ℂ) ^ (-(2 + y * I)) * riemannZeta₁ (2 + y * I) * Hfun a G v (2 + y * I)).re := by
  obtain ⟨M, hM⟩ := hvb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hHd := differentiableOn_Hfun ha hG hG₁ hG0 hα hsupp hvm ⟨M, hM⟩
  obtain ⟨C, hC⟩ := norm_Hfun_le ha hG hG₁ hG0 hGi hvdec
  obtain ⟨B, hB⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_zeta₁_mul_le (σ₀ := 1 / 2) (σ₁ := 2) (T₀ := 1)
    (CH := C) (H := Hfun a G v) (by norm_num) (by norm_num) (by norm_num)
    (fun s h1 h2 h3 => hC s (by linarith) h2 h3)
  set f : ℂ → ℂ := fun s => (n : ℂ) ^ (-s) * riemannZeta₁ s * Hfun a G v s with hf
  have hfd : DifferentiableOn ℂ f {s | -1 < s.re} := by
    intro s hs
    exact ((((differentiableAt_id.neg).const_cpow
      (Or.inl (by exact_mod_cast hn0.ne'))).mul
        differentiable_riemannZeta₁.differentiableAt).differentiableWithinAt).mul (hHd s hs)
  have hdec : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖f s‖ ≤ B * (1 + |s.im|) ^ (-(3 / 2 : ℝ)) := by
    intro s h1 h2 h3
    have hb := hB s h1 h2 (by simpa using h3)
    rw [show (-(5 / 4 + (1 / 2 : ℝ) / 2)) = -(3 / 2) by norm_num] at hb
    simp only [hf, mul_assoc]
    rw [norm_mul]
    calc ‖(n : ℂ) ^ (-s)‖ * ‖riemannZeta₁ s * Hfun a G v s‖
        ≤ 1 * (B * (1 + |s.im|) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul (norm_natCast_cpow_le_one hn (by simp; linarith)) hb (norm_nonneg _)
            zero_le_one
      _ = B * (1 + |s.im|) ^ (-(3 / 2 : ℝ)) := one_mul _
  -- Parseval on `Re s = ½`
  have hE := integrable_logScale_eimage ha hG hG₁ hGi
  have hV : Integrable (logScale fun θ => v (n * θ)) ∧ MemLp (logScale fun θ => v (n * θ)) 2 volume :=
    integrable_logScale_of_support (F := fun θ => v (n * θ)) (hvm.comp (measurable_const_mul (n : ℝ)))
    (fun θ => hM (n * θ)) (α := α / n) (β := β / n) (by positivity)
    (fun θ hθ => hsupp _ fun h => hθ ⟨by rw [div_le_iff₀ hn0]; linarith [h.1],
      by rw [le_div_iff₀ hn0]; linarith [h.2]⟩)
  have hP := integral_mul_eq_mellin hE.1 hE.2 hV.1 hV.2
  have hpt : ∀ t : ℝ, mellinR (eimage a G) (1 - (1 / 2 + t * I))
      * mellinR (fun θ => v (n * θ)) (1 / 2 + t * I) = f (((1 / 2 : ℝ) : ℂ) + t * I) := by
    intro t
    have e : ((1 / 2 : ℝ) : ℂ) + t * I = 1 / 2 + t * I := by push_cast; ring
    rw [e]
    exact mellinR_eimage_mul_dil ha hG hG₁ hG0 hGi v hn (by simp)
  simp_rw [hpt] at hP
  have hint : Integrable fun y : ℝ => f (((1 / 2 : ℝ) : ℂ) + y * I) :=
    integrable_vline (continuous_vline hfd fun y => by
      show -1 < ((((1 / 2 : ℝ) : ℂ) + y * I)).re
      rw [vline_re]; norm_num) (by norm_num : (1 : ℝ) < 3 / 2)
      fun s hs h3 => hdec s (by rw [hs]) (by rw [hs]; norm_num) h3
  have hre := integral_re (𝕜 := ℂ) hint
  simp only [RCLike.re_to_complex] at hre
  rw [hre] at hP
  -- the shift `½ → 2`
  have hshift := integral_vline_eq (f := f) (σ₁ := 1 / 2) (σ₂ := 2) (δ := 1 / 2) (κ := 3 / 2)
    (T₀ := 1) (B := B) (by norm_num) (by norm_num) (by norm_num)
    (hfd.mono fun s hs => by simp only [mem_ofPred_eq] at hs ⊢; linarith [hs.1]) hdec
  refine hP.trans ?_
  rw [hshift]
  simp only [hf, Complex.ofReal_ofNat]

/-- **The left prime channel**: `Σ Λ(n)⟨E, v(n·)⟩ = (1/2π) Re ∫ −ζ'(s)(s − 1)H(s) dt + Re H(1)`,
`s = ½ + it`. -/
theorem tsum_primeLeft {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v)
    (hvb : ∃ M, ∀ θ, |v θ| ≤ M)
    (hvdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|) :
    ∑' n : ℕ, (Λ n : ℝ) * dil (eimage a G) v n
      = (1 / (2 * π)) * (∫ t : ℝ, -deriv riemannZeta (cl t) * (cl t - 1) * Hfun a G v (cl t)).re
        + (Hfun a G v 1).re := by
  obtain ⟨M, hM⟩ := hvb
  have hHd := differentiableOn_Hfun ha hG hG₁ hG0 hα hsupp hvm ⟨M, hM⟩
  obtain ⟨C, hC⟩ := norm_Hfun_le ha hG hG₁ hG0 hGi hvdec
  have hH : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖Hfun a G v s‖ ≤ C * (1 + |s.im|) ^ (-3 : ℝ) := fun s h1 h2 h3 => hC s (by linarith) h2 h3
  obtain ⟨B, hB⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_zeta₁_mul_le (σ₀ := 1 / 2) (σ₁ := 2) (T₀ := 1)
    (CH := C) (H := Hfun a G v) (by norm_num) (by norm_num) (by norm_num) hH
  obtain ⟨B', hB'⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_deriv_zeta_mul_le (σ₀ := 1 / 2) (σ₁ := 2)
    (T₀ := 1) (CH := C) (H := Hfun a G v) (by norm_num) (by norm_num) (by norm_num) hH
  set φ : ℂ → ℂ := fun s => riemannZeta₁ s * Hfun a G v s with hφ
  set ψ : ℂ → ℂ := fun s => (riemannZeta₁ s - (s - 1) * deriv riemannZeta₁ s) * Hfun a G v s
    with hψ
  have hφd : DifferentiableOn ℂ φ {s | -1 < s.re} := fun s hs =>
    differentiable_riemannZeta₁.differentiableAt.differentiableWithinAt.mul (hHd s hs)
  have hφ2 : Integrable fun y : ℝ => φ ((2 : ℝ) + y * I) :=
    integrable_vline (continuous_vline hφd fun y => by
      show -1 < (((2 : ℝ) : ℂ) + y * I).re
      rw [vline_re]; norm_num) (κ := 3 / 2) (T₀ := 1) (B := B) (by norm_num) fun s hs h3 => by
        have hb := hB s (by rw [hs]; norm_num) (by rw [hs]) (by simpa using h3)
        rwa [show (-(5 / 4 + (1 / 2 : ℝ) / 2)) = -(3 / 2) by norm_num] at hb
  have hterm : ∀ n : ℕ, (Λ n : ℝ) * dil (eimage a G) v n = 1 / (2 * π) *
      ((Λ n : ℂ) * ∫ y : ℝ, (n : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) * φ ((2 : ℝ) + y * I)).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [dil_left_eq ha hG hG₁ hG0 hGi hα hsupp hvm ⟨M, hM⟩ hvdec hn, Complex.re_ofReal_mul]
    simp only [hφ, Complex.ofReal_ofNat, mul_assoc]
    ring
  have hsum := summable_vonMangoldt_vline (φ := φ) (σ := 2) (by norm_num)
  have hL := integral_LSeries_vonMangoldt_vline (φ := φ) (σ := 2) (by norm_num) hφ2
  rw [tsum_congr hterm, tsum_mul_left, ← Complex.re_tsum hsum, ← hL]
  -- the pole of `−ζ'` at `1`
  have hψd : DifferentiableOn ℂ ψ {s | -1 < s.re} := by
    have hd1 := (differentiable_riemannZeta₁.differentiableOn (s := univ)).deriv isOpen_univ
    intro s hs
    exact ((differentiable_riemannZeta₁.differentiableAt.sub
      ((differentiableAt_id.sub (differentiableAt_const _)).mul
        ((hd1 s (mem_univ _)).differentiableAt (univ_mem' fun _ => mem_univ _))))
      ).differentiableWithinAt.mul (hHd s hs)
  have hψeq : ∀ s : ℂ, s ≠ 1 →
      ψ s = -(deriv riemannZeta s * (s - 1) * Hfun a G v s) * (s - 1) := by
    intro s hs
    have h := sub_ne_zero.mpr hs
    have e := neg_deriv_zeta_mul_eq hs
    have e' : riemannZeta₁ s - (s - 1) * deriv riemannZeta₁ s
        = -deriv riemannZeta s * (s - 1) * (s - 1) := by
      rw [e]; field_simp
    simp only [hψ, e']
    ring
  have hψdec : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖ψ s‖ ≤ (2 * B') * (1 + |s.im|) ^ (-(7 / 16 : ℝ)) := by
    intro s h1 h2 h3
    have hb := hB' s h1 h2 (by rw [show max (1 : ℝ) 2 = 2 by norm_num]; exact h3)
    rw [show (-(5 / 4 + (1 / 2 : ℝ) / 2 - 1 / 16)) = -(23 / 16) by norm_num] at hb
    have hs1 : s ≠ 1 := by
      rintro rfl; simp at h3; linarith
    have hpos : 0 < 1 + |s.im| := by positivity
    rw [hψeq s hs1, norm_mul, norm_neg]
    have hX := (norm_nonneg _).trans hb
    calc ‖deriv riemannZeta s * (s - 1) * Hfun a G v s‖ * ‖s - 1‖
        ≤ (B' * (1 + |s.im|) ^ (-(23 / 16 : ℝ))) * (2 * (1 + |s.im|)) :=
          mul_le_mul hb (Cvs.Zeta.ZetaDerivStripGrowth.norm_sub_one_le (by linarith) (by linarith))
            (norm_nonneg _) hX
      _ = (2 * B') * ((1 + |s.im|) ^ (-(23 / 16 : ℝ)) * (1 + |s.im|)) := by ring
      _ = (2 * B') * (1 + |s.im|) ^ (-(7 / 16 : ℝ)) := by
          rw [← Real.rpow_add_one hpos.ne']; norm_num
  have hpole := integral_vline_sub_of_pole (φ := ψ) (σ₁ := 1 / 2) (σ₂ := 2) (x₀ := 1)
    (δ := 1 / 2) (κ := 7 / 16) (T₀ := 2) (B := 2 * B') (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (hψd.mono fun s hs => by simp only [mem_ofPred_eq] at hs ⊢; linarith [hs.1])
    hψdec
  simp only [Complex.ofReal_one] at hpole
  have hψ1 : ψ 1 = Hfun a G v 1 := by simp [hψ]
  have h2 : ∀ y : ℝ, -deriv riemannZeta ((2 : ℝ) + y * I) / riemannZeta ((2 : ℝ) + y * I)
      * φ ((2 : ℝ) + y * I) = ψ ((2 : ℝ) + y * I) / ((2 : ℝ) + y * I - 1) := by
    intro y
    set s : ℂ := ((2 : ℝ) : ℂ) + y * I
    have hsre : s.re = 2 := vline_re 2 y
    have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; norm_num at hsre
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; norm_num)
    have h := sub_ne_zero.mpr hs1
    rw [hψeq s hs1]
    simp only [hφ]
    rw [← mul_assoc, neg_logDeriv_mul_zeta₁ hs1 hz]
    field_simp
  have hhalf : ∀ t : ℝ, -deriv riemannZeta (cl t) * (cl t - 1) * Hfun a G v (cl t)
      = ψ ((1 / 2 : ℝ) + t * I) / ((1 / 2 : ℝ) + t * I - 1) := by
    intro t
    rw [cl_eq]
    set s : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I
    have hsre : s.re = 1 / 2 := vline_re _ t
    have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; norm_num at hsre
    have h := sub_ne_zero.mpr hs1
    rw [hψeq s hs1]
    field_simp
  rw [integral_congr_ae (Eventually.of_forall h2), sub_eq_iff_eq_add'.mp hpole, hψ1,
    integral_congr_ae (Eventually.of_forall hhalf), Complex.add_re,
    show (2 * (π : ℂ) * Hfun a G v 1) = ((2 * π : ℝ) : ℂ) * Hfun a G v 1 by push_cast; ring,
    Complex.re_ofReal_mul, mul_add]
  congr 1
  field_simp

/-! ### The right prime channel `Σ Λ(n)⟨E(n·), v⟩` -/

/-- **The right dilate on `Re s = −¼`**: `⟨E(n·), v⟩ = (1/2π) Re ∫ n^{s−1} ζ₁(s) H(s) dy`,
`s = −¼ + iy`. -/
theorem dil_right_eq {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v)
    (hvb : ∃ M, ∀ θ, |v θ| ≤ M)
    (hvdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|)
    {n : ℕ} (hn : 1 ≤ n) :
    dil v (eimage a G) n = (1 / (2 * π)) *
      (∫ y : ℝ, (n : ℂ) ^ ((-1 / 4 + y * I) - 1) * riemannZeta₁ (-1 / 4 + y * I)
        * Hfun a G v (-1 / 4 + y * I)).re := by
  obtain ⟨M, hM⟩ := hvb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hHd := differentiableOn_Hfun ha hG hG₁ hG0 hα hsupp hvm ⟨M, hM⟩
  obtain ⟨C, hC⟩ := norm_Hfun_le ha hG hG₁ hG0 hGi hvdec
  obtain ⟨B, hB⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_zeta₁_mul_le (σ₀ := -1 / 4) (σ₁ := 1 / 2) (T₀ := 1)
    (CH := C) (H := Hfun a G v) (by norm_num) (by norm_num) (by norm_num)
    (fun s h1 h2 h3 => hC s (by linarith) (by linarith) h3)
  set f : ℂ → ℂ := fun s => (n : ℂ) ^ (s - 1) * riemannZeta₁ s * Hfun a G v s with hf
  have hfd : DifferentiableOn ℂ f {s | -1 < s.re} := by
    intro s hs
    exact ((((differentiableAt_id.sub (differentiableAt_const _)).const_cpow
      (Or.inl (by exact_mod_cast hn0.ne'))).mul
        differentiable_riemannZeta₁.differentiableAt).differentiableWithinAt).mul (hHd s hs)
  have hdec : ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖f s‖ ≤ B * (1 + |s.im|) ^ (-(9 / 8 : ℝ)) := by
    intro s h1 h2 h3
    have hb := hB s h1 h2 (by simpa using h3)
    rw [show (-(5 / 4 + (-1 / 4 : ℝ) / 2)) = -(9 / 8) by norm_num] at hb
    simp only [hf, mul_assoc]
    rw [norm_mul]
    calc ‖(n : ℂ) ^ (s - 1)‖ * ‖riemannZeta₁ s * Hfun a G v s‖
        ≤ 1 * (B * (1 + |s.im|) ^ (-(9 / 8 : ℝ))) :=
          mul_le_mul (norm_natCast_cpow_le_one hn (by simp; linarith)) hb (norm_nonneg _)
            zero_le_one
      _ = B * (1 + |s.im|) ^ (-(9 / 8 : ℝ)) := one_mul _
  -- Parseval on `Re s = ½`
  have hE := integrable_logScale_comp_mul (integrable_logScale_eimage ha hG hG₁ hGi) hn0
  have hV := integrable_logScale_of_support hvm hM hα hsupp
  have hP := integral_mul_eq_mellin hE.1 hE.2 hV.1 hV.2
  have hpt : ∀ t : ℝ, mellinR (fun θ => eimage a G (n * θ)) (1 - (1 / 2 + t * I))
      * mellinR v (1 / 2 + t * I) = f (((1 / 2 : ℝ) : ℂ) + t * I) := by
    intro t
    have e : ((1 / 2 : ℝ) : ℂ) + t * I = 1 / 2 + t * I := by push_cast; ring
    rw [e]
    exact mellinR_eimage_dil ha hG hG₁ hG0 hGi v hn (by simp)
  simp_rw [hpt] at hP
  have hint : Integrable fun y : ℝ => f (((1 / 2 : ℝ) : ℂ) + y * I) :=
    integrable_vline (continuous_vline hfd fun y => by
      show -1 < ((((1 / 2 : ℝ) : ℂ) + y * I)).re
      rw [vline_re]; norm_num) (by norm_num : (1 : ℝ) < 9 / 8)
      fun s hs h3 => hdec s (by rw [hs]; norm_num) (by rw [hs]) h3
  have hre := integral_re (𝕜 := ℂ) hint
  simp only [RCLike.re_to_complex] at hre
  rw [hre] at hP
  -- the shift `½ → −¼`
  have hshift := integral_vline_eq (f := f) (σ₁ := -1 / 4) (σ₂ := 1 / 2) (δ := 1 / 4)
    (κ := 9 / 8) (T₀ := 1) (B := B) (by norm_num) (by norm_num) (by norm_num)
    (hfd.mono fun s hs => by simp only [mem_ofPred_eq] at hs ⊢; linarith [hs.1]) hdec
  have e : dil v (eimage a G) n = ∫ θ in Ioi (0 : ℝ), eimage a G (n * θ) * v θ := by
    unfold dil; simp only [mul_comm]
  rw [e, hP, ← hshift]
  simp only [hf]
  push_cast
  rfl

/-- **The right prime channel** (`HasSum`): `Σ Λ(n)⟨E(n·), v⟩ = (1/2π) Re ∫ (ζ' + 𝒜ζ)(s)(s − 1)H(s) dt
− (a/2) Re g(0) Re Mv(0)` on `s = ½ + it`. -/
theorem hasSum_primeRight {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v)
    (hvb : ∃ M, ∀ θ, |v θ| ≤ M)
    (hvdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|) :
    HasSum (fun n : ℕ => (Λ n : ℝ) * dil v (eimage a G) n)
      ((1 / (2 * π)) * (∫ t : ℝ, (deriv riemannZeta (cl t) + archA (cl t) * riemannZeta (cl t))
          * (cl t - 1) * Hfun a G v (cl t)).re - (a / 2) * (gM G 0).re * (mellinR v 0).re) := by
  obtain ⟨M, hM⟩ := hvb
  have hHd := differentiableOn_Hfun ha hG hG₁ hG0 hα hsupp hvm ⟨M, hM⟩
  obtain ⟨C, hC⟩ := norm_Hfun_le ha hG hG₁ hG0 hGi hvdec
  have hH : ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖Hfun a G v s‖ ≤ C * (1 + |s.im|) ^ (-3 : ℝ) :=
    fun s h1 h2 h3 => hC s (by linarith) (by linarith) h3
  obtain ⟨B, hB⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_zeta₁_mul_le (σ₀ := -1 / 4) (σ₁ := 1 / 2) (T₀ := 1)
    (CH := C) (H := Hfun a G v) (by norm_num) (by norm_num) (by norm_num) hH
  obtain ⟨B₁, hB₁⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_deriv_zeta_mul_le (σ₀ := -1 / 4) (σ₁ := 1 / 2)
    (T₀ := 1) (CH := C) (H := Hfun a G v) (by norm_num) (by norm_num) (by norm_num) hH
  obtain ⟨B₂, hB₂⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_archA₀_mul_le (σ₀ := -1 / 4) (σ₁ := 1 / 2)
    (T₀ := 1) (CH := C) (H := Hfun a G v) (by norm_num) (by norm_num) hH
  set φ : ℂ → ℂ := fun s => riemannZeta₁ s * Hfun a G v s with hφ
  set k : ℂ → ℂ := fun s =>
    (deriv riemannZeta s + archA s * riemannZeta s) * (s - 1) * Hfun a G v s with hk
  set k₀ : ℂ → ℂ := fun s =>
    (deriv riemannZeta s + archA₀ s * riemannZeta s) * (s - 1) * Hfun a G v s with hk₀
  have hφd : DifferentiableOn ℂ φ {s | -1 < s.re} := fun s hs =>
    differentiable_riemannZeta₁.differentiableAt.differentiableWithinAt.mul (hHd s hs)
  have hφdec : ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖φ s‖ ≤ B * (1 + |s.im|) ^ (-(9 / 8 : ℝ)) := by
    intro s h1 h2 h3
    have hb := hB s h1 h2 (by simpa using h3)
    rwa [show (-(5 / 4 + (-1 / 4 : ℝ) / 2)) = -(9 / 8) by norm_num] at hb
  have hφint : Integrable fun y : ℝ => φ (((-1 / 4 : ℝ) : ℂ) + y * I) :=
    integrable_vline (continuous_vline hφd fun y => by
      show -1 < ((((-1 / 4 : ℝ) : ℂ) + y * I)).re
      rw [vline_re]; norm_num) (by norm_num : (1 : ℝ) < 9 / 8)
      fun s hs h3 => hφdec s (by rw [hs]) (by rw [hs]; norm_num) h3
  -- the right dilates as line integrals on `Re w = 5/4`, `w = 1 − s`
  set φ' : ℂ → ℂ := fun w => φ (1 - w) with hφ'
  have hrefl : ∀ y : ℝ, 1 - (((5 / 4 : ℝ) : ℂ) + y * I) = ((-1 / 4 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by
    intro y; push_cast; ring
  have hφ'int : Integrable fun y : ℝ => φ' (((5 / 4 : ℝ) : ℂ) + y * I) := by
    have h := hφint.comp_neg
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [hφ', hrefl]
  have hterm : ∀ n : ℕ, (Λ n : ℝ) * dil v (eimage a G) n = 1 / (2 * π) *
      ((Λ n : ℂ) * ∫ y : ℝ, (n : ℂ) ^ (-(((5 / 4 : ℝ) : ℂ) + y * I))
        * φ' ((5 / 4 : ℝ) + y * I)).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [dil_right_eq ha hG hG₁ hG0 hGi hα hsupp hvm ⟨M, hM⟩ hvdec hn, Complex.re_ofReal_mul]
    have hI : (∫ y : ℝ, (n : ℂ) ^ ((-1 / 4 + y * I) - 1) * riemannZeta₁ (-1 / 4 + y * I)
        * Hfun a G v (-1 / 4 + y * I))
        = ∫ y : ℝ, (n : ℂ) ^ (-(((5 / 4 : ℝ) : ℂ) + y * I)) * φ' ((5 / 4 : ℝ) + y * I) := by
      rw [← integral_neg_eq_self]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hφ', hφ, hrefl]
      have e : (-1 / 4 + ((-y : ℝ) : ℂ) * I) - 1 = -(((5 / 4 : ℝ) : ℂ) + y * I) := by
        push_cast; ring
      have e' : ((-1 / 4 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = -1 / 4 + ((-y : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [e', e, mul_assoc]
    rw [hI]
    ring
  have hsum := summable_vonMangoldt_vline (φ := φ') (σ := 5 / 4) (by norm_num)
  have hL := integral_LSeries_vonMangoldt_vline (φ := φ') (σ := 5 / 4) (by norm_num) hφ'int
  have hS : HasSum (fun n : ℕ => (Λ n : ℂ) * ∫ y : ℝ, (n : ℂ) ^ (-(((5 / 4 : ℝ) : ℂ) + y * I))
      * φ' ((5 / 4 : ℝ) + y * I)) (∫ y : ℝ, -deriv riemannZeta (((5 / 4 : ℝ) : ℂ) + y * I)
        / riemannZeta (((5 / 4 : ℝ) : ℂ) + y * I) * φ' (((5 / 4 : ℝ) : ℂ) + y * I)) := by
    rw [hL]; exact hsum.hasSum
  -- the line integral `∫ (−ζ'/ζ)(w) φ(1 − w)` on `Re w = 5/4` is `∫ k` on `Re s = −¼`
  have hV1 : (∫ y : ℝ, -deriv riemannZeta (((5 / 4 : ℝ) : ℂ) + y * I)
        / riemannZeta (((5 / 4 : ℝ) : ℂ) + y * I) * φ' (((5 / 4 : ℝ) : ℂ) + y * I))
      = ∫ y : ℝ, k (((-1 / 4 : ℝ) : ℂ) + y * I) := by
    rw [← integral_neg_eq_self (fun y : ℝ => k (((-1 / 4 : ℝ) : ℂ) + y * I))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have e : ((5 / 4 : ℝ) : ℂ) + y * I = 1 - (((-1 / 4 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      push_cast; ring
    set s : ℂ := ((-1 / 4 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I
    have hsre : s.re = -1 / 4 := vline_re _ _
    simp only [hφ', hφ, hk, e, sub_sub_cancel]
    exact neg_logDeriv_one_sub_mul_zeta₁ (by rw [hsre]; norm_num)
      (ne_neg_two_mul (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)) _
  -- the shift `−¼ → ½` across the pole of `𝒜` at `0`
  have hzd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun s hs =>
    (differentiableAt_riemannZeta (mem_compl_singleton_iff.mp hs)).differentiableWithinAt
  have hdz := hzd.deriv isOpen_compl_singleton
  have hHopen : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hk₀d : DifferentiableOn ℂ k₀ {s | -1 / 4 - 1 / 4 < s.re ∧ s.re < 1 / 2 + 1 / 4} := by
    intro s hs
    simp only [mem_ofPred_eq] at hs
    obtain ⟨hs₁, hs₂⟩ := hs
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs₂
    have hA := (differentiableOn_archA₀ s ⟨by linarith, by linarith⟩).differentiableAt
      ((Cvs.Zeta.VerticalLineShift.isOpen_vstrip (-2) 1).mem_nhds ⟨by linarith, by linarith⟩)
    have hD := (hdz s (mem_compl_singleton_iff.mpr hs1)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.mpr hs1))
    have hH := (hHd s (show -1 < s.re by linarith)).differentiableAt
      (hHopen.mem_nhds (show -1 < s.re by linarith))
    exact (((hD.add (hA.mul (differentiableAt_riemannZeta hs1))).mul
        (differentiableAt_id.sub (differentiableAt_const _))).mul hH).differentiableWithinAt
  have hk₀dec : ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 1 / 2 → 2 ≤ |s.im| →
      ‖k₀ s‖ ≤ (B₁ + B₂) * (1 + |s.im|) ^ (-(17 / 16 : ℝ)) := by
    intro s h1 h2 h3
    have hm : max (1 : ℝ) 2 ≤ |s.im| := by rw [show max (1 : ℝ) 2 = 2 by norm_num]; exact h3
    have e17 : (-(5 / 4 + (-1 / 4 : ℝ) / 2 - 1 / 16)) = -(17 / 16) := by norm_num
    have hb₁ := hB₁ s h1 h2 hm
    have hb₂ := hB₂ s h1 h2 hm
    rw [e17] at hb₁ hb₂
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at h2
    have e : k₀ s = deriv riemannZeta s * (s - 1) * Hfun a G v s
        + archA₀ s * riemannZeta₁ s * Hfun a G v s := by
      simp only [hk₀, riemannZeta₁_eq hs1]; ring
    rw [e, add_mul]
    exact (norm_add_le _ _).trans (add_le_add hb₁ hb₂)
  have hk₀int : ∀ σ : ℝ, -1 / 4 ≤ σ → σ ≤ 1 / 2 → Integrable fun y : ℝ => k₀ (σ + y * I) :=
    fun σ h1 h2 => integrable_vline (continuous_vline hk₀d fun y => by
      constructor <;> rw [vline_re] <;> linarith) (by norm_num : (1 : ℝ) < 17 / 16)
      fun s hs h3 => hk₀dec s (by rw [hs]; exact h1) (by rw [hs]; exact h2) h3
  have hφsint : ∀ σ : ℝ, -1 / 4 ≤ σ → σ ≤ 1 / 2 → σ ≠ 0 →
      Integrable fun y : ℝ => φ (σ + y * I) / (σ + y * I - ((0 : ℝ) : ℂ)) := by
    intro σ h1 h2 hσ0
    refine integrable_vline (f := fun s => φ s / (s - ((0 : ℝ) : ℂ))) (T₀ := 1) (B := B)
      ((continuous_vline hφd fun y => by
        show -1 < ((σ : ℂ) + y * I).re
        rw [vline_re]; linarith).div (by fun_prop) fun y h => hσ0 ?_)
      (by norm_num : (1 : ℝ) < 9 / 8) fun s (hs : s.re = σ) (h3 : 1 ≤ |s.im|) => ?_
    · simpa using congrArg Complex.re h
    · simp only [Complex.ofReal_zero, sub_zero]
      have hsn : 1 ≤ ‖s‖ := h3.trans (Complex.abs_im_le_norm s)
      rw [norm_div]
      exact (div_le_self (norm_nonneg _) hsn).trans
        (hφdec s (by rw [hs]; exact h1) (by rw [hs]; exact h2) h3)
  have hksplit : ∀ σ : ℝ, -1 / 4 ≤ σ → σ ≤ 1 / 2 → σ ≠ 0 →
      ∫ y : ℝ, k (σ + y * I)
        = (∫ y : ℝ, k₀ (σ + y * I)) - ∫ y : ℝ, φ (σ + y * I) / (σ + y * I - ((0 : ℝ) : ℂ)) := by
    intro σ h1 h2 hσ0
    rw [← integral_sub (hk₀int σ h1 h2) (hφsint σ h1 h2 hσ0)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hsre := vline_re σ y
    have hs0 : (σ : ℂ) + y * I ≠ 0 := fun h => hσ0 (by rw [h] at hsre; simpa using hsre.symm)
    simp only [hk, hk₀, hφ, Complex.ofReal_zero, sub_zero]
    exact deriv_zeta_add_archA_mul_eq (by rw [hsre]; linarith) (by rw [hsre]; linarith) hs0 _
  have hk₀shift := integral_vline_eq (f := k₀) (σ₁ := -1 / 4) (σ₂ := 1 / 2) (δ := 1 / 4)
    (κ := 17 / 16) (T₀ := 2) (B := B₁ + B₂) (by norm_num) (by norm_num) (by norm_num) hk₀d hk₀dec
  have hpole := integral_vline_sub_of_pole (φ := φ) (σ₁ := -1 / 4) (σ₂ := 1 / 2) (x₀ := 0)
    (δ := 1 / 4) (κ := 9 / 8) (T₀ := 1) (B := B) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (hφd.mono fun s hs => by simp only [mem_ofPred_eq] at hs ⊢; linarith [hs.1])
    hφdec
  have hV2 : ∫ y : ℝ, k (((-1 / 4 : ℝ) : ℂ) + y * I)
      = (∫ y : ℝ, k (((1 / 2 : ℝ) : ℂ) + y * I)) + 2 * (π : ℂ) * φ 0 := by
    simp only [Complex.ofReal_zero] at hpole
    rw [hksplit _ le_rfl (by norm_num) (by norm_num), hksplit _ (by norm_num) le_rfl (by norm_num),
      hk₀shift, ← hpole]
    simp only [Complex.ofReal_zero]
    ring
  have hV3 : ∫ y : ℝ, k (((1 / 2 : ℝ) : ℂ) + y * I) = ∫ t : ℝ, k (cl t) :=
    integral_congr_ae (Eventually.of_forall fun t => by simp only [cl_eq])
  have hφ0 : 2 * (π : ℂ) * φ 0 = ((2 * π * (-(a / 2)) * poleM v : ℝ) : ℂ) * gM G 0 := by
    simp only [hφ, riemannZeta₁_zero, Hfun_zero a v hGi, mellinR_zero]
    push_cast; ring
  have hval : (1 / (2 * π)) * (∫ t : ℝ, (deriv riemannZeta (cl t) + archA (cl t)
        * riemannZeta (cl t)) * (cl t - 1) * Hfun a G v (cl t)).re
        - (a / 2) * (gM G 0).re * (mellinR v 0).re
      = 1 / (2 * π) * (∫ y : ℝ, -deriv riemannZeta (((5 / 4 : ℝ) : ℂ) + y * I)
        / riemannZeta (((5 / 4 : ℝ) : ℂ) + y * I) * φ' (((5 / 4 : ℝ) : ℂ) + y * I)).re := by
    rw [hV1, hV2, hV3, hφ0, Complex.add_re, Complex.re_ofReal_mul, mellinR_zero,
      Complex.ofReal_re]
    simp only [hk]
    field_simp
    ring
  rw [show (fun n : ℕ => (Λ n : ℝ) * dil v (eimage a G) n) = _ from funext hterm, hval]
  exact (Complex.hasSum_re hS).mul_left _

/-! ### The arch channel and the integrands on the critical line -/

theorem continuous_cl : Continuous cl := by unfold cl; fun_prop

/-- `t ↦ 𝒜(s)ζ₁(s)H(s)` is integrable on `s = ½ + it`. -/
theorem integrable_archA_line {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v)
    (hvb : ∃ M, ∀ θ, |v θ| ≤ M)
    (hvdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|) :
    Integrable fun t : ℝ => archA (cl t) * riemannZeta₁ (cl t) * Hfun a G v (cl t) := by
  have hHd := differentiableOn_Hfun ha hG hG₁ hG0 hα hsupp hvm hvb
  obtain ⟨C, hC⟩ := norm_Hfun_le ha hG hG₁ hG0 hGi hvdec
  obtain ⟨B, hB⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_archA_mul_le (σ₀ := 1 / 2) (σ₁ := 1 / 2) (T₀ := 1)
    (CH := C) (H := Hfun a G v) (by norm_num) (by norm_num)
    (fun s h1 h2 h3 => hC s (by linarith) (by linarith) h3)
  have hf : (fun t : ℝ => archA (cl t) * riemannZeta₁ (cl t) * Hfun a G v (cl t))
      = fun t : ℝ => (archSymbol t : ℂ) * riemannZeta₁ (cl t) * Hfun a G v (cl t) :=
    funext fun t => by rw [archA_cl]
  refine integrable_of_decay (T₀ := 2) (B := B) (κ := 23 / 16) ?_ (by norm_num) fun y hy => ?_
  · rw [hf]
    exact ((Complex.continuous_ofReal.comp Cvs.WeilForm.Archimedean.ArchFormIntegrable.continuous_archSymbol).mul
      (differentiable_riemannZeta₁.continuous.comp continuous_cl)).mul
      (hHd.continuousOn.comp_continuous continuous_cl fun t => by
        show -1 < (cl t).re
        rw [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_re]; norm_num)
  · have hb := hB (cl y) (by simp) (by simp)
      (by rw [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_im, show max (1 : ℝ) 2 = 2 by norm_num]; exact hy)
    rw [show (-(5 / 4 + (1 / 2 : ℝ) / 2 - 1 / 16)) = -(23 / 16) by norm_num,
      Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_im] at hb
    exact hb

/-- `t ↦ −ζ'(s)(s − 1)H(s)` is integrable on `s = ½ + it`. -/
theorem integrable_deriv_zeta_line {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v)
    (hvb : ∃ M, ∀ θ, |v θ| ≤ M)
    (hvdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|) :
    Integrable fun t : ℝ => -deriv riemannZeta (cl t) * (cl t - 1) * Hfun a G v (cl t) := by
  have hHd := differentiableOn_Hfun ha hG hG₁ hG0 hα hsupp hvm hvb
  obtain ⟨C, hC⟩ := norm_Hfun_le ha hG hG₁ hG0 hGi hvdec
  obtain ⟨B, hB⟩ := Cvs.Zeta.ZetaDerivStripGrowth.norm_deriv_zeta_mul_le (σ₀ := 1 / 2) (σ₁ := 1 / 2)
    (T₀ := 1) (CH := C) (H := Hfun a G v) (by norm_num) (by norm_num) (by norm_num)
    (fun s h1 h2 h3 => hC s (by linarith) (by linarith) h3)
  have hzd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun s hs =>
    (differentiableAt_riemannZeta (mem_compl_singleton_iff.mp hs)).differentiableWithinAt
  have hcl1 : ∀ t : ℝ, cl t ∈ ({1}ᶜ : Set ℂ) := fun t h => by
    have := congrArg Complex.re (mem_singleton_iff.mp h)
    rw [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_re] at this; norm_num at this
  refine integrable_of_decay (T₀ := 2) (B := B) (κ := 23 / 16) ?_ (by norm_num) fun y hy => ?_
  · exact (((hzd.deriv isOpen_compl_singleton).continuousOn.comp_continuous continuous_cl
      hcl1).neg.mul (continuous_cl.sub continuous_const)).mul
      (hHd.continuousOn.comp_continuous continuous_cl fun t => by
        show -1 < (cl t).re
        rw [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_re]; norm_num)
  · have hb := hB (cl y) (by simp) (by simp)
      (by rw [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_im, show max (1 : ℝ) 2 = 2 by norm_num]; exact hy)
    rw [show (-(5 / 4 + (1 / 2 : ℝ) / 2 - 1 / 16)) = -(23 / 16) by norm_num,
      Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_im] at hb
    rw [neg_mul, neg_mul, norm_neg]
    exact hb

/-- **The arch channel**: `∫ a(t) ρ_{E,v}(t) dt = (1/2π) Re ∫ 𝒜(s)ζ₁(s)H(s) dt` on `s = ½ + it`. -/
theorem arch_eimage {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v)
    (hvb : ∃ M, ∀ θ, |v θ| ≤ M)
    (hvdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|) :
    ∫ t, archSymbol t * crossSpec (logScale (eimage a G)) (logScale v) t
      = (1 / (2 * π)) * (∫ t : ℝ, archA (cl t) * riemannZeta₁ (cl t) * Hfun a G v (cl t)).re := by
  have hint := integrable_archA_line ha hG hG₁ hG0 hGi hα hsupp hvm hvb hvdec
  have hpt : ∀ t : ℝ, archSymbol t * crossSpec (logScale (eimage a G)) (logScale v) t
      = (archA (cl t) * riemannZeta₁ (cl t) * Hfun a G v (cl t)).re / (2 * π) := by
    intro t
    rw [crossSpec_logScale]
    have e : (1 / 2 : ℂ) + t * I = cl t := by simp only [cl]; ring
    rw [e, mellinR_eimage ha hG hG₁ hG0 hGi (w := 1 - cl t) (by simp), sub_sub_cancel, archA_cl,
      mul_div_assoc', ← Complex.re_ofReal_mul]
    simp only [Hfun]
    congr 2
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_div]
  have hre := integral_re (𝕜 := ℂ) hint
  simp only [RCLike.re_to_complex] at hre
  rw [hre]
  ring

/-! ### The radical lemma -/

/-- **The radical lemma**: `weilθ(E_G, v) = 0` for `G ∈ C¹[0, 1]` with `G(0) = 0 = ∫₀¹ G` and `v`
bounded, measurable, supported in `[α, β] ⊂ (0, ∞)`, with `|Mv(s)| ≤ C/|Im s|` on `−½ ≤ Re s ≤ 2`. -/
theorem radical_lemma {a : ℝ} (ha : 0 < a) {G G₁ v : ℝ → ℝ}
    (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, v θ = 0) (hvm : Measurable v)
    (hvb : ∃ M, ∀ θ, |v θ| ≤ M)
    (hvdec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|) :
    weilθ (eimage a G) v = 0 := by
  have hR := hasSum_primeRight ha hG hG₁ hG0 hGi hα hsupp hvm hvb hvdec
  have hLfin : ∀ n ∉ Finset.range (⌊β / a⌋₊ + 1), (Λ n : ℝ) * dil (eimage a G) v n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) hn
    have hβ : β < n * a := by
      have := Nat.lt_of_floor_lt hn
      rwa [div_lt_iff₀ ha] at this
    unfold dil
    rw [setIntegral_eq_zero_of_forall_eq_zero fun θ _ => ?_, mul_zero]
    by_cases hv : v (n * θ) = 0
    · rw [hv, mul_zero]
    · have hmem : (n : ℝ) * θ ∈ Icc α β := by
        by_contra h; exact hv (hsupp _ h)
      rw [eimage_of_lt ha (lt_of_mul_lt_mul_left (hmem.2.trans_lt hβ) hn0.le), zero_mul]
  have hLs : Summable fun n : ℕ => (Λ n : ℝ) * dil (eimage a G) v n :=
    summable_of_ne_finset_zero hLfin
  have hsplit : ∑' n : ℕ, (Λ n : ℝ) * (dil (eimage a G) v n + dil v (eimage a G) n)
      = (∑' n : ℕ, (Λ n : ℝ) * dil (eimage a G) v n)
        + ∑' n : ℕ, (Λ n : ℝ) * dil v (eimage a G) n := by
    simp_rw [mul_add]; exact hLs.tsum_add hR.summable
  have h₁ := integrable_archA_line ha hG hG₁ hG0 hGi hα hsupp hvm hvb hvdec
  have h₂ := integrable_deriv_zeta_line ha hG hG₁ hG0 hGi hα hsupp hvm hvb hvdec
  have h₃ : ∫ t : ℝ, (deriv riemannZeta (cl t) + archA (cl t) * riemannZeta (cl t))
        * (cl t - 1) * Hfun a G v (cl t)
      = (∫ t : ℝ, archA (cl t) * riemannZeta₁ (cl t) * Hfun a G v (cl t))
        - ∫ t : ℝ, -deriv riemannZeta (cl t) * (cl t - 1) * Hfun a G v (cl t) := by
    rw [← integral_sub h₁ h₂]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have hs1 : cl t ≠ 1 := fun h => by
      have := congrArg Complex.re h
      rw [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl_re] at this; norm_num at this
    simp only [riemannZeta₁_eq hs1]
    ring
  unfold weilθ
  rw [hsplit, tsum_primeLeft ha hG hG₁ hG0 hGi hα hsupp hvm hvb hvdec, hR.tsum_eq,
    arch_eimage ha hG hG₁ hG0 hGi hα hsupp hvm hvb hvdec, poleP_eimage ha hG hG₁ hG0 hGi,
    poleM_eimage ha hG hG₁ hG0 hGi, poleM_eq_mellinR v, poleP_of_support hsupp, h₃, Hfun_one,
    mellinR_one v, Complex.sub_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-! ### The spine instance `a = 2π/c`, `G̃ = G − G(0)β(·/a)` -/

/-- `∫₀¹ F = 0` for `F` continuous and even on `[−1, 1]` with `∫_{−1}^{1} F = 0`. -/
theorem integral_zero_one_of_even {F : ℝ → ℝ} (hF : ContinuousOn F (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, F (-s) = F s) (hi : ∫ s in (-1 : ℝ)..1, F s = 0) :
    ∫ s in (0 : ℝ)..1, F s = 0 := by
  have h1 : IntervalIntegrable F volume (-1) 0 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (hF.mono (Icc_subset_Icc le_rfl (by norm_num)))
  have h2 : IntervalIntegrable F volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (hF.mono (Icc_subset_Icc (by norm_num) le_rfl))
  have hneg : ∫ s in (-1 : ℝ)..0, F s = ∫ s in (0 : ℝ)..1, F s := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (f := F)
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact heven s ⟨by linarith [hs.1], hs.2⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, hneg] at hi
  linarith

end Cvs.WeilForm.EImageRadical
