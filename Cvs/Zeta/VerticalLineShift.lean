import Mathlib
import Cvs.Zeta.RectArgument
import Cvs.Zeta.RectCauchy
import Cvs.Zeta.RectWinding
import Cvs.Zeta.XiVertical

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Moving vertical lines

For `f` holomorphic on an open vertical strip with polynomial decay in `|Im s|`, the integrals
along two lines `Re s = σ₁, σ₂` agree; a simple pole at a real `x₀` between them contributes
`2πφ(x₀)`; on `Re s = σ > 1` the von Mangoldt series of `−ζ'/ζ` integrates term by term.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology LSeries ArithmeticFunction
open scoped Interval

namespace Cvs.Zeta.VerticalLineShift

/-! ### Integrability and the horizontal sides -/

/-- A continuous function on `ℝ` bounded by `B(1+|y|)^{−κ}` for `|y| ≥ T₀`, with `κ > 1`,
is integrable. -/
theorem integrable_of_decay {h : ℝ → ℂ} (hc : Continuous h) {T₀ B κ : ℝ} (hκ : 1 < κ)
    (hd : ∀ y : ℝ, T₀ ≤ |y| → ‖h y‖ ≤ B * (1 + |y|) ^ (-κ)) : Integrable h := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -|T₀|) (b := |T₀|)).exists_bound_of_continuousOn
    hc.continuousOn
  have hint : Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-κ)) :=
    integrable_one_add_norm (by simpa using hκ)
  refine (hint.const_mul (max (M * (1 + |T₀|) ^ κ) B)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  have hpos : 0 < 1 + |y| := by positivity
  by_cases hy : T₀ ≤ |y|
  · exact (hd y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · replace hy : |y| < T₀ := not_le.mp hy
    have hyI : y ∈ Icc (-|T₀|) |T₀| := abs_le.mp (hy.le.trans (le_abs_self _))
    have h1 := hM y hyI
    have hM0 : 0 ≤ M := (norm_nonneg _).trans h1
    have hge : 1 ≤ (1 + |T₀|) ^ κ * (1 + |y|) ^ (-κ) := by
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact Real.rpow_le_rpow hpos.le (by linarith [le_abs_self T₀]) (by linarith)
    calc ‖h y‖ ≤ M := h1
      _ ≤ M * ((1 + |T₀|) ^ κ * (1 + |y|) ^ (-κ)) := le_mul_of_one_le_right hM0 hge
      _ = (M * (1 + |T₀|) ^ κ) * (1 + |y|) ^ (-κ) := by ring
      _ ≤ max (M * (1 + |T₀|) ^ κ) B * (1 + |y|) ^ (-κ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

theorem vline_re (σ y : ℝ) : ((σ : ℂ) + y * I).re = σ := by simp

theorem vline_im (σ y : ℝ) : ((σ : ℂ) + y * I).im = y := by simp

/-- The horizontal side at height `c T` vanishes when `|c T| → ∞` and `g` decays on the closed
strip. -/
theorem tendsto_integral_horiz {g : ℂ → ℂ} {σ₁ σ₂ T₀ B κ : ℝ} (hσ : σ₁ ≤ σ₂) (hκ : 0 < κ)
    (hd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| → ‖g s‖ ≤ B * (1 + |s.im|) ^ (-κ))
    {c : ℝ → ℝ} (hc : Tendsto (fun T => |c T|) atTop atTop) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, g (x + c T * I)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => B * (1 + |c T|) ^ (-κ) * (σ₂ - σ₁)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => (1 + |c T|) ^ (-κ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hκ).comp (tendsto_atTop_add_const_left _ 1 hc)
    simpa using (h1.const_mul B).mul_const (σ₂ - σ₁)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hc.eventually (eventually_ge_atTop T₀)] with T hT
  have hb : ∀ x ∈ Ι σ₁ σ₂, ‖g (x + c T * I)‖ ≤ B * (1 + |c T|) ^ (-κ) := by
    intro x hx
    rw [uIoc_of_le hσ] at hx
    have := hd ((x : ℂ) + c T * I) (by rw [vline_re]; exact hx.1.le) (by rw [vline_re]; exact hx.2)
      (by rw [vline_im]; exact hT)
    rwa [vline_im] at this
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rwa [abs_of_nonneg (sub_nonneg.mpr hσ)] at this

/-- The rectangle `[σ₁, σ₂] × [−T, T]` tends to `i` times the difference of the two vertical
line integrals. -/
theorem tendsto_rectBoundaryIntegral {g : ℂ → ℂ} {σ₁ σ₂ : ℝ}
    (h₁ : Integrable fun y : ℝ => g (σ₁ + y * I)) (h₂ : Integrable fun y : ℝ => g (σ₂ + y * I))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, g (x + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, g (x + (T : ℂ) * I)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => Cvs.Zeta.rectBoundaryIntegral g (σ₁ - T * I) (σ₂ + T * I)) atTop
      (𝓝 (I * ((∫ y : ℝ, g (σ₂ + y * I)) - ∫ y : ℝ, g (σ₁ + y * I)))) := by
  have hJ₁ := intervalIntegral_tendsto_integral h₁ tendsto_neg_atTop_atBot tendsto_id
  have hJ₂ := intervalIntegral_tendsto_integral h₂ tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbot.sub htop).add (hJ₂.const_mul I)).sub (hJ₁.const_mul I)
  rw [show I * ((∫ y : ℝ, g (σ₂ + y * I)) - ∫ y : ℝ, g (σ₁ + y * I))
      = 0 - 0 + I * (∫ y : ℝ, g (σ₂ + y * I)) - I * ∫ y : ℝ, g (σ₁ + y * I) by ring]
  refine hlim.congr fun T => ?_
  have hzr : ((σ₁ : ℂ) - T * I).re = σ₁ := by simp
  have hzi : ((σ₁ : ℂ) - T * I).im = -T := by simp
  have hwr : ((σ₂ : ℂ) + T * I).re = σ₂ := by simp
  have hwi : ((σ₂ : ℂ) + T * I).im = T := by simp
  simp only [Cvs.Zeta.rectBoundaryIntegral, hzr, hzi, hwr, hwi, id]

theorem isOpen_vstrip (a b : ℝ) : IsOpen {s : ℂ | a < s.re ∧ s.re < b} :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

theorem closedRect_subset {σ₁ σ₂ δ T : ℝ} (hσ : σ₁ ≤ σ₂) (hδ : 0 < δ) :
    Cvs.Zeta.closedRect ((σ₁ : ℂ) - T * I) ((σ₂ : ℂ) + T * I)
      ⊆ {s : ℂ | σ₁ - δ < s.re ∧ s.re < σ₂ + δ} := by
  intro s hs
  have hre : s.re ∈ [[σ₁, σ₂]] := by simpa using hs.1
  rw [uIcc_of_le hσ] at hre
  exact ⟨by linarith [hre.1], by linarith [hre.2]⟩

/-! ### Two lines without a pole -/

/-- **Moving a vertical line.** Holomorphy on the open strip and decay of order `κ > 1` on the
closed strip `σ₁ ≤ Re s ≤ σ₂` move the line integral from `σ₁` to `σ₂`. -/
theorem integral_vline_eq {f : ℂ → ℂ} {σ₁ σ₂ δ κ T₀ B : ℝ} (hσ : σ₁ ≤ σ₂) (hδ : 0 < δ)
    (hκ : 1 < κ) (hf : DifferentiableOn ℂ f {s | σ₁ - δ < s.re ∧ s.re < σ₂ + δ})
    (hdec : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| → ‖f s‖ ≤ B * (1 + |s.im|) ^ (-κ)) :
    ∫ y : ℝ, f (σ₁ + y * I) = ∫ y : ℝ, f (σ₂ + y * I) := by
  have hline : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ σ₂ → Integrable fun y : ℝ => f (σ + y * I) := by
    intro σ h1 h2
    refine integrable_of_decay (T₀ := T₀) (B := B) ?_ hκ fun y hy => ?_
    · exact hf.continuousOn.comp_continuous (by fun_prop)
        fun y => ⟨by rw [vline_re]; linarith, by rw [vline_re]; linarith⟩
    · have := hdec ((σ : ℂ) + y * I) (by rw [vline_re]; exact h1) (by rw [vline_re]; exact h2)
        (by rw [vline_im]; exact hy)
      rwa [vline_im] at this
  have hlim := tendsto_rectBoundaryIntegral (hline σ₁ le_rfl hσ) (hline σ₂ hσ le_rfl)
    (tendsto_integral_horiz hσ (by linarith) hdec (c := fun T => -T)
      (by simpa using tendsto_abs_atTop_atTop))
    (tendsto_integral_horiz hσ (by linarith) hdec (c := id) tendsto_abs_atTop_atTop)
  have hzero : ∀ T : ℝ, Cvs.Zeta.rectBoundaryIntegral f (σ₁ - T * I) (σ₂ + T * I) = 0 := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((σ₁ : ℂ) - T * I) ((σ₂ : ℂ) + T * I) (hf.mono (closedRect_subset hσ hδ))
    simpa [Cvs.Zeta.rectBoundaryIntegral, smul_eq_mul] using h
  have h0 : I * ((∫ y : ℝ, f (σ₂ + y * I)) - ∫ y : ℝ, f (σ₁ + y * I)) = 0 :=
    tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)
  have := (mul_eq_zero.mp h0).resolve_left I_ne_zero
  exact (sub_eq_zero.mp this).symm

/-! ### Two lines across a simple real pole -/

/-- `φ(s)/(s − x₀)` decays one order faster than `φ` once `|Im s| ≥ 1`. -/
theorem norm_div_sub_le {φ : ℂ → ℂ} {x₀ B κ : ℝ} {s : ℂ} (h1 : 1 ≤ |s.im|)
    (hb : ‖φ s‖ ≤ B * (1 + |s.im|) ^ (-κ)) :
    ‖φ s / (s - x₀)‖ ≤ (2 * B) * (1 + |s.im|) ^ (-(κ + 1)) := by
  have hpos : 0 < 1 + |s.im| := by positivity
  have hX : 0 ≤ B * (1 + |s.im|) ^ (-κ) := (norm_nonneg _).trans hb
  have hden : (1 + |s.im|) / 2 ≤ ‖s - x₀‖ := by
    have : |s.im| ≤ ‖s - x₀‖ := by
      simpa using Complex.abs_im_le_norm (s - x₀)
    linarith
  rw [norm_div]
  calc ‖φ s‖ / ‖s - x₀‖ ≤ B * (1 + |s.im|) ^ (-κ) / ((1 + |s.im|) / 2) :=
        div_le_div₀ hX hb (by positivity) hden
    _ = (2 * B) * ((1 + |s.im|) ^ (-κ) / (1 + |s.im|)) := by field_simp
    _ = (2 * B) * (1 + |s.im|) ^ (-(κ + 1)) := by
        rw [show -(κ + 1) = -κ - 1 by ring, Real.rpow_sub_one hpos.ne']

/-- **Moving a vertical line across a simple real pole.** With `φ` holomorphic on the open
strip and decaying of any order `κ > 0`, the two line integrals of `φ(s)/(s − x₀)` differ by
`2πφ(x₀)`. -/
theorem integral_vline_sub_of_pole {φ : ℂ → ℂ} {σ₁ σ₂ x₀ δ κ T₀ B : ℝ} (h₁ : σ₁ < x₀)
    (h₂ : x₀ < σ₂) (hδ : 0 < δ) (hκ : 0 < κ)
    (hφ : DifferentiableOn ℂ φ {s | σ₁ - δ < s.re ∧ s.re < σ₂ + δ})
    (hdec : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| → ‖φ s‖ ≤ B * (1 + |s.im|) ^ (-κ)) :
    (∫ y : ℝ, φ (σ₂ + y * I) / (σ₂ + y * I - x₀))
      - ∫ y : ℝ, φ (σ₁ + y * I) / (σ₁ + y * I - x₀) = 2 * (Real.pi : ℂ) * φ x₀ := by
  have hσ : σ₁ ≤ σ₂ := by linarith
  set g : ℂ → ℂ := fun u => φ u / (u - x₀) with hg
  have hgd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → max T₀ 1 ≤ |s.im| →
      ‖g s‖ ≤ (2 * B) * (1 + |s.im|) ^ (-(κ + 1)) := fun s h1 h2 h3 =>
    norm_div_sub_le ((le_max_right _ _).trans h3) (hdec s h1 h2 ((le_max_left _ _).trans h3))
  have hline : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ σ₂ → σ ≠ x₀ → Integrable fun y : ℝ => g (σ + y * I) := by
    intro σ h1 h2 hne
    refine integrable_of_decay (T₀ := max T₀ 1) (B := 2 * B) (κ := κ + 1) ?_ (by linarith) fun y hy => ?_
    · refine (hφ.continuousOn.comp_continuous (by fun_prop)
        fun y => ⟨by rw [vline_re]; linarith, by rw [vline_re]; linarith⟩).div (by fun_prop) ?_
      intro y hy
      have : ((σ : ℂ) + y * I - x₀).re = 0 := by rw [hy]; simp
      exact hne (by simpa [sub_eq_zero] using this)
    · have := hgd ((σ : ℂ) + y * I) (by rw [vline_re]; exact h1) (by rw [vline_re]; exact h2)
        (by rw [vline_im]; exact hy)
      rwa [vline_im] at this
  have hlim := tendsto_rectBoundaryIntegral (hline σ₁ le_rfl hσ h₁.ne) (hline σ₂ hσ le_rfl h₂.ne')
    (tendsto_integral_horiz hσ (by linarith) hgd (c := fun T => -T)
      (by simpa using tendsto_abs_atTop_atTop))
    (tendsto_integral_horiz hσ (by linarith) hgd (c := id) tendsto_abs_atTop_atTop)
  have hres : ∀ᶠ T : ℝ in atTop,
      Cvs.Zeta.rectBoundaryIntegral g (σ₁ - T * I) (σ₂ + T * I) = 2 * (Real.pi : ℂ) * I * φ x₀ := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact Cvs.Zeta.rectBoundaryIntegral_div_sub_eq (ρ := (x₀ : ℂ)) (by simpa using h₁) (by simpa using h₂)
      (by simpa using hT) (by simpa using hT) (isOpen_vstrip _ _) (closedRect_subset hσ hδ) hφ
  have h0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hres.mono fun T h => h.symm))
  have hI : I * (((∫ y : ℝ, g (σ₂ + y * I)) - ∫ y : ℝ, g (σ₁ + y * I))
      - 2 * (Real.pi : ℂ) * φ x₀) = 0 := by
    rw [mul_sub, h0]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hI).resolve_left I_ne_zero)

/-! ### The von Mangoldt series on a vertical line -/

theorem norm_term_vline (σ y : ℝ) (n : ℕ) :
    ‖term (fun k => (Λ k : ℂ)) ((σ : ℂ) + y * I) n‖ = ‖term (fun k => (Λ k : ℂ)) (σ : ℂ) n‖ := by
  rw [norm_term_eq, norm_term_eq, vline_re, ofReal_re]

theorem term_vline_eq (s : ℂ) (n : ℕ) :
    term (fun k => (Λ k : ℂ)) s n = (Λ n : ℂ) * (n : ℂ) ^ (-s) :=
  term_def₀ (by simp) s n

theorem continuous_term_vline (σ : ℝ) (n : ℕ) :
    Continuous fun y : ℝ => term (fun k => (Λ k : ℂ)) ((σ : ℂ) + y * I) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using continuous_const
  · simp_rw [term_vline_eq]
    exact continuous_const.mul
      ((by fun_prop : Continuous fun y : ℝ => -((σ : ℂ) + y * I)).const_cpow
        (Or.inl (Nat.cast_ne_zero.mpr hn)))

/-- **The von Mangoldt series, integrated along `Re s = σ > 1`.** For `φ` integrable on the
line, `∫ (−ζ'/ζ)(s)φ(s) = Σ_n Λ(n) ∫ n^{−s}φ(s)`. -/
theorem integral_LSeries_vonMangoldt_vline {φ : ℂ → ℂ} {σ : ℝ} (hσ : 1 < σ)
    (hφ : Integrable fun y : ℝ => φ (σ + y * I)) :
    ∫ y : ℝ, (-deriv riemannZeta (σ + y * I) / riemannZeta (σ + y * I)) * φ (σ + y * I)
      = ∑' n : ℕ, (Λ n : ℂ) * ∫ y : ℝ, (n : ℂ) ^ (-((σ : ℂ) + y * I)) * φ (σ + y * I) := by
  set F : ℕ → ℝ → ℂ := fun n y =>
    term (fun k => (Λ k : ℂ)) ((σ : ℂ) + y * I) n * φ (σ + y * I) with hF
  have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hint : ∀ n, Integrable (F n) := fun n =>
    hφ.bdd_mul (continuous_term_vline σ n).aestronglyMeasurable
      (Eventually.of_forall fun y => le_of_eq (norm_term_vline σ y n))
  have hsum : Summable fun n => ∫ y : ℝ, ‖F n y‖ := by
    have : ∀ n, ∫ y : ℝ, ‖F n y‖
        = ‖term (fun k => (Λ k : ℂ)) (σ : ℂ) n‖ * ∫ y : ℝ, ‖φ (σ + y * I)‖ := by
      intro n
      simp_rw [hF, norm_mul, norm_term_vline]
      exact integral_const_mul _ _
    simp_rw [this]
    exact (Cvs.Zeta.summable_norm_term_vonMangoldt hσ').mul_right _
  have hpt : ∀ y : ℝ, ∑' n, F n y
      = (-deriv riemannZeta (σ + y * I) / riemannZeta (σ + y * I)) * φ (σ + y * I) := by
    intro y
    have hre : 1 < ((σ : ℂ) + y * I).re := by rw [vline_re]; exact hσ
    rw [hF, tsum_mul_right, ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre]
    rfl
  rw [← integral_congr_ae (Eventually.of_forall hpt),
    ← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun n => ?_
  simp_rw [hF, term_vline_eq, mul_assoc]
  exact integral_const_mul _ _

end Cvs.Zeta.VerticalLineShift
