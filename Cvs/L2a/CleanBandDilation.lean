import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.FrameFloorJumpAbsorption
import Cvs.L2a.MirrorFloor
import Cvs.L2a.MirrorSplitDefect
import Cvs.L2a.ReflectionFloor
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Upstream.CosineTransformDilation
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The clean-band form of `Dil` and the `e₁` term

`Dil = −2re⟨ū, JE⟩ + 2re⟨e₁, E⟩` with `ū = h − a_B`, `e₁ = Jh + h`, `Je₁ = e₁`; on the rung span
`∫_{Ioi 1}|e₁|² = Σ aᵢ²(1 − τᵢ)²Mᵢ ≤ ε²P`, `‖D_m(1_(m,X]Φ)‖ = m^{-1/2}‖1_(m,X]Φ‖`, `|2re⟨e₁, E⟩| ≤ 2ε(Σ m^{-1/2})P`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.Upstream.CosineTransformDilation Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.FrameFloorJumpAbsorption

namespace Cvs.L2a.CleanBandDilation

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))
local notation "H₁" => Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))

/-! ### Lemma 0 and the clean-band form of `Dil` -/

/-- `a_F = 1_(X,∞)Φ` is orthogonal to `E`, which is supported in `(1, X/2]`. -/
theorem re_inner_aF_dilSum {Φ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) {aF e : H₀}
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    RCLike.re (inner ℂ aF e) = 0 := by
  rw [re_inner_of_ae haF he fun x hx => indicator_of_notMem (fun h => not_lt.2 hx (lt_of_le_of_lt hX h)) _]
  refine (setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_).trans (integral_zero _ _)
  by_cases hx : X < x
  · rw [dilSum_of_gt (by linarith) hx, mul_zero]
  · rw [indicator_of_notMem (show x ∉ Ioi X from hx), zero_mul]

/-- **Lemma 1, the clean-band form of `Dil`**: `coreDil = −2re⟨ū, JE⟩ + 2re⟨e₁, E⟩`, `ū = u + a_F = h − a_B`,
`h = u + a_B + a_F`, `e₁ = Jh + h`. -/
theorem coreDil_eq_clean {c : ℝ} (hc : 0 < c) {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hχX : ∀ x, X < x → χ x = 1) {u aB aF e : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haB : (aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    coreDil c Φ χ X
      = -2 * RCLike.re (inner ℂ (u + aF) (Uop hc e))
        + 2 * RCLike.re (inner ℂ (Uop hc (u + (aB + aF)) + (u + (aB + aF))) e) := by
  rw [← coreDil_eq hc hX hχX hu haB haF he]
  have h1 : inner ℂ (u + aB + Uop hc aB) e = inner ℂ (u + aB) e + inner ℂ aB (Uop hc e) := by
    rw [inner_add_left, inner_Uop]
  have h2 : inner ℂ (Uop hc (u + (aB + aF)) + (u + (aB + aF))) e
      = inner ℂ (u + (aB + aF)) (Uop hc e) + inner ℂ (u + (aB + aF)) e := by
    rw [inner_add_left, inner_Uop]
  have h3 : inner ℂ (u + aF) (Uop hc e) = inner ℂ (u + (aB + aF)) (Uop hc e) - inner ℂ aB (Uop hc e) := by
    simp only [inner_add_left]; ring
  have h4 : inner ℂ (u + (aB + aF)) e = inner ℂ (u + aB) e + inner ℂ aF e := by
    simp only [inner_add_left]; ring
  have h5 := re_inner_aF_dilSum hX haF he
  rw [h1, h2, h3, h4]
  simp only [map_add, map_sub]
  rw [h5]
  ring

/-- `ū = (1 − 1_(1,X]χ) 1_(1,∞)Φ` as a function. -/
def ubar (Φ χ : ℝ → ℝ) (X x : ℝ) : ℝ :=
  (Ioi 1).indicator Φ x - (Ioc 1 X).indicator (fun x => χ x * Φ x) x

/-- `ū = 1_(1,∞)(1 − χ)Φ + 1_(X,∞)Φ` pointwise, with `χ = 1` beyond `X ≥ 1`. -/
theorem ubar_eq {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hχX : ∀ x, X < x → χ x = 1) (x : ℝ) :
    ubar Φ χ X x = (Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x + (Ioi X).indicator Φ x := by
  have h1 := edge_split (Φ := Φ) hχX x
  have h2 := arm_split (Φ := Φ) (χ := fun _ => 1) hX (fun _ _ => rfl) x
  simp only [one_mul] at h2
  unfold ubar
  linarith

/-- `ū` vanishes on `(0, 1]`. -/
theorem ubar_of_le_one {Φ χ : ℝ → ℝ} {X x : ℝ} (hx : x ≤ 1) : ubar Φ χ X x = 0 := by
  unfold ubar
  rw [indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from fun h => not_lt.2 hx h),
    indicator_of_notMem (show x ∉ Ioc 1 X from fun h => not_lt.2 hx h.1), sub_zero]

/-- The class of `u + a_F` is `ū`. -/
theorem ubar_ae {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hχX : ∀ x, X < x → χ x = 1) {u aF : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ)) :
    ((u + aF : H₀) : ℝ → ℂ) =ᵐ[μ₀] fun x => ((ubar Φ χ X x : ℝ) : ℂ) := by
  filter_upwards [Lp.coeFn_add u aF, hu, haF] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, ← Complex.ofReal_add, ubar_eq hX hχX]

/-- `re⟨f, g⟩ = ∫_{Ioi 1} (re f)·ψ` for a real class `g = ψ` vanishing on `(0, 1]`. -/
theorem re_inner_of_ae_left {f g : H₀} {ψ : ℝ → ℝ} (hg : (g : ℝ → ℂ) =ᵐ[μ₀] fun x => (ψ x : ℂ))
    (hψ : ∀ x, x ≤ 1 → ψ x = 0) :
    RCLike.re (inner ℂ f g) = ∫ x in Ioi 1, ((f : ℝ → ℂ) x).re * ψ x := by
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
  have h : ∫ x, RCLike.re (inner ℂ ((f : ℝ → ℂ) x) ((g : ℝ → ℂ) x)) ∂μ₀
      = ∫ x in Ioi 0, ((f : ℝ → ℂ) x).re * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx, RCLike.inner_apply']
    simp
  rw [h]
  exact integral_Ioi_zero_eq fun x hx => by rw [hψ x hx, mul_zero]

/-- `re⟨f, g⟩ = ∫_{Ioi 1} φ·(re g)` for a real class `f = φ` vanishing on `(0, 1]`. -/
theorem re_inner_of_ae_right {f g : H₀} {φ : ℝ → ℝ} (hf : (f : ℝ → ℂ) =ᵐ[μ₀] fun x => (φ x : ℂ))
    (hφ : ∀ x, x ≤ 1 → φ x = 0) :
    RCLike.re (inner ℂ f g) = ∫ x in Ioi 1, φ x * ((g : ℝ → ℂ) x).re := by
  rw [inner_re_symm, re_inner_of_ae_left hf hφ]
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

/-- The class of `Jh + h` for `h = 1_(1,∞)Φ` is `eOne c Φ`. -/
theorem eOne_ae_of_ae {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ} {h : H₀}
    (hh : (h : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator Φ x : ℝ) : ℂ)) :
    ((Uop hc h + h : H₀) : ℝ → ℂ) =ᵐ[μ₀] eOne c Φ := by
  have hh' : (h : ℝ → ℂ) =ᵐ[μ₀] (Ioi 1).indicator fun x => (Φ x : ℂ) :=
    hh.trans (ae_of_all _ fun x => ofReal_indicator _ _ x)
  filter_upwards [Lp.coeFn_add (Uop hc h) h, coeFn_Uop hc h, hh'] with y h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, calK_congr hh']
  rfl

/-! ### Prop A: the `e₁` term on the rung span -/

/-- **Prop A (i)**: `∫_{Ioi 1} |e₁|² = Σ aᵢ²(1 − τᵢ)² Mᵢ`, with `τᵢ = μᵢ√(c/2π)` and `Mᵢ = ∫_{Ioi 1} ψᵢ²`. -/
theorem integral_norm_eOne_sq_Ioi_one {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s) :
    ∫ y in Ioi 1, ‖eOne c (fun ξ => ∑ i, a i * psi c (g i) ξ) y‖ ^ 2
      = ∑ i, (a i * (1 - μ i * √(c / (2 * π)))) ^ 2 * ∫ x in Ioi 1, psi c (g i) x ^ 2 := by
  have hgc : ∀ i, ContinuousOn (g i) (Icc (-1 : ℝ) 1) := fun i => by
    have : ContinuousOn (g i) (uIcc (-1 : ℝ) 1) := fun s hs =>
      (hg i s hs).continuousAt.continuousWithinAt
    rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at this
  have h : ∫ y in Ioi 1, ‖eOne c (fun ξ => ∑ i, a i * psi c (g i) ξ) y‖ ^ 2
      = ∫ y in Ioi 1, (∑ i, a i * (1 - μ i * √(c / (2 * π))) * psi c (g i) y) ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [eOne_high a hc hgc heven hμ] with y hy
    rw [hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h]
  exact Cvs.Prolate.RungExactOrthogonality.integral_span_sq (fun i => a i * (1 - μ i * √(c / (2 * π)))) hg hg₁ hg₂c hang
    hc hχ

/-- **Prop A (ii)**: with `1 − ε ≤ τᵢ`, `0 ≤ ε`: `∫_{Ioi 1} |e₁|² ≤ ε² P`, `P = ∫_{Ioi 1} Φ²`. -/
theorem integral_norm_eOne_sq_Ioi_one_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ}
    {χ μ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i, 1 - ε ≤ μ i * √(c / (2 * π))) :
    ∫ y in Ioi 1, ‖eOne c (fun ξ => ∑ i, a i * psi c (g i) ξ) y‖ ^ 2
      ≤ ε ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  obtain ⟨ψL, -, -, -, -, hKψ, -, hψn, -⟩ := rung_span_L2 a hg hg₁ hg₂c hang hc hχ heven hμ
  rw [integral_norm_eOne_sq_Ioi_one a hg hg₁ hg₂c hang hc hχ heven hμ,
    Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hM : 0 ≤ ∫ x in Ioi 1, psi c (g i) x ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  rcases hM.eq_or_lt with hM0 | hM0
  · rw [← hM0]; simp
  · have hp : 0 < ‖ψL i‖ := by
      have h2 := hψn i
      nlinarith [norm_nonneg (ψL i)]
    have hK := norm_Kop_le hc (ψL i)
    rw [hKψ i, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg] at hK
    have hτ1 : |μ i * √(c / (2 * π))| ≤ 1 := le_of_mul_le_mul_right (by linarith) hp
    have h1 : (1 - μ i * √(c / (2 * π))) ^ 2 ≤ ε ^ 2 := by
      have := hτ i
      have := (abs_le.1 hτ1).2
      nlinarith
    calc (a i * (1 - μ i * √(c / (2 * π)))) ^ 2 * ∫ x in Ioi 1, psi c (g i) x ^ 2
        = (1 - μ i * √(c / (2 * π))) ^ 2 * (a i ^ 2 * ∫ x in Ioi 1, psi c (g i) x ^ 2) := by ring
      _ ≤ ε ^ 2 * (a i ^ 2 * ∫ x in Ioi 1, psi c (g i) x ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg (sq_nonneg _) hM)

/-! ### The dilate norm identity and `‖E‖` -/

/-- The `m`-th term of `dilSum`: `1_(1,X/m](θ) Φ(mθ)`. -/
def dilTerm (Φ : ℝ → ℝ) (X : ℝ) (m : ℕ) (θ : ℝ) : ℝ := (Ioc 1 (X / m)).indicator (fun θ => Φ (m * θ)) θ

/-- `dilSum` is the sum of its terms. -/
theorem dilSum_eq_sum_dilTerm (Φ : ℝ → ℝ) (X θ : ℝ) :
    dilSum Φ X θ = ∑ m ∈ Finset.Icc 2 ⌊X⌋₊, dilTerm Φ X m θ := rfl

/-- Each term of `E` lies in `L²(0, ∞)` for `Φ ∈ L²(1, ∞)`. -/
theorem memLp_dilTerm {Φ : ℝ → ℝ} (hΦ : MemLp Φ 2 μ₁) (X : ℝ) (m : ℕ) :
    MemLp (fun θ => ((dilTerm Φ X m θ : ℝ) : ℂ)) 2 μ₀ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have e : (fun θ => ((dilTerm Φ X 0 θ : ℝ) : ℂ)) = 0 := by
      funext θ
      simp [dilTerm]
    rw [e]; exact MemLp.zero
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hΦ0 : MemLp ((Ioi (1 : ℝ)).indicator Φ) 2 μ₀ :=
      ((memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hΦ).restrict _
    have h := (memLp_comp_mul_Ioi hΦ0.ofReal (m := (m : ℝ)) (by linarith)).indicator
      (measurableSet_Ioc (a := 1) (b := X / m)).nullMeasurableSet
    have e : (fun θ => ((dilTerm Φ X m θ : ℝ) : ℂ))
        = (Ioc 1 (X / m)).indicator fun x => (((Ioi 1).indicator Φ (m * x) : ℝ) : ℂ) := by
      funext x
      by_cases hx : x ∈ Ioc 1 (X / m)
      · have hmx : (m : ℝ) * x ∈ Ioi (1 : ℝ) := show (1 : ℝ) < m * x by nlinarith [hx.1]
        rw [dilTerm, indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hmx]
      · rw [dilTerm, indicator_of_notMem hx, indicator_of_notMem hx, Complex.ofReal_zero]
    rw [e]; exact h

/-- The cut `1_(m,X]Φ` lies in `L²(0, ∞)` for `Φ ∈ L²(1, ∞)` and `m ≥ 1`. -/
theorem memLp_cut {Φ : ℝ → ℝ} (hΦ : MemLp Φ 2 μ₁) (X : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    MemLp (fun x => (((Ioc (m : ℝ) X).indicator Φ x : ℝ) : ℂ)) 2 μ₀ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h : MemLp Φ 2 (volume.restrict (Ioc (m : ℝ) X)) :=
    hΦ.mono_measure (Measure.restrict_mono (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hm1)) le_rfl)
  exact (((memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 h).restrict _).ofReal

/-- The class of `E` is the sum of the classes of its terms. -/
theorem dilSum_toLp_eq {Φ : ℝ → ℝ} (hΦ : MemLp Φ 2 μ₁) {X : ℝ} {e : H₀}
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    e = ∑ m ∈ Finset.Icc 2 ⌊X⌋₊, (memLp_dilTerm hΦ X m).toLp _ := by
  refine Lp.ext ?_
  filter_upwards [he, Lp.coeFn_fun_finsetSum (Finset.Icc 2 ⌊X⌋₊) fun m => (memLp_dilTerm hΦ X m).toLp _,
    ae_all_iff.2 fun m => (memLp_dilTerm hΦ X m).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, dilSum_eq_sum_dilTerm, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun m _ => (h3 m).symm

/-- `|re⟨f, e⟩| ≤ ‖f‖_{L²(1,∞)} ‖e‖` when `e` vanishes on `(0, 1]`. -/
theorem abs_re_inner_le_of_ae_zero {f e : H₀} (he0 : ∀ᵐ x ∂μ₀, x ≤ 1 → (e : ℝ → ℂ) x = 0) :
    |RCLike.re (inner ℂ f e)| ≤ √(∫ y in Ioi 1, ‖(f : ℝ → ℂ) y‖ ^ 2) * ‖e‖ := by
  have hf' := (Lp.memLp f).indicator (measurableSet_Ioi (a := (1 : ℝ))).nullMeasurableSet
  have hinner : inner ℂ (hf'.toLp _) e = inner ℂ f e := by
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf'.coeFn_toLp, he0] with x h1 h2
    rw [h1]
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hx]
    · simp [indicator_of_notMem hx, h2 (not_lt.1 hx)]
  have hn : ‖hf'.toLp _‖ = √(∫ y in Ioi 1, ‖(f : ℝ → ℂ) y‖ ^ 2) := by
    rw [norm_toLp_eq]
    congr 1
    calc ∫ x in Ioi 0, ‖(Ioi (1 : ℝ)).indicator (f : ℝ → ℂ) x‖ ^ 2
        = ∫ x in Ioi 0, (Ioi (1 : ℝ)).indicator (fun x => ‖(f : ℝ → ℂ) x‖ ^ 2) x := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          dsimp only
          by_cases hx : x ∈ Ioi (1 : ℝ)
          · rw [indicator_of_mem hx, indicator_of_mem hx]
          · rw [indicator_of_notMem hx, indicator_of_notMem hx, norm_zero]; ring
      _ = ∫ y in Ioi 1, ‖(f : ℝ → ℂ) y‖ ^ 2 := by
          rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]
  calc |RCLike.re (inner ℂ f e)| = |RCLike.re (inner ℂ (hf'.toLp _) e)| := by rw [hinner]
    _ ≤ ‖inner ℂ (hf'.toLp _) e‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖hf'.toLp _‖ * ‖e‖ := norm_inner_le_norm _ _
    _ = √(∫ y in Ioi 1, ‖(f : ℝ → ℂ) y‖ ^ 2) * ‖e‖ := by rw [hn]

end Cvs.L2a.CleanBandDilation
