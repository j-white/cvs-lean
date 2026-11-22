import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The mirror floor

Abstractly: for contractions `K`, `W`, `Φ = −KΦ + r`, `‖r‖ ≤ ε‖Φ‖` and `‖WK(WΦ)‖ ≤ η‖Φ‖`, a part dominated by `WΦ` is
at most `‖Φ − WΦ‖ + (η + ε)‖Φ‖`; with `A² + L² = ‖Φ‖²` this gives `μ_β ‖Φ‖² ≤ L²`, `μ_β = ((√(2−β²) − β)/2)²`.
On a span `Φ = Σ aᵢψᵢ` of even rungs with `τᵢ = μᵢ√(c/2π) ≥ 1 − ε` (Cvs.Prolate.RungMirrorIdentity) and the `η` bound on `w K(wΦ)`:
`‖1_(X,∞)Φ‖ ≤ ‖1_(1,X]Φ‖ + β‖Φ‖` and `μ_β ∫_{Ioi 1} Φ² ≤ ∫₁^X Φ²`, using exact orthogonality (Cvs.Prolate.RungExactOrthogonality).
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.Upstream.CosineTransformHalfLine

namespace Cvs.L2a.MirrorFloor

/-- The floor constant `μ_β = ((√(2 − β²) − β)/2)²`. -/
def muBeta (β : ℝ) : ℝ := ((√(2 - β ^ 2) - β) / 2) ^ 2

/-- **Scalar floor**: `a² + l² = n²` and `a ≤ l + βn` with `0 ≤ β < 1` give `μ_β n² ≤ l²`. -/
theorem muBeta_mul_le {a l n β : ℝ} (ha : 0 ≤ a) (hl : 0 ≤ l) (hn : 0 ≤ n)
    (hsplit : a ^ 2 + l ^ 2 = n ^ 2) (hle : a ≤ l + β * n) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    muBeta β * n ^ 2 ≤ l ^ 2 := by
  set s := √(2 - β ^ 2) with hs_def
  have h2 : 0 ≤ 2 - β ^ 2 := by nlinarith
  have hs2 : s ^ 2 = 2 - β ^ 2 := Real.sq_sqrt h2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsβ : β < s := by nlinarith
  set m := (s - β) / 2 with hm_def
  have hm0 : 0 < m := by rw [hm_def]; linarith
  have hroot : 2 * m ^ 2 + 2 * β * m = 1 - β ^ 2 := by rw [hm_def]; nlinarith
  have hq : 0 ≤ (l - m * n) * (2 * l + 2 * m * n + 2 * β * n) := by
    have : n ^ 2 - l ^ 2 ≤ (l + β * n) ^ 2 := by
      rw [← hsplit]; nlinarith
    nlinarith
  have hlm : m * n ≤ l := by
    by_contra hcon
    replace hcon := not_le.1 hcon
    have hpos : 0 < 2 * l + 2 * m * n + 2 * β * n := by nlinarith
    nlinarith
  have hmn : 0 ≤ m * n := mul_nonneg hm0.le hn
  calc muBeta β * n ^ 2 = (m * n) ^ 2 := by rw [muBeta, ← hm_def]; ring
    _ ≤ l ^ 2 := pow_le_pow_left₀ hmn hlm 2

/-- **The mirror inequality (MF)**, abstractly: for contractions `K`, `W`, `KΦ = −Φ + r`, `‖r‖ ≤ ε‖Φ‖` and
`‖WK(WΦ)‖ ≤ η‖Φ‖`, any `A ≤ ‖WΦ‖` satisfies `A ≤ L + (η + ε)‖Φ‖` whenever `‖Φ − WΦ‖ ≤ L`. -/
theorem mirror_le {E : Type*} [SeminormedAddCommGroup E] (K W : E →+ E)
    (hK : ∀ v, ‖K v‖ ≤ ‖v‖) (hW : ∀ v, ‖W v‖ ≤ ‖v‖) {Φ r : E} {ε η A L : ℝ}
    (hΦ : K Φ = -Φ + r) (hr : ‖r‖ ≤ ε * ‖Φ‖) (hη : ‖W (K (W Φ))‖ ≤ η * ‖Φ‖)
    (hA : A ≤ ‖W Φ‖) (hL : ‖Φ - W Φ‖ ≤ L) :
    A ≤ L + (η + ε) * ‖Φ‖ := by
  have h1 : W Φ = W r - W (K Φ) := by
    rw [← map_sub]; congr 1; rw [hΦ]; abel
  have h2 : W (K Φ) = W (K (W Φ)) + W (K (Φ - W Φ)) := by
    rw [← map_add, ← map_add]; congr 2; abel
  have h3 : ‖W (K (Φ - W Φ))‖ ≤ L := (hW _).trans ((hK _).trans hL)
  have h4 : ‖W r‖ ≤ ε * ‖Φ‖ := (hW _).trans hr
  calc A ≤ ‖W Φ‖ := hA
    _ = ‖W r - (W (K (W Φ)) + W (K (Φ - W Φ)))‖ := by rw [← h2, ← h1]
    _ ≤ ‖W r‖ + (‖W (K (W Φ))‖ + ‖W (K (Φ - W Φ))‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ L + (η + ε) * ‖Φ‖ := by linarith

/-! ### The instance on `L²(1, ∞)` -/

local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))
local notation "H₁" => Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))

/-- The squared norm of an element of complex `L²(μ)` is the integral of its squared modulus. -/
theorem norm_sq_eq_integral {μ : Measure ℝ} (φ : Lp ℂ 2 μ) :
    ‖φ‖ ^ 2 = ∫ x, ‖(φ : ℝ → ℂ) x‖ ^ 2 ∂μ := by
  have h1 : (inner ℂ φ φ : ℂ) = (‖φ‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K φ
  have h2 : (inner ℂ φ φ : ℂ) = ∫ x, (inner ℂ ((φ : ℝ → ℂ) x) ((φ : ℝ → ℂ) x) : ℂ) ∂μ :=
    L2.inner_def φ φ
  have h3 : ∀ x, (inner ℂ ((φ : ℝ → ℂ) x) ((φ : ℝ → ℂ) x) : ℂ)
      = (‖(φ : ℝ → ℂ) x‖ : ℂ) ^ 2 := fun x => inner_self_eq_norm_sq_to_K _
  have : (‖φ‖ : ℂ) ^ 2 = ((∫ x, ‖(φ : ℝ → ℂ) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← h1, h2]; simp only [h3]; norm_cast
  exact_mod_cast this

/-- The squared norm of `toLp f` is `∫ ‖f‖²`. -/
theorem norm_toLp_sq {μ : Measure ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- The norm of `toLp f` is `√(∫ ‖f‖²)`. -/
theorem norm_toLp_eq {μ : Measure ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = √(∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [← norm_toLp_sq hf, Real.sqrt_sq (norm_nonneg _)]

/-- Functions equal almost everywhere on `(1, ∞)` have indicators of `Ioi 1` equal almost everywhere. -/
theorem indicator_congr {f g : ℝ → ℂ} (h : f =ᵐ[μ₁] g) :
    (Ioi (1 : ℝ)).indicator f =ᵐ[volume] (Ioi (1 : ℝ)).indicator g := by
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 h] with x hx
  by_cases hx1 : x ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem hx1, indicator_of_mem hx1, hx hx1]
  · rw [indicator_of_notMem hx1, indicator_of_notMem hx1]

/-- The cut `1_(1,∞) h` of `h ∈ L²(1, ∞)` lies in `L²(0, ∞)`. -/
theorem memLp_indicator_one {h : ℝ → ℂ} (hh : MemLp h 2 μ₁) :
    MemLp ((Ioi (1 : ℝ)).indicator h) 2 (volume.restrict (Ioi 0)) :=
  ((memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hh).restrict _

/-- The cosine transform of the cut lies in `L²(1, ∞)`. -/
theorem memLp_calK_one {c : ℝ} (hc : 0 < c) {h : ℝ → ℂ} (hh : MemLp h 2 μ₁) :
    MemLp (calK c ((Ioi (1 : ℝ)).indicator h)) 2 μ₁ :=
  (memLp_calK hc (memLp_indicator_one hh)).mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl)

/-- **The compression `K = 1_(1,∞) calK c 1_(1,∞)`** as a linear operator on `L²(1, ∞)`. -/
def Kop {c : ℝ} (hc : 0 < c) : H₁ →ₗ[ℂ] H₁ where
  toFun h := (memLp_calK_one hc (Lp.memLp h)).toLp _
  map_add' h₁ h₂ := by
    have e1 : calK c ((Ioi (1 : ℝ)).indicator (h₁ + h₂ : H₁))
        = calK c ((Ioi (1 : ℝ)).indicator (h₁ : ℝ → ℂ) + (Ioi (1 : ℝ)).indicator (h₂ : ℝ → ℂ)) := by
      refine calK_congr (ae_restrict_of_ae ?_)
      rw [← indicator_add']
      exact indicator_congr (Lp.coeFn_add h₁ h₂)
    have e2 := calK_add hc (memLp_ev (memLp_indicator_one (Lp.memLp h₁)))
      (memLp_ev (memLp_indicator_one (Lp.memLp h₂)))
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (by rw [e1]; exact ae_restrict_of_ae e2)
  map_smul' r h := by
    have e1 : calK c ((Ioi (1 : ℝ)).indicator (r • h : H₁))
        = calK c (r • (Ioi (1 : ℝ)).indicator (h : ℝ → ℂ)) := by
      refine calK_congr (ae_restrict_of_ae ?_)
      rw [show r • (Ioi (1 : ℝ)).indicator (h : ℝ → ℂ)
          = (Ioi (1 : ℝ)).indicator (r • (h : ℝ → ℂ)) from (indicator_const_smul _ r _).symm]
      exact indicator_congr (Lp.coeFn_smul r h)
    have e2 := calK_smul hc r (memLp_ev (memLp_indicator_one (Lp.memLp h)))
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (by rw [e1]; exact ae_restrict_of_ae e2)

/-- The compression `K` is a contraction on `L²(1, ∞)` (Cvs.Upstream.CosineTransformHalfLine). -/
theorem norm_Kop_le {c : ℝ} (hc : 0 < c) (h : H₁) : ‖Kop hc h‖ ≤ ‖h‖ := by
  have hsq : ‖Kop hc h‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    change ‖(memLp_calK_one hc (Lp.memLp h)).toLp _‖ ^ 2 ≤ _
    rw [norm_toLp_sq, norm_sq_eq_integral]
    exact norm_calK_indicator_le hc zero_le_one (Lp.memLp h)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- Multiplication by a measurable weight with `|w| ≤ 1` keeps `L²(1, ∞)`. -/
theorem memLp_weight {w : ℝ → ℝ} (hwm : Measurable w) (hw : ∀ x, |w x| ≤ 1) {f : ℝ → ℂ}
    (hf : MemLp f 2 μ₁) : MemLp (fun x => (w x : ℂ) * f x) 2 μ₁ :=
  hf.of_le ((Complex.measurable_ofReal.comp hwm).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw x))

/-- **Multiplication by the weight `w`** as a linear operator on `L²(1, ∞)`. -/
def Wop {w : ℝ → ℝ} (hwm : Measurable w) (hw : ∀ x, |w x| ≤ 1) : H₁ →ₗ[ℂ] H₁ where
  toFun h := (memLp_weight hwm hw (Lp.memLp h)).toLp _
  map_add' h₁ h₂ := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_add h₁ h₂] with x hx
    rw [hx, Pi.add_apply, Pi.add_apply, mul_add]
  map_smul' r h := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_smul r h] with x hx
    rw [hx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- The weight operator is a contraction. -/
theorem norm_Wop_le {w : ℝ → ℝ} (hwm : Measurable w) (hw : ∀ x, |w x| ≤ 1) (h : H₁) :
    ‖Wop hwm hw h‖ ≤ ‖h‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [(memLp_weight hwm hw (Lp.memLp h)).coeFn_toLp] with x hx
  change ‖((memLp_weight hwm hw (Lp.memLp h)).toLp _ : ℝ → ℂ) x‖ ≤ _
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw x)

/-- A real combination of real `L²` functions, cast to `ℂ`, lies in `L²`. -/
theorem memLp_span {ι : Type*} (s : Finset ι) {μ : Measure ℝ} {f : ι → ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) 2 μ) (b : ι → ℝ) :
    MemLp (fun x => ((∑ i ∈ s, b i * f i x : ℝ) : ℂ)) 2 μ :=
  ((memLp_finsetSum s fun i _ => (hf i).const_mul (b i)).ofReal)

/-- **`toLp` of a real combination** is the combination of the `toLp`s. -/
theorem toLp_span {ι : Type*} (s : Finset ι) {μ : Measure ℝ} {f : ι → ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) 2 μ) (b : ι → ℝ) :
    (memLp_span s hf b).toLp _ = ∑ i ∈ s, (b i : ℂ) • ((hf i).ofReal.toLp fun x => (f i x : ℂ)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      refine Lp.ext ?_
      filter_upwards [(memLp_span ∅ hf b).coeFn_toLp, Lp.coeFn_zero ℂ 2 μ] with x h1 h2
      rw [h1, h2, Finset.sum_empty, Pi.zero_apply, Complex.ofReal_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, ← ih, ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
      refine MemLp.toLp_congr _ _ (ae_of_all _ fun x => ?_)
      simp only [Finset.sum_insert hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring

/-- The norm of `toLp` of a real function cast to `ℂ` is `√(∫ f²)`. -/
theorem norm_toLp_ofReal {μ : Measure ℝ} {f : ℝ → ℝ} (hf : MemLp (fun x => (f x : ℂ)) 2 μ) :
    ‖hf.toLp _‖ = √(∫ x, f x ^ 2 ∂μ) := by
  rw [norm_toLp_eq]
  congr 2
  ext x
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The square of a cut is the cut of the square. -/
theorem indicator_sq (s : Set ℝ) (f : ℝ → ℝ) (x : ℝ) :
    s.indicator f x ^ 2 = s.indicator (fun x => f x ^ 2) x := by
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]; ring

/-- A rung whose angular function vanishes on `[−1, 1]` vanishes identically. -/
theorem psi_eq_zero {c : ℝ} {g : ℝ → ℝ} (h0 : ∀ s ∈ Icc (-1 : ℝ) 1, g s = 0) (ξ : ℝ) :
    psi c g ξ = 0 := by
  simp only [psi, Cvs.Prolate.SlepianCommutingRelation.kint]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
    simp [h0 s hs])]
  simp

/-- **The mirror inequality (MF) on the rung span.** For even rungs `ψᵢ = psi c gᵢ` with pairwise distinct `χᵢ`,
eigen relations `ψᵢ = μᵢgᵢ` on `[−1, 1]`, `τᵢ = μᵢ√(c/2π) ≥ 1 − ε`, a weight `0 ≤ w ≤ 1` with `w = 1` on `[X, ∞)`,
and `∫_{Ioi 1} |w K(wΦ)|² ≤ η² ∫_{Ioi 1} Φ²`: `‖1_(X,∞)Φ‖ ≤ ‖1_(1,X]Φ‖ + (η + ε)‖Φ‖_{L²(1,∞)}`. -/
theorem mirror_le_span {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X ≤ x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2) :
    √(∫ ξ in Ioi X, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ √(∫ ξ in (1 : ℝ)..X, (∑ i, a i * psi c (g i) ξ) ^ 2)
        + (η + ε) * √(∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2) := by
  classical
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ, Φ = fun ξ => ∑ i, a i * psi c (g i) ξ := ⟨_, rfl⟩
  have key : ∀ ξ, ∑ i, a i * psi c (g i) ξ = Φ ξ := fun ξ => by rw [hΦdef]
  simp only [key] at hη ⊢
  have hw : ∀ x, |w x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hw0 x], hw1 x⟩
  have hgc : ∀ i, ContinuousOn (g i) (Icc (-1 : ℝ) 1) := fun i => by
    have : ContinuousOn (g i) (uIcc (-1 : ℝ) 1) := fun s hs =>
      (hg i s hs).continuousAt.continuousWithinAt
    rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at this
  have hψ : ∀ i, MemLp (psi c (g i)) 2 μ₁ := fun i =>
    Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc
  have hM0 : ∀ i, 0 ≤ ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := fun i =>
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  obtain ⟨ψL, hψL⟩ : ∃ ψL : ι → H₁, ∀ i, ψL i = (hψ i).ofReal.toLp fun x => (psi c (g i) x : ℂ) :=
    ⟨_, fun _ => rfl⟩
  -- the mirror identity on each rung: `K ψᵢ = −τᵢ ψᵢ`
  have hKψ : ∀ i, Kop hc (ψL i) = ((-(μ i * √(c / (2 * π))) : ℝ) : ℂ) • ψL i := by
    intro i
    have hcoe : (ψL i : ℝ → ℂ) =ᵐ[μ₁] fun x => (psi c (g i) x : ℂ) := by
      rw [hψL i]; exact MemLp.coeFn_toLp _
    have hcongr : calK c ((Ioi (1 : ℝ)).indicator (ψL i : ℝ → ℂ))
        = calK c ((Ioi 1).indicator fun x => (psi c (g i) x : ℂ)) :=
      calK_congr (ae_restrict_of_ae (indicator_congr hcoe))
    refine Lp.ext ?_
    filter_upwards [(memLp_calK_one hc (Lp.memLp (ψL i))).coeFn_toLp,
      Lp.coeFn_smul ((-(μ i * √(c / (2 * π))) : ℝ) : ℂ) (ψL i), hcoe,
      Cvs.Prolate.RungMirrorIdentity.mirror_identity hc (hgc i) (heven i) (hμ i)] with y h1 h2 h3 h4
    change ((memLp_calK_one hc (Lp.memLp (ψL i))).toLp _ : ℝ → ℂ) y = _
    rw [h1, h2, Pi.smul_apply, h3, hcongr, h4, smul_eq_mul]
    push_cast; ring
  -- `Φ` and the remainder `r = Σ aᵢ(1 − τᵢ)ψᵢ` in `L²(1, ∞)`
  have hFm : MemLp (fun x => (Φ x : ℂ)) 2 μ₁ := by
    rw [hΦdef]; exact memLp_span Finset.univ hψ a
  obtain ⟨F, hFdef⟩ : ∃ F : H₁, F = hFm.toLp _ := ⟨_, rfl⟩
  have hFsum : F = ∑ i, (a i : ℂ) • ψL i := by
    simp only [hψL]
    rw [← toLp_span Finset.univ hψ a, hFdef]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => by simp [hΦdef])
  set b : ι → ℝ := fun i => a i * (1 - μ i * √(c / (2 * π))) with hb
  obtain ⟨r, hrdef⟩ : ∃ r : H₁, r = (memLp_span Finset.univ hψ b).toLp _ := ⟨_, rfl⟩
  have hrsum : r = ∑ i, (b i : ℂ) • ψL i := by
    simp only [hψL]; rw [hrdef, toLp_span Finset.univ hψ b]
  have hF2 : ‖F‖ ^ 2 = ∫ ξ in Ioi 1, Φ ξ ^ 2 := by
    rw [hFdef, norm_toLp_ofReal, Real.sq_sqrt (setIntegral_nonneg measurableSet_Ioi
      fun _ _ => sq_nonneg _)]
  have hFP : ‖F‖ ^ 2 = ∑ i, a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := by
    rw [hF2, hΦdef]
    exact Cvs.Prolate.RungExactOrthogonality.integral_span_sq a hg hg₁ hg₂c hang hc hχ
  -- step 5: `KΦ = −Φ + r`
  have hΦ : Kop hc F = -F + r := by
    rw [hFsum, hrsum, map_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hKψ, smul_smul, ← neg_smul, ← add_smul]
    congr 1
    simp only [hb]
    push_cast; ring
  -- `‖r‖ ≤ ε ‖Φ‖`
  have hr : ‖r‖ ≤ ε * ‖F‖ := by
    have hterm : ∀ i, b i ^ 2 * (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2)
        ≤ ε ^ 2 * (a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) := by
      intro i
      by_cases h0 : ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0
      · have h1 := Cvs.Prolate.RungMirrorIdentity.abs_tau_le_one hc (hgc i) (heven i) (hμ i) h0
        have hlo : 0 ≤ 1 - μ i * √(c / (2 * π)) := by linarith [(abs_le.1 h1).2]
        have hhi : 1 - μ i * √(c / (2 * π)) ≤ ε := by linarith [hτ i]
        have hsq : (1 - μ i * √(c / (2 * π))) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hlo hhi 2
        have hn : 0 ≤ a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 :=
          mul_nonneg (sq_nonneg _) (hM0 i)
        calc b i ^ 2 * (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2)
            = (1 - μ i * √(c / (2 * π))) ^ 2 * (a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) := by
              simp only [hb]; ring
          _ ≤ ε ^ 2 * (a i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) :=
              mul_le_mul_of_nonneg_right hsq hn
      · simp only [not_exists, not_and, not_not] at h0
        have hz : (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2) = 0 := by
          simp [psi_eq_zero h0]
        rw [hz]; simp
    have hr2 : ‖r‖ ^ 2 = ∑ i, b i ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2 := by
      rw [hrdef, norm_toLp_ofReal, Real.sq_sqrt (setIntegral_nonneg measurableSet_Ioi
        fun _ _ => sq_nonneg _)]
      exact Cvs.Prolate.RungExactOrthogonality.integral_span_sq b hg hg₁ hg₂c hang hc hχ
    have hsq : ‖r‖ ^ 2 ≤ (ε * ‖F‖) ^ 2 := by
      rw [hr2, mul_pow, hFP, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hterm i
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hε (norm_nonneg _))
      two_ne_zero).1 hsq
  -- the `η` bound: `‖wK(wΦ)‖ ≤ η ‖Φ‖`
  have hWF : ((Wop hwm hw F : H₁) : ℝ → ℂ) =ᵐ[μ₁] fun x => ((w x * Φ x : ℝ) : ℂ) := by
    filter_upwards [(memLp_weight hwm hw (Lp.memLp F)).coeFn_toLp, hFm.coeFn_toLp] with x h1 h2
    change ((memLp_weight hwm hw (Lp.memLp F)).toLp _ : ℝ → ℂ) x = _
    rw [h1, hFdef, h2]; push_cast; ring
  have hη' : ‖Wop hwm hw (Kop hc (Wop hwm hw F))‖ ≤ η * ‖F‖ := by
    have hcongr : calK c ((Ioi (1 : ℝ)).indicator (Wop hwm hw F : ℝ → ℂ))
        = calK c ((Ioi 1).indicator fun x => ((w x * Φ x : ℝ) : ℂ)) :=
      calK_congr (ae_restrict_of_ae (indicator_congr hWF))
    have hsq : ‖Wop hwm hw (Kop hc (Wop hwm hw F))‖ ^ 2 ≤ (η * ‖F‖) ^ 2 := by
      rw [mul_pow, hF2, norm_sq_eq_integral]
      refine le_of_eq_of_le (integral_congr_ae ?_) hη
      filter_upwards [(memLp_weight hwm hw (Lp.memLp (Kop hc (Wop hwm hw F)))).coeFn_toLp,
        (memLp_calK_one hc (Lp.memLp (Wop hwm hw F))).coeFn_toLp] with y h1 h2
      change ‖((memLp_weight hwm hw (Lp.memLp (Kop hc (Wop hwm hw F)))).toLp _ : ℝ → ℂ) y‖ ^ 2 = _
      rw [h1]
      change ‖(w y : ℂ) * ((memLp_calK_one hc (Lp.memLp (Wop hwm hw F))).toLp _ : ℝ → ℂ) y‖ ^ 2 = _
      rw [h2, hcongr]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hη0 (norm_nonneg _))
      two_ne_zero).1 hsq
  -- the high and low parts
  have hΦr : MemLp Φ 2 μ₁ := by
    rw [hΦdef]; exact memLp_finsetSum Finset.univ fun i _ => (hψ i).const_mul (a i)
  have hhim : MemLp (fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ)) 2 μ₁ :=
    (hΦr.indicator measurableSet_Ioi.nullMeasurableSet).ofReal
  have hlom : MemLp (fun x => (((Iic X).indicator Φ x : ℝ) : ℂ)) 2 μ₁ :=
    (hΦr.indicator measurableSet_Iic.nullMeasurableSet).ofReal
  have hA : ‖hhim.toLp _‖ ≤ ‖Wop hwm hw F‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hhim.coeFn_toLp, hWF] with x h1 h2
    rw [h1, h2, Complex.norm_real, Complex.norm_real]
    by_cases hx : x ∈ Ioi X
    · rw [indicator_of_mem hx, hwX x (le_of_lt hx), one_mul]
    · rw [indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
  have hL : ‖F - Wop hwm hw F‖ ≤ ‖hlom.toLp _‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hlom.coeFn_toLp, hWF, Lp.coeFn_sub F (Wop hwm hw F), hFm.coeFn_toLp]
      with x h1 h2 h3 h4
    rw [h1, h3, Pi.sub_apply, h2, hFdef, h4, Complex.norm_real, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hx : x ∈ Iic X
    · rw [indicator_of_mem hx, show Φ x - w x * Φ x = (1 - w x) * Φ x by ring, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (abs_le.2 ⟨by linarith [hw1 x], by linarith [hw0 x]⟩)
    · rw [indicator_of_notMem hx, hwX x (le_of_lt (not_le.1 hx)), one_mul, sub_self]
  have hmf := mirror_le (Kop hc).toAddMonoidHom (Wop hwm hw).toAddMonoidHom
    (norm_Kop_le hc) (norm_Wop_le hwm hw) hΦ hr hη' hA hL
  have hhi : ‖hhim.toLp _‖ = √(∫ ξ in Ioi X, Φ ξ ^ 2) := by
    rw [norm_toLp_ofReal]
    simp only [indicator_sq]
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hX]
  have hlo : ‖hlom.toLp _‖ = √(∫ ξ in (1 : ℝ)..X, Φ ξ ^ 2) := by
    rw [norm_toLp_ofReal]
    simp only [indicator_sq]
    rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, intervalIntegral.integral_of_le hX]
  have hFn : ‖F‖ = √(∫ ξ in Ioi 1, Φ ξ ^ 2) := by
    rw [← hF2, Real.sqrt_sq (norm_nonneg _)]
  rw [← hhi, ← hlo, ← hFn]
  exact hmf

/-- **The mirror floor on the rung span**: under the hypotheses of `mirror_le_span` with `η + ε < 1`,
`μ_{η+ε} ∫_{Ioi 1} Φ² ≤ ∫₁^X Φ²`. -/
theorem mirror_floor_span {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}
    (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    {ε : ℝ} (hε : 0 ≤ ε) (hτ : ∀ i, 1 - ε ≤ μ i * √(c / (2 * π)))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    {X : ℝ} (hX : 1 ≤ X) (hwX : ∀ x, X ≤ x → w x = 1)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ y in Ioi 1, ‖(w y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((w x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ η ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
    (hβ : η + ε < 1) :
    muBeta (η + ε) * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2
      ≤ ∫ ξ in (1 : ℝ)..X, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
  have hmf := mirror_le_span a hg hg₁ hg₂c hang hc hχ heven hμ hε hτ hwm hw0 hw1 hX hwX hη0 hη
  set f : ℝ → ℝ := fun ξ => (∑ i, a i * psi c (g i) ξ) ^ 2 with hf
  have hΦr : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 μ₁ :=
    memLp_finsetSum Finset.univ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hint : IntegrableOn f (Ioi 1) := (memLp_two_iff_integrable_sq hΦr.aestronglyMeasurable).1 hΦr
  have hsplit : (∫ ξ in (1 : ℝ)..X, f ξ) + ∫ ξ in Ioi X, f ξ = ∫ ξ in Ioi 1, f ξ :=
    intervalIntegral.integral_interval_add_Ioi hint (hint.mono_set (Ioi_subset_Ioi hX))
  have hA0 : 0 ≤ ∫ ξ in Ioi X, f ξ := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hL0 : 0 ≤ ∫ ξ in (1 : ℝ)..X, f ξ :=
    intervalIntegral.integral_nonneg hX fun _ _ => sq_nonneg _
  have hN0 : 0 ≤ ∫ ξ in Ioi 1, f ξ := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have h := muBeta_mul_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt hA0, Real.sq_sqrt hL0, Real.sq_sqrt hN0]; linarith) hmf
    (add_nonneg hη0 hε) hβ
  rwa [Real.sq_sqrt hN0, Real.sq_sqrt hL0] at h

end Cvs.L2a.MirrorFloor
