import Mathlib
import Cvs.L2a.MirrorFloor
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The reflection floor

Abstractly: for a self-adjoint contraction `K`, orthogonal `ψᵢ` with `Kψᵢ = −τᵢψᵢ`, `τᵢ ≥ 1 − ε`, `Φ ∈ span ψᵢ` and any
`D`: `|⟨Φ, D⟩|² ≤ ‖Φ‖²(‖D‖² − re⟨D, KD⟩)/(2 − ε)`, so `re⟨D, KD⟩ ≥ −ρ‖D‖²` gives `((1 − ε − ρ)/(2 − ε))‖Φ‖² ≤ ‖Φ + D‖²`.
`MirrorFloor`'s compression `Kop` of `CosineTransformHalfLine`'s `calK` is self-adjoint; on a rung span (Cvs.Prolate.RungExactOrthogonality, Cvs.Prolate.RungMirrorIdentity) with `D = posTail Φ X − Φ`
(Cvs.L2a.PositionTruncatedTail) this gives `κ ∫_{Ioi 1} Φ² ≤ ∫_{Ioi 1} (posTail Φ X)²`, `κ = (1 − ε − ρ)/(2 − ε)`, and `FrameFloorMirror`'s `hFF` (Cvs.L2a.MirrorConcentrationHalf).
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor

namespace Cvs.L2a.ReflectionFloor

/-! ### The abstract reflection floor -/

section Abstract

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The inner product of two combinations of an orthogonal family is diagonal. -/
theorem inner_sum_smul_orth {ι : Type*} [Fintype ι] {ψ : ι → E} (horth : ∀ i j, i ≠ j → ⟪ψ i, ψ j⟫ = 0)
    (b a : ι → 𝕜) :
    ⟪∑ i, b i • ψ i, ∑ j, a j • ψ j⟫ = ∑ i, (starRingEnd 𝕜) (b i) * a i * ⟪ψ i, ψ i⟫ := by
  classical
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i (fun j _ hji => by
      rw [inner_smul_left, inner_smul_right, horth i j (Ne.symm hji), mul_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h), inner_smul_left, inner_smul_right]
  ring

/-- **Pythagoras for an orthogonal family**: `‖Σ aᵢψᵢ‖² = Σ |aᵢ|²‖ψᵢ‖²`. -/
theorem norm_sum_smul_orth_sq {ι : Type*} [Fintype ι] {ψ : ι → E} (horth : ∀ i j, i ≠ j → ⟪ψ i, ψ j⟫ = 0)
    (a : ι → 𝕜) :
    ‖∑ i, a i • ψ i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 * ‖ψ i‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_sum_smul_orth horth, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.conj_mul, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_mul, RCLike.ofReal_re]

end Abstract

/-! ### The compression of `calK` to `L²(1, ∞)` is self-adjoint -/

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))
local notation "H₁" => Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))

/-- **The cosine transform** as a linear operator on `L²(0, ∞)`. -/
def Uop {c : ℝ} (hc : 0 < c) : H₀ →ₗ[ℂ] H₀ where
  toFun h := (memLp_calK hc (Lp.memLp h)).toLp _
  map_add' h₁ h₂ := by
    have e1 : calK c ((h₁ + h₂ : H₀) : ℝ → ℂ) = calK c ((h₁ : ℝ → ℂ) + (h₂ : ℝ → ℂ)) :=
      calK_congr (Lp.coeFn_add h₁ h₂)
    have e2 := calK_add hc (memLp_ev (Lp.memLp h₁)) (memLp_ev (Lp.memLp h₂))
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (by rw [e1]; exact ae_restrict_of_ae e2)
  map_smul' r h := by
    have e1 : calK c ((r • h : H₀) : ℝ → ℂ) = calK c (r • (h : ℝ → ℂ)) := calK_congr (Lp.coeFn_smul r h)
    have e2 := calK_smul hc r (memLp_ev (Lp.memLp h))
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (by rw [e1]; exact ae_restrict_of_ae e2)

/-- `Uop h` is `calK c h` almost everywhere on `(0, ∞)`. -/
theorem coeFn_Uop {c : ℝ} (hc : 0 < c) (h : H₀) : (Uop hc h : ℝ → ℂ) =ᵐ[μ₀] calK c h :=
  (memLp_calK hc (Lp.memLp h)).coeFn_toLp

/-- `Uop` preserves norms (`CosineTransformHalfLine`'s `norm_calK`). -/
theorem norm_Uop {c : ℝ} (hc : 0 < c) (h : H₀) : ‖Uop hc h‖ = ‖h‖ := by
  have hsq : ‖Uop hc h‖ ^ 2 = ‖h‖ ^ 2 := by
    change ‖(memLp_calK hc (Lp.memLp h)).toLp _‖ ^ 2 = _
    rw [norm_toLp_sq, norm_sq_eq_integral]
    exact norm_calK hc (Lp.memLp h)
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- `Uop` is an involution (`CosineTransformHalfLine`'s `calK_calK`). -/
theorem Uop_Uop {c : ℝ} (hc : 0 < c) (h : H₀) : Uop hc (Uop hc h) = h := by
  refine Lp.ext ?_
  have e : calK c (Uop hc h : ℝ → ℂ) = calK c (calK c h) := calK_congr (coeFn_Uop hc h)
  filter_upwards [coeFn_Uop hc (Uop hc h), calK_calK hc (Lp.memLp h)] with y h1 h2
  rw [h1, e, h2]

/-- **`Uop` is self-adjoint**: a norm-preserving involution preserves inner products by polarization. -/
theorem inner_Uop {c : ℝ} (hc : 0 < c) (f g : H₀) :
    inner ℂ (Uop hc f) g = inner ℂ f (Uop hc g) := by
  have hiso := (LinearMap.norm_map_iff_inner_map_map (Uop hc)).1 (norm_Uop hc)
  calc inner ℂ (Uop hc f) g = inner ℂ (Uop hc f) (Uop hc (Uop hc g)) := by rw [Uop_Uop]
    _ = inner ℂ f (Uop hc g) := hiso f (Uop hc g)

/-- The extension by zero of `h ∈ L²(1, ∞)` to `L²(0, ∞)`. -/
def ext (h : H₁) : H₀ := (memLp_indicator_one (Lp.memLp h)).toLp _

/-- `ext h` is the cut `1_(1,∞) h` almost everywhere on `(0, ∞)`. -/
theorem coeFn_ext (h : H₁) : (ext h : ℝ → ℂ) =ᵐ[μ₀] (Ioi (1 : ℝ)).indicator h :=
  (memLp_indicator_one (Lp.memLp h)).coeFn_toLp

/-- `Kop h` is `calK c (1_(1,∞) h)` almost everywhere on `(1, ∞)`. -/
theorem coeFn_Kop {c : ℝ} (hc : 0 < c) (h : H₁) :
    (Kop hc h : ℝ → ℂ) =ᵐ[μ₁] calK c ((Ioi (1 : ℝ)).indicator h) :=
  (memLp_calK_one hc (Lp.memLp h)).coeFn_toLp

/-- `calK c (ext h) = calK c (1_(1,∞) h)`. -/
theorem calK_ext {c : ℝ} (h : H₁) : calK c (ext h : ℝ → ℂ) = calK c ((Ioi (1 : ℝ)).indicator h) :=
  calK_congr (coeFn_ext h)

/-- An integral over `(0, ∞)` of a cut to `(1, ∞)` is the integral over `(1, ∞)`. -/
theorem integral_Ioi_zero_indicator (φ : ℝ → ℂ) :
    ∫ x in Ioi 0, (Ioi (1 : ℝ)).indicator φ x = ∫ x in Ioi 1, φ x := by
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- `⟨Kop h, k⟩ = ⟨Uop (ext h), ext k⟩`. -/
theorem inner_Kop_left {c : ℝ} (hc : 0 < c) (h k : H₁) :
    inner ℂ (Kop hc h) k = inner ℂ (Uop hc (ext h)) (ext k) := by
  rw [L2.inner_def, L2.inner_def]
  calc ∫ x, inner ℂ ((Kop hc h : ℝ → ℂ) x) ((k : ℝ → ℂ) x) ∂μ₁
      = ∫ x in Ioi 1, inner ℂ (calK c ((Ioi (1 : ℝ)).indicator h) x) ((k : ℝ → ℂ) x) :=
        integral_congr_ae (by filter_upwards [coeFn_Kop hc h] with x hx; rw [hx])
    _ = ∫ x in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun x => inner ℂ (calK c ((Ioi (1 : ℝ)).indicator h) x) ((k : ℝ → ℂ) x)) x :=
        (integral_Ioi_zero_indicator _).symm
    _ = ∫ x, inner ℂ ((Uop hc (ext h) : ℝ → ℂ) x) ((ext k : ℝ → ℂ) x) ∂μ₀ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_Uop hc (ext h), coeFn_ext k] with x h1 h2
        rw [h1, h2, calK_ext]
        by_cases hx : x ∈ Ioi (1 : ℝ)
        · rw [indicator_of_mem hx, indicator_of_mem hx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, inner_zero_right]

/-- `⟨h, Kop k⟩ = ⟨ext h, Uop (ext k)⟩`. -/
theorem inner_Kop_right {c : ℝ} (hc : 0 < c) (h k : H₁) :
    inner ℂ h (Kop hc k) = inner ℂ (ext h) (Uop hc (ext k)) := by
  rw [← inner_conj_symm, inner_Kop_left hc k h, inner_conj_symm]

/-! ### The reflection floor on the rung span -/

end Cvs.L2a.ReflectionFloor
