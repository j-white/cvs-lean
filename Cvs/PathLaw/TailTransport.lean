/-
Transporting the rapid-decay tails to `ℓ²(ℤ)` (campaign stage 6).

The project's DTFT is `fourierBasisV.repr.symm`, where `fourierBasisV`
is the volume-side Fourier Hilbert basis. So the abstract tail theorem
applies directly on the volume `L²`, and the DTFT carries window spans
to window spans (`dtft_single`). Chain:

* `fourierBasisV_repr_eq` — the volume-basis coefficients are the
  Fourier coefficients;
* `superAlgebraic_window_tail_V` — the bump eigenfunction has
  super-algebraic Fourier-window tails on the volume `L²`;
* `norm_sub_starProjection_map` — isometric equivalences preserve
  projection tails onto mapped subspaces (Mathlib's
  `starProjection_map_apply`);
* `map_sectionSpaceC` — the DTFT maps the `ℓ²` window span onto the
  Fourier window span;
* `superAlgebraic_sectionSpaceC_tail` — **the DTFT preimage of the
  bump eigenfunction has super-algebraic `ℓ²(ℤ)` window-section
  tails.**
-/
import Cvs.PathLaw.GevreyTail
import Cvs.PathLaw.SpectrumTransport

open MeasureTheory Real Submodule AddCircle
open scoped ContDiff

namespace Cvs.PathLaw

local notation "𝕋₁" => AddCircle (1 : ℝ)
local notation "L2V" => Lp ℂ 2 (volume : Measure 𝕋₁)

/-- Isometric equivalences preserve projection tails onto mapped
subspaces. -/
theorem norm_sub_starProjection_map {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (e : E ≃ₗᵢ[𝕜] F) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    [(K.map (e.toLinearEquiv : E →ₗ[𝕜] F)).HasOrthogonalProjection]
    (x : E) :
    ‖e x - (K.map (e.toLinearEquiv : E →ₗ[𝕜] F)).starProjection (e x)‖
      = ‖x - K.starProjection x‖ := by
  rw [starProjection_map_apply, e.symm_apply_apply, ← e.map_sub,
    e.norm_map]

/-- `starProjection` is a congruence in the subspace. -/
theorem starProjection_congr {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K₁ K₂ : Submodule 𝕜 E} (h : K₁ = K₂)
    [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection] (x : E) :
    K₁.starProjection x = K₂.starProjection x := by
  subst h
  rfl

/-- The volume-basis coefficients are the Fourier coefficients. -/
lemma fourierBasisV_repr_eq (f : L2V) (k : ℤ) :
    fourierBasisV.repr f k = fourierCoeff (f : 𝕋₁ → ℂ) k := by
  rw [HilbertBasis.repr_apply_apply, MeasureTheory.L2.inner_def,
    fourierCoeff, ← volume_eq_haar]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_fourierBasisV k] with z hz
  rw [hz, RCLike.inner_apply, smul_eq_mul, ← fourier_neg]
  ring

/-- The bump eigenfunction packaged in the volume `L²`. -/
noncomputable def rungFunCV (β : ℝ) (hβ : 0 < β) (L : ℕ) (j : Fin L)
    (c : ℝ → ℝ) (hcm : Measurable c) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |c r| ≤ B) : L2V :=
  MemLp.toLp (fun z : 𝕋₁ => ((rungFun β L j c z : ℝ) : ℂ))
    ((memLp_rungFun β hβ L j c hcm B hB hbd).ofReal)

/-- **The rapid-decay tail theorem on the volume `L²`.** -/
theorem superAlgebraic_window_tail_V (β : ℝ) (hβ : 0 < β)
    (j : Fin (capacity 1 β)) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hsupp : tsupport b ⊆ Set.Ioo (0 : ℝ)
      (1 - ((capacity 1 β : ℝ) - 1) * β))
    (hbm : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |b r| ≤ B) :
    SuperAlgebraicDecay fun N =>
      ‖rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd
        - (basisWindow fourierBasisV N).starProjection
            (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd)‖ := by
  apply superAlgebraicDecay_basisWindow_tail
  have hae : (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd : 𝕋₁ → ℂ)
      =ᵐ[(haarAddCircle : Measure 𝕋₁)]
        fun z : 𝕋₁ => ((rungFun β (capacity 1 β) j b z : ℝ) : ℂ) := by
    rw [← volume_eq_haar]
    exact MemLp.coeFn_toLp _
  have hfun : (fun k : ℤ =>
      fourierBasisV.repr
        (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd) k)
      = fourierCoeff (fun z : 𝕋₁ =>
          ((rungFun β (capacity 1 β) j b z : ℝ) : ℂ)) := by
    funext k
    rw [fourierBasisV_repr_eq]
    exact congrFun (fourierCoeff_congr_ae hae) k
  rw [hfun]
  exact rapidFourierDecay_rungFun β hβ j b hb hsupp

/-! ### Down to `ℓ²(ℤ)` through the DTFT -/

/-- The complex window section of `ℓ²(ℤ)`. -/
noncomputable def sectionSpaceC (N : ℕ) : Submodule ℂ AtomSpaceC :=
  span ℂ ((fun k : ℤ => lp.single 2 k (1 : ℂ)) '' {k : ℤ | |k| ≤ (N : ℤ)})

instance sectionSpaceC_finiteDimensional (N : ℕ) :
    FiniteDimensional ℂ (sectionSpaceC N) := by
  apply FiniteDimensional.span_of_finite
  apply Set.Finite.image
  have hsub : {k : ℤ | |k| ≤ (N : ℤ)} ⊆ Set.Icc (-(N : ℤ)) N := fun k hk =>
    Set.mem_Icc.mpr (abs_le.mp hk)
  exact (Set.finite_Icc _ _).subset hsub

/-- The DTFT maps the `ℓ²` window span onto the Fourier window span. -/
theorem map_sectionSpaceC (N : ℕ) :
    (sectionSpaceC N).map (dtft.toLinearEquiv : AtomSpaceC →ₗ[ℂ] L2V)
      = basisWindow fourierBasisV N := by
  rw [sectionSpaceC, basisWindow, Submodule.map_span]
  congr 1
  rw [← Set.image_comp]
  refine Set.image_congr fun k _ => ?_
  exact dtft_single k

/-- **The DTFT preimage of the bump eigenfunction has super-algebraic
`ℓ²(ℤ)` window-section tails** — the tail hypothesis, on the
sequence side. -/
theorem superAlgebraic_sectionSpaceC_tail (β : ℝ) (hβ : 0 < β)
    (j : Fin (capacity 1 β)) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hsupp : tsupport b ⊆ Set.Ioo (0 : ℝ)
      (1 - ((capacity 1 β : ℝ) - 1) * β))
    (hbm : Measurable b) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ r, 0 ≤ r → r < β → |b r| ≤ B) :
    SuperAlgebraicDecay fun N =>
      ‖dtft.symm (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd)
        - (sectionSpaceC N).starProjection
            (dtft.symm (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd))‖ := by
  have h := superAlgebraic_window_tail_V β hβ j b hb hsupp hbm B hB hbd
  refine SuperAlgebraicDecay.of_le (C := 1) h (fun N => norm_nonneg _)
    (fun N => ?_)
  rw [one_mul]
  refine le_of_eq ?_
  have hinst : ((sectionSpaceC N).map
      (dtft.toLinearEquiv : AtomSpaceC →ₗ[ℂ] L2V)).HasOrthogonalProjection :=
    (map_sectionSpaceC N) ▸ inferInstance
  calc ‖dtft.symm (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd)
        - (sectionSpaceC N).starProjection
            (dtft.symm (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd))‖
      = ‖dtft (dtft.symm (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd))
          - ((sectionSpaceC N).map
              (dtft.toLinearEquiv : AtomSpaceC →ₗ[ℂ] L2V)).starProjection
                (dtft (dtft.symm
                  (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd)))‖ :=
        (norm_sub_starProjection_map dtft (sectionSpaceC N) _).symm
    _ = ‖rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd
          - (basisWindow fourierBasisV N).starProjection
              (rungFunCV β hβ (capacity 1 β) j b hbm B hB hbd)‖ := by
        rw [dtft.apply_symm_apply,
          starProjection_congr (map_sectionSpaceC N)]

end Cvs.PathLaw
