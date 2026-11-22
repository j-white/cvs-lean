import Mathlib
import Cvs.L2a.CleanBandDilation
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.FrameFloorJumpAbsorption
import Cvs.L2a.OdeFreeFrames
import Cvs.L2a.ReflectionFloor
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
# The dilate form of `Dil`, the corner split and the assembly into `hAL`

`⟨ū, J D_m g⟩ = ⟨J D_m ū, g⟩`, so `Dil = −2Σ_m re⟨J D_m ū, 1_(m,X]Φ⟩ + 2re⟨e₁, E⟩`; a smooth partition
`w_b + w_mid + w_t = 1` on each `(m, X]` splits the sum into `Dbot + Dmid + Dtop`, and three bounds on these give `hAL`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.Upstream.CosineTransformDilation Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.FrameFloorJumpAbsorption Cvs.L2a.CleanBandDilation

namespace Cvs.L2a.DilationCornerSplit

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))
local notation "H₁" => Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))

/-! ### Lemma 2: the dilate form -/

/-- The unnormalised dilation `(D_m f)(x) = f(mx)` on `L²(0, ∞)`, `m > 0`: `m^{-1/2}` times `CosineTransformDilation`'s unitary
`dilOp`. -/
def dilU {m : ℝ} (hm : 0 < m) (f : H₀) : H₀ := (((√m)⁻¹ : ℝ) : ℂ) • dilOp hm f

/-- `dilU hm f` is `f(m ·)` almost everywhere on `(0, ∞)`. -/
theorem coeFn_dilU {m : ℝ} (hm : 0 < m) (f : H₀) :
    (dilU hm f : ℝ → ℂ) =ᵐ[μ₀] fun x => (f : ℝ → ℂ) (m * x) := by
  unfold dilU
  filter_upwards [Lp.coeFn_smul (((√m)⁻¹ : ℝ) : ℂ) (dilOp hm f), coeFn_dilOp hm f] with x h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (Real.sqrt_pos.2 hm).ne', Complex.ofReal_one, one_mul]

/-- `⟨f, D_m g⟩ = ⟨D_{1/m} f, g⟩` for the unitary dilation. -/
theorem inner_dilOp_right {m : ℝ} (hm : 0 < m) (f g : H₀) :
    inner ℂ f (dilOp hm g) = inner ℂ (dilOp (inv_pos.2 hm) f) g := by
  have hiso := (LinearMap.norm_map_iff_inner_map_map (dilOp hm)).1 (norm_dilOp hm)
  calc inner ℂ f (dilOp hm g) = inner ℂ (dilOp hm (dilOp (inv_pos.2 hm) f)) (dilOp hm g) := by
        rw [dilOp_dilOp_inv]
    _ = inner ℂ (dilOp (inv_pos.2 hm) f) g := hiso _ _

/-- **Lemma 2, the dilate form**: `⟨ū, J D_m g⟩ = ⟨J D_m ū, g⟩` (exact, not only the real part). -/
theorem inner_Uop_dilU {c m : ℝ} (hc : 0 < c) (hm : 0 < m) (f g : H₀) :
    inner ℂ f (Uop hc (dilU hm g)) = inner ℂ (Uop hc (dilU hm f)) g := by
  unfold dilU
  rw [map_smul, map_smul, inner_smul_right, inner_smul_left, Complex.conj_ofReal, ← inner_Uop,
    inner_dilOp_right, ← Uop_dilOp]

/-- `D_m` of the cut `1_(m,X]Φ` is the `m`-th term of `E`. -/
theorem dilU_cut_eq {Φ : ℝ → ℝ} (hΦ : MemLp Φ 2 μ₁) (X : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    dilU (Nat.cast_pos.2 hm) ((memLp_cut hΦ X hm).toLp _) = (memLp_dilTerm hΦ X m).toLp _ := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  refine Lp.ext ?_
  filter_upwards [coeFn_dilU hm' ((memLp_cut hΦ X hm).toLp _),
    (qmp_mul_Ioi hm').ae (memLp_cut hΦ X hm).coeFn_toLp, (memLp_dilTerm hΦ X m).coeFn_toLp]
    with θ h1 h2 h3
  rw [h1, h3, h2, dilTerm, Cvs.L2a.OdeFreeFrames.indicator_dilate hm']

/-- `re⟨J D_m ū, g⟩ = ∫_{Ioi 1} re(calK(ū(m·)))·ψ` for a real class `g = ψ` vanishing on `(0, 1]`. -/
theorem re_inner_Uop_dilU_eq {c : ℝ} (hc : 0 < c) {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hχX : ∀ x, X < x → χ x = 1) {u aF : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ)) {m : ℝ} (hm : 0 < m)
    {ψ : ℝ → ℝ} {g : H₀} (hg : (g : ℝ → ℂ) =ᵐ[μ₀] fun x => (ψ x : ℂ)) (hψ : ∀ x, x ≤ 1 → ψ x = 0) :
    RCLike.re (inner ℂ (Uop hc (dilU hm (u + aF))) g)
      = ∫ x in Ioi 1, (calK c (fun t => ((ubar Φ χ X (m * t) : ℝ) : ℂ)) x).re * ψ x := by
  have hdil : (dilU hm (u + aF) : ℝ → ℂ) =ᵐ[μ₀] fun t => ((ubar Φ χ X (m * t) : ℝ) : ℂ) :=
    (coeFn_dilU hm (u + aF)).trans ((qmp_mul_Ioi hm).ae_eq_comp (ubar_ae hX hχX hu haF))
  rw [re_inner_of_ae_left hg hψ]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one)
    (coeFn_Uop hc (dilU hm (u + aF)))] with x hx
  rw [hx, calK_congr hdil]

/-! ### The corner weights -/

/-- Multiplication by a measurable weight with `|w| ≤ 1` keeps a real class in `L²(0, ∞)`. -/
theorem memLp_weight₀ {w : ℝ → ℝ} (hwm : Measurable w) (hw : ∀ x, |w x| ≤ 1) {f : ℝ → ℝ}
    (hf : MemLp (fun x => (f x : ℂ)) 2 μ₀) : MemLp (fun x => ((w x * f x : ℝ) : ℂ)) 2 μ₀ := by
  have e : (fun x => ((w x * f x : ℝ) : ℂ)) = fun x => (w x : ℂ) * (f x : ℂ) := by
    funext x; exact Complex.ofReal_mul _ _
  rw [e]
  exact hf.of_le ((Complex.measurable_ofReal.comp hwm).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw x))

/-! ### Lemma 3: the corner split -/

/-- `−2 Σ_{2≤m≤⌊X⌋} re⟨J D_m ū, (w m) 1_(m,X]Φ⟩` as real integrals, for a family of weights `w m`. -/
def dilPart (c : ℝ) (Φ χ : ℝ → ℝ) (X : ℝ) (w : ℕ → ℝ → ℝ) : ℝ :=
  -2 * ∑ m ∈ Finset.Icc 2 ⌊X⌋₊, ∫ x in Ioi 1,
    (calK c (fun t => ((ubar Φ χ X (m * t) : ℝ) : ℂ)) x).re * (w m x * (Ioc (m : ℝ) X).indicator Φ x)

/-- **Lemma 2 summed**: `coreDil = −2 Σ_m re⟨J D_m ū, 1_(m,X]Φ⟩ + 2re⟨e₁, E⟩`. -/
theorem coreDil_eq_dilate {c : ℝ} (hc : 0 < c) {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hχX : ∀ x, X < x → χ x = 1) (hΦ : MemLp Φ 2 μ₁) {u aB aF e : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haB : (aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    coreDil c Φ χ X
      = dilPart c Φ χ X (fun _ _ => 1)
        + 2 * RCLike.re (inner ℂ (Uop hc (u + (aB + aF)) + (u + (aB + aF))) e) := by
  rw [coreDil_eq_clean hc hX hχX hu haB haF he]
  congr 1
  unfold dilPart
  congr 1
  rw [dilSum_toLp_eq hΦ he, map_sum, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := by have := (Finset.mem_Icc.1 hm).1; omega
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hg : ((memLp_cut hΦ X hm1).toLp _ : ℝ → ℂ)
      =ᵐ[μ₀] fun x => ((1 * (Ioc (m : ℝ) X).indicator Φ x : ℝ) : ℂ) :=
    (memLp_cut hΦ X hm1).coeFn_toLp.trans (ae_of_all _ fun x => by simp only [one_mul])
  rw [← dilU_cut_eq hΦ X hm1, inner_Uop_dilU hc (Nat.cast_pos.2 hm1),
    re_inner_Uop_dilU_eq hc hX hχX hu haF (Nat.cast_pos.2 hm1) hg fun x hx => by
      rw [indicator_of_notMem (fun h => by linarith [h.1]), mul_zero]]

/-! ### The assembly into `hAL` -/

end Cvs.L2a.DilationCornerSplit
