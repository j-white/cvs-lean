import Mathlib
import Cvs.L2a.MirrorFloor
import Cvs.L2a.ReflectionFloor
import Cvs.Upstream.CosineTransformHalfLine

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosine transform commutes with dilations

For `m > 0`, `calK c (h (m ·)) = m⁻¹ (calK c h)(· / m)` (`CosineTransformHalfLine`'s `calK`); with the unitary dilation
`D_m h = √m h(m ·)` on `L²(0, ∞)` this is `U D_m = D_{1/m} U` and `U D_m U = D_m*` (`ReflectionFloor`'s `Uop`).
Band transfer: `∫_A ‖calK c (h (m ·))‖² = m⁻¹ ∫_{A/m} ‖calK c h‖²`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor

namespace Cvs.Upstream.CosineTransformDilation

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

/-- **The cosine transform of a dilate**: for `m > 0`, `calK c (h (m ·)) = m⁻¹ (calK c h)(· / m)`
almost everywhere. -/
theorem calK_comp_mul {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {h : ℝ → ℂ}
    (hh : MemLp (ev h) 2 (volume : Measure ℝ)) :
    calK c (fun x => h (m * x)) =ᵐ[volume] fun y => ((m⁻¹ : ℝ) : ℂ) * calK c h (m⁻¹ * y) := by
  have ha : c / (2 * π) ≠ 0 := by positivity
  set V : Lp ℂ 2 (volume : Measure ℝ) := hh.toLp (ev h)
  have hev : ev (fun x => h (m * x)) = fun x => ev h (m * x) := by
    funext x; simp [ev, abs_mul, abs_of_pos hm]
  have hmV : MemLp (fun x => (V : ℝ → ℂ) (m * x)) 2 (volume : Measure ℝ) :=
    memLp_comp_mul (Lp.memLp V) hm.ne'
  have hhm : MemLp (ev (fun x => h (m * x))) 2 (volume : Measure ℝ) := by
    rw [hev]; exact memLp_comp_mul hh hm.ne'
  have hL : hhm.toLp _ = hmV.toLp _ := by
    refine MemLp.toLp_congr _ _ ?_
    rw [hev]
    exact ((qmp_mul hm.ne').ae_eq_comp hh.coeFn_toLp).symm
  have hF := fourier_toLp_comp_mul V hm.ne' hmV
  rw [calK_eq hhm, calK_eq hh, hL]
  filter_upwards [(qmp_mul ha).ae hF] with y hy
  rw [hy, abs_of_pos hm, show m⁻¹ * (c / (2 * π) * y) = c / (2 * π) * (m⁻¹ * y) by ring]
  ring

/-- Multiplication by `m > 0` is quasi-measure-preserving on `(0, ∞)`. -/
theorem qmp_mul_Ioi {m : ℝ} (hm : 0 < m) :
    QuasiMeasurePreserving (fun x : ℝ => m * x) μ₀ μ₀ := by
  refine ⟨(measurable_const_mul m).aemeasurable, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.restrict_apply hs] at h0
  rw [Measure.map_apply (measurable_const_mul m) hs,
    Measure.restrict_apply (measurable_const_mul m hs)]
  have hsub : (fun x : ℝ => m * x) ⁻¹' s ∩ Ioi 0 ⊆ (fun x : ℝ => m * x) ⁻¹' (s ∩ Ioi 0) :=
    fun x hx => ⟨hx.1, mul_pos hm hx.2⟩
  exact measure_mono_null hsub ((qmp_mul hm.ne').preimage_null h0)

/-- A dilate of a function in `L²(0, ∞)` is in `L²(0, ∞)`. -/
theorem memLp_comp_mul_Ioi {h : ℝ → ℂ} (hh : MemLp h 2 μ₀) {m : ℝ} (hm : 0 < m) :
    MemLp (fun x => h (m * x)) 2 μ₀ := by
  refine ((memLp_comp_mul (memLp_ev hh) hm.ne').restrict (Ioi 0)).ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact ev_of_pos h (mul_pos hm hx)

/-- **The unitary dilation** `D_m h = √m h(m ·)` on `L²(0, ∞)`, for `m > 0`. -/
def dilOp {m : ℝ} (hm : 0 < m) : H₀ →ₗ[ℂ] H₀ where
  toFun h := ((memLp_comp_mul_Ioi (Lp.memLp h) hm).const_mul ((√m : ℝ) : ℂ)).toLp _
  map_add' h₁ h₂ := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [(qmp_mul_Ioi hm).ae (Lp.coeFn_add h₁ h₂)] with x hx
    simp only [Pi.add_apply] at hx ⊢
    rw [hx, mul_add]
  map_smul' r h := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [(qmp_mul_Ioi hm).ae (Lp.coeFn_smul r h)] with x hx
    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx]; ring

/-- `dilOp hm h` is `√m h(m ·)` almost everywhere on `(0, ∞)`. -/
theorem coeFn_dilOp {m : ℝ} (hm : 0 < m) (h : H₀) :
    (dilOp hm h : ℝ → ℂ) =ᵐ[μ₀] fun x => ((√m : ℝ) : ℂ) * (h : ℝ → ℂ) (m * x) :=
  ((memLp_comp_mul_Ioi (Lp.memLp h) hm).const_mul _).coeFn_toLp

/-- `D_m D_{1/m} = 1`. -/
theorem dilOp_dilOp_inv {m : ℝ} (hm : 0 < m) (h : H₀) :
    dilOp hm (dilOp (inv_pos.2 hm) h) = h := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dilOp hm (dilOp (inv_pos.2 hm) h),
    (qmp_mul_Ioi hm).ae (coeFn_dilOp (inv_pos.2 hm) h)] with x h1 h2
  rw [h1, h2, inv_mul_cancel_left₀ hm.ne', ← mul_assoc, ← Complex.ofReal_mul, Real.sqrt_inv,
    mul_inv_cancel₀ (Real.sqrt_pos.2 hm).ne', Complex.ofReal_one, one_mul]

/-- `D_m` preserves norms. -/
theorem norm_dilOp {m : ℝ} (hm : 0 < m) (h : H₀) : ‖dilOp hm h‖ = ‖h‖ := by
  have hsq : ‖dilOp hm h‖ ^ 2 = ‖h‖ ^ 2 := by
    rw [norm_sq_eq_integral, norm_sq_eq_integral]
    calc ∫ x, ‖(dilOp hm h : ℝ → ℂ) x‖ ^ 2 ∂μ₀
        = ∫ x in Ioi 0, m * ‖(h : ℝ → ℂ) (m * x)‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_dilOp hm h] with x hx
          rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg m),
            mul_pow, Real.sq_sqrt hm.le]
      _ = ∫ x, ‖(h : ℝ → ℂ) x‖ ^ 2 ∂μ₀ := by
          rw [integral_const_mul, integral_comp_mul_left_Ioi (fun x => ‖(h : ℝ → ℂ) x‖ ^ 2) 0 hm,
            mul_zero, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- **`U D_m = D_{1/m} U`** on `L²(0, ∞)`. -/
theorem Uop_dilOp {c m : ℝ} (hc : 0 < c) (hm : 0 < m) (h : H₀) :
    Uop hc (dilOp hm h) = dilOp (inv_pos.2 hm) (Uop hc h) := by
  refine Lp.ext ?_
  have hev := memLp_ev (memLp_comp_mul_Ioi (Lp.memLp h) hm)
  have e1 : calK c (dilOp hm h : ℝ → ℂ)
      = calK c (((√m : ℝ) : ℂ) • fun x => (h : ℝ → ℂ) (m * x)) := calK_congr (coeFn_dilOp hm h)
  have hs : ((√m : ℝ) : ℂ) * ((m⁻¹ : ℝ) : ℂ) = ((√(m⁻¹) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.sqrt_inv]
    congr 1
    have h0 : √m ≠ 0 := (Real.sqrt_pos.2 hm).ne'
    rw [show m⁻¹ = (√m)⁻¹ * (√m)⁻¹ by rw [← mul_inv, Real.mul_self_sqrt hm.le], ← mul_assoc,
      mul_inv_cancel₀ h0, one_mul]
  filter_upwards [coeFn_Uop hc (dilOp hm h), ae_restrict_of_ae (calK_smul hc ((√m : ℝ) : ℂ) hev),
    ae_restrict_of_ae (calK_comp_mul hc hm (memLp_ev (Lp.memLp h))),
    coeFn_dilOp (inv_pos.2 hm) (Uop hc h),
    (qmp_mul_Ioi (inv_pos.2 hm)).ae (coeFn_Uop hc h)] with y h1 h2 h3 h4 h5
  rw [h1, e1, h2, Pi.smul_apply, smul_eq_mul, h3, h4, h5, ← mul_assoc, hs]

end Cvs.Upstream.CosineTransformDilation
