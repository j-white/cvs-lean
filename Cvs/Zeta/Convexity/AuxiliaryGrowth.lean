import Mathlib
import Cvs.Zeta.Convexity.CompletedZetaStripBound
import Cvs.Zeta.Convexity.GammaInverseBound
import Cvs.Zeta.ConvexityAuxDifferentiable
import Cvs.Zeta.ConvexityEvenBranch
import Cvs.Zeta.ConvexityPhragmenLindelof
import Cvs.Zeta.ConvexityScaleComparison
import Cvs.Zeta.ConvexityZetaEdges
import Cvs.Zeta.ExplicitFormula.SquaredKernelFormula

/-!
# The growth hypothesis for `ζ₀`'s auxiliary, discharged
-/

open Complex

namespace Cvs.ZetaGrowth

/-- `e^{Au}` is beaten by `e^{e^{eu}}` once `u ≥ 2A/e²` — the same quadratic step
as.rpow_le_exp_exp`, with a linear exponent in place of a logarithmic one. -/
theorem exp_le_exp_exp {A e u : ℝ} (hA : 0 ≤ A) (he : 0 < e) (hu : 0 < u)
    (hu2 : 2 * A / e ^ 2 ≤ u) :
    Real.exp (A * u) ≤ Real.exp (Real.exp (e * u)) := by
  refine Real.exp_le_exp.mpr ?_
  have hq : (e * u) ^ 2 / 2 ≤ Real.exp (e * u) :=
    Cvs.Zeta.SquaredKernel.sq_half_le_exp (by positivity)
  have hkey : A * u ≤ (e * u) ^ 2 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < e ^ 2)] at hu2
    nlinarith [hu, sq_nonneg (e * u)]
  linarith

/-- **The growth hypothesis of `vertical_strip`, from an exponential bound.** needed a polynomial;
`GammaInverseBound` only gives an exponential, and an exponential is still far below `exp(B·exp(e|t|))`. -/
theorem isBigO_expexp_of_exp {g : ℂ → ℂ} {M A α β : ℝ}
    (hαβ : α < β) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hb : ∀ z : ℂ, z ∈ Cvs.Zeta.ConvexityAuxDifferentiable.strip α β → 1 ≤ |z.im| → ‖g z‖ ≤ M * Real.exp (A * |z.im|)) :
    ∃ e < Real.pi / (β - α), ∃ B,
      g =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop
        ⊓ Filter.principal (Cvs.Zeta.ConvexityAuxDifferentiable.strip α β)]
        fun z : ℂ => Real.exp (B * Real.exp (e * |z.im|)) := by
  have hβα : (0 : ℝ) < β - α := by linarith
  set e : ℝ := Real.pi / (2 * (β - α)) with he
  have hepos : 0 < e := by rw [he]; positivity
  have helt : e < Real.pi / (β - α) := by
    rw [he, div_lt_div_iff₀ (by positivity) hβα]
    nlinarith [Real.pi_pos, hβα]
  refine ⟨e, helt, 1, ?_⟩
  refine Asymptotics.IsBigO.of_bound M ?_
  have hcomap : ∀ᶠ z : ℂ in Filter.comap (fun z : ℂ => |z.im|) Filter.atTop,
      max 1 (2 * A / e ^ 2) ≤ |z.im| :=
    Filter.Eventually.comap (Filter.eventually_ge_atTop _) _
  have hprin : ∀ᶠ z : ℂ in Filter.principal (Cvs.Zeta.ConvexityAuxDifferentiable.strip α β), z ∈ Cvs.Zeta.ConvexityAuxDifferentiable.strip α β :=
    Filter.eventually_principal.mpr (fun _ hz => hz)
  filter_upwards [hcomap.filter_mono inf_le_left, hprin.filter_mono inf_le_right] with z hz hzs
  have hone : (1 : ℝ) ≤ |z.im| := le_trans (le_max_left _ _) hz
  have hu : (0 : ℝ) < |z.im| := lt_of_lt_of_le zero_lt_one hone
  have hu2 : 2 * A / e ^ 2 ≤ |z.im| := le_trans (le_max_right _ _) hz
  have hstep : Real.exp (A * |z.im|) ≤ Real.exp (Real.exp (e * |z.im|)) :=
    exp_le_exp_exp hA hepos hu hu2
  have hnorm : ‖Real.exp (1 * Real.exp (e * |z.im|))‖ = Real.exp (Real.exp (e * |z.im|)) := by
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hnorm]
  calc ‖g z‖ ≤ M * Real.exp (A * |z.im|) := hb z hzs hone
    _ ≤ M * Real.exp (Real.exp (e * |z.im|)) := mul_le_mul_of_nonneg_left hstep hM

/-- **The damping never helps the growth.** Off the real axis `‖K-(s+c)²‖ ≥ (Im s)² ≥ 1`, so the
real part of the even branch is nonnegative and the `-(a'+b'σ)` factor makes that term
nonpositive; the remaining `b'·t·Im(evenLog)` is bounded by `ConvexityEvenBranch`. -/
theorem norm_aux_le_of_ge_one {f : ℂ → ℂ} {c K a' b' β : ℝ}
    (hK : (β + c) ^ 2 < K) {s : ℂ} (hc : 0 ≤ s.re + c) (hβ : s.re ≤ β)
    (him : 1 ≤ |s.im|) (hp : 0 ≤ a' + b' * s.re) :
    ‖Cvs.Zeta.ConvexityAuxDifferentiable.aux f c K a' b' s‖ ≤ ‖f s‖ * Real.exp (|b'| * (Real.pi * (β + c) / 2)) := by
  rw [Cvs.ArchScore.norm_aux_even]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hw : s.im ^ 2 ≤ ‖(K : ℂ) - (s + (c : ℂ)) ^ 2‖ := Cvs.ArchScore.norm_ge_sq hK hc hβ
  have hsq : (1 : ℝ) ≤ s.im ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg s.im]
  have h1 : (1 : ℝ) ≤ ‖(K : ℂ) - (s + (c : ℂ)) ^ 2‖ := by linarith
  have hLre : 0 ≤ (Cvs.ArchScore.evenLog c K s).re := by
    rw [Cvs.ArchScore.evenLog_re]
    have := Real.log_nonneg h1
    linarith
  have hIm := Cvs.ArchScore.abs_im_mul_im_evenLog_le hK hc hβ
  have hb : b' * s.im * (Cvs.ArchScore.evenLog c K s).im ≤ |b'| * (Real.pi * (β + c) / 2) := by
    have hstep : b' * (s.im * (Cvs.ArchScore.evenLog c K s).im)
        ≤ |b'| * |s.im * (Cvs.ArchScore.evenLog c K s).im| := by
      refine le_trans (le_abs_self _) (le_of_eq (abs_mul _ _))
    have hstep2 : |b'| * |s.im * (Cvs.ArchScore.evenLog c K s).im|
        ≤ |b'| * (Real.pi * (β + c) / 2) := mul_le_mul_of_nonneg_left hIm (abs_nonneg b')
    have hassoc : b' * s.im * (Cvs.ArchScore.evenLog c K s).im
        = b' * (s.im * (Cvs.ArchScore.evenLog c K s).im) := by ring
    rw [hassoc]; linarith
  have h0 : 0 ≤ (a' + b' * s.re) * (Cvs.ArchScore.evenLog c K s).re := mul_nonneg hp hLre
  have heq : -(a' + b' * s.re) * (Cvs.ArchScore.evenLog c K s).re
      = -((a' + b' * s.re) * (Cvs.ArchScore.evenLog c K s).re) := by ring
  rw [heq]
  linarith

/-! ### The instantiation for `ζ₀` -/

theorem zetaStripConst_nonneg : 0 ≤ Cvs.ZetaGrowth.zetaStripConst := by
  rw [Cvs.ZetaGrowth.zetaStripConst]
  have h : ∀ γ : ℝ, 0 ≤ ∫ t in Set.Ioi (0 : ℝ),
      t ^ (γ - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖ := by
    intro γ
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (norm_nonneg _)
  have h1 := h (-1/4)
  have h2 := h (3/4)
  norm_num at h1 h2 ⊢
  linarith

/-- The strip constant for `ζ`, with the height factored out. -/
noncomputable def zetaStripC : ℝ :=
  (Cvs.ZetaGrowth.zetaStripConst / 2 + 2)
    * (Real.pi ^ (3/4 : ℝ) * ((Real.Gamma (1/4) + Real.Gamma (5/4)) / Real.pi))

theorem zetaStripC_nonneg : 0 ≤ zetaStripC := by
  have h := zetaStripConst_nonneg
  have hG1 : 0 < Real.Gamma (1/4 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hG2 : 0 < Real.Gamma (5/4 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  rw [zetaStripC]
  positivity

theorem norm_zeta_exp {s : ℂ} (h1 : -1/2 ≤ s.re) (h2 : s.re ≤ 3/2) (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ zetaStripC * Real.exp (Real.pi / 2 * |s.im|) := by
  have h := Cvs.ZetaGrowth.norm_zeta_strip_le h1 h2 him
  have harg : Real.pi * |s.im| / 2 = Real.pi / 2 * |s.im| := by ring
  rw [harg] at h
  refine le_trans h (le_of_eq ?_)
  rw [zetaStripC]
  ring

theorem norm_zeta₀_exp {s : ℂ} (h1 : -1/2 ≤ s.re) (h2 : s.re ≤ 3/2) (him : 1 ≤ |s.im|) :
    ‖riemannZeta₀ s‖ ≤ (zetaStripC + 1) * Real.exp (Real.pi / 2 * |s.im|) := by
  have h0 := Cvs.ArchScore.norm_zeta₀_le him (norm_zeta_exp h1 h2 him)
  have hexp : (1 : ℝ) ≤ Real.exp (Real.pi / 2 * |s.im|) :=
    Real.one_le_exp (by positivity)
  have hring : (zetaStripC + 1) * Real.exp (Real.pi / 2 * |s.im|)
      = zetaStripC * Real.exp (Real.pi / 2 * |s.im|)
        + Real.exp (Real.pi / 2 * |s.im|) := by ring
  linarith

/-- **The growth hypothesis for `ζ₀`'s auxiliary, discharged.**  This is the last hypothesis of
`ConvexityPhragmenLindelof.norm_aux_le_of_edges` that had no supplier. -/
theorem growth_aux_zeta₀ :
    ∃ e < Real.pi / (3/2 - (-1/2 : ℝ)), ∃ B,
      (Cvs.Zeta.ConvexityAuxDifferentiable.aux riemannZeta₀ 1 7 (3/4) (-1/2))
        =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop
          ⊓ Filter.principal (Cvs.Zeta.ConvexityAuxDifferentiable.strip (-1/2) (3/2))]
          fun z : ℂ => Real.exp (B * Real.exp (e * |z.im|)) := by
  have hEpos : (0 : ℝ) < Real.exp (|(-1/2 : ℝ)| * (Real.pi * (3/2 + 1) / 2)) := Real.exp_pos _
  refine isBigO_expexp_of_exp (M := (zetaStripC + 1)
      * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (3/2 + 1) / 2)))
    (A := Real.pi / 2) (by norm_num) ?_ (by positivity) ?_
  · have := zetaStripC_nonneg
    positivity
  · intro z hz him
    obtain ⟨hz1, hz2⟩ := hz
    have hc : (0 : ℝ) ≤ z.re + 1 := by linarith
    have hβ : z.re ≤ 3/2 := le_of_lt hz2
    have hp : (0 : ℝ) ≤ 3/4 + (-1/2) * z.re := by linarith
    have haux := norm_aux_le_of_ge_one (f := riemannZeta₀) (c := 1) (K := 7)
      (a' := 3/4) (b' := -1/2) (β := 3/2) (by norm_num) hc hβ him hp
    have hz₀ := norm_zeta₀_exp (by linarith) hβ him
    calc ‖Cvs.Zeta.ConvexityAuxDifferentiable.aux riemannZeta₀ 1 7 (3/4) (-1/2) z‖
        ≤ ‖riemannZeta₀ z‖ * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (3/2 + 1) / 2)) := haux
      _ ≤ ((zetaStripC + 1) * Real.exp (Real.pi / 2 * |z.im|))
            * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (3/2 + 1) / 2)) := by
          exact mul_le_mul_of_nonneg_right hz₀ (le_of_lt hEpos)
      _ = ((zetaStripC + 1) * Real.exp (|(-1/2 : ℝ)| * (Real.pi * (3/2 + 1) / 2)))
            * Real.exp (Real.pi / 2 * |z.im|) := by ring

end Cvs.ZetaGrowth
