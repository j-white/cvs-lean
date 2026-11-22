import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The offset kernel, and what dominates it

The kernel `gaussKernel lam a w = e^{-λ(w-a)²}` and its real part at a zero, in closed form;
the two regimes that make the construction work — the on-line row, where every summand is
positive, and the far field, where the contribution is forgotten; and the majorants that make
the sum converge at all.
-/

open Complex Real

namespace Cvs.Zeta.GaussKernel.AdmissibleKernel

/-- The packet as a kernel in the `w` variable: `exp(-λ(w∓a)²)`, whose
`ofCritical` image is `gaussPacket`. -/
noncomputable def gaussKernel (lam a : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(lam : ℂ) * (w - (a : ℂ)) ^ 2)
    + Complex.exp (-(lam : ℂ) * (w + (a : ℂ)) ^ 2)

/-- The real part of one Gaussian summand at `w = γ - iδ`, in closed form. -/
theorem re_gaussKernel_summand (lam a γ δ : ℝ) :
    (Complex.exp (-(lam : ℂ) * (((γ : ℂ) - (δ : ℂ) * Complex.I) - (a : ℂ)) ^ 2)).re
      = Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2)) * Real.cos (2 * lam * (γ - a) * δ) := by
  rw [Complex.exp_re]
  refine congrArg₂ (· * ·) (congrArg Real.exp ?_) (congrArg Real.cos ?_)
  · simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  · simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring

/-- **The kernel at an off-line point.** Writing `w = γ - iδ`, `Re (gaussKernel λ a w) = e^{λ(δ² -
(γ-a)²)} cos(2λ(γ-a)δ) + e^{λ(δ² - (γ+a)²)} cos(2λ(γ+a)δ)`. -/
theorem re_gaussKernel (lam a γ δ : ℝ) :
    (gaussKernel lam a ((γ : ℂ) - (δ : ℂ) * Complex.I)).re
      = Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2)) * Real.cos (2 * lam * (γ - a) * δ)
        + Real.exp (lam * (δ ^ 2 - (γ + a) ^ 2)) * Real.cos (2 * lam * (γ + a) * δ) := by
  unfold gaussKernel
  rw [Complex.add_re, re_gaussKernel_summand]
  congr 1
  have hrw : ((γ : ℂ) - (δ : ℂ) * Complex.I) + (a : ℂ)
      = ((γ : ℂ) - (δ : ℂ) * Complex.I) - ((-a : ℝ) : ℂ) := by push_cast; ring
  rw [hrw, re_gaussKernel_summand]
  congr 2 <;> ring

/-- **The phase is achievable, at arbitrarily large width.** For any nonzero `u` and `δ` and any
threshold `M`, some `λ > M` makes `cos(2λuδ) = -1`. -/
theorem exists_lam_cos_eq_neg_one {u δ : ℝ} (hu : u ≠ 0) (hδ : δ ≠ 0) (M : ℝ) :
    ∃ lam : ℝ, M < lam ∧ 0 < lam ∧ Real.cos (2 * lam * u * δ) = -1 := by
  have hne : (2 : ℝ) * u * δ ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨by norm_num, hu⟩, hδ⟩
  have hθ : 0 < |2 * u * δ| := abs_pos.mpr hne
  obtain ⟨k, hk⟩ := exists_nat_gt (max M 0 * |2 * u * δ| / (2 * Real.pi))
  refine ⟨(Real.pi + 2 * Real.pi * k) / |2 * u * δ|, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hθ]
    rw [div_lt_iff₀ (by positivity)] at hk
    nlinarith [Real.pi_pos, le_max_left M (0 : ℝ), le_max_right M (0 : ℝ),
      mul_nonneg (le_max_right M (0 : ℝ)) hθ.le]
  · positivity
  · have hval : 2 * ((Real.pi + 2 * Real.pi * k) / |2 * u * δ|) * u * δ
        = ((Real.pi + 2 * Real.pi * k) / |2 * u * δ|) * (2 * u * δ) := by ring
    have hlampos : 0 < (Real.pi + 2 * Real.pi * k) / |2 * u * δ| := by positivity
    have habs : |2 * ((Real.pi + 2 * Real.pi * k) / |2 * u * δ|) * u * δ|
        = Real.pi + 2 * Real.pi * k := by
      rw [hval, abs_mul, abs_of_pos hlampos, div_mul_cancel₀ _ (ne_of_gt hθ)]
    calc Real.cos (2 * ((Real.pi + 2 * Real.pi * k) / |2 * u * δ|) * u * δ)
        = Real.cos |2 * ((Real.pi + 2 * Real.pi * k) / |2 * u * δ|) * u * δ| :=
          (Real.cos_abs _).symm
      _ = Real.cos (Real.pi + 2 * Real.pi * k) := by rw [habs]
      _ = -1 := by
          rw [show Real.pi + 2 * Real.pi * (k : ℝ)
                = Real.pi + (k : ℝ) * (2 * Real.pi) from by ring,
            Real.cos_add_nat_mul_two_pi, Real.cos_pi]

/-!
## The competing-zero question

Left open when the offset kernel was introduced, and settled below rather than on paper.
-/

/-! ## The on-line row, pointwise -/

/-! ## Zeros away from the offset -/

/-- `e^{lam c} → 0` along `lam → ∞` when `c < 0`.  Mathlib has no `atTop`
multiplication by a *negative* constant, so the limit is routed through negation
and `Real.tendsto_exp_atBot`. -/
theorem tendsto_exp_mul_nhds_zero {c : ℝ} (hc : c < 0) :
    Filter.Tendsto (fun lam : ℝ => Real.exp (lam * c)) Filter.atTop (nhds 0) := by
  have hc' : (0 : ℝ) < -c := by linarith
  have h := Filter.Tendsto.atTop_mul_const hc' (Filter.tendsto_id (α := ℝ))
  have hb : Filter.Tendsto (fun lam : ℝ => -(lam * -c)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atBot_iff.mpr h
  exact Real.tendsto_exp_atBot.comp (hb.congr fun lam => by ring)

/-! ## The summable majorant, and the window that survives -/

/-!
## The surviving zeros are finitely many

Mathlib proves the zeros of `riemannZeta` are a discrete set (`isDiscrete_riemannZetaZeros`),
hence finite on every compact (`IsCompact.inter_riemannZetaZeros_finite`).
-/

/-!
## The Gaussian majorant is dominated by an inverse square

The remaining hypothesis for summing over *all* zeros is a tail estimate, and that needs a
counting input, which is arithmetic and lives outside this block.
-/

/-- The estimate with every quantity free: no division, no `let`, so the atoms
stay atoms and the combination is linear. -/
private theorem gauss_weight_aux {E K γ a u : ℝ} (hEpos : 0 < E) (hE : E ≤ 1)
    (hkey : u ^ 2 * E ≤ K) (hg : γ ^ 2 ≤ 2 * u ^ 2 + 2 * a ^ 2) :
    (1 + γ ^ 2) * E ≤ 1 + 2 * a ^ 2 + 2 * K := by
  nlinarith [mul_le_mul_of_nonneg_right hg hEpos.le,
    mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * a ^ 2) (sub_nonneg.mpr hE)]

/-- `u² e^{-lam u²} ≤ 1/lam`, from `x + 1 ≤ eˣ` alone — no supremum computed. -/
theorem sq_mul_exp_neg_le {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    u ^ 2 * Real.exp (-(lam * u ^ 2)) ≤ 1 / lam := by
  have hEpos : 0 < Real.exp (-(lam * u ^ 2)) := Real.exp_pos _
  have h1 : lam * u ^ 2 + 1 ≤ Real.exp (lam * u ^ 2) := Real.add_one_le_exp _
  have h2 : Real.exp (lam * u ^ 2) * Real.exp (-(lam * u ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : (lam * u ^ 2 + 1) * Real.exp (-(lam * u ^ 2))
      ≤ Real.exp (lam * u ^ 2) * Real.exp (-(lam * u ^ 2)) :=
    mul_le_mul_of_nonneg_right h1 hEpos.le
  rw [h2] at h3
  rw [le_div_iff₀ hlam]
  nlinarith [h3, hEpos]

/-- `(1 + γ²) e^{-lam (γ - a)²} ≤ 1 + 2a² + 2/lam`. -/
theorem exp_neg_sq_mul_one_add_sq_le {lam : ℝ} (hlam : 0 < lam) (a γ : ℝ) :
    (1 + γ ^ 2) * Real.exp (-(lam * (γ - a) ^ 2)) ≤ 1 + 2 * a ^ 2 + 2 / lam := by
  have hE : Real.exp (-(lam * (γ - a) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg hlam.le (sq_nonneg (γ - a))]
  have hg : γ ^ 2 ≤ 2 * (γ - a) ^ 2 + 2 * a ^ 2 := by
    nlinarith [sq_nonneg (γ - 2 * a)]
  have h := gauss_weight_aux (E := Real.exp (-(lam * (γ - a) ^ 2))) (K := 1 / lam)
    (u := γ - a) (γ := γ) (a := a) (Real.exp_pos _) hE
    (sq_mul_exp_neg_le hlam (γ - a)) hg
  calc (1 + γ ^ 2) * Real.exp (-(lam * (γ - a) ^ 2))
      ≤ 1 + 2 * a ^ 2 + 2 * (1 / lam) := h
    _ = 1 + 2 * a ^ 2 + 2 / lam := by ring

/-- The form a comparison test consumes: the Gaussian weight at ordinate `γ` is
at most an explicit constant over `1 + γ²`. -/
theorem exp_neg_sq_le_const_div {lam : ℝ} (hlam : 0 < lam) (a γ : ℝ) :
    Real.exp (-(lam * (γ - a) ^ 2)) ≤ (1 + 2 * a ^ 2 + 2 / lam) / (1 + γ ^ 2) := by
  have hpos : (0 : ℝ) < 1 + γ ^ 2 := by nlinarith [sq_nonneg γ]
  rw [le_div_iff₀ hpos, mul_comm]
  exact exp_neg_sq_mul_one_add_sq_le hlam a γ

/-- **The same weight at inverse-fourth strength.** Splitting the exponent in half and squaring
the inverse-square bound costs only a squared constant, and `(1 + γ²)² ≥ 1 + γ⁴` converts the
denominator. -/
theorem exp_neg_sq_le_const_div_quartic {lam : ℝ} (hlam : 0 < lam) (a γ : ℝ) :
    Real.exp (-(lam * (γ - a) ^ 2)) ≤ (1 + 2 * a ^ 2 + 4 / lam) ^ 2 / (1 + γ ^ 4) := by
  have hh : (0 : ℝ) < lam / 2 := by linarith
  have h := exp_neg_sq_le_const_div hh a γ
  rw [show (2 : ℝ) / (lam / 2) = 4 / lam by rw [div_div_eq_mul_div]; norm_num] at h
  have hE0 : (0 : ℝ) ≤ Real.exp (-(lam / 2 * (γ - a) ^ 2)) := (Real.exp_pos _).le
  have hsplit : Real.exp (-(lam / 2 * (γ - a) ^ 2)) ^ 2
      = Real.exp (-(lam * (γ - a) ^ 2)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hpos4 : (0 : ℝ) < 1 + γ ^ 4 := by positivity
  rw [← hsplit]
  refine (pow_le_pow_left₀ hE0 h 2).trans ?_
  rw [div_pow, div_le_div_iff₀ (by positivity) hpos4]
  nlinarith [mul_nonneg (sq_nonneg (1 + 2 * a ^ 2 + 4 / lam)) (sq_nonneg γ)]

/-!
## Summability, with the arithmetic input isolated

The zero side of the explicit formula is a `tsum`, and a `tsum` over a non-summable family is
`0` by convention — so a *negativity* statement about it is worthless until summability is
known.
-/

end Cvs.Zeta.GaussKernel.AdmissibleKernel
