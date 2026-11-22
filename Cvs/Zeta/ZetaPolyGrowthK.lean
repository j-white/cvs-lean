import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.ZetaGrowth
import Cvs.Zeta.ZetaInterior
import Cvs.Zeta.ZetaPolyGrowth
import Cvs.Zeta.ZetaStrip

/-!
# Rung 7, parameterised by the strip width

`Cvs.Zeta.ZetaPolyGrowth` proves polynomial growth of `ζ` on `[-1/2, 3/2]`, with the strip, the
denominator `(s+3)²` and the Phragmén–Lindelöf constant `c = 1` all hardcoded.
-/

open Complex Real Filter Asymptotics Set

namespace Cvs.Zeta

/-- The auxiliary function for the strip `[1/2 - k, 3/2]`.  The shift `k+2` is chosen so
that `Re (s + (k+2)) ≥ 5/2` uniformly in `k` on that strip. -/
noncomputable def zetaAuxK (k : ℕ) (s : ℂ) : ℂ := riemannZeta₁ s / (s + (k + 2)) ^ (k + 1)

/-- **The denominator estimate, linear rather than squared.** On `Re s ≥ 1/2 - k` the shifted
point satisfies `‖s + (k+2)‖ ≥ (1 + |Im s|)/2`. -/
theorem norm_add_shift_ge (k : ℕ) {s : ℂ} (h : (1 / 2 : ℝ) - k ≤ s.re) :
    (1 + |s.im|) / 2 ≤ ‖s + (k + 2)‖ := by
  have hre : (s + (k + 2 : ℕ)).re = s.re + (k + 2) := by push_cast; simp
  have him : (s + (k + 2 : ℕ)).im = s.im := by push_cast; simp
  have h1 : (5 : ℝ) / 2 ≤ ‖s + (k + 2)‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    push_cast at hre ⊢
    rw [hre]
    rw [abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k])]
    linarith
  have h2 : |s.im| ≤ ‖s + (k + 2)‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    push_cast at him ⊢
    rw [him]
  rcases le_or_gt |s.im| 4 with hc | hc
  · linarith
  · linarith

theorem differentiableAt_zetaAuxK (k : ℕ) {z : ℂ} (hz : -((k : ℝ) + 1) < z.re) :
    DifferentiableAt ℂ (zetaAuxK k) z := by
  have hne : z + ((k : ℂ) + 2) ≠ 0 := by
    intro h
    have hre : (z + ((k : ℂ) + 2)).re = 0 := by rw [h]; simp
    simp at hre
    linarith
  exact DifferentiableAt.fun_div (differentiable_riemannZeta₁ z)
    ((differentiableAt_id.add_const _).fun_pow (k + 1)) (pow_ne_zero _ hne)

theorem diffContOnCl_zetaAuxK (k : ℕ) :
    DiffContOnCl ℂ (zetaAuxK k) (Complex.re ⁻¹' Ioo ((1 / 2 : ℝ) - k) (3 / 2)) := by
  have hlt : ((1 / 2 : ℝ) - k) ≠ 3 / 2 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    intro hc; linarith
  have hsub : closure (Complex.re ⁻¹' Ioo ((1 / 2 : ℝ) - k) (3 / 2))
      ⊆ Complex.re ⁻¹' Icc ((1 / 2 : ℝ) - k) (3 / 2) := by
    refine subset_trans (Continuous.closure_preimage_subset Complex.continuous_re _) ?_
    rw [closure_Ioo hlt]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · exact (differentiableAt_zetaAuxK k
      (by have := hz.1; simp at this ⊢; linarith)).differentiableWithinAt
  · exact (differentiableAt_zetaAuxK k
      (by have := (hsub hz).1; simp at this ⊢; linarith)).continuousAt.continuousWithinAt

theorem norm_sub_one_le_K (k : ℕ) {s : ℂ} (h1 : (1 / 2 : ℝ) - k ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    ‖s - 1‖ ≤ ((k : ℝ) + 2) * (1 + |s.im|) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (s - 1).re = s.re - 1 := by simp
  have him : (s - 1).im = s.im := by simp
  rw [hre, him]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : |s.re - 1| ≤ (k : ℝ) + 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith [abs_nonneg s.im]

/-- The quotient is bounded by a constant whenever `ζ` obeys a degree-`k` bound. -/
theorem norm_zetaAuxK_le {k : ℕ} {s : ℂ} (hs : s ≠ 1) (hre : (1 / 2 : ℝ) - k ≤ s.re)
    {D : ℝ} (hD : ‖riemannZeta s‖ ≤ D * (1 + |s.im|) ^ k) (hD0 : 0 ≤ D)
    (hup : ‖s - 1‖ ≤ ((k : ℝ) + 2) * (1 + |s.im|)) :
    ‖zetaAuxK k s‖ ≤ ((k : ℝ) + 2) * D * 2 ^ (k + 1) := by
  have hu : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hden := norm_add_shift_ge k hre
  have hpos : (0 : ℝ) < ((1 + |s.im|) / 2) ^ (k + 1) := by positivity
  have hdenpow : ((1 + |s.im|) / 2) ^ (k + 1) ≤ ‖s + ((k : ℂ) + 2)‖ ^ (k + 1) := by
    refine pow_le_pow_left₀ (by positivity) ?_ _
    exact_mod_cast hden
  have hnum : ‖riemannZeta₁ s‖ ≤ ((k : ℝ) + 2) * D * (1 + |s.im|) ^ (k + 1) := by
    rw [riemannZeta₁_eq_mul hs, norm_mul]
    calc ‖s - 1‖ * ‖riemannZeta s‖
        ≤ (((k : ℝ) + 2) * (1 + |s.im|)) * (D * (1 + |s.im|) ^ k) :=
          mul_le_mul hup hD (norm_nonneg _) (by positivity)
      _ = ((k : ℝ) + 2) * D * (1 + |s.im|) ^ (k + 1) := by ring
  rw [zetaAuxK, norm_div, norm_pow, div_le_iff₀ (lt_of_lt_of_le hpos hdenpow)]
  refine hnum.trans ?_
  have hstep : ((k : ℝ) + 2) * D * (1 + |s.im|) ^ (k + 1)
      = (((k : ℝ) + 2) * D * 2 ^ (k + 1)) * ((1 + |s.im|) / 2) ^ (k + 1) := by
    rw [div_pow]
    field_simp
  rw [hstep]
  refine mul_le_mul_of_nonneg_left hdenpow (by positivity)

/-- Both edges of the strip `[1/2 - k, 3/2]` give a constant bound. -/
theorem exists_edge_bound_K (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ s : ℂ, s.re = (1 / 2 : ℝ) - k → ‖zetaAuxK k s‖ ≤ C)
      ∧ ∀ s : ℂ, s.re = 3 / 2 → ‖zetaAuxK k s‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_riemannZeta_left_edge k hk
  set Z : ℝ := ∑' n : ℕ, ‖LSeries.term 1 ((3 / 2 : ℝ) : ℂ) n‖ with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => norm_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set D : ℝ := max (C₁ * (1 + (k : ℝ)) ^ k) Z with hDdef
  have hD0 : 0 ≤ D := le_trans (by positivity) (le_max_left _ _)
  refine ⟨((k : ℝ) + 2) * D * 2 ^ (k + 1), by positivity, ?_, ?_⟩
  · intro s hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs; linarith
    have hform : s = (1 / 2 : ℂ) - (k : ℕ) + (s.im : ℝ) * I := by
      refine Complex.ext ?_ ?_
      · simp [hs]
      · simp
    have hz : ‖riemannZeta s‖ ≤ D * (1 + |s.im|) ^ k := by
      have h := hC₁ s.im
      rw [← hform] at h
      refine h.trans ?_
      have hstep : (1 + |s.im| + (k : ℝ)) ^ k ≤ ((1 + (k : ℝ)) * (1 + |s.im|)) ^ k := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        nlinarith [abs_nonneg s.im]
      calc C₁ * (1 + |s.im| + (k : ℝ)) ^ k
          ≤ C₁ * ((1 + (k : ℝ)) * (1 + |s.im|)) ^ k := by gcongr
        _ = (C₁ * (1 + (k : ℝ)) ^ k) * (1 + |s.im|) ^ k := by rw [mul_pow]; ring
        _ ≤ D * (1 + |s.im|) ^ k := by
            gcongr
            exact le_max_left _ _
    exact norm_zetaAuxK_le hs1 (by rw [hs]) hz hD0
      (norm_sub_one_le_K k (by rw [hs]) (by rw [hs]; linarith))
  · intro s hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs; linarith
    have hz : ‖riemannZeta s‖ ≤ D * (1 + |s.im|) ^ k := by
      have h := norm_riemannZeta_le_of_re_le (σ₀ := 3 / 2) (by norm_num) (le_of_eq hs.symm)
      have h1 : (1 : ℝ) ≤ (1 + |s.im|) ^ k := one_le_pow₀ (by linarith [abs_nonneg s.im])
      have h2 : Z ≤ D := le_max_right _ _
      nlinarith [hZ0, norm_nonneg (riemannZeta s)]
    exact norm_zetaAuxK_le hs1 (by rw [hs]; linarith) hz hD0
      (norm_sub_one_le_K k (by rw [hs]; linarith) (by rw [hs]))

/-- The Phragmén–Lindelöf growth hypothesis, with `c` scaled to the strip width. -/
theorem zetaAuxK_growth (k : ℕ) :
    ∃ c < π / (3 / 2 - ((1 / 2 : ℝ) - k)), ∃ B : ℝ,
      zetaAuxK k =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
          𝓟 (Complex.re ⁻¹' Ioo ((1 / 2 : ℝ) - k) (3 / 2))]
        fun z : ℂ => Real.exp (B * Real.exp (c * |z.im|)) := by
  obtain ⟨Ci, hCi0, hCi⟩ :=
    exists_norm_riemannZeta_le_exp (a := (1 / 2 : ℝ) - k) (b := 3 / 2) (by norm_num)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hw : (3 / 2 - ((1 / 2 : ℝ) - k)) = 1 + k := by ring
  have hwpos : (0 : ℝ) < 1 + k := by linarith
  refine ⟨1 / (1 + k), ?_, π * (1 + k) / 2, ?_⟩
  · rw [hw]
    gcongr
    linarith [Real.pi_gt_three]
  refine Asymptotics.IsBigO.of_bound (((k : ℝ) + 2) * Ci * 2 ^ (k + 1)) ?_
  have h1 : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop, (1 : ℝ) ≤ |z.im| :=
    Filter.Eventually.comap (Filter.eventually_ge_atTop (1 : ℝ)) _
  have h2 : ∀ᶠ z : ℂ in 𝓟 (Complex.re ⁻¹' Ioo ((1 / 2 : ℝ) - k) (3 / 2)),
      z.re ∈ Ioo ((1 / 2 : ℝ) - k) (3 / 2) := Filter.eventually_principal.mpr fun _ hz => hz
  filter_upwards [h1.filter_mono inf_le_left, h2.filter_mono inf_le_right] with z hz1 hz2
  have hu : (0 : ℝ) ≤ |z.im| := abs_nonneg _
  have hzne : z ≠ 1 := by intro h; rw [h] at hz1; norm_num at hz1
  set E : ℝ := Ci * Real.exp (π * |z.im| / 2) with hE
  have hE0 : 0 ≤ E := by positivity
  have hzeta : ‖riemannZeta z‖ ≤ E * (1 + |z.im|) ^ k := by
    have h := hCi z hz2.1.le hz2.2.le hz1
    have h1' : (1 : ℝ) ≤ (1 + |z.im|) ^ k := one_le_pow₀ (by linarith)
    nlinarith [hE0]
  have hmain := norm_zetaAuxK_le hzne hz2.1.le hzeta hE0
    (norm_sub_one_le_K k hz2.1.le hz2.2.le)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hstep : Real.exp (π * |z.im| / 2)
      ≤ Real.exp (π * (1 + k) / 2 * Real.exp (1 / (1 + k) * |z.im|)) := by
    refine Real.exp_le_exp.mpr ?_
    have he : 1 + 1 / (1 + k) * |z.im| ≤ Real.exp (1 / (1 + k) * |z.im|) := by
      linarith [Real.add_one_le_exp (1 / (1 + k) * |z.im|)]
    have hpp : (0 : ℝ) < π := Real.pi_pos
    have hkey : π * (1 + k) / 2 * (1 + 1 / (1 + k) * |z.im|)
        = π * (1 + k) / 2 + π * |z.im| / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ π * (1 + k) / 2)]
  have hA : (0 : ℝ) ≤ ((k : ℝ) + 2) * Ci * 2 ^ (k + 1) := by positivity
  calc ‖zetaAuxK k z‖ ≤ ((k : ℝ) + 2) * E * 2 ^ (k + 1) := hmain
    _ = (((k : ℝ) + 2) * Ci * 2 ^ (k + 1)) * Real.exp (π * |z.im| / 2) := by rw [hE]; ring
    _ ≤ (((k : ℝ) + 2) * Ci * 2 ^ (k + 1))
        * Real.exp (π * (1 + k) / 2 * Real.exp (1 / (1 + k) * |z.im|)) :=
        mul_le_mul_of_nonneg_left hstep hA

/-- **Rung 7, parameterised.**  `ζ₁` has polynomial growth of degree `k+1` on the strip
`[1/2 − k, 3/2]`, for every `k ≥ 1`. -/
theorem exists_norm_riemannZeta₁_le_pow (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (1 / 2 : ℝ) - k ≤ s.re → s.re ≤ 3 / 2 →
      ‖riemannZeta₁ s‖ ≤ C * (1 + |s.im|) ^ (k + 1) := by
  obtain ⟨Ce, hCe0, hleft, hright⟩ := exists_edge_bound_K k hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨Ce * ((k : ℝ) + 7 / 2) ^ (k + 1), by positivity, fun s h1 h2 => ?_⟩
  have hpl : ‖zetaAuxK k s‖ ≤ Ce :=
    PhragmenLindelof.vertical_strip (diffContOnCl_zetaAuxK k) (zetaAuxK_growth k)
      hleft hright h1 h2
  have hne : s + ((k : ℂ) + 2) ≠ 0 := by
    intro h
    have hre : (s + ((k : ℂ) + 2)).re = 0 := by rw [h]; simp
    simp at hre
    linarith
  have hzeta : riemannZeta₁ s = zetaAuxK k s * (s + ((k : ℂ) + 2)) ^ (k + 1) := by
    rw [zetaAuxK, div_mul_cancel₀ _ (pow_ne_zero _ hne)]
  have hu : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hup : ‖s + ((k : ℂ) + 2)‖ ≤ ((k : ℝ) + 7 / 2) * (1 + |s.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : (s + ((k : ℂ) + 2)).re = s.re + (k + 2) := by simp
    have him : (s + ((k : ℂ) + 2)).im = s.im := by simp
    rw [hre, him, abs_of_nonneg (by linarith : (0:ℝ) ≤ s.re + (k + 2))]
    nlinarith
  rw [hzeta, norm_mul, norm_pow]
  have hpow : ‖s + ((k : ℂ) + 2)‖ ^ (k + 1)
      ≤ (((k : ℝ) + 7 / 2) * (1 + |s.im|)) ^ (k + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hup _
  calc ‖zetaAuxK k s‖ * ‖s + ((k : ℂ) + 2)‖ ^ (k + 1)
      ≤ Ce * (((k : ℝ) + 7 / 2) * (1 + |s.im|)) ^ (k + 1) := by
        refine mul_le_mul hpl hpow (by positivity) hCe0
    _ = Ce * ((k : ℝ) + 7 / 2) ^ (k + 1) * (1 + |s.im|) ^ (k + 1) := by rw [mul_pow]; ring

/-- **`ζ` polynomially bounded on the half-plane `Re s ≥ 1/2 − k`**, for every `k ≥ 1`.
This is what the Landau disc at height `T` needs, with `k` chosen from its radius. -/
theorem exists_norm_riemannZeta_le_pow_of_re_ge (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (1 / 2 : ℝ) - k ≤ s.re → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (k + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta₁_le_pow k hk
  set Z : ℝ := ∑' n : ℕ, ‖LSeries.term 1 ((3 / 2 : ℝ) : ℂ) n‖ with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨max C Z, le_trans hC0 (le_max_left _ _), fun s h1 h3 => ?_⟩
  have hu : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hsq : (1 : ℝ) ≤ (1 + |s.im|) ^ (k + 1) := one_le_pow₀ (by linarith)
  rcases le_or_gt s.re (3 / 2) with h2 | h2
  · have hs1 : s ≠ 1 := by intro h; rw [h] at h3; norm_num at h3
    have hlow : (1 : ℝ) ≤ ‖s - 1‖ := by
      refine le_trans h3 ?_
      simpa using Complex.abs_im_le_norm (s - 1)
    have hz : ‖riemannZeta₁ s‖ = ‖s - 1‖ * ‖riemannZeta s‖ := by
      rw [riemannZeta₁_eq_mul hs1, norm_mul]
    have hb := hC s h1 h2
    rw [hz] at hb
    have hmax : C ≤ max C Z := le_max_left _ _
    nlinarith [norm_nonneg (riemannZeta s), hb, hlow, hsq]
  · have hz : ‖riemannZeta s‖ ≤ Z :=
      norm_riemannZeta_le_of_re_le (σ₀ := 3 / 2) (by norm_num) h2.le
    have hmax : Z ≤ max C Z := le_max_right _ _
    nlinarith [hZ0, hsq]

end Cvs.Zeta
