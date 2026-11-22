/-
The Single-Atom Path Law — the real-scalar form.

`single_atom_path_lawC` (`Cvs.PathLaw.Model`) is stated over `ℂ`, the scalars of
the paper's DTFT. This file derives the real-scalar form: an operator on
`ℓ²(ℤ, ℝ)` with the Loewner matrix has the same norm, because the
complexification of a real operator preserves the operator norm — the `ℓ²`
analogue of the orthogonal splitting `‖f‖² = ‖Re f‖² + ‖Im f‖²` used in
`Cvs.PathLaw.Complexify`, and again no self-adjointness is needed.

Proved here (no `sorry`):
* `seqRe`, `seqIm`, `seqOfReal` — the real/imaginary-part maps on `ℓ²`;
* `norm_sq_seq_re_add_im` — the orthogonal splitting on `ℓ²(ℤ, ℂ)`;
* `complexifyT` with `norm_complexifyT : ‖T_ℂ‖ = ‖T‖`;
* `atomEntry_symm` — the Loewner matrix is symmetric;
* `single_atom_path_lawR` — **the Path Law over `ℝ`**.
-/
import Cvs.PathLaw.Model

open MeasureTheory Real
open scoped ENNReal

namespace Cvs.PathLaw

/-! ### Real and imaginary parts of an `ℓ²(ℤ, ℂ)` sequence -/

private lemma summable_norm_rpow (x : AtomSpaceC) :
    Summable fun i : ℤ => ‖(x : ∀ _ : ℤ, ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
  (memℓp_gen_iff (by norm_num)).mp (lp.memℓp x)

theorem memℓp_seqRe (x : AtomSpaceC) :
    Memℓp (fun i : ℤ => ((x : ∀ _ : ℤ, ℂ) i).re) 2 := by
  refine memℓp_gen ?_
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (summable_norm_rpow x)
  · exact Real.rpow_nonneg (norm_nonneg _) _
  · refine Real.rpow_le_rpow (norm_nonneg _) ?_ ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _

theorem memℓp_seqIm (x : AtomSpaceC) :
    Memℓp (fun i : ℤ => ((x : ∀ _ : ℤ, ℂ) i).im) 2 := by
  refine memℓp_gen ?_
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (summable_norm_rpow x)
  · exact Real.rpow_nonneg (norm_nonneg _) _
  · refine Real.rpow_le_rpow (norm_nonneg _) ?_ ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _

theorem memℓp_seqOfReal (g : AtomSpace) :
    Memℓp (fun i : ℤ => (((g : ∀ _ : ℤ, ℝ) i : ℝ) : ℂ)) 2 := by
  refine memℓp_gen ?_
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp g)
  refine h.congr fun i => ?_
  rw [Complex.norm_real]

/-- The real part of an `ℓ²(ℤ, ℂ)` sequence. -/
noncomputable def seqRe (x : AtomSpaceC) : AtomSpace :=
  ⟨fun i => ((x : ∀ _ : ℤ, ℂ) i).re, memℓp_seqRe x⟩

/-- The imaginary part. -/
noncomputable def seqIm (x : AtomSpaceC) : AtomSpace :=
  ⟨fun i => ((x : ∀ _ : ℤ, ℂ) i).im, memℓp_seqIm x⟩

/-- A real sequence viewed as a complex one. -/
noncomputable def seqOfReal (g : AtomSpace) : AtomSpaceC :=
  ⟨fun i => (((g : ∀ _ : ℤ, ℝ) i : ℝ) : ℂ), memℓp_seqOfReal g⟩

@[simp] theorem seqRe_apply (x : AtomSpaceC) (i : ℤ) :
    (seqRe x : ∀ _ : ℤ, ℝ) i = ((x : ∀ _ : ℤ, ℂ) i).re := rfl

@[simp] theorem seqIm_apply (x : AtomSpaceC) (i : ℤ) :
    (seqIm x : ∀ _ : ℤ, ℝ) i = ((x : ∀ _ : ℤ, ℂ) i).im := rfl

@[simp] theorem seqOfReal_apply (g : AtomSpace) (i : ℤ) :
    (seqOfReal g : ∀ _ : ℤ, ℂ) i = (((g : ∀ _ : ℤ, ℝ) i : ℝ) : ℂ) := rfl

/-! ### The orthogonal splitting of the `ℓ²` norm -/

private lemma norm_sq_lp (x : AtomSpaceC) :
    ‖x‖ ^ (2 : ℝ≥0∞).toReal
      = ∑' i : ℤ, ‖(x : ∀ _ : ℤ, ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
  lp.norm_rpow_eq_tsum (by norm_num) x

private lemma norm_sq_lp_real (g : AtomSpace) :
    ‖g‖ ^ (2 : ℝ≥0∞).toReal
      = ∑' i : ℤ, ‖(g : ∀ _ : ℤ, ℝ) i‖ ^ (2 : ℝ≥0∞).toReal :=
  lp.norm_rpow_eq_tsum (by norm_num) g

private lemma rpow_two (a : ℝ) : a ^ (2 : ℝ≥0∞).toReal = a ^ 2 := by
  rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The orthogonal splitting** `‖x‖² = ‖Re x‖² + ‖Im x‖²` on `ℓ²(ℤ, ℂ)`. -/
theorem norm_sq_seq_re_add_im (x : AtomSpaceC) :
    ‖x‖ ^ 2 = ‖seqRe x‖ ^ 2 + ‖seqIm x‖ ^ 2 := by
  have hre := norm_sq_lp_real (seqRe x)
  have him := norm_sq_lp_real (seqIm x)
  have hx := norm_sq_lp x
  rw [rpow_two] at hre him hx
  rw [hx, hre, him]
  have hsumre : Summable fun i : ℤ => ‖(seqRe x : ∀ _ : ℤ, ℝ) i‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by norm_num)).mp (lp.memℓp (seqRe x))
  have hsumim : Summable fun i : ℤ => ‖(seqIm x : ∀ _ : ℤ, ℝ) i‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by norm_num)).mp (lp.memℓp (seqIm x))
  rw [← Summable.tsum_add hsumre hsumim]
  refine tsum_congr fun i => ?_
  rw [rpow_two, rpow_two, rpow_two]
  rw [seqRe_apply, seqIm_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_seqRe_le (x : AtomSpaceC) : ‖seqRe x‖ ≤ ‖x‖ := by
  have h := norm_sq_seq_re_add_im x
  nlinarith [norm_nonneg (seqRe x), norm_nonneg (seqIm x), norm_nonneg x,
    sq_nonneg (‖seqIm x‖)]

theorem norm_seqIm_le (x : AtomSpaceC) : ‖seqIm x‖ ≤ ‖x‖ := by
  have h := norm_sq_seq_re_add_im x
  nlinarith [norm_nonneg (seqRe x), norm_nonneg (seqIm x), norm_nonneg x,
    sq_nonneg (‖seqRe x‖)]

theorem seqRe_seqOfReal (g : AtomSpace) : seqRe (seqOfReal g) = g := by
  apply lp.ext
  funext i
  rw [seqRe_apply, seqOfReal_apply, Complex.ofReal_re]

theorem seqIm_seqOfReal (g : AtomSpace) : seqIm (seqOfReal g) = 0 := by
  apply lp.ext
  funext i
  rw [seqIm_apply, seqOfReal_apply, Complex.ofReal_im]
  rfl

theorem norm_seqOfReal (g : AtomSpace) : ‖seqOfReal g‖ = ‖g‖ := by
  have h := norm_sq_seq_re_add_im (seqOfReal g)
  rw [seqRe_seqOfReal, seqIm_seqOfReal, norm_zero] at h
  have h2 : ‖seqOfReal g‖ ^ 2 = ‖g‖ ^ 2 := by rw [h]; ring
  nlinarith [norm_nonneg (seqOfReal g), norm_nonneg g]

/-! ### Complexification of a real operator -/

section Complexify

variable (T : AtomSpace →L[ℝ] AtomSpace)

private lemma seqRe_add (x y : AtomSpaceC) : seqRe (x + y) = seqRe x + seqRe y := by
  apply lp.ext
  funext i
  show (((x + y : AtomSpaceC) : ∀ _ : ℤ, ℂ) i).re
      = ((seqRe x + seqRe y : AtomSpace) : ∀ _ : ℤ, ℝ) i
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_add, Pi.add_apply, Complex.add_re,
    seqRe_apply, seqRe_apply]

private lemma seqIm_add (x y : AtomSpaceC) : seqIm (x + y) = seqIm x + seqIm y := by
  apply lp.ext
  funext i
  show (((x + y : AtomSpaceC) : ∀ _ : ℤ, ℂ) i).im
      = ((seqIm x + seqIm y : AtomSpace) : ∀ _ : ℤ, ℝ) i
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_add, Pi.add_apply, Complex.add_im,
    seqIm_apply, seqIm_apply]

private lemma seqRe_smul (c : ℂ) (x : AtomSpaceC) :
    seqRe (c • x) = c.re • seqRe x - c.im • seqIm x := by
  apply lp.ext
  funext i
  show (((c • x : AtomSpaceC) : ∀ _ : ℤ, ℂ) i).re
      = ((c.re • seqRe x - c.im • seqIm x : AtomSpace) : ∀ _ : ℤ, ℝ) i
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.mul_re, lp.coeFn_sub,
    Pi.sub_apply, lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply,
    seqRe_apply, seqIm_apply, smul_eq_mul, smul_eq_mul]

private lemma seqIm_smul (c : ℂ) (x : AtomSpaceC) :
    seqIm (c • x) = c.re • seqIm x + c.im • seqRe x := by
  apply lp.ext
  funext i
  show (((c • x : AtomSpaceC) : ∀ _ : ℤ, ℂ) i).im
      = ((c.re • seqIm x + c.im • seqRe x : AtomSpace) : ∀ _ : ℤ, ℝ) i
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.mul_im, lp.coeFn_add,
    Pi.add_apply, lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply,
    seqRe_apply, seqIm_apply, smul_eq_mul, smul_eq_mul]

private lemma seqOfReal_add (g h : AtomSpace) :
    seqOfReal (g + h) = seqOfReal g + seqOfReal h := by
  apply lp.ext
  funext i
  show ((((g + h : AtomSpace) : ∀ _ : ℤ, ℝ) i : ℝ) : ℂ)
      = ((seqOfReal g + seqOfReal h : AtomSpaceC) : ∀ _ : ℤ, ℂ) i
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_add, Pi.add_apply, seqOfReal_apply,
    seqOfReal_apply]
  push_cast
  ring

private lemma seqOfReal_sub (g h : AtomSpace) :
    seqOfReal (g - h) = seqOfReal g - seqOfReal h := by
  apply lp.ext
  funext i
  show ((((g - h : AtomSpace) : ∀ _ : ℤ, ℝ) i : ℝ) : ℂ)
      = ((seqOfReal g - seqOfReal h : AtomSpaceC) : ∀ _ : ℤ, ℂ) i
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sub, Pi.sub_apply, seqOfReal_apply,
    seqOfReal_apply]
  push_cast
  ring

private lemma seqOfReal_smul (r : ℝ) (g : AtomSpace) :
    seqOfReal (r • g) = ((r : ℝ) : ℂ) • seqOfReal g := by
  apply lp.ext
  funext i
  show ((((r • g : AtomSpace) : ∀ _ : ℤ, ℝ) i : ℝ) : ℂ)
      = ((((r : ℝ) : ℂ) • seqOfReal g : AtomSpaceC) : ∀ _ : ℤ, ℂ) i
  rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply, seqOfReal_apply,
    smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- The complexification of a real operator on `ℓ²(ℤ)`, as a `ℂ`-linear map. -/
noncomputable def complexifyₗ : AtomSpaceC →ₗ[ℂ] AtomSpaceC where
  toFun x := seqOfReal (T (seqRe x)) + Complex.I • seqOfReal (T (seqIm x))
  map_add' x y := by
    rw [seqRe_add, seqIm_add, map_add, map_add, seqOfReal_add, seqOfReal_add, smul_add]
    abel
  map_smul' c x := by
    simp only [RingHom.id_apply, seqRe_smul, seqIm_smul, map_sub, map_add, map_smul,
      seqOfReal_sub, seqOfReal_add, seqOfReal_smul]
    set A := seqOfReal (T (seqRe x)) with hA
    set B := seqOfReal (T (seqIm x)) with hB
    have e1 : (c : ℂ) = (c.re : ℂ) + Complex.I * (c.im : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    have e2 : c * Complex.I = Complex.I * (c.re : ℂ) - (c.im : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im c]
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (c.im : ℂ) * hI
    calc ((c.re : ℂ) • A - (c.im : ℂ) • B)
          + Complex.I • ((c.re : ℂ) • B + (c.im : ℂ) • A)
        = ((c.re : ℂ) + Complex.I * (c.im : ℂ)) • A
          + (Complex.I * (c.re : ℂ) - (c.im : ℂ)) • B := by
          rw [smul_add, smul_smul, smul_smul, add_smul, sub_smul]
          abel
      _ = c • A + (c * Complex.I) • B := by
          have hA' : ((c.re : ℂ) + Complex.I * (c.im : ℂ)) • A = c • A := by
            rw [← e1]
          have hB' : (Complex.I * (c.re : ℂ) - (c.im : ℂ)) • B
              = (c * Complex.I) • B := by
            rw [← e2]
          rw [hA', hB']
      _ = c • (A + Complex.I • B) := by rw [smul_add, smul_smul]

end Complexify

/-! ### The complexified operator and its norm -/

section Norm

variable (T : AtomSpace →L[ℝ] AtomSpace)

private lemma complexifyₗ_apply (x : AtomSpaceC) :
    complexifyₗ T x
      = seqOfReal (T (seqRe x)) + Complex.I • seqOfReal (T (seqIm x)) := rfl

private lemma seqRe_complexifyₗ (x : AtomSpaceC) :
    seqRe (complexifyₗ T x) = T (seqRe x) := by
  apply lp.ext
  funext i
  rw [complexifyₗ_apply, seqRe_apply]
  show (((seqOfReal (T (seqRe x)) + Complex.I • seqOfReal (T (seqIm x))
      : AtomSpaceC) : ∀ _ : ℤ, ℂ) i).re = _
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, seqOfReal_apply,
    seqOfReal_apply, Complex.add_re, smul_eq_mul, Complex.mul_re]
  simp

private lemma seqIm_complexifyₗ (x : AtomSpaceC) :
    seqIm (complexifyₗ T x) = T (seqIm x) := by
  apply lp.ext
  funext i
  rw [complexifyₗ_apply, seqIm_apply]
  show (((seqOfReal (T (seqRe x)) + Complex.I • seqOfReal (T (seqIm x))
      : AtomSpaceC) : ∀ _ : ℤ, ℂ) i).im = _
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, seqOfReal_apply,
    seqOfReal_apply, Complex.add_im, smul_eq_mul, Complex.mul_im]
  simp

private lemma norm_complexifyₗ_le (x : AtomSpaceC) :
    ‖complexifyₗ T x‖ ≤ ‖T‖ * ‖x‖ := by
  have hsq : ‖complexifyₗ T x‖ ^ 2
      = ‖T (seqRe x)‖ ^ 2 + ‖T (seqIm x)‖ ^ 2 := by
    rw [norm_sq_seq_re_add_im, seqRe_complexifyₗ, seqIm_complexifyₗ]
  have h1 : ‖T (seqRe x)‖ ≤ ‖T‖ * ‖seqRe x‖ := T.le_opNorm _
  have h2 : ‖T (seqIm x)‖ ≤ ‖T‖ * ‖seqIm x‖ := T.le_opNorm _
  have h3 : ‖seqRe x‖ ^ 2 + ‖seqIm x‖ ^ 2 = ‖x‖ ^ 2 :=
    (norm_sq_seq_re_add_im x).symm
  have hfin : ‖complexifyₗ T x‖ ^ 2 ≤ (‖T‖ * ‖x‖) ^ 2 := by
    rw [hsq, mul_pow, ← h3]
    nlinarith [norm_nonneg (T (seqRe x)), norm_nonneg (T (seqIm x)),
      norm_nonneg (seqRe x), norm_nonneg (seqIm x), norm_nonneg T]
  have hnn : (0 : ℝ) ≤ ‖T‖ * ‖x‖ := by positivity
  nlinarith [norm_nonneg (complexifyₗ T x)]

/-- The complexification, as a bounded operator. -/
noncomputable def complexifyT : AtomSpaceC →L[ℂ] AtomSpaceC :=
  LinearMap.mkContinuous (complexifyₗ T) ‖T‖ (norm_complexifyₗ_le T)

private lemma complexifyT_apply (x : AtomSpaceC) :
    complexifyT T x
      = seqOfReal (T (seqRe x)) + Complex.I • seqOfReal (T (seqIm x)) := rfl

/-- On real sequences the complexification acts as `T`. -/
theorem complexifyT_seqOfReal (g : AtomSpace) :
    complexifyT T (seqOfReal g) = seqOfReal (T g) := by
  rw [complexifyT_apply, seqRe_seqOfReal, seqIm_seqOfReal, map_zero]
  have h0 : seqOfReal (0 : AtomSpace) = 0 := by
    apply lp.ext
    funext i
    show (((0 : AtomSpace) : ∀ _ : ℤ, ℝ) i : ℂ) = ((0 : AtomSpaceC) : ∀ _ : ℤ, ℂ) i
    rw [lp.coeFn_zero, lp.coeFn_zero]
    simp
  rw [h0, smul_zero, add_zero]

/-- **The complexification preserves the operator norm.** -/
theorem norm_complexifyT : ‖complexifyT T‖ = ‖T‖ := by
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (norm_complexifyₗ_le T)) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
  have h1 : ‖T g‖ = ‖complexifyT T (seqOfReal g)‖ := by
    rw [complexifyT_seqOfReal, norm_seqOfReal]
  rw [h1, ← norm_seqOfReal g]
  exact (complexifyT T).le_opNorm _

end Norm

/-! ### The Path Law over `ℝ` -/

/-- The Loewner matrix is symmetric. -/
theorem atomEntry_symm (q c : ℕ) (k l : ℤ) :
    atomEntry q c k l = atomEntry q c l k := by
  unfold atomEntry
  simp only []
  by_cases hkl : k = l
  · subst hkl
    simp
  · rw [ite_eq_right hkl, ite_eq_right (Ne.symm hkl)]
    rw [show (π * ((k : ℝ) - l)) = -(π * ((l : ℝ) - k)) by ring,
      show (Real.sin (2 * π * (1 - Real.log q / Real.log c) * k)
          - Real.sin (2 * π * (1 - Real.log q / Real.log c) * l))
        = -(Real.sin (2 * π * (1 - Real.log q / Real.log c) * l)
          - Real.sin (2 * π * (1 - Real.log q / Real.log c) * k)) by ring,
      neg_div_neg_eq]

private lemma seqRe_single (k : ℤ) :
    seqRe (lp.single 2 k (1 : ℂ)) = lp.single 2 k (1 : ℝ) := by
  apply lp.ext
  funext i
  rw [seqRe_apply, lp.single_apply, lp.single_apply]
  by_cases h : i = k
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, Complex.one_re]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Complex.zero_re]

private lemma seqIm_single (k : ℤ) :
    seqIm (lp.single 2 k (1 : ℂ)) = 0 := by
  apply lp.ext
  funext i
  rw [seqIm_apply, lp.single_apply, lp.coeFn_zero]
  by_cases h : i = k
  · subst h
    rw [Pi.single_eq_same, Complex.one_im]
    rfl
  · rw [Pi.single_eq_of_ne h, Complex.zero_im]
    rfl

private lemma inner_single_seqOfReal (l : ℤ) (y : AtomSpace) :
    inner ℂ (lp.single 2 l (1 : ℂ)) (seqOfReal y)
      = (((y : ∀ _ : ℤ, ℝ) l : ℝ) : ℂ) := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_single l ?_]
  · rw [lp.single_apply, Pi.single_eq_same, seqOfReal_apply, RCLike.inner_apply]
    simp
  · intro i hi
    rw [lp.single_apply, Pi.single_eq_of_ne hi, RCLike.inner_apply]
    simp

/-- **THE SINGLE-ATOM PATH LAW, REAL SCALARS.**

Any bounded operator on `ℓ²(ℤ, ℝ)` whose matrix in the standard basis is the
unfolded Loewner divided-difference matrix has operator norm exactly
`2 cos(π/(⌈log c / log q⌉ + 1)) · Λ(q)/√q`. Derived from the complex form
`single_atom_path_lawC` by complexification. -/
theorem single_atom_path_lawR (q c : ℕ) (hq : 2 ≤ q) (hc : q < c)
    (T : AtomSpace →L[ℝ] AtomSpace)
    (hT : ∀ k l : ℤ, (T (lp.single 2 k 1) : ∀ _ : ℤ, ℝ) l = atomEntry q c k l) :
    ‖T‖ = pathLawNorm q c := by
  rw [← norm_complexifyT T]
  refine single_atom_path_lawC q c hq hc (complexifyT T) fun k l => ?_
  have hsingle : complexifyT T (lp.single 2 k (1 : ℂ))
      = seqOfReal (T (lp.single 2 k (1 : ℝ))) := by
    rw [show lp.single 2 k (1 : ℂ) = seqOfReal (lp.single 2 k (1 : ℝ)) by
        apply lp.ext
        funext i
        rw [seqOfReal_apply, lp.single_apply, lp.single_apply]
        by_cases h : i = k
        · subst h
          rw [Pi.single_eq_same, Pi.single_eq_same]
          norm_num
        · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]
          norm_num,
      complexifyT_seqOfReal]
  rw [hsingle, inner_single_seqOfReal, hT k l, atomEntry_symm]

private lemma inner_single_apply (l : ℤ) (x : AtomSpaceC) :
    inner ℂ (lp.single 2 l (1 : ℂ)) x = (x : ∀ _ : ℤ, ℂ) l := by
  rw [lp.inner_eq_tsum, tsum_eq_single l]
  · rw [lp.single_apply, Pi.single_eq_same, RCLike.inner_apply]
    simp
  · intro i hi
    rw [lp.single_apply, Pi.single_eq_of_ne hi, RCLike.inner_apply]
    simp

/-- The canonical Loewner atom operator on `ℓ²(ℤ, ℝ)` as a bounded linear operator. -/
noncomputable def atomCLMR (q c : ℕ) : AtomSpace →L[ℝ] AtomSpace :=
  LinearMap.mkContinuous
    { toFun := fun g => seqRe (atomCLMC q c (seqOfReal g))
      map_add' := fun g h => by rw [seqOfReal_add, map_add, seqRe_add]
      map_smul' := fun r g => by
        rw [seqOfReal_smul, map_smul]
        show seqRe (((r : ℝ) : ℂ) • atomCLMC q c (seqOfReal g)) = r • seqRe (atomCLMC q c (seqOfReal g))
        rw [seqRe_smul]
        simp }
    ‖atomCLMC q c‖
    (fun g => by
      calc ‖seqRe (atomCLMC q c (seqOfReal g))‖
          ≤ ‖atomCLMC q c (seqOfReal g)‖ := norm_seqRe_le _
        _ ≤ ‖atomCLMC q c‖ * ‖seqOfReal g‖ := (atomCLMC q c).le_opNorm _
        _ = ‖atomCLMC q c‖ * ‖g‖ := by rw [norm_seqOfReal])

/-- The canonical real atom has the Loewner matrix elements. -/
theorem inner_atomCLMR (q c : ℕ) (hq : 2 ≤ q) (hc : q < c) (k l : ℤ) :
    (atomCLMR q c (lp.single 2 k 1) : ∀ _ : ℤ, ℝ) l = atomEntry q c k l := by
  have h := inner_atomCLMC q c hq hc k l
  show (seqRe (atomCLMC q c (seqOfReal (lp.single 2 k 1))) : ∀ _ : ℤ, ℝ) l = atomEntry q c k l
  have hsingle : seqOfReal (lp.single 2 k (1 : ℝ)) = lp.single 2 k (1 : ℂ) := by
    apply lp.ext
    funext i
    rw [seqOfReal_apply, lp.single_apply, lp.single_apply]
    by_cases hik : i = k
    · subst hik; simp
    · rw [Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hik]; simp
  rw [hsingle, seqRe_apply]
  rw [inner_single_apply] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re] at hre
  rw [hre, atomEntry_symm]

/-- **Unconditional Path Law for the canonical real atom.** -/
theorem opNorm_atomCLMR (q c : ℕ) (hq : 2 ≤ q) (hc : q < c) :
    ‖atomCLMR q c‖ = pathLawNorm q c :=
  single_atom_path_lawR q c hq hc (atomCLMR q c) (inner_atomCLMR q c hq hc)

end Cvs.PathLaw
