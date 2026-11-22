import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.Mellin.EdgeRemainderClosedForm

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The S-sums from the edge count

`Σ f(s_i) = J f(b) − ∫_a^b N f'` with `N(x) = #{i : s_i ≤ x}`, so `N(S) ≤ A S` on `[5, c]` gives
`Σ s_i⁻¹ ≤ A log(c/5) + J/c`, `Σ s_i⁻² ≤ 2A/5`, `Σ s_i⁻³ ≤ 3A/50`; `c Σ_i` of Lemma E's majorant (Cvs.Prolate.Mellin.EdgeRemainderClosedForm)
is `ℛ(S₁, S₂, S₃)` exactly, hence at most `ℛ(c, r, J)` with `EdgeBesselCount`'s count.
-/

namespace Cvs.L2a.EdgeCountSSums

open Real Set MeasureTheory intervalIntegral Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Mellin.EdgeRemainderClosedForm Cvs.Prolate.EdgeBesselCount

/-- The cut-off `1_{s ≤ x} f'(x)` is interval integrable on `[a, b]`, with integral `∫_s^b f'`. -/
theorem ite_intervalIntegrable_and_integral {a b s : ℝ} (has : a ≤ s) (hsb : s ≤ b) {f' : ℝ → ℝ}
    (hf' : ContinuousOn f' (Icc a b)) :
    IntervalIntegrable (fun x => if s ≤ x then f' x else 0) volume a b ∧
      ∫ x in a..b, (if s ≤ x then f' x else 0) = ∫ x in s..b, f' x := by
  have hc2 : IntervalIntegrable f' volume s b :=
    (hf'.mono (Icc_subset_Icc has le_rfl)).intervalIntegrable_of_Icc hsb
  have eq1 : EqOn (fun _ => (0 : ℝ)) (fun x => if s ≤ x then f' x else 0) (uIoo a s) := by
    intro x hx
    rw [uIoo_of_le has] at hx
    simp [not_le.mpr hx.2]
  have eq2 : EqOn f' (fun x => if s ≤ x then f' x else 0) (uIoo s b) := by
    intro x hx
    rw [uIoo_of_le hsb] at hx
    simp [hx.1.le]
  have hi1 : IntervalIntegrable (fun x => if s ≤ x then f' x else 0) volume a s :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo eq1
  have hi2 : IntervalIntegrable (fun x => if s ≤ x then f' x else 0) volume s b := hc2.congr_uIoo eq2
  refine ⟨hi1.trans hi2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    ← intervalIntegral.integral_congr_uIoo eq1, ← intervalIntegral.integral_congr_uIoo eq2]
  simp

/-- `N(x) f'(x)` as a sum of cut-offs: `N(x) = #{i : s_i ≤ x}`. -/
theorem card_filter_mul_eq_sum {ι : Type*} [Fintype ι] (s : ι → ℝ) (f' : ℝ → ℝ) (x : ℝ) :
    ((Finset.univ.filter fun i => s i ≤ x).card : ℝ) * f' x = ∑ i, (if s i ≤ x then f' x else 0) := by
  classical
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- `N f'` is interval integrable on `[a, b]` when every `s_i ∈ [a, b]`. -/
theorem layer_intervalIntegrable {ι : Type*} [Fintype ι] (s : ι → ℝ) {a b : ℝ} (hs : ∀ i, s i ∈ Icc a b)
    {f' : ℝ → ℝ} (hf' : ContinuousOn f' (Icc a b)) :
    IntervalIntegrable (fun x => ((Finset.univ.filter fun i => s i ≤ x).card : ℝ) * f' x) volume a b := by
  have h := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
    (f := fun i x => if s i ≤ x then f' x else 0)
    fun i _ => (ite_intervalIntegrable_and_integral (hs i).1 (hs i).2 hf').1
  refine h.congr fun x _ => ?_
  simp only [Finset.sum_apply, card_filter_mul_eq_sum]

/-- The layer cake: `Σ f(s_i) = J f(b) − ∫_a^b N f'`. -/
theorem sum_eq_layer {ι : Type*} [Fintype ι] (s : ι → ℝ) {a b : ℝ} (hs : ∀ i, s i ∈ Icc a b)
    {f f' : ℝ → ℝ} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Icc a b)) :
    ∑ i, f (s i)
      = Fintype.card ι * f b - ∫ x in a..b, ((Finset.univ.filter fun i => s i ≤ x).card : ℝ) * f' x := by
  classical
  simp_rw [card_filter_mul_eq_sum]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (ite_intervalIntegrable_and_integral (hs i).1 (hs i).2 hf').1]
  have hterm : ∀ i, ∫ x in a..b, (if s i ≤ x then f' x else 0) = f b - f (s i) := by
    intro i
    rw [(ite_intervalIntegrable_and_integral (hs i).1 (hs i).2 hf').2]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hf x ?_) ?_
    · rw [uIcc_of_le (hs i).2] at hx; exact ⟨(hs i).1.trans hx.1, hx.2⟩
    · exact (hf'.mono (Icc_subset_Icc (hs i).1 le_rfl)).intervalIntegrable_of_Icc (hs i).2
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- With `f' ≤ 0` and `N(x) ≤ A x` on `[a, b]`: `Σ f(s_i) ≤ J f(b) + ∫_a^b A x (−f'(x))`. -/
theorem sum_le_of_count {ι : Type*} [Fintype ι] (s : ι → ℝ) {a b A : ℝ} (hab : a ≤ b)
    (hs : ∀ i, s i ∈ Icc a b) {f f' : ℝ → ℝ} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Icc a b)) (hf'0 : ∀ x ∈ Icc a b, f' x ≤ 0)
    (hN : ∀ S ∈ Icc a b, ((Finset.univ.filter fun i => s i ≤ S).card : ℝ) ≤ A * S) :
    ∑ i, f (s i) ≤ Fintype.card ι * f b + ∫ x in a..b, A * x * -f' x := by
  rw [sum_eq_layer s hs hf hf']
  have hcont : ContinuousOn (fun x => A * x * f' x) (Icc a b) :=
    (continuousOn_const.mul continuousOn_id).mul hf'
  have hmono : ∫ x in a..b, A * x * f' x
      ≤ ∫ x in a..b, ((Finset.univ.filter fun i => s i ≤ x).card : ℝ) * f' x :=
    intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable_of_Icc hab)
      (layer_intervalIntegrable s hs hf') fun x hx =>
        mul_le_mul_of_nonpos_right (hN x hx) (hf'0 x hx)
  have hneg : ∫ x in a..b, A * x * -f' x = -∫ x in a..b, A * x * f' x := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext x; ring
  rw [hneg]
  linarith

/-- `0 ≤ A` and `J ≤ A c` from the count at `S = 5` and `S = c`. -/
theorem count_consts {ι : Type*} [Fintype ι] (s : ι → ℝ) {A c : ℝ} (hc : 5 ≤ c) (hsc : ∀ i, s i ≤ c)
    (hN : ∀ S ∈ Icc (5 : ℝ) c, ((Finset.univ.filter fun i => s i ≤ S).card : ℝ) ≤ A * S) :
    0 ≤ A ∧ (Fintype.card ι : ℝ) ≤ A * c := by
  have h5 := hN 5 ⟨le_rfl, hc⟩
  have hcc := hN c ⟨hc, le_rfl⟩
  have hfull : (Finset.univ.filter fun i => s i ≤ c) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => hsc i
  rw [hfull, Finset.card_univ] at hcc
  refine ⟨?_, hcc⟩
  have : (0 : ℝ) ≤ ((Finset.univ.filter fun i => s i ≤ (5 : ℝ)).card : ℝ) := Nat.cast_nonneg _
  linarith

/-- `Σ s_i⁻¹ ≤ A log(c/5) + J/c` from `N(S) ≤ A S` on `[5, c]`. -/
theorem sum_inv_le_of_count {ι : Type*} [Fintype ι] (s : ι → ℝ) {A c : ℝ} (hc : 5 ≤ c)
    (hs5 : ∀ i, 5 ≤ s i) (hsc : ∀ i, s i ≤ c)
    (hN : ∀ S ∈ Icc (5 : ℝ) c, ((Finset.univ.filter fun i => s i ≤ S).card : ℝ) ≤ A * S) :
    ∑ i, (s i)⁻¹ ≤ A * Real.log (c / 5) + Fintype.card ι / c := by
  have hpos : ∀ x ∈ Icc (5 : ℝ) c, 0 < x := fun x hx => by linarith [hx.1]
  have h := sum_le_of_count s hc (fun i => ⟨hs5 i, hsc i⟩) (f := fun x => x⁻¹)
    (f' := fun x => -(x ^ 2)⁻¹) (fun x hx => hasDerivAt_inv (hpos x hx).ne')
    (ContinuousOn.neg (ContinuousOn.inv₀ (continuousOn_pow 2) fun x hx => (pow_pos (hpos x hx) 2).ne'))
    (fun x hx => by have := hpos x hx; simp only [neg_nonpos]; positivity) hN
  have hI : ∫ x in (5 : ℝ)..c, A * x * -(-(x ^ 2)⁻¹) = A * Real.log (c / 5) := by
    have heq : EqOn (fun x : ℝ => A * x * -(-(x ^ 2)⁻¹)) (fun x => A * x⁻¹) (uIcc 5 c) := by
      intro x hx
      rw [uIcc_of_le hc] at hx
      have := (hpos x hx).ne'
      show A * x * -(-(x ^ 2)⁻¹) = A * x⁻¹
      rw [neg_neg]; field_simp
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const_mul,
      integral_inv_of_pos (by norm_num) (by linarith)]
  rw [hI, ← div_eq_mul_inv] at h
  linarith

/-- `Σ s_i⁻² ≤ 2A/5` from `N(S) ≤ A S` on `[5, c]`. -/
theorem sum_inv_sq_le_of_count {ι : Type*} [Fintype ι] (s : ι → ℝ) {A c : ℝ} (hc : 5 ≤ c)
    (hs5 : ∀ i, 5 ≤ s i) (hsc : ∀ i, s i ≤ c)
    (hN : ∀ S ∈ Icc (5 : ℝ) c, ((Finset.univ.filter fun i => s i ≤ S).card : ℝ) ≤ A * S) :
    ∑ i, (s i ^ 2)⁻¹ ≤ 2 * A / 5 := by
  obtain ⟨hA, hJ⟩ := count_consts s hc hsc hN
  have hpos : ∀ x ∈ Icc (5 : ℝ) c, 0 < x := fun x hx => by linarith [hx.1]
  have hd : ∀ x ∈ Icc (5 : ℝ) c, HasDerivAt (fun x : ℝ => (x ^ 2)⁻¹) (-2 * (x ^ 3)⁻¹) x := by
    intro x hx
    have hx0 := (hpos x hx).ne'
    refine ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0)).congr_deriv ?_
    norm_num; field_simp
  have h := sum_le_of_count s hc (fun i => ⟨hs5 i, hsc i⟩) hd
    (ContinuousOn.mul continuousOn_const
      (ContinuousOn.inv₀ (continuousOn_pow 3) fun x hx => (pow_pos (hpos x hx) 3).ne'))
    (fun x hx => by have := hpos x hx; have : 0 < (x ^ 3)⁻¹ := by positivity
                    linarith) hN
  have hI : ∫ x in (5 : ℝ)..c, A * x * -(-2 * (x ^ 3)⁻¹) = 2 * A * (1 / 5 - 1 / c) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -(2 * A) * x⁻¹)]
    · ring
    · intro x hx
      rw [uIcc_of_le hc] at hx
      have hx0 := (hpos x hx).ne'
      refine ((hasDerivAt_inv hx0).const_mul (-(2 * A))).congr_deriv ?_
      field_simp
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hc]
      exact (continuousOn_const.mul continuousOn_id).mul (ContinuousOn.neg (continuousOn_const.mul
        (ContinuousOn.inv₀ (continuousOn_pow 3) fun x hx => (pow_pos (hpos x hx) 3).ne')))
  rw [hI] at h
  have hc0 : 0 < c := by linarith
  have : (Fintype.card ι : ℝ) * (c ^ 2)⁻¹ ≤ 2 * A * (1 / c) := by
    rw [show (Fintype.card ι : ℝ) * (c ^ 2)⁻¹ = (Fintype.card ι : ℝ) / c * (1 / c) by field_simp]
    gcongr
    rw [div_le_iff₀ hc0]; linarith
  linarith

/-- `Σ s_i⁻³ ≤ 3A/50` from `N(S) ≤ A S` on `[5, c]`. -/
theorem sum_inv_cube_le_of_count {ι : Type*} [Fintype ι] (s : ι → ℝ) {A c : ℝ} (hc : 5 ≤ c)
    (hs5 : ∀ i, 5 ≤ s i) (hsc : ∀ i, s i ≤ c)
    (hN : ∀ S ∈ Icc (5 : ℝ) c, ((Finset.univ.filter fun i => s i ≤ S).card : ℝ) ≤ A * S) :
    ∑ i, (s i ^ 3)⁻¹ ≤ 3 * A / 50 := by
  obtain ⟨hA, hJ⟩ := count_consts s hc hsc hN
  have hpos : ∀ x ∈ Icc (5 : ℝ) c, 0 < x := fun x hx => by linarith [hx.1]
  have hd : ∀ x ∈ Icc (5 : ℝ) c, HasDerivAt (fun x : ℝ => (x ^ 3)⁻¹) (-3 * (x ^ 4)⁻¹) x := by
    intro x hx
    have hx0 := (hpos x hx).ne'
    refine ((hasDerivAt_pow 3 x).inv (pow_ne_zero 3 hx0)).congr_deriv ?_
    norm_num; field_simp
  have h := sum_le_of_count s hc (fun i => ⟨hs5 i, hsc i⟩) hd
    (ContinuousOn.mul continuousOn_const
      (ContinuousOn.inv₀ (continuousOn_pow 4) fun x hx => (pow_pos (hpos x hx) 4).ne'))
    (fun x hx => by have := hpos x hx; have : 0 < (x ^ 4)⁻¹ := by positivity
                    linarith) hN
  have hI : ∫ x in (5 : ℝ)..c, A * x * -(-3 * (x ^ 4)⁻¹) = 3 * A / 2 * (1 / 25 - 1 / c ^ 2) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => -(3 * A / 2) * (x ^ 2)⁻¹)]
    · ring
    · intro x hx
      rw [uIcc_of_le hc] at hx
      have hx0 := (hpos x hx).ne'
      refine (((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0)).const_mul (-(3 * A / 2))).congr_deriv ?_
      norm_num; field_simp
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hc]
      exact (continuousOn_const.mul continuousOn_id).mul (ContinuousOn.neg (continuousOn_const.mul
        (ContinuousOn.inv₀ (continuousOn_pow 4) fun x hx => (pow_pos (hpos x hx) 4).ne')))
  rw [hI] at h
  have hc0 : 0 < c := by linarith
  have : (Fintype.card ι : ℝ) * (c ^ 3)⁻¹ ≤ 3 * A / 2 * (1 / c ^ 2) := by
    rw [show (Fintype.card ι : ℝ) * (c ^ 3)⁻¹ = (Fintype.card ι : ℝ) / c * (1 / c ^ 2) by field_simp]
    have hJc : (Fintype.card ι : ℝ) / c ≤ 3 * A / 2 := by rw [div_le_iff₀ hc0]; nlinarith
    exact mul_le_mul_of_nonneg_right hJc (by positivity)
  linarith

/-- `ℛ` as a function of the sums `S_p = Σ s_i^{−p}`. -/
noncomputable def RcalS (c r J S1 S2 S3 : ℝ) : ℝ :=
  16 / 15 * S3 + 2 * r / (3 * (1 - r)) * S1 + √(32 / 15) * e1 r * S2 / c + e1 r ^ 2 / 2 * S1 / c ^ 2
    + 2 * r * (J / c) * (2 * (2 + r) * Lc c + (2 + r) ^ 2 / 2) / (1 - r) ^ 4 + √(I1bar r * I2bar r) * S2 / c

/-- `ℛ` with the sums replaced by their count bounds. -/
noncomputable def Rcal (c r J : ℝ) : ℝ :=
  RcalS c r J (Ac c * Real.log (c / 5) + J / c) (2 * Ac c / 5) (3 * Ac c / 50)

/-- `c · lemmaEBound(c, r, s)` expanded in powers of `s⁻¹`. -/
theorem mul_lemmaEBound_eq {c r s : ℝ} (hc : c ≠ 0) (hs : s ≠ 0) :
    c * lemmaEBound c r s
      = 16 / 15 * (s ^ 3)⁻¹ + 2 * r / (3 * (1 - r)) * s⁻¹ + √(32 / 15) * e1 r * (s ^ 2)⁻¹ / c
        + e1 r ^ 2 / 2 * s⁻¹ / c ^ 2
        + 2 * r * (1 / c) * (2 * (2 + r) * Lc c + (2 + r) ^ 2 / 2) / (1 - r) ^ 4
        + √(I1bar r * I2bar r) * (s ^ 2)⁻¹ / c := by
  unfold lemmaEBound
  rw [add_sq, sq_sqrt (by norm_num : (0 : ℝ) ≤ 32 / 15)]
  by_cases hr : 1 - r = 0
  · have hr' : r = 1 := by linarith
    subst hr'
    field_simp
    ring
  · field_simp
    ring

/-- `c Σ_i lemmaEBound(c, r, s_i) = ℛ(S₁, S₂, S₃)` exactly. -/
theorem mul_sum_lemmaEBound_eq {ι : Type*} [Fintype ι] (s : ι → ℝ) {c r : ℝ} (hc : c ≠ 0)
    (hs : ∀ i, s i ≠ 0) :
    c * ∑ i, lemmaEBound c r (s i)
      = RcalS c r (Fintype.card ι) (∑ i, (s i)⁻¹) (∑ i, (s i ^ 2)⁻¹) (∑ i, (s i ^ 3)⁻¹) := by
  rw [Finset.mul_sum]
  simp_rw [mul_lemmaEBound_eq hc (hs _)]
  unfold RcalS
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- `ℛ(S₁, S₂, S₃)` is monotone in each sum for `0 ≤ r < 1`, `c > 0`. -/
theorem RcalS_mono {c r J S1 S2 S3 S1' S2' S3' : ℝ} (hc : 0 < c) (hr0 : 0 ≤ r) (hr : r < 1)
    (h1 : S1 ≤ S1') (h2 : S2 ≤ S2') (h3 : S3 ≤ S3') :
    RcalS c r J S1 S2 S3 ≤ RcalS c r J S1' S2' S3' := by
  have h1r : 0 < 1 - r := by linarith
  have he := e1_nonneg hr0 hr
  unfold RcalS
  gcongr

/-- `c Σ_i` of Lemma E's majorant over the rungs is at most `ℛ(c, r, J)`, `J` the number of rungs. -/
theorem mul_sum_lemmaEBound_le_Rcal {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c r : ℝ}
    {χ : ι → ℝ} (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχinj : Function.Injective χ)
    (hψ1 : ∀ i, psi c (g i) 1 ≠ 0) (hr0 : 0 ≤ r) (hr : r < 1) :
    c * ∑ i, lemmaEBound c r ((c ^ 2 - χ i) / c) ≤ Rcal c r (Fintype.card ι) := by
  have hc0 : 0 < c := by linarith
  set s : ι → ℝ := fun i => (c ^ 2 - χ i) / c with hsdef
  have hs5 : ∀ i, 5 ≤ s i := fun i => by
    simp only [hsdef]; rw [le_div_iff₀ hc0]; linarith [hσ i]
  have hsc : ∀ i, s i ≤ c := fun i => by
    simp only [hsdef]; rw [div_le_iff₀ hc0]; nlinarith [hχ0 i]
  have hN : ∀ S ∈ Icc (5 : ℝ) c, ((Finset.univ.filter fun i => s i ≤ S).card : ℝ) ≤ Ac c * S :=
    fun S hS => edge_count_le hg hg₁ hg₂c hang hc hχ0 hσ hχinj hψ1 hS.1
  have hc5 : (5 : ℝ) ≤ c := by linarith
  rw [mul_sum_lemmaEBound_eq s hc0.ne' fun i => by linarith [hs5 i]]
  exact RcalS_mono hc0 hr0 hr (sum_inv_le_of_count s hc5 hs5 hsc hN)
    (sum_inv_sq_le_of_count s hc5 hs5 hsc hN) (sum_inv_cube_le_of_count s hc5 hs5 hsc hN)

end Cvs.L2a.EdgeCountSSums
