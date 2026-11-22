/-
Rapid Fourier decay of smooth bumps.

Classical (Katznelson, *An Introduction to Harmonic Analysis*, §I.4;
Stein–Shakarchi, *Fourier Analysis*, Ch. 2): a smooth function
compactly supported in an interval has Fourier coefficients decaying
faster than any algebraic rate. The proof is iterated integration by
parts — the boundary terms vanish because the bump vanishes at the
endpoints, so each pass trades one power of `n` for one derivative:

  ‖c_n(f)‖ = (b-a)/(2π|n|) · ‖c_n(f')‖.

Campaign context: stage 1 of discharging the tail hypothesis of
`superalgebraic_sections` (`Cvs.PathLaw.SuperAlgebraic`). The remaining
stages: the bump-modulated chain eigenfunction of the masked rotation,
its coefficient product formula `c_n = D_m(n)·b̂(n)`, and the transport
of the resulting super-algebraic ℓ²-tails to the window sections.
-/
import Cvs.PathLaw.SuperAlgebraic
import Mathlib.Analysis.Fourier.AddCircle

open Real Set
open scoped ContDiff

namespace Cvs.PathLaw

/-- Fourier coefficients decaying faster than any algebraic rate. -/
def RapidFourierDecay (c : ℤ → ℂ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℤ, n ≠ 0 → ‖c n‖ ≤ C / |(n : ℝ)| ^ k

/-- One integration by parts: for a smooth bump supported inside the
interval, the boundary terms vanish and each Fourier coefficient trades
a power of `n` for a derivative. -/
lemma norm_fourierCoeffOn_deriv {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hsupp : tsupport f ⊆ Ioo a b)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn hab f n‖
      = (b - a) / (2 * π * |(n : ℝ)|)
        * ‖fourierCoeffOn hab (deriv f) n‖ := by
  obtain ⟨hdiff, hderiv⟩ := contDiff_infty_iff_deriv.mp hf
  have hfa : f a = 0 := image_eq_zero_of_notMem_tsupport
    (fun hmem => lt_irrefl a (hsupp hmem).1)
  have hfb : f b = 0 := image_eq_zero_of_notMem_tsupport
    (fun hmem => lt_irrefl b (hsupp hmem).2)
  rw [fourierCoeffOn_of_hasDerivAt hab hn
    (fun x _ => (hdiff x).hasDerivAt)
    (hderiv.continuous.intervalIntegrable a b)]
  rw [hfb, hfa, sub_zero, mul_zero, zero_sub, norm_mul, norm_neg, norm_mul]
  have hnorm1 : ‖(1 : ℂ) / (-2 * (π : ℂ) * Complex.I * (n : ℂ))‖
      = 1 / (2 * π * |(n : ℝ)|) := by
    rw [norm_div, norm_one]
    congr 1
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hnorm2 : ‖((b : ℂ) - (a : ℂ))‖ = b - a := by
    rw [← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)]
  rw [hnorm1, hnorm2]
  ring

/-- Iterated integration by parts: `k` passes trade `k` powers of `n`
for `k` derivatives. -/
theorem norm_fourierCoeffOn_le_pow {a b : ℝ} (hab : a < b) {n : ℤ}
    (hn : n ≠ 0) (k : ℕ) :
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → tsupport f ⊆ Ioo a b →
    ‖fourierCoeffOn hab f n‖
      ≤ ((b - a) / (2 * π * |(n : ℝ)|)) ^ k
        * ‖fourierCoeffOn hab (deriv^[k] f) n‖ := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hr : (0 : ℝ) ≤ (b - a) / (2 * π * |(n : ℝ)|) :=
    div_nonneg hba.le (by positivity)
  induction k with
  | zero =>
    intro f _ _
    simp
  | succ k IH =>
    intro f hf hsupp
    have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
    have hsupp' : tsupport (deriv f) ⊆ Ioo a b :=
      subset_trans tsupport_deriv_subset hsupp
    calc ‖fourierCoeffOn hab f n‖
        = (b - a) / (2 * π * |(n : ℝ)|)
            * ‖fourierCoeffOn hab (deriv f) n‖ :=
          norm_fourierCoeffOn_deriv hab hf hsupp hn
      _ ≤ (b - a) / (2 * π * |(n : ℝ)|)
            * (((b - a) / (2 * π * |(n : ℝ)|)) ^ k
              * ‖fourierCoeffOn hab (deriv^[k] (deriv f)) n‖) :=
          mul_le_mul_of_nonneg_left (IH hf' hsupp') hr
      _ = ((b - a) / (2 * π * |(n : ℝ)|)) ^ (k + 1)
            * ‖fourierCoeffOn hab (deriv^[k + 1] f) n‖ := by
          rw [Function.iterate_succ_apply, pow_succ]
          ring

/-- The zeroth-order bound: a Fourier coefficient is at most the mean of
the norm. -/
lemma norm_fourierCoeffOn_le_integral {a b : ℝ} (hab : a < b) (g : ℝ → ℂ)
    (n : ℤ) :
    ‖fourierCoeffOn hab g n‖ ≤ (1 / (b - a)) * ∫ x in a..b, ‖g x‖ := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  rw [fourierCoeffOn_eq_integral, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (b - a))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab.le) ?_
  refine le_of_eq (intervalIntegral.integral_congr fun x _ => ?_)
  rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]

/-- **Smooth bumps have rapidly decaying Fourier coefficients**
(classical; iterated integration by parts). -/
theorem rapidFourierDecay_of_smooth_bump {a b : ℝ} (hab : a < b)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hsupp : tsupport f ⊆ Ioo a b) :
    RapidFourierDecay (fourierCoeffOn hab f) := by
  intro k
  refine ⟨((b - a) / (2 * π)) ^ k
    * ((1 / (b - a)) * ∫ x in a..b, ‖deriv^[k] f x‖), fun n hn => ?_⟩
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have h1 := norm_fourierCoeffOn_le_pow hab hn k hf hsupp
  have h2 := norm_fourierCoeffOn_le_integral hab (deriv^[k] f) n
  calc ‖fourierCoeffOn hab f n‖
      ≤ ((b - a) / (2 * π * |(n : ℝ)|)) ^ k
          * ‖fourierCoeffOn hab (deriv^[k] f) n‖ := h1
    _ ≤ ((b - a) / (2 * π * |(n : ℝ)|)) ^ k
          * ((1 / (b - a)) * ∫ x in a..b, ‖deriv^[k] f x‖) := by
        refine mul_le_mul_of_nonneg_left h2 ?_
        exact pow_nonneg (div_nonneg hba.le (by positivity)) k
    _ = ((b - a) / (2 * π)) ^ k
          * ((1 / (b - a)) * ∫ x in a..b, ‖deriv^[k] f x‖)
          / |(n : ℝ)| ^ k := by
        rw [← div_div, div_pow, div_mul_eq_mul_div]

/-- Rapid decay survives multiplication by a bounded sequence — the
shape of the coefficient product formula `c_n = D_m(n)·b̂(n)`. -/
theorem RapidFourierDecay.mul_bounded {c : ℤ → ℂ}
    (hc : RapidFourierDecay c) {d : ℤ → ℂ} {M : ℝ}
    (hd : ∀ n, ‖d n‖ ≤ M) :
    RapidFourierDecay fun n => d n * c n := by
  intro k
  obtain ⟨C, hC⟩ := hc k
  refine ⟨M * C, fun n hn => ?_⟩
  calc ‖d n * c n‖ = ‖d n‖ * ‖c n‖ := norm_mul _ _
    _ ≤ M * (C / |(n : ℝ)| ^ k) :=
        mul_le_mul (hd n) (hC n hn) (norm_nonneg _)
          (le_trans (norm_nonneg _) (hd n))
    _ = M * C / |(n : ℝ)| ^ k := by ring

end Cvs.PathLaw
