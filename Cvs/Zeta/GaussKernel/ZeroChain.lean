import Mathlib
import Cvs.Zeta.CompletedXiOrderOneGrowth
import Cvs.Zeta.CompletedZeroIndex
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.BumpAlgebra
import Cvs.Zeta.GaussKernel.RealSegmentClosed
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZetaZeroWindows

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The chain, over the zeros of `ζ`

`BumpAlgebra` builds the chain abstractly, over any family of ordinates and deviations with window
finiteness and a mirror.
-/

namespace Cvs.GaussKernel

open Cvs.Zeta.GaussKernel.AdmissibleKernel Cvs.GaussKernel Filter Asymptotics

/-- The ordinate of a non-trivial zero. -/
noncomputable def gam (ρ : nonTrivialZeroSet) : ℝ := ((ρ : ℂ)).im

/-- Its distance from the critical line. -/
noncomputable def del (ρ : nonTrivialZeroSet) : ℝ := ((ρ : ℂ)).re - 1 / 2

theorem del_ne_zero_iff {ρ : nonTrivialZeroSet} :
    del ρ ≠ 0 ↔ ((ρ : ℂ)).re ≠ 1 / 2 := by
  rw [del]
  constructor
  · intro h hc; exact h (by rw [hc]; ring)
  · intro h hc; exact h (by linarith [sub_eq_zero.mp hc])

/-- **`ζ`'s zeros reflect.**  Conjugation preserves the real part and flips the
ordinate, and `Cvs.GaussKernel.noRealOffLineZero` rules out the fixed point. -/
theorem hasMirror_zeta : HasMirror gam del := by
  intro ρ hδ
  have him : ((ρ : ℂ)).im ≠ 0 :=
    Cvs.GaussKernel.noRealOffLineZero ρ (del_ne_zero_iff.mp hδ)
  obtain ⟨σ, hpos, hre, habs⟩ := Cvs.Zeta.GaussKernel.AdmissibleKernel.exists_pos_im_nonTrivial him
  exact ⟨σ, hpos, habs, by rw [del, del, hre]⟩

/-- The windows are finite, from the arithmetic input. -/
theorem finite_window (M : ℝ) : {ρ : nonTrivialZeroSet | |gam ρ| ≤ M}.Finite :=
  finite_window_of_summable gam summable_zeta_quartic M

/-- The deviations are bounded by `1/2`, from the strip. -/
theorem del_bdd (ρ : nonTrivialZeroSet) : |del ρ| ≤ 1 / 2 :=
  abs_re_sub_half_le ρ

/-- **`¬RH` supplies the seed.**  An off-line zero, lifted to the record at its
own height and mirrored to positive ordinate. -/
theorem exists_seed (hnot : ¬ riemannHypothesis) :
    ∃ ρ₀ : nonTrivialZeroSet, GoodRecord gam del ρ₀ := by
  obtain ⟨ρ₁, hoff⟩ := exists_offLine_of_not_allZerosOnLine hnot
  have hδ₁ : del ρ₁ ≠ 0 := del_ne_zero_iff.mpr hoff
  obtain ⟨j, hjrec, -, hjge⟩ := exists_record_ge gam del finite_window ρ₁
  have hδj : del j ≠ 0 := by
    intro h
    rw [h] at hjge
    have : (0 : ℝ) < (del ρ₁) ^ 2 := by positivity
    nlinarith
  obtain ⟨ρ₀, hgood, -, -⟩ := goodRecord_of_record gam del hasMirror_zeta hjrec hδj
  exact ⟨ρ₀, hgood⟩

/-! ### The counting bridge -/

open Cvs.Zeta.Explicit.Venue in
/-- **The window count is at most the venue's zero count.**  Each zero gives a
distinct index in the multiplicity-expanded window, and multiplicity is at
least one. -/
theorem card_window_le_count (T : ℝ) :
    (finite_window T).toFinset.card ≤ nontrivialZetaZeroCount T := by
  classical
  have hinj : ∀ ρ σ : nonTrivialZeroSet,
      (toZeroIndex ρ).1 = (toZeroIndex σ).1 → ρ = σ := by
    intro ρ σ h
    exact Subtype.ext (by
      rw [← toZeroIndex_value ρ, ← toZeroIndex_value σ]
      exact congrArg nontrivialZetaZeroValue h)
  have hmaps : ∀ ρ ∈ (finite_window T).toFinset,
      (toZeroIndex ρ).1 ∈ nontrivialZetaZeroWindowFinset T := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    rw [mem_nontrivialZetaZeroWindowFinset, toZeroIndex_value]
    exact hρ
  refine le_trans (Finset.card_le_card_of_injOn _ hmaps
    (fun ρ _ σ _ h => hinj ρ σ h)) ?_
  rw [nontrivialZetaZeroCount, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun rho _ => completedZetaZeroMultiplicity_pos rho

/-- `C log m < m` eventually, for any `C`. -/
theorem eventually_mul_log_lt (C : ℝ) : ∀ᶠ m : ℝ in atTop, C * Real.log m < m := by
  have hc : (0 : ℝ) < 1 / (2 * (|C| + 1)) := by positivity
  have h := Real.isLittleO_log_id_atTop.def hc
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with m hm hm0
  simp only [Real.norm_eq_abs, id_eq] at hm
  rw [abs_of_pos hm0] at hm
  have hCle : C * Real.log m ≤ |C| * |Real.log m| := by
    calc C * Real.log m ≤ |C * Real.log m| := le_abs_self _
      _ = |C| * |Real.log m| := abs_mul _ _
  have hbound : |C| * |Real.log m| ≤ |C| * (1 / (2 * (|C| + 1)) * m) :=
    mul_le_mul_of_nonneg_left hm (abs_nonneg C)
  have hfin : |C| * (1 / (2 * (|C| + 1)) * m) < m := by
    have hd : (0 : ℝ) < 2 * (|C| + 1) := by positivity
    rw [show |C| * (1 / (2 * (|C| + 1)) * m) = |C| * m / (2 * (|C| + 1)) by ring,
      div_lt_iff₀ hd]
    nlinarith [abs_nonneg C, hm0]
  linarith

/-- The crowding statement `BumpAlgebra`'s chain produces. -/
def Crowding : Prop :=
  ∀ i₀ : nonTrivialZeroSet, GoodRecord gam del i₀ → ∀ n : ℕ,
    n ≤ ((finite_window (|gam i₀| + Real.sqrt n / 2)).toFinset).card

open Cvs.Zeta.Explicit.Venue in
/-- **Positivity at the offset kernel implies RH, unconditionally.** If the construction never
succeeds, `BumpAlgebra`'s chain crowds `n` distinct zeros into a window of radius `|γ₀| + √n / 2` for
every `n`. -/
theorem riemannHypothesis_of_card (hcard : Crowding) :
    riemannHypothesis := by
  by_contra hnot
  obtain ⟨ρ₀, hg⟩ := exists_seed hnot
  obtain ⟨C, T0, hC, hT0, hcount⟩ := nontrivialZetaZeroCountBigO_proved
  set a : ℝ := |gam ρ₀| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have hev : ∀ᶠ K : ℕ in atTop,
      C * Real.log (K : ℝ) < (K : ℝ) ∧ 2 * a + 2 * T0 + 2 ≤ (K : ℝ) := by
    refine tendsto_natCast_atTop_atTop.eventually
      (((eventually_mul_log_lt C).and (eventually_ge_atTop (2 * a + 2 * T0 + 2))))
  obtain ⟨K, hklog, hkbig⟩ := hev.exists
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by linarith
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  -- the chain, at n = K²
  have hsqrt : Real.sqrt ((K ^ 2 : ℕ) : ℝ) = (K : ℝ) := by
    push_cast
    exact Real.sqrt_sq (by positivity)
  have hchain0 := hcard _ hg (K ^ 2)
  set T : ℝ := a + (K : ℝ) / 2 with hTdef
  -- transport the window radius along `hsqrt` *inside the membership predicate*, which is a
  -- plain inequality between reals; rewriting under `Set.Finite.toFinset` is not type correct
  -- now that `Crowding` makes the finiteness proof an opaque constant
  have hTeq : a + Real.sqrt ((K ^ 2 : ℕ) : ℝ) / 2 = T := by rw [hsqrt, hTdef]
  have hchain : K ^ 2 ≤ ((finite_window T).toFinset).card := by
    refine le_trans hchain0 (Finset.card_le_card ?_)
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    rw [hTeq] at hρ
    exact hρ
  -- the counting law
  have hTT0 : T0 ≤ T := by rw [hTdef]; linarith
  have hTle : T ≤ (K : ℝ) := by rw [hTdef]; linarith
  have hT1 : (1 : ℝ) ≤ T := by rw [hTdef]; linarith
  have hcard : ((K : ℝ)) ^ 2 ≤ (nontrivialZetaZeroCount T : ℝ) := by
    have h1 : ((K ^ 2 : ℕ) : ℝ) ≤ ((finite_window T).toFinset.card : ℝ) := by
      exact_mod_cast hchain
    have h2 : (((finite_window T).toFinset.card : ℕ) : ℝ)
        ≤ (nontrivialZetaZeroCount T : ℝ) := by
      exact_mod_cast card_window_le_count T
    push_cast at h1
    linarith
  have hCT := hcount T hTT0
  -- K² ≤ C·T·log T ≤ C·K·log K
  have hlogle : Real.log T ≤ Real.log (K : ℝ) := Real.log_le_log (by linarith) hTle
  have hlog0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hK1
  have hfinal : ((K : ℝ)) ^ 2 ≤ C * (K : ℝ) * Real.log (K : ℝ) := by
    refine le_trans hcard (le_trans hCT ?_)
    have : C * T * Real.log T ≤ C * (K : ℝ) * Real.log (K : ℝ) := by
      have hCT0 : 0 ≤ C * T := by positivity
      nlinarith [Real.log_nonneg hT1, hlogle, hTle, hC, hlog0]
    exact this
  nlinarith [hklog, hK0, hlog0]

/-!
## RH as marginal stability

Writing `ρ = ½ + δ + iγ`, the contribution of a zero to `ψ(x)` is `x^{½+δ}·e^{iγ log x}`, so
`δ` is a growth exponent.
-/

/-!
## How much a failure costs

A zero off the line at `½ + δ + iγ` forces three companions: `½ - δ + iγ`, `½ + δ - iγ`, `½ -
δ - iγ`.
-/

open Cvs.GaussKernel

/-- A zero off the line has nonzero ordinate: `Cvs.GaussKernel.noRealOffLineZero`. -/
theorem im_ne_zero_of_del_ne_zero {ρ : nonTrivialZeroSet} (h : del ρ ≠ 0) :
    ((ρ : ℂ)).im ≠ 0 :=
  Cvs.GaussKernel.noRealOffLineZero ρ (by intro hre; exact h (by rw [del, hre]; ring))

/-! ## The sum rule

The four-point cancellation is a special case.  Over *any* finite set of zeros
closed under `ρ ↦ 1 - ρ`, the deviations sum to zero, because the sum equals its
own negative.  A failure of RH therefore has zero mean and positive variance. -/

end Cvs.GaussKernel
