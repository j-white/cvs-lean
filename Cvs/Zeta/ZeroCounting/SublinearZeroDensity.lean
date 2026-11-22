import Mathlib
import Cvs.Route.Visibility.ExteriorTransformHolomorphy
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.RightEdgeDirichletPoly
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.MollifiedDetectorSeries
import Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf
import Cvs.Zeta.ZeroCounting.CarlsonCountBridge
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint
import Cvs.Zeta.ZeroDensityTail
import Cvs.Zeta.ZetaSeamStatement
import Cvs.Zeta.ZetaZeroConfig

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Unconditional sublinear zero-density theorem `N(σ, T) = O_σ(T^{θ(σ)})` (`θ(σ) < 1`)

Summing `Cvs.Route.Visibility.ExteriorTransformHolomorphy.norm_sq_le_ball` over `ρ ∈ dyadicUpperBox σ T` against `Cvs.Zeta.ZeroDensityTail.localCount_le` and `Cvs.Zeta.GaussKernel.RightEdgeDirichletPoly`'s strip `L²`
bound gives dyadic count `O_σ(T^{1 - c²/4})` (`c = (σ - 1/2)/2`), hence `SublinearZeroDensity` and `Cvs.Zeta.GaussKernel.AdmissibleKernel.ZeroDensity`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset Asymptotics Metric
open scoped Classical
open Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint (zeroBox zeroBox_finite zeroBox_subset N_zero N_zero_of_one_le mem_nonTrivialZeroSet_of_mem_zeroBox carlsonCount_le_N_zero carlsonCount_eq_zero_of_one_le tendsto_natCount_div_atTop tendsto_div_atTop_of_eventually_le)
open Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf (upperBox upperCount N_zero_le_two_mul_upperCount)
open Cvs.Route.Visibility.ExteriorTransformHolomorphy (norm_sq_le_ball)
open Cvs.Zeta.MollifiedDetectorSeries (mollifiedDetector differentiableOn_mollifiedDetector mollifiedDetector_eq_neg_one_of_zeta_zero)
open Cvs.Zeta.GaussKernel.RightEdgeDirichletPoly (integral_strip_mollifiedDetector_sq_le)

namespace Cvs.Zeta.ZeroCounting.SublinearZeroDensity

/-! ### Dyadic zero box and local ball-cover multiplicity -/

/-- Sublinear zero-density property: for every `σ ∈ (1/2, 1]`, `N(σ, T) = O_σ(T^θ)` with `0 < θ < 1`. -/
def SublinearZeroDensity : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 →
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ (fun T : ℝ => (N_zero σ T : ℝ)) =O[atTop] (fun T : ℝ => T ^ θ)

/-- Distinct zeros of `ζ` with `σ ≤ Re ρ ≤ 1` and `T < Im ρ ≤ 2T`. -/
def dyadicUpperBox (σ T : ℝ) : Set ℂ :=
  {ρ ∈ upperBox σ (2 * T) | T < ρ.im}

theorem dyadicUpperBox_finite {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    (dyadicUpperBox σ T).Finite :=
  ((zeroBox_finite hσ (2 * T)).subset inter_subset_left).subset fun _ h => h.1

theorem upperCount_mono {σ T₁ T₂ : ℝ} (hσ : 0 < σ) (hT : T₁ ≤ T₂) :
    upperCount σ T₁ ≤ upperCount σ T₂ := by
  have hfin : (upperBox σ T₂).Finite := (zeroBox_finite hσ T₂).subset inter_subset_left
  refine Set.ncard_le_ncard ?_ hfin
  rintro ρ ⟨hzb, him0⟩
  exact ⟨zeroBox_subset le_rfl hT hzb, him0⟩

theorem upperCount_two_mul_le {σ T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T) :
    upperCount σ (2 * T) ≤ upperCount σ T + (dyadicUpperBox σ T).ncard := by
  have hfin1 : (upperBox σ T).Finite := (zeroBox_finite hσ T).subset inter_subset_left
  have hfin2 : (dyadicUpperBox σ T).Finite := dyadicUpperBox_finite hσ T
  have hsub : upperBox σ (2 * T) ⊆ upperBox σ T ∪ dyadicUpperBox σ T := by
    rintro ρ ⟨⟨⟨hre1, hre2, _, him_hi⟩, hz⟩, him0⟩
    have him_ge : 0 ≤ ρ.im := him0
    rcases le_or_gt ρ.im T with hle | hgt
    · exact Or.inl ⟨⟨⟨hre1, hre2, by linarith [hT], hle⟩, hz⟩, him0⟩
    · exact Or.inr ⟨⟨⟨⟨hre1, hre2, by linarith [hT], him_hi⟩, hz⟩, him0⟩, hgt⟩
  calc upperCount σ (2 * T)
      ≤ (upperBox σ T ∪ dyadicUpperBox σ T).ncard := Set.ncard_le_ncard hsub (hfin1.union hfin2)
    _ ≤ (upperBox σ T).ncard + (dyadicUpperBox σ T).ncard := Set.ncard_union_le _ _

/-- Every radius-`r` (`r = c/2 < 1`) ball around `ρ ∈ dyadicUpperBox (1/2 + 2c) T` lies inside the
strip `[1/2 + c, 3/2] ×ℂ [T - 1, 2T + 1]`. -/
theorem ball_subset_strip_of_mem_dyadicUpperBox {c T : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 4)
    {ρ : ℂ} (hρ : ρ ∈ dyadicUpperBox (1 / 2 + 2 * c) T) :
    ball ρ (c / 2) ⊆ Icc (1 / 2 + c) (3 / 2) ×ℂ Icc (T - 1) (2 * T + 1) := by
  intro z hz
  obtain ⟨⟨⟨⟨hre_lo, hre_hi, _, him_hi⟩, _⟩, _⟩, him_lo⟩ := hρ
  have hd : ‖z - ρ‖ < c / 2 := by simpa [dist_eq_norm] using hz
  have hre_diff : |z.re - ρ.re| ≤ c / 2 := by
    simpa only [sub_re] using (Complex.abs_re_le_norm (z - ρ)).trans hd.le
  have him_diff : |z.im - ρ.im| ≤ c / 2 := by
    simpa only [sub_im] using (Complex.abs_im_le_norm (z - ρ)).trans hd.le
  rw [mem_reProdIm, Set.mem_Icc, Set.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith [(abs_le.mp hre_diff).1, (abs_le.mp hre_diff).2,
      (abs_le.mp him_diff).1, (abs_le.mp him_diff).2]

/-- Pointwise ball-cover multiplicity: for `T ≥ 32` and `z` with `z.im ∈ [T - 1, 2T + 1]`, at most
`176 log(3T)` points `ρ ∈ dyadicUpperBox σ T` (`0 < σ`) satisfy `z ∈ ball ρ r` (`r ≤ 1`). -/
theorem card_filter_mem_ball_le {σ r T : ℝ} (hσ : 0 < σ) (hr : r ≤ 1) (hT : 32 ≤ T)
    (Z : Finset ℂ) (hZ : (Z : Set ℂ) ⊆ dyadicUpperBox σ T)
    {z : ℂ} (hz : z.im ∈ Icc (T - 1) (2 * T + 1)) :
    ((Z.filter (fun ρ => z ∈ ball ρ r)).card : ℝ) ≤ 176 * Real.log (3 * T) := by
  set F : Finset ℂ := Z.filter (fun ρ => z ∈ ball ρ r)
  have hsub : (F : Set ℂ) ⊆ Cvs.Zeta.Base.zerosIn (z.im - 1) z.im ∪ Cvs.Zeta.Base.zerosIn z.im (z.im + 1) := by
    intro ρ hρ
    rw [Finset.mem_coe, Finset.mem_filter] at hρ
    obtain ⟨hρZ, hball⟩ := hρ
    have hρD := hZ hρZ
    have hnt := mem_nonTrivialZeroSet_of_mem_zeroBox hσ hρD.1.1
    have hnt23 : Cvs.Zeta.Base.IsNontrivialZero ρ := ⟨hnt.1, hnt.2.1, hnt.2.2⟩
    have hd : ‖z - ρ‖ < 1 := (by simpa [dist_eq_norm] using hball : ‖z - ρ‖ < r).trans_le hr
    have him_abs : |z.im - ρ.im| < 1 :=
      lt_of_le_of_lt (by simpa only [sub_im] using Complex.abs_im_le_norm (z - ρ)) hd
    have hlo : z.im - 1 < ρ.im := by linarith [(abs_lt.mp him_abs).2]
    have hhi : ρ.im ≤ z.im + 1 := by linarith [(abs_lt.mp him_abs).1]
    rcases le_or_gt ρ.im z.im with hmid | hmid
    · exact Or.inl ⟨hnt23, hlo, hmid⟩
    · exact Or.inr ⟨hnt23, hmid, hhi⟩
  have hfin1 := Cvs.Zeta.Base.zerosIn_finite (z.im - 1) z.im
  have hfin2 := Cvs.Zeta.Base.zerosIn_finite z.im (z.im + 1)
  have hcard_nat : F.card ≤ Cvs.Zeta.Base.Ncount (z.im - 1) z.im + Cvs.Zeta.Base.Ncount z.im (z.im + 1) := by
    calc F.card = (F : Set ℂ).ncard := (Set.ncard_coe_finset F).symm
      _ ≤ (Cvs.Zeta.Base.zerosIn (z.im - 1) z.im ∪ Cvs.Zeta.Base.zerosIn z.im (z.im + 1)).ncard :=
          Set.ncard_le_ncard hsub (hfin1.union hfin2)
      _ ≤ Cvs.Zeta.Base.Ndist (z.im - 1) z.im + Cvs.Zeta.Base.Ndist z.im (z.im + 1) :=
          Set.ncard_union_le _ _
      _ ≤ Cvs.Zeta.Base.Ncount (z.im - 1) z.im + Cvs.Zeta.Base.Ncount z.im (z.im + 1) :=
          Nat.add_le_add (Cvs.Zeta.Base.trivial_chain₀ _ _).2.2.2.2.2
            (Cvs.Zeta.Base.trivial_chain₀ _ _).2.2.2.2.2
  have hc1 : (Cvs.Zeta.Base.Ncount (z.im - 1) z.im : ℝ) ≤ 88 * Real.log (3 * T) := by
    have h1 := Cvs.Zeta.ZeroDensityTail.localCount_le (z.im - 1)
    rw [sub_add_cancel] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) (by norm_num))
    · positivity
    · rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.2]
  have hc2 : (Cvs.Zeta.Base.Ncount z.im (z.im + 1) : ℝ) ≤ 88 * Real.log (3 * T) := by
    have h2 := Cvs.Zeta.ZeroDensityTail.localCount_le z.im
    refine h2.trans (mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) (by norm_num))
    · positivity
    · rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.2]
  have hcast : (F.card : ℝ) ≤ (Cvs.Zeta.Base.Ncount (z.im - 1) z.im : ℝ) + (Cvs.Zeta.Base.Ncount z.im (z.im + 1) : ℝ) := by
    exact_mod_cast hcard_nat
  linarith

/-! ### Dyadic zero count bound `O_σ(T^{1 - c²/4})` -/

/-- **Dyadic zero-density bound**: for `σ ∈ (1/2, 1)` with `c = (σ - 1/2)/2`, there exist
`C_d ≥ 0` and `T_d ≥ 32` such that `((dyadicUpperBox σ T).ncard : ℝ) ≤ C_d · T^{1 - c²/4}`
for all `T ≥ T_d`. -/
theorem dyadicUpperBox_ncard_le {σ : ℝ} (hσ_lo : 1 / 2 < σ) (hσ_hi : σ < 1) :
    ∃ C_d T_d : ℝ, 0 ≤ C_d ∧ 32 ≤ T_d ∧ ∀ {T : ℝ}, T_d ≤ T →
      ((dyadicUpperBox σ T).ncard : ℝ) ≤ C_d * T ^ (1 - ((σ - 1 / 2) / 2) ^ 2 / 4) := by
  set c : ℝ := (σ - 1 / 2) / 2
  have hc0 : 0 < c := by dsimp only [c]; linarith
  have hc1 : c < 1 / 4 := by dsimp only [c]; linarith
  have hσ_eq : σ = 1 / 2 + 2 * c := by dsimp only [c]; ring
  set r : ℝ := c / 2
  have hr0 : 0 < r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1 := by dsimp only [r]; linarith
  set η : ℝ := c ^ 2 / 4
  have hη0 : 0 < η := by dsimp only [η]; positivity
  obtain ⟨C_A, T_A, hCA0, hTA32, hstrip⟩ := integral_strip_mollifiedDetector_sq_le hc0 hc1
  set C_d : ℝ := (Real.pi * r ^ 2)⁻¹ * (176 * (2 / η)) * C_A
  have hCd0 : 0 ≤ C_d := by dsimp only [C_d]; positivity
  refine ⟨C_d, T_A, hCd0, hTA32, fun {T} hT => ?_⟩
  have hT32 : 32 ≤ T := hTA32.trans hT
  have hT0 : 0 < T := by linarith
  set X : ℕ := ⌊T ^ c⌋₊
  set S_C : Set ℂ := Icc (1 / 2 + c) (3 / 2) ×ℂ Icc (T - 1) (2 * T + 1)
  set F : ℂ → ℝ := fun z => ‖mollifiedDetector X z‖ ^ 2
  have hfinD : (dyadicUpperBox σ T).Finite := dyadicUpperBox_finite (by linarith) T
  set Z : Finset ℂ := hfinD.toFinset
  have hZ_sub : (Z : Set ℂ) ⊆ dyadicUpperBox σ T := by
    intro ρ hρ; exact (hfinD.mem_toFinset).mp hρ
  -- `F` is continuous on compact `S_C`, hence integrable on `S_C`
  have hSC_compact : IsCompact S_C := isCompact_Icc.reProdIm isCompact_Icc
  have hSC_meas : MeasurableSet S_C := hSC_compact.isClosed.measurableSet
  have hF_cont : ContinuousOn F S_C := by
    refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
    refine (differentiableOn_mollifiedDetector X).continuousOn.mono fun z hz => ?_
    intro h1
    have him := congrArg Complex.im (Set.mem_singleton_iff.mp h1)
    simp at him
    linarith [hz.2.1]
  have hF_int : IntegrableOn F S_C := hF_cont.integrableOn_compact hSC_compact
  -- each `ρ ∈ Z` satisfies `1 ≤ (π r²)⁻¹ ∫_{S_C} (ball ρ r).indicator F`
  have hball_one : ∀ ρ ∈ Z,
      (1 : ℝ) ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in S_C, (ball ρ r).indicator F z := by
    intro ρ hρZ
    have hρD : ρ ∈ dyadicUpperBox (1 / 2 + 2 * c) T := by rw [← hσ_eq]; exact hZ_sub hρZ
    have hz0 : riemannZeta ρ = 0 := hρD.1.1.2
    have hval : ‖mollifiedDetector X ρ‖ ^ 2 = 1 := by
      rw [mollifiedDetector_eq_neg_one_of_zeta_zero X hz0, norm_neg, norm_one, one_pow]
    have hdcc : DiffContOnCl ℂ (mollifiedDetector X) (ball ρ r) := by
      refine (differentiableOn_mollifiedDetector X).diffContOnCl_ball fun z hz => ?_
      intro h1
      have him1 : z.im = 0 := by rw [Set.mem_singleton_iff.mp h1, one_im]
      have hd : ‖z - ρ‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
      have him_diff : |z.im - ρ.im| ≤ r := by
        simpa only [sub_im] using (Complex.abs_im_le_norm (z - ρ)).trans hd
      linarith [(abs_le.mp him_diff).1, hρD.2]
    have hsub_ball : ball ρ r ⊆ S_C := ball_subset_strip_of_mem_dyadicUpperBox hc0 hc1 hρD
    have hind_eq : ∫ z in ball ρ r, F z = ∫ z in S_C, (ball ρ r).indicator F z := by
      rw [setIntegral_indicator measurableSet_ball, Set.inter_eq_right.mpr hsub_ball]
    have hmv := norm_sq_le_ball hr0 hdcc
    rwa [hval, hind_eq] at hmv
  -- sum over `ρ ∈ Z` and exchange finite sum with `S_C` integral
  have hsum_balls : (Z.card : ℝ)
      ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in S_C, ∑ ρ ∈ Z, (ball ρ r).indicator F z := by
    calc (Z.card : ℝ) = ∑ _ρ ∈ Z, (1 : ℝ) := by simp
      _ ≤ ∑ ρ ∈ Z, (Real.pi * r ^ 2)⁻¹ * ∫ z in S_C, (ball ρ r).indicator F z :=
          Finset.sum_le_sum hball_one
      _ = (Real.pi * r ^ 2)⁻¹ * ∑ ρ ∈ Z, ∫ z in S_C, (ball ρ r).indicator F z := by
          rw [← Finset.mul_sum]
      _ = (Real.pi * r ^ 2)⁻¹ * ∫ z in S_C, ∑ ρ ∈ Z, (ball ρ r).indicator F z := by
          rw [← integral_finsetSum Z (fun ρ _ => hF_int.indicator measurableSet_ball)]
  -- pointwise multiplicity bound on `S_C`
  have hpt_mult : ∀ z ∈ S_C,
      (∑ ρ ∈ Z, (ball ρ r).indicator F z) ≤ (176 * Real.log (3 * T)) * F z := by
    intro z hz
    have hsum_eq : (∑ ρ ∈ Z, (ball ρ r).indicator F z)
        = ((Z.filter (fun ρ => z ∈ ball ρ r)).card : ℝ) * F z := by
      have hite : ∀ ρ ∈ Z, (ball ρ r).indicator F z = if z ∈ ball ρ r then F z else 0 :=
        fun ρ _ => Set.indicator_apply (ball ρ r) F z
      rw [Finset.sum_congr rfl hite, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_right
      (card_filter_mem_ball_le (by linarith) hr1 hT32 Z hZ_sub hz.2) (sq_nonneg _)
  have hint_sum : IntegrableOn (fun z => ∑ ρ ∈ Z, (ball ρ r).indicator F z) S_C :=
    integrable_finsetSum Z (fun ρ _ => hF_int.indicator measurableSet_ball)
  have hint_mult : (∫ z in S_C, ∑ ρ ∈ Z, (ball ρ r).indicator F z)
      ≤ (176 * Real.log (3 * T)) * ∫ z in S_C, F z := by
    calc (∫ z in S_C, ∑ ρ ∈ Z, (ball ρ r).indicator F z)
        ≤ ∫ z in S_C, (176 * Real.log (3 * T)) * F z :=
          setIntegral_mono_on hint_sum (hF_int.const_mul _) hSC_meas hpt_mult
      _ = (176 * Real.log (3 * T)) * ∫ z in S_C, F z := integral_const_mul _ _
  -- bound `log(3T) ≤ (2 / η) T^η` and combine with `hstrip`
  have hlog3T : Real.log (3 * T) ≤ (2 / η) * T ^ η := by
    have h3T : 3 * T ≤ T ^ 2 := by nlinarith
    have h1 : Real.log (3 * T) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) h3T
    rw [Real.log_pow, Nat.cast_ofNat] at h1
    have h2 : Real.log (T ^ η) ≤ T ^ η - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_rpow hT0] at h2
    have h3 : Real.log T ≤ (1 / η) * T ^ η := by
      rw [one_div_mul_eq_div, le_div_iff₀ hη0]; linarith
    calc Real.log (3 * T) ≤ 2 * Real.log T := h1
      _ ≤ 2 * ((1 / η) * T ^ η) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = (2 / η) * T ^ η := by ring
  have hF_nonneg : 0 ≤ ∫ z in S_C, F z := setIntegral_nonneg hSC_meas fun _ _ => sq_nonneg _
  have hlog_pos : 0 ≤ Real.log (3 * T) := Real.log_nonneg (by linarith)
  have hexp_combine : T ^ η * T ^ (1 - c ^ 2 / 2) = T ^ (1 - c ^ 2 / 4) := by
    rw [← Real.rpow_add hT0]; congr 1; dsimp only [η]; ring
  have hcard_eq : ((dyadicUpperBox σ T).ncard : ℝ) = (Z.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hfinD]
  rw [hcard_eq]
  calc (Z.card : ℝ)
      ≤ (Real.pi * r ^ 2)⁻¹ * ((176 * Real.log (3 * T)) * ∫ z in S_C, F z) :=
        hsum_balls.trans (mul_le_mul_of_nonneg_left hint_mult (by positivity))
    _ ≤ (Real.pi * r ^ 2)⁻¹ * ((176 * ((2 / η) * T ^ η)) * (C_A * T ^ (1 - c ^ 2 / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hlog3T (by norm_num)) (hstrip hT)
          hF_nonneg (by positivity)
    _ = C_d * (T ^ η * T ^ (1 - c ^ 2 / 2)) := by dsimp only [C_d]; ring
    _ = C_d * T ^ (1 - c ^ 2 / 4) := by rw [hexp_combine]

/-! ### Dyadic telescoping and unconditional `SublinearZeroDensity` -/

/-- **Dyadic telescoping**: if the dyadic count on `(T, 2T]` is `≤ C_d T^θ` for `T ≥ T₀ ≥ 1`
with `0 < θ < 1`, then `upperCount σ T ≤ (upperCount σ (2T₀) + D) · T^θ` for all `T ≥ T₀`. -/
theorem upperCount_le_of_dyadic {σ θ C_d T₀ : ℝ} (hσ : 0 < σ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hCd : 0 ≤ C_d) (hT₀ : 1 ≤ T₀)
    (hdyad : ∀ {T : ℝ}, T₀ ≤ T → ((dyadicUpperBox σ T).ncard : ℝ) ≤ C_d * T ^ θ) :
    ∃ C_u : ℝ, 0 ≤ C_u ∧ ∀ {T : ℝ}, T₀ ≤ T → (upperCount σ T : ℝ) ≤ C_u * T ^ θ := by
  set q : ℝ := (2 : ℝ) ^ (-θ)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set B : ℝ := (upperCount σ (2 * T₀) : ℝ)
  set D : ℝ := C_d * q / (1 - q)
  have hB0 : 0 ≤ B := Nat.cast_nonneg _
  have hD0 : 0 ≤ D := div_nonneg (mul_nonneg hCd hq0.le) (by linarith)
  have hDq : (D + C_d) * q = D := by
    dsimp only [D]
    have h1q : 1 - q ≠ 0 := by linarith
    field_simp
    ring
  -- induction on dyadic generations `T ∈ [T₀, 2^k · (2 T₀)]`
  have hind : ∀ k : ℕ, ∀ {T : ℝ}, T₀ ≤ T → T ≤ (2 : ℝ) ^ k * (2 * T₀) →
      (upperCount σ T : ℝ) ≤ B + D * T ^ θ := by
    intro k
    induction k with
    | zero =>
      intro T hT_lo hT_hi
      rw [pow_zero, one_mul] at hT_hi
      have h1 : (upperCount σ T : ℝ) ≤ B := by
        dsimp only [B]; exact_mod_cast upperCount_mono hσ hT_hi
      have h2 : 0 ≤ D * T ^ θ := mul_nonneg hD0 (Real.rpow_nonneg (by linarith) _)
      linarith
    | succ k ih =>
      intro T hT_lo hT_hi
      rcases le_or_gt T (2 * T₀) with hbase | hstep
      · have h1 : (upperCount σ T : ℝ) ≤ B := by
          dsimp only [B]; exact_mod_cast upperCount_mono hσ hbase
        have h2 : 0 ≤ D * T ^ θ := mul_nonneg hD0 (Real.rpow_nonneg (by linarith) _)
        linarith
      · set T' : ℝ := T / 2
        have hT'_lo : T₀ ≤ T' := by dsimp only [T']; linarith
        have hT'_hi : T' ≤ (2 : ℝ) ^ k * (2 * T₀) := by
          dsimp only [T']; rw [pow_succ'] at hT_hi; linarith
        have h2T' : 2 * T' = T := by dsimp only [T']; ring
        have hsplit : (upperCount σ T : ℝ)
            ≤ (upperCount σ T' : ℝ) + ((dyadicUpperBox σ T').ncard : ℝ) := by
          rw [← h2T']
          exact_mod_cast upperCount_two_mul_le hσ (by linarith)
        have hih := ih hT'_lo hT'_hi
        have hd := hdyad hT'_lo
        have hhalf_pow : (T') ^ θ = q * T ^ θ := by
          dsimp only [T', q]
          rw [div_eq_mul_inv, Real.mul_rpow (by linarith) (by norm_num),
            Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
          ring
        calc (upperCount σ T : ℝ)
            ≤ (B + D * (T') ^ θ) + C_d * (T') ^ θ :=
              hsplit.trans (add_le_add hih hd)
          _ = B + (D + C_d) * (T') ^ θ := by ring
          _ = B + ((D + C_d) * q) * T ^ θ := by rw [hhalf_pow]; ring
          _ = B + D * T ^ θ := by rw [hDq]
  refine ⟨B + D, by positivity, fun {T} hT => ?_⟩
  set k : ℕ := ⌊T⌋₊ + 1
  have hk_bound : T ≤ (2 : ℝ) ^ k * (2 * T₀) := by
    have hfl : T ≤ (k : ℝ) := by
      dsimp only [k]; push_cast; exact (Nat.lt_floor_add_one T).le
    have hpow : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast k.lt_two_pow_self.le
    calc T ≤ (2 : ℝ) ^ k := hfl.trans hpow
      _ = (2 : ℝ) ^ k * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ) ^ k * (2 * T₀) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h1 := hind k hT hk_bound
  have hone_le : 1 ≤ T ^ θ := Real.one_le_rpow (hT₀.trans hT) hθ0.le
  calc (upperCount σ T : ℝ) ≤ B + D * T ^ θ := h1
    _ ≤ B * T ^ θ + D * T ^ θ := by linarith [le_mul_of_one_le_right hB0 hone_le]
    _ = (B + D) * T ^ θ := by ring

/-- **Unconditional sublinear zero-density theorem**: for every `σ ∈ (1/2, 1]`, there exists
`θ ∈ (0, 1)` such that `N(σ, T) = O_σ(T^θ)` as `T → ∞`. -/
theorem sublinearZeroDensity : SublinearZeroDensity := by
  intro σ hσ_lo hσ_hi
  rcases eq_or_lt_of_le hσ_hi with rfl | hσ_lt
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    have hzero : (fun T : ℝ => (N_zero 1 T : ℝ)) = fun _ => (0 : ℝ) := by
      funext T; rw [N_zero_of_one_le le_rfl, Nat.cast_zero]
    rw [hzero]
    exact isBigO_zero _ _
  · set c : ℝ := (σ - 1 / 2) / 2
    have hc0 : 0 < c := by dsimp only [c]; linarith
    have hc1 : c < 1 / 4 := by dsimp only [c]; linarith
    set θ : ℝ := 1 - c ^ 2 / 4
    have hθ0 : 0 < θ := by dsimp only [θ]; nlinarith
    have hθ1 : θ < 1 := by dsimp only [θ]; nlinarith [sq_pos_of_pos hc0]
    obtain ⟨C_d, T_d, hCd0, hTd32, hdyad⟩ := dyadicUpperBox_ncard_le hσ_lo hσ_lt
    obtain ⟨C_u, hCu0, hup⟩ := upperCount_le_of_dyadic (by linarith) hθ0 hθ1 hCd0
      (by linarith : 1 ≤ T_d) hdyad
    refine ⟨θ, hθ0, hθ1, IsBigO.of_bound (2 * C_u) ?_⟩
    filter_upwards [eventually_ge_atTop T_d] with T hT
    have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) (hTd32.trans hT)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg hT0.le _)]
    have h2 : (N_zero σ T : ℝ) ≤ 2 * (upperCount σ T : ℝ) := by
      exact_mod_cast N_zero_le_two_mul_upperCount (by linarith) T
    calc (N_zero σ T : ℝ) ≤ 2 * (upperCount σ T : ℝ) := h2
      _ ≤ 2 * (C_u * T ^ θ) := mul_le_mul_of_nonneg_left (hup hT) (by norm_num)
      _ = (2 * C_u) * T ^ θ := by ring

/-- **Unconditional `Cvs.Zeta.GaussKernel.AdmissibleKernel.ZeroDensity`** (`N(1/2 + d, T) = o(T)` for every `d > 0`),
discharging the classical zero-density hypothesis across the `GaussKernel` chain. -/
theorem zeroDensity : Cvs.Zeta.GaussKernel.AdmissibleKernel.ZeroDensity := by
  refine Cvs.GaussKernel.zeroDensity_of_carlson (fun d hd => ?_)
  rcases lt_or_ge d (1 / 2 : ℝ) with hd2 | hd2
  · obtain ⟨θ, _, hθ1, hO⟩ := sublinearZeroDensity (1 / 2 + d) (by linarith) (by linarith)
    have hN : Tendsto (fun T : ℝ => (N_zero (1 / 2 + d) T : ℝ) / T) atTop (nhds 0) :=
      tendsto_natCount_div_atTop hθ1 hO
    refine tendsto_div_atTop_of_eventually_le
      (Eventually.of_forall fun _ => Nat.cast_nonneg _) ?_ hN
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact_mod_cast carlsonCount_le_N_zero (by linarith) hT
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [carlsonCount_eq_zero_of_one_le (by linarith) hT, Nat.cast_zero, zero_div]

end Cvs.Zeta.ZeroCounting.SublinearZeroDensity

end
