import Mathlib
import Cvs.Finite.AveragedApproximant
import Cvs.Finite.CosineModeTransformBounds
import Cvs.Finite.EvenSectorZeroSide
import Cvs.Finite.ModeTransformLogGrowth
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.LogEnvelopeSquareSummable

/-!
# Envelopes for the mode transforms on the critical strip

A cosine mode's window transform is `O(1/(1 + |Re ξ|))` on the strip `|Im ξ| ≤ 3/2` (crude
near its frequency, `Cvs.Finite.CosineModeTransformBounds`'s far bound beyond twice it), and so is any cosine polynomial. The
averaged fresh modes of `Cvs.Finite.AveragedApproximant` are `O(phi(|Re ξ|))` uniformly in `N`: below `2ω_{M₀+N}` by
`Cvs.Finite.ModeTransformLogGrowth` and `Cvs.Zeta.LogEnvelopeSquareSummable`'s monotone envelope, beyond by the far bound; at fixed `ξ` they vanish.
-/

noncomputable section

open Real Filter Topology Cvs.WeilForm.SelfConvolutionTransform

namespace Cvs.Finite.ModeTransformEnvelopes
open Cvs.ZeroCounting

/-- The window transform of the cosine mode `m`. -/
def Wm (L : ℝ) (m : ℤ) (ξ : ℂ) : ℂ :=
  Cvs.Detection.windowTransform L (cf fun y => Real.cos (2 * π * m / L * y)) ξ

/-- The strip factor at height `3/2`. -/
def E (L : ℝ) : ℝ := Real.exp (3 * L / 2)

theorem exp_le_E {L : ℝ} (hL : 0 ≤ L) {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2) :
    Real.exp (L * |ξ.im|) ≤ E L := by
  unfold E
  exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg ξ.im])

/-- **The far bound on the strip**: beyond twice the frequency (and beyond `1`), a mode is
`(20/3)(E+1)/(1 + |Re ξ|)`. -/
theorem norm_Wm_far {L : ℝ} (hL : 0 < L) (m : ℤ) {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2)
    (h1 : 1 ≤ |ξ.re|) (h2 : 2 * |(2 * π * m / L : ℝ)| ≤ |ξ.re|) :
    ‖Wm L m ξ‖ ≤ (20 / 3) * (E L + 1) / (1 + |ξ.re|) := by
  set ω : ℝ := 2 * π * m / L with hω
  have hω2 : ω ^ 2 ≤ ξ.re ^ 2 / 4 := by
    have := abs_nonneg ω
    nlinarith [sq_abs ω, sq_abs ξ.re]
  have hne : ω ^ 2 ≠ ξ.re ^ 2 := by
    intro h; nlinarith [sq_abs ξ.re]
  have hfar := Cvs.Finite.CosineModeTransformBounds.norm_windowTransform_cos_far hL m hne
  rw [← hω] at hfar
  have hden : 3 * ξ.re ^ 2 / 4 ≤ |ω ^ 2 - ξ.re ^ 2| := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [sq_nonneg ξ.re])]; linarith
  have hnorm : ‖ξ‖ ≤ 5 / 2 * |ξ.re| := by
    have := Complex.norm_le_abs_re_add_abs_im ξ
    linarith
  have hE := exp_le_E hL.le hξ
  have hre2 : 0 < ξ.re ^ 2 := by nlinarith [sq_abs ξ.re]
  have hE1 : 0 < E L + 1 := by unfold E; positivity
  calc ‖Wm L m ξ‖ ≤ ‖ξ‖ * (Real.exp (L * |ξ.im|) + 1) / |ω ^ 2 - ξ.re ^ 2| := hfar
    _ ≤ (5 / 2 * |ξ.re|) * (E L + 1) / (3 * ξ.re ^ 2 / 4) := by
        gcongr
    _ = (10 / 3) * (E L + 1) / |ξ.re| := by
        rw [← sq_abs ξ.re]
        field_simp
        ring
    _ ≤ (20 / 3) * (E L + 1) / (1 + |ξ.re|) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith

/-- **The crude bound on the strip.** -/
theorem norm_Wm_crude {L : ℝ} (hL : 0 < L) (m : ℤ) {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2) :
    ‖Wm L m ξ‖ ≤ L * E L := by
  refine (Cvs.Finite.CosineModeTransformBounds.norm_windowTransform_cos_le hL.le _ ξ).trans ?_
  exact mul_le_mul_of_nonneg_left (exp_le_E hL.le hξ) hL.le

/-- **A single mode is `O(1/(1 + |Re ξ|))` on the strip.** -/
theorem exists_Wm_bound {L : ℝ} (hL : 0 < L) (m : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 → ‖Wm L m ξ‖ ≤ C / (1 + |ξ.re|) := by
  set ω : ℝ := 2 * π * m / L with hω
  have hE0 : 0 < E L := Real.exp_pos _
  refine ⟨L * E L * (2 * |ω| + 2) + (20 / 3) * (E L + 1), by positivity, fun ξ hξ => ?_⟩
  have hden : 0 < 1 + |ξ.re| := by linarith [abs_nonneg ξ.re]
  rcases le_or_gt |ξ.re| (2 * |ω| + 1) with h | h
  · have hc := norm_Wm_crude hL m hξ
    refine hc.trans ?_
    rw [le_div_iff₀ hden]
    have : L * E L * (1 + |ξ.re|) ≤ L * E L * (2 * |ω| + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [abs_nonneg ω]
  · have hf := norm_Wm_far hL m hξ (by linarith [abs_nonneg ω]) (by linarith)
    refine hf.trans ?_
    have : 0 ≤ L * E L * (2 * |ω| + 2) := by positivity
    exact div_le_div_of_nonneg_right (by linarith) hden.le

/-- **A cosine polynomial's transform is `O(1/(1 + |Re ξ|))` on the strip.** -/
theorem exists_cosPoly_bound {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (mode : ι → ℤ)
    (xi : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf (Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi)) ξ‖
        ≤ C / (1 + |ξ.re|) := by
  choose C hC0 hC using fun i => exists_Wm_bound hL (mode i)
  refine ⟨∑ i, |xi i| * C i, Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hC0 i),
    fun ξ hξ => ?_⟩
  have hden : 0 < 1 + |ξ.re| := by linarith [abs_nonneg ξ.re]
  unfold Cvs.Finite.EvenSectorZeroSide.cosPoly
  rw [Cvs.Finite.CosineModeTransformBounds.windowTransform_sum_cf L xi
    (fun i y => Real.cos (Cvs.Finite.TruncationZeroFreeOffAxes.omega L mode i * y)) (fun i => by fun_prop) ξ]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact hC i ξ hξ

/-! ### The averaged fresh modes -/

/-- The fresh cosines, summed. -/
def avg (L : ℝ) (M₀ N : ℕ) : ℝ → ℝ :=
  fun y => ∑ m : {m : ℕ // m ∈ Finset.Icc 1 N}, Real.cos (2 * π * ((M₀ : ℝ) + (m : ℕ)) / L * y)

/-- The transform of the fresh sum is the sum of the fresh mode transforms. -/
theorem windowTransform_avg (L : ℝ) (M₀ N : ℕ) (ξ : ℂ) :
    Cvs.Detection.windowTransform L (cf (avg L M₀ N)) ξ
      = ∑ m : {m : ℕ // m ∈ Finset.Icc 1 N}, Wm L ((M₀ + (m : ℕ) : ℕ) : ℤ) ξ := by
  unfold avg Wm
  have := Cvs.Finite.CosineModeTransformBounds.windowTransform_sum_cf L (fun _ => (1:ℝ))
    (fun m : {m : ℕ // m ∈ Finset.Icc 1 N} => fun y => Real.cos (2 * π * ((M₀ : ℝ) + (m : ℕ)) / L * y))
    (fun m => by fun_prop) ξ
  simp only [one_mul, Complex.ofReal_one] at this
  rw [this]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  rfl

/-- **The fresh sum, crudely.** -/
theorem norm_avg_crude {L : ℝ} (hL : 0 < L) (M₀ N : ℕ) {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2) :
    ‖Cvs.Detection.windowTransform L (cf (avg L M₀ N)) ξ‖ ≤ N * (L * E L) := by
  rw [windowTransform_avg]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun m _ => norm_Wm_crude hL _ hξ).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Nat.card_Icc, nsmul_eq_mul]
  simp

/-- **The fresh sum, far out**: beyond `2ω_{M₀+N}` and beyond `1`. -/
theorem norm_avg_far {L : ℝ} (hL : 0 < L) (M₀ N : ℕ) {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2)
    (h1 : 1 ≤ |ξ.re|) (h2 : 2 * (2 * π / L * (M₀ + N)) ≤ |ξ.re|) :
    ‖Cvs.Detection.windowTransform L (cf (avg L M₀ N)) ξ‖
      ≤ N * ((20 / 3) * (E L + 1) / (1 + |ξ.re|)) := by
  rw [windowTransform_avg]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m : {m : ℕ // m ∈ Finset.Icc 1 N},
      ‖Wm L ((M₀ + (m : ℕ) : ℕ) : ℤ) ξ‖ ≤ (20 / 3) * (E L + 1) / (1 + |ξ.re|) := by
    intro m
    refine norm_Wm_far hL _ hξ h1 ?_
    have hm : ((m : ℕ) : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp m.2).2
    have hω : |(2 * π * (((M₀ + (m : ℕ) : ℕ) : ℤ) : ℝ) / L : ℝ)| ≤ 2 * π / L * (M₀ + N) := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
      have : 0 ≤ 2 * π / L := by positivity
      calc 2 * π * ((M₀ : ℝ) + (m : ℕ)) / L = 2 * π / L * ((M₀ : ℝ) + (m : ℕ)) := by ring
        _ ≤ 2 * π / L * (M₀ + N) := mul_le_mul_of_nonneg_left (by linarith) this
    linarith
  refine (Finset.sum_le_sum fun m _ => hterm m).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, Nat.card_Icc, nsmul_eq_mul]
  simp

/-- The constants of `Cvs.Finite.ModeTransformLogGrowth`'s bound at height `3/2`. -/
def A (L : ℝ) : ℝ := 2 * L * E L
def B (L : ℝ) : ℝ := 3 * (E L + 1) * (2 * π / L + 3 / 2) / (2 * π / L) ^ 2

theorem A_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ A L := by unfold A E; positivity
theorem B_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ B L := by unfold B E; positivity

/-- **The fresh sum is `A + B·ell` on the strip**, for every `ξ` and `N ≥ 1`. -/
theorem norm_avg_le_ell {L : ℝ} (hL : 0 < L) (M₀ : ℕ) {N : ℕ} (hN : 1 ≤ N) {ξ : ℂ}
    (hξ : |ξ.im| ≤ 3 / 2) :
    ‖Cvs.Detection.windowTransform L (cf (avg L M₀ N)) ξ‖
      ≤ A L + B L * Cvs.Finite.AveragedApproximant.ell M₀ N := by
  rw [windowTransform_avg]
  refine (norm_sum_le _ _).trans ?_
  -- reindex to `Icc (M₀+1) (M₀+N)` and enlarge to `Icc 1 (M₀+N)`
  have hre : ∑ m : {m : ℕ // m ∈ Finset.Icc 1 N}, ‖Wm L ((M₀ + (m : ℕ) : ℕ) : ℤ) ξ‖
      = ∑ m ∈ Finset.Icc (M₀ + 1) (M₀ + N), ‖Wm L (m : ℤ) ξ‖ := by
    rw [Finset.sum_coe_sort (Finset.Icc 1 N) (fun m : ℕ => ‖Wm L ((M₀ + m : ℕ) : ℤ) ξ‖),
      ← Finset.map_add_left_Icc, Finset.sum_map]
    rfl
  rw [hre]
  have hsub : ∑ m ∈ Finset.Icc (M₀ + 1) (M₀ + N), ‖Wm L (m : ℤ) ξ‖
      ≤ ∑ m ∈ Finset.Icc 1 (M₀ + N), ‖Wm L (m : ℤ) ξ‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
      (fun _ _ _ => norm_nonneg _)
  refine hsub.trans ?_
  have h := Cvs.Finite.ModeTransformLogGrowth.sum_norm_windowTransform_cos_le hL (M₀ + N) ξ
  have hW : ∀ m : ℕ, ‖Wm L (m : ℤ) ξ‖
      = ‖Cvs.Detection.windowTransform L (cf fun y => Real.cos (2 * π * m / L * y)) ξ‖ := by
    intro m; unfold Wm; push_cast; rfl
  simp only [hW]
  refine h.trans ?_
  have hE := exp_le_E hL.le hξ
  have hδ : 0 < 2 * π / L := by positivity
  have hlog : 1 + Real.log ((M₀ + N : ℕ) : ℝ) ≤ Cvs.Finite.AveragedApproximant.ell M₀ N := by
    have := Cvs.Finite.AveragedApproximant.log_N_le_ell M₀ N
    unfold Cvs.Finite.AveragedApproximant.ell at this ⊢
    push_cast
    have hMN : (0:ℝ) < M₀ + N := by
      have : (1:ℝ) ≤ N := by exact_mod_cast hN
      linarith [(Nat.cast_nonneg M₀ : (0:ℝ) ≤ M₀)]
    linarith [Real.log_le_log hMN (by linarith : (M₀ : ℝ) + N ≤ 1 + M₀ + N)]
  have hlog0 : 0 ≤ 1 + Real.log ((M₀ + N : ℕ) : ℝ) := by
    have : (1:ℝ) ≤ ((M₀ + N : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ M₀ + N)
    linarith [Real.log_nonneg this]
  have hE0 : 0 < Real.exp (L * |ξ.im|) := Real.exp_pos _
  unfold A B
  have hfac : 3 * (Real.exp (L * |ξ.im|) + 1) * (2 * π / L + |ξ.im|)
      * (1 + Real.log ((M₀ + N : ℕ) : ℝ)) / (2 * π / L) ^ 2
      ≤ 3 * (E L + 1) * (2 * π / L + 3 / 2) / (2 * π / L) ^ 2 * Cvs.Finite.AveragedApproximant.ell M₀ N := by
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h1 : 3 * (Real.exp (L * |ξ.im|) + 1) * (2 * π / L + |ξ.im|)
        ≤ 3 * (E L + 1) * (2 * π / L + 3 / 2) := by
      have := abs_nonneg ξ.im
      have hE1 : 0 ≤ 3 * (E L + 1) := by unfold E; positivity
      gcongr
    exact mul_le_mul h1 hlog hlog0 (by unfold E; positivity)
  have h2 : 2 * L * Real.exp (L * |ξ.im|) ≤ 2 * L * E L :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  linarith

/-- **The uniform envelope**: the fresh average is `C·phi(|Re ξ|)` for every `N ≥ 1`. -/
theorem exists_avg_envelope {L : ℝ} (hL : 0 < L) (M₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ ξ : ℂ, |ξ.im| ≤ 3 / 2 →
      ‖Cvs.Detection.windowTransform L (cf (avg L M₀ N)) ξ‖
        ≤ N * (C * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re|) := by
  set δ : ℝ := 2 * π / L with hδ
  have hδ0 : 0 < δ := by positivity
  set K : ℝ := max (2 * δ) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK2 : 2 * δ ≤ K := le_max_left _ _
  have hE0 : 0 < E L := Real.exp_pos _
  have hA := A_nonneg hL
  have hB := B_nonneg hL
  refine ⟨2 * L * E L + (20 / 3) * (E L + 1) + 2 * (A L + B L) * (M₀ + 1) * K,
    by positivity, fun N hN ξ hξ => ?_⟩
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hre0 : 0 ≤ |ξ.re| := abs_nonneg _
  have hphi := Cvs.Zeta.LogEnvelopeSquareSummable.phi_nonneg hre0
  have hphi1 := Cvs.Zeta.LogEnvelopeSquareSummable.one_div_le_phi hre0
  have hden : 0 < 1 + |ξ.re| := by linarith
  -- the three constants each dominate their case; all are nonnegative
  have hc1 : 0 ≤ 2 * L * E L := by positivity
  have hc2 : 0 ≤ (20 / 3) * (E L + 1) := by positivity
  have hc3 : 0 ≤ 2 * (A L + B L) * (M₀ + 1) * K := by positivity
  rcases le_or_gt |ξ.re| 1 with hsmall | hbig
  · -- crude
    have h := norm_avg_crude hL M₀ N hξ
    refine h.trans ?_
    have : L * E L ≤ 2 * L * E L * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re| := by
      have h1 : 1 / (1 + |ξ.re|) ≥ 1 / 2 := by
        rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hden]; linarith
      nlinarith
    calc (N : ℝ) * (L * E L) ≤ N * (2 * L * E L * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re|) :=
          mul_le_mul_of_nonneg_left this hNpos.le
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hNpos.le
          nlinarith
  · rcases le_or_gt (2 * (δ * (M₀ + N))) |ξ.re| with hfar | hnear
    · -- far
      have h := norm_avg_far hL M₀ N hξ hbig.le (by rw [hδ] at hfar; linarith)
      refine h.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hNpos.le
      calc (20 / 3) * (E L + 1) / (1 + |ξ.re|)
          = (20 / 3) * (E L + 1) * (1 / (1 + |ξ.re|)) := by ring
        _ ≤ (20 / 3) * (E L + 1) * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re| :=
            mul_le_mul_of_nonneg_left hphi1 hc2
        _ ≤ _ := by nlinarith
    · -- near: the logarithmic bound and the monotone envelope
      have h := norm_avg_le_ell hL M₀ hN hξ
      refine h.trans ?_
      have hell1 := Cvs.Finite.AveragedApproximant.one_le_ell M₀ N
      have hMN : (1:ℝ) ≤ M₀ + N := by linarith [(Nat.cast_nonneg M₀ : (0:ℝ) ≤ M₀)]
      -- `ell ≤ 2(M₀+1)·N·phi(M₀+N)`
      have hell : Cvs.Finite.AveragedApproximant.ell M₀ N
          ≤ 2 * (M₀ + 1) * N * Cvs.Zeta.LogEnvelopeSquareSummable.phi ((M₀ : ℝ) + N) := by
        unfold Cvs.Zeta.LogEnvelopeSquareSummable.phi Cvs.Finite.AveragedApproximant.ell
        rw [mul_div_assoc', le_div_iff₀ (by linarith : (0:ℝ) < 1 + ((M₀ : ℝ) + N))]
        have hnum : 0 ≤ 1 + Real.log (1 + M₀ + N) := by
          have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 1 + M₀ + N); linarith
        have hcard : 1 + (M₀ : ℝ) + N ≤ 2 * (M₀ + 1) * N := by
          nlinarith [(Nat.cast_nonneg M₀ : (0:ℝ) ≤ M₀)]
        rw [show (1 : ℝ) + ((M₀ : ℝ) + N) = 1 + M₀ + N by ring]
        nlinarith
      -- `phi(M₀+N) ≤ phi(|Re ξ|/K) ≤ K·phi(|Re ξ|)`
      have hmono : Cvs.Zeta.LogEnvelopeSquareSummable.phi ((M₀ : ℝ) + N)
          ≤ Cvs.Zeta.LogEnvelopeSquareSummable.phi (|ξ.re| / K) := by
        refine Cvs.Zeta.LogEnvelopeSquareSummable.phi_antitone (by positivity) ?_
        rw [div_le_iff₀ (by linarith)]
        calc |ξ.re| ≤ 2 * (δ * (M₀ + N)) := hnear.le
          _ = (2 * δ) * (M₀ + N) := by ring
          _ ≤ K * (M₀ + N) := mul_le_mul_of_nonneg_right hK2 (by linarith)
          _ = (M₀ + N) * K := by ring
      have hscale := Cvs.Zeta.LogEnvelopeSquareSummable.phi_div_le hre0 hK1
      have hphiMN : Cvs.Zeta.LogEnvelopeSquareSummable.phi ((M₀ : ℝ) + N)
          ≤ K * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re| := hmono.trans hscale
      calc A L + B L * Cvs.Finite.AveragedApproximant.ell M₀ N
          ≤ (A L + B L) * Cvs.Finite.AveragedApproximant.ell M₀ N := by nlinarith
        _ ≤ (A L + B L) * (2 * (M₀ + 1) * N * Cvs.Zeta.LogEnvelopeSquareSummable.phi ((M₀ : ℝ) + N)) :=
            mul_le_mul_of_nonneg_left hell (by positivity)
        _ ≤ (A L + B L) * (2 * (M₀ + 1) * N * (K * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re|)) := by
            gcongr
        _ = N * (2 * (A L + B L) * (M₀ + 1) * K * Cvs.Zeta.LogEnvelopeSquareSummable.phi |ξ.re|) := by ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ hNpos.le
            nlinarith

/-- **At a fixed point of the strip, the normalised fresh average vanishes.** -/
theorem tendsto_avg_div {L : ℝ} (hL : 0 < L) (M₀ : ℕ) (s : ℝ) {ξ : ℂ} (hξ : |ξ.im| ≤ 3 / 2) :
    Tendsto (fun N : ℕ => ((s / N : ℝ) : ℂ)
      * Cvs.Detection.windowTransform L (cf (avg L M₀ N)) ξ) atTop (𝓝 0) := by
  have hA := A_nonneg hL
  have hB := B_nonneg hL
  have hlim : Tendsto (fun N : ℕ => |s| * (A L + B L) * (Cvs.Finite.AveragedApproximant.ell M₀ N ^ 2 / N))
      atTop (𝓝 0) := by
    simpa using (Cvs.Finite.AveragedApproximant.tendsto_ell_sq_div M₀).const_mul (|s| * (A L + B L))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hell1 := Cvs.Finite.AveragedApproximant.one_le_ell M₀ N
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hNpos]
  have h := norm_avg_le_ell hL M₀ hN hξ
  calc |s| / N * ‖Cvs.Detection.windowTransform L (cf (avg L M₀ N)) ξ‖
      ≤ |s| / N * (A L + B L * Cvs.Finite.AveragedApproximant.ell M₀ N) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ |s| / N * ((A L + B L) * Cvs.Finite.AveragedApproximant.ell M₀ N ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have e1 : A L ≤ A L * Cvs.Finite.AveragedApproximant.ell M₀ N ^ 2 :=
          le_mul_of_one_le_right hA (by nlinarith)
        have e2 : B L * Cvs.Finite.AveragedApproximant.ell M₀ N
            ≤ B L * Cvs.Finite.AveragedApproximant.ell M₀ N ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) hB
        linarith
    _ = |s| * (A L + B L) * (Cvs.Finite.AveragedApproximant.ell M₀ N ^ 2 / N) := by
        field_simp

end Cvs.Finite.ModeTransformEnvelopes
