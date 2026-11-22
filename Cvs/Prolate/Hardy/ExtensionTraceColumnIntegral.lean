import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CentralRungExpansion
import Cvs.Prolate.Hardy.ColumnRungCoefficients
import Cvs.Prolate.Hardy.FourierDefectColumns

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The extension trace in the rung basis is the exterior-column integral

For any bounded `J : L²(I) → L²(ℝ)`, `Σ_k g(σ_k)‖JQh_k‖² = S_J + O_J` with `S_J = 2∫_{u>1}‖JQe_u‖²` and
`O_J = 2∫_{u>1}⟨JQe_u, JQFe_u⟩`: the two expansions `Qe_u = Σ_k B_{h_k}(u)Qh_k`, `QFe_u = Σ_k σ_kB_{h_k}(u)Qh_k`,
double orthogonality, and dominated convergence under `|e_u| ≤ (2c + 2)/(πu)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Finset

namespace Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx)
open Cvs.Prolate.Hardy.FourierDefectColumns (Fop bandB)
open Cvs.Prolate.Hardy.CentralRungExpansion (hk coef qI continuous_hk)
open Cvs.Prolate.Hardy.ColumnRungCoefficients (eC continuous_eC)
open Cvs.Prolate.Gram.CentralResolventTrace (L2I sigma gpoly)

/-- The target space `L²(ℝ)`. -/
abbrev L2R : Type := Lp ℝ 2 (volume : Measure ℝ)

/-- The central column `Qe_u ∈ L²(I)` (zero for `u ≤ 1`). -/
def colA (c u : ℝ) : L2I := if hu : 1 < u then qI (continuous_eC c hu) else 0

/-- The central column `QFe_u ∈ L²(I)` (zero for `u ≤ 1`). -/
def colF (c u : ℝ) : L2I := if hu : 1 < u then qI (Cvs.Prolate.Hardy.FourierDefectColumns.continuous_Fop c (continuous_eC c hu)) else 0

/-- The extension energy `S_J = 2∫_{u>1}‖JQe_u‖²`. -/
def extS (c : ℝ) (J : L2I →L[ℝ] L2R) : ℝ := 2 * ∫ u in Ioi 1, ‖J (colA c u)‖ ^ 2

/-- The mixed term `O_J = 2∫_{u>1}⟨JQe_u, JQFe_u⟩`. -/
def extO (c : ℝ) (J : L2I →L[ℝ] L2R) : ℝ := 2 * ∫ u in Ioi 1, inner ℝ (J (colA c u)) (J (colF c u))

open Classical in
/-- The `k`-th term `g(σ_k)‖JQh_k‖²` of `Tr(JQGQJ*)` in the rung basis. -/
def eigTerm (c : ℝ) (J : L2I →L[ℝ] L2R) (k : ℕ) : ℝ :=
  if ∃ χ, IsLevelIdx c k χ then gpoly (sigma c k) * ‖J (qI (continuous_hk c k))‖ ^ 2 else 0

/-! ### The expansions of the columns -/

theorem Fop_neg (c : ℝ) (y : ℝ → ℝ) (s : ℝ) : Fop c y (-s) = Fop c y s := by
  unfold Fop; rw [mul_neg, Cvs.Prolate.Hardy.FourierDefectColumns.cosT_neg]

theorem hasSum_colA {c u : ℝ} (hc : c ≠ 0) (hu : 1 < u) :
    HasSum (fun k => bandB c (hk c k) u • qI (continuous_hk c k)) (colA c u) := by
  rw [colA, dif_pos hu]
  have h := Cvs.Prolate.Hardy.CentralRungExpansion.hasSum_qI hc (continuous_eC c hu) (fun t _ => Cvs.Prolate.Hardy.ColumnRungCoefficients.eC_neg c u t)
  simpa only [Cvs.Prolate.Hardy.ColumnRungCoefficients.coef_eC hu] using h

theorem hasSum_colF {c u : ℝ} (hc : c ≠ 0) (hu : 1 < u) :
    HasSum (fun k => (sigma c k * bandB c (hk c k) u) • qI (continuous_hk c k)) (colF c u) := by
  rw [colF, dif_pos hu]
  have h := Cvs.Prolate.Hardy.CentralRungExpansion.hasSum_qI hc (Cvs.Prolate.Hardy.FourierDefectColumns.continuous_Fop c (continuous_eC c hu)) (fun t _ => Fop_neg c _ t)
  simpa only [Cvs.Prolate.Hardy.ColumnRungCoefficients.coef_Fop (continuous_eC c hu), Cvs.Prolate.Hardy.ColumnRungCoefficients.coef_eC hu] using h

theorem bandB_hk_of_not {c : ℝ} {k : ℕ} (h : ¬ ∃ χ, IsLevelIdx c k χ) (u : ℝ) : bandB c (hk c k) u = 0 := by
  rw [Cvs.Prolate.Hardy.CentralRungExpansion.hk_of_not h, Cvs.Prolate.Hardy.ColumnRungCoefficients.bandB_zero]

/-- Bessel: `Σ_{k<N} B_{h_k}(u)² ≤ ∫_{−1}^{1} e_u²`. -/
theorem sum_bandB_sq_le {c u : ℝ} (hc : c ≠ 0) (hu : 1 < u) (N : ℕ) :
    ∑ k ∈ range N, bandB c (hk c k) u ^ 2 ≤ ∫ t in (-1 : ℝ)..1, eC c u t ^ 2 := by
  have h := Cvs.Prolate.Hardy.CentralRungExpansion.hasSum_coef_sq hc (continuous_eC c hu) (fun t _ => Cvs.Prolate.Hardy.ColumnRungCoefficients.eC_neg c u t)
  simp only [Cvs.Prolate.Hardy.ColumnRungCoefficients.coef_eC hu] at h
  exact sum_le_hasSum _ (fun k _ => sq_nonneg _) h

theorem integrableOn_bandB_mul {c : ℝ} (hc : 0 < c) (k j : ℕ) :
    IntegrableOn (fun u => bandB c (hk c k) u * bandB c (hk c j) u) (Ioi 1) := by
  have h1 := (Cvs.Prolate.Hardy.FourierDefectColumns.integrable_bandB_sq hc.le (continuous_hk c k)).integrableOn (s := Ioi 1)
  have h2 := (Cvs.Prolate.Hardy.FourierDefectColumns.integrable_bandB_sq hc.le (continuous_hk c j)).integrableOn (s := Ioi 1)
  refine (h1.add h2).mono' ((Cvs.Prolate.Hardy.FourierDefectColumns.continuous_bandB c (continuous_hk c k)).mul
    (Cvs.Prolate.Hardy.FourierDefectColumns.continuous_bandB c (continuous_hk c j))).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  show ‖bandB c (hk c k) u * bandB c (hk c j) u‖ ≤ bandB c (hk c k) u ^ 2 + bandB c (hk c j) u ^ 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|bandB c (hk c k) u| - |bandB c (hk c j) u|), sq_abs (bandB c (hk c k) u),
    sq_abs (bandB c (hk c j) u)]

theorem integrableOn_inv_sq : IntegrableOn (fun u : ℝ => (u ^ 2)⁻¹) (Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos).congr_fun (fun u hu => ?_) measurableSet_Ioi
  show u ^ (-2 : ℝ) = (u ^ 2)⁻¹
  rw [Real.rpow_neg (by linarith [hu.out]), Real.rpow_two]

open Classical in
/-- **Dominated convergence for the column pairing**: the partial rung sums of `2∫_{u>1}⟨JQe_u, JX_u⟩` are
`Σ_{k<N} m_k(σ_k² − σ_k⁴)‖JQh_k‖²` whenever `X_u = Σ_k m_kB_{h_k}(u)Qh_k` with `|m_k| ≤ 1`. -/
theorem tendsto_sum_colPair {c : ℝ} (hc : 0 < c) (J : L2I →L[ℝ] L2R) (m : ℕ → ℝ)
    (hm : ∀ k, (∃ χ, IsLevelIdx c k χ) → |m k| ≤ 1) (X : ℝ → L2I)
    (hX : ∀ u, 1 < u → HasSum (fun k => (m k * bandB c (hk c k) u) • qI (continuous_hk c k)) (X u)) :
    Tendsto (fun N => ∑ k ∈ range N, (if ∃ χ, IsLevelIdx c k χ then m k * (sigma c k ^ 2 - sigma c k ^ 4) else 0) *
      ‖J (qI (continuous_hk c k))‖ ^ 2) atTop (𝓝 (2 * ∫ u in Ioi 1, inner ℝ (J (colA c u)) (J (X u)))) := by
  classical
  set β : ℕ → ℝ → ℝ := fun k u => bandB c (hk c k) u with hβ
  set φ : ℕ → L2I := fun k => qI (continuous_hk c k) with hφ
  set M : ℕ → ℕ → ℝ := fun k j => inner ℝ (J (φ k)) (J (φ j)) with hM
  set F : ℕ → ℝ → ℝ := fun N u => ∑ k ∈ range N, ∑ j ∈ range N, β k u * (m j * β j u) * M k j with hF
  have hβc : ∀ k, Continuous (β k) := fun k => Cvs.Prolate.Hardy.FourierDefectColumns.continuous_bandB c (continuous_hk c k)
  have hβ0 : ∀ k, ¬ (∃ χ, IsLevelIdx c k χ) → ∀ u, β k u = 0 := fun k h u => bandB_hk_of_not h u
  -- the finite pairings
  have hinner : ∀ N u, F N u = inner ℝ (J (∑ k ∈ range N, β k u • φ k)) (J (∑ j ∈ range N, (m j * β j u) • φ j)) := by
    intro N u
    rw [map_sum, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, real_inner_smul_left, real_inner_smul_right]
    simp only [hM]; ring
  -- pointwise limit
  have hlim : ∀ᵐ u ∂(volume.restrict (Ioi 1)), Tendsto (fun N => F N u) atTop
      (𝓝 (inner ℝ (J (colA c u)) (J (X u)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp_rw [hinner]
    have hA := ((J.continuous.tendsto _).comp (hasSum_colA hc.ne' hu).tendsto_sum_nat)
    have hB := ((J.continuous.tendsto _).comp (hX u hu).tendsto_sum_nat)
    exact hA.inner hB
  -- the bound
  set K : ℝ := ‖J‖ ^ 2 * (2 * ((2 * c + 2) / π) ^ 2) with hK
  have hbound : ∀ N, ∀ᵐ u ∂(volume.restrict (Ioi 1)), ‖F N u‖ ≤ K * (u ^ 2)⁻¹ := by
    intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 1 < u := hu
    have hE := (sum_bandB_sq_le hc.ne' hu' N).trans (Cvs.Prolate.Hardy.ColumnRungCoefficients.integral_eC_sq_le hc.le hu')
    have ha := Cvs.Prolate.Hardy.CentralRungExpansion.norm_sum_sq_le (c := c) (range N) (a := fun k => β k u) (fun k h => hβ0 k h u)
    have hb := Cvs.Prolate.Hardy.CentralRungExpansion.norm_sum_sq_le (c := c) (range N) (a := fun k => m k * β k u)
      (fun k h => by simp only [hβ0 k h u, mul_zero])
    have hmb : ∑ k ∈ range N, (m k * β k u) ^ 2 ≤ ∑ k ∈ range N, β k u ^ 2 := by
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases h : ∃ χ, IsLevelIdx c k χ
      · rw [mul_pow]
        have : m k ^ 2 ≤ 1 := by nlinarith [hm k h, abs_nonneg (m k), sq_abs (m k)]
        nlinarith [sq_nonneg (β k u)]
      · rw [hβ0 k h u]; simp
    set a := ∑ k ∈ range N, β k u • φ k
    set b := ∑ j ∈ range N, (m j * β j u) • φ j
    set E := 2 * ((2 * c + 2) / (π * u)) ^ 2
    have hJa : ‖J a‖ ^ 2 ≤ ‖J‖ ^ 2 * E := by
      calc ‖J a‖ ^ 2 ≤ (‖J‖ * ‖a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (J.le_opNorm a) 2
        _ = ‖J‖ ^ 2 * ‖a‖ ^ 2 := by ring
        _ ≤ ‖J‖ ^ 2 * E := mul_le_mul_of_nonneg_left (ha.trans hE) (sq_nonneg _)
    have hJb : ‖J b‖ ^ 2 ≤ ‖J‖ ^ 2 * E := by
      calc ‖J b‖ ^ 2 ≤ (‖J‖ * ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (J.le_opNorm b) 2
        _ = ‖J‖ ^ 2 * ‖b‖ ^ 2 := by ring
        _ ≤ ‖J‖ ^ 2 * E := mul_le_mul_of_nonneg_left ((hb.trans hmb).trans hE) (sq_nonneg _)
    have hE0 : 0 ≤ ‖J‖ ^ 2 * E := by positivity
    have hab : ‖J a‖ * ‖J b‖ ≤ ‖J‖ ^ 2 * E := by
      nlinarith [norm_nonneg (J a), norm_nonneg (J b), sq_nonneg (‖J a‖ - ‖J b‖)]
    have hEK : ‖J‖ ^ 2 * E = K * (u ^ 2)⁻¹ := by
      simp only [hK, E]
      have : u ≠ 0 := by linarith
      field_simp
    rw [hinner, Real.norm_eq_abs, ← hEK]
    exact (abs_real_inner_le_norm _ _).trans hab
  have hFm : ∀ N, AEStronglyMeasurable (F N) (volume.restrict (Ioi 1)) := by
    intro N
    refine Continuous.aestronglyMeasurable ?_
    simp only [hF]
    exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun j _ =>
      ((hβc k).mul (continuous_const.mul (hβc j))).mul continuous_const
  have hDCT := tendsto_integral_of_dominated_convergence (fun u => K * (u ^ 2)⁻¹) hFm
    (integrableOn_inv_sq.const_mul K) hbound hlim
  -- the integrals of the partial pairings
  have hint : ∀ N, 2 * ∫ u in Ioi 1, F N u = ∑ k ∈ range N,
      (if ∃ χ, IsLevelIdx c k χ then m k * (sigma c k ^ 2 - sigma c k ^ 4) else 0) *
        ‖J (qI (continuous_hk c k))‖ ^ 2 := by
    intro N
    have hij : ∀ k j, IntegrableOn (fun u => β k u * (m j * β j u) * M k j) (Ioi 1) := by
      intro k j
      have e : (fun u => β k u * (m j * β j u) * M k j) =
          fun u => m j * M k j * (bandB c (hk c k) u * bandB c (hk c j) u) := by
        ext u; simp only [hβ]; ring
      rw [e]
      exact (integrableOn_bandB_mul hc k j).const_mul _
    simp only [hF]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hij k j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_finsetSum _ fun j _ => hij k j, Finset.mul_sum]
    have hterm : ∀ j, 2 * ∫ u in Ioi 1, β k u * (m j * β j u) * M k j =
        m j * M k j * (2 * ∫ u in Ioi 1, β k u * β j u) := by
      intro j
      rw [show (fun u => β k u * (m j * β j u) * M k j) = fun u => m j * M k j * (β k u * β j u) by ext u; ring,
        integral_const_mul]; ring
    simp_rw [hterm]
    by_cases hkl : ∃ χ, IsLevelIdx c k χ
    · rw [if_pos hkl, Finset.sum_eq_single k]
      · rw [Cvs.Prolate.Hardy.ColumnRungCoefficients.integral_bandB_mul hc hkl hkl, if_pos rfl, ← real_inner_self_eq_norm_sq]
        simp only [hM, hφ]; ring
      · intro j _ hjk
        by_cases hjl : ∃ χ, IsLevelIdx c j χ
        · rw [Cvs.Prolate.Hardy.ColumnRungCoefficients.integral_bandB_mul hc hkl hjl, if_neg (Ne.symm hjk), mul_zero]
        · simp [hβ0 j hjl]
      · intro h; exact absurd hk h
    · rw [if_neg hkl, zero_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hβ0 k hkl]
  have := hDCT.const_mul 2
  simp_rw [hint] at this
  exact this

open Classical in
/-- The `S_J` part `(σ_k² − σ_k⁴)‖JQh_k‖²`. -/
def termS (c : ℝ) (J : L2I →L[ℝ] L2R) (k : ℕ) : ℝ :=
  (if ∃ χ, IsLevelIdx c k χ then 1 * (sigma c k ^ 2 - sigma c k ^ 4) else 0) * ‖J (qI (continuous_hk c k))‖ ^ 2

open Classical in
/-- The `O_J` part `σ_k(σ_k² − σ_k⁴)‖JQh_k‖²`. -/
def termO (c : ℝ) (J : L2I →L[ℝ] L2R) (k : ℕ) : ℝ :=
  (if ∃ χ, IsLevelIdx c k χ then sigma c k * (sigma c k ^ 2 - sigma c k ^ 4) else 0) *
    ‖J (qI (continuous_hk c k))‖ ^ 2

theorem termS_nonneg {c : ℝ} (hc : 0 < c) (J : L2I →L[ℝ] L2R) (k : ℕ) : 0 ≤ termS c J k := by
  unfold termS
  split_ifs with h
  · have h1 := Cvs.Prolate.Gram.CentralResolventTrace.abs_sigma_le_one hc h
    have h2 : sigma c k ^ 2 ≤ 1 := by nlinarith [abs_nonneg (sigma c k), sq_abs (sigma c k)]
    have : 0 ≤ sigma c k ^ 2 - sigma c k ^ 4 := by nlinarith [sq_nonneg (sigma c k)]
    positivity
  · simp

theorem abs_termO_le {c : ℝ} (hc : 0 < c) (J : L2I →L[ℝ] L2R) (k : ℕ) : ‖termO c J k‖ ≤ termS c J k := by
  unfold termO termS
  split_ifs with h
  · have h1 := Cvs.Prolate.Gram.CentralResolventTrace.abs_sigma_le_one hc h
    have h2 : sigma c k ^ 2 ≤ 1 := by nlinarith [abs_nonneg (sigma c k), sq_abs (sigma c k)]
    have h3 : 0 ≤ sigma c k ^ 2 - sigma c k ^ 4 := by nlinarith [sq_nonneg (sigma c k)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg (sq_nonneg ‖J (qI (continuous_hk c k))‖)]
    have := mul_le_mul_of_nonneg_right h1 h3
    nlinarith [sq_nonneg ‖J (qI (continuous_hk c k))‖]
  · simp

/-- `Σ_k (σ_k² − σ_k⁴)‖JQh_k‖² = S_J`. -/
theorem hasSum_termS {c : ℝ} (hc : 0 < c) (J : L2I →L[ℝ] L2R) : HasSum (termS c J) (extS c J) := by
  have h := tendsto_sum_colPair hc J (fun _ => 1) (fun k _ => by simp) (colA c)
    (fun u hu => by simpa only [one_mul] using hasSum_colA hc.ne' hu)
  simp_rw [real_inner_self_eq_norm_sq] at h
  exact (hasSum_iff_tendsto_nat_of_nonneg (termS_nonneg hc J) _).2 h

/-- `Σ_k σ_k(σ_k² − σ_k⁴)‖JQh_k‖² = O_J`. -/
theorem hasSum_termO {c : ℝ} (hc : 0 < c) (J : L2I →L[ℝ] L2R) : HasSum (termO c J) (extO c J) := by
  have h := tendsto_sum_colPair hc J (sigma c) (fun k hk => Cvs.Prolate.Gram.CentralResolventTrace.abs_sigma_le_one hc hk) (colF c)
    (fun u hu => hasSum_colF hc.ne' hu)
  have hs : Summable (termO c J) :=
    Summable.of_norm_bounded (hasSum_termS hc J).summable (abs_termO_le hc J)
  have h2 := hs.hasSum.tendsto_sum_nat
  have : ∑' k, termO c J k = extO c J := tendsto_nhds_unique h2 h
  rw [← this]; exact hs.hasSum

/-- **The trace in two bases**: `Σ_k g(σ_k)‖JQh_k‖² = S_J + O_J` for every bounded `J : L²(I) → L²(ℝ)`. -/
theorem hasSum_eigTerm {c : ℝ} (hc : 0 < c) (J : L2I →L[ℝ] L2R) :
    HasSum (eigTerm c J) (extS c J + extO c J) := by
  refine ((hasSum_termS hc J).add (hasSum_termO hc J)).congr_fun fun k => ?_
  unfold eigTerm termS termO
  split_ifs with h
  · simp only [gpoly]; ring
  · simp

end Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral

end
