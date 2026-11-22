import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.CleanBandDilation
import Cvs.L2a.CornerSplitSqrtFloor
import Cvs.L2a.DilationCornerSplit
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.QIdentityComplexWeight
import Cvs.L2a.QIdentityCutPoint
import Cvs.L2a.QIdentityRealWeight
import Cvs.L2a.ReflectionFloor
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungCauchySplit
import Cvs.Prolate.RungDecayBeyondEdge
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Upstream.CosineTransformDilation
import Cvs.Upstream.CosineTransformHalfLine
import Cvs.Upstream.QuinticSmoothStep

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut kernels: CK (i) and (ii)

One complex Q-step on each transition of the quintic partition gives `Dbot = −2Σ_m∫ū𝔅_m + Γ_bot` and
`Dtop = Σ_m C_m + 𝒞_a + R_top`, with `𝔅_m`, `C_m` the cut samples at `x₀ = m` and `x₀ = M`. A Q-step in `t` on `(M, ∞)` gives
`𝒞_a = 𝔇 − 𝔈₁`; a weight-one `t`-step followed by an `x`-step on `[M − δ, M]` gives `R_top^far = 𝔈₁ + 𝔈_V − 𝔗₂`,
the double boundary `𝔇` being common to both.
-/

noncomputable section

namespace Cvs.L2a.CutKernels

open Real Set Filter Topology MeasureTheory Complex
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts Cvs.L2a.CleanBandDilation Cvs.L2a.QIdentityComplexWeight Cvs.Prolate.RungCauchySplit
open scoped ComplexConjugate

variable {ι : Type} [Fintype ι]

/-- **The Q-identity on `(α, ∞)`**: with `wψe`, `eψR` integrable on `(α, ∞)` and `B(T) → 0`,
`∫_{(α,∞)} wψe = ∫_{(α,∞)} eψR − B(α)`. -/
theorem ibpC_Ioi {g g₁ g₂ : ℝ → ℝ} {w w₁ w₂ : ℝ → ℂ} {c χ y α : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hy : 0 < y) (hα : 1 < α)
    (hw : ∀ x ∈ Ici α, HasDerivAt w (w₁ x) x) (hw₁ : ∀ x ∈ Ici α, HasDerivAt w₁ (w₂ x) x)
    (hw₂ : ContinuousOn w₂ (Ici α))
    (hL : IntegrableOn (fun x => w x * (psi c g x : ℂ) * eF c y x) (Ioi α))
    (hR : IntegrableOn (fun x => eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x) (Ioi α))
    (hB : Tendsto (fun T => bBc w w₁ c χ g y T) atTop (𝓝 0)) :
    ∫ x in Ioi α, w x * (psi c g x : ℂ) * eF c y x
      = (∫ x in Ioi α, eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x) - bBc w w₁ c χ g y α := by
  have hlim : Tendsto (fun T => ∫ x in α..T, w x * (psi c g x : ℂ) * eF c y x) atTop
      (𝓝 ((∫ x in Ioi α, eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x) + (0 - bBc w w₁ c χ g y α))) := by
    have h := (intervalIntegral_tendsto_integral_Ioi α hR tendsto_id).add (hB.sub_const (bBc w w₁ c χ g y α))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop α] with T hT
    rw [id, ibpC_Icc hg hg₁ hg₂c hang hc hy hα hT (fun x hx => hw x hx.1) (fun x hx => hw₁ x hx.1)
      (hw₂.mono Icc_subset_Ici_self)]
  rw [tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi α hL tendsto_id) hlim]
  ring

/-- `B` sees only `w(x)` and `w′(x)`. -/
theorem bBc_congr {w w₁ v v₁ : ℝ → ℂ} {c χ y x : ℝ} {g : ℝ → ℝ} (h0 : w x = v x) (h1 : w₁ x = v₁ x) :
    bBc w w₁ c χ g y x = bBc v v₁ c χ g y x := by
  unfold bBc gWc gWc₁; rw [h0, h1]

/-! ### Far decay of the Q-identity on `(α, ∞)` at `y > 1` -/

/-- Continuity on `[α, ∞)` and an eventual `K/t²` bound give integrability on `(α, ∞)`. -/
theorem integrableOn_Ioi_of_le_div_sq {f : ℝ → ℂ} {α : ℝ} (hf : ContinuousOn f (Ici α))
    (hK : ∃ K, ∀ᶠ t in atTop, ‖f t‖ ≤ K / t ^ 2) : IntegrableOn f (Ioi α) := by
  obtain ⟨K, hK⟩ := hK
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hK
  set T := max (max T₀ α) 1 with hT
  have hαT : α ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hT0 : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [← Ioc_union_Ioi_eq_Ioi hαT]
  refine IntegrableOn.union ?_ ?_
  · exact ((hf.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT0).const_mul K)
      ((hf.mono fun t ht => le_of_lt (lt_of_le_of_lt hαT ht)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hT0 ht
    have h := hT₀ t ((le_max_left _ _).trans ((le_max_left _ _).trans (le_of_lt ht)))
    rw [Real.rpow_neg ht0.le, Real.rpow_two]
    calc ‖f t‖ ≤ K / t ^ 2 := h
      _ = K * (t ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- An eventual `K/t` bound gives the limit `0`. -/
theorem tendsto_zero_of_le_div {f : ℝ → ℂ} (hK : ∃ K, ∀ᶠ t in atTop, ‖f t‖ ≤ K / t) :
    Tendsto f atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hK
  exact squeeze_zero_norm' hK (tendsto_const_nhds.div_atTop tendsto_id)

/-- The rung decays like `1/t` and its `u` grows at most like `t` (Cvs.Prolate.RungDecayBeyondEdge). -/
theorem psi_rungU_bounds {g g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c) :
    ∃ Ψ U, 0 ≤ Ψ ∧ 0 ≤ U ∧ ∀ t, 1 ≤ t → |psi c g t| ≤ Ψ / t ∧ |rungU c g t| ≤ U * t := by
  refine ⟨_, _, ?_, ?_, fun t ht => ⟨Cvs.Prolate.RungDecayBeyondEdge.abs_psi_le hg hg₁ hg₂c hc ht,
    Cvs.Prolate.RungDecayBeyondEdge.abs_rungU_le hg hg₁ hg₂c hc ht⟩⟩
  · have h0 : 0 ≤ ∫ s in (-1 : ℝ)..1, |g₂ s| :=
      intervalIntegral.integral_nonneg (by norm_num) fun s _ => abs_nonneg _
    positivity
  · have h0 : 0 ≤ ∫ s in (-1 : ℝ)..1, 2 * |g₁ s| + |g₂ s| :=
      intervalIntegral.integral_nonneg (by norm_num) fun s _ => by positivity
    positivity

/-- For `y > 1`, `χ ≥ 0`, `t ≥ 1` and `t ≥ 2 + 2/(y² − 1)`: `|Q| ≥ (c²(y² − 1)/2)t²`. -/
theorem norm_qQ_ge_far {c χ y t : ℝ} (hχ0 : 0 ≤ χ) (hy : 1 < y) (ht1 : 1 ≤ t)
    (ht : 2 + 2 / (y ^ 2 - 1) ≤ t) : c ^ 2 * (y ^ 2 - 1) / 2 * t ^ 2 ≤ ‖qQ c χ y t‖ := by
  have hs : 0 < y ^ 2 - 1 := by nlinarith
  have hst : 2 * (y ^ 2 - 1) + 2 ≤ (y ^ 2 - 1) * t := by
    have h := mul_le_mul_of_nonneg_left ht hs.le
    rw [mul_add, mul_div_cancel₀ _ hs.ne'] at h
    linarith
  have htt : t ≤ t ^ 2 := by nlinarith
  have h1 : 1 ≤ (y ^ 2 - 1) * (t ^ 2 / 2 - 1) := by nlinarith
  refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  rw [qQ_re]
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith [mul_le_mul_of_nonneg_left h1 hc2]

/-- **The far remainder decays**: for `y > 1`, `|w| ≤ C`, `|w′|, |w″| ≤ C/t` give `|R[w]| ≤ K/t`. -/
theorem norm_rRc_le_far {w w₁ w₂ : ℝ → ℂ} {c χ y : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hy : 1 < y)
    (hw : ∃ C, ∀ᶠ t in atTop, ‖w t‖ ≤ C ∧ ‖w₁ t‖ ≤ C / t ∧ ‖w₂ t‖ ≤ C / t) :
    ∃ K, ∀ᶠ t in atTop, ‖rRc w w₁ w₂ c χ y t‖ ≤ K / t := by
  obtain ⟨C, hC⟩ := hw
  have hC0 : 0 ≤ C := by
    obtain ⟨t, ht⟩ := hC.exists
    exact (norm_nonneg _).trans ht.1
  have hs : 0 < y ^ 2 - 1 := by nlinarith
  have hy0 : 0 < y := by linarith
  set k := c ^ 2 * (y ^ 2 - 1) / 2 with hk
  set E := 2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y with hE
  set F := 2 * c ^ 2 * (y ^ 2 - 1) with hF
  have hk0 : 0 < k := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hF0 : 0 ≤ F := by positivity
  have hcy : 0 ≤ c * y := by positivity
  refine ⟨C * ((3 + 2 * (c * y)) / k + (4 * E + 2 * (c * y) * E + F) / k ^ 2 + 2 * E ^ 2 / k ^ 3), ?_⟩
  filter_upwards [hC, eventually_ge_atTop (max 1 (2 + 2 / (y ^ 2 - 1)))] with t ht' ht
  obtain ⟨h0, h1, h2⟩ := ht'
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hQ : k * t ^ 2 ≤ ‖qQ c χ y t‖ := norm_qQ_ge_far hχ0 hy ht1 ((le_max_right _ _).trans ht)
  have hkt : 0 < k * t ^ 2 := by positivity
  have hQ0 : qQ c χ y t ≠ 0 := norm_pos_iff.1 (hkt.trans_le hQ)
  have hp0 : 0 ≤ pP t := by unfold pP; nlinarith
  have hp : pP t ≤ t ^ 2 := by unfold pP; linarith
  have hQ₁ : ‖qQ₁ c y t‖ ≤ E * t := norm_qQ₁_le hc ht1 hy.le
  have hQ₂ : ‖qQ₂ c y‖ = F := norm_qQ₂_eq hy.le
  have htt : t ^ 2 ≤ t ^ 3 := by nlinarith
  have hA₁ : ‖aC₁ w₁ w₂ c y t‖ ≤ C * (3 + 2 * (c * y)) * t := by
    refine (norm_aC₁_le hc.le hy0.le ht1).trans ?_
    calc (2 * t + 2 * (c * y) * pP t) * ‖w₁ t‖ + pP t * ‖w₂ t‖
        ≤ (2 * t + 2 * (c * y) * t ^ 2) * (C / t) + t ^ 2 * (C / t) := by gcongr
      _ = C * (2 + 2 * (c * y) * t + t) := by field_simp
      _ ≤ C * (3 + 2 * (c * y)) * t := by nlinarith
  have hA₂ : ‖aC₂ w w₁ c y t‖ ≤ C * (4 * E + 2 * (c * y) * E + F) * t ^ 3 := by
    refine (norm_aC₂_le hc.le hy0.le ht1).trans ?_
    rw [hQ₂]
    calc ((2 * t + 2 * (c * y) * pP t) * ‖qQ₁ c y t‖ + pP t * F) * ‖w t‖ + 2 * pP t * ‖qQ₁ c y t‖ * ‖w₁ t‖
        ≤ ((2 * t + 2 * (c * y) * t ^ 2) * (E * t) + t ^ 2 * F) * C + 2 * t ^ 2 * (E * t) * (C / t) := by
          gcongr
      _ = C * ((4 * E + F) * t ^ 2 + 2 * (c * y) * E * t ^ 3) := by field_simp; ring
      _ ≤ C * (4 * E + 2 * (c * y) * E + F) * t ^ 3 := by
          have : (4 * E + F) * t ^ 2 ≤ (4 * E + F) * t ^ 3 := mul_le_mul_of_nonneg_left htt (by positivity)
          nlinarith
  have hA₃ : ‖aC₃ w c y t‖ ≤ 2 * E ^ 2 * C * t ^ 4 := by
    rw [norm_aC₃_eq ht1]
    calc 2 * pP t * ‖qQ₁ c y t‖ ^ 2 * ‖w t‖ ≤ 2 * t ^ 2 * (E * t) ^ 2 * C := by gcongr
      _ = 2 * E ^ 2 * C * t ^ 4 := by ring
  refine (norm_rRc_le hQ0).trans ?_
  have e₁ : ‖aC₁ w₁ w₂ c y t‖ / ‖qQ c χ y t‖ ≤ C * (3 + 2 * (c * y)) / k / t :=
    calc ‖aC₁ w₁ w₂ c y t‖ / ‖qQ c χ y t‖ ≤ C * (3 + 2 * (c * y)) * t / (k * t ^ 2) :=
          div_le_div₀ (by positivity) hA₁ hkt hQ
      _ = C * (3 + 2 * (c * y)) / k / t := by field_simp
  have e₂ : ‖aC₂ w w₁ c y t‖ / ‖qQ c χ y t‖ ^ 2 ≤ C * (4 * E + 2 * (c * y) * E + F) / k ^ 2 / t :=
    calc ‖aC₂ w w₁ c y t‖ / ‖qQ c χ y t‖ ^ 2 ≤ C * (4 * E + 2 * (c * y) * E + F) * t ^ 3 / (k * t ^ 2) ^ 2 :=
          div_le_div₀ (by positivity) hA₂ (by positivity) (pow_le_pow_left₀ hkt.le hQ 2)
      _ = C * (4 * E + 2 * (c * y) * E + F) / k ^ 2 / t := by field_simp
  have e₃ : ‖aC₃ w c y t‖ / ‖qQ c χ y t‖ ^ 3 ≤ 2 * E ^ 2 * C / k ^ 3 / t :=
    calc ‖aC₃ w c y t‖ / ‖qQ c χ y t‖ ^ 3 ≤ 2 * E ^ 2 * C * t ^ 4 / (k * t ^ 2) ^ 3 :=
          div_le_div₀ (by positivity) hA₃ (by positivity) (pow_le_pow_left₀ hkt.le hQ 3)
      _ = 2 * E ^ 2 * C / k ^ 3 / t / t := by field_simp
      _ ≤ 2 * E ^ 2 * C / k ^ 3 / t := div_le_self (by positivity) ht1
  calc ‖aC₁ w₁ w₂ c y t‖ / ‖qQ c χ y t‖ + ‖aC₂ w w₁ c y t‖ / ‖qQ c χ y t‖ ^ 2
        + ‖aC₃ w c y t‖ / ‖qQ c χ y t‖ ^ 3
      ≤ C * (3 + 2 * (c * y)) / k / t + C * (4 * E + 2 * (c * y) * E + F) / k ^ 2 / t
        + 2 * E ^ 2 * C / k ^ 3 / t := add_le_add (add_le_add e₁ e₂) e₃
    _ = C * ((3 + 2 * (c * y)) / k + (4 * E + 2 * (c * y) * E + F) / k ^ 2 + 2 * E ^ 2 / k ^ 3) / t := by
        ring

/-- **The far boundary term decays**: for `y > 1`, `|w| ≤ C`, `|w′| ≤ C/t` give `|B[w]| ≤ K/t`. -/
theorem norm_bBc_le_far {g g₁ g₂ : ℝ → ℝ} {w w₁ : ℝ → ℂ} {c χ y : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hy : 1 < y)
    (hw : ∃ C, ∀ᶠ t in atTop, ‖w t‖ ≤ C ∧ ‖w₁ t‖ ≤ C / t) :
    ∃ K, ∀ᶠ t in atTop, ‖bBc w w₁ c χ g y t‖ ≤ K / t := by
  obtain ⟨C, hC⟩ := hw
  have hC0 : 0 ≤ C := by
    obtain ⟨t, ht⟩ := hC.exists
    exact (norm_nonneg _).trans ht.1
  obtain ⟨Ψ, U, hΨ0, hU0, hΨU⟩ := psi_rungU_bounds hg hg₁ hg₂c hc
  have hs : 0 < y ^ 2 - 1 := by nlinarith
  have hy0 : 0 < y := by linarith
  set k := c ^ 2 * (y ^ 2 - 1) / 2 with hk
  set E := 2 * c ^ 2 * (y ^ 2 - 1) + 2 * c * y with hE
  have hk0 : 0 < k := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hcy : 0 ≤ c * y := by positivity
  refine ⟨C * U / k + Ψ * (C / k + C * E / k ^ 2 + c * y * C / k), ?_⟩
  filter_upwards [hC, eventually_ge_atTop (max 1 (2 + 2 / (y ^ 2 - 1)))] with t ht' ht
  obtain ⟨h0, h1⟩ := ht'
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  obtain ⟨hψ, hu⟩ := hΨU t ht1
  have hQ : k * t ^ 2 ≤ ‖qQ c χ y t‖ := norm_qQ_ge_far hχ0 hy ht1 ((le_max_right _ _).trans ht)
  have hkt : 0 < k * t ^ 2 := by positivity
  have hQn : 0 < ‖qQ c χ y t‖ := hkt.trans_le hQ
  have hQ0 : qQ c χ y t ≠ 0 := norm_pos_iff.1 hQn
  have hp0 : 0 ≤ pP t := by unfold pP; nlinarith
  have hp : pP t ≤ t ^ 2 := by unfold pP; linarith
  have hQ₁ : ‖qQ₁ c y t‖ ≤ E * t := norm_qQ₁_le hc ht1 hy.le
  have hG : ‖gWc w c χ y t‖ ≤ C / (k * t ^ 2) := by
    unfold gWc; rw [norm_div]; exact div_le_div₀ hC0 h0 hkt hQ
  have hG₁ : ‖gWc₁ w w₁ c χ y t‖ ≤ (C / t) / (k * t ^ 2) + C * (E * t) / (k * t ^ 2) ^ 2 := by
    unfold gWc₁
    rw [norm_div, norm_pow]
    have hn : ‖w₁ t * qQ c χ y t - w t * qQ₁ c y t‖ ≤ ‖w₁ t‖ * ‖qQ c χ y t‖ + ‖w t‖ * ‖qQ₁ c y t‖ := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_); rw [norm_mul, norm_mul]
    have hQn' := hQn.ne'
    calc ‖w₁ t * qQ c χ y t - w t * qQ₁ c y t‖ / ‖qQ c χ y t‖ ^ 2
        ≤ (‖w₁ t‖ * ‖qQ c χ y t‖ + ‖w t‖ * ‖qQ₁ c y t‖) / ‖qQ c χ y t‖ ^ 2 := by gcongr
      _ = ‖w₁ t‖ / ‖qQ c χ y t‖ + ‖w t‖ * ‖qQ₁ c y t‖ / ‖qQ c χ y t‖ ^ 2 := by field_simp
      _ ≤ (C / t) / (k * t ^ 2) + C * (E * t) / (k * t ^ 2) ^ 2 := by
          gcongr ?_ + ?_
          · exact div_le_div₀ (by positivity) h1 hkt hQ
          · exact div_le_div₀ (by positivity) (mul_le_mul h0 hQ₁ (norm_nonneg _) hC0) (by positivity)
              (pow_le_pow_left₀ hkt.le hQ 2)
  have hB : ‖bBc w w₁ c χ g y t‖
      ≤ ‖gWc w c χ y t‖ * |rungU c g t| + pP t * (‖gWc₁ w w₁ c χ y t‖ + c * y * ‖gWc w c χ y t‖) * |psi c g t| := by
    unfold bBc
    rw [norm_mul, (continuous_eF c y).2, one_mul]
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    gcongr
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul, abs_of_pos hc,
      abs_of_pos hy0, le_refl]
  refine hB.trans ?_
  have hb1 : ‖gWc w c χ y t‖ * |rungU c g t| ≤ C * U / k / t :=
    calc ‖gWc w c χ y t‖ * |rungU c g t| ≤ C / (k * t ^ 2) * (U * t) :=
          mul_le_mul hG hu (abs_nonneg _) (by positivity)
      _ = C * U / k / t := by field_simp
  have hb2 : pP t * (‖gWc₁ w w₁ c χ y t‖ + c * y * ‖gWc w c χ y t‖) * |psi c g t|
      ≤ Ψ * (C / k + C * E / k ^ 2 + c * y * C / k) / t :=
    calc pP t * (‖gWc₁ w w₁ c χ y t‖ + c * y * ‖gWc w c χ y t‖) * |psi c g t|
        ≤ t ^ 2 * (((C / t) / (k * t ^ 2) + C * (E * t) / (k * t ^ 2) ^ 2) + c * y * (C / (k * t ^ 2)))
          * (Ψ / t) := by gcongr
      _ = Ψ * ((C / k + C * E / k ^ 2) / t + c * y * C / k) / t := by field_simp
      _ ≤ Ψ * ((C / k + C * E / k ^ 2) + c * y * C / k) / t := by
          gcongr
          exact div_le_self (by positivity) ht1
  calc ‖gWc w c χ y t‖ * |rungU c g t| + pP t * (‖gWc₁ w w₁ c χ y t‖ + c * y * ‖gWc w c χ y t‖) * |psi c g t|
      ≤ C * U / k / t + Ψ * (C / k + C * E / k ^ 2 + c * y * C / k) / t := add_le_add hb1 hb2
    _ = (C * U / k + Ψ * (C / k + C * E / k ^ 2 + c * y * C / k)) / t := by ring

/-- `eψR[w]` is integrable on `(α, ∞)` for `y > 1` and a weight with the far bounds. -/
theorem integrableOn_eψR_far {g g₁ g₂ : ℝ → ℝ} {w w₁ w₂ : ℝ → ℂ} {c χ y α : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ0 : 0 ≤ χ) (hy : 1 < y) (hα : 1 < α)
    (hwc : ContinuousOn w (Ici α)) (hw₁c : ContinuousOn w₁ (Ici α)) (hw₂c : ContinuousOn w₂ (Ici α))
    (hw : ∃ C, ∀ᶠ t in atTop, ‖w t‖ ≤ C ∧ ‖w₁ t‖ ≤ C / t ∧ ‖w₂ t‖ ≤ C / t) :
    IntegrableOn (fun x => eF c y x * (psi c g x : ℂ) * rRc w w₁ w₂ c χ y x) (Ioi α) := by
  obtain ⟨-, -, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  have hQ : ∀ x ∈ Ici α, qQ c χ y x ≠ 0 := fun x hx =>
    Cvs.L2a.QIdentityRealWeight.qQ_ne_zero_of_pos hc (by linarith [mem_Ici.1 hx]) (by linarith)
  refine integrableOn_Ioi_of_le_div_sq (((continuous_eF c y).1.continuousOn.mul
    (continuous_ofReal.comp hψc).continuousOn).mul (continuousOn_gWc_rRc hwc hw₁c hw₂c hQ).2.2) ?_
  obtain ⟨K, hK⟩ := norm_rRc_le_far hc hχ0 hy hw
  obtain ⟨Ψ, U, hΨ0, -, hΨU⟩ := psi_rungU_bounds hg hg₁ hg₂c hc
  refine ⟨Ψ * K, ?_⟩
  filter_upwards [hK, eventually_ge_atTop 1] with t hR ht
  have ht0 : 0 < t := by linarith
  have hψ := (hΨU t ht).1
  rw [norm_mul, norm_mul, (continuous_eF c y).2, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |psi c g t| * ‖rRc w w₁ w₂ c χ y t‖ ≤ (Ψ / t) * (K / t) :=
        mul_le_mul hψ hR (norm_nonneg _) ((abs_nonneg _).trans hψ)
    _ = Ψ * K / t ^ 2 := by field_simp

/-- `wψe` is integrable on `(α, ∞)` for a weight continuous on `[α, ∞)` with `|w| ≤ C/t`. -/
theorem integrableOn_wψe_far {g g₁ g₂ : ℝ → ℝ} {w : ℝ → ℂ} {c χ y α : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hwc : ContinuousOn w (Ici α)) (hw : ∃ C, ∀ᶠ t in atTop, ‖w t‖ ≤ C / t) :
    IntegrableOn (fun x => w x * (psi c g x : ℂ) * eF c y x) (Ioi α) := by
  obtain ⟨-, -, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  refine integrableOn_Ioi_of_le_div_sq ((hwc.mul (continuous_ofReal.comp hψc).continuousOn).mul
    (continuous_eF c y).1.continuousOn) ?_
  obtain ⟨C, hC⟩ := hw
  obtain ⟨Ψ, U, hΨ0, -, hΨU⟩ := psi_rungU_bounds hg hg₁ hg₂c hc
  refine ⟨C * Ψ, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with t hw ht
  have ht0 : 0 < t := by linarith
  have hψ := (hΨU t ht).1
  rw [norm_mul, norm_mul, (continuous_eF c y).2, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖w t‖ * |psi c g t| ≤ (C / t) * (Ψ / t) := mul_le_mul hw hψ (abs_nonneg _) ((norm_nonneg _).trans hw)
    _ = C * Ψ / t ^ 2 := by field_simp

/-! ### The dilate pairing and the cosine transform of a cut -/

/-- An indicator of a continuous function on `(α, β]` is in `L² ∩ L¹`. -/
theorem memLp_indicator_Ioc {f : ℝ → ℝ} (hf : Continuous f) (α β : ℝ) :
    MemLp ((Ioc α β).indicator f) 2 volume ∧ Integrable ((Ioc α β).indicator f) := by
  have hmeas : AEStronglyMeasurable ((Ioc α β).indicator f) volume :=
    (hf.measurable.indicator measurableSet_Ioc).aestronglyMeasurable
  have hi : IntegrableOn f (Ioc α β) := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 ?_, (integrable_indicator_iff measurableSet_Ioc).2 hi⟩
  have e : (fun x => ‖(Ioc α β).indicator f x‖ ^ 2) = (Ioc α β).indicator (fun x => ‖f x‖ ^ 2) := by
    funext x; by_cases hx : x ∈ Ioc α β <;> simp [hx]
  rw [e]
  exact (integrable_indicator_iff measurableSet_Ioc).2
    (((hf.norm.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self)

/-- **The cosine transform of a dilated cut**: for `0 ≤ α ≤ β`, `m > 0` and continuous `f`,
`calK(1_(α,β]f(m·))(x) = (κ/m)∫_α^β f(ξ)cos(cξx/m) dξ` almost everywhere. -/
theorem calK_dil_indicator {c m α β : ℝ} (hc : 0 < c) (hm : 0 < m) (hα : 0 ≤ α) (hαβ : α ≤ β)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Cvs.Upstream.CosineTransformHalfLine.calK c (fun s => (((Ioc α β).indicator f (m * s) : ℝ) : ℂ)) =ᵐ[volume]
      fun x => ((√(2 * c / π) / m * ∫ ξ in α..β, f ξ * Real.cos (c * ξ * (x / m)) : ℝ) : ℂ) := by
  set h : ℝ → ℝ := fun s => (Ioc α β).indicator f (m * s) with hh
  have he : h = (Ioc (α / m) (β / m)).indicator (fun s => f (m * s)) := by
    funext s
    have hiff : m * s ∈ Ioc α β ↔ s ∈ Ioc (α / m) (β / m) := by
      simp only [mem_Ioc, div_lt_iff₀ hm, le_div_iff₀ hm]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    show (Ioc α β).indicator f (m * s) = _
    by_cases hs : s ∈ Ioc (α / m) (β / m)
    · rw [indicator_of_mem (hiff.2 hs), indicator_of_mem hs]
    · rw [indicator_of_notMem (fun h => hs (hiff.1 h)), indicator_of_notMem hs]
  have hfm : Continuous fun s => f (m * s) := hf.comp (continuous_const.mul continuous_id)
  obtain ⟨h2, hi⟩ := memLp_indicator_Ioc hfm (α / m) (β / m)
  rw [← he] at h2 hi
  filter_upwards [Cvs.Upstream.CosineTransformHalfLine.calK_ofReal_eq_integral hc (h2.restrict _) hi.integrableOn] with x hx
  rw [hx]
  congr 1
  have hL : ∫ s in Ioi 0, h s * Real.cos (c * s * x)
      = ∫ s in Ioi 0, (Ioc α β).indicator f (m * s) * Real.cos (c * (m * s) * (x / m)) := by
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [hh]
    rw [show c * (m * s) * (x / m) = c * s * x by field_simp]
  have hcomp := integral_comp_mul_left_Ioi
    (fun ξ => (Ioc α β).indicator f ξ * Real.cos (c * ξ * (x / m))) 0 hm
  simp only [mul_zero, smul_eq_mul] at hcomp
  rw [hL, hcomp]
  have hind : (fun ξ => (Ioc α β).indicator f ξ * Real.cos (c * ξ * (x / m)))
      = (Ioc α β).indicator (fun ξ => f ξ * Real.cos (c * ξ * (x / m))) := by
    funext ξ; by_cases hξ : ξ ∈ Ioc α β <;> simp [hξ]
  rw [hind, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 (show Ioc α β ⊆ Ioi 0 from fun ξ hξ => lt_of_le_of_lt hα hξ.1),
    intervalIntegral.integral_of_le hαβ]
  ring

/-- **The dilate pairing as integrals**: `∫_{(1,∞)} Re calK(f(m·))·g = ∫_{(1,∞)} f·Re calK(g(m·))` for real `f, g`
vanishing on `(−∞, 1]`. -/
theorem integral_re_calK_dil_comm {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {f g : ℝ → ℝ}
    (hf : MemLp (fun x => (f x : ℂ)) 2 (volume.restrict (Ioi 0)))
    (hg : MemLp (fun x => (g x : ℂ)) 2 (volume.restrict (Ioi 0)))
    (hf1 : ∀ x, x ≤ 1 → f x = 0) (hg1 : ∀ x, x ≤ 1 → g x = 0) :
    ∫ x in Ioi 1, (Cvs.Upstream.CosineTransformHalfLine.calK c (fun t => (f (m * t) : ℂ)) x).re * g x
      = ∫ t in Ioi 1, f t * (Cvs.Upstream.CosineTransformHalfLine.calK c (fun s => (g (m * s) : ℂ)) t).re := by
  have hK : ∀ (H : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) {h : ℝ → ℝ},
      (H : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] (fun x => (h x : ℂ)) →
      ((Cvs.L2a.ReflectionFloor.Uop hc (Cvs.L2a.DilationCornerSplit.dilU hm H) : ℝ → ℂ)) =ᵐ[volume.restrict (Ioi 1)]
        Cvs.Upstream.CosineTransformHalfLine.calK c (fun t => (h (m * t) : ℂ)) := by
    intro H h hH
    have hdil : (Cvs.L2a.DilationCornerSplit.dilU hm H : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] fun t => (h (m * t) : ℂ) :=
      (Cvs.L2a.DilationCornerSplit.coeFn_dilU hm H).trans ((Cvs.Upstream.CosineTransformDilation.qmp_mul_Ioi hm).ae_eq_comp hH)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one)
      (Cvs.L2a.ReflectionFloor.coeFn_Uop hc (Cvs.L2a.DilationCornerSplit.dilU hm H))] with x hx
    rw [hx, Cvs.Upstream.CosineTransformHalfLine.calK_congr hdil]
  have hL : RCLike.re (inner ℂ (Cvs.L2a.ReflectionFloor.Uop hc (Cvs.L2a.DilationCornerSplit.dilU hm (hf.toLp _))) (hg.toLp _))
      = ∫ x in Ioi 1, (Cvs.Upstream.CosineTransformHalfLine.calK c (fun t => (f (m * t) : ℂ)) x).re * g x := by
    rw [re_inner_of_ae_left hg.coeFn_toLp hg1]
    refine integral_congr_ae ?_
    filter_upwards [hK _ hf.coeFn_toLp] with x hx
    rw [hx]
  have hR : RCLike.re (inner ℂ (hf.toLp _) (Cvs.L2a.ReflectionFloor.Uop hc (Cvs.L2a.DilationCornerSplit.dilU hm (hg.toLp _))))
      = ∫ t in Ioi 1, f t * (Cvs.Upstream.CosineTransformHalfLine.calK c (fun s => (g (m * s) : ℂ)) t).re := by
    rw [re_inner_of_ae_right hf.coeFn_toLp hf1]
    refine integral_congr_ae ?_
    filter_upwards [hK _ hg.coeFn_toLp] with x hx
    rw [hx]
  rw [← hL, ← hR, Cvs.L2a.DilationCornerSplit.inner_Uop_dilU hc hm]

/-- A real `L²(1, ∞)` function vanishing on `(−∞, 1]` is a class in `L²(0, ∞)`. -/
theorem memLp_ofReal_of_Ioi_one {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioi 1)))
    (h0 : ∀ x, x ≤ 1 → f x = 0) : MemLp (fun x => (f x : ℂ)) 2 (volume.restrict (Ioi 0)) := by
  have e : f = (Ioi 1).indicator f := by
    funext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, h0 x (not_lt.1 hx)]
  rw [e]
  exact (((memLp_indicator_iff_restrict (μ := volume) measurableSet_Ioi.nullMeasurableSet).2 hf).restrict _).ofReal

/-- The real part of a phase integral is the cosine integral. -/
theorem intervalIntegral_mul_cos_eq_re {f : ℝ → ℝ} (hf : Continuous f) (c y α β : ℝ) :
    ∫ ξ in α..β, f ξ * Real.cos (c * ξ * y) = (∫ ξ in α..β, (f ξ : ℂ) * eF c y ξ).re := by
  have hint : IntervalIntegrable (fun ξ => (f ξ : ℂ) * eF c y ξ) volume α β :=
    ((continuous_ofReal.comp hf).mul (continuous_eF c y).1).intervalIntegrable _ _
  rw [← RCLike.re_to_complex, ← intervalIntegral.intervalIntegral_re hint]
  refine intervalIntegral.integral_congr fun ξ _ => ?_
  simp only [eF, RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  ring_nf

/-- Splitting `Φ = Σᵢaᵢψᵢ` inside a weighted phase integral. -/
theorem intervalIntegral_wΦ_eF {g : ι → ℝ → ℝ} {c : ℝ} (a : ι → ℝ) (hψc : ∀ i, Continuous (psi c (g i)))
    {w : ℝ → ℝ} (hw : Continuous w) (y α β : ℝ) :
    ∫ ξ in α..β, ((w ξ * ∑ i, a i * psi c (g i) ξ : ℝ) : ℂ) * eF c y ξ
      = ∑ i, (a i : ℂ) * ∫ ξ in α..β, ((w ξ : ℝ) : ℂ) * (psi c (g i) ξ : ℂ) * eF c y ξ := by
  have hii : ∀ i, IntervalIntegrable (fun ξ => (a i : ℂ) * (((w ξ : ℝ) : ℂ) * (psi c (g i) ξ : ℂ) * eF c y ξ))
      volume α β := fun i =>
    (continuous_const.mul (((continuous_ofReal.comp hw).mul (continuous_ofReal.comp (hψc i))).mul
      (continuous_eF c y).1)).intervalIntegrable _ _
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun i _ => hii i]
  refine intervalIntegral.integral_congr fun ξ _ => ?_
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `ū = 1_(1,∞)Φ − 1_(1,X]wFΦ` is in `L²(1, ∞)`. -/
theorem memLp_ubar {Φ : ℝ → ℝ} (hΦ : MemLp Φ 2 (volume.restrict (Ioi 1))) (X : ℝ) :
    MemLp (ubar Φ wF X) 2 (volume.restrict (Ioi 1)) := by
  have hw : MemLp (fun x => wF x * Φ x) 2 (volume.restrict (Ioi 1)) :=
    hΦ.of_le (continuous_wF.1.aestronglyMeasurable.mul hΦ.aestronglyMeasurable) (ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Cvs.L2a.FarFarBound.wF_bounds x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (Cvs.L2a.FarFarBound.wF_bounds x).2.1)
  exact (hΦ.indicator measurableSet_Ioi.nullMeasurableSet).sub (hw.indicator measurableSet_Ioc.nullMeasurableSet)

/-- `(1 − wF)Φ` vanishes on `[2, ∞)`, so its cut to `(1, ∞)` is its cut to `(1, 2)`. -/
theorem indicator_Ioi_one_wF (Φ : ℝ → ℝ) :
    (Ioi 1).indicator (fun x => (1 - wF x) * Φ x) = (Ioo 1 2).indicator (fun x => (1 - wF x) * Φ x) := by
  funext x
  by_cases h2 : x ∈ Ioo (1 : ℝ) 2
  · rw [indicator_of_mem h2, indicator_of_mem (Ioo_subset_Ioi_self h2)]
  · rw [indicator_of_notMem h2]
    by_cases h1 : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem h1, (wF_of_two_le (not_lt.1 fun h => h2 ⟨h1, h⟩)).1, sub_self, zero_mul]
    · rw [indicator_of_notMem h1]

/-- **Splitting `ū`**: `∫_{(1,∞)} ū f = ∫_{(1,2)} (1 − wF)Φ f + ∫_{(M,∞)} Φ f` for `f ∈ L²(1, ∞)`, `M ≥ 2`. -/
theorem integral_ubar_mul {Φ f : ℝ → ℝ} (hΦ : MemLp Φ 2 (volume.restrict (Ioi 1)))
    (hf : MemLp f 2 (volume.restrict (Ioi 1))) {M : ℝ} (hM : 2 ≤ M) :
    ∫ t in Ioi 1, ubar Φ wF M t * f t
      = (∫ t in Ioo 1 2, (1 - wF t) * Φ t * f t) + ∫ t in Ioi M, Φ t * f t := by
  have hχX : ∀ x, M < x → wF x = 1 := fun x hx => (wF_of_two_le (by linarith)).1
  have hw : MemLp (fun x => (1 - wF x) * Φ x) 2 (volume.restrict (Ioi 1)) :=
    hΦ.of_le ((continuous_const.sub continuous_wF.1).aestronglyMeasurable.mul hΦ.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        obtain ⟨h0, h1, -, -⟩ := Cvs.L2a.FarFarBound.wF_bounds x
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith))
  have hi1 : Integrable (fun t => (1 - wF t) * Φ t * f t) (volume.restrict (Ioi 1)) := hw.integrable_mul hf
  have hi2 : Integrable (fun t => Φ t * f t) (volume.restrict (Ioi 1)) := hΦ.integrable_mul hf
  have hpt : ∀ t, ubar Φ wF M t * f t = (Ioo 1 2).indicator (fun t => (1 - wF t) * Φ t * f t) t
      + (Ioi M).indicator (fun t => Φ t * f t) t := by
    intro t
    rw [ubar_eq (by linarith) hχX t, indicator_Ioi_one_wF]
    by_cases h1 : t ∈ Ioo (1 : ℝ) 2 <;> by_cases h2 : t ∈ Ioi M <;>
      simp only [indicator_of_mem, indicator_of_notMem, h1, h2, not_false_eq_true] <;> ring
  simp_rw [hpt]
  rw [integral_add (hi1.indicator measurableSet_Ioo) (hi2.indicator measurableSet_Ioi),
    setIntegral_indicator measurableSet_Ioo, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.2 Ioo_subset_Ioi_self, inter_eq_right.2 (Ioi_subset_Ioi (by linarith))]

/-- **The per-cut split**: if `Re calK(g(m·)) = A + B` with `A ∈ L²(1, ∞)`, then `B ∈ L²(1, ∞)` and
`∫_{(1,∞)} Re calK(u(m·))·g = ∫ uA + ∫ uB`. -/
theorem integral_dil_split {c m : ℝ} (hc : 0 < c) (hm : 0 < m) {u gm A B : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioi 1))) (hu1 : ∀ x, x ≤ 1 → u x = 0)
    (hg : MemLp (fun x => (gm x : ℂ)) 2 (volume.restrict (Ioi 0))) (hg1 : ∀ x, x ≤ 1 → gm x = 0)
    (hA : MemLp A 2 (volume.restrict (Ioi 1)))
    (hid : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), (Cvs.Upstream.CosineTransformHalfLine.calK c (fun s => (gm (m * s) : ℂ)) t).re = A t + B t) :
    MemLp B 2 (volume.restrict (Ioi 1))
      ∧ ∫ x in Ioi 1, (Cvs.Upstream.CosineTransformHalfLine.calK c (fun t => (u (m * t) : ℂ)) x).re * gm x
        = (∫ t in Ioi 1, u t * A t) + ∫ t in Ioi 1, u t * B t := by
  have hid1 := ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one) hid
  have hK : MemLp (fun t => (Cvs.Upstream.CosineTransformHalfLine.calK c (fun s => (gm (m * s) : ℂ)) t).re) 2 (volume.restrict (Ioi 1)) :=
    ((Cvs.Upstream.CosineTransformHalfLine.memLp_calK hc (Cvs.Upstream.CosineTransformDilation.memLp_comp_mul_Ioi hg hm)).mono_measure
      (Measure.restrict_mono_set volume (Ioi_subset_Ioi zero_le_one))).re
  have hB : MemLp B 2 (volume.restrict (Ioi 1)) :=
    (hK.sub hA).ae_eq (by filter_upwards [hid1] with t ht; simp only [Pi.sub_apply]; rw [ht]; ring)
  refine ⟨hB, ?_⟩
  have i1 : Integrable (fun t => u t * A t) (volume.restrict (Ioi 1)) := hu.integrable_mul hA
  have i2 : Integrable (fun t => u t * B t) (volume.restrict (Ioi 1)) := hu.integrable_mul hB
  rw [integral_re_calK_dil_comm hc hm (memLp_ofReal_of_Ioi_one hu hu1) hg hu1 hg1, ← integral_add i1 i2]
  refine integral_congr_ae ?_
  filter_upwards [hid1] with t ht
  rw [ht]; ring

/-- The cut sample `𝒜(y) = Σᵢ aᵢSᵢ[μ_y](x₀)` with the exact multiplier `μ_y = muCut c y x₀`. -/
def cutSample (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (x₀ y : ℝ) : ℂ :=
  ∑ i, (a i : ℂ) * Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c y x₀) c (χ i) (g i) x₀

/-- `𝔅_m(t) = −(κ/m)Re 𝒜_m(t/m)`, `κ = √(2c/π)`. -/
def frakB (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  -(√(2 * c / π) / m) * (cutSample c χ g a m (t / m)).re

/-- The bottom bulk `(κ/m)Re Σᵢ aᵢ∫_m^{m+δ} eψᵢR[w_b]` at `y = t/m`. -/
def bulkBot (c δ : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  √(2 * c / π) / m * (∑ i, (a i : ℂ) * ∫ x in (m : ℝ)..m + δ, eF c (t / m) x * (psi c (g i) x : ℂ)
    * rRc (Cvs.L2a.CornerSplitSqrtFloor.wbC δ m) (Cvs.L2a.CornerSplitSqrtFloor.wbC₁ δ m) (Cvs.L2a.CornerSplitSqrtFloor.wbC₂ δ m) c (χ i) (t / m) x).re

/-- `Γ_bot = −2Σ_m∫_{(1,∞)} ū·bulk_m`. -/
def GammaBot (c δ : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M : ℕ) : ℝ :=
  -2 * ∑ m ∈ Finset.Icc 2 (M - 1),
    ∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkBot c δ χ g a m t

/-- The cut sample along `y = t/m` is in `L²(1, ∞)`. -/
theorem memLp_cutSample_div {c x₀ m : ℝ} (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (hx : 1 < x₀) (hc : 0 < c)
    (hm : 0 < m) : MemLp (fun t => (cutSample c χ g a x₀ (t / m)).re) 2 (volume.restrict (Ioi 1)) := by
  have h : MemLp (fun t => cutSample c χ g a x₀ (t / m)) 2 (volume.restrict (Ioi 1)) := by
    unfold cutSample Cvs.L2a.BandTransferBandForm.smp
    exact memLp_finsetSum _ fun i _ => (((Cvs.L2a.QIdentityCutPoint.memLp_muCut_div hx hc hm _).mul_const _).add
      ((Cvs.L2a.QIdentityCutPoint.memLp_muCut_div hx hc hm _).mul_const _)).const_mul _
  exact h.re

/-- The quintic weights are continuous. -/
theorem continuous_wG_S (δ m : ℝ) :
    Continuous (fun x => Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x) ∧ Continuous (fun x => Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ m x) := by
  unfold Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.L2a.CornerSplitSqrtFloor.wTopG
  exact ⟨continuous_const.sub (Cvs.Upstream.QuinticSmoothStep.contDiff_S.continuous.comp ((continuous_id.sub continuous_const).div_const δ)),
    continuous_const.sub (Cvs.Upstream.QuinticSmoothStep.contDiff_S.continuous.comp ((continuous_const.sub continuous_id).div_const δ))⟩

/-- The bottom cut `w_b1_(m,M]Φ` is `1_(m,m+δ]w_bΦ` once `m + δ ≤ M`. -/
theorem wBot_cut_eq (Φ : ℝ → ℝ) {δ m M : ℝ} (hδ0 : 0 < δ) (hmM : m + δ ≤ M) :
    (fun x => Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x * (Ioc m M).indicator Φ x)
      = (Ioc m (m + δ)).indicator (fun x => Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x * Φ x) := by
  funext x
  by_cases hx : x ∈ Ioc m (m + δ)
  · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ Ioc m M from ⟨hx.1, by linarith [hx.2]⟩)]
  · rw [indicator_of_notMem hx]
    by_cases hxm : x ≤ m
    · rw [indicator_of_notMem (fun (h : x ∈ Ioc m M) => not_lt.2 hxm h.1), mul_zero]
    · have hlt : m + δ < x := lt_of_not_ge fun h => hx ⟨lt_of_not_ge hxm, h⟩
      rw [Cvs.L2a.CornerSplitSqrtFloor.wBotG_eq_zero Cvs.L2a.CornerSplitSqrtFloor.isStep_S hδ0 hlt.le, zero_mul]

/-- **The bottom cut kernel at `m`**: `Re calK(w_b1_(m,M]Φ(m·))(t) = 𝔅_m(t) + bulk_m(t)` for a.e. `t > 0`. -/
theorem reCalK_bot {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      (Cvs.Upstream.CosineTransformHalfLine.calK c (fun s => ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m (m * s)
        * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * s) : ℝ) : ℂ)) t).re
        = frakB c χ g a m t + bulkBot c δ χ g a m t := by
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hΦc : Continuous (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  have hwc := (continuous_wG_S δ m).1
  have hwΦc : Continuous fun x => Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x * ∑ i, a i * psi c (g i) x := hwc.mul hΦc
  have hfun := wBot_cut_eq (fun ξ => ∑ i, a i * psi c (g i) ξ) hδ0 (show (m : ℝ) + δ ≤ M by linarith)
  have hfun' : (fun s => ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m (m * s)
        * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * s) : ℝ) : ℂ))
      = fun s => (((Ioc (m : ℝ) (m + δ)).indicator
          (fun x => Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x * ∑ i, a i * psi c (g i) x) (m * s) : ℝ) : ℂ) := by
    funext s; rw [← congrFun hfun]
  rw [hfun']
  filter_upwards [ae_restrict_of_ae (calK_dil_indicator hc hm0 (by linarith : (0 : ℝ) ≤ m)
    (by linarith : (m : ℝ) ≤ m + δ) hwΦc), ae_restrict_mem measurableSet_Ioi] with t ht ht0
  rw [ht, Complex.ofReal_re, intervalIntegral_mul_cos_eq_re hwΦc, intervalIntegral_wΦ_eF a hψc hwc]
  have hy : 0 < t / m := div_pos ht0 hm0
  obtain ⟨h0, h1, h2, h3⟩ := Cvs.L2a.CornerSplitSqrtFloor.wbC_cut_far hδ0.ne' (m : ℝ)
  have hibp : ∀ i, ∫ ξ in (m : ℝ)..m + δ, ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m ξ : ℝ) : ℂ) * (psi c (g i) ξ : ℂ)
        * eF c (t / m) ξ
      = (∫ ξ in (m : ℝ)..m + δ, eF c (t / m) ξ * (psi c (g i) ξ : ℂ)
          * rRc (Cvs.L2a.CornerSplitSqrtFloor.wbC δ m) (Cvs.L2a.CornerSplitSqrtFloor.wbC₁ δ m) (Cvs.L2a.CornerSplitSqrtFloor.wbC₂ δ m) c (χ i) (t / m) ξ)
        - Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c (t / m) m) c (χ i) (g i) m := by
    intro i
    have h := ibpC_Icc (hg i) (hg₁ i) (hg₂c i) (hang i) hc hy (by linarith : (1 : ℝ) < m)
      (by linarith : (m : ℝ) ≤ m + δ) (fun x _ => Cvs.L2a.CornerSplitSqrtFloor.hasDerivAt_wbC δ m x)
      (fun x _ => Cvs.L2a.CornerSplitSqrtFloor.hasDerivAt_wbC₁ δ m x) (Cvs.L2a.CornerSplitSqrtFloor.continuous_wbC₂ δ m).continuousOn
    rw [bBc_eq_zero h2 h3, Cvs.L2a.QIdentityCutPoint.bBc_cut_split (by linarith) hc (hχc i) h0 h1] at h
    exact h.trans (by ring)
  simp_rw [hibp]
  unfold frakB bulkBot cutSample
  simp only [mul_sub, Finset.sum_sub_distrib, Complex.sub_re]
  ring

/-- **The bottom split at `m`**: `bulk_m ∈ L²(1, ∞)` and the `m`-th term of `Dbot` is `∫ū𝔅_m + ∫ū·bulk_m`. -/
theorem dil_split_bot {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    MemLp (bulkBot c δ χ g a m) 2 (volume.restrict (Ioi 1))
      ∧ ∫ x in Ioi 1, (Cvs.Upstream.CosineTransformHalfLine.calK c (fun t => ((ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (m * t) : ℝ) : ℂ))
          x).re * (Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x)
        = (∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t)
          + ∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkBot c δ χ g a m t := by
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hΦc : Continuous (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hΦ2 : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum _ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  have hfun := wBot_cut_eq (fun ξ => ∑ i, a i * psi c (g i) ξ) hδ0 (show (m : ℝ) + δ ≤ M by linarith)
  have hgm : MemLp (fun x => ((Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x
      * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x : ℝ) : ℂ)) 2 (volume.restrict (Ioi 0)) := by
    have hwΦc : Continuous fun x => Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x * ∑ i, a i * psi c (g i) x :=
      (continuous_wG_S δ m).1.mul hΦc
    have h := ((memLp_indicator_Ioc hwΦc (m : ℝ) (m + δ)).1.restrict
      (Ioi (0 : ℝ))).ofReal (K := ℂ)
    rw [← hfun] at h
    exact h
  have hgm1 : ∀ x : ℝ, x ≤ 1 →
      Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x = 0 :=
    fun x hx => by rw [indicator_of_notMem (fun h => by linarith [h.1]), mul_zero]
  have hA : MemLp (frakB c χ g a m) 2 (volume.restrict (Ioi 1)) :=
    (memLp_cutSample_div χ g a (by linarith : (1 : ℝ) < m) hc hm0).const_mul _
  exact integral_dil_split (u := ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M)
    (gm := fun x => Cvs.L2a.CornerSplitSqrtFloor.wBotG Cvs.Upstream.QuinticSmoothStep.S δ m x * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x)
    hc hm0 (memLp_ubar hΦ2 _) (fun x hx => ubar_of_le_one hx) hgm hgm1 hA
    (reCalK_bot a hg hg₁ hg₂c hang hc hχc hm hmM hδ0 hδ1)

/-- **CK (i), bottom**: `Dbot = −2Σ_m∫_{(1,∞)} ū𝔅_m + Γ_bot`. -/
theorem Dbot_eq_kernel {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M : ℕ} (hM : 3 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Cvs.L2a.CornerSplitSqrtFloor.DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
      = -2 * ∑ m ∈ Finset.Icc 2 (M - 1),
          (∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t)
        + GammaBot c δ χ g a M := by
  unfold Cvs.L2a.CornerSplitSqrtFloor.DbotG Cvs.L2a.DilationCornerSplit.dilPart GammaBot
  rw [Nat.floor_natCast]
  have hsplitI : Finset.Icc 2 M = Finset.Icc 2 (M - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
  have hMM : ((M - 1 + 1 : ℕ) : ℝ) = M := by rw [Nat.sub_add_cancel (by omega)]
  rw [hsplitI, Finset.sum_Icc_succ_top (by omega), hMM]
  simp only [Set.Ioc_self, Set.indicator_empty, mul_zero, integral_zero, add_zero]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm2, hmM⟩ := Finset.mem_Icc.1 hm
  exact (dil_split_bot a hg hg₁ hg₂c hang hc hχc hm2 (by omega) hδ0 hδ1).2

/-- `C_m = −(2κ/m)∫_{(1,2)}(1 − wF)Φ Re 𝒜_M(t/m)`. -/
def cTop (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M m : ℕ) : ℝ :=
  -(2 * √(2 * c / π) / m) * ∫ t in Ioo 1 2,
    (1 - wF t) * (∑ i, a i * psi c (g i) t) * (cutSample c χ g a M (t / m)).re

/-- `𝒞_a = −Σ_m(2κ/m)∫_{(M,∞)}Φ Re 𝒜_M(t/m)`, the leading top kernel paired with `h` on `(M, ∞)`. -/
def calCa (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M : ℕ) : ℝ :=
  -∑ m ∈ Finset.Icc 2 (M - 1), 2 * √(2 * c / π) / m
    * ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) * (cutSample c χ g a M (t / m)).re

/-- The top bulk `(κ/m)Re Σᵢ aᵢ∫_{M−δ}^M eψᵢR[w_t]` at `y = t/m`. -/
def bulkTop (c δ : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M m : ℕ) (t : ℝ) : ℝ :=
  √(2 * c / π) / m * (∑ i, (a i : ℂ) * ∫ x in (M : ℝ) - δ..M, eF c (t / m) x * (psi c (g i) x : ℂ)
    * rRc (Cvs.L2a.CornerSplitSqrtFloor.wtC δ M) (Cvs.L2a.CornerSplitSqrtFloor.wtC₁ δ M) (Cvs.L2a.CornerSplitSqrtFloor.wtC₂ δ M) c (χ i) (t / m) x).re

/-- `R_top = −2Σ_m∫_{(1,∞)} ū·bulkTop_m`. -/
def Rtop (c δ : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M : ℕ) : ℝ :=
  -2 * ∑ m ∈ Finset.Icc 2 (M - 1),
    ∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkTop c δ χ g a M m t

/-- The top cut `w_t1_(m,M]Φ` is `1_(M−δ,M]w_tΦ` once `m ≤ M − δ`. -/
theorem wTop_cut_eq (Φ : ℝ → ℝ) {δ m M : ℝ} (hδ0 : 0 < δ) (hmM : m ≤ M - δ) :
    (fun x => Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x * (Ioc m M).indicator Φ x)
      = (Ioc (M - δ) M).indicator (fun x => Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x * Φ x) := by
  funext x
  by_cases hx : x ∈ Ioc (M - δ) M
  · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ Ioc m M from ⟨by linarith [hx.1], hx.2⟩)]
  · rw [indicator_of_notMem hx]
    by_cases hxm : x ≤ M - δ
    · rw [Cvs.L2a.CornerSplitSqrtFloor.wTopG_eq_zero Cvs.L2a.CornerSplitSqrtFloor.isStep_S hδ0 hxm, zero_mul]
    · have hlt : M < x := lt_of_not_ge fun h => hx ⟨lt_of_not_ge hxm, h⟩
      rw [indicator_of_notMem (fun (h : x ∈ Ioc m M) => not_lt.2 h.2 hlt), mul_zero]

/-- **The top cut kernel at `m`**: `Re calK(w_t1_(m,M]Φ(m·))(t) = (κ/m)Re 𝒜_M(t/m) + bulkTop_m(t)`
for a.e. `t > 0`. -/
theorem reCalK_top {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      (Cvs.Upstream.CosineTransformHalfLine.calK c (fun s => ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M (m * s)
        * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * s) : ℝ) : ℂ)) t).re
        = √(2 * c / π) / m * (cutSample c χ g a M (t / m)).re + bulkTop c δ χ g a M m t := by
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hΦc : Continuous (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  have hwc := (continuous_wG_S δ M).2
  have hwΦc : Continuous fun x => Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x * ∑ i, a i * psi c (g i) x := hwc.mul hΦc
  have hfun := wTop_cut_eq (fun ξ => ∑ i, a i * psi c (g i) ξ) hδ0 (show (m : ℝ) ≤ M - δ by linarith)
  have hfun' : (fun s => ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M (m * s)
        * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * s) : ℝ) : ℂ))
      = fun s => (((Ioc ((M : ℝ) - δ) M).indicator
          (fun x => Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x * ∑ i, a i * psi c (g i) x) (m * s) : ℝ) : ℂ) := by
    funext s; rw [← congrFun hfun]
  rw [hfun']
  filter_upwards [ae_restrict_of_ae (calK_dil_indicator hc hm0 (by linarith : (0 : ℝ) ≤ M - δ)
    (by linarith : (M : ℝ) - δ ≤ M) hwΦc), ae_restrict_mem measurableSet_Ioi] with t ht ht0
  rw [ht, Complex.ofReal_re, intervalIntegral_mul_cos_eq_re hwΦc, intervalIntegral_wΦ_eF a hψc hwc]
  have hy : 0 < t / m := div_pos ht0 hm0
  obtain ⟨h0, h1, h2, h3⟩ := Cvs.L2a.CornerSplitSqrtFloor.wtC_cut_far hδ0.ne' (M : ℝ)
  have hibp : ∀ i, ∫ ξ in (M : ℝ) - δ..M, ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M ξ : ℝ) : ℂ) * (psi c (g i) ξ : ℂ)
        * eF c (t / m) ξ
      = (∫ ξ in (M : ℝ) - δ..M, eF c (t / m) ξ * (psi c (g i) ξ : ℂ)
          * rRc (Cvs.L2a.CornerSplitSqrtFloor.wtC δ M) (Cvs.L2a.CornerSplitSqrtFloor.wtC₁ δ M) (Cvs.L2a.CornerSplitSqrtFloor.wtC₂ δ M) c (χ i) (t / m) ξ)
        + Cvs.L2a.BandTransferBandForm.smp (Cvs.L2a.QIdentityCutPoint.muCut c (t / m) M) c (χ i) (g i) M := by
    intro i
    have h := ibpC_Icc (hg i) (hg₁ i) (hg₂c i) (hang i) hc hy (by linarith : (1 : ℝ) < M - δ)
      (by linarith : (M : ℝ) - δ ≤ M) (fun x _ => Cvs.L2a.CornerSplitSqrtFloor.hasDerivAt_wtC δ M x)
      (fun x _ => Cvs.L2a.CornerSplitSqrtFloor.hasDerivAt_wtC₁ δ M x) (Cvs.L2a.CornerSplitSqrtFloor.continuous_wtC₂ δ M).continuousOn
    rw [bBc_eq_zero h2 h3, Cvs.L2a.QIdentityCutPoint.bBc_cut_split (by linarith) hc (hχc i) h0 h1] at h
    exact h.trans (by ring)
  simp_rw [hibp]
  unfold bulkTop cutSample
  simp only [mul_add, Finset.sum_add_distrib, Complex.add_re]
  ring

/-- **The top split at `m`**: `bulkTop_m ∈ L²(1, ∞)` and the `m`-th term of `Dtop` is
`∫ū(κ/m)Re 𝒜_M(·/m) + ∫ū·bulkTop_m`. -/
theorem dil_split_top {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    MemLp (bulkTop c δ χ g a M m) 2 (volume.restrict (Ioi 1))
      ∧ ∫ x in Ioi 1, (Cvs.Upstream.CosineTransformHalfLine.calK c (fun t => ((ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (m * t) : ℝ) : ℂ))
          x).re * (Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x)
        = (∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t
            * (√(2 * c / π) / m * (cutSample c χ g a M (t / m)).re))
          + ∫ t in Ioi 1, ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * bulkTop c δ χ g a M m t := by
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hΦc : Continuous (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  have hΦ2 : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum _ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (m : ℝ) + 1 ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) < m := by linarith
  have hfun := wTop_cut_eq (fun ξ => ∑ i, a i * psi c (g i) ξ) hδ0 (show (m : ℝ) ≤ M - δ by linarith)
  have hgm : MemLp (fun x => ((Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x
      * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x : ℝ) : ℂ)) 2 (volume.restrict (Ioi 0)) := by
    have hwΦc : Continuous fun x => Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x * ∑ i, a i * psi c (g i) x :=
      (continuous_wG_S δ M).2.mul hΦc
    have h := ((memLp_indicator_Ioc hwΦc ((M : ℝ) - δ) M).1.restrict (Ioi (0 : ℝ))).ofReal (K := ℂ)
    rw [← hfun] at h
    exact h
  have hgm1 : ∀ x : ℝ, x ≤ 1 →
      Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x = 0 :=
    fun x hx => by rw [indicator_of_notMem (fun h => by linarith [h.1]), mul_zero]
  have hA : MemLp (fun t => √(2 * c / π) / m * (cutSample c χ g a M (t / m)).re) 2 (volume.restrict (Ioi 1)) :=
    (memLp_cutSample_div χ g a (by linarith : (1 : ℝ) < M) hc hm0).const_mul _
  exact integral_dil_split (u := ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M)
    (gm := fun x => Cvs.L2a.CornerSplitSqrtFloor.wTopG Cvs.Upstream.QuinticSmoothStep.S δ M x * (Ioc (m : ℝ) M).indicator (fun ξ => ∑ i, a i * psi c (g i) ξ) x)
    hc hm0 (memLp_ubar hΦ2 _) (fun x hx => ubar_of_le_one hx) hgm hgm1 hA
    (reCalK_top a hg hg₁ hg₂c hang hc hχc hm hmM hδ0 hδ1)

/-- **CK (i), top**: `Dtop = Σ_m C_m + 𝒞_a + R_top`. -/
theorem Dtop_eq_kernel {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχc : ∀ i, χ i < c ^ 2) {M : ℕ} (hM : 3 ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Cvs.L2a.CornerSplitSqrtFloor.DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M δ
      = ∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m + calCa c χ g a M + Rtop c δ χ g a M := by
  have hΦ2 : MemLp (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum _ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc).const_mul (a i)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast (show 2 ≤ M by omega)
  unfold Cvs.L2a.CornerSplitSqrtFloor.DtopG Cvs.L2a.DilationCornerSplit.dilPart cTop calCa Rtop
  rw [Nat.floor_natCast]
  have hsplitI : Finset.Icc 2 M = Finset.Icc 2 (M - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
  have hMM : ((M - 1 + 1 : ℕ) : ℝ) = M := by rw [Nat.sub_add_cancel (by omega)]
  rw [hsplitI, Finset.sum_Icc_succ_top (by omega), hMM]
  simp only [Set.Ioc_self, Set.indicator_empty, mul_zero, integral_zero, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm2, hmM⟩ := Finset.mem_Icc.1 hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hA : MemLp (fun t => √(2 * c / π) / m * (cutSample c χ g a M (t / m)).re) 2 (volume.restrict (Ioi 1)) :=
    (memLp_cutSample_div χ g a (by linarith : (1 : ℝ) < M) hc hm0).const_mul _
  rw [(dil_split_top a hg hg₁ hg₂c hang hc hχc hm2 (by omega) hδ0 hδ1).2, integral_ubar_mul hΦ2 hA hM2]
  have e1 : ∫ t in Ioo 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t)
        * (√(2 * c / π) / m * (cutSample c χ g a M (t / m)).re)
      = √(2 * c / π) / m * ∫ t in Ioo 1 2, (1 - wF t) * (∑ i, a i * psi c (g i) t)
        * (cutSample c χ g a M (t / m)).re := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  have e2 : ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t)
        * (√(2 * c / π) / m * (cutSample c χ g a M (t / m)).re)
      = √(2 * c / π) / m * ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) * (cutSample c χ g a M (t / m)).re := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [e1, e2]
  ring

/-- The holomorphic phase-free top sample `𝒜̃(η) = Σᵢaᵢ(μ̃(kᵢ; η)ψᵢ⁺ + μ̃(−kᵢ; η)ψᵢ⁻)` at `x₀`. -/
def sampleC (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (x₀ : ℝ) (η : ℂ) : ℂ :=
  ∑ i, (a i : ℂ) * (Cvs.L2a.QIdentityCutPoint.muQC c x₀ (kP c (χ i) x₀) η * psiP c (χ i) (g i) x₀
    + Cvs.L2a.QIdentityCutPoint.muQC c x₀ (-kP c (χ i) x₀) η * conj (psiP c (χ i) (g i) x₀))

theorem cutSample_eq (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (x₀ y : ℝ) :
    cutSample c χ g a x₀ y = eF c y x₀ * sampleC c χ g a x₀ (y : ℂ) := by
  unfold cutSample sampleC Cvs.L2a.BandTransferBandForm.smp Cvs.L2a.QIdentityCutPoint.muCut
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Cvs.L2a.QIdentityCutPoint.muQC_ofReal, Cvs.L2a.QIdentityCutPoint.muQC_ofReal]
  ring

/-- The region `Re η > 0`, `p c |Im η| < x₀` of Cvs.L2a.QIdentityCutPoint.qQkC_ne_zero. -/
def regionC (c x₀ : ℝ) : Set ℂ := {η | 0 < η.re ∧ pP x₀ * c * |η.im| < x₀}

theorem isOpen_regionC (c x₀ : ℝ) : IsOpen (regionC c x₀) :=
  show IsOpen ({η : ℂ | 0 < η.re} ∩ {η : ℂ | pP x₀ * c * |η.im| < x₀}) from (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_const.mul (continuous_abs.comp Complex.continuous_im)) continuous_const)

theorem ofReal_mem_regionC {c x₀ s : ℝ} (hx : 1 < x₀) (hs : 0 < s) : ((s : ℝ) : ℂ) ∈ regionC c x₀ :=
  ⟨by simpa using hs, by simp; linarith⟩

/-- The top sample is holomorphic on `regionC`. -/
theorem differentiableOn_sampleC {c x₀ : ℝ} (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (hc : 0 < c)
    (hx : 1 < x₀) : DifferentiableOn ℂ (sampleC c χ g a x₀) (regionC c x₀) := by
  intro η hη
  obtain ⟨hη1, hη2⟩ : 0 < η.re ∧ pP x₀ * c * |η.im| < x₀ := hη
  have hd : ∀ ξ : ℝ, DifferentiableAt ℂ (Cvs.L2a.QIdentityCutPoint.muQC c x₀ ξ) η := fun ξ =>
    Cvs.L2a.QIdentityCutPoint.differentiableAt_muQC (Cvs.L2a.QIdentityCutPoint.qQkC_ne_zero hc hx hη1 hη2)
  have : DifferentiableAt ℂ (fun η => ∑ i, (a i : ℂ) * (Cvs.L2a.QIdentityCutPoint.muQC c x₀ (kP c (χ i) x₀) η
      * psiP c (χ i) (g i) x₀ + Cvs.L2a.QIdentityCutPoint.muQC c x₀ (-kP c (χ i) x₀) η * conj (psiP c (χ i) (g i) x₀))) η := by
    fun_prop
  exact this.differentiableWithinAt

/-- `|Q(ξ)|` on a disc: `|Q(z)| ≥ |Q(η₀)| − r(pc²(2|η₀| + r) + 2cx)` for `|z − η₀| ≤ r`. -/
theorem norm_qQkC_ge_on_disc {c x ξ : ℝ} (hc : 0 ≤ c) (hx : 1 ≤ x) {η₀ z : ℂ} {r : ℝ} (hz : ‖z - η₀‖ ≤ r) :
    ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ η₀‖ - r * (pP x * c ^ 2 * (2 * ‖η₀‖ + r) + 2 * c * x) ≤ ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  have hp : 0 ≤ pP x := by unfold pP; nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hdiff : Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z - Cvs.L2a.QIdentityCutPoint.qQkC c x ξ η₀
      = (z - η₀) * (((pP x : ℝ) : ℂ) * (c : ℂ) ^ 2 * (z + η₀) - 2 * I * (c : ℂ) * (x : ℂ)) := by
    unfold Cvs.L2a.QIdentityCutPoint.qQkC; ring
  have hzn : ‖z‖ ≤ ‖η₀‖ + r := by
    calc ‖z‖ = ‖(z - η₀) + η₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - η₀‖ + ‖η₀‖ := norm_add_le _ _
      _ ≤ ‖η₀‖ + r := by linarith
  have hb : ‖((pP x : ℝ) : ℂ) * (c : ℂ) ^ 2 * (z + η₀) - 2 * I * (c : ℂ) * (x : ℂ)‖
      ≤ pP x * c ^ 2 * (2 * ‖η₀‖ + r) + 2 * c * x := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
    · rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
      have : ‖z + η₀‖ ≤ 2 * ‖η₀‖ + r := (norm_add_le _ _).trans (by linarith)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hx0]
      norm_num
  have h1 : ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z - Cvs.L2a.QIdentityCutPoint.qQkC c x ξ η₀‖ ≤ r * (pP x * c ^ 2 * (2 * ‖η₀‖ + r) + 2 * c * x) := by
    rw [hdiff, norm_mul]
    exact mul_le_mul hz hb (norm_nonneg _) hr
  have h2 := norm_sub_norm_le (Cvs.L2a.QIdentityCutPoint.qQkC c x ξ η₀) (Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z)
  rw [norm_sub_rev] at h2
  linarith

/-- The Cauchy estimate for a function differentiable on a closed disc. -/
theorem norm_iteratedDeriv_le_of_closedBall {f : ℂ → ℂ} {η₀ : ℂ} {r C : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ Metric.closedBall η₀ r, DifferentiableAt ℂ f z)
    (hC : ∀ z ∈ Metric.sphere η₀ r, ‖f z‖ ≤ C) (j : ℕ) :
    ‖iteratedDeriv j f η₀‖ ≤ j.factorial * C / r ^ j :=
  Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    (DifferentiableOn.diffContOnCl_ball (fun z hz => (hf z hz).differentiableWithinAt) subset_rfl) hC

/-- `Q(ξ)` at a real point is the real-`y` `Q(ξ)`. -/
theorem qQkC_ofReal (c x ξ y : ℝ) : Cvs.L2a.QIdentityCutPoint.qQkC c x ξ (y : ℂ) = Cvs.L2a.QIdentityCutPoint.qQk c y x ξ := by
  unfold Cvs.L2a.QIdentityCutPoint.qQkC Cvs.L2a.QIdentityCutPoint.qQk; push_cast; ring

/-- **The kernel on unit discs far out**: for large `η`, `Q(ξ) ≠ 0` and `|μ̃(ξ; z)| ≤ K/η` on `|z − η| ≤ 1`. -/
theorem muQC_ball {c x ξ : ℝ} (hc : 0 < c) (hx : 1 < x) :
    ∃ K, ∀ᶠ η : ℝ in atTop, ∀ z ∈ Metric.closedBall (η : ℂ) 1,
      Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z ≠ 0 ∧ ‖Cvs.L2a.QIdentityCutPoint.muQC c x ξ z‖ ≤ K / η := by
  have hp : 0 < pP x := pP_pos hx
  have hx0 : 0 < x := by linarith
  set p := pP x with hp_def
  set D := ξ ^ 2 + 2 * c * x / p with hD_def
  have hD0 : 0 ≤ D := by positivity
  refine ⟨4 * (|ξ| + 2 * c) / c ^ 2 + 16 * (10 * c ^ 2 * x + 4 * c) / (p * c ^ 4), ?_⟩
  filter_upwards [eventually_ge_atTop (9 + D / c ^ 2)] with η hη z hz
  have hη9 : 9 ≤ η := le_trans (le_add_of_nonneg_right (by positivity)) hη
  have hη1 : 1 ≤ η := by linarith
  have hη0 : 0 < η := by linarith
  have hDη : D ≤ c ^ 2 * η := by
    have h : D / c ^ 2 ≤ η := by linarith
    rw [div_le_iff₀ (by positivity)] at h; linarith
  have hz' : ‖z - (η : ℂ)‖ ≤ 1 := by rw [← dist_eq_norm]; exact hz
  have hηn : ‖(η : ℂ)‖ = η := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0]
  have hzn : ‖z‖ ≤ η + 1 := by
    calc ‖z‖ = ‖(z - η) + η‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - η‖ + ‖(η : ℂ)‖ := norm_add_le _ _
      _ ≤ η + 1 := by rw [hηn]; linarith
  have hQη : p * (c ^ 2 * η ^ 2 - ξ ^ 2) ≤ ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ (η : ℂ)‖ := by
    rw [qQkC_ofReal]
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) hp.le).trans (Cvs.L2a.QIdentityCutPoint.le_norm_qQk_re hx.le)
  have hdisc := norm_qQkC_ge_on_disc (ξ := ξ) hc.le hx.le hz'
  rw [hηn] at hdisc
  have hQ : p * c ^ 2 * η ^ 2 / 4 ≤ ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z‖ := by
    have e : 2 * c * x = p * (D - ξ ^ 2) := by rw [hD_def]; field_simp; ring
    have h1 : 2 * η + 1 ≤ η ^ 2 / 4 := by nlinarith
    have h2 : D ≤ c ^ 2 * η ^ 2 / 2 := by nlinarith
    have h3 : c ^ 2 * (2 * η + 1) + D ≤ 3 * (c ^ 2 * η ^ 2) / 4 := by
      have := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hp.le
    nlinarith
  have hQ0' : 0 < p * c ^ 2 * η ^ 2 / 4 := by positivity
  have hQn : 0 < ‖Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z‖ := hQ0'.trans_le hQ
  refine ⟨norm_pos_iff.1 hQn, ?_⟩
  have hN1 : ‖I * ((ξ : ℂ) - (c : ℂ) * z)‖ ≤ (|ξ| + 2 * c) * η := by
    rw [norm_mul, Complex.norm_I, one_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hc]
    have : c * ‖z‖ ≤ c * (η + 1) := mul_le_mul_of_nonneg_left hzn hc.le
    nlinarith [abs_nonneg ξ]
  have hN2 : ‖Cvs.L2a.QIdentityCutPoint.qQ₁C c x z‖ ≤ (10 * c ^ 2 * x + 4 * c) * η ^ 2 := by
    unfold Cvs.L2a.QIdentityCutPoint.qQ₁C
    refine (norm_sub_le _ _).trans ?_
    have hz2 : ‖z ^ 2 - 1‖ ≤ (η + 1) ^ 2 + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, norm_one]
      have := pow_le_pow_left₀ (norm_nonneg z) hzn 2
      linarith
    have ea : ‖(2 : ℂ) * (c : ℂ) ^ 2 * (x : ℂ) * (z ^ 2 - 1)‖ = 2 * c ^ 2 * x * ‖z ^ 2 - 1‖ := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, abs_of_pos hx0,
        Complex.norm_ofNat]
    have eb : ‖(2 : ℂ) * I * (c : ℂ) * z‖ = 2 * 1 * c * ‖z‖ := by
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
        Complex.norm_ofNat]
    rw [ea, eb]
    have h1 : 2 * c ^ 2 * x * ‖z ^ 2 - 1‖ ≤ 2 * c ^ 2 * x * ((η + 1) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left hz2 (by positivity)
    have h2 : 2 * 1 * c * ‖z‖ ≤ 2 * 1 * c * (η + 1) := mul_le_mul_of_nonneg_left hzn (by positivity)
    have h3 : (η + 1) ^ 2 + 1 ≤ 5 * η ^ 2 := by nlinarith
    have h4 : η + 1 ≤ 2 * η ^ 2 := by nlinarith
    have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * c ^ 2 * x)
    have h6 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * c)
    nlinarith
  unfold Cvs.L2a.QIdentityCutPoint.muQC
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  have e1 : ‖I * ((ξ : ℂ) - (c : ℂ) * z) / Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z‖ ≤ (|ξ| + 2 * c) * η / (p * c ^ 2 * η ^ 2 / 4) := by
    rw [norm_div]; exact div_le_div₀ (by positivity) hN1 hQ0' hQ
  have e2 : ‖Cvs.L2a.QIdentityCutPoint.qQ₁C c x z / Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z ^ 2‖
      ≤ (10 * c ^ 2 * x + 4 * c) * η ^ 2 / (p * c ^ 2 * η ^ 2 / 4) ^ 2 := by
    rw [norm_div, norm_pow]
    exact div_le_div₀ (by positivity) hN2 (by positivity) (pow_le_pow_left₀ hQ0'.le hQ 2)
  calc p * ‖I * ((ξ : ℂ) - (c : ℂ) * z) / Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z + Cvs.L2a.QIdentityCutPoint.qQ₁C c x z / Cvs.L2a.QIdentityCutPoint.qQkC c x ξ z ^ 2‖
      ≤ p * ((|ξ| + 2 * c) * η / (p * c ^ 2 * η ^ 2 / 4)
        + (10 * c ^ 2 * x + 4 * c) * η ^ 2 / (p * c ^ 2 * η ^ 2 / 4) ^ 2) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add e1 e2)) hp.le
    _ = 4 * (|ξ| + 2 * c) / c ^ 2 / η + 16 * (10 * c ^ 2 * x + 4 * c) / (p * c ^ 4) / η / η := by
        field_simp; ring
    _ ≤ 4 * (|ξ| + 2 * c) / c ^ 2 / η + 16 * (10 * c ^ 2 * x + 4 * c) / (p * c ^ 4) / η := by
        have := div_le_self (by positivity : (0 : ℝ) ≤ 16 * (10 * c ^ 2 * x + 4 * c) / (p * c ^ 4) / η) hη1
        linarith
    _ = (4 * (|ξ| + 2 * c) / c ^ 2 + 16 * (10 * c ^ 2 * x + 4 * c) / (p * c ^ 4)) / η := by ring

/-- **The top sample on unit discs far out**: holomorphic, and `|𝒜̃(z)| ≤ C/η` on `|z − η| ≤ 1`. -/
theorem sampleC_ball {c x₀ : ℝ} (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (hc : 0 < c) (hx : 1 < x₀) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ η : ℝ in atTop, ∀ z ∈ Metric.closedBall (η : ℂ) 1,
      DifferentiableAt ℂ (sampleC c χ g a x₀) z ∧ ‖sampleC c χ g a x₀ z‖ ≤ C / η := by
  have hP := fun i => muQC_ball (ξ := kP c (χ i) x₀) hc hx
  have hN := fun i => muQC_ball (ξ := -kP c (χ i) x₀) hc hx
  choose KP hKP using hP
  choose KN hKN using hN
  refine ⟨∑ i, |a i| * (|KP i| * ‖psiP c (χ i) (g i) x₀‖ + |KN i| * ‖psiP c (χ i) (g i) x₀‖),
    by positivity, ?_⟩
  filter_upwards [Filter.eventually_all.2 hKP, Filter.eventually_all.2 hKN, eventually_gt_atTop 0]
    with η hPη hNη hη0 z hz
  constructor
  · have : DifferentiableAt ℂ (fun η => ∑ i, (a i : ℂ) * (Cvs.L2a.QIdentityCutPoint.muQC c x₀ (kP c (χ i) x₀) η
        * psiP c (χ i) (g i) x₀ + Cvs.L2a.QIdentityCutPoint.muQC c x₀ (-kP c (χ i) x₀) η * conj (psiP c (χ i) (g i) x₀))) z := by
      have hdP : ∀ i, DifferentiableAt ℂ (Cvs.L2a.QIdentityCutPoint.muQC c x₀ (kP c (χ i) x₀)) z :=
        fun i => Cvs.L2a.QIdentityCutPoint.differentiableAt_muQC (hPη i z hz).1
      have hdN : ∀ i, DifferentiableAt ℂ (Cvs.L2a.QIdentityCutPoint.muQC c x₀ (-kP c (χ i) x₀)) z :=
        fun i => Cvs.L2a.QIdentityCutPoint.differentiableAt_muQC (hNη i z hz).1
      have hi : ∀ i ∈ (Finset.univ : Finset ι), DifferentiableAt ℂ (fun η => (a i : ℂ) *
          (Cvs.L2a.QIdentityCutPoint.muQC c x₀ (kP c (χ i) x₀) η * psiP c (χ i) (g i) x₀
            + Cvs.L2a.QIdentityCutPoint.muQC c x₀ (-kP c (χ i) x₀) η * conj (psiP c (χ i) (g i) x₀))) z :=
        fun i _ => (differentiableAt_const (a i : ℂ)).mul
          (((hdP i).mul_const (psiP c (χ i) (g i) x₀)).add ((hdN i).mul_const (conj (psiP c (χ i) (g i) x₀))))
      exact DifferentiableAt.fun_sum hi
    exact this
  · unfold sampleC
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, add_div]
    have h1 := (hPη i z hz).2
    have h2 := (hNη i z hz).2
    have h1' : KP i / η ≤ |KP i| / η := div_le_div_of_nonneg_right (le_abs_self _) hη0.le
    have h2' : KN i / η ≤ |KN i| / η := div_le_div_of_nonneg_right (le_abs_self _) hη0.le
    rw [mul_comm (|KP i|), mul_comm (|KN i|), mul_div_assoc, mul_div_assoc]
    rw [mul_comm ‖Cvs.L2a.QIdentityCutPoint.muQC c x₀ (kP c (χ i) x₀) z‖, mul_comm ‖Cvs.L2a.QIdentityCutPoint.muQC c x₀ (-kP c (χ i) x₀) z‖]
    gcongr
    · exact h1.trans h1'
    · exact h2.trans h2'

/-- The weight `V_m(t) = 𝒜̃_M(t/m)` and its first two derivatives. -/
def vW (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M m : ℕ) (t : ℝ) : ℂ :=
  sampleC c χ g a M ((t / m : ℝ) : ℂ)

def vW₁ (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M m : ℕ) (t : ℝ) : ℂ :=
  (1 / (m : ℂ)) * deriv (sampleC c χ g a M) ((t / m : ℝ) : ℂ)

def vW₂ (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M m : ℕ) (t : ℝ) : ℂ :=
  (1 / (m : ℂ)) ^ 2 * deriv (deriv (sampleC c χ g a M)) ((t / m : ℝ) : ℂ)

theorem hasDerivAt_vW {g : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) (hc : 0 < c) {M m : ℕ} (hM : 2 ≤ M)
    (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (vW c χ g a M m) (vW₁ c χ g a M m t) t ∧ HasDerivAt (vW₁ c χ g a M m) (vW₂ c χ g a M m t) t
      ∧ ContinuousAt (vW₂ c χ g a M m) t := by
  have hM' : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hU := isOpen_regionC c (M : ℝ)
  have hF : DifferentiableOn ℂ (sampleC c χ g a M) (regionC c M) := differentiableOn_sampleC χ g a hc hM'
  have hF' : DifferentiableOn ℂ (deriv (sampleC c χ g a M)) (regionC c M) := hF.deriv hU
  have hF'' : DifferentiableOn ℂ (deriv (deriv (sampleC c χ g a M))) (regionC c M) := hF'.deriv hU
  have hts : 0 < t / m := div_pos ht hm'
  have hmem := hU.mem_nhds (ofReal_mem_regionC (c := c) hM' hts)
  have hdiv : HasDerivAt (fun t : ℝ => t / m) (1 / m) t := by
    simpa using (hasDerivAt_id t).div_const (m : ℝ)
  have key : ∀ {G : ℂ → ℂ}, DifferentiableOn ℂ G (regionC c M) →
      HasDerivAt (fun t : ℝ => G ((t / m : ℝ) : ℂ)) ((1 / (m : ℂ)) * deriv G ((t / m : ℝ) : ℂ)) t := by
    intro G hG
    have h1 : HasDerivAt G (deriv G ((t / m : ℝ) : ℂ)) ((t / m : ℝ) : ℂ) :=
      (hG.differentiableAt hmem).hasDerivAt
    refine (h1.comp_ofReal.scomp t hdiv).congr_deriv ?_
    rw [Complex.real_smul]; push_cast; ring
  refine ⟨key hF, ?_, ?_⟩
  · refine ((key hF').const_mul (1 / (m : ℂ))).congr_deriv ?_
    unfold vW₂; ring
  · unfold vW₂
    have hcomp : ContinuousAt (fun t : ℝ => ((t / m : ℝ) : ℂ)) t :=
      (Complex.continuous_ofReal.comp (continuous_id.div_const (m : ℝ))).continuousAt
    exact continuousAt_const.mul
      (ContinuousAt.comp (g := deriv (deriv (sampleC c χ g a M))) (hF''.continuousOn.continuousAt hmem) hcomp)

/-- **The top kernel and its derivatives decay**: `|V|, |V′|, |V″| ≤ C/t` for large `t`. -/
theorem vW_decay {c : ℝ} (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (hc : 0 < c) {M m : ℕ} (hM : 2 ≤ M)
    (hm : 1 ≤ m) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ t in atTop, ‖vW c χ g a M m t‖ ≤ C / t ∧ ‖vW₁ c χ g a M m t‖ ≤ C / t
      ∧ ‖vW₂ c χ g a M m t‖ ≤ C / t := by
  have hM' : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  obtain ⟨C, hC0, hC⟩ := sampleC_ball χ g a hc hM'
  refine ⟨C * m + 2 * C, by positivity, ?_⟩
  have htend : Tendsto (fun t : ℝ => t / m) atTop atTop := tendsto_id.atTop_div_const hm0
  filter_upwards [htend.eventually hC, eventually_gt_atTop 0] with t ht ht0
  have hη0 : 0 < t / m := div_pos ht0 hm0
  have hd : ∀ z ∈ Metric.closedBall ((t / m : ℝ) : ℂ) 1, DifferentiableAt ℂ (sampleC c χ g a M) z :=
    fun z hz => (ht z hz).1
  have hsph : ∀ z ∈ Metric.sphere ((t / m : ℝ) : ℂ) 1, ‖sampleC c χ g a M z‖ ≤ C / (t / m) :=
    fun z hz => (ht z (Metric.sphere_subset_closedBall hz)).2
  have h0 : ‖sampleC c χ g a M ((t / m : ℝ) : ℂ)‖ ≤ C / (t / m) :=
    (ht _ (Metric.mem_closedBall_self zero_le_one)).2
  have h1 := norm_iteratedDeriv_le_of_closedBall one_pos hd hsph 1
  have h2 := norm_iteratedDeriv_le_of_closedBall one_pos hd hsph 2
  rw [iteratedDeriv_one] at h1
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
  simp only [Nat.factorial, Nat.cast_one, one_mul, one_pow, div_one, Nat.succ_eq_add_one, zero_add,
    Nat.mul_one] at h1 h2
  rw [show ((1 + 1 : ℕ) : ℝ) = 2 by norm_num] at h2
  have hmC : ‖(1 / (m : ℂ))‖ = 1 / m := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  have hCt : C / (t / m) = C * m / t := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · calc ‖vW c χ g a M m t‖ ≤ C / (t / m) := h0
      _ = C * m / t := hCt
      _ ≤ (C * m + 2 * C) / t := by gcongr; linarith
  · unfold vW₁
    rw [norm_mul, hmC]
    calc 1 / (m : ℝ) * ‖deriv (sampleC c χ g a M) ((t / m : ℝ) : ℂ)‖ ≤ 1 / m * (C / (t / m)) := by gcongr
      _ = C / t := by field_simp
      _ ≤ (C * m + 2 * C) / t := by gcongr; nlinarith
  · unfold vW₂
    rw [norm_mul, norm_pow, hmC]
    calc (1 / (m : ℝ)) ^ 2 * ‖deriv (deriv (sampleC c χ g a M)) ((t / m : ℝ) : ℂ)‖
        ≤ (1 / m) ^ 2 * (2 * (C / (t / m))) := by gcongr
      _ = 2 * C / m / t := by field_simp
      _ ≤ (C * m + 2 * C) / t := by
          gcongr
          calc 2 * C / m ≤ 2 * C := div_le_self (by positivity) hm1
            _ ≤ C * m + 2 * C := by nlinarith

/-- `𝔇 = Σ_m(2κ/m)Re Σᵢaᵢ B[V_m](M)` at `y = M/m`: the double boundary at the orbit point. -/
def frakD (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 (M - 1), 2 * √(2 * c / π) / m
    * (∑ i, (a i : ℂ) * bBc (vW c χ g a M m) (vW₁ c χ g a M m) c (χ i) (g i) ((M : ℝ) / m) M).re

/-- `𝔈₁ = Σ_m(2κ/m)Re Σᵢaᵢ∫_{(M,∞)} eψᵢR[V_m]` at `y = M/m`: the `t`-bulk of `𝒞_a`. -/
def frakE1 (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 (M - 1), 2 * √(2 * c / π) / m
    * (∑ i, (a i : ℂ) * ∫ t in Ioi (M : ℝ), eF c ((M : ℝ) / m) t * (psi c (g i) t : ℂ)
      * rRc (vW c χ g a M m) (vW₁ c χ g a M m) (vW₂ c χ g a M m) c (χ i) ((M : ℝ) / m) t).re

/-- `𝒜_M(t/m) = e^{ic(M/m)t}V_m(t)`: the top cut sample along `y = t/m` at the orbit phase. -/
theorem cutSample_div_eq (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (M m : ℕ) (t : ℝ) :
    cutSample c χ g a M (t / m) = eF c ((M : ℝ) / m) t * vW c χ g a M m t := by
  rw [cutSample_eq]
  unfold vW eF
  rw [show c * (t / (m : ℝ)) * (M : ℝ) = c * ((M : ℝ) / m) * t by ring]

/-- `V`, `V′`, `V″` are continuous on any `s ⊆ (0, ∞)`. -/
theorem continuousOn_vW {g : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) (hc : 0 < c) {M m : ℕ}
    (hM : 2 ≤ M) (hm : 1 ≤ m) {s : Set ℝ} (hs : s ⊆ Ioi 0) :
    ContinuousOn (vW c χ g a M m) s ∧ ContinuousOn (vW₁ c χ g a M m) s ∧ ContinuousOn (vW₂ c χ g a M m) s :=
  ⟨fun _ hx => (hasDerivAt_vW a hc hM hm (hs hx)).1.continuousAt.continuousWithinAt,
    fun _ hx => (hasDerivAt_vW a hc hM hm (hs hx)).2.1.continuousAt.continuousWithinAt,
    fun _ hx => (hasDerivAt_vW a hc hM hm (hs hx)).2.2.continuousWithinAt⟩

/-- **The `t`-step at the orbit point** for one cut `m`:
`∫_{(M,∞)}Φ Re 𝒜_M(t/m) = Re Σᵢaᵢ∫eψᵢR[V] − Re Σᵢaᵢ B[V](M)`. -/
theorem integral_Ioi_cutSample_eq {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ0 : ∀ i, 0 ≤ χ i) {M m : ℕ} (hm : 2 ≤ m) (hmM : m + 1 ≤ M) :
    ∫ t in Ioi (M : ℝ), (∑ i, a i * psi c (g i) t) * (cutSample c χ g a M (t / m)).re
      = (∑ i, (a i : ℂ) * ∫ t in Ioi (M : ℝ), eF c ((M : ℝ) / m) t * (psi c (g i) t : ℂ)
          * rRc (vW c χ g a M m) (vW₁ c χ g a M m) (vW₂ c χ g a M m) c (χ i) ((M : ℝ) / m) t).re
        - (∑ i, (a i : ℂ) * bBc (vW c χ g a M m) (vW₁ c χ g a M m) c (χ i) (g i) ((M : ℝ) / m) M).re := by
  have hM2 : 2 ≤ M := by omega
  have hm1 : 1 ≤ m := by omega
  have hMr : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hy : 1 < (M : ℝ) / m := by
    rw [one_lt_div hm0]; exact_mod_cast (show m < M by omega)
  have hy0 : 0 < (M : ℝ) / m := by linarith
  obtain ⟨C, hC0, hC⟩ := vW_decay χ g a hc hM2 hm1
  have hpos : Ici (M : ℝ) ⊆ Ioi 0 := fun _ hx => lt_of_lt_of_le (by linarith : (0 : ℝ) < M) hx
  have hd := fun x (hx : x ∈ Ici (M : ℝ)) => hasDerivAt_vW (g := g) (χ := χ) a hc hM2 hm1 (hpos hx)
  obtain ⟨hvc, hv₁c, hv₂c⟩ := continuousOn_vW (g := g) (χ := χ) a hc hM2 hm1 hpos
  have hbd3 : ∃ C, ∀ᶠ t in atTop, ‖vW c χ g a M m t‖ ≤ C ∧ ‖vW₁ c χ g a M m t‖ ≤ C / t
      ∧ ‖vW₂ c χ g a M m t‖ ≤ C / t :=
    ⟨C, by filter_upwards [hC, eventually_ge_atTop 1] with t h ht
           exact ⟨h.1.trans (div_le_self hC0 ht), h.2.1, h.2.2⟩⟩
  have hbd2 : ∃ C, ∀ᶠ t in atTop, ‖vW c χ g a M m t‖ ≤ C ∧ ‖vW₁ c χ g a M m t‖ ≤ C / t := by
    obtain ⟨C', hC'⟩ := hbd3
    exact ⟨C', hC'.mono fun t h => ⟨h.1, h.2.1⟩⟩
  have hL : ∀ i, IntegrableOn (fun t => vW c χ g a M m t * (psi c (g i) t : ℂ) * eF c ((M : ℝ) / m) t)
      (Ioi (M : ℝ)) := fun i =>
    integrableOn_wψe_far (hg i) (hg₁ i) (hg₂c i) (hang i) hc hvc ⟨C, hC.mono fun t h => h.1⟩
  have hR : ∀ i, IntegrableOn (fun t => eF c ((M : ℝ) / m) t * (psi c (g i) t : ℂ)
      * rRc (vW c χ g a M m) (vW₁ c χ g a M m) (vW₂ c χ g a M m) c (χ i) ((M : ℝ) / m) t) (Ioi (M : ℝ)) :=
    fun i => integrableOn_eψR_far (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) hy hMr hvc hv₁c hv₂c hbd3
  have hB : ∀ i, Tendsto (fun T => bBc (vW c χ g a M m) (vW₁ c χ g a M m) c (χ i) (g i) ((M : ℝ) / m) T)
      atTop (𝓝 0) := fun i =>
    tendsto_zero_of_le_div (norm_bBc_le_far (hg i) (hg₁ i) (hg₂c i) hc (hχ0 i) hy hbd2)
  have hI := fun i => ibpC_Ioi (hg i) (hg₁ i) (hg₂c i) (hang i) hc hy0 hMr (fun x hx => (hd x hx).1)
    (fun x hx => (hd x hx).2.1) hv₂c (hL i) (hR i) (hB i)
  have hpt : ∀ t, (∑ i, a i * psi c (g i) t) * (cutSample c χ g a M (t / m)).re
      = (∑ i, (a i : ℂ) * (vW c χ g a M m t * (psi c (g i) t : ℂ) * eF c ((M : ℝ) / m) t)).re := by
    intro t
    rw [cutSample_div_eq, ← Complex.re_ofReal_mul]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hpt]
  have hint : Integrable (fun t => ∑ i, (a i : ℂ) * (vW c χ g a M m t * (psi c (g i) t : ℂ)
      * eF c ((M : ℝ) / m) t)) (volume.restrict (Ioi (M : ℝ))) :=
    integrable_finsetSum _ fun i _ => (hL i).const_mul _
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [hre, integral_finsetSum _ fun i _ => (hL i).const_mul _]
  simp_rw [integral_const_mul, hI]
  rw [← Complex.sub_re, ← Finset.sum_sub_distrib]
  exact congrArg Complex.re (Finset.sum_congr rfl fun i _ => by ring)

/-- **CK (ii)**: `𝒞_a = 𝔇 − 𝔈₁`. -/
theorem Ca_eq_D_sub_E {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) {M : ℕ} (hM : 3 ≤ M) :
    calCa c χ g a M = frakD c χ g a M - frakE1 c χ g a M := by
  unfold calCa frakD frakE1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm2, hmM⟩ := Finset.mem_Icc.1 hm
  rw [integral_Ioi_cutSample_eq a hg hg₁ hg₂c hang hc hχ0 hm2 (by omega)]
  ring

/-! ### The `a_F` part: the weight-one `t`-step and the `x`-step -/

end Cvs.L2a.CutKernels
