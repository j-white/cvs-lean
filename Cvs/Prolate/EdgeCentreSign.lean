import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularEdgeValueNonzero
import Cvs.Prolate.CosineTransformSignLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionChiVariation
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.VolterraResolventEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge–centre sign: Sturm comparison and the even spectrum of the regular solution

Sturm comparison via `f₁U₂ − U₁f₂ = ∫₁^ξ ((Q − χ) − (Q' − χ'))f₁f₂`; along the even spectrum `{χ : U_χ(0) = 0}`
the centre value `f_χ(0)` alternates, and for `c²s²` the `k`-th even angular level has `(−1)^k g(0) g(1) > 0`.
-/

noncomputable section

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.VolterraResolventEdge Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.RegularSolutionChiVariation

namespace Cvs.Prolate.EdgeCentreSign

/-! ### Real-variable helpers -/

/-- A function vanishing at `a` with derivative `f' ≠ 0` has `f t · f' > 0` just to the right of `a`. -/
theorem eventually_mul_deriv_pos {f : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a) (h0 : f a = 0)
    (hf' : f' ≠ 0) : ∀ᶠ t in 𝓝[>] a, 0 < f t * f' := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hf).mono_left (nhdsGT_le_nhdsNE a)
  have h2 : Tendsto (fun t => slope f a t * f') (𝓝[>] a) (𝓝 (f' * f')) := hs.mul_const f'
  filter_upwards [h2.eventually (eventually_gt_nhds (mul_self_pos.mpr hf')), self_mem_nhdsWithin]
    with t ht hta
  rw [slope_def_field, h0, sub_zero] at ht
  have hta' : 0 < t - a := sub_pos.mpr hta
  have hne : t - a ≠ 0 := hta'.ne'
  have := mul_pos ht hta'
  calc (0:ℝ) < f t / (t - a) * f' * (t - a) := this
    _ = f t * f' := by field_simp

/-- A function vanishing at `a` with derivative `f' ≠ 0` has `f t · f' < 0` just to the left of `a`. -/
theorem eventually_mul_deriv_neg {f : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a) (h0 : f a = 0)
    (hf' : f' ≠ 0) : ∀ᶠ t in 𝓝[<] a, f t * f' < 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hf).mono_left (nhdsLT_le_nhdsNE a)
  have h2 : Tendsto (fun t => slope f a t * f') (𝓝[<] a) (𝓝 (f' * f')) := hs.mul_const f'
  filter_upwards [h2.eventually (eventually_gt_nhds (mul_self_pos.mpr hf')), self_mem_nhdsWithin]
    with t ht hta
  rw [slope_def_field, h0, sub_zero] at ht
  have hta' : t - a < 0 := sub_neg.mpr hta
  have hne : t - a ≠ 0 := hta'.ne
  have := mul_neg_of_pos_of_neg ht hta'
  calc f t * f' = f t / (t - a) * f' * (t - a) := by field_simp
    _ < 0 := this

/-- Where `f` is least at `a` from the left, `f'(a) ≤ 0`. -/
theorem deriv_nonpos_of_left {f : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a)
    (h : ∀ᶠ t in 𝓝[<] a, f a ≤ f t) : f' ≤ 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hf).mono_left (nhdsLT_le_nhdsNE a)
  refine le_of_tendsto hs ?_
  filter_upwards [h, self_mem_nhdsWithin] with t ht hta
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht) (sub_nonpos.mpr (le_of_lt hta))

/-- Where `f` is least at `a` from the right, `f'(a) ≥ 0`. -/
theorem deriv_nonneg_of_right {f : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a)
    (h : ∀ᶠ t in 𝓝[>] a, f a ≤ f t) : 0 ≤ f' := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hf).mono_left (nhdsGT_le_nhdsNE a)
  refine ge_of_tendsto hs ?_
  filter_upwards [h, self_mem_nhdsWithin] with t ht hta
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr (le_of_lt hta))

/-- A continuous function with no zero on `[a, b]` has the sign of `f a` there. -/
theorem mul_pos_of_ne_zero {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (h : ∀ t ∈ Icc a b, f t ≠ 0) : ∀ t ∈ Icc a b, 0 < f a * f t := by
  intro t ht
  have hfa := h a ⟨le_rfl, ht.1.trans ht.2⟩
  have hft := h t ht
  rcases lt_or_gt_of_ne (mul_ne_zero hfa hft) with hlt | hgt
  · exfalso
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have h0 : (0:ℝ) ∈ uIcc (f a) (f t) := by
      rw [mem_uIcc]
      rcases lt_or_gt_of_ne hfa with ha | ha
      · left; constructor <;> nlinarith
      · right; constructor <;> nlinarith
    have hc : ContinuousOn f (uIcc a t) := by rw [uIcc_of_le ht.1]; exact hf.mono hsub
    obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc hc h0
    rw [uIcc_of_le ht.1] at hs
    exact h s (hsub hs) hs0
  · exact hgt

/-- A function positive at `x` whose derivative is positive wherever it vanishes is positive on `[x, y]`. -/
theorem pos_of_deriv_pos_at_zero {A A' : ℝ → ℝ} {x y : ℝ}
    (hA : ∀ t ∈ Icc x y, HasDerivAt A (A' t) t) (hAx : 0 < A x)
    (hz : ∀ t ∈ Ioc x y, A t = 0 → 0 < A' t) : ∀ t ∈ Icc x y, 0 < A t := by
  by_contra hcon
  push Not at hcon
  have hc : ContinuousOn A (Icc x y) := fun t ht => (hA t ht).continuousAt.continuousWithinAt
  set S := Icc x y ∩ A ⁻¹' Iic 0 with hS
  have hSne : S.Nonempty := let ⟨t, ht, h⟩ := hcon; ⟨t, ht, h⟩
  have hSc : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSb : BddBelow S := ⟨x, fun t ht => ht.1.1⟩
  set t₀ := sInf S with ht₀def
  have ht₀ : t₀ ∈ S := hSc.csInf_mem hSne hSb
  have hpos : ∀ t ∈ Ico x t₀, 0 < A t := by
    intro t ht
    by_contra hle
    push Not at hle
    have := csInf_le hSb ⟨⟨ht.1, ht.2.le.trans ht₀.1.2⟩, hle⟩
    linarith [ht.2]
  have hxt₀ : x < t₀ := by
    refine lt_of_le_of_ne ht₀.1.1 (fun h => ?_)
    have h2 : A t₀ ≤ 0 := ht₀.2
    rw [← h] at h2
    linarith
  have hA0 : A t₀ = 0 := by
    have hge : 0 ≤ A t₀ := ge_of_tendsto
      ((hA t₀ ht₀.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsLT hxt₀] with t ht using (hpos t ⟨ht.1.le, ht.2⟩).le)
    exact le_antisymm ht₀.2 hge
  have hA' := hz t₀ ⟨hxt₀, ht₀.1.2⟩ hA0
  have hev := eventually_mul_deriv_neg (hA t₀ ht₀.1) hA0 hA'.ne'
  obtain ⟨t, ht, ht'⟩ := (hev.and (Ioo_mem_nhdsLT hxt₀)).exists
  have := hpos t ⟨ht'.1.le, ht'.2⟩
  nlinarith [mul_pos this hA']

/-! ### §1 Wronskians -/

/-- **The two-level Wronskian**: the regular solutions `f₁, f₂` of `(Q, χ)`, `(Q', χ')`, with fluxes `U₁, U₂`, satisfy
`f₁U₂ − U₁f₂ = ∫₁^ξ ((Q − χ) − (Q' − χ')) f₁f₂` on `(−1, ∞)`. -/
theorem cross_wronskian (Q Q' : C(ℝ, ℝ)) (χ χ' : ℝ) {ξ : ℝ} (hξ : -1 < ξ) :
    regSol Q χ ξ * regU Q' χ' ξ - regU Q χ ξ * regSol Q' χ' ξ =
      ∫ t in (1:ℝ)..ξ, ((Q t - χ) - (Q' t - χ')) * (regSol Q χ t * regSol Q' χ' t) := by
  set F : ℝ → ℝ := fun t => regSol Q χ t * regU Q' χ' t - regU Q χ t * regSol Q' χ' t with hF
  have hd : ∀ t, -1 < t →
      HasDerivAt F (((Q t - χ) - (Q' t - χ')) * (regSol Q χ t * regSol Q' χ' t)) t := by
    intro t ht
    have d := ((hasDerivAt_regSol Q χ ht).mul (hasDerivAt_regU Q' χ' ht)).sub
      ((hasDerivAt_regU Q χ ht).mul (hasDerivAt_regSol Q' χ' ht))
    refine d.congr_deriv ?_
    rw [← pP_mul_regV Q' χ' ht, ← pP_mul_regV Q χ ht]
    ring
  have hsub := uIcc_one_subset_Ioi hξ
  have hc : ContinuousOn (fun t => ((Q t - χ) - (Q' t - χ')) * (regSol Q χ t * regSol Q' χ' t))
      (Ioi (-1)) :=
    (((Q.continuous.sub continuous_const).sub (Q'.continuous.sub continuous_const)).continuousOn).mul
      ((continuousOn_regSol Q χ).mul (continuousOn_regSol Q' χ'))
  have hI := ftc_uIcc (f := F) (x := 1) (y := ξ)
    (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => hd t (hsub (Ioo_subset_Icc_self ht))) ((hc.mono hsub).intervalIntegrable)
  rw [hI]
  simp [F, regU, regSol_one]

/-- **The centre Wronskian is negative** on `(−1, 1)`: `f U̇ − U ḟ = −∫_ξ^1 f² < 0`. -/
theorem wronskian_neg (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) (hξ1 : ξ < 1) :
    regSol Q χ ξ * regUDot Q χ ξ - regU Q χ ξ * regDot Q χ ξ < 0 := by
  rw [mass_identity Q χ hξ, intervalIntegral.integral_symm, neg_lt_zero]
  refine intervalIntegral.integral_pos hξ1 ?_ (fun x _ => sq_nonneg _)
    ⟨1, ⟨hξ1.le, le_rfl⟩, by simp [regSol_one]⟩
  exact ((continuousOn_regSol Q χ).pow 2).mono fun x hx => lt_of_lt_of_le hξ hx.1

/-- Inside `(−1, 1)` the regular solution and its flux do not vanish together. -/
theorem regU_ne_zero_of_regSol_eq_zero (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) (hξ1 : ξ < 1)
    (h : regSol Q χ ξ = 0) : regU Q χ ξ ≠ 0 := by
  intro hU
  have := wronskian_neg Q χ hξ hξ1
  rw [h, hU] at this
  simp at this

/-- **Zeros in `(−1, 1)` are simple**: where the regular solution vanishes its derivative does not. -/
theorem regV_ne_zero_of_regSol_eq_zero (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : -1 < ξ) (hξ1 : ξ < 1)
    (h : regSol Q χ ξ = 0) : regV Q χ ξ ≠ 0 := by
  intro hV
  apply regU_ne_zero_of_regSol_eq_zero Q χ hξ hξ1 h
  rw [← pP_mul_regV Q χ hξ, hV, mul_zero]

/-! ### §2 Below the potential -/

/-- Some level lies below `Q` on `[0, 1]`. -/
theorem exists_lt_potential (Q : C(ℝ, ℝ)) : ∃ m : ℝ, ∀ χ < m, ∀ s ∈ Icc (0:ℝ) 1, χ < Q s := by
  obtain ⟨s₀, -, hs₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one)
    Q.continuous.continuousOn
  exact ⟨Q s₀, fun χ hχ s hs => lt_of_lt_of_le hχ (hs₀ hs)⟩

/-- Where `χ < Q` on `[z, 1]` and the regular solution is positive on `(z, 1]`, its flux is positive on `[z, 1)`. -/
theorem regU_pos_of_pos {Q : C(ℝ, ℝ)} {χ z : ℝ} (hz : -1 < z) (hQ : ∀ s ∈ Icc z 1, χ < Q s)
    (hpos : ∀ s ∈ Ioc z 1, 0 < regSol Q χ s) : ∀ s ∈ Ico z 1, 0 < regU Q χ s := by
  intro s hs
  have hs1 : -1 < s := lt_of_lt_of_le hz hs.1
  rw [regU, intervalIntegral.integral_symm, neg_neg]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht => mul_pos
    (sub_pos.2 (hQ t ⟨hs.1.trans ht.1.le, ht.2.le⟩)) (hpos t ⟨lt_of_le_of_lt hs.1 ht.1, ht.2.le⟩)) hs.2
  exact ((((Q.continuous.sub continuous_const).continuousOn).mul (continuousOn_regSol Q χ)).mono
    (by rw [uIcc_comm]; exact uIcc_one_subset_Ioi hs1)).intervalIntegrable

/-- Where `χ < Q` on `[ξ, 1]`, the regular solution is at least `1` on `[ξ, 1]`. -/
theorem one_le_regSol_of_lt (Q : C(ℝ, ℝ)) {χ ξ : ℝ} (hξ : -1 < ξ) (hξ1 : ξ ≤ 1)
    (hQ : ∀ s ∈ Icc ξ 1, χ < Q s) : ∀ s ∈ Icc ξ 1, 1 ≤ regSol Q χ s := by
  have hanti : ∀ z ∈ Icc ξ 1, (∀ s ∈ Ioc z 1, 0 < regSol Q χ s) →
      ∀ s ∈ Icc z 1, 1 ≤ regSol Q χ s := by
    intro z hz hpos
    have hz1 : -1 < z := lt_of_lt_of_le hξ hz.1
    have hU := regU_pos_of_pos hz1 (fun s hs => hQ s ⟨hz.1.trans hs.1, hs.2⟩) hpos
    have hA : AntitoneOn (regSol Q χ) (Icc z 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := regV Q χ) (convex_Icc z 1)
        ((continuousOn_regSol Q χ).mono fun s hs => lt_of_lt_of_le hz1 hs.1) (fun s hs => ?_)
        (fun s hs => ?_)
      · rw [interior_Icc] at hs
        exact (hasDerivAt_regSol Q χ (lt_trans hz1 hs.1)).hasDerivWithinAt
      · rw [interior_Icc] at hs
        have hs1 : -1 < s := lt_trans hz1 hs.1
        have hp : pP s < 0 := by unfold pP; nlinarith [hs.1, hs.2]
        have hu := hU s ⟨hs.1.le, hs.2⟩
        rw [← pP_mul_regV Q χ hs1] at hu
        nlinarith
    intro s hs
    have := hA hs ⟨hz.2, le_rfl⟩ hs.2
    rwa [regSol_one] at this
  have hpos : ∀ s ∈ Icc ξ 1, 0 < regSol Q χ s := by
    by_contra hcon
    push Not at hcon
    have hc : ContinuousOn (regSol Q χ) (Icc ξ 1) :=
      (continuousOn_regSol Q χ).mono fun s hs => lt_of_lt_of_le hξ hs.1
    set Z := Icc ξ 1 ∩ regSol Q χ ⁻¹' Iic 0 with hZ
    have hZne : Z.Nonempty := let ⟨s, hs, h⟩ := hcon; ⟨s, hs, h⟩
    have hZc : IsClosed Z := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hZb : BddAbove Z := ⟨1, fun s hs => hs.1.2⟩
    have hzZ : sSup Z ∈ Z := hZc.csSup_mem hZne hZb
    have hpz : ∀ s ∈ Ioc (sSup Z) 1, 0 < regSol Q χ s := by
      intro s hs
      by_contra hle
      push Not at hle
      have : s ≤ sSup Z := le_csSup hZb ⟨⟨hzZ.1.1.trans hs.1.le, hs.2⟩, hle⟩
      linarith [hs.1]
    have := hanti (sSup Z) hzZ.1 hpz (sSup Z) ⟨le_rfl, hzZ.1.2⟩
    have h2 : regSol Q χ (sSup Z) ≤ 0 := hzZ.2
    linarith
  exact hanti ξ ⟨le_rfl, hξ1⟩ (fun s hs => hpos s ⟨hs.1.le, hs.2⟩)

/-- Where `χ < Q` on `[ξ, 1]` with `ξ < 1`, the flux of the regular solution at `ξ` is positive. -/
theorem regU_pos_of_lt (Q : C(ℝ, ℝ)) {χ ξ : ℝ} (hξ : -1 < ξ) (hξ1 : ξ < 1)
    (hQ : ∀ s ∈ Icc ξ 1, χ < Q s) : 0 < regU Q χ ξ :=
  regU_pos_of_pos hξ hQ (fun s hs => lt_of_lt_of_le one_pos
    (one_le_regSol_of_lt Q hξ hξ1.le hQ s ⟨hs.1.le, hs.2⟩)) ξ ⟨le_rfl, hξ1⟩

/-! ### §3 Sturm comparison -/

/-- The regular solution is continuous on `[u, v]` for `−1 < u`. -/
theorem continuousOn_regSol_Icc (R : C(ℝ, ℝ)) (κ : ℝ) {u v : ℝ} (hu : -1 < u) :
    ContinuousOn (regSol R κ) (Icc u v) :=
  (continuousOn_regSol R κ).mono fun _ hs => lt_of_lt_of_le hu hs.1

/-- **Sturm comparison at the regular end**: if `f = regSol Q χ` vanishes at `a ∈ (−1, 1)` and not on `(a, 1)`,
and `Q' − χ' < Q − χ` on `(a, 1)`, then `regSol Q' χ'` vanishes in `(a, 1)`. -/
theorem sturm_edge {Q Q' : C(ℝ, ℝ)} {χ χ' a : ℝ} (ha : -1 < a) (ha1 : a < 1)
    (hlt : ∀ t ∈ Ioo a 1, Q' t - χ' < Q t - χ) (h0 : regSol Q χ a = 0)
    (hne : ∀ t ∈ Ioo a 1, regSol Q χ t ≠ 0) :
    ∃ t ∈ Ioo a 1, regSol Q' χ' t = 0 := by
  by_contra hcon
  push Not at hcon
  have hposOf : ∀ (R : C(ℝ, ℝ)) (κ : ℝ), (∀ t ∈ Ioo a 1, regSol R κ t ≠ 0) →
      ∀ t ∈ Ioo a 1, 0 < regSol R κ t := by
    intro R κ hR t ht
    have := mul_pos_of_ne_zero (continuousOn_regSol_Icc R κ (v := 1) (lt_trans ha ht.1)) (fun s hs => by
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [h, regSol_one]; exact one_ne_zero
      · exact hR s ⟨lt_of_lt_of_le ht.1 hs.1, h⟩) 1 ⟨ht.2.le, le_rfl⟩
    rwa [regSol_one, mul_one] at this
  have hy := hposOf Q χ hne
  have hy' := hposOf Q' χ' hcon
  have hy'a : 0 ≤ regSol Q' χ' a :=
    ge_of_tendsto ((hasDerivAt_regSol Q' χ' ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsGT ha1] with t ht using (hy' t ht).le)
  have hVa : 0 ≤ regV Q χ a :=
    deriv_nonneg_of_right (hasDerivAt_regSol Q χ ha)
      (by filter_upwards [Ioo_mem_nhdsGT ha1] with t ht; rw [h0]; exact (hy t ht).le)
  have hpa : pP a < 0 := by unfold pP; nlinarith
  have hUa : regU Q χ a ≤ 0 := by rw [← pP_mul_regV Q χ ha]; nlinarith
  have hcw := cross_wronskian Q Q' χ χ' ha
  rw [h0, zero_mul, zero_sub, intervalIntegral.integral_symm] at hcw
  have hint : 0 < ∫ t in a..1, ((Q t - χ) - (Q' t - χ')) * (regSol Q χ t * regSol Q' χ' t) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht => mul_pos
      (by linarith [hlt t ht]) (mul_pos (hy t ht) (hy' t ht))) ha1
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ha1.le]
    exact (((Q.continuous.sub continuous_const).sub (Q'.continuous.sub continuous_const)).continuousOn).mul
      ((continuousOn_regSol_Icc Q χ ha).mul (continuousOn_regSol_Icc Q' χ' ha))
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hUa hy'a]

/-- **Sturm comparison**: if `regSol Q χ` vanishes at `a < b` in `(−1, 1)` and not between, and `Q' − χ' < Q − χ`
on `(a, b)`, then `regSol Q' χ'` vanishes in `(a, b)`. -/
theorem sturm_between {Q Q' : C(ℝ, ℝ)} {χ χ' a b : ℝ} (ha : -1 < a) (hab : a < b) (hb : b < 1)
    (hlt : ∀ t ∈ Ioo a b, Q' t - χ' < Q t - χ) (ha0 : regSol Q χ a = 0) (hb0 : regSol Q χ b = 0)
    (hne : ∀ t ∈ Ioo a b, regSol Q χ t ≠ 0) :
    ∃ t ∈ Ioo a b, regSol Q' χ' t = 0 := by
  by_contra hcon
  push Not at hcon
  have hb' : -1 < b := lt_trans ha hab
  set m := (a + b) / 2 with hmdef
  have hm : m ∈ Ioo a b := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  have hsign : ∀ (R : C(ℝ, ℝ)) (κ : ℝ), (∀ t ∈ Ioo a b, regSol R κ t ≠ 0) →
      ∀ t ∈ Ioo a b, 0 < regSol R κ m * regSol R κ t := by
    intro R κ hR t ht
    rcases le_total m t with h | h
    · exact mul_pos_of_ne_zero (continuousOn_regSol_Icc R κ (v := t) (lt_trans ha hm.1))
        (fun s hs => hR s ⟨lt_of_lt_of_le hm.1 hs.1, lt_of_le_of_lt hs.2 ht.2⟩) t ⟨h, le_rfl⟩
    · have := mul_pos_of_ne_zero (continuousOn_regSol_Icc R κ (v := m) (lt_trans ha ht.1))
        (fun s hs => hR s ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hm.2⟩) m ⟨h, le_rfl⟩
      rwa [mul_comm] at this
  set ε := regSol Q χ m
  set δ := regSol Q' χ' m
  have hεy := hsign Q χ hne
  have hδy := hsign Q' χ' hcon
  have hδa : 0 ≤ δ * regSol Q' χ' a :=
    ge_of_tendsto (((hasDerivAt_regSol Q' χ' ha).const_mul δ).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) (by filter_upwards [Ioo_mem_nhdsGT hab] with t ht using (hδy t ht).le)
  have hδb : 0 ≤ δ * regSol Q' χ' b :=
    ge_of_tendsto (((hasDerivAt_regSol Q' χ' hb').const_mul δ).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds) (by filter_upwards [Ioo_mem_nhdsLT hab] with t ht using (hδy t ht).le)
  have hεVa : 0 ≤ ε * regV Q χ a :=
    deriv_nonneg_of_right ((hasDerivAt_regSol Q χ ha).const_mul ε)
      (by filter_upwards [Ioo_mem_nhdsGT hab] with t ht; rw [ha0, mul_zero]; exact (hεy t ht).le)
  have hεVb : ε * regV Q χ b ≤ 0 :=
    deriv_nonpos_of_left ((hasDerivAt_regSol Q χ hb').const_mul ε)
      (by filter_upwards [Ioo_mem_nhdsLT hab] with t ht; rw [hb0, mul_zero]; exact (hεy t ht).le)
  have hpa : pP a < 0 := by unfold pP; nlinarith
  have hpb : pP b < 0 := by unfold pP; nlinarith
  have hεUa : ε * regU Q χ a ≤ 0 := by
    rw [← pP_mul_regV Q χ ha, mul_left_comm]; exact mul_nonpos_of_nonpos_of_nonneg hpa.le hεVa
  have hεUb : 0 ≤ ε * regU Q χ b := by
    rw [← pP_mul_regV Q χ hb', mul_left_comm]; exact mul_nonneg_of_nonpos_of_nonpos hpb.le hεVb
  set F : ℝ → ℝ := fun t => ((Q t - χ) - (Q' t - χ')) * (regSol Q χ t * regSol Q' χ' t) with hF
  have hFc : ContinuousOn F (Ioi (-1)) :=
    (((Q.continuous.sub continuous_const).sub (Q'.continuous.sub continuous_const)).continuousOn).mul
      ((continuousOn_regSol Q χ).mul (continuousOn_regSol Q' χ'))
  have hFi : ∀ u v : ℝ, -1 < u → -1 < v → IntervalIntegrable F MeasureTheory.volume u v := by
    intro u v hu hv
    refine (hFc.mono fun s hs => ?_).intervalIntegrable
    rcases le_total u v with h | h
    · rw [uIcc_of_le h] at hs; exact lt_of_lt_of_le hu hs.1
    · rw [uIcc_of_ge h] at hs; exact lt_of_lt_of_le hv hs.1
  have hca := cross_wronskian Q Q' χ χ' ha
  have hcb := cross_wronskian Q Q' χ χ' hb'
  rw [ha0, zero_mul, zero_sub] at hca
  rw [hb0, zero_mul, zero_sub] at hcb
  have hdiff : (∫ t in (1:ℝ)..b, F t) - ∫ t in (1:ℝ)..a, F t = ∫ t in a..b, F t :=
    intervalIntegral.integral_interval_sub_left (hFi 1 b (by norm_num) hb') (hFi 1 a (by norm_num) ha)
  have hint : 0 < ∫ t in a..b, ((Q t - χ) - (Q' t - χ')) *
      ((ε * regSol Q χ t) * (δ * regSol Q' χ' t)) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht => mul_pos
      (by linarith [hlt t ht]) (mul_pos (hεy t ht) (hδy t ht))) hab
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab.le]
    exact (((Q.continuous.sub continuous_const).sub (Q'.continuous.sub continuous_const)).continuousOn).mul
      ((continuousOn_const.mul (continuousOn_regSol_Icc Q χ ha)).mul
        (continuousOn_const.mul (continuousOn_regSol_Icc Q' χ' ha)))
  have hscale : (∫ t in a..b, ((Q t - χ) - (Q' t - χ')) * ((ε * regSol Q χ t) * (δ * regSol Q' χ' t)))
      = ε * δ * ∫ t in a..b, F t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    simp only [hF]
    ring
  have hkey : ε * δ * ∫ t in a..b, F t =
      (ε * regU Q χ a) * (δ * regSol Q' χ' a) - (ε * regU Q χ b) * (δ * regSol Q' χ' b) := by
    rw [← hdiff, ← hca, ← hcb]
    ring
  have h1 := mul_nonpos_of_nonpos_of_nonneg hεUa hδa
  have h2 := mul_nonneg hεUb hδb
  linarith

/-! ### §4 Rotation -/

/-- **Rotation, first quarter**: with `A Ḃ − B Ȧ < 0` on `[x, y]`, `A x, B x > 0` and no zero of `B` on `[x, y)`,
`A > 0` on `[x, y]`. -/
theorem rotation_first {A B A' B' : ℝ → ℝ} {x y : ℝ}
    (hA : ∀ t ∈ Icc x y, HasDerivAt A (A' t) t) (hB : ∀ t ∈ Icc x y, HasDerivAt B (B' t) t)
    (hW : ∀ t ∈ Icc x y, A t * B' t - B t * A' t < 0) (hAx : 0 < A x) (hBx : 0 < B x)
    (hB0 : ∀ t ∈ Ico x y, B t ≠ 0) : ∀ t ∈ Icc x y, 0 < A t := by
  have hBpos : ∀ t ∈ Ico x y, 0 < B t := by
    intro t ht
    have hcB : ContinuousOn B (Icc x t) := fun s hs =>
      (hB s ⟨hs.1, hs.2.trans ht.2.le⟩).continuousAt.continuousWithinAt
    have := mul_pos_of_ne_zero hcB (fun s hs => hB0 s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩) t ⟨ht.1, le_rfl⟩
    exact (pos_iff_pos_of_mul_pos this).mp hBx
  refine pos_of_deriv_pos_at_zero hA hAx (fun t ht hAt => ?_)
  have hWt := hW t ⟨ht.1.le, ht.2⟩
  rw [hAt, zero_mul, zero_sub, neg_lt_zero] at hWt
  have hBt : 0 ≤ B t :=
    ge_of_tendsto ((hB t ⟨ht.1.le, ht.2⟩).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs using
        (hBpos s ⟨hs.1.le, lt_of_lt_of_le hs.2 ht.2⟩).le)
  rcases eq_or_lt_of_le hBt with h | h
  · rw [← h, zero_mul] at hWt; exact absurd hWt (lt_irrefl 0)
  · exact (pos_iff_pos_of_mul_pos hWt).mp h

/-- **Rotation, half turn**: if `x < y` are zeros of `B` with none between and `A x Ḃ x < 0`, `A y Ḃ y < 0`, then
`A x A y < 0`. -/
theorem rotation_alternates {A B B' : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hB : ∀ t ∈ Icc x y, HasDerivAt B (B' t) t) (hBx : B x = 0) (hBy : B y = 0)
    (hB0 : ∀ t ∈ Ioo x y, B t ≠ 0) (hWx : A x * B' x < 0) (hWy : A y * B' y < 0) :
    A x * A y < 0 := by
  have hx : x ∈ Icc x y := ⟨le_rfl, hxy.le⟩
  have hy : y ∈ Icc x y := ⟨hxy.le, le_rfl⟩
  have hB'x : B' x ≠ 0 := fun h => by rw [h, mul_zero] at hWx; exact lt_irrefl 0 hWx
  have hB'y : B' y ≠ 0 := fun h => by rw [h, mul_zero] at hWy; exact lt_irrefl 0 hWy
  obtain ⟨t₁, ht₁, ht₁'⟩ :=
    ((eventually_mul_deriv_pos (hB x hx) hBx hB'x).and (Ioo_mem_nhdsGT hxy)).exists
  obtain ⟨t₂, ht₂, ht₂'⟩ :=
    ((eventually_mul_deriv_neg (hB y hy) hBy hB'y).and (Ioo_mem_nhdsLT hxy)).exists
  have hcB : ∀ u v : ℝ, x < u → v < y → ContinuousOn B (Icc u v) := fun u v hu hv s hs =>
    (hB s ⟨hu.le.trans hs.1, hs.2.trans hv.le⟩).continuousAt.continuousWithinAt
  have h12 : 0 < B t₁ * B t₂ := by
    rcases le_total t₁ t₂ with h | h
    · exact mul_pos_of_ne_zero (hcB t₁ t₂ ht₁'.1 ht₂'.2)
        (fun s hs => hB0 s ⟨lt_of_lt_of_le ht₁'.1 hs.1, lt_of_le_of_lt hs.2 ht₂'.2⟩) t₂ ⟨h, le_rfl⟩
    · have := mul_pos_of_ne_zero (hcB t₂ t₁ ht₂'.1 ht₁'.2)
        (fun s hs => hB0 s ⟨lt_of_lt_of_le ht₂'.1 hs.1, lt_of_le_of_lt hs.2 ht₁'.2⟩) t₁ ⟨h, le_rfl⟩
      rwa [mul_comm] at this
  have hBB : B' x * B' y < 0 := by
    have h3 := mul_neg_of_pos_of_neg ht₁ ht₂
    have e : (B t₁ * B' x) * (B t₂ * B' y) = (B t₁ * B t₂) * (B' x * B' y) := by ring
    rw [e] at h3
    exact neg_of_mul_neg_right h3 h12.le
  have h4 := mul_pos_of_neg_of_neg hWx hWy
  have e : (A x * B' x) * (A y * B' y) = (A x * A y) * (B' x * B' y) := by ring
  rw [e] at h4
  nlinarith

/-! ### §5 The even spectrum -/

/-- The even spectrum of `Q`: the levels at which the regular solution has zero flux at the centre `ξ = 0`. -/
def evenSpec (Q : C(ℝ, ℝ)) : Set ℝ := {χ | regU Q χ 0 = 0}

/-- The centre flux is continuous in the level. -/
theorem continuous_regU_zero (Q : C(ℝ, ℝ)) : Continuous fun χ => regU Q χ 0 :=
  continuous_iff_continuousAt.2 fun χ =>
    (hasDerivAt_regU_chi Q χ (by norm_num : (-1:ℝ) < 0)).continuousAt

/-- The even spectrum is closed. -/
theorem isClosed_evenSpec (Q : C(ℝ, ℝ)) : IsClosed (evenSpec Q) :=
  isClosed_eq (continuous_regU_zero Q) continuous_const

/-- On the even spectrum the centre flux has nonzero `χ`-derivative. -/
theorem regUDot_ne_zero_of_mem (Q : C(ℝ, ℝ)) {χ : ℝ} (hχ : χ ∈ evenSpec Q) : regUDot Q χ 0 ≠ 0 := by
  intro h
  have := wronskian_neg Q χ (ξ := 0) (by norm_num) (by norm_num)
  have hχ' : regU Q χ 0 = 0 := hχ
  rw [hχ', h] at this
  simp at this

/-- Every level of the even spectrum lies at or above any level below `Q` on `[0, 1]`. -/
theorem le_of_mem_evenSpec (Q : C(ℝ, ℝ)) {m : ℝ} (hm : ∀ χ < m, ∀ s ∈ Icc (0:ℝ) 1, χ < Q s)
    {χ : ℝ} (hχ : χ ∈ evenSpec Q) : m ≤ χ := by
  by_contra hlt
  push Not at hlt
  exact (regU_pos_of_lt Q (by norm_num) (by norm_num) (fun s hs => hm χ hlt s hs)).ne' hχ

/-- **The even spectrum below any level is finite.** -/
theorem finite_evenSpec_Iio (Q : C(ℝ, ℝ)) (χ : ℝ) : (evenSpec Q ∩ Iio χ).Finite := by
  obtain ⟨m, hm⟩ := exists_lt_potential Q
  have hsub : evenSpec Q ∩ Iio χ ⊆ evenSpec Q ∩ Icc m χ := fun x hx =>
    ⟨hx.1, le_of_mem_evenSpec Q hm hx.1, (mem_Iio.mp hx.2).le⟩
  refine Set.Finite.subset ?_ hsub
  refine IsCompact.finite (isCompact_Icc.inter_left (isClosed_evenSpec Q)) ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  have hev := (hasDerivAt_regU_chi Q x (by norm_num : (-1:ℝ) < 0)).eventually_ne (c := (0:ℝ))
    (regUDot_ne_zero_of_mem Q hx.1)
  rw [inf_principal_eq_bot]
  filter_upwards [hev] with z hz hzS
  exact hz hzS.1

/-! ### §6 The sign alternates along the even spectrum -/

/-- **The centre value alternates along the even spectrum**: at a level `χ` with `k` levels of the even spectrum
below it, `(−1)^k f_χ(0) > 0`. -/
theorem centre_sign (Q : C(ℝ, ℝ)) {χ : ℝ} (hχ : χ ∈ evenSpec Q) :
    0 < (-1) ^ (evenSpec Q ∩ Iio χ).ncard * regSol Q χ 0 := by
  have hA : ∀ t, HasDerivAt (fun χ => regSol Q χ 0) (regDot Q t 0) t :=
    fun t => hasDerivAt_regSol_regDot Q t 0
  have hB : ∀ t, HasDerivAt (fun χ => regU Q χ 0) (regUDot Q t 0) t :=
    fun t => hasDerivAt_regU_chi Q t (by norm_num)
  have hW : ∀ t, regSol Q t 0 * regUDot Q t 0 - regU Q t 0 * regDot Q t 0 < 0 :=
    fun t => wronskian_neg Q t (by norm_num) (by norm_num)
  obtain ⟨m, hm⟩ := exists_lt_potential Q
  suffices H : ∀ n : ℕ, ∀ χ ∈ evenSpec Q, (evenSpec Q ∩ Iio χ).ncard = n →
      0 < (-1) ^ n * regSol Q χ 0 from H _ χ hχ rfl
  intro n
  induction n with
  | zero =>
    intro χ hχ hn
    have hemp : evenSpec Q ∩ Iio χ = ∅ := (Set.ncard_eq_zero (finite_evenSpec_Iio Q χ)).mp hn
    have hmχ := le_of_mem_evenSpec Q hm hχ
    have hlt : ∀ s ∈ Icc (0:ℝ) 1, m - 1 < Q s := fun s hs => hm (m - 1) (by linarith) s hs
    have hpos := rotation_first (A := fun χ => regSol Q χ 0) (B := fun χ => regU Q χ 0)
      (x := m - 1) (y := χ) (fun t _ => hA t) (fun t _ => hB t) (fun t _ => hW t)
      (lt_of_lt_of_le one_pos (one_le_regSol_of_lt Q (by norm_num) zero_le_one hlt 0
        ⟨le_rfl, zero_le_one⟩))
      (regU_pos_of_lt Q (by norm_num) (by norm_num) hlt)
      (fun t ht h0 => by
        have : t ∈ evenSpec Q ∩ Iio χ := ⟨h0, ht.2⟩
        rw [hemp] at this; exact this)
      χ ⟨by linarith, le_rfl⟩
    simpa using hpos
  | succ k ih =>
    intro χ hχ hn
    set S := evenSpec Q ∩ Iio χ with hSdef
    have hfin : S.Finite := finite_evenSpec_Iio Q χ
    have hne : S.Nonempty := by rw [← Set.ncard_pos hfin]; omega
    obtain ⟨χm, hχmS, hmax⟩ := Set.exists_max_image S id hfin hne
    have hS' : evenSpec Q ∩ Iio χm = S \ {χm} := by
      ext z
      constructor
      · rintro ⟨hz, hzm⟩
        exact ⟨⟨hz, mem_Iio.mpr (lt_trans (mem_Iio.mp hzm) (mem_Iio.mp hχmS.2))⟩,
          ne_of_lt (mem_Iio.mp hzm)⟩
      · rintro ⟨⟨hz, hzχ⟩, hzm⟩
        exact ⟨hz, lt_of_le_of_ne (hmax z ⟨hz, hzχ⟩) hzm⟩
    have hk : (evenSpec Q ∩ Iio χm).ncard = k := by
      rw [hS', Set.ncard_sdiff_singleton_of_mem hχmS]; omega
    have ihm := ih χm hχmS.1 hk
    have hχm0 : regU Q χm 0 = 0 := hχmS.1
    have hχ0 : regU Q χ 0 = 0 := hχ
    have hWm := hW χm
    have hWχ := hW χ
    rw [hχm0, zero_mul, sub_zero] at hWm
    rw [hχ0, zero_mul, sub_zero] at hWχ
    have halt := rotation_alternates (A := fun χ => regSol Q χ 0) (B := fun χ => regU Q χ 0)
      (x := χm) (y := χ) hχmS.2 (fun t _ => hB t) hχmS.1 hχ (fun t ht h0 => by
        have := hmax t ⟨h0, ht.2⟩
        simp only [id] at this
        linarith [ht.1]) hWm hWχ
    have hpow : (-1 : ℝ) ^ (k + 1) = -((-1) ^ k) := by rw [pow_succ]; ring
    rw [hpow]
    have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    nlinarith [mul_pos ihm (neg_pos.mpr halt)]

/-! ### §7 The first even level -/

/-- **No zero enters through the top or the interior**: on `[χ₁, χ₂] × [ξ₁, ξ₂]` (`−1 < ξ₁`, `ξ₂ ≤ 1`) the regular
solution has no zero if it has none on the edges `χ = χ₁` and `ξ = ξ₁`. -/
theorem regSol_ne_zero_of_edges (Q : C(ℝ, ℝ)) {χ₁ χ₂ ξ₁ ξ₂ : ℝ} (hξ₁ : -1 < ξ₁) (hξ₂ : ξ₂ ≤ 1)
    (hleft : ∀ ξ ∈ Icc ξ₁ ξ₂, regSol Q χ₁ ξ ≠ 0) (hbot : ∀ χ ∈ Icc χ₁ χ₂, regSol Q χ ξ₁ ≠ 0) :
    ∀ χ ∈ Icc χ₁ χ₂, ∀ ξ ∈ Icc ξ₁ ξ₂, regSol Q χ ξ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨χ0, hχ0, ξ0, hξ0, hz0⟩ := hcon
  have hRsub : Icc χ₁ χ₂ ×ˢ Icc ξ₁ ξ₂ ⊆ (univ : Set ℝ) ×ˢ Ioi (-1) := fun p hp =>
    ⟨trivial, lt_of_lt_of_le hξ₁ hp.2.1⟩
  have hFc : ContinuousOn (fun p : ℝ × ℝ => regSol Q p.1 p.2) (Icc χ₁ χ₂ ×ˢ Icc ξ₁ ξ₂) :=
    (continuousOn_regSol_joint Q).mono hRsub
  set K := Icc χ₁ χ₂ ×ˢ Icc ξ₁ ξ₂ ∩ (fun p : ℝ × ℝ => regSol Q p.1 p.2) ⁻¹' {0} with hK
  have hKc : IsClosed K :=
    hFc.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_Icc) isClosed_singleton
  have hKcpt : IsCompact K := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKc inter_subset_left
  have hKne : K.Nonempty := ⟨(χ0, ξ0), ⟨hχ0, hξ0⟩, hz0⟩
  obtain ⟨p, hpK, hpmin⟩ := hKcpt.exists_isMinOn hKne continuous_fst.continuousOn
  obtain ⟨⟨hp1, hp2⟩, hp0⟩ := hpK
  have hp0' : regSol Q p.1 p.2 = 0 := hp0
  have hmin : ∀ χ ∈ Icc χ₁ χ₂, ∀ ξ ∈ Icc ξ₁ ξ₂, regSol Q χ ξ = 0 → p.1 ≤ χ :=
    fun χ hχ ξ hξ h => hpmin (show (χ, ξ) ∈ K from ⟨⟨hχ, hξ⟩, h⟩)
  have hχs : χ₁ < p.1 := lt_of_le_of_ne hp1.1 (fun h => hleft p.2 hp2 (by rw [h]; exact hp0'))
  have hξs : ξ₁ < p.2 := lt_of_le_of_ne hp2.1 (fun h => hbot p.1 hp1 (by rw [h]; exact hp0'))
  have hξs1 : p.2 < 1 := lt_of_le_of_ne (hp2.2.trans hξ₂)
    (fun h => by rw [h, regSol_one] at hp0'; exact one_ne_zero hp0')
  have hξsm : -1 < p.2 := lt_trans hξ₁ hξs
  set σ := regSol Q χ₁ ξ₁ with hσdef
  have hσ : σ ≠ 0 := hleft ξ₁ ⟨le_rfl, hξs.le.trans hp2.2⟩
  have hleftpos : ∀ ξ ∈ Icc ξ₁ ξ₂, 0 < σ * regSol Q χ₁ ξ :=
    mul_pos_of_ne_zero (continuousOn_regSol_Icc Q χ₁ hξ₁) hleft
  have hpre : ∀ χ ∈ Ico χ₁ p.1, ∀ ξ ∈ Icc ξ₁ ξ₂, 0 < σ * regSol Q χ ξ := by
    intro χ hχ ξ hξ
    have hcχ : ContinuousOn (fun χ' => regSol Q χ' ξ) (Icc χ₁ χ) := fun χ' _ =>
      (hasDerivAt_regSol_regDot Q χ' ξ).continuousAt.continuousWithinAt
    have h1 := mul_pos_of_ne_zero hcχ (fun χ' hχ' h0 => by
      have := hmin χ' ⟨hχ'.1, hχ'.2.trans (hχ.2.le.trans hp1.2)⟩ ξ hξ h0
      linarith [hχ'.2, hχ.2]) χ ⟨hχ.1, le_rfl⟩
    have h2 := hleftpos ξ hξ
    have h3 := mul_pos h2 h1
    have e : σ * regSol Q χ₁ ξ * (regSol Q χ₁ ξ * regSol Q χ ξ) =
        (σ * regSol Q χ ξ) * (regSol Q χ₁ ξ * regSol Q χ₁ ξ) := by ring
    rw [e] at h3
    exact (mul_pos_iff_of_pos_right (mul_self_pos.mpr (hleft ξ hξ))).mp h3
  have hlim : ∀ ξ ∈ Icc ξ₁ ξ₂, 0 ≤ σ * regSol Q p.1 ξ := by
    intro ξ hξ
    have hc : ContinuousAt (fun χ => σ * regSol Q χ ξ) p.1 :=
      ((hasDerivAt_regSol_regDot Q p.1 ξ).const_mul σ).continuousAt
    exact ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsLT hχs] with χ hχ using (hpre χ ⟨hχ.1.le, hχ.2⟩ ξ hξ).le)
  rcases eq_or_lt_of_le hp2.2 with htop | hin
  · have hV : σ * regV Q p.1 p.2 ≤ 0 :=
      deriv_nonpos_of_left ((hasDerivAt_regSol Q p.1 hξsm).const_mul σ)
        (by filter_upwards [Ioo_mem_nhdsLT hξs] with ξ hξ; rw [hp0', mul_zero];
            exact hlim ξ ⟨hξ.1.le, hξ.2.le.trans hp2.2⟩)
    have hD : σ * regDot Q p.1 p.2 ≤ 0 :=
      deriv_nonpos_of_left ((hasDerivAt_regSol_regDot Q p.1 p.2).const_mul σ)
        (by filter_upwards [Ioo_mem_nhdsLT hχs] with χ hχ; rw [hp0', mul_zero];
            exact (hpre χ ⟨hχ.1.le, hχ.2⟩ p.2 hp2).le)
    have hpp : pP p.2 < 0 := by unfold pP; nlinarith
    have hU : 0 ≤ σ * regU Q p.1 p.2 := by
      rw [← pP_mul_regV Q p.1 hξsm, mul_left_comm]; exact mul_nonneg_of_nonpos_of_nonpos hpp.le hV
    have hW := wronskian_neg Q p.1 hξsm hξs1
    rw [hp0', zero_mul, zero_sub, neg_lt_zero] at hW
    have e : (σ * regU Q p.1 p.2) * (σ * regDot Q p.1 p.2) =
        (σ * σ) * (regU Q p.1 p.2 * regDot Q p.1 p.2) := by ring
    have h5 : 0 < (σ * regU Q p.1 p.2) * (σ * regDot Q p.1 p.2) := by
      rw [e]; exact mul_pos (mul_self_pos.mpr hσ) hW
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hU hD]
  · have hloc : IsLocalMin (fun ξ => σ * regSol Q p.1 ξ) p.2 := by
      filter_upwards [Icc_mem_nhds hξs hin] with ξ hξ
      show σ * regSol Q p.1 p.2 ≤ σ * regSol Q p.1 ξ
      rw [hp0', mul_zero]; exact hlim ξ hξ
    have h0 := hloc.hasDerivAt_eq_zero ((hasDerivAt_regSol Q p.1 hξsm).const_mul σ)
    exact regV_ne_zero_of_regSol_eq_zero Q p.1 hξsm hξs1 hp0' ((mul_eq_zero.mp h0).resolve_left hσ)

/-- **At and below the first even level the regular solution is positive on `[0, 1]`.** -/
theorem regSol_pos_of_le_evenSpec (Q : C(ℝ, ℝ)) {χ : ℝ} (hχ : ∀ χ' ∈ evenSpec Q, χ ≤ χ') :
    ∀ ξ ∈ Icc (0:ℝ) 1, 0 < regSol Q χ ξ := by
  obtain ⟨m, hm⟩ := exists_lt_potential Q
  have hxm : min χ (m - 1) < m := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hxχ : min χ (m - 1) ≤ χ := min_le_left _ _
  have hlt : ∀ s ∈ Icc (0:ℝ) 1, min χ (m - 1) < Q s := fun s hs => hm _ hxm s hs
  have hbotpos := rotation_first (A := fun χ => regSol Q χ 0) (B := fun χ => regU Q χ 0)
    (x := min χ (m - 1)) (y := χ)
    (fun t _ => hasDerivAt_regSol_regDot Q t 0) (fun t _ => hasDerivAt_regU_chi Q t (by norm_num))
    (fun t _ => wronskian_neg Q t (ξ := 0) (by norm_num) (by norm_num))
    (lt_of_lt_of_le one_pos (one_le_regSol_of_lt Q (by norm_num) zero_le_one hlt 0
      ⟨le_rfl, zero_le_one⟩))
    (regU_pos_of_lt Q (by norm_num) (by norm_num) hlt)
    (fun t ht h0 => by have := hχ t h0; linarith [ht.2])
  have hleft : ∀ ξ ∈ Icc (0:ℝ) 1, regSol Q (min χ (m - 1)) ξ ≠ 0 := fun ξ hξ =>
    (lt_of_lt_of_le one_pos (one_le_regSol_of_lt Q (by norm_num) zero_le_one hlt ξ hξ)).ne'
  have hne := regSol_ne_zero_of_edges Q (χ₁ := min χ (m - 1)) (χ₂ := χ) (ξ₁ := 0) (ξ₂ := 1)
    (by norm_num) le_rfl hleft (fun t ht => (hbotpos t ht).ne')
  intro ξ hξ
  have := mul_pos_of_ne_zero (continuousOn_regSol_Icc Q χ (v := 1) (by linarith [hξ.1] : (-1:ℝ) < ξ))
    (fun s hs => hne χ ⟨hxχ, le_rfl⟩ s ⟨hξ.1.trans hs.1, hs.2⟩) 1 ⟨hξ.2, le_rfl⟩
  rwa [regSol_one, mul_one] at this

/-- For `Q` monotone on `[0, 1]`, the regular solution at the first even level is antitone on `[0, 1]`. -/
theorem antitoneOn_regSol_first (Q : C(ℝ, ℝ)) (hQ : MonotoneOn Q (Icc 0 1)) {χ : ℝ}
    (hχ : χ ∈ evenSpec Q) (hfirst : ∀ χ' ∈ evenSpec Q, χ ≤ χ') :
    AntitoneOn (regSol Q χ) (Icc 0 1) := by
  have hpos := regSol_pos_of_le_evenSpec Q hfirst
  have hU0 : regU Q χ 0 = 0 := hχ
  have hU1 : regU Q χ 1 = 0 := by simp [regU]
  have hUc : ContinuousOn (regU Q χ) (Icc 0 1) := fun s hs =>
    (hasDerivAt_regU Q χ (by linarith [hs.1] : (-1:ℝ) < s)).continuousAt.continuousWithinAt
  have hU : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ regU Q χ s := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s₀, hs₀, hneg⟩ := hcon
    obtain ⟨s₁, hs₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hUc
    have hU1' : regU Q χ s₁ < 0 := lt_of_le_of_lt (hmin hs₀) hneg
    have hs₁0 : s₁ ≠ 0 := fun h => by rw [h, hU0] at hU1'; exact lt_irrefl 0 hU1'
    have hs₁1 : s₁ ≠ 1 := fun h => by rw [h, hU1] at hU1'; exact lt_irrefl 0 hU1'
    have hs₁' : s₁ ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hs₁.1 (Ne.symm hs₁0), lt_of_le_of_ne hs₁.2 hs₁1⟩
    have hloc : IsLocalMin (regU Q χ) s₁ := by
      filter_upwards [Icc_mem_nhds hs₁'.1 hs₁'.2] with s hs using hmin hs
    have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_regU Q χ (by linarith [hs₁'.1] : (-1:ℝ) < s₁))
    have hQs₁ : Q s₁ = χ := by
      have hp := hpos s₁ hs₁
      have h' : (Q s₁ - χ) * regSol Q χ s₁ = 0 := by linarith
      have := (mul_eq_zero.mp h').resolve_right hp.ne'
      linarith
    have hanti : AntitoneOn (regU Q χ) (Icc s₁ 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun s => -((Q s - χ) * regSol Q χ s))
        (convex_Icc s₁ 1) (hUc.mono (Icc_subset_Icc hs₁.1 le_rfl)) (fun s hs => ?_) (fun s hs => ?_)
      · rw [interior_Icc] at hs
        exact (hasDerivAt_regU Q χ (by linarith [hs.1, hs₁'.1])).hasDerivWithinAt
      · rw [interior_Icc] at hs
        have hs01 : s ∈ Icc (0:ℝ) 1 := ⟨by linarith [hs.1, hs₁'.1], hs.2.le⟩
        have hQs : χ ≤ Q s := hQs₁ ▸ hQ hs₁ hs01 hs.1.le
        have := hpos s hs01
        nlinarith
    have := hanti ⟨le_rfl, hs₁.2⟩ ⟨hs₁.2, le_rfl⟩ hs₁.2
    rw [hU1] at this
    linarith
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := regV Q χ) (convex_Icc 0 1)
    (continuousOn_regSol_Icc Q χ (by norm_num)) (fun s hs => ?_) (fun s hs => ?_)
  · rw [interior_Icc] at hs
    exact (hasDerivAt_regSol Q χ (by linarith [hs.1])).hasDerivWithinAt
  · rw [interior_Icc] at hs
    have hs1 : (-1:ℝ) < s := by linarith [hs.1]
    have hp : pP s < 0 := by unfold pP; nlinarith [hs.1, hs.2]
    have hu := hU s ⟨hs.1.le, hs.2.le⟩
    rw [← pP_mul_regV Q χ hs1] at hu
    nlinarith

/-! ### §8 Even angular functions -/

/-- `χ` is an even angular level: some even `g ≢ 0` with derivatives `g₁`, `g₂` on `[−1, 1]` solves the angular
equation at `χ`. -/
def IsEvenLevel (c χ : ℝ) : Prop :=
  ∃ g g₁ g₂ : ℝ → ℝ, (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) ∧
    (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) ∧
    (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) ∧
    (∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) ∧ ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0

/-- The level of an even angular solution `g ≢ 0` lies in the even spectrum of `c²s²`. -/
theorem mem_evenSpec_of_angular {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) :
    χ ∈ evenSpec (sqC c) := by
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hgs₀
  have hrep := angular_eq_mul_regSol hg hg₁ hang
  have h0mem : (0:ℝ) ∈ uIcc (-1 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num)]; constructor <;> norm_num
  have hnbhd : Icc (-1 : ℝ) 1 ∈ 𝓝 (0:ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hgneg : HasDerivAt (g ∘ fun s => -s) (g₁ 0 * -1) 0 :=
    HasDerivAt.comp_of_eq 0 (hg 0 h0mem) (hasDerivAt_neg' 0) (by simp)
  have hg10 : g₁ 0 = 0 := by
    have h1 := hgneg.congr_of_eventuallyEq (show g =ᶠ[𝓝 0] (g ∘ fun s => -s) from by
      filter_upwards [hnbhd] with s hs using (heven s hs).symm)
    have := h1.unique (hg 0 h0mem)
    linarith
  have hd : HasDerivAt g (g 1 * regV (sqC c) χ 0) 0 := by
    refine ((hasDerivAt_regSol (sqC c) χ (by norm_num)).const_mul (g 1)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show (-1:ℝ) < 0 by norm_num) (show (0:ℝ) < 1 by norm_num)] with s hs
    exact hrep s ⟨hs.1, hs.2.le⟩
  have hV : regV (sqC c) χ 0 = 0 := by
    have := hd.unique (hg 0 h0mem)
    rw [hg10] at this
    exact (mul_eq_zero.mp this).resolve_left hg1
  show regU (sqC c) χ 0 = 0
  rw [← pP_mul_regV (sqC c) χ (by norm_num), hV, mul_zero]

/-- The derivative of the potential `c²ξ²`. -/
theorem hasDerivAt_sqC (c x : ℝ) : HasDerivAt (sqC c) (2 * c ^ 2 * x) x := by
  have e : (sqC c : ℝ → ℝ) = fun ξ => c ^ 2 * ξ ^ 2 := rfl
  rw [e]
  exact ((hasDerivAt_pow 2 x).const_mul (c ^ 2)).congr_deriv (by ring)

/-- **The even spectrum of `c²s²` is the set of even angular levels.** -/
theorem isEvenLevel_iff (c χ : ℝ) : IsEvenLevel c χ ↔ χ ∈ evenSpec (sqC c) := by
  constructor
  · rintro ⟨g, g₁, g₂, hg, hg₁, hang, heven, hg0⟩
    exact mem_evenSpec_of_angular hg hg₁ hang heven hg0
  · intro hχ
    have hU : regU (sqC c) χ 0 = 0 := hχ
    have hV0 : regV (sqC c) χ 0 = 0 := by
      have := pP_mul_regV (sqC c) χ (show (-1:ℝ) < 0 by norm_num)
      rw [hU] at this
      unfold pP at this
      linarith
    have hode := regSol_ode (sqC c) χ (by simpa using hasDerivAt_sqC c 1)
    have hsq : ∀ x : ℝ, sqC c x = c ^ 2 * x ^ 2 := fun x => rfl
    refine ⟨fun s => regSol (sqC c) χ |s|,
      fun s => if 0 ≤ s then regV (sqC c) χ s else -regV (sqC c) χ (-s),
      fun s => regV₂ (sqC c) (2 * c ^ 2) χ |s|, ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [uIcc_of_le (by norm_num)] at hs
      dsimp only
      rcases lt_trichotomy s 0 with h | h | h
      · rw [if_neg (not_le.mpr h)]
        have hd := HasDerivAt.comp_of_eq s
          (hasDerivAt_regSol (sqC c) χ (by linarith [hs.2] : (-1:ℝ) < -s)) (hasDerivAt_neg' s) rfl
        refine (hd.congr_deriv (by ring)).congr_of_eventuallyEq ?_
        filter_upwards [Iio_mem_nhds h] with t ht
        simp [abs_of_neg (show t < 0 from ht)]
      · subst h
        rw [if_pos le_rfl, hV0]
        have hR : HasDerivWithinAt (fun t => regSol (sqC c) χ |t|) 0 (Ici 0) 0 := by
          have := (hasDerivAt_regSol (sqC c) χ (by norm_num : (-1:ℝ) < 0)).hasDerivWithinAt (s := Ici 0)
          rw [hV0] at this
          exact this.congr (fun t ht => by simp [abs_of_nonneg (show (0:ℝ) ≤ t from ht)]) (by simp)
        have hL : HasDerivWithinAt (fun t => regSol (sqC c) χ |t|) 0 (Iic 0) 0 := by
          have := (HasDerivAt.comp_of_eq (0:ℝ) (hasDerivAt_regSol (sqC c) χ (by norm_num : (-1:ℝ) < 0))
            (hasDerivAt_neg' (0:ℝ)) (by simp)).hasDerivWithinAt (s := Iic 0)
          rw [hV0, zero_mul] at this
          exact this.congr (fun t ht => by simp [abs_of_nonpos (show t ≤ (0:ℝ) from ht)]) (by simp)
        have := hL.union hR
        rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
      · rw [if_pos h.le]
        refine (hasDerivAt_regSol (sqC c) χ (by linarith)).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds h] with t ht
        simp [abs_of_pos (show (0:ℝ) < t from ht)]
    · intro s hs
      rw [uIcc_of_le (by norm_num)] at hs
      dsimp only
      rcases lt_trichotomy s 0 with h | h | h
      · have hd := (HasDerivAt.comp_of_eq s (hode (-s) (by linarith [hs.2])).1 (hasDerivAt_neg' s) rfl).neg
        rw [abs_of_neg h]
        refine (hd.congr_deriv (by simp)).congr_of_eventuallyEq ?_
        filter_upwards [Iio_mem_nhds h] with t ht
        simp [if_neg (not_le.mpr (show t < 0 from ht))]
      · subst h
        rw [abs_zero]
        have hR : HasDerivWithinAt (fun t => if 0 ≤ t then regV (sqC c) χ t else -regV (sqC c) χ (-t))
            (regV₂ (sqC c) (2 * c ^ 2) χ 0) (Ici 0) 0 :=
          ((hode 0 (by norm_num)).1.hasDerivWithinAt).congr
            (fun t ht => if_pos (show (0:ℝ) ≤ t from ht)) (if_pos le_rfl)
        have hneg : HasDerivAt (fun t => -regV (sqC c) χ (-t)) (regV₂ (sqC c) (2 * c ^ 2) χ 0) 0 := by
          have := (HasDerivAt.comp_of_eq (0:ℝ) (hode 0 (by norm_num)).1 (hasDerivAt_neg' (0:ℝ))
            (by simp)).neg
          exact this.congr_deriv (by ring)
        have hL : HasDerivWithinAt (fun t => if 0 ≤ t then regV (sqC c) χ t else -regV (sqC c) χ (-t))
            (regV₂ (sqC c) (2 * c ^ 2) χ 0) (Iic 0) 0 := by
          refine hneg.hasDerivWithinAt.congr (fun t ht => ?_) ?_
          · rcases eq_or_lt_of_le (show t ≤ (0:ℝ) from ht) with h0 | h0
            · subst h0; simp [hV0]
            · exact if_neg (not_le.mpr h0)
          · simp [hV0]
        have := hL.union hR
        rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
      · rw [abs_of_pos h]
        refine (hode s (by linarith)).1.congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds h] with t ht
        simp [if_pos (show (0:ℝ) ≤ t from (show (0:ℝ) < t from ht).le)]
    · intro s hs
      rw [uIcc_of_le (by norm_num)] at hs
      dsimp only
      rcases le_or_gt 0 s with h | h
      · have := (hode s (by linarith)).2
        rw [hsq] at this
        simp only [if_pos h, abs_of_nonneg h]
        linear_combination -this
      · have := (hode (-s) (by linarith [hs.2])).2
        rw [hsq] at this
        simp only [if_neg (not_le.mpr h), abs_of_neg h]
        linear_combination -this
    · intro s _
      simp [abs_neg]
    · exact ⟨1, ⟨by norm_num, le_rfl⟩, by simp [regSol_one]⟩

/-- **The edge–centre sign**: an even angular solution `g ≢ 0` at a level with `k` even angular levels below it has
`(−1)^k g(0) g(1) > 0`. -/
theorem edge_centre_sign {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) :
    0 < (-1) ^ (evenSpec (sqC c) ∩ Iio χ).ncard * (g 0 * g 1) := by
  have hmem := mem_evenSpec_of_angular hg hg₁ hang heven hg0
  have hcs := centre_sign (sqC c) hmem
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hgs₀
  have h0 : g 0 = g 1 * regSol (sqC c) χ 0 :=
    angular_eq_mul_regSol hg hg₁ hang 0 ⟨by norm_num, by norm_num⟩
  rw [h0]
  have e : (-1:ℝ) ^ (evenSpec (sqC c) ∩ Iio χ).ncard * (g 1 * regSol (sqC c) χ 0 * g 1) =
      (g 1 * g 1) * ((-1) ^ (evenSpec (sqC c) ∩ Iio χ).ncard * regSol (sqC c) χ 0) := by ring
  rw [e]
  exact mul_pos (mul_self_pos.mpr hg1) hcs

/-- **`g(0) g(1) > 0` exactly at even index**: for an even angular solution `g ≢ 0`, `0 < g(0) g(1)` iff the number of
even angular levels below its level is even. -/
theorem edge_centre_pos_iff {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) :
    0 < g 0 * g 1 ↔ Even (evenSpec (sqC c) ∩ Iio χ).ncard := by
  have h := edge_centre_sign hg hg₁ hang heven hg0
  rcases Nat.even_or_odd (evenSpec (sqC c) ∩ Iio χ).ncard with he | ho
  · rw [he.neg_one_pow, one_mul] at h
    exact ⟨fun _ => he, fun _ => h⟩
  · rw [ho.neg_one_pow] at h
    refine ⟨fun hpos => ?_, fun he => absurd he (Nat.not_even_iff_odd.mpr ho)⟩
    linarith

/-- With no even level below `χ`, `χ` lies at or below every even level. -/
theorem le_of_ncard_eq_zero {c χ : ℝ} (h0 : (evenSpec (sqC c) ∩ Iio χ).ncard = 0) :
    ∀ χ' ∈ evenSpec (sqC c), χ ≤ χ' := by
  have hemp : evenSpec (sqC c) ∩ Iio χ = ∅ := (Set.ncard_eq_zero (finite_evenSpec_Iio _ χ)).mp h0
  intro χ' h'
  by_contra hlt
  push Not at hlt
  have : χ' ∈ evenSpec (sqC c) ∩ Iio χ := ⟨h', hlt⟩
  rw [hemp] at this
  exact this

/-- **The ground state has no zero on `[−1, 1]`**: at the first even level, `g(s) g(1) > 0` there. -/
theorem ground_pos {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (h0 : (evenSpec (sqC c) ∩ Iio χ).ncard = 0) :
    ∀ s ∈ Icc (-1 : ℝ) 1, 0 < g s * g 1 := by
  have hpos := regSol_pos_of_le_evenSpec (sqC c) (le_of_ncard_eq_zero h0)
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hang hs₀ hgs₀
  have hrep := angular_eq_mul_regSol hg hg₁ hang
  have hpos' : ∀ s ∈ Icc (0:ℝ) 1, 0 < g s * g 1 := fun s hs => by
    rw [hrep s ⟨by linarith [hs.1], hs.2⟩]
    have e : g 1 * regSol (sqC c) χ s * g 1 = (g 1 * g 1) * regSol (sqC c) χ s := by ring
    rw [e]
    exact mul_pos (mul_self_pos.mpr hg1) (hpos s hs)
  intro s hs
  rcases le_total 0 s with h | h
  · exact hpos' s ⟨h, hs.2⟩
  · have := hpos' (-s) ⟨by linarith, by linarith [hs.1]⟩
    rwa [heven s hs] at this

/-- At the first even level, `g(1) g` is antitone on `[0, 1]`. -/
theorem ground_antitoneOn {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (h0 : (evenSpec (sqC c) ∩ Iio χ).ncard = 0) :
    AntitoneOn (fun s => g 1 * g s) (Icc 0 1) := by
  have hmem := mem_evenSpec_of_angular hg hg₁ hang heven hg0
  have hQmono : MonotoneOn (sqC c) (Icc 0 1) := fun a ha b _ hab => by
    show c ^ 2 * a ^ 2 ≤ c ^ 2 * b ^ 2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.1 hab 2) (sq_nonneg c)
  have hanti := antitoneOn_regSol_first (sqC c) hQmono hmem (le_of_ncard_eq_zero h0)
  have hrep := angular_eq_mul_regSol hg hg₁ hang
  intro a ha b hb hab
  show g 1 * g b ≤ g 1 * g a
  rw [hrep a ⟨by linarith [ha.1], ha.2⟩, hrep b ⟨by linarith [hb.1], hb.2⟩]
  have := hanti ha hb hab
  have e1 : g 1 * (g 1 * regSol (sqC c) χ b) = (g 1 * g 1) * regSol (sqC c) χ b := by ring
  have e2 : g 1 * (g 1 * regSol (sqC c) χ a) = (g 1 * g 1) * regSol (sqC c) χ a := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left this (mul_self_nonneg _)

/-- **The edge–centre sign on a family with even index**, the form `CosineTransformSignLaw`'s `hsign_of_edge` takes. -/
theorem hedge_of_even_index {ι : Type*} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hidx : ∀ i, Even (evenSpec (sqC c) ∩ Iio (χ i)).ncard) :
    ∀ i, 0 < g i 0 * g i 1 := fun i => by
  have h := edge_centre_sign (hg i) (hg₁ i) (hang i) (heven i) (hg0 i)
  rwa [(hidx i).neg_one_pow, one_mul] at h

/-- **`hsign` on a family with even index**: `0 < ψᵢ(1) gᵢ(1)` for every rung (`CosineTransformSignLaw`'s `hsign_of_edge`). -/
theorem hsign_of_even_index {ι : Type*} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ} (hc : 0 < c)
    (hχ0 : ∀ i, 0 ≤ χ i)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (evenSpec (sqC c) ∩ Iio (χ i)).ncard) :
    ∀ i, 0 < Cvs.L2a.AngularProlateTailPositive.psi c (g i) 1 * g i 1 :=
  Cvs.Prolate.CosineTransformSignLaw.hsign_of_edge hc hχ0 hg hg₁ hg₂c hang heven hg0 hμ
    (hedge_of_even_index hg hg₁ hang heven hg0 hidx)

end Cvs.Prolate.EdgeCentreSign
