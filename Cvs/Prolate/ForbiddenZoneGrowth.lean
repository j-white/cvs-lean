import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Forbidden growth: the edge comparison in the forbidden zone

For a rung `ψ = ∫ g cos(cξs)` with `0 ≤ χ < c²`, on `[√χ/c, 1]` the equation reads `(Pψ')' = Qψ`, `P = 1 − s²`,
`Q = c²s² − χ ≥ 0`; with `Z(s) = ∫_s^1 √(Q/P)` and `κ_C(Z) = Z/(½ + √(Z² + 9/4))`, `y = exp(∫_0^Z κ_C)` is a positive
subsolution `(Py')' ≤ Qy` whose Wronskian with `ψ` vanishes at the edge and decreases, so `ψ(1)² y(s) ≤ ψ(s)ψ(1)`.
-/

namespace Cvs.Prolate.ForbiddenZoneGrowth

open Real Set Filter Topology MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity

/-- `κ_C(Z) = Z/(½ + √(Z² + 9/4))`. -/
noncomputable def kappaC (Z : ℝ) : ℝ := Z / (1 / 2 + √(Z ^ 2 + 9 / 4))

/-- `Φ_C(Z) = √(Z² + 9/4) − 3/2 − ½ log((½ + √(Z² + 9/4))/2)`, with `Φ_C' = κ_C` and `Φ_C(0) = 0`. -/
noncomputable def PhiC (Z : ℝ) : ℝ := √(Z ^ 2 + 9 / 4) - 3 / 2 - 1 / 2 * Real.log ((1 / 2 + √(Z ^ 2 + 9 / 4)) / 2)

/-- The forbidden-zone phase `Z(s) = ∫_s^1 √(Q/P)` in the layer variable `r = √(1 − s)`:
`∫_0^{√(1−s)} 2√(q(1 − r²))/√(2 − r²) dr`. -/
noncomputable def forbZ (c χ s : ℝ) : ℝ := ∫ r in (0 : ℝ)..√(1 - s), 2 * √(qP c χ (1 - r ^ 2)) / √(2 - r ^ 2)

/-- The comparison function `y = exp(Φ_C(Z(s)))`. -/
noncomputable def compY (c χ s : ℝ) : ℝ := Real.exp (PhiC (forbZ c χ s))

/-- Its flux `P y' = −y κ_C(Z) √(PQ)`. -/
noncomputable def compM (c χ s : ℝ) : ℝ := -(compY c χ s * kappaC (forbZ c χ s) * √((1 - s ^ 2) * qP c χ s))

theorem sqrt_nine_quarters : √((0 : ℝ) ^ 2 + 9 / 4) = 3 / 2 := by
  rw [show (0 : ℝ) ^ 2 + 9 / 4 = (3 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem PhiC_zero : PhiC 0 = 0 := by
  unfold PhiC
  rw [sqrt_nine_quarters]
  norm_num

theorem kappaC_zero : kappaC 0 = 0 := by
  unfold kappaC; simp

theorem kappaC_nonneg {Z : ℝ} (hZ : 0 ≤ Z) : 0 ≤ kappaC Z := by
  unfold kappaC
  exact div_nonneg hZ (by positivity)

/-- `d/dZ √(Z² + 9/4) = Z/√(Z² + 9/4)`. -/
theorem hasDerivAt_root (Z : ℝ) :
    HasDerivAt (fun Z : ℝ => √(Z ^ 2 + 9 / 4)) (2 * Z / (2 * √(Z ^ 2 + 9 / 4))) Z := by
  have hr : 0 < Z ^ 2 + 9 / 4 := by positivity
  have h1 : HasDerivAt (fun Z : ℝ => Z ^ 2 + 9 / 4) (2 * Z) Z := by
    have := (hasDerivAt_pow 2 Z).add_const (9 / 4 : ℝ)
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  exact h1.sqrt hr.ne'

theorem root_pos (Z : ℝ) : 0 < √(Z ^ 2 + 9 / 4) := Real.sqrt_pos.mpr (by positivity)

theorem root_sq (Z : ℝ) : √(Z ^ 2 + 9 / 4) ^ 2 = Z ^ 2 + 9 / 4 := Real.sq_sqrt (by positivity)

theorem hasDerivAt_PhiC (Z : ℝ) : HasDerivAt PhiC (kappaC Z) Z := by
  have hs := hasDerivAt_root Z
  have hr := root_pos Z
  have hne : (1 / 2 + √(Z ^ 2 + 9 / 4)) / 2 ≠ 0 := by positivity
  have hl := ((hs.const_add (1 / 2 : ℝ)).div_const 2).log hne
  have h := (hs.sub_const (3 / 2)).sub (hl.const_mul (1 / 2))
  have e : PhiC = fun Z => √(Z ^ 2 + 9 / 4) - 3 / 2 - 1 / 2 * Real.log ((1 / 2 + √(Z ^ 2 + 9 / 4)) / 2) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold kappaC
  field_simp
  ring

theorem hasDerivAt_kappaC (Z : ℝ) :
    HasDerivAt kappaC ((√(Z ^ 2 + 9 / 4) / 2 + 9 / 4) / (√(Z ^ 2 + 9 / 4) * (1 / 2 + √(Z ^ 2 + 9 / 4)) ^ 2)) Z := by
  have hs := hasDerivAt_root Z
  have hr := root_pos Z
  have hr2 := root_sq Z
  have hne : 1 / 2 + √(Z ^ 2 + 9 / 4) ≠ 0 := by positivity
  have h := (hasDerivAt_id' Z).div (hs.const_add (1 / 2 : ℝ)) hne
  have e : kappaC = fun Z => Z / (1 / 2 + √(Z ^ 2 + 9 / 4)) := rfl
  rw [e]
  refine h.congr_deriv ?_
  set r := √(Z ^ 2 + 9 / 4) with hr_def
  have hZ2 : Z * (2 * Z / (2 * r)) = (r ^ 2 - 9 / 4) / r := by
    rw [hr2]; field_simp; ring
  rw [hZ2]
  field_simp
  ring

/-- **The subsolution inequality** `κ_C' + κ_C/Z ≤ 1 − κ_C²` for `Z > 0`: it reduces to `√(Z² + 9/4) ≥ 3/2`. -/
theorem kappaC_subsolution {Z : ℝ} (hZ : 0 < Z) :
    (√(Z ^ 2 + 9 / 4) / 2 + 9 / 4) / (√(Z ^ 2 + 9 / 4) * (1 / 2 + √(Z ^ 2 + 9 / 4)) ^ 2) + kappaC Z / Z
      ≤ 1 - kappaC Z ^ 2 := by
  have hr := root_pos Z
  have hr2 := root_sq Z
  have hr32 : 3 / 2 ≤ √(Z ^ 2 + 9 / 4) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  have hκZ : kappaC Z / Z = 1 / (1 / 2 + √(Z ^ 2 + 9 / 4)) := by
    unfold kappaC; field_simp
  have hκ2 : kappaC Z ^ 2 = (√(Z ^ 2 + 9 / 4) ^ 2 - 9 / 4) / (1 / 2 + √(Z ^ 2 + 9 / 4)) ^ 2 := by
    unfold kappaC; rw [div_pow, hr2]; ring_nf
  rw [hκZ, hκ2]
  set r := √(Z ^ 2 + 9 / 4) with hr_def
  rw [← sub_nonneg]
  have e : 1 - (r ^ 2 - 9 / 4) / (1 / 2 + r) ^ 2 - ((r / 2 + 9 / 4) / (r * (1 / 2 + r) ^ 2) + 1 / (1 / 2 + r))
      = (3 / 4) * (2 * r - 3) / (r * (1 / 2 + r) ^ 2) := by
    field_simp; ring
  rw [e]
  apply div_nonneg (by linarith) (by positivity)

/-- The integrand of `Z` in the layer variable is continuous on `(−√2, √2)`. -/
theorem continuousOn_forbInt (c χ : ℝ) :
    ContinuousOn (fun r : ℝ => 2 * √(qP c χ (1 - r ^ 2)) / √(2 - r ^ 2)) (Ioo (-√2) (√2)) := by
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    apply Continuous.mul continuous_const
    apply Continuous.sqrt
    unfold qP; fun_prop
  · exact (Continuous.sqrt (by fun_prop)).continuousOn
  · intro r hr
    have h2 : r ^ 2 < 2 := by
      have := sq_lt_sq' hr.1 hr.2
      rwa [Real.sq_sqrt (by norm_num)] at this
    exact (Real.sqrt_pos.mpr (by linarith)).ne'

theorem sqrt_one_sub_mem {s : ℝ} (hs : -1 < s) : √(1 - s) ∈ Ioo (-√2) (√2) := by
  refine ⟨lt_of_lt_of_le (by rw [neg_lt_zero]; exact Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_nonneg _), ?_⟩
  exact (Real.sqrt_lt_sqrt_iff_of_pos (by norm_num)).mpr (by linarith)

theorem intervalIntegrable_forbInt (c χ : ℝ) {b : ℝ} (hb : b ∈ Ioo (-√2) (√2)) (hb0 : 0 ≤ b) :
    IntervalIntegrable (fun r : ℝ => 2 * √(qP c χ (1 - r ^ 2)) / √(2 - r ^ 2)) volume 0 b := by
  apply ContinuousOn.intervalIntegrable
  refine (continuousOn_forbInt c χ).mono ?_
  rw [uIcc_of_le hb0]
  intro r hr
  exact ⟨lt_of_lt_of_le (by rw [neg_lt_zero]; exact Real.sqrt_pos.mpr (by norm_num)) hr.1,
    lt_of_le_of_lt hr.2 hb.2⟩

theorem forbZ_one (c χ : ℝ) : forbZ c χ 1 = 0 := by
  unfold forbZ; simp

theorem forbZ_nonneg (c χ s : ℝ) : 0 ≤ forbZ c χ s := by
  unfold forbZ
  exact intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _) fun r => by positivity

theorem forbZ_pos {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hs : s ∈ Ioo (√χ / c) 1) : 0 < forbZ c χ s := by
  have ha0 : 0 ≤ √χ / c := div_nonneg (Real.sqrt_nonneg _) hc.le
  have hs0 : 0 < s := lt_of_le_of_lt ha0 hs.1
  have hb : 0 < √(1 - s) := Real.sqrt_pos.mpr (by linarith [hs.2])
  unfold forbZ
  apply intervalIntegral_pos_of_pos_on (intervalIntegrable_forbInt c χ (sqrt_one_sub_mem (by linarith)) hb.le)
    _ hb
  intro r hr
  have hr2 : r ^ 2 < 1 - s := (Real.lt_sqrt hr.1.le).mp hr.2
  have h1 : √χ / c < 1 - r ^ 2 := by linarith [hs.1]
  have h2 : √χ < c * (1 - r ^ 2) := by rwa [div_lt_iff₀ hc, mul_comm] at h1
  have hq : 0 < qP c χ (1 - r ^ 2) := by
    unfold qP
    have := pow_lt_pow_left₀ h2 (Real.sqrt_nonneg _) two_ne_zero
    rw [Real.sq_sqrt hχ0] at this
    nlinarith
  have h3 : 0 < 2 - r ^ 2 := by nlinarith
  exact div_pos (mul_pos two_pos (Real.sqrt_pos.mpr hq)) (Real.sqrt_pos.mpr h3)

theorem continuousOn_forbZ (c χ : ℝ) : ContinuousOn (forbZ c χ) (Icc 0 1) := by
  have h1 : (1 : ℝ) ∈ Ioo (-√2) (√2) := by
    have h := sqrt_one_sub_mem (s := 0) (by norm_num)
    rwa [sub_zero, Real.sqrt_one] at h
  have hI : IntervalIntegrable (fun r : ℝ => 2 * √(qP c χ (1 - r ^ 2)) / √(2 - r ^ 2)) volume 0 1 :=
    intervalIntegrable_forbInt c χ h1 zero_le_one
  have hF : ContinuousOn (fun b => ∫ r in (0 : ℝ)..b, 2 * √(qP c χ (1 - r ^ 2)) / √(2 - r ^ 2)) (uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval' hI (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
  have hg : ContinuousOn (fun s : ℝ => √(1 - s)) (Icc 0 1) := (Continuous.sqrt (by fun_prop)).continuousOn
  have hmaps : MapsTo (fun s : ℝ => √(1 - s)) (Icc 0 1) (uIcc 0 1) := by
    intro s hs
    rw [uIcc_of_le zero_le_one]
    exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (by linarith [hs.1])⟩
  exact hF.comp hg hmaps

/-- `Z' = −√(Q/P)` on `(−1, 1)`. -/
theorem hasDerivAt_forbZ (c χ : ℝ) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (forbZ c χ) (-(√(qP c χ s) / √(1 - s ^ 2))) s := by
  have hb := sqrt_one_sub_mem hs.1
  have h1s : 0 < 1 - s := by linarith [hs.2]
  have h1s' : 0 < 1 + s := by linarith [hs.1]
  have hF : HasDerivAt (fun b => ∫ r in (0 : ℝ)..b, 2 * √(qP c χ (1 - r ^ 2)) / √(2 - r ^ 2))
      (2 * √(qP c χ (1 - √(1 - s) ^ 2)) / √(2 - √(1 - s) ^ 2)) (√(1 - s)) :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_forbInt c χ hb (Real.sqrt_nonneg _))
      ((continuousOn_forbInt c χ).stronglyMeasurableAtFilter isOpen_Ioo _ hb)
      ((continuousOn_forbInt c χ).continuousAt (isOpen_Ioo.mem_nhds hb))
  have hg : HasDerivAt (fun s : ℝ => √(1 - s)) (-1 / (2 * √(1 - s))) s :=
    ((hasDerivAt_id' s).const_sub 1).sqrt h1s.ne'
  have e : forbZ c χ = (fun b => ∫ r in (0 : ℝ)..b, 2 * √(qP c χ (1 - r ^ 2)) / √(2 - r ^ 2))
      ∘ (fun s : ℝ => √(1 - s)) := rfl
  rw [e]
  refine (hF.comp s hg).congr_deriv ?_
  rw [Real.sq_sqrt h1s.le, show (1 : ℝ) - (1 - s) = s by ring, show (2 : ℝ) - (1 - s) = 1 + s by ring,
    show (1 : ℝ) - s ^ 2 = (1 + s) * (1 - s) by ring, Real.sqrt_mul h1s'.le]
  have hp : 0 < √(1 + s) := Real.sqrt_pos.mpr h1s'
  have hm : 0 < √(1 - s) := Real.sqrt_pos.mpr h1s
  field_simp

/-- `Z(s) ≤ σ√(1 − s²)/s` on `(√χ/c, 1]`, `σ = √(c² − χ)`: both sides vanish at `1` and `√Q ≤ σ/s²`. -/
theorem forbZ_mul_le {c χ s : ℝ} (hc : 0 < c) (hs : s ∈ Ioc (√χ / c) 1) :
    forbZ c χ s * s ≤ √(c ^ 2 - χ) * √(1 - s ^ 2) := by
  have ha0 : 0 ≤ √χ / c := div_nonneg (Real.sqrt_nonneg _) hc.le
  have hs0 : 0 < s := lt_of_le_of_lt ha0 hs.1
  have hσ : 0 ≤ √(c ^ 2 - χ) := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · subst h1; rw [forbZ_one]; simp
  -- `G(t) = σ√(1 − t²)/t − Z(t)` is antitone on `[s, 1]` and vanishes at `1`
  set G : ℝ → ℝ := fun t => √(c ^ 2 - χ) * √(1 - t ^ 2) / t - forbZ c χ t with hG
  have hGc : ContinuousOn G (Icc s 1) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.div (Continuous.continuousOn (continuous_const.mul (Continuous.sqrt (by fun_prop))))
        continuousOn_id
      intro t ht; exact (lt_of_lt_of_le hs0 ht.1).ne'
    · exact (continuousOn_forbZ c χ).mono (Icc_subset_Icc hs0.le le_rfl)
  have hGd : ∀ t ∈ Ioo s 1, HasDerivAt G
      ((√(c ^ 2 - χ) * (-(2 * t) / (2 * √(1 - t ^ 2))) * t - √(c ^ 2 - χ) * √(1 - t ^ 2) * 1) / t ^ 2
        - -(√(qP c χ t) / √(1 - t ^ 2))) t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hs0 ht.1
    have hP : 0 < 1 - t ^ 2 := by nlinarith [ht.2]
    have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
      have := (hasDerivAt_pow 2 t).const_sub 1
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    have h2 := ((h1.sqrt hP.ne').const_mul (√(c ^ 2 - χ))).div (hasDerivAt_id' t) ht0.ne'
    exact h2.sub (hasDerivAt_forbZ c χ ⟨by linarith, ht.2⟩)
  have hanti : AntitoneOn G (Icc s 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc s 1) hGc
    · rw [interior_Icc]; exact fun t ht => (hGd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      rw [(hGd t ht).deriv]
      have ht0 : 0 < t := lt_trans hs0 ht.1
      have hP : 0 < 1 - t ^ 2 := by nlinarith [ht.2]
      have hsP : 0 < √(1 - t ^ 2) := Real.sqrt_pos.mpr hP
      have hsP2 : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hP.le
      -- `√Q ≤ σ ≤ σ/t²`
      have hQ : qP c χ t ≤ c ^ 2 - χ := by unfold qP; nlinarith [ht.2]
      have hsQ : √(qP c χ t) ≤ √(c ^ 2 - χ) := Real.sqrt_le_sqrt hQ
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.2]
      have hσt : √(c ^ 2 - χ) * t ^ 2 ≤ √(c ^ 2 - χ) := by nlinarith
      have e : (√(c ^ 2 - χ) * (-(2 * t) / (2 * √(1 - t ^ 2))) * t - √(c ^ 2 - χ) * √(1 - t ^ 2) * 1) / t ^ 2
          - -(√(qP c χ t) / √(1 - t ^ 2))
          = (√(qP c χ t) * t ^ 2 - √(c ^ 2 - χ)) / (t ^ 2 * √(1 - t ^ 2)) := by
        field_simp
        rw [hsP2]
        ring
      rw [e]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      nlinarith
  have h := hanti ⟨le_rfl, h1.le⟩ ⟨h1.le, le_rfl⟩ h1.le
  simp only [hG, forbZ_one, one_pow, sub_self, Real.sqrt_zero, mul_zero, zero_div] at h
  rw [sub_nonneg, div_eq_mul_inv] at h
  calc forbZ c χ s * s ≤ √(c ^ 2 - χ) * √(1 - s ^ 2) * s⁻¹ * s := mul_le_mul_of_nonneg_right h hs0.le
    _ = √(c ^ 2 - χ) * √(1 - s ^ 2) := by field_simp

/-- **The exact lemma `Z F ≤ 1`**, cleared of denominators: `Z·s(Q − c²P) ≤ Q√(PQ)` on `(√χ/c, 1)`. -/
theorem forbZ_mul_F_le {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : s ∈ Ioo (√χ / c) 1) :
    forbZ c χ s * (s * (qP c χ s - c ^ 2 * (1 - s ^ 2))) ≤ qP c χ s * √((1 - s ^ 2) * qP c χ s) := by
  have ha0 : 0 ≤ √χ / c := div_nonneg (Real.sqrt_nonneg _) hc.le
  have hs0 : 0 < s := lt_of_le_of_lt ha0 hs.1
  have hP : 0 < 1 - s ^ 2 := by nlinarith [hs.2]
  have hZ := forbZ_pos hc hχ0 hs
  have hQ : 0 < qP c χ s := by
    have h2 : √χ < c * s := by
      have h := hs.1
      rw [div_lt_iff₀ hc] at h
      linarith
    unfold qP
    have := pow_lt_pow_left₀ h2 (Real.sqrt_nonneg _) two_ne_zero
    rw [Real.sq_sqrt hχ0] at this
    nlinarith
  have hsQ : 0 < √(qP c χ s) := Real.sqrt_pos.mpr hQ
  have hsP : 0 ≤ √(1 - s ^ 2) := Real.sqrt_nonneg _
  rw [Real.sqrt_mul hP.le]
  rcases le_or_gt (qP c χ s - c ^ 2 * (1 - s ^ 2)) 0 with hD | hD
  · have : forbZ c χ s * (s * (qP c χ s - c ^ 2 * (1 - s ^ 2))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hZ.le (mul_nonpos_of_nonneg_of_nonpos hs0.le hD)
    exact this.trans (by positivity)
  · -- `Z s ≤ σ√P` and `σ(2Q − σ²) ≤ Q√Q`
    have hZs := forbZ_mul_le hc ⟨hs.1, hs.2.le⟩
    set σ := √(c ^ 2 - χ) with hσ_def
    set q := √(qP c χ s) with hq_def
    have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
    have hσ2 : σ ^ 2 = c ^ 2 - χ := Real.sq_sqrt (by linarith)
    have hq2 : q ^ 2 = qP c χ s := Real.sq_sqrt hQ.le
    have hqσ : q ≤ σ := Real.sqrt_le_sqrt (by unfold qP; nlinarith [hs.2])
    have hD' : qP c χ s - c ^ 2 * (1 - s ^ 2) = 2 * q ^ 2 - σ ^ 2 := by rw [hq2, hσ2]; unfold qP; ring
    have key : σ * (2 * q ^ 2 - σ ^ 2) ≤ q ^ 2 * q := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqσ) (show 0 ≤ σ ^ 2 + σ * q - q ^ 2 by nlinarith)]
    calc forbZ c χ s * (s * (qP c χ s - c ^ 2 * (1 - s ^ 2)))
        = forbZ c χ s * s * (qP c χ s - c ^ 2 * (1 - s ^ 2)) := by ring
      _ ≤ σ * √(1 - s ^ 2) * (qP c χ s - c ^ 2 * (1 - s ^ 2)) := mul_le_mul_of_nonneg_right hZs hD.le
      _ = √(1 - s ^ 2) * (σ * (2 * q ^ 2 - σ ^ 2)) := by rw [hD']; ring
      _ ≤ √(1 - s ^ 2) * (q ^ 2 * q) := mul_le_mul_of_nonneg_left key hsP
      _ = qP c χ s * (√(1 - s ^ 2) * q) := by rw [hq2]; ring

theorem compY_pos (c χ s : ℝ) : 0 < compY c χ s := Real.exp_pos _

theorem compY_one (c χ : ℝ) : compY c χ 1 = 1 := by
  unfold compY; rw [forbZ_one, PhiC_zero, Real.exp_zero]

theorem continuous_PhiC : Continuous PhiC :=
  continuous_iff_continuousAt.mpr fun Z => (hasDerivAt_PhiC Z).continuousAt

theorem continuous_kappaC : Continuous kappaC :=
  continuous_iff_continuousAt.mpr fun Z => (hasDerivAt_kappaC Z).continuousAt

theorem continuousOn_compY (c χ : ℝ) : ContinuousOn (compY c χ) (Icc 0 1) :=
  (Real.continuous_exp.comp continuous_PhiC).comp_continuousOn (continuousOn_forbZ c χ)

theorem hasDerivAt_compY {c χ s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (compY c χ) (-(compY c χ s * kappaC (forbZ c χ s) * (√(qP c χ s) / √(1 - s ^ 2)))) s := by
  have h := ((hasDerivAt_PhiC (forbZ c χ s)).comp s (hasDerivAt_forbZ c χ hs)).exp
  refine h.congr_deriv ?_
  unfold compY
  simp only [Function.comp]
  ring

/-- **The comparison function is a subsolution**: `(P y')' = Q y (κ² + κ_Z + κF) ≤ Q y` on `(√χ/c, 1)`. -/
theorem compM_subsolution {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : s ∈ Ioo (√χ / c) 1) :
    ∃ R : ℝ, HasDerivAt (compM c χ) R s ∧ R ≤ qP c χ s * compY c χ s := by
  have ha0 : 0 ≤ √χ / c := div_nonneg (Real.sqrt_nonneg _) hc.le
  have hs0 : 0 < s := lt_of_le_of_lt ha0 hs.1
  have hs' : s ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hs.2⟩
  have hP : 0 < 1 - s ^ 2 := by nlinarith [hs.2]
  have hZ := forbZ_pos hc hχ0 hs
  have hQ : 0 < qP c χ s := by
    have h2 : √χ < c * s := by
      have h := hs.1
      rw [div_lt_iff₀ hc] at h
      linarith
    unfold qP
    have := pow_lt_pow_left₀ h2 (Real.sqrt_nonneg _) two_ne_zero
    rw [Real.sq_sqrt hχ0] at this
    nlinarith
  have hF := forbZ_mul_F_le hc hχ0 hχc hs
  have hsub := kappaC_subsolution hZ
  have hy := hasDerivAt_compY (c := c) (χ := χ) hs'
  have hκ := (hasDerivAt_kappaC (forbZ c χ s)).comp s (hasDerivAt_forbZ c χ hs')
  have hPQ : HasDerivAt (fun s : ℝ => (1 - s ^ 2) * qP c χ s)
      (-(2 * s) * qP c χ s + (1 - s ^ 2) * (2 * c ^ 2 * s)) s := by
    have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * s)) s := by
      have := (hasDerivAt_pow 2 s).const_sub 1
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    have h2 : HasDerivAt (qP c χ) (2 * c ^ 2 * s) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (c ^ 2)).sub_const χ
      have e : qP c χ = fun t => c ^ 2 * t ^ 2 - χ := rfl
      rw [e]; refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
    exact h1.mul h2
  have hA := hPQ.sqrt (mul_pos hP hQ).ne'
  have hκ' : HasDerivAt (fun t => kappaC (forbZ c χ t))
      ((√(forbZ c χ s ^ 2 + 9 / 4) / 2 + 9 / 4) /
        (√(forbZ c χ s ^ 2 + 9 / 4) * (1 / 2 + √(forbZ c χ s ^ 2 + 9 / 4)) ^ 2) *
          -(√(qP c χ s) / √(1 - s ^ 2))) s := hκ
  have hM := ((hy.fun_mul hκ').fun_mul hA).fun_neg
  refine ⟨_, hM, ?_⟩
  -- the derivative in closed form
  have hsP : 0 < √(1 - s ^ 2) := Real.sqrt_pos.mpr hP
  have hsQ : 0 < √(qP c χ s) := Real.sqrt_pos.mpr hQ
  have hA' : √((1 - s ^ 2) * qP c χ s) = √(1 - s ^ 2) * √(qP c χ s) := Real.sqrt_mul hP.le _
  set y := compY c χ s with hy_def
  set Z := forbZ c χ s with hZ_def
  set κ := kappaC Z with hκ_def
  set κ' := (√(Z ^ 2 + 9 / 4) / 2 + 9 / 4) / (√(Z ^ 2 + 9 / 4) * (1 / 2 + √(Z ^ 2 + 9 / 4)) ^ 2) with hκ'_def
  set p := √(1 - s ^ 2) with hp_def
  set q := √(qP c χ s) with hq_def
  have hp2 : p ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hP.le
  have hq2 : q ^ 2 = qP c χ s := Real.sq_sqrt hQ.le
  have hy0 := compY_pos c χ s
  have hκ0 : 0 ≤ κ := kappaC_nonneg hZ.le
  rw [hA']
  have hR : -((-(y * κ * (q / p)) * κ + y * (κ' * -(q / p))) * (p * q)
      + y * κ * ((-(2 * s) * qP c χ s + (1 - s ^ 2) * (2 * c ^ 2 * s)) / (2 * (p * q))))
      = qP c χ s * y * (κ ^ 2 + κ') + y * κ * (s * (qP c χ s - c ^ 2 * (1 - s ^ 2)) / (p * q)) := by
    rw [← hq2, ← hp2]
    field_simp
    ring
  rw [hR]
  -- `s(Q − c²P)/(pq) ≤ Q/Z` from `Z·s(Q − c²P) ≤ Q·pq`
  have hFle : s * (qP c χ s - c ^ 2 * (1 - s ^ 2)) / (p * q) ≤ qP c χ s / Z := by
    rw [div_le_div_iff₀ (by positivity) hZ]
    rw [hA'] at hF
    linarith [hF]
  have hκsub : κ ^ 2 + κ' + κ / Z ≤ 1 := by linarith [hsub]
  calc qP c χ s * y * (κ ^ 2 + κ') + y * κ * (s * (qP c χ s - c ^ 2 * (1 - s ^ 2)) / (p * q))
      ≤ qP c χ s * y * (κ ^ 2 + κ') + y * κ * (qP c χ s / Z) := by
        have := mul_le_mul_of_nonneg_left hFle (by positivity : (0 : ℝ) ≤ y * κ)
        linarith
    _ = qP c χ s * y * (κ ^ 2 + κ' + κ / Z) := by field_simp
    _ ≤ qP c χ s * y * 1 := mul_le_mul_of_nonneg_left hκsub (by positivity)
    _ = qP c χ s * y := mul_one _

/-- The rung's `(ψ, u)` system inside the window: `ψ' = u/p` on `(−1, 1)` (the mirror of `rung_system`). -/
theorem rung_system_forbidden {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    ∀ ξ ∈ Ioo (-1 : ℝ) 1, HasDerivAt (psi c g) (rungU c g ξ / pP ξ) ξ := by
  obtain ⟨hψ, -, -⟩ := psi_system hg hg₁ hg₂c hang
  intro ξ hξ
  have hp : pP ξ ≠ 0 := by
    unfold pP
    have : ξ ^ 2 < 1 := by nlinarith [hξ.1, hξ.2]
    linarith
  unfold rungU; rw [mul_div_cancel_left₀ _ hp]; exact hψ ξ

/-- **`ψu` is antitone in the forbidden zone**: `(ψu)' = u²/p − qψ² ≤ 0` where `p < 0 ≤ q`. -/
theorem mul_flux_antitoneOn {ψ u : ℝ → ℝ} {c χ a : ℝ} (ha0 : 0 ≤ a)
    (hψ : ∀ s ∈ Ico a 1, HasDerivAt ψ (u s / pP s) s) (hψc : ContinuousOn ψ (Icc a 1))
    (hu : ∀ s ∈ Icc a 1, HasDerivAt u (-(qP c χ s * ψ s)) s) (hq : ∀ s ∈ Icc a 1, 0 ≤ qP c χ s) :
    AntitoneOn (fun s => ψ s * u s) (Icc a 1) := by
  have huc : ContinuousOn u (Icc a 1) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hd : ∀ s ∈ Ioo a 1, HasDerivAt (fun s => ψ s * u s) (u s / pP s * u s + ψ s * -(qP c χ s * ψ s)) s :=
    fun s hs => (hψ s (Ioo_subset_Ico_self hs)).mul (hu s (Ioo_subset_Icc_self hs))
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a 1) (hψc.mul huc)
    (f' := fun s => u s / pP s * u s + ψ s * -(qP c χ s * ψ s))
  · rw [interior_Icc]; exact fun s hs => (hd s hs).hasDerivWithinAt
  · rw [interior_Icc]; intro s hs
    have hp : pP s < 0 := by unfold pP; nlinarith [hs.1, hs.2]
    have h1 : u s / pP s * u s ≤ 0 := by
      rw [div_mul_eq_mul_div, div_nonpos_iff]; left; exact ⟨by nlinarith [sq_nonneg (u s)], hp.le⟩
    have h2 : ψ s * -(qP c χ s * ψ s) ≤ 0 := by
      nlinarith [mul_nonneg (hq s (Ioo_subset_Icc_self hs)) (sq_nonneg (ψ s))]
    linarith

/-- **`ψ²` is antitone in the forbidden zone**: `ψu ≥ 0` from `u(1) = 0`, so `(ψ²)' = 2ψu/p ≤ 0`. -/
theorem sq_antitoneOn {ψ u : ℝ → ℝ} {c χ a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hψ : ∀ s ∈ Ico a 1, HasDerivAt ψ (u s / pP s) s) (hψc : ContinuousOn ψ (Icc a 1))
    (hu : ∀ s ∈ Icc a 1, HasDerivAt u (-(qP c χ s * ψ s)) s) (hu1 : u 1 = 0)
    (hq : ∀ s ∈ Icc a 1, 0 ≤ qP c χ s) :
    (∀ s ∈ Icc a 1, 0 ≤ ψ s * u s) ∧ AntitoneOn (fun s => ψ s ^ 2) (Icc a 1) := by
  have hanti := mul_flux_antitoneOn ha0 hψ hψc hu hq
  have hpu : ∀ s ∈ Icc a 1, 0 ≤ ψ s * u s := fun s hs => by
    have := hanti hs ⟨ha1.le, le_rfl⟩ hs.2
    simp only [hu1, mul_zero] at this
    exact this
  refine ⟨hpu, ?_⟩
  have hd : ∀ s ∈ Ioo a 1, HasDerivAt (fun s => ψ s ^ 2) (2 * ψ s * (u s / pP s)) s := fun s hs => by
    have := (hψ s (Ioo_subset_Ico_self hs)).pow 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a 1) (hψc.pow 2)
    (f' := fun s => 2 * ψ s * (u s / pP s))
  · rw [interior_Icc]; exact fun s hs => (hd s hs).hasDerivWithinAt
  · rw [interior_Icc]; intro s hs
    have hp : pP s < 0 := by unfold pP; nlinarith [hs.1, hs.2]
    rw [show 2 * ψ s * (u s / pP s) = 2 * (ψ s * u s) / pP s by ring, div_nonpos_iff]
    left; exact ⟨by linarith [hpu s (Ioo_subset_Icc_self hs)], hp.le⟩

/-- **The edge is the minimum**: with `ψ(1) > 0`, `ψ(1) ≤ ψ(s)` and `0 ≤ u(s)` on `[a, 1]` (sign by
`intermediate_value_Icc`). -/
theorem edge_le_of_forbidden {ψ u : ℝ → ℝ} {c χ a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hψ : ∀ s ∈ Ico a 1, HasDerivAt ψ (u s / pP s) s) (hψc : ContinuousOn ψ (Icc a 1))
    (hu : ∀ s ∈ Icc a 1, HasDerivAt u (-(qP c χ s * ψ s)) s) (hu1 : u 1 = 0)
    (hq : ∀ s ∈ Icc a 1, 0 ≤ qP c χ s) (h1 : 0 < ψ 1) :
    ∀ s ∈ Icc a 1, ψ 1 ≤ ψ s ∧ 0 ≤ u s := by
  obtain ⟨hpu, hanti⟩ := sq_antitoneOn ha0 ha1 hψ hψc hu hu1 hq
  have hsq : ∀ s ∈ Icc a 1, ψ 1 ^ 2 ≤ ψ s ^ 2 := fun s hs => hanti hs ⟨ha1.le, le_rfl⟩ hs.2
  intro s hs
  -- `ψ` has no zero on `[a, 1]`, so it has the sign of `ψ(1)`
  have hpos : 0 < ψ s := by
    by_contra hcon
    push Not at hcon
    have hivt := intermediate_value_Icc hs.2 (hψc.mono (Icc_subset_Icc hs.1 le_rfl))
    obtain ⟨t, ht, ht0⟩ := hivt ⟨hcon, h1.le⟩
    have := hsq t ⟨hs.1.trans ht.1, ht.2⟩
    rw [ht0] at this
    nlinarith
  refine ⟨?_, (mul_nonneg_iff_of_pos_left hpos).mp (hpu s hs)⟩
  have := sq_le_sq.mp (hsq s hs)
  rwa [abs_of_pos h1, abs_of_pos hpos] at this

/-- **The edge comparison**: `ψ ≥ 0` with `(Pψ')' = Qψ`, `y > 0` with `(Py')' ≤ Qy`, and the Wronskian
`ψ·Py' − y·Pψ' = ψm + yu → 0` at `1⁻`: then `ψ(1) y(s) ≤ ψ(s) y(1)` on `(a, 1)`. -/
theorem edge_comparison {ψ ψ' u y y' m P Q : ℝ → ℝ} {a : ℝ} (ha : a < 1)
    (hP : ∀ s ∈ Ioo a 1, 0 < P s) (hψ0 : ∀ s ∈ Ioo a 1, 0 ≤ ψ s) (hy0 : ∀ s ∈ Ioc a 1, 0 < y s)
    (hψ : ∀ s ∈ Ioo a 1, HasDerivAt ψ (ψ' s) s) (hu : ∀ s ∈ Ioo a 1, u s = -(P s * ψ' s))
    (hu' : ∀ s ∈ Ioo a 1, HasDerivAt u (-(Q s * ψ s)) s)
    (hy : ∀ s ∈ Ioo a 1, HasDerivAt y (y' s) s) (hm : ∀ s ∈ Ioo a 1, m s = P s * y' s)
    (hm' : ∀ s ∈ Ioo a 1, ∃ R, HasDerivAt m R s ∧ R ≤ Q s * y s)
    (hψc : ContinuousOn ψ (Ioc a 1)) (hyc : ContinuousOn y (Ioc a 1))
    (hW : Filter.Tendsto (fun s => ψ s * m s + y s * u s) (𝓝[<] 1) (𝓝 0)) :
    ∀ s ∈ Ioo a 1, ψ 1 * y s ≤ ψ s * y 1 := by
  set W : ℝ → ℝ := fun s => ψ s * m s + y s * u s with hW_def
  -- `W' = ψ(R − Qy) ≤ 0`, so `W` is antitone on `(a, 1)`
  have hWd : ∀ s ∈ Ioo a 1, ∃ R, HasDerivAt W (ψ' s * m s + ψ s * R + (y' s * u s + y s * -(Q s * ψ s))) s
      ∧ R ≤ Q s * y s := fun s hs => by
    obtain ⟨R, hR, hRle⟩ := hm' s hs
    exact ⟨R, ((hψ s hs).mul hR).add ((hy s hs).mul (hu' s hs)), hRle⟩
  have hWanti : AntitoneOn W (Ioo a 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo a 1)
    · intro s hs; obtain ⟨R, hR, -⟩ := hWd s hs; exact hR.continuousAt.continuousWithinAt
    · rw [interior_Ioo]; intro s hs; obtain ⟨R, hR, -⟩ := hWd s hs
      exact hR.differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]; intro s hs; obtain ⟨R, hR, hRle⟩ := hWd s hs
      rw [hR.deriv, hu s hs, hm s hs]
      have : ψ' s * (P s * y' s) + ψ s * R + (y' s * -(P s * ψ' s) + y s * -(Q s * ψ s))
          = ψ s * (R - Q s * y s) := by ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos (hψ0 s hs) (by linarith)
  -- `W ≥ 0` on `(a, 1)` from the edge limit
  have hW0 : ∀ s ∈ Ioo a 1, 0 ≤ W s := fun s hs => by
    apply le_of_tendsto hW
    filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
    exact hWanti hs ⟨hs.1.trans ht.1, ht.2⟩ ht.1.le
  -- `(ψ/y)' = −W/(Py²) ≤ 0`
  intro s hs
  have hd : ∀ t ∈ Ioo s 1, HasDerivAt (fun t => ψ t / y t) ((ψ' t * y t - ψ t * y' t) / y t ^ 2) t :=
    fun t ht => (hψ t ⟨hs.1.trans ht.1, ht.2⟩).div (hy t ⟨hs.1.trans ht.1, ht.2⟩)
      (hy0 t ⟨hs.1.trans ht.1, ht.2.le⟩).ne'
  have hcont : ContinuousOn (fun t => ψ t / y t) (Icc s 1) := by
    have hsub : Icc s 1 ⊆ Ioc a 1 := fun t ht => ⟨lt_of_lt_of_le hs.1 ht.1, ht.2⟩
    exact (hψc.mono hsub).div (hyc.mono hsub) fun t ht => (hy0 t (hsub ht)).ne'
  have hanti : AntitoneOn (fun t => ψ t / y t) (Icc s 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc s 1) hcont
    · rw [interior_Icc]; exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      have ht' : t ∈ Ioo a 1 := ⟨hs.1.trans ht.1, ht.2⟩
      rw [(hd t ht).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      have h0 := hW0 t ht'
      simp only [hW_def, hu t ht', hm t ht'] at h0
      have e : ψ t * (P t * y' t) + y t * -(P t * ψ' t) = P t * (ψ t * y' t - ψ' t * y t) := by ring
      rw [e] at h0
      have := (mul_nonneg_iff_of_pos_left (hP t ht')).mp h0
      linarith
  have h := hanti ⟨le_rfl, hs.2.le⟩ ⟨hs.2.le, le_rfl⟩ hs.2.le
  simp only at h
  have hys := hy0 s ⟨hs.1, hs.2.le⟩
  have hy1 := hy0 1 ⟨ha, le_rfl⟩
  rwa [div_le_div_iff₀ hy1 hys] at h

/-- **Forbidden growth for a positive edge**: a `(ψ, u)` system on `(−1, 1)` with `u(1) = 0`, `ψ(1) > 0` has
`ψ(1) y(s) ≤ ψ(s)` on `[√χ/c, 1]`. -/
theorem forbidden_growth_of_pos {ψ u : ℝ → ℝ} {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ s ∈ Ioo (-1 : ℝ) 1, HasDerivAt ψ (u s / pP s) s) (hψc : Continuous ψ)
    (hu : ∀ s, HasDerivAt u (-(qP c χ s * ψ s)) s) (huc : Continuous u) (hu1 : u 1 = 0) (h1 : 0 < ψ 1) :
    ∀ s ∈ Icc (√χ / c) 1, ψ 1 * compY c χ s ≤ ψ s := by
  set a := √χ / c with ha_def
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hc.le
  have ha1 : a < 1 := by rw [ha_def, div_lt_one hc, Real.sqrt_lt' hc]; exact hχc
  have hq : ∀ s ∈ Icc a 1, 0 ≤ qP c χ s := fun s hs => by
    have h2 : √χ ≤ c * s := by
      have h := hs.1
      rw [ha_def, div_le_iff₀ hc] at h
      linarith
    unfold qP
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    rw [Real.sq_sqrt hχ0] at this
    nlinarith
  have hψ' : ∀ s ∈ Ico a 1, HasDerivAt ψ (u s / pP s) s := fun s hs => hψ s ⟨by linarith [hs.1], hs.2⟩
  have hedge := edge_le_of_forbidden ha0 ha1 hψ' hψc.continuousOn (fun s _ => hu s) hu1 hq h1
  have hP : ∀ s ∈ Ioo a 1, 0 < 1 - s ^ 2 := fun s hs => by nlinarith [hs.1, hs.2]
  -- the Wronskian vanishes at the edge
  have hWc : ContinuousOn (fun s => ψ s * compM c χ s + compY c χ s * u s) (Icc 0 1) := by
    have hκZ : ContinuousOn (fun s => kappaC (forbZ c χ s)) (Icc 0 1) :=
      continuous_kappaC.comp_continuousOn (continuousOn_forbZ c χ)
    have hA : Continuous (fun s : ℝ => √((1 - s ^ 2) * qP c χ s)) := by
      apply Continuous.sqrt; unfold qP; fun_prop
    have hM : ContinuousOn (compM c χ) (Icc 0 1) :=
      (((continuousOn_compY c χ).mul hκZ).mul hA.continuousOn).neg
    exact (hψc.continuousOn.mul hM).add ((continuousOn_compY c χ).mul huc.continuousOn)
  have hW1 : ψ 1 * compM c χ 1 + compY c χ 1 * u 1 = 0 := by
    simp [compM, compY_one, forbZ_one, kappaC_zero, hu1]
  have hW : Filter.Tendsto (fun s => ψ s * compM c χ s + compY c χ s * u s) (𝓝[<] 1) (𝓝 0) := by
    have h := (hWc 1 ⟨zero_le_one, le_rfl⟩).tendsto
    rw [hW1] at h
    refine h.mono_left ?_
    exact (nhdsWithin_le_of_mem (Ioo_mem_nhdsLT zero_lt_one)).trans (nhdsWithin_mono _ Ioo_subset_Icc_self)
  have hcomp := edge_comparison (ψ := ψ) (ψ' := fun s => u s / pP s) (u := u) (y := compY c χ)
    (y' := fun s => -(compY c χ s * kappaC (forbZ c χ s) * (√(qP c χ s) / √(1 - s ^ 2))))
    (m := compM c χ) (P := fun s => 1 - s ^ 2) (Q := qP c χ) ha1 hP
    (fun s hs => le_trans h1.le (hedge s (Ioo_subset_Icc_self hs)).1) (fun s _ => compY_pos c χ s)
    (fun s hs => hψ s ⟨by linarith [hs.1], hs.2⟩)
    (fun s hs => by
      have hp : pP s ≠ 0 := by unfold pP; linarith [hP s hs]
      unfold pP at hp ⊢; field_simp; ring)
    (fun s _ => hu s)
    (fun s hs => hasDerivAt_compY ⟨by linarith [hs.1], hs.2⟩)
    (fun s hs => by
      have hPs := hP s hs
      unfold compM
      rw [Real.sqrt_mul hPs.le]
      set p := √(1 - s ^ 2) with hp_def
      have hp2 : p ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hPs.le
      have hp0 : p ≠ 0 := (Real.sqrt_pos.mpr hPs).ne'
      rw [← hp2]
      field_simp)
    (fun s hs => compM_subsolution hc hχ0 hχc hs)
    hψc.continuousOn ((continuousOn_compY c χ).mono fun s hs => ⟨ha0.trans hs.1.le, hs.2⟩) hW
  -- close up to the endpoints by continuity
  intro s hs
  have hcl : s ∈ closure (Ioo a 1) := by rw [closure_Ioo ha1.ne]; exact hs
  refine ContinuousWithinAt.closure_le (f := fun t => ψ 1 * compY c χ t) hcl ?_
    hψc.continuousAt.continuousWithinAt ?_
  · exact continuousWithinAt_const.mul
      ((continuousOn_compY c χ s ⟨ha0.trans hs.1, hs.2⟩).mono fun t ht => ⟨ha0.trans ht.1.le, ht.2.le⟩)
  · intro t ht
    have := hcomp t ht
    rwa [compY_one, mul_one] at this

/-- **Forbidden growth**: for a rung with `0 ≤ χ < c²` and `s ∈ [√χ/c, 1]`, `ψ(1)² exp(Φ_C(Z(s))) ≤ ψ(s) ψ(1)`. -/
theorem forbidden_growth {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {s : ℝ} (hs : s ∈ Icc (√χ / c) 1) :
    psi c g 1 ^ 2 * Real.exp (PhiC (forbZ c χ s)) ≤ psi c g s * psi c g 1 := by
  have hψ := rung_system_forbidden hg hg₁ hg₂c hang
  obtain ⟨-, hu, hψc, huc⟩ := rung_system hg hg₁ hg₂c hang
  have hu1 : rungU c g 1 = 0 := by unfold rungU pP; simp
  show psi c g 1 ^ 2 * compY c χ s ≤ psi c g s * psi c g 1
  rcases lt_trichotomy (psi c g 1) 0 with h1 | h1 | h1
  · -- the mirror system `(−ψ, −u)`
    have hψn : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun t => -psi c g t) (-rungU c g t / pP t) t :=
      fun t ht => by rw [neg_div]; exact (hψ t ht).neg
    have hun : ∀ t, HasDerivAt (fun t => -rungU c g t) (-(qP c χ t * -psi c g t)) t :=
      fun t => (hu t).neg.congr_deriv (by ring)
    have h := forbidden_growth_of_pos hc hχ0 hχc hψn hψc.neg hun huc.neg (by simp [hu1])
      (by simpa using h1) s hs
    nlinarith [mul_le_mul_of_nonpos_left h h1.le]
  · rw [h1]; simp
  · have h := forbidden_growth_of_pos hc hχ0 hχc hψ hψc hu huc hu1 h1 s hs
    nlinarith [mul_le_mul_of_nonneg_left h h1.le]

/-- **Forbidden growth, squared**: `ψ(1)² exp(2Φ_C(Z(s))) ≤ ψ(s)²` on `[√χ/c, 1]`. -/
theorem forbidden_growth_sq {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {s : ℝ} (hs : s ∈ Icc (√χ / c) 1) :
    psi c g 1 ^ 2 * Real.exp (2 * PhiC (forbZ c χ s)) ≤ psi c g s ^ 2 := by
  have h := forbidden_growth hc hχ0 hχc hg hg₁ hg₂c hang hs
  have he : Real.exp (2 * PhiC (forbZ c χ s)) = Real.exp (PhiC (forbZ c χ s)) ^ 2 := by
    rw [sq, ← Real.exp_add, two_mul]
  rw [he]
  rcases eq_or_ne (psi c g 1) 0 with h1 | h1
  · rw [h1]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]; positivity
  have hpos : 0 < psi c g 1 ^ 2 := by positivity
  have h0 : 0 ≤ psi c g 1 ^ 2 * Real.exp (PhiC (forbZ c χ s)) := by positivity
  have hsq := pow_le_pow_left₀ h0 h 2
  have e : (psi c g 1 ^ 2 * Real.exp (PhiC (forbZ c χ s))) ^ 2
      = psi c g 1 ^ 2 * Real.exp (PhiC (forbZ c χ s)) ^ 2 * psi c g 1 ^ 2 := by ring
  have e' : (psi c g s * psi c g 1) ^ 2 = psi c g s ^ 2 * psi c g 1 ^ 2 := by ring
  rw [e, e'] at hsq
  exact le_of_mul_le_mul_right hsq hpos

end Cvs.Prolate.ForbiddenZoneGrowth
