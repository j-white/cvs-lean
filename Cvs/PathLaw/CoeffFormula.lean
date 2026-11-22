/-
The Fourier coefficient product formula (rapid-decay campaign, stage 3).

For a base amplitude `b` vanishing outside the open long-base interval
`(0, ℓ)`, `ℓ = 1 - (m-1)β`, the capacity-family rung function is the
plain (indicator-free) sum of translated bumps,

  rungFun(x) = ∑_{p<m} b(x - pβ) · sin((p+1)θ_j)  on [0,1],

because a translated bump is nonzero only inside its own window. Its
circle Fourier coefficients therefore factor:

  c_n(rungFun) = (∑_{p<m} sin((p+1)θ_j) · e_{-n}(pβ)) · ∫₀¹ e_{-n}(t) b(t) dt,

a bounded discrete factor times the coefficients of the single bump.
Combined with `rapidFourierDecay_of_smooth_bump` (stage 1) and
`RapidFourierDecay.mul_bounded`, this makes the coefficients of the
bump-modulated top eigenfunction rapidly decaying.
-/
import Cvs.PathLaw.GevreyEigen

open MeasureTheory Real
open scoped ContDiff

namespace Cvs.PathLaw

local notation "𝕋₁" => AddCircle (1 : ℝ)

/-- The character property in the point argument. -/
lemma fourier_point_add {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp_rw [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

section Model

variable (β : ℝ)

/-- **The indicator-free window model.** If the amplitude vanishes
outside the open long-base interval, the capacity-family rung function
on `[0,1]` is the plain sum of translated, envelope-weighted bumps. -/
theorem rungFun_coe_eq_sum (hβ : 0 < β) (j : Fin (capacity 1 β))
    (b : ℝ → ℝ)
    (hb0 : ∀ t, t ∉ Set.Ioo (0 : ℝ)
      (1 - ((capacity 1 β : ℝ) - 1) * β) → b t = 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    rungFun β (capacity 1 β) j b ((x : ℝ) : 𝕋₁)
      = ∑ p ∈ Finset.range (capacity 1 β),
          b (x - (p : ℝ) * β)
            * Real.sin (((p : ℝ) + 1) * pathAngle (capacity 1 β) j) := by
  have hℓpos : 0 < 1 - ((capacity 1 β : ℝ) - 1) * β := by
    have := capacity_sub_one_mul_lt β hβ
    linarith
  have hm0 : 0 < capacity 1 β := one_le_capacity β hβ
  have hIoo_sub : ∀ p : ℕ, ∀ y : ℝ,
      y - (p : ℝ) * β ∈ Set.Ioo (0 : ℝ)
        (1 - ((capacity 1 β : ℝ) - 1) * β) →
      y ∈ Set.Ico ((p : ℝ) * β)
        ((p : ℝ) * β + (1 - ((capacity 1 β : ℝ) - 1) * β)) := by
    intro p y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rcases eq_or_lt_of_le hx.2 with hx1 | hx1
  · -- the endpoint `x = 1` wraps to `0`; both sides vanish
    subst hx1
    have h1 : (((1 : ℝ)) : 𝕋₁) = (((0 : ℝ)) : 𝕋₁) := by
      rw [AddCircle.coe_period]
      simp
    have hzero_mem : (0 : ℝ) ∈ Set.Ico ((0 : ℝ) * β)
        ((0 : ℝ) * β + (1 - ((capacity 1 β : ℝ) - 1) * β)) := by
      constructor
      · simp
      · simpa using hℓpos
    have hLHS : rungFun β (capacity 1 β) j b (((1 : ℝ)) : 𝕋₁) = 0 := by
      rw [h1]
      have hcast : ((0 : ℕ) : ℝ) * β = (0 : ℝ) * β := by norm_num
      rw [rungFun_eval_window β hβ j b (p := 0) hm0
        (by simpa using hzero_mem)]
      have hb00 : b (0 - ((0 : ℕ) : ℝ) * β) = 0 := by
        apply hb0
        intro hcon
        have := hcon.1
        simp at this
      rw [hb00, zero_mul]
    rw [hLHS]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    have hpm : p < capacity 1 β := Finset.mem_range.mp hp
    have hb1p : b (1 - (p : ℝ) * β) = 0 := by
      apply hb0
      intro hcon
      have hp1 : ((p : ℝ) + 1) ≤ (capacity 1 β : ℝ) := by exact_mod_cast hpm
      have := hcon.2
      nlinarith
    rw [hb1p, zero_mul]
  · -- interior: window case split
    by_cases hcase : ∃ p ∈ Finset.range (capacity 1 β),
        x ∈ Set.Ico ((p : ℝ) * β)
          ((p : ℝ) * β + (1 - ((capacity 1 β : ℝ) - 1) * β))
    · obtain ⟨p, hpm, hpx⟩ := hcase
      rw [rungFun_eval_window β hβ j b (Finset.mem_range.mp hpm) hpx]
      symm
      apply Finset.sum_eq_single_of_mem p hpm
      intro q hq hqp
      have hbq : b (x - (q : ℝ) * β) = 0 := by
        by_contra hne
        have hqIoo : x - (q : ℝ) * β ∈ Set.Ioo (0 : ℝ)
            (1 - ((capacity 1 β : ℝ) - 1) * β) := by
          by_contra hnot
          exact hne (hb0 _ hnot)
        have hqwin := hIoo_sub q x hqIoo
        have h1 := (chain_coords_window β hβ hpx).1
        have h2 := (chain_coords_window β hβ hqwin).1
        exact hqp (by omega)
      rw [hbq, zero_mul]
    · push Not at hcase
      rw [rungFun_eval_off_windows β hβ j b hx.1 hx1
        (fun p hp => hcase p (Finset.mem_range.mpr hp))]
      symm
      apply Finset.sum_eq_zero
      intro p hp
      have hbp : b (x - (p : ℝ) * β) = 0 := by
        by_contra hne
        have hpIoo : x - (p : ℝ) * β ∈ Set.Ioo (0 : ℝ)
            (1 - ((capacity 1 β : ℝ) - 1) * β) := by
          by_contra hnot
          exact hne (hb0 _ hnot)
        exact hcase p hp (hIoo_sub p x hpIoo)
      rw [hbp, zero_mul]

end Model

section Formula

variable (β : ℝ)

/-- A continuous integrand vanishing outside `(0,ℓ)` integrates the same
over any interval `[u,v] ⊇ [0,ℓ]` — in particular over `0..1`. -/
lemma integral_eq_of_vanishing (G : ℝ → ℂ) (hG : Continuous G)
    {ℓ : ℝ} (hℓ1 : ℓ ≤ 1)
    (hvan : ∀ t, t ∉ Set.Ioo (0 : ℝ) ℓ → G t = 0)
    {u v : ℝ} (hu : u ≤ 0) (hv : ℓ ≤ v) :
    ∫ t in u..v, G t = ∫ t in (0 : ℝ)..1, G t := by
  have hint : ∀ w w' : ℝ, IntervalIntegrable G volume w w' := fun w w' =>
    hG.intervalIntegrable w w'
  have hzero : ∀ {w w' : ℝ}, (∀ t, t ∈ Set.uIcc w w' → G t = 0) →
      ∫ t in w..w', G t = 0 := by
    intro w w' h
    rw [intervalIntegral.integral_congr h]
    simp
  have hvan' : ∀ {w w' : ℝ}, w ≤ w' → (∀ t, w ≤ t → t ≤ w' →
      t ∉ Set.Ioo (0 : ℝ) ℓ) → ∫ t in w..w', G t = 0 := by
    intro w w' hww h
    apply hzero
    intro t ht
    rw [Set.uIcc_of_le hww] at ht
    exact hvan t (h t ht.1 ht.2)
  have hlow : ∫ t in u..(0 : ℝ), G t = 0 :=
    hvan' hu fun t _ ht2 hcon => absurd (lt_of_le_of_lt ht2 hcon.1)
      (lt_irrefl _)
  have hhighv : ∫ t in ℓ..v, G t = 0 :=
    hvan' hv fun t ht1 _ hcon => absurd (lt_of_le_of_lt ht1 hcon.2)
      (lt_irrefl _)
  have hhigh1 : ∫ t in ℓ..(1 : ℝ), G t = 0 :=
    hvan' hℓ1 fun t ht1 _ hcon => absurd (lt_of_le_of_lt ht1 hcon.2)
      (lt_irrefl _)
  have hsplit1 : ∫ t in u..v, G t
      = (∫ t in u..(0 : ℝ), G t) + ((∫ t in (0 : ℝ)..ℓ, G t)
          + ∫ t in ℓ..v, G t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 ℓ)
      (hint ℓ v),
      intervalIntegral.integral_add_adjacent_intervals (hint u 0)
      (hint 0 v)]
  have hsplit2 : ∫ t in (0 : ℝ)..1, G t
      = (∫ t in (0 : ℝ)..ℓ, G t) + ∫ t in ℓ..(1 : ℝ), G t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 ℓ)
      (hint ℓ 1)]
  rw [hsplit1, hsplit2, hlow, hhighv, hhigh1]
  ring

/-- **The coefficient product formula.** The circle Fourier coefficients
of the bump-modulated capacity rung function factor as a bounded
discrete envelope factor times the coefficients of the single bump. -/
theorem fourierCoeff_rungFun (hβ : 0 < β) (j : Fin (capacity 1 β))
    (b : ℝ → ℝ) (hbc : Continuous b)
    (hb0 : ∀ t, t ∉ Set.Ioo (0 : ℝ)
      (1 - ((capacity 1 β : ℝ) - 1) * β) → b t = 0) (n : ℤ) :
    fourierCoeff (fun z : 𝕋₁ =>
        ((rungFun β (capacity 1 β) j b z : ℝ) : ℂ)) n
      = (∑ p ∈ Finset.range (capacity 1 β),
          ((Real.sin (((p : ℝ) + 1) * pathAngle (capacity 1 β) j) : ℝ) : ℂ)
            * fourier (-n) ((((p : ℝ) * β) : ℝ) : 𝕋₁))
        * ∫ t in (0 : ℝ)..1, fourier (-n) ((t : ℝ) : 𝕋₁) * ((b t : ℝ) : ℂ) := by
  have hfact : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hℓpos : 0 < 1 - ((capacity 1 β : ℝ) - 1) * β := by
    have := capacity_sub_one_mul_lt β hβ
    linarith
  have hℓ1 : (1 - ((capacity 1 β : ℝ) - 1) * β) ≤ 1 := by
    have hm1 : 1 ≤ capacity 1 β := one_le_capacity β hβ
    have h1 : (1 : ℝ) ≤ (capacity 1 β : ℝ) := by exact_mod_cast hm1
    nlinarith
  -- the coefficient as an interval integral
  rw [fourierCoeff_eq_intervalIntegral _ n 0]
  rw [zero_add]
  simp only [one_div_one, one_smul]
  -- replace the rung function by the indicator-free model
  have hcongr : ∫ x in (0 : ℝ)..1,
        fourier (-n) ((x : ℝ) : 𝕋₁)
          • ((rungFun β (capacity 1 β) j b ((x : ℝ) : 𝕋₁) : ℝ) : ℂ)
      = ∫ x in (0 : ℝ)..1,
          ∑ p ∈ Finset.range (capacity 1 β),
            ((Real.sin (((p : ℝ) + 1) * pathAngle (capacity 1 β) j) : ℝ) : ℂ)
              * (fourier (-n) ((x : ℝ) : 𝕋₁)
                  * ((b (x - (p : ℝ) * β) : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    dsimp only
    rw [rungFun_coe_eq_sum β hβ j b hb0 hx, smul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hcongr]
  -- exchange sum and integral (continuous integrands)
  have hint : ∀ p : ℕ, IntervalIntegrable (fun x : ℝ =>
      ((Real.sin (((p : ℝ) + 1) * pathAngle (capacity 1 β) j) : ℝ) : ℂ)
        * (fourier (-n) ((x : ℝ) : 𝕋₁)
            * ((b (x - (p : ℝ) * β) : ℝ) : ℂ))) volume 0 1 := by
    intro p
    apply Continuous.intervalIntegrable
    apply Continuous.mul continuous_const
    apply Continuous.mul
    · exact (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' 1)
    · exact Complex.continuous_ofReal.comp
        (hbc.comp (continuous_id.sub continuous_const))
  rw [intervalIntegral.integral_finsetSum (fun p _ => hint p)]
  -- evaluate each summand by translation
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpm : p < capacity 1 β := Finset.mem_range.mp hp
  rw [intervalIntegral.integral_const_mul]
  rw [mul_assoc]
  congr 1
  -- ∫₀¹ e₋ₙ(x)·b(x−pβ) dx = e₋ₙ(pβ)·∫₀¹ e₋ₙ(t)·b(t) dt
  have hshift : ∫ x in (0 : ℝ)..1,
        fourier (-n) ((x : ℝ) : 𝕋₁) * ((b (x - (p : ℝ) * β) : ℝ) : ℂ)
      = ∫ u in ((0 : ℝ) - (p : ℝ) * β)..(1 - (p : ℝ) * β),
          fourier (-n) (((u + (p : ℝ) * β) : ℝ) : 𝕋₁) * ((b u : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_comp_sub_right
      (fun u : ℝ => fourier (-n) (((u + (p : ℝ) * β) : ℝ) : 𝕋₁)
        * ((b u : ℝ) : ℂ)) ((p : ℝ) * β)]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [sub_add_cancel]
  rw [hshift]
  have hchar : ∀ u : ℝ,
      fourier (-n) (((u + (p : ℝ) * β) : ℝ) : 𝕋₁)
        = fourier (-n) ((u : ℝ) : 𝕋₁)
          * fourier (-n) ((((p : ℝ) * β) : ℝ) : 𝕋₁) := by
    intro u
    have hcoe : (((u + (p : ℝ) * β) : ℝ) : 𝕋₁)
        = ((u : ℝ) : 𝕋₁) + ((((p : ℝ) * β) : ℝ) : 𝕋₁) := rfl
    rw [hcoe, fourier_point_add]
  have hpull : ∫ u in ((0 : ℝ) - (p : ℝ) * β)..(1 - (p : ℝ) * β),
        fourier (-n) (((u + (p : ℝ) * β) : ℝ) : 𝕋₁) * ((b u : ℝ) : ℂ)
      = fourier (-n) ((((p : ℝ) * β) : ℝ) : 𝕋₁)
        * ∫ u in ((0 : ℝ) - (p : ℝ) * β)..(1 - (p : ℝ) * β),
            fourier (-n) ((u : ℝ) : 𝕋₁) * ((b u : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [hchar u]
    ring
  rw [hpull]
  refine congrArg (fourier (-n) ((((p : ℝ) * β) : ℝ) : 𝕋₁) * ·) ?_
  -- extend/restrict the translated range back to 0..1
  have hbound : (1 - ((capacity 1 β : ℝ) - 1) * β) ≤ 1 - (p : ℝ) * β := by
    have hp1 : ((p : ℝ)) ≤ (capacity 1 β : ℝ) - 1 := by
      have h1 : ((p : ℝ) + 1) ≤ (capacity 1 β : ℝ) := by exact_mod_cast hpm
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hp1 hβ.le]
  have hG : Continuous fun u : ℝ =>
      fourier (-n) ((u : ℝ) : 𝕋₁) * ((b u : ℝ) : ℂ) := by
    apply Continuous.mul
    · exact (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' 1)
    · exact Complex.continuous_ofReal.comp hbc
  have hvan : ∀ t, t ∉ Set.Ioo (0 : ℝ)
      (1 - ((capacity 1 β : ℝ) - 1) * β) →
      fourier (-n) ((t : ℝ) : 𝕋₁) * ((b t : ℝ) : ℂ) = 0 := by
    intro t ht
    rw [hb0 t ht]
    simp
  exact integral_eq_of_vanishing
    (fun u : ℝ => fourier (-n) ((u : ℝ) : 𝕋₁) * ((b u : ℝ) : ℂ))
    hG hℓ1 hvan (by nlinarith [hβ.le] : (0 : ℝ) - (p : ℝ) * β ≤ 0) hbound

/-- **Rapid decay of the bump-modulated eigenfunction's coefficients.**
For a smooth bump supported inside the long-base interval, the circle
Fourier coefficients of the capacity rung function decay faster than
any algebraic rate: the discrete envelope factor is bounded by `m`, and
the single-bump coefficients are rapid by iterated integration by
parts. This discharges the analytic content of the tail hypothesis
at the level of Fourier coefficients. -/
theorem rapidFourierDecay_rungFun (hβ : 0 < β)
    (j : Fin (capacity 1 β)) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hsupp : tsupport b ⊆ Set.Ioo (0 : ℝ)
      (1 - ((capacity 1 β : ℝ) - 1) * β)) :
    RapidFourierDecay (fourierCoeff (fun z : 𝕋₁ =>
      ((rungFun β (capacity 1 β) j b z : ℝ) : ℂ))) := by
  have hℓ1 : (1 - ((capacity 1 β : ℝ) - 1) * β) ≤ 1 := by
    have hm1 : 1 ≤ capacity 1 β := one_le_capacity β hβ
    have h1 : (1 : ℝ) ≤ (capacity 1 β : ℝ) := by exact_mod_cast hm1
    nlinarith
  have hb0 : ∀ t, t ∉ Set.Ioo (0 : ℝ)
      (1 - ((capacity 1 β : ℝ) - 1) * β) → b t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hmem => ht (hsupp hmem)
  have hbC : ContDiff ℝ ∞ (fun t : ℝ => ((b t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hb
  have hsuppC : tsupport (fun t : ℝ => ((b t : ℝ) : ℂ))
      ⊆ Set.Ioo (0 : ℝ) 1 := by
    refine subset_trans (closure_minimal ?_ (isClosed_tsupport b))
      (subset_trans hsupp (Set.Ioo_subset_Ioo_right hℓ1))
    intro t ht
    apply subset_closure
    simp only [Function.mem_support] at ht ⊢
    intro h0
    exact ht (by rw [h0]; norm_num)
  have hrapidB : RapidFourierDecay
      (fourierCoeffOn zero_lt_one (fun t : ℝ => ((b t : ℝ) : ℂ))) :=
    rapidFourierDecay_of_smooth_bump zero_lt_one hbC hsuppC
  have hBeq : ∀ n : ℤ,
      (∫ t in (0 : ℝ)..1, fourier (-n) ((t : ℝ) : 𝕋₁) * ((b t : ℝ) : ℂ))
        = fourierCoeffOn zero_lt_one (fun t : ℝ => ((b t : ℝ) : ℂ)) n := by
    intro n
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero, one_div_one, one_smul, smul_eq_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [fourier_coe_apply, fourier_coe_apply]
    norm_num
  have hDbd : ∀ n : ℤ, ‖∑ p ∈ Finset.range (capacity 1 β),
      ((Real.sin (((p : ℝ) + 1) * pathAngle (capacity 1 β) j) : ℝ) : ℂ)
        * fourier (-n) ((((p : ℝ) * β) : ℝ) : 𝕋₁)‖
      ≤ (capacity 1 β : ℝ) := by
    intro n
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ p ∈ Finset.range (capacity 1 β),
        ‖((Real.sin (((p : ℝ) + 1) * pathAngle (capacity 1 β) j) : ℝ) : ℂ)
          * fourier (-n) ((((p : ℝ) * β) : ℝ) : 𝕋₁)‖ ≤ 1 := by
      intro p _
      rw [norm_mul]
      have h2 : ‖fourier (-n) ((((p : ℝ) * β) : ℝ) : 𝕋₁)‖ = 1 := by
        rw [fourier_apply, Circle.norm_coe]
      rw [h2, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    calc ∑ p ∈ Finset.range (capacity 1 β),
          ‖((Real.sin (((p : ℝ) + 1) * pathAngle (capacity 1 β) j) : ℝ) : ℂ)
            * fourier (-n) ((((p : ℝ) * β) : ℝ) : 𝕋₁)‖
        ≤ ∑ _p ∈ Finset.range (capacity 1 β), (1 : ℝ) :=
          Finset.sum_le_sum hterm
      _ = (capacity 1 β : ℝ) := by simp
  have hfun : (fourierCoeff (fun z : 𝕋₁ =>
      ((rungFun β (capacity 1 β) j b z : ℝ) : ℂ)))
      = fun n => (∑ p ∈ Finset.range (capacity 1 β),
          ((Real.sin (((p : ℝ) + 1) * pathAngle (capacity 1 β) j) : ℝ) : ℂ)
            * fourier (-n) ((((p : ℝ) * β) : ℝ) : 𝕋₁))
          * fourierCoeffOn zero_lt_one (fun t : ℝ => ((b t : ℝ) : ℂ)) n := by
    funext n
    rw [fourierCoeff_rungFun β hβ j b hb.continuous hb0 n, hBeq n]
  rw [hfun]
  exact hrapidB.mul_bounded hDbd

end Formula

end Cvs.PathLaw
