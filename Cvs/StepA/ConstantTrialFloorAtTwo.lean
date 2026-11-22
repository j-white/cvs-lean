import Mathlib
import Cvs.StepA.EvenMultiplierAtTwo
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.TruncatedArchCappedBudget
import Cvs.WeilForm.TruncatedEffectiveSymbol
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-!
# The constant even trial clears the eigenvalue floor (`hea`)

The tail-correction analytic ingredients (an oscillatory-integral bound with no sine-integral
special function), then the constant trial's mass functional lower bound and the even plane gap
assembly toward `Cvs.StepA.StepAAtTwoAssembled.stepA_x2`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open Cvs.StepA.EvenMultiplierAtTwo

namespace Cvs.StepA.ConstantTrialFloorAtTwo

theorem rpow_neg2 {x : ℝ} (hx : 0 < x) : x ^ (-2:ℝ) = 1 / x^2 := by
  rw [Real.rpow_neg hx.le, Real.rpow_two, one_div]
theorem rpow_neg3 {x : ℝ} (hx : 0 < x) : x ^ (-3:ℝ) = 1 / x^3 := by
  rw [show (-3:ℝ) = -((3:ℕ):ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast, one_div]

theorem inv_sq_int (s : ℝ) (hs : 0 < s) : IntegrableOn (fun x : ℝ => 1 / x^2) (Ioi s) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hs).congr_fun
    (fun x hx => ?_) measurableSet_Ioi
  exact rpow_neg2 (hs.trans (Set.mem_Ioi.mp hx))

theorem inv_cube_int (s : ℝ) (hs : 0 < s) : IntegrableOn (fun x : ℝ => 1 / x^3) (Ioi s) := by
  refine (integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) hs).congr_fun
    (fun x hx => ?_) measurableSet_Ioi
  exact rpow_neg3 (hs.trans (Set.mem_Ioi.mp hx))

theorem inv_cube_integral (s : ℝ) (hs : 0 < s) : (∫ x in Ioi s, 1 / x^3) = 1 / (2 * s^2) := by
  rw [show (∫ x in Ioi s, 1 / x^3) = ∫ x in Ioi s, x ^ (-3:ℝ) from
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => (rpow_neg3 (hs.trans (Set.mem_Ioi.mp hx))).symm),
    integral_Ioi_rpow_of_lt (a := -3) (by norm_num) hs,
    show (-3:ℝ)+1 = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg hs.le, Real.rpow_natCast]
  push_cast
  rw [neg_div_neg_eq]
  field_simp

theorem cos_tail_le (s L : ℝ) (hs : 0 < s) (hL : 0 < L) :
    (∫ t in Ioi s, Real.cos (t*L) / t^2) ≤ 2 / (L * s^2) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  set A : ℝ → ℝ := fun x => Real.cos (x*L) / x^2 with hAdef
  set Bf : ℝ → ℝ := fun x => 2 * Real.sin (x*L) / (L * x^3) with hBfdef
  set F : ℝ → ℝ := fun x => Real.sin (x*L) / (L * x^2) with hFdef
  -- derivative F' = A - Bf on Ioi s
  have hderiv : ∀ x ∈ Ioi s, HasDerivAt F (A x - Bf x) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := hs.trans hx
    have hsin : HasDerivAt (fun y => Real.sin (y*L)) (Real.cos (x*L) * L) x := by
      simpa only [Function.comp_def, id_eq, one_mul] using
        (Real.hasDerivAt_sin (x*L)).comp x ((hasDerivAt_id x).mul_const L)
    have hden : HasDerivAt (fun y => L * y^2) (L * (2*x)) x := by
      simpa using ((hasDerivAt_pow 2 x)).const_mul L
    have hq := hsin.div hden (by positivity)
    refine hq.congr_deriv ?_
    rw [hAdef, hBfdef]
    field_simp
  -- integrabilities
  have hAcont : ContinuousOn A (Ioi s) := by
    apply ContinuousOn.div₀ (by fun_prop) (by fun_prop)
    intro x hx; have : (0:ℝ) < x := hs.trans (Set.mem_Ioi.mp hx); positivity
  have hAint : IntegrableOn A (Ioi s) := by
    refine (inv_sq_int s hs).mono' (hAcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    have hx0 : (0:ℝ) < x := hs.trans (Set.mem_Ioi.mp hx)
    rw [hAdef, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < x^2)]
    gcongr
    exact Real.abs_cos_le_one _
  -- Bf integrability, dominated by 2/(L x^3)
  have hdomBf : IntegrableOn (fun x : ℝ => 2/L * (1/x^3)) (Ioi s) := (inv_cube_int s hs).const_mul _
  have hBfcont : ContinuousOn Bf (Ioi s) := by
    apply ContinuousOn.div₀ (by fun_prop) (by fun_prop)
    intro x hx; have : (0:ℝ) < x := hs.trans (Set.mem_Ioi.mp hx); positivity
  have hBfle : ∀ x ∈ Ioi s, Bf x ≤ 2/L * (1/x^3) := by
    intro x hx; have hx0 : (0:ℝ) < x := hs.trans (Set.mem_Ioi.mp hx)
    have hd : (0:ℝ) < L*x^3 := by positivity
    rw [hBfdef, div_le_iff₀ hd, show 2/L*(1/x^3)*(L*x^3) = 2 by field_simp]
    nlinarith [Real.sin_le_one (x*L)]
  have hBfint : IntegrableOn Bf (Ioi s) := by
    refine hdomBf.mono' (hBfcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    have hx0 : (0:ℝ) < x := hs.trans (Set.mem_Ioi.mp hx)
    have hd : (0:ℝ) < L*x^3 := by positivity
    rw [Real.norm_eq_abs, hBfdef, abs_div, abs_of_pos hd, div_le_iff₀ hd,
      show 2/L*(1/x^3)*(L*x^3) = 2 by field_simp]
    have h1 : |2 * Real.sin (x*L)| ≤ 2 := by
      rw [abs_mul, abs_two]; nlinarith [Real.abs_sin_le_one (x*L)]
    linarith [h1]
  have hF'int : IntegrableOn (fun x => A x - Bf x) (Ioi s) := hAint.sub hBfint
  -- F -> 0 at atTop
  have hFtend : Filter.Tendsto F Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun x => (1/L) * (x^2)⁻¹) (fun x => ?_) ?_
    · by_cases hx : x = 0
      · subst hx; rw [hFdef]; simp
      · rw [hFdef, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < L*x^2),
          div_le_iff₀ (by positivity), show (1/L)*(x^2)⁻¹*(L*x^2) = 1 by field_simp]
        exact Real.abs_sin_le_one _
    · have h2 : Filter.Tendsto (fun x : ℝ => (x^2)⁻¹) Filter.atTop (nhds 0) :=
        (tendsto_pow_atTop (by norm_num)).inv_tendsto_atTop
      simpa using h2.const_mul (1/L)
  have hFcont : ContinuousWithinAt F (Ici s) s := by
    apply ContinuousAt.continuousWithinAt
    rw [hFdef]; apply ContinuousAt.div₀ (by fun_prop) (by fun_prop); positivity
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hFcont hderiv hF'int hFtend
  rw [integral_sub hAint hBfint] at hmain
  have hFs : -(F s) ≤ 1/(L*s^2) := by
    rw [hFdef, ← neg_div]
    gcongr
    linarith [Real.neg_one_le_sin (s*L)]
  have hBfbound : (∫ x in Ioi s, Bf x) ≤ 1/(L*s^2) := by
    calc (∫ x in Ioi s, Bf x) ≤ ∫ x in Ioi s, 2/L * (1/x^3) :=
          setIntegral_mono_on hBfint hdomBf measurableSet_Ioi hBfle
      _ = 2/L * ∫ x in Ioi s, 1/x^3 := integral_const_mul _ _
      _ = 2/L * (1/(2*s^2)) := by rw [inv_cube_integral s hs]
      _ = 1/(L*s^2) := by field_simp
  have hAeq : (∫ t in Ioi s, A t) = (∫ x in Ioi s, Bf x) + -(F s) := by linarith [hmain]
  have hgoal : (∫ t in Ioi s, Real.cos (t*L)/t^2) = (∫ x in Ioi s, Bf x) + -(F s) := by
    rw [← hAeq]
  rw [hgoal]
  have h2 : (2:ℝ)/(L*s^2) = 1/(L*s^2) + 1/(L*s^2) := by ring
  rw [h2]
  linarith [hBfbound, hFs]

theorem inv_sq_integral (s : ℝ) (hs : 0 < s) : (∫ x in Ioi s, 1 / x^2) = 1 / s := by
  rw [show (∫ x in Ioi s, 1 / x^2) = ∫ x in Ioi s, x ^ (-2:ℝ) from
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => (rpow_neg2 (hs.trans (Set.mem_Ioi.mp hx))).symm),
    integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hs,
    show (-2:ℝ)+1 = -((1:ℕ):ℝ) by norm_num, Real.rpow_neg hs.le, Real.rpow_natCast]
  push_cast; field_simp

theorem cos_over_sq_int (s L : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t => Real.cos (t*L) / t^2) (Ioi s) := by
  refine (inv_sq_int s hs).mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  · refine (ContinuousOn.div₀ (by fun_prop) (by fun_prop) ?_).aestronglyMeasurable measurableSet_Ioi
    intro x hx; have : (0:ℝ) < x := hs.trans (Set.mem_Ioi.mp hx); positivity
  · have hx0 : (0:ℝ) < x := hs.trans (Set.mem_Ioi.mp hx)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < x^2)]
    gcongr
    exact Real.abs_cos_le_one _

theorem spec_tail_ge {L : ℝ} (hL : 0 < L) (s : ℝ) (hs : 0 < s) :
    (1/Real.pi) * (1/s - 2/(L*s^2))
      ≤ ∫ t in Ioi s, Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW L)) t := by
  have hcongr : (∫ t in Ioi s, Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW L)) t)
      = ∫ t in Ioi s, (1 - Real.cos (t*L)) / (Real.pi * t^2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    exact specDensity_constW hL t (ne_of_gt (hs.trans (Set.mem_Ioi.mp ht)))
  rw [hcongr]
  -- (1-cos)/(π t²) = (1/π)(1/t² - cos/t²)
  have hsplit : (∫ t in Ioi s, (1 - Real.cos (t*L)) / (Real.pi * t^2))
      = (1/Real.pi) * ((∫ t in Ioi s, 1/t^2) - ∫ t in Ioi s, Real.cos (t*L)/t^2) := by
    rw [← integral_sub (inv_sq_int s hs) (cos_over_sq_int s L hs), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0:ℝ) < t := hs.trans (Set.mem_Ioi.mp ht)
    field_simp
  rw [hsplit, inv_sq_integral s hs]
  have hcos := cos_tail_le s L hs hL
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1/Real.pi)
  linarith [hcos]

theorem layer_cake_lower {spec : ℝ → ℝ} (hspec_nn : ∀ t, 0 ≤ spec t)
    (hspec_int : Integrable spec)
    {g : ℝ → ℝ} (m : ℕ) (a : ℕ → ℝ) (c : ℕ → ℝ) (Bv : ℕ → ℝ)
    (hc_nn : ∀ j, 0 ≤ c j)
    (hg_int : Integrable (fun t => g t * spec t))
    (hstep : ∀ t, (∑ j ∈ Finset.range m, c j * (Set.Ioi (a j)).indicator (fun _ => (1:ℝ)) t) ≤ g t)
    (hB : ∀ j ∈ Finset.range m, Bv j ≤ ∫ t in Ioi (a j), spec t) :
    (∑ j ∈ Finset.range m, c j * Bv j) ≤ ∫ t, g t * spec t := by
  -- step function
  set stepf : ℝ → ℝ := fun t => ∑ j ∈ Finset.range m, c j * (Set.Ioi (a j)).indicator (fun _ => (1:ℝ)) t with hstepf
  -- ∫ stepf * spec = ∑ c_j ∫_{Ioi a_j} spec
  have hterm_int : ∀ j, Integrable (fun t => c j * (Set.Ioi (a j)).indicator (fun _ => (1:ℝ)) t * spec t) := by
    intro j
    have : (fun t => c j * (Set.Ioi (a j)).indicator (fun _ => (1:ℝ)) t * spec t)
        = fun t => c j * (Set.Ioi (a j)).indicator spec t := by
      funext t; by_cases ht : t ∈ Set.Ioi (a j)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; ring
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; ring
    rw [this]
    exact (hspec_int.indicator measurableSet_Ioi).const_mul _
  have hstepspec_eq : (∫ t, stepf t * spec t) = ∑ j ∈ Finset.range m, c j * ∫ t in Ioi (a j), spec t := by
    have hrw : (fun t => stepf t * spec t)
        = fun t => ∑ j ∈ Finset.range m, c j * (Set.Ioi (a j)).indicator (fun _ => (1:ℝ)) t * spec t := by
      funext t; rw [hstepf, Finset.sum_mul]
    rw [hrw, integral_finsetSum _ (fun j _ => hterm_int j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show (fun t => c j * (Set.Ioi (a j)).indicator (fun _ => (1:ℝ)) t * spec t)
        = fun t => c j * ((Set.Ioi (a j)).indicator spec t) from ?_, integral_const_mul,
      integral_indicator measurableSet_Ioi]
    funext t; by_cases ht : t ∈ Set.Ioi (a j)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; ring
  -- ∫ stepf*spec ≤ ∫ g*spec
  have hstepspec_int : Integrable (fun t => stepf t * spec t) := by
    rw [show (fun t => stepf t * spec t)
        = fun t => ∑ j ∈ Finset.range m, c j * (Set.Ioi (a j)).indicator (fun _ => (1:ℝ)) t * spec t from by
          funext t; rw [hstepf, Finset.sum_mul]]
    exact integrable_finsetSum _ (fun j _ => hterm_int j)
  have hmono : (∫ t, stepf t * spec t) ≤ ∫ t, g t * spec t := by
    refine integral_mono hstepspec_int hg_int (fun t => ?_)
    exact mul_le_mul_of_nonneg_right (hstep t) (hspec_nn t)
  calc (∑ j ∈ Finset.range m, c j * Bv j)
      ≤ ∑ j ∈ Finset.range m, c j * ∫ t in Ioi (a j), spec t :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hB j hj) (hc_nn j))
    _ = ∫ t, stepf t * spec t := hstepspec_eq.symm
    _ ≤ ∫ t, g t * spec t := hmono

theorem trunc_mono (N : ℕ) {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h12 : t1 ≤ t2) :
    Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol N t1 ≤ Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol N t2 := by
  unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol
  gcongr ((Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) + ∑ k ∈ Finset.range N, (1/((k:ℝ)+1/4) - ?_)) with k hk
  · have hc : (0:ℝ) < (k:ℝ) + 1/4 := by positivity
    have hsq : (t1/2)^2 ≤ (t2/2)^2 := by
      have : 0 ≤ t2 := le_trans h1 h12
      nlinarith
    have hd1 : (0:ℝ) < ((k:ℝ)+1/4)^2 + (t1/2)^2 := by positivity
    exact div_le_div_of_nonneg_left hc.le hd1 (by linarith)

theorem trunc_le_channels {K N : ℕ} (hKN : K ≤ N) (t : ℝ) :
    Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol K t ≤ Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol N t := by
  unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol
  have hsum : (∑ k ∈ Finset.range K, (1 / ((k:ℝ)+1/4) - ((k:ℝ)+1/4) / (((k:ℝ)+1/4)^2 + (t/2)^2)))
      ≤ ∑ k ∈ Finset.range N, (1 / ((k:ℝ)+1/4) - ((k:ℝ)+1/4) / (((k:ℝ)+1/4)^2 + (t/2)^2)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKN) (fun k _ _ => ?_)
    have hd : (0:ℝ) < ((k:ℝ)+1/4)^2 + (t/2)^2 := by positivity
    rw [show 1 / ((k:ℝ)+1/4) - ((k:ℝ)+1/4) / (((k:ℝ)+1/4)^2 + (t/2)^2)
        = (t/2)^2 / (((k:ℝ)+1/4) * (((k:ℝ)+1/4)^2 + (t/2)^2)) by field_simp; ring]
    positivity
  linarith [hsum]

theorem mcap_split_ge (t : ℝ) {K : ℕ} (hK : K ≤ 100) :
    (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar)
      + max 0 ((Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol K t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar - 1)
      ≤ mcap t := by
  set E100 := (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar with hE100
  set EK := (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol K t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar with hEK
  have hEKle : EK ≤ E100 := by
    rw [hEK, hE100]
    exact (div_le_div_iff_of_pos_right lamstar_pos).mpr (by linarith [trunc_le_channels hK t])
  show (1 - E100) + max 0 (EK - 1) ≤ mcap t
  rw [mcap, show (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar)
      = 1 - E100 from rfl]
  by_cases h : EK ≤ 1
  · rw [max_eq_left (by linarith), add_zero]
    exact le_max_right _ _
  · push Not at h
    rw [max_eq_right (by linarith)]
    have : (1 - E100) + (EK - 1) ≤ 0 := by linarith
    exact le_trans this (le_max_left _ _)

/-- Layer-cake step bound for five nodes using rational under-estimates `v j ≤ g (a j)`. -/
theorem hstep5v {g : ℝ → ℝ} (a : ℕ → ℝ) (v : ℕ → ℝ)
    (hnodes : a 0 < a 1 ∧ a 1 < a 2 ∧ a 2 < a 3 ∧ a 3 < a 4)
    (hg_mono : ∀ x y : ℝ, a 0 ≤ x → x ≤ y → g x ≤ g y)
    (hg_nn : ∀ t : ℝ, 0 ≤ g t)
    (hv0 : 0 ≤ v 0) (hvm : v 0 ≤ v 1 ∧ v 1 ≤ v 2 ∧ v 2 ≤ v 3 ∧ v 3 ≤ v 4)
    (hvle : v 0 ≤ g (a 0) ∧ v 1 ≤ g (a 1) ∧ v 2 ≤ g (a 2) ∧ v 3 ≤ g (a 3) ∧ v 4 ≤ g (a 4))
    (t : ℝ) :
    (v 0 * (Set.Ioi (a 0)).indicator (fun _ => (1:ℝ)) t
      + (v 1 - v 0) * (Set.Ioi (a 1)).indicator (fun _ => (1:ℝ)) t
      + (v 2 - v 1) * (Set.Ioi (a 2)).indicator (fun _ => (1:ℝ)) t
      + (v 3 - v 2) * (Set.Ioi (a 3)).indicator (fun _ => (1:ℝ)) t
      + (v 4 - v 3) * (Set.Ioi (a 4)).indicator (fun _ => (1:ℝ)) t) ≤ g t := by
  obtain ⟨h01, h12, h23, h34⟩ := hnodes
  obtain ⟨hm01, hm12, hm23, hm34⟩ := hvm
  obtain ⟨hl0, hl1, hl2, hl3, hl4⟩ := hvle
  simp only [Set.indicator_apply, Set.mem_Ioi]
  rcases lt_or_ge (a 0) t with ht0 | ht0
  · rcases lt_or_ge (a 1) t with ht1 | ht1
    · rcases lt_or_ge (a 2) t with ht2 | ht2
      · rcases lt_or_ge (a 3) t with ht3 | ht3
        · rcases lt_or_ge (a 4) t with ht4 | ht4
          · simp only [ite_eq_left ht0, ite_eq_left ht1, ite_eq_left ht2, ite_eq_left ht3, ite_eq_left ht4, mul_one]
            have := hg_mono (a 4) t (by linarith) ht4.le; linarith
          · simp only [ite_eq_left ht0, ite_eq_left ht1, ite_eq_left ht2, ite_eq_left ht3, ite_eq_right (not_lt.mpr ht4), mul_zero, mul_one, add_zero]
            have := hg_mono (a 3) t (by linarith) ht3.le; linarith
        · simp only [ite_eq_left ht0, ite_eq_left ht1, ite_eq_left ht2, ite_eq_right (not_lt.mpr ht3), ite_eq_right (not_lt.mpr (le_trans ht3 h34.le)), mul_zero, mul_one, add_zero]
          have := hg_mono (a 2) t (by linarith) ht2.le; linarith
      · simp only [ite_eq_left ht0, ite_eq_left ht1, ite_eq_right (not_lt.mpr ht2), ite_eq_right (not_lt.mpr (le_trans ht2 h23.le)), ite_eq_right (not_lt.mpr (le_trans ht2 (le_trans h23.le h34.le))), mul_zero, mul_one, add_zero]
        have := hg_mono (a 1) t (by linarith) ht1.le; linarith
    · simp only [ite_eq_left ht0, ite_eq_right (not_lt.mpr ht1), ite_eq_right (not_lt.mpr (le_trans ht1 h12.le)), ite_eq_right (not_lt.mpr (le_trans ht1 (le_trans h12.le h23.le))), ite_eq_right (not_lt.mpr (le_trans ht1 (le_trans h12.le (le_trans h23.le h34.le)))), mul_zero, mul_one, add_zero]
      have := hg_mono (a 0) t (le_refl _) ht0.le; linarith
  · simp only [ite_eq_right (not_lt.mpr ht0), ite_eq_right (not_lt.mpr (le_trans ht0 h01.le)), ite_eq_right (not_lt.mpr (le_trans ht0 (le_trans h01.le h12.le))), ite_eq_right (not_lt.mpr (le_trans ht0 (le_trans h01.le (le_trans h12.le h23.le)))), ite_eq_right (not_lt.mpr (le_trans ht0 (le_trans h01.le (le_trans h12.le (le_trans h23.le h34.le))))), mul_zero, add_zero]
    exact hg_nn t

noncomputable def gExc (t : ℝ) : ℝ :=
  max 0 ((Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar - 1)

theorem gExc_nonneg (t : ℝ) : 0 ≤ gExc t := le_max_left _ _

theorem gExc_even (t : ℝ) : gExc (-t) = gExc t := by
  unfold gExc; rw [Cvs.StepA.EvenMultiplierAtTwo.truncArchSymbol_even]

theorem gExc_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : gExc x ≤ gExc y := by
  unfold gExc
  apply max_le_max (le_refl 0)
  have hd : (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 x - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar
      ≤ (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 y - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar :=
    (div_le_div_iff_of_pos_right lamstar_pos).mpr (by linarith [trunc_mono 100 hx hxy])
  linarith

theorem spec_even {L : ℝ} (hL : 0 < L) (t : ℝ) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW L)) (-t)
      = Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW L)) t := by
  by_cases ht : t = 0
  · rw [ht]; simp
  · rw [specDensity_constW hL (-t) (by simpa using ht), specDensity_constW hL t ht]
    rw [show (-t)*L = -(t*L) by ring, Real.cos_neg, neg_sq]

noncomputable def node5 : ℕ → ℝ := fun j => [(9:ℝ), 12, 17, 25, 40].getD j 0
noncomputable def vval5 : ℕ → ℝ := fun j => [(135:ℝ)/10000, 639/10000, 1243/10000, 1897/10000, 2651/10000].getD j 0
noncomputable def coef5 : ℕ → ℝ := fun j => [(135:ℝ)/10000, 504/10000, 604/10000, 654/10000, 754/10000].getD j 0
noncomputable def beta5 : ℕ → ℝ := fun j => [(2402:ℝ)/100000, 2014/100000, 1554/100000, 1126/100000, 738/100000].getD j 0

theorem node_le_gExc {s v : ℝ}
    (hv : v ≤ (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 50 s - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar - 1) :
    v ≤ gExc s := by
  have h100 := trunc_le_channels (show (50:ℕ) ≤ 100 by norm_num) s
  have hd : (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 50 s - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar
      ≤ (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 s - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar :=
    (div_le_div_iff_of_pos_right lamstar_pos).mpr (by linarith)
  unfold gExc
  exact le_trans hv (le_trans (by linarith) (le_max_right _ _))

private theorem nb (s c v : ℝ)
    (hE : Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 50 s - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0
      = ∑ k ∈ Finset.range 50, (1 / ((k:ℝ)+1/4) - ((k:ℝ)+1/4) / (((k:ℝ)+1/4)^2 + c)))
    (hnum : v ≤ (∑ k ∈ Finset.range 50, (1 / ((k:ℝ)+1/4) - ((k:ℝ)+1/4) / (((k:ℝ)+1/4)^2 + c))) / lamstar - 1) :
    v ≤ gExc s := by
  apply node_le_gExc; rw [hE]; exact hnum

theorem node_bound0 : vval5 0 ≤ gExc (node5 0) := by
  show (135:ℝ)/10000 ≤ gExc 9
  refine nb 9 ((9/2)^2) _ ?_ ?_
  · unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol; rw [add_sub_cancel_left]
  · rw [lamstar]; norm_num [Finset.sum_range_succ]
theorem node_bound1 : vval5 1 ≤ gExc (node5 1) := by
  show (639:ℝ)/10000 ≤ gExc 12
  refine nb 12 ((12/2)^2) _ ?_ ?_
  · unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol; rw [add_sub_cancel_left]
  · rw [lamstar]; norm_num [Finset.sum_range_succ]
theorem node_bound2 : vval5 2 ≤ gExc (node5 2) := by
  show (1243:ℝ)/10000 ≤ gExc 17
  refine nb 17 ((17/2)^2) _ ?_ ?_
  · unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol; rw [add_sub_cancel_left]
  · rw [lamstar]; norm_num [Finset.sum_range_succ]
theorem node_bound3 : vval5 3 ≤ gExc (node5 3) := by
  show (1897:ℝ)/10000 ≤ gExc 25
  refine nb 25 ((25/2)^2) _ ?_ ?_
  · unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol; rw [add_sub_cancel_left]
  · rw [lamstar]; norm_num [Finset.sum_range_succ]
theorem node_bound4 : vval5 4 ≤ gExc (node5 4) := by
  show (2651:ℝ)/10000 ≤ gExc 40
  refine nb 40 ((40/2)^2) _ ?_ ?_
  · unfold Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol; rw [add_sub_cancel_left]
  · rw [lamstar]; norm_num [Finset.sum_range_succ]

theorem beta_le_B (s β : ℝ) (hs : 0 < s)
    (hrat : β ≤ (1/(3.1416:ℝ)) * (1/s - 2/((6931471803/10000000000:ℝ) * s^2)))
    (hin : 0 ≤ 1/s - 2/((6931471803/10000000000:ℝ) * s^2)) :
    β ≤ (1/Real.pi) * (1/s - 2/(Real.log 2 * s^2)) := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpip : (0:ℝ) < Real.pi := Real.pi_pos
  have hL : (6931471803/10000000000:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  refine le_trans hrat ?_
  apply mul_le_mul (one_div_le_one_div_of_le hpip hpi.le) ?_ hin (by positivity)
  have h2 : (2:ℝ)/(Real.log 2 * s^2) ≤ 2/((6931471803/10000000000:ℝ) * s^2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right hL.le (by positivity))
  linarith

theorem gExc_le (t : ℝ) :
    gExc t ≤ (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar := by
  unfold gExc
  have hnn : (0:ℝ) ≤ (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar :=
    div_nonneg (by linarith [Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol_ge 100 t]) lamstar_pos.le
  by_cases h : (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar - 1 ≤ 0
  · rw [max_eq_left h]; exact hnn
  · push Not at h; rw [max_eq_right h.le]; linarith

theorem gExc_continuous : Continuous gExc := by
  have hT : Continuous (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100) := by
    have hk : ∀ k ∈ Finset.range 100, Continuous (fun t : ℝ =>
        1 / ((k : ℝ) + 1 / 4) - ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2)) := by
      intro k _
      have hden : Continuous (fun t : ℝ => ((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2) := by fun_prop
      have hne : ∀ t : ℝ, ((k : ℝ) + 1 / 4) ^ 2 + (t / 2) ^ 2 ≠ 0 := fun t => by positivity
      exact continuous_const.sub (continuous_const.div₀ hden hne)
    have hs := continuous_finsetSum (Finset.range 100) hk
    exact continuous_const.add hs
  have h : gExc = fun t => max 0 ((Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
      - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) / lamstar - 1) := rfl
  rw [h]
  exact continuous_const.max (((hT.sub continuous_const).div_const _).sub continuous_const)

theorem correction_lower :
    (1785399/250000000 : ℝ)
      ≤ ∫ t, gExc t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW (Real.log 2))) t := by
  have hL : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set spec := Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW (Real.log 2))) with hspec
  have hf : MeasureTheory.MemLp (Cvs.WeilForm.WindowRepresentative.rep (constW (Real.log 2))) 2 volume :=
    Cvs.WeilForm.WindowRepresentative.memLp_rep _
  have hfint : Integrable (Cvs.WeilForm.WindowRepresentative.rep (constW (Real.log 2))) := integrable_rep _
  have hspec_nn : ∀ t, 0 ≤ spec t := fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t
  have hspec_int : Integrable spec := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  -- integrability of gExc*spec via domination
  have hexc : Integrable (fun t => (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
      - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * spec t) := by
    have he : (fun t => (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * spec t)
        = fun t => Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t * spec t
          - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * spec t := by funext t; ring
    rw [he]; exact (Cvs.WeilForm.TruncatedEffectiveSymbol.integrable_truncArch_mul 100 hf hfint).sub (hspec_int.const_mul _)
  have hgspec_int : Integrable (fun t => gExc t * spec t) := by
    refine (hexc.const_mul (1/lamstar)).mono'
      (gExc_continuous.aestronglyMeasurable.mul hspec_int.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gExc_nonneg t) (hspec_nn t))]
    calc gExc t * spec t
        ≤ ((Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)/lamstar) * spec t :=
          mul_le_mul_of_nonneg_right (gExc_le t) (hspec_nn t)
      _ = (1/lamstar) * ((Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * spec t) := by
          rw [div_eq_inv_mul, one_div]; ring
  have heven : ∀ t, (gExc (-t) * spec (-t)) = gExc t * spec t := by
    intro t; rw [gExc_even]; exact congrArg (gExc t * ·) (spec_even hL t)
  have hhalf : (∫ t, gExc t * spec t) = 2 * ∫ t in Ioi (0:ℝ), gExc t * spec t :=
    even_integral_two_Ioi hgspec_int heven
  set spec' := (Set.Ioi (0:ℝ)).indicator spec with hspec'
  have hg_int' : Integrable (fun t => gExc t * spec' t) := by
    have : (fun t => gExc t * spec' t) = (Set.Ioi (0:ℝ)).indicator (fun t => gExc t * spec t) := by
      funext t; rw [hspec']
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
    rw [this]; exact hgspec_int.indicator measurableSet_Ioi
  have hspec'_nn : ∀ t, 0 ≤ spec' t := fun t => Set.indicator_nonneg (fun a _ => hspec_nn a) t
  have hspec'_int : Integrable spec' := hspec_int.indicator measurableSet_Ioi
  have hlc := layer_cake_lower (spec := spec') (g := gExc) 5 node5 coef5 beta5
    (hc_nn := ?_) (hg_int := hg_int') (hstep := ?_) (hB := ?_)
    (hspec_nn := hspec'_nn)
    (hspec_int := hspec'_int)
  · have hint_eq : (∫ t, gExc t * spec' t) = ∫ t in Ioi (0:ℝ), gExc t * spec t := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [hspec', Set.indicator_apply]
      by_cases ht : t ∈ Set.Ioi (0:ℝ) <;> simp [ht]
    have hsum_eq : (∑ j ∈ Finset.range 5, coef5 j * beta5 j) = 1785399/500000000 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, coef5, beta5]
      norm_num [List.getD]
    have hkey : (1785399/500000000 : ℝ) ≤ ∫ t in Ioi (0:ℝ), gExc t * spec t := by
      rw [← hsum_eq, ← hint_eq]; exact hlc
    rw [hhalf]; linarith [hkey]
  · intro j; unfold coef5; rcases j with _|_|_|_|_|j <;> norm_num [List.getD]
  · intro t
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      show coef5 0 = vval5 0 from by norm_num [coef5, vval5],
      show coef5 1 = vval5 1 - vval5 0 from by norm_num [coef5, vval5],
      show coef5 2 = vval5 2 - vval5 1 from by norm_num [coef5, vval5],
      show coef5 3 = vval5 3 - vval5 2 from by norm_num [coef5, vval5],
      show coef5 4 = vval5 4 - vval5 3 from by norm_num [coef5, vval5]]
    refine hstep5v node5 vval5 ?_
      (fun x y hx hxy => gExc_mono (by have : node5 0 = 9 := rfl; linarith) hxy)
      gExc_nonneg ?_ ?_ ⟨node_bound0, node_bound1, node_bound2, node_bound3, node_bound4⟩ t
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [node5]
    · norm_num [vval5]
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [vval5]
  · intro j hj
    have htail : ∀ s : ℝ, 0 < s → beta5 j ≤ (1/Real.pi) * (1/s - 2/(Real.log 2 * s^2)) →
        beta5 j ≤ ∫ t in Ioi s, spec' t := by
      intro s hs hb
      have hspeceq : (∫ t in Ioi s, spec' t) = ∫ t in Ioi s, spec t := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        rw [hspec', Set.indicator_of_mem (Set.mem_Ioi.mpr (lt_trans hs (Set.mem_Ioi.mp ht)))]
      rw [hspeceq]
      exact le_trans hb (spec_tail_ge hL s hs)
    fin_cases hj
    · exact htail (node5 0) (by norm_num [node5]) (beta_le_B _ _ (by norm_num [node5]) (by norm_num [beta5, node5]) (by norm_num [node5]))
    · exact htail (node5 1) (by norm_num [node5]) (beta_le_B _ _ (by norm_num [node5]) (by norm_num [beta5, node5]) (by norm_num [node5]))
    · exact htail (node5 2) (by norm_num [node5]) (beta_le_B _ _ (by norm_num [node5]) (by norm_num [beta5, node5]) (by norm_num [node5]))
    · exact htail (node5 3) (by norm_num [node5]) (beta_le_B _ _ (by norm_num [node5]) (by norm_num [beta5, node5]) (by norm_num [node5]))
    · exact htail (node5 4) (by norm_num [node5]) (beta_le_B _ _ (by norm_num [node5]) (by norm_num [beta5, node5]) (by norm_num [node5]))

theorem sqrt2_le' : Real.sqrt 2 ≤ 10000000/7071067 := by
  rw [show (10000000/7071067:ℝ) = Real.sqrt ((10000000/7071067)^2) from (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_le_sqrt; norm_num
theorem sqrt2_inv_ge : (7071067/10000000:ℝ) ≤ (Real.sqrt 2)⁻¹ := by
  rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 7071067/10000000) (Real.sqrt_pos.mpr (by norm_num)),
    show ((7071067/10000000:ℝ))⁻¹ = 10000000/7071067 by norm_num]
  exact sqrt2_le'

theorem chan_eq (a : ℝ) : Real.exp (Real.log 2 * a) = (2:ℝ) ^ a := (Real.rpow_def_of_pos (by norm_num) a).symm

theorem ch0 : (7071067/10000000:ℝ) ≤ Real.exp (-(2 * (1/4:ℝ) * Real.log 2)) := by
  rw [show (-(2 * (1/4:ℝ) * Real.log 2)) = Real.log 2 * (-(1/2)) by ring, chan_eq,
    show ((2:ℝ)) ^ (-(1/2):ℝ) = (Real.sqrt 2)⁻¹ from by
      rw [Real.rpow_neg (by norm_num), Real.rpow_div_two_eq_sqrt _ (by norm_num), Real.rpow_one]]
  exact sqrt2_inv_ge

theorem ch1 : (7071067/40000000:ℝ) ≤ Real.exp (-(2*((1:ℝ)+1/4)*Real.log 2)) := by
  rw [show (-(2*((1:ℝ)+1/4)*Real.log 2)) = Real.log 2 * (-(5/2)) by ring, chan_eq,
    show ((2:ℝ)) ^ (-(5/2):ℝ) = (Real.sqrt 2)⁻¹ * (1/4) from by
      rw [show (-(5/2):ℝ) = -(1/2) + (-2) by ring, Real.rpow_add (by norm_num),
        Real.rpow_neg (by norm_num), Real.rpow_div_two_eq_sqrt _ (by norm_num), Real.rpow_one,
        show ((2:ℝ)) ^ (-2:ℝ) = 1/4 from by
          rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]; norm_num]]
  nlinarith [sqrt2_inv_ge, Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)]

theorem ch2 : (7071067/160000000:ℝ) ≤ Real.exp (-(2*((2:ℝ)+1/4)*Real.log 2)) := by
  rw [show (-(2*((2:ℝ)+1/4)*Real.log 2)) = Real.log 2 * (-(9/2)) by ring, chan_eq,
    show ((2:ℝ)) ^ (-(9/2):ℝ) = (Real.sqrt 2)⁻¹ * (1/16) from by
      rw [show (-(9/2):ℝ) = -(1/2) + (-4) by ring, Real.rpow_add (by norm_num),
        Real.rpow_neg (by norm_num), Real.rpow_div_two_eq_sqrt _ (by norm_num), Real.rpow_one,
        show ((2:ℝ)) ^ (-4:ℝ) = 1/16 from by
          rw [show (-4:ℝ) = -((4:ℕ):ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]; norm_num]]
  nlinarith [sqrt2_inv_ge, Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)]

theorem Dsym_upper : Dsym (constW (Real.log 2)) ≤ 2877/1000 := by
  have hL : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [Dsym_constW_eq hL]
  have hsplit : (∑ k ∈ Finset.range 100,
        (1 - Real.exp (-(2 * ((k:ℝ) + 1/4) * Real.log 2))) / (2 * ((k:ℝ) + 1/4)^2))
      = (∑ k ∈ Finset.range 100, 1 / (2 * ((k:ℝ) + 1/4)^2))
        - ∑ k ∈ Finset.range 100, Real.exp (-(2 * ((k:ℝ) + 1/4) * Real.log 2)) / (2 * ((k:ℝ) + 1/4)^2) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_); rw [sub_div]
  rw [hsplit]
  set S1 := ∑ k ∈ Finset.range 100, 1 / (2 * ((k:ℝ) + 1/4)^2) with hS1
  set Se := ∑ k ∈ Finset.range 100, Real.exp (-(2 * ((k:ℝ) + 1/4) * Real.log 2)) / (2 * ((k:ℝ) + 1/4)^2) with hSe
  -- lower bound Se by 3-term
  have h3 : (∑ k ∈ Finset.range 3, Real.exp (-(2 * ((k:ℝ) + 1/4) * Real.log 2)) / (2 * ((k:ℝ) + 1/4)^2)) ≤ Se := by
    rw [hSe]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by norm_num)) (fun k _ _ => ?_)
    positivity
  have hlow : (7071067/10000000)/(2*((0:ℝ)+1/4)^2) + (7071067/40000000)/(2*((1:ℝ)+1/4)^2)
        + (7071067/160000000)/(2*((2:ℝ)+1/4)^2)
      ≤ ∑ k ∈ Finset.range 3, Real.exp (-(2 * ((k:ℝ) + 1/4) * Real.log 2)) / (2 * ((k:ℝ) + 1/4)^2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [zero_add, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    gcongr
    · exact ch0
    · exact ch1
    · exact ch2
  have hBlow : (7071067/10000000)/(2*((0:ℝ)+1/4)^2) + (7071067/40000000)/(2*((1:ℝ)+1/4)^2)
        + (7071067/160000000)/(2*((2:ℝ)+1/4)^2) ≤ Se := le_trans hlow h3
  have hS1le : S1 ≤ 2877/1000 + ((7071067/10000000)/(2*((0:ℝ)+1/4)^2) + (7071067/40000000)/(2*((1:ℝ)+1/4)^2)
        + (7071067/160000000)/(2*((2:ℝ)+1/4)^2)) := by
    rw [hS1]; norm_num [Finset.sum_range_succ]
  linarith [hBlow, hS1le]

theorem Msym_constW_lower :
    Real.log 2 - (2877/1000)/lamstar + 1785399/250000000 ≤ Msym (constW (Real.log 2)) := by
  have hL : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set spec := Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (constW (Real.log 2))) with hspec
  have hf : MeasureTheory.MemLp (Cvs.WeilForm.WindowRepresentative.rep (constW (Real.log 2))) 2 volume :=
    Cvs.WeilForm.WindowRepresentative.memLp_rep _
  have hfint : Integrable (Cvs.WeilForm.WindowRepresentative.rep (constW (Real.log 2))) := integrable_rep _
  have hspec_nn : ∀ t, 0 ≤ spec t := fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t
  have hspec_int : Integrable spec := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf hfint
  have hmass : (∫ t, spec t) = Real.log 2 := by
    rw [hspec, Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity_eq_selfConvolution hfint hf,
      Cvs.WeilForm.TruncatedArchCappedBudget.selfConvolution_zero_eq, ← Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
    exact norm_sq_constW hL.le
  -- integrabilities
  have hexc : Integrable (fun t => (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
      - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * spec t) := by
    have he : (fun t => (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * spec t)
        = fun t => Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t * spec t
          - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * spec t := by funext t; ring
    rw [he]; exact (Cvs.WeilForm.TruncatedEffectiveSymbol.integrable_truncArch_mul 100 hf hfint).sub (hspec_int.const_mul _)
  have hgspec_int : Integrable (fun t => gExc t * spec t) := by
    refine (hexc.const_mul (1/lamstar)).mono'
      (gExc_continuous.aestronglyMeasurable.mul hspec_int.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gExc_nonneg t) (hspec_nn t))]
    calc gExc t * spec t
        ≤ ((Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)/lamstar) * spec t :=
          mul_le_mul_of_nonneg_right (gExc_le t) (hspec_nn t)
      _ = (1/lamstar) * ((Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * spec t) := by
          rw [div_eq_inv_mul, one_div]; ring
  have hmcapsp : Integrable (fun t => mcap t * spec t) := by
    refine hspec_int.mono' ((mcap_continuous.aestronglyMeasurable).mul hspec_int.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mcap_nonneg t) (hspec_nn t))]
    exact mul_le_of_le_one_left (hspec_nn t) (mcap_le_one t)
  have hlin_int : Integrable (fun t => (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t
      - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)/lamstar) * spec t) := by
    have he : (fun t => (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)/lamstar) * spec t)
        = fun t => spec t - (1/lamstar) * ((Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * spec t) := by
      funext t; rw [div_eq_inv_mul, one_div]; ring
    rw [he]; exact hspec_int.sub (hexc.const_mul _)
  -- split
  have hsplit : (∫ t, (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)/lamstar) * spec t)
      + (∫ t, gExc t * spec t) ≤ Msym (constW (Real.log 2)) := by
    rw [Msym, ← integral_add hlin_int hgspec_int]
    refine integral_mono (hlin_int.add hgspec_int) hmcapsp (fun t => ?_)
    have := mcap_split_ge t (le_refl 100)
    calc (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)/lamstar) * spec t
          + gExc t * spec t = ((1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)/lamstar) + gExc t) * spec t := by ring
      _ ≤ mcap t * spec t := by
          exact mul_le_mul_of_nonneg_right this (hspec_nn t)
  -- linear integral value
  have hlinval : (∫ t, (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)/lamstar) * spec t)
      = Real.log 2 - Dsym (constW (Real.log 2)) / lamstar := by
    have he : (fun t => (1 - (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)/lamstar) * spec t)
        = fun t => spec t - (1/lamstar) * ((Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * spec t) := by
      funext t; rw [div_eq_inv_mul, one_div]; ring
    have hD : Dsym (constW (Real.log 2))
        = ∫ t, (Cvs.WeilForm.TruncatedEffectiveSymbol.truncArchSymbol 100 t - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * spec t := rfl
    rw [he, integral_sub hspec_int (hexc.const_mul _), hmass,
      MeasureTheory.integral_const_mul, hD]
    ring
  rw [hlinval] at hsplit
  have hcorr := correction_lower
  have hDsym := Dsym_upper
  have hlampos := lamstar_pos
  have hdd : Dsym (constW (Real.log 2)) / lamstar ≤ (2877/1000)/lamstar :=
    (div_le_div_iff_of_pos_right hlampos).mpr hDsym
  rw [← hspec] at hcorr
  linarith [hsplit, hcorr, hdd]

theorem reflW_smul {L : ℝ} (c : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    Cvs.WeilForm.WindowReflectionSymmetry.reflW (c • v) = c • Cvs.WeilForm.WindowReflectionSymmetry.reflW v := by
  apply Subtype.ext
  show Cvs.WeilForm.WindowReflectionSymmetry.refl L ((c • v : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 volume)
      = ((c • Cvs.WeilForm.WindowReflectionSymmetry.reflW v : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℝ 2 volume)
  rw [Submodule.coe_smul, Submodule.coe_smul]
  exact Cvs.WeilForm.WindowReflectionSymmetry.refl_smul L c _

noncomputable def enorm : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2) :=
  (Real.sqrt (Real.log 2))⁻¹ • constW (Real.log 2)

theorem reflW_enorm : Cvs.WeilForm.WindowReflectionSymmetry.reflW enorm = enorm := by
  unfold enorm; rw [reflW_smul, reflW_constW]

theorem norm_enorm : ‖(enorm : Lp ℝ 2 (volume : Measure ℝ))‖ = 1 := by
  have hL : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : ‖(constW (Real.log 2) : Lp ℝ 2 (volume : Measure ℝ))‖ = Real.sqrt (Real.log 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_constW hL.le]
  unfold enorm
  rw [Submodule.coe_smul, norm_smul, hsq, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hL))]

theorem Msym_enorm : Msym enorm = Msym (constW (Real.log 2)) / Real.log 2 := by
  have hL : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold enorm
  rw [Msym_smul, show ((Real.sqrt (Real.log 2))⁻¹)^2 = (Real.log 2)⁻¹ from by
    rw [inv_pow, Real.sq_sqrt hL.le]]
  ring

theorem hea : (274/1000 : ℝ) ≤ Msym enorm := by
  have hL : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [Msym_enorm, le_div_iff₀ hL]
  have hlow := Msym_constW_lower
  have hlog := Real.log_two_gt_d9
  rw [lamstar] at hlow
  norm_num at hlow ⊢
  nlinarith [hlow, hlog]

end Cvs.StepA.ConstantTrialFloorAtTwo
