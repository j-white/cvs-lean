import Mathlib
import Cvs.StepA.Edge.TwoEdgeSplit
import Cvs.Upstream.ExpDifferenceBound
import Cvs.Upstream.OscillationBeatsError
import Cvs.Upstream.SimultaneousApproximation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge discriminant: Rayleigh quotients, phases and simultaneous return

For a finite family with weights `m ≥ 0` at depth `δ > 0` the edge Rayleigh quotients lie in
`[−M/2δ, M/2δ]`; `edgeDisc = sSup + sInf` moves with the phases, changes sign up to the antipodal
distance, has a witness vanishing past its support bound when positive, and the phases return
together along `L = log n`.
-/

noncomputable section

open Real MeasureTheory Filter Topology

namespace Cvs.StepA.Edge.EdgeDiscriminant
open Cvs.ZeroCounting

open Cvs.StepA.Edge.TwoEdgeSplit (edgePair edgeForm phaseDist abs_edgeForm_le abs_edgeForm_sub_le norm_sq_edgePair_le norm_exp_phase)

/-! ### The edge discriminant -/

/-- The edge Rayleigh quotients at scale `L`, over continuous profiles on `[0, a]`. -/
def edgeRay {α : Type*} (s : Finset α) (m γ : α → ℝ) (δ L : ℝ) : Set ℝ :=
  {r | ∃ F : ℝ → ℝ, ∃ a : ℝ, Continuous F ∧ 0 < ∫ u in (0 : ℝ)..a, F u ^ 2 ∧
    r = edgeForm s m γ δ L F a / ∫ u in (0 : ℝ)..a, F u ^ 2}

/-- The edge discriminant `sup + inf` of the edge Rayleigh quotients at scale `L`. -/
def edgeDisc {α : Type*} (s : Finset α) (m γ : α → ℝ) (δ L : ℝ) : ℝ :=
  sSup (edgeRay s m γ δ L) + sInf (edgeRay s m γ δ L)

/-! ### The edge Rayleigh quotients -/

/-- The edge Rayleigh quotients are nonempty. -/
theorem edgeRay_nonempty {α : Type*} (s : Finset α) (m γ : α → ℝ) (δ L : ℝ) :
    (edgeRay s m γ δ L).Nonempty :=
  ⟨_, fun _ => 1, 1, continuous_const, by simp, rfl⟩

/-- A positive square integral over `[0, a]` forces `a > 0`. -/
theorem pos_of_integral_sq_pos {F : ℝ → ℝ} {a : ℝ} (h : 0 < ∫ u in (0 : ℝ)..a, F u ^ 2) :
    0 < a := by
  by_contra ha
  push Not at ha
  have : ∫ u in (0 : ℝ)..a, F u ^ 2 ≤ 0 := by
    rw [intervalIntegral.integral_symm]
    exact neg_nonpos.mpr (intervalIntegral.integral_nonneg ha fun u _ => sq_nonneg _)
  linarith

section Ray

variable {α : Type*} (s : Finset α) {m : α → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) (γ : α → ℝ) {δ : ℝ}
  (hδ : 0 < δ) (L : ℝ)

include hm hδ in
/-- Every edge Rayleigh quotient lies in `[−(∑ m)/(2δ), (∑ m)/(2δ)]`. -/
theorem abs_le_of_mem_edgeRay {r : ℝ} (hr : r ∈ edgeRay s m γ δ L) :
    |r| ≤ (∑ i ∈ s, m i) / (2 * δ) := by
  obtain ⟨F, a, hF, hpos, rfl⟩ := hr
  have ha := (pos_of_integral_sq_pos hpos).le
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have h := abs_edgeForm_le s hm γ hδ L hF ha
  calc |edgeForm s m γ δ L F a| ≤ (∑ i ∈ s, m i) * (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := h
    _ = (∑ i ∈ s, m i) / (2 * δ) * ∫ u in (0 : ℝ)..a, F u ^ 2 := by ring

include hm hδ in
/-- The edge Rayleigh quotients are bounded below. -/
theorem edgeRay_bddBelow : BddBelow (edgeRay s m γ δ L) :=
  ⟨-((∑ i ∈ s, m i) / (2 * δ)), fun _ hr => (abs_le.mp (abs_le_of_mem_edgeRay s hm γ hδ L hr)).1⟩

include hm hδ in
/-- **The infimum is an edge lower bound**: `sInf · ∫₀^a F² ≤ edgeForm(F, a)` for every continuous
`F` and `a ≥ 0`. -/
theorem sInf_mul_le_edgeForm {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a) :
    sInf (edgeRay s m γ δ L) * ∫ u in (0 : ℝ)..a, F u ^ 2 ≤ edgeForm s m γ δ L F a := by
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..a, F u ^ 2 :=
    intervalIntegral.integral_nonneg ha fun u _ => sq_nonneg _
  rcases h0.lt_or_eq with hpos | hzero
  · have hmem : edgeForm s m γ δ L F a / (∫ u in (0 : ℝ)..a, F u ^ 2) ∈ edgeRay s m γ δ L :=
      ⟨F, a, hF, hpos, rfl⟩
    have h := csInf_le (edgeRay_bddBelow s hm γ hδ L) hmem
    rwa [le_div_iff₀ hpos] at h
  · have h := abs_edgeForm_le s hm γ hδ L hF ha
    rw [← hzero, mul_zero, zero_div, abs_nonpos_iff] at h
    rw [← hzero, mul_zero, h]

end Ray

/-- **An edge lower bound moves with the phases**: if `λ` is an edge lower bound at `L₀`, then
`λ − phaseDist(L, L₀)/(2δ)` is one at `L`. -/
theorem edgeLower_shift {α : Type*} (s : Finset α) {m : α → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) (γ : α → ℝ)
    {δ : ℝ} (hδ : 0 < δ) {L₀ lam : ℝ}
    (hlam : ∀ F : ℝ → ℝ, ∀ a : ℝ, Continuous F → 0 ≤ a →
      lam * ∫ u in (0 : ℝ)..a, F u ^ 2 ≤ edgeForm s m γ δ L₀ F a) (L : ℝ) :
    ∀ F : ℝ → ℝ, ∀ a : ℝ, Continuous F → 0 ≤ a →
      (lam - phaseDist s m γ L L₀ / (2 * δ)) * ∫ u in (0 : ℝ)..a, F u ^ 2
        ≤ edgeForm s m γ δ L F a := by
  intro F a hF ha
  have h1 := hlam F a hF ha
  have h2 := (abs_le.mp (abs_edgeForm_sub_le s hm γ hδ L L₀ hF ha)).1
  have e : (lam - phaseDist s m γ L L₀ / (2 * δ)) * ∫ u in (0 : ℝ)..a, F u ^ 2
      = lam * (∫ u in (0 : ℝ)..a, F u ^ 2)
        - phaseDist s m γ L L₀ * (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := by ring
  rw [e]
  linarith

/-! ### Antisymmetry up to the antipodal distance -/

/-! ### A witness vanishing beyond its support bound -/

/-- The cutoff `min 1 (max 0 ((k+1)(a − u)))`: `1` up to `a − 1/(k+1)`, `0` from `a` on. -/
def cutoff (a : ℝ) (k : ℕ) (u : ℝ) : ℝ := min 1 (max 0 (((k : ℝ) + 1) * (a - u)))

/-- The cutoff is continuous. -/
@[fun_prop] theorem continuous_cutoff (a : ℝ) (k : ℕ) : Continuous (cutoff a k) := by
  unfold cutoff; fun_prop

/-- The cutoff vanishes from `a` on. -/
theorem cutoff_of_le {a u : ℝ} (k : ℕ) (h : a ≤ u) : cutoff a k u = 0 := by
  unfold cutoff
  rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))]
  exact min_eq_right zero_le_one

/-- The cutoff lies in `[0, 1]`. -/
theorem abs_cutoff_le (a : ℝ) (k : ℕ) (u : ℝ) : |cutoff a k u| ≤ 1 := by
  unfold cutoff
  rw [abs_le]
  constructor
  · exact le_min (by norm_num) ((le_max_left _ _).trans' (by norm_num))
  · exact min_le_left _ _

/-- Below `a`, the cutoff is eventually `1`. -/
theorem eventually_cutoff_eq_one {a u : ℝ} (h : u < a) : ∀ᶠ k : ℕ in atTop, cutoff a k u = 1 := by
  filter_upwards [eventually_ge_atTop ⌈1 / (a - u)⌉₊] with k hk
  have hau : 0 < a - u := by linarith
  have h1 : 1 / (a - u) ≤ (k : ℝ) + 1 := ((Nat.ceil_le).mp hk).trans (by linarith)
  have h2 : 1 ≤ ((k : ℝ) + 1) * (a - u) := by
    rw [div_le_iff₀ hau] at h1; linarith
  unfold cutoff
  exact min_eq_left (h2.trans (le_max_right _ _))

/-- **The cut-off edge pairing converges**: for `δ ≥ 0`, continuous `F` and `a ≥ 0`,
`edgePair(F · cutoff_k, a) → edgePair(F, a)`. -/
theorem tendsto_edgePair_cutoff {δ : ℝ} (hδ : 0 ≤ δ) (γ : ℝ) {F : ℝ → ℝ} (hF : Continuous F)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun k : ℕ => edgePair δ γ (fun u => F u * cutoff a k u) a) atTop
      (𝓝 (edgePair δ γ F a)) := by
  unfold edgePair
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun u => |F u|)
    (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => ?_)
    (hF.abs.intervalIntegrable _ _) ?_
  · exact (by fun_prop : Continuous fun u : ℝ => ((F u * cutoff a k u : ℝ) : ℂ)
      * Complex.exp (-((δ : ℂ) + γ * Complex.I) * u)).aestronglyMeasurable
      |>.restrict
  · refine Eventually.of_forall fun u hu => ?_
    rw [Set.uIoc_of_le ha] at hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Complex.norm_exp]
    have h1 : (-((δ : ℂ) + γ * Complex.I) * u).re = -(δ * u) := by simp
    rw [h1]
    have h2 : Real.exp (-(δ * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hu.1])
    have h3 := abs_cutoff_le a k u
    calc |F u| * |cutoff a k u| * Real.exp (-(δ * u)) ≤ |F u| * 1 * 1 := by
          gcongr
      _ = |F u| := by ring
  · filter_upwards [Measure.ae_ne volume a] with u hua hu
    rw [Set.uIoc_of_le ha] at hu
    have hlt : u < a := lt_of_le_of_ne hu.2 hua
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cutoff_eq_one hlt] with k hk
    rw [hk, mul_one]

/-- **The cut-off energy converges**: for continuous `F` and `a ≥ 0`,
`∫₀^a (F · cutoff_k)² → ∫₀^a F²`. -/
theorem tendsto_integral_sq_cutoff {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun k : ℕ => ∫ u in (0 : ℝ)..a, (F u * cutoff a k u) ^ 2) atTop
      (𝓝 (∫ u in (0 : ℝ)..a, F u ^ 2)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun u => F u ^ 2)
    (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => ?_)
    ((by fun_prop : Continuous fun u => F u ^ 2).intervalIntegrable _ _) ?_
  · exact (by fun_prop : Continuous fun u : ℝ => (F u * cutoff a k u) ^ 2).aestronglyMeasurable
      |>.restrict
  · refine Eventually.of_forall fun u _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    have h3 := abs_cutoff_le a k u
    have h4 : cutoff a k u ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h3
    nlinarith [sq_nonneg (F u)]
  · filter_upwards [Measure.ae_ne volume a] with u hua hu
    rw [Set.uIoc_of_le ha] at hu
    have hlt : u < a := lt_of_le_of_ne hu.2 hua
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cutoff_eq_one hlt] with k hk
    rw [hk, mul_one]

/-- **A witness vanishing beyond its support bound**: if a continuous `F` has edge quotient above
`t` on `[0, a]`, so does some continuous `F'` vanishing on `[a, ∞)`. -/
theorem exists_vanishing_witness {α : Type*} (s : Finset α) (m γ : α → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (L : ℝ) {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ} (hpos : 0 < ∫ u in (0 : ℝ)..a, F u ^ 2) {t : ℝ}
    (ht : t < edgeForm s m γ δ L F a / ∫ u in (0 : ℝ)..a, F u ^ 2) :
    ∃ F' : ℝ → ℝ, Continuous F' ∧ (∀ u, a ≤ u → F' u = 0) ∧ 0 < ∫ u in (0 : ℝ)..a, F' u ^ 2 ∧
      t < edgeForm s m γ δ L F' a / ∫ u in (0 : ℝ)..a, F' u ^ 2 := by
  have ha := (pos_of_integral_sq_pos hpos).le
  have hform : Tendsto (fun k : ℕ => edgeForm s m γ δ L (fun u => F u * cutoff a k u) a) atTop
      (𝓝 (edgeForm s m γ δ L F a)) := by
    unfold edgeForm
    refine tendsto_finsetSum s fun i _ => ?_
    refine Tendsto.const_mul (m i) ?_
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_const_nhds.mul ((tendsto_edgePair_cutoff hδ (γ i) hF ha).pow 2))
  have hq := hform.div (tendsto_integral_sq_cutoff hF ha) hpos.ne'
  obtain ⟨k, hk1, hk2⟩ := ((hq.eventually (lt_mem_nhds ht)).and
    ((tendsto_integral_sq_cutoff hF ha).eventually (lt_mem_nhds hpos))).exists
  exact ⟨fun u => F u * cutoff a k u, hF.mul (continuous_cutoff a k),
    fun u hu => by simp only [cutoff_of_le k hu, mul_zero], hk2, hk1⟩

/-- **Below the supremum, a witness vanishing past its support bound**: for `δ ≥ 0` and `t` below
the supremum of the edge Rayleigh quotients at `L`, some continuous `F` vanishing on `[a, ∞)`,
`a ≥ 0`, has `∫₀^a F² > 0` and edge quotient above `t`. -/
theorem exists_vanishing_gt_of_lt_sSup {α : Type*} (s : Finset α) (m γ : α → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) {L t : ℝ} (ht : t < sSup (edgeRay s m γ δ L)) :
    ∃ (F : ℝ → ℝ) (a : ℝ), Continuous F ∧ 0 ≤ a ∧ (∀ u, a ≤ u → F u = 0) ∧
      0 < ∫ u in (0 : ℝ)..a, F u ^ 2 ∧
      t < edgeForm s m γ δ L F a / ∫ u in (0 : ℝ)..a, F u ^ 2 := by
  obtain ⟨r, ⟨F, a, hF, hn, rfl⟩, hr⟩ := exists_lt_of_lt_csSup (edgeRay_nonempty s m γ δ L) ht
  obtain ⟨F₀, hF₀, hsupp, hn₀, hq⟩ := exists_vanishing_witness s m γ hδ L hF hn hr
  exact ⟨F₀, a, hF₀, (pos_of_integral_sq_pos hn).le, hsupp, hn₀, hq⟩

/-! ### Profiles vanishing past their support bound -/

/-! ### Simultaneous return of the phases along `log n` -/

/-- **Simultaneous return of finitely many rotations at integer times**: for every `η > 0`,
frequently in `T ∈ ℕ`, `‖e^{iγᵢT} − 1‖ ≤ η` for all `i ∈ s`. -/
theorem frequently_phase_return {α : Type*} (s : Finset α) (γ : α → ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ᶠ T : ℕ in atTop, ∀ i ∈ s, ‖Complex.exp (γ i * T * Complex.I) - 1‖ ≤ η := by
  rw [frequently_atTop]
  intro T₀
  obtain ⟨Q, hQ, hQη⟩ : ∃ Q : ℕ, 0 < Q ∧ 2 * π / Q ≤ η := by
    refine ⟨⌈2 * π / η⌉₊ + 1, Nat.succ_pos _, ?_⟩
    have h1 : 2 * π / η ≤ (⌈2 * π / η⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hη] at h1
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  obtain ⟨n, hn0, -, happ⟩ := Cvs.Operator.exists_simultaneous_approx
    (fun j : Fin s.card => γ (s.equivFin.symm j) * ((T₀ + 1 : ℕ) : ℝ) / (2 * π)) hQ
  refine ⟨n * (T₀ + 1), by nlinarith, fun i hi => ?_⟩
  have h := happ (s.equivFin ⟨i, hi⟩)
  simp only [Equiv.symm_apply_apply] at h
  rw [UnitAddCircle.norm_eq] at h
  set x : ℝ := γ i * ((T₀ + 1 : ℕ) : ℝ) / (2 * π) * n with hx
  have hT : (γ i : ℂ) * (((n * (T₀ + 1) : ℕ) : ℝ) : ℂ) * Complex.I
      = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
    rw [hx]
    have hπ : (2 * π : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hk : Complex.exp (((2 * π * (round x : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
    have e : ((2 * π * (round x : ℝ) : ℝ) : ℂ) * Complex.I
        = (round x : ℤ) * (2 * π * Complex.I) := by push_cast; ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  have hcast : (γ i : ℂ) * ((n * (T₀ + 1) : ℕ) : ℂ) * Complex.I
      = (γ i : ℂ) * (((n * (T₀ + 1) : ℕ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hcast, hT, ← hk]
  refine (Cvs.Upstream.ExpDifferenceBound.norm_exp_sub_exp_le _ _).trans ?_
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  calc 2 * π * |x - (round x : ℝ)| ≤ 2 * π * (1 / Q) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * π / Q := by ring
    _ ≤ η := hQη

/-- **Simultaneous recurrence along `log n`**: for a finite family, `m ≥ 0`, any `L₀` and `ε > 0`,
`phaseDist(log n, L₀) ≤ ε` for arbitrarily large natural `n`. -/
theorem frequently_phaseDist_log_le {α : Type*} (s : Finset α) {m : α → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i)
    (γ : α → ℝ) (L₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, phaseDist s m γ (Real.log n) L₀ ≤ ε := by
  set M := ∑ i ∈ s, m i with hM
  set G := ∑ i ∈ s, m i * |γ i| with hG
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i hi => hm i hi
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun i hi => mul_nonneg (hm i hi) (abs_nonneg _)
  set η := ε / (2 * (M + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hret := frequently_atTop.mp (frequently_phase_return s γ hη0)
  rw [frequently_atTop]
  intro n₀
  obtain ⟨T, hT, hTret⟩ := hret ⌈max (n₀ : ℝ) (2 * G / ε) + |L₀|⌉₊
  set L := L₀ + T with hL
  have hTge : max (n₀ : ℝ) (2 * G / ε) + |L₀| ≤ T := (Nat.ceil_le).mp hT
  have hLge : max (n₀ : ℝ) (2 * G / ε) ≤ L := by
    have := neg_abs_le L₀; rw [hL]; linarith
  have hLexp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  refine ⟨⌈Real.exp L⌉₊, ?_, ?_⟩
  · have h1 : (n₀ : ℝ) ≤ Real.exp L := ((le_max_left _ _).trans hLge).trans hLexp
    exact_mod_cast h1.trans (Nat.le_ceil _)
  · have hlog := Cvs.Upstream.OscillationBeatsError.abs_log_natCeil_sub_log_le (Real.exp_pos L)
    rw [Real.log_exp] at hlog
    have hGe : G * (Real.exp L)⁻¹ ≤ ε / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos L)]
      have h2 : 2 * G / ε ≤ L := (le_max_right _ _).trans hLge
      rw [div_le_iff₀ hε] at h2
      nlinarith
    have hterm : ∀ i ∈ s, m i * ‖Complex.exp (γ i * (Real.log (⌈Real.exp L⌉₊ : ℕ)) * Complex.I)
        - Complex.exp (γ i * L₀ * Complex.I)‖
        ≤ m i * |γ i| * (Real.exp L)⁻¹ + m i * η := by
      intro i hi
      have h1 : ‖Complex.exp (γ i * (Real.log (⌈Real.exp L⌉₊ : ℕ)) * Complex.I)
          - Complex.exp (γ i * L * Complex.I)‖ ≤ |γ i| * (Real.exp L)⁻¹ := by
        have := Cvs.Upstream.ExpDifferenceBound.norm_exp_sub_exp_le
          (γ i * Real.log (⌈Real.exp L⌉₊ : ℕ)) (γ i * L)
        rw [Complex.ofReal_mul, Complex.ofReal_mul] at this
        refine this.trans ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
      have h2 : ‖Complex.exp (γ i * L * Complex.I) - Complex.exp (γ i * L₀ * Complex.I)‖ ≤ η := by
        have e : Complex.exp (γ i * L * Complex.I) - Complex.exp (γ i * L₀ * Complex.I)
            = Complex.exp (γ i * L₀ * Complex.I) * (Complex.exp (γ i * T * Complex.I) - 1) := by
          rw [mul_sub, mul_one, ← Complex.exp_add, hL]; congr 2; push_cast; ring
        rw [e, norm_mul, norm_exp_phase, one_mul]
        exact hTret i hi
      have h3 := norm_sub_le_norm_sub_add_norm_sub
        (Complex.exp (γ i * (Real.log (⌈Real.exp L⌉₊ : ℕ)) * Complex.I))
        (Complex.exp (γ i * L * Complex.I)) (Complex.exp (γ i * L₀ * Complex.I))
      have h4 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add h1 h2)) (hm i hi)
      linarith [h4]
    unfold phaseDist
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← hG, ← hM]
    have hMη : M * η ≤ ε / 2 := by
      rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith

end Cvs.StepA.Edge.EdgeDiscriminant
