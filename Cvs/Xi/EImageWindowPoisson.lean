import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The E-image `E_G(θ) = (a/θ) Σ_{n≥1} G(na/θ)`, its window `k_G` and Poisson summation

`E_G` is linear and vanishes below `a`; with `a = 2π/c`, `fullTail (psi c G) = E_G + aG(0)/(2θ) − ½∫G` off the
lattice, so `E_G = k_G + fullTail` a.e. when `G(0) = ∫G = 0`; `fullTail (psi 2π β) = T_β`; `‖k_G‖² ≤ H_⌊1/a⌋‖G‖²_{(0,1)}`;
and `Σ (∫hᵢ/∫h₀)² ≤ 2c/(πλ₀)`.
-/

noncomputable section

open Real Set Filter MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FullTailConvergence

namespace Cvs.Xi.EImageWindowPoisson

/-- The E-image `E_G(θ) = (a/θ) Σ_{1 ≤ n ≤ θ/a} G(na/θ)`. -/
def eimage (a : ℝ) (G : ℝ → ℝ) (θ : ℝ) : ℝ :=
  a / θ * ∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ)

/-- The window image `k_G = E_G · 1_{[a, 1]}`. -/
def window (a : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  (Icc a 1).indicator (eimage a G)

/-- The profile `T_β(θ) = (1/2θ)[1 + 2 Σ_{1 ≤ n < θ} β(n/θ)]`. -/
def Tbeta (β : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (1 + 2 * ∑ n ∈ Finset.Ico 1 ⌈θ⌉₊, β (n / θ)) / (2 * θ)

/-! ### Linearity and support -/

theorem eimage_add (a : ℝ) (G H : ℝ → ℝ) :
    eimage a (fun s => G s + H s) = fun θ => eimage a G θ + eimage a H θ := by
  funext θ; simp only [eimage, Finset.sum_add_distrib, mul_add]

theorem eimage_smul (a d : ℝ) (G : ℝ → ℝ) :
    eimage a (fun s => d * G s) = fun θ => d * eimage a G θ := by
  funext θ; simp only [eimage, ← Finset.mul_sum]; ring

theorem eimage_sub (a : ℝ) (G H : ℝ → ℝ) :
    eimage a (fun s => G s - H s) = fun θ => eimage a G θ - eimage a H θ := by
  funext θ; simp only [eimage, Finset.sum_sub_distrib, mul_sub]

theorem eimage_sum {ι : Type*} (S : Finset ι) (a : ℝ) (b : ι → ℝ) (G : ι → ℝ → ℝ) :
    eimage a (fun s => ∑ i ∈ S, b i * G i s) = fun θ => ∑ i ∈ S, b i * eimage a (G i) θ := by
  funext θ
  simp only [eimage, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n _ => by ring

theorem window_sum {ι : Type*} (S : Finset ι) (a : ℝ) (b : ι → ℝ) (G : ι → ℝ → ℝ) :
    window a (fun s => ∑ i ∈ S, b i * G i s) = fun θ => ∑ i ∈ S, b i * window a (G i) θ := by
  funext θ
  unfold window
  by_cases h : θ ∈ Icc a 1
  · simp only [indicator_of_mem h, eimage_sum]
  · simp [indicator_of_notMem h]

theorem window_sub (a : ℝ) (G H : ℝ → ℝ) :
    window a (fun s => G s - H s) = fun θ => window a G θ - window a H θ := by
  funext θ
  unfold window
  by_cases h : θ ∈ Icc a 1
  · simp only [indicator_of_mem h, eimage_sub]
  · simp [indicator_of_notMem h]

/-- `E_G` vanishes below `a`, for `a > 0`. -/
theorem eimage_of_lt {a θ : ℝ} (ha : 0 < a) (hθ : θ < a) (G : ℝ → ℝ) : eimage a G θ = 0 := by
  have : ⌊θ / a⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one ha).mpr hθ)
  simp [eimage, this]

/-- The summation points `na/θ` of `E_G` lie in `(0, 1]`, and then `θ ≥ a`. -/
theorem mem_Ioc_of_mem {a θ : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ∈ Finset.Icc 1 ⌊θ / a⌋₊) :
    a ≤ θ ∧ n * a / θ ∈ Ioc (0 : ℝ) 1 := by
  rw [Finset.mem_Icc] at hn
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
  have h2 : (n : ℝ) ≤ θ / a := (Nat.le_floor_iff' (by omega)).mp hn.2
  have hθa : a ≤ θ := by
    have := h1.trans h2; rwa [le_div_iff₀ ha, one_mul] at this
  have hθ : 0 < θ := ha.trans_le hθa
  refine ⟨hθa, by positivity, ?_⟩
  rw [div_le_one hθ]
  rwa [le_div_iff₀ ha] at h2

/-- `E_G` depends only on `G` on `(0, 1]`. -/
theorem eimage_congr {a : ℝ} (ha : 0 < a) {G H : ℝ → ℝ} (hGH : ∀ s ∈ Ioc (0 : ℝ) 1, G s = H s) :
    eimage a G = eimage a H := by
  funext θ
  unfold eimage
  congr 1
  exact Finset.sum_congr rfl fun n hn => hGH _ (mem_Ioc_of_mem ha hn).2

theorem window_of_notMem {a θ : ℝ} (G : ℝ → ℝ) (h : θ ∉ Icc a 1) : window a G θ = 0 :=
  indicator_of_notMem h _

/-- `T_β = 1/(2θ)` on `(0, 1]`. -/
theorem Tbeta_of_le_one (β : ℝ → ℝ) {θ : ℝ} (hθ : θ ≤ 1) : Tbeta β θ = 1 / (2 * θ) := by
  have : Finset.Ico 1 ⌈θ⌉₊ = ∅ :=
    Finset.Ico_eq_empty_of_le (Nat.ceil_le.mpr (by exact_mod_cast hθ))
  simp [Tbeta, this]

/-- **The rescaled cut profile**: for `0 < a ≤ 1`, `θ > 0` and `β = 0` on `[1, ∞)`,
`E_{β(·/a)}(θ) = a(T_β(θ) − 1/(2θ))`. -/
theorem eimage_rescale {a θ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hθ : 0 < θ) {β : ℝ → ℝ}
    (hβ : ∀ y, 1 ≤ y → β y = 0) :
    eimage a (fun s => β (s / a)) θ = a * (Tbeta β θ - 1 / (2 * θ)) := by
  have e1 : ∀ n : ℕ, (n : ℝ) * a / θ / a = n / θ := fun n => by field_simp
  have hsub : Finset.Ico 1 ⌈θ⌉₊ ⊆ Finset.Icc 1 ⌊θ / a⌋₊ := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [Finset.mem_Icc]
    refine ⟨hn.1, Nat.le_floor ?_⟩
    have h1 : (n : ℝ) < θ := Nat.lt_ceil.mp hn.2
    have h2 : θ ≤ θ / a := by rw [le_div_iff₀ ha]; nlinarith
    linarith
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, β (n / θ) = ∑ n ∈ Finset.Ico 1 ⌈θ⌉₊, β (n / θ) := by
    refine (Finset.sum_subset hsub fun n hn hn' => hβ _ ?_).symm
    rw [Finset.mem_Ico, not_and_or] at hn'
    rw [Finset.mem_Icc] at hn
    rcases hn' with h | h
    · exact absurd hn.1 h
    · rw [not_lt, Nat.ceil_le] at h
      rwa [le_div_iff₀ hθ, one_mul]
  simp only [eimage, e1, hsum, Tbeta]
  field_simp
  ring

/-- **The window does not see the rescaled cut profile**: `k_{G − dβ(·/a)} = k_G` for `0 < a ≤ 1` and
`β = 0` on `[1, ∞)`. -/
theorem window_sub_rescale {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (G : ℝ → ℝ) (d : ℝ) {β : ℝ → ℝ}
    (hβ : ∀ y, 1 ≤ y → β y = 0) :
    window a (fun s => G s - d * β (s / a)) = window a G := by
  funext θ
  unfold window
  by_cases h : θ ∈ Icc a 1
  · simp only [indicator_of_mem h, eimage_sub, eimage_smul (G := fun s => β (s / a))]
    rw [eimage_rescale ha ha1 (ha.trans_le h.1) hβ, Tbeta_of_le_one β h.2]
    ring
  · simp [indicator_of_notMem h]

/-! ### Poisson summation: the (I9) instance -/

/-- A symmetric integer sum folds onto `n ≥ 1`. -/
theorem sum_Icc_int (f : ℤ → ℝ) (k : ℕ) :
    ∑ n ∈ Finset.Icc (-(k : ℤ)) k, f n = f 0 + ∑ n ∈ Finset.Icc 1 k, (f n + f (-n)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)
        = insert (-((k : ℤ) + 1)) (insert ((k : ℤ) + 1) (Finset.Icc (-(k : ℤ)) k)) := by
      ext n; simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
    rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
      Finset.sum_Icc_succ_top (by omega)]
    push_cast
    ring

/-- **The Poisson piece is the E-image**: for `G` even on `[−1, 1]` and `k < cθ/(2π) < k + 1`, with `a = 2π/c`,
`poissonPiece c G k θ = E_G(θ) + aG(0)/(2θ) − ½∫G`. -/
theorem poissonPiece_eq_eimage {G : ℝ → ℝ} {c θ : ℝ} (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s)
    (hc : 0 < c) (hθ : 0 < θ) {k : ℕ} (hk : (k : ℝ) < c * θ / (2 * π)) (hk' : c * θ / (2 * π) < k + 1) :
    poissonPiece c G k θ
      = eimage (2 * π / c) G θ + 2 * π / c * G 0 / (2 * θ) - 1 / 2 * ∫ s in (-1 : ℝ)..1, G s := by
  have hpi := pi_pos
  have hfl : ⌊θ / (2 * π / c)⌋₊ = k := by
    rw [show θ / (2 * π / c) = c * θ / (2 * π) by field_simp]
    exact (Nat.floor_eq_iff (by positivity)).mpr ⟨hk.le, hk'⟩
  have hpt : ∀ n ∈ Finset.Icc 1 k, G (2 * π * ((n : ℤ) : ℝ) / (c * θ)) + G (2 * π * ((-(n : ℤ) : ℤ) : ℝ) / (c * θ))
      = 2 * G (n * (2 * π / c) / θ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn' : (n : ℝ) ≤ k := by exact_mod_cast hn.2
    have e : 2 * π * ((n : ℤ) : ℝ) / (c * θ) = n * (2 * π / c) / θ := by push_cast; field_simp
    have hm : n * (2 * π / c) / θ ∈ Icc (-1 : ℝ) 1 := by
      have h0 : 0 ≤ n * (2 * π / c) / θ := by positivity
      refine ⟨by linarith, ?_⟩
      have hlt : (n : ℝ) * (2 * π) < c * θ := by
        have := lt_of_le_of_lt hn' hk; rwa [lt_div_iff₀ (by positivity)] at this
      rw [show (n : ℝ) * (2 * π / c) / θ = n * (2 * π) / (c * θ) by field_simp, div_le_one (by positivity)]
      exact hlt.le
    rw [e, show 2 * π * (((-(n : ℤ)) : ℤ) : ℝ) / (c * θ) = -(n * (2 * π / c) / θ) by push_cast; field_simp,
      heven _ hm]
    ring
  unfold poissonPiece eimage
  rw [sum_Icc_int (fun n : ℤ => G (2 * π * (n : ℝ) / (c * θ))), Finset.sum_congr rfl hpt, hfl,
    ← Finset.mul_sum]
  simp only [Int.cast_zero, mul_zero, zero_div]
  field_simp
  ring

/-- **(I9) on the lattice complement**: for `G` even and `C²` on `[−1, 1]`, `a = 2π/c`, `θ > 1`, `θ ∉ aℕ`:
`fullTail (psi c G) θ = E_G(θ) + aG(0)/(2θ) − ½∫G`. -/
theorem fullTail_eq_eimage {G G₁ G₂ : ℝ → ℝ} {c θ : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hθ : 1 < θ)
    (hlat : ∀ k : ℕ, θ ≠ k * (2 * π / c)) :
    fullTail (psi c G) θ
      = eimage (2 * π / c) G θ + 2 * π / c * G 0 / (2 * θ) - 1 / 2 * ∫ s in (-1 : ℝ)..1, G s := by
  have hpi := pi_pos
  have hθ0 : 0 < θ := by linarith
  set k := ⌊c * θ / (2 * π)⌋₊ with hkd
  have hx : 0 ≤ c * θ / (2 * π) := by positivity
  have hk1 : (k : ℝ) ≤ c * θ / (2 * π) := Nat.floor_le hx
  have hk2 : c * θ / (2 * π) < k + 1 := Nat.lt_floor_add_one _
  have hk : (k : ℝ) < c * θ / (2 * π) := by
    refine lt_of_le_of_ne hk1 fun h => hlat k ?_
    field_simp at h ⊢
    linarith
  rw [fullTail_eq_poissonPiece hg hg₁ hg₂c hc hθ hk hk2, poissonPiece_eq_eimage heven hc hθ0 hk hk2]

theorem fullTail_of_le_one (Φ : ℝ → ℝ) {θ : ℝ} (hθ : θ ≤ 1) : fullTail Φ θ = 0 := by
  simp [fullTail, not_lt.mpr hθ]

/-- The lattice `aℕ` is Lebesgue-null. -/
theorem ae_notMem_lattice (a : ℝ) : ∀ᵐ θ : ℝ, ∀ k : ℕ, θ ≠ k * a := by
  have h : (range fun k : ℕ => (k : ℝ) * a).Countable := countable_range _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (h.measure_zero volume)] with θ hθ k hk
  exact hθ ⟨k, hk.symm⟩

/-- **The (I9) instance**: for `G̃` even and `C²` on `[−1, 1]` with `G̃(0) = 0 = ∫G̃` and `a = 2π/c`,
`E_G̃ = k_G̃ + fullTail (psi c G̃)` almost everywhere on `ℝ`. -/
theorem eimage_ae_eq_window_add_fullTail {G G₁ G₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) :
    eimage (2 * π / c) G =ᵐ[volume] fun θ => window (2 * π / c) G θ + fullTail (psi c G) θ := by
  have ha : 0 < 2 * π / c := by have := pi_pos; positivity
  filter_upwards [ae_notMem_lattice (2 * π / c)] with θ hθ
  rcases le_or_gt θ 1 with h1 | h1
  · rw [fullTail_of_le_one _ h1, add_zero]
    unfold window
    by_cases h : θ ∈ Icc (2 * π / c) 1
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]
      refine eimage_of_lt ha (lt_of_not_ge fun h' => h ⟨h', h1⟩) G
  · rw [window_of_notMem G (fun h => by linarith [h.2]), zero_add,
      fullTail_eq_eimage hg hg₁ hg₂c heven hc h1 hθ, hG0, hGi]
    ring

/-! ### The window norm -/

/-- On `(0, 1]`, `E_G(θ) = (a/θ) Σ_{1 ≤ n ≤ ⌊1/a⌋} (G·1_{[0,1]})(na/θ)`. -/
theorem eimage_eq_sum_indicator {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (G : ℝ → ℝ) :
    eimage a G θ = a / θ * ∑ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, (Icc (0 : ℝ) 1).indicator G (n * a / θ) := by
  unfold eimage
  congr 1
  have hsub : Finset.Icc 1 ⌊θ / a⌋₊ ⊆ Finset.Icc 1 ⌊1 / a⌋₊ :=
    Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (div_le_div_of_nonneg_right hθ1 ha.le))
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [indicator_of_mem (Ioc_subset_Icc_self (mem_Ioc_of_mem ha hn).2)]
  · intro n hn hn'
    refine indicator_of_notMem (fun hm => hn' ?_) _
    rw [Finset.mem_Icc] at hn ⊢
    refine ⟨hn.1, Nat.le_floor ?_⟩
    have := hm.2
    rw [div_le_one hθ] at this
    rwa [le_div_iff₀ ha]

/-- The substitution `θ ↦ na/θ` has derivative `−na/θ²` on `[a, 1]`, `a > 0`. -/
theorem hasDerivWithinAt_recip {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∀ θ ∈ Icc a 1, HasDerivWithinAt (fun θ => n * a / θ) (-(n * a) / θ ^ 2) (Icc a 1) θ := by
  intro θ hθ
  have hθ0 : θ ≠ 0 := (ha.trans_le hθ.1).ne'
  have := (hasDerivAt_inv hθ0).const_mul ((n : ℝ) * a)
  refine (this.congr_deriv (by field_simp)).hasDerivWithinAt.congr_of_mem (fun x _ => ?_) hθ
  simp [div_eq_mul_inv]

/-- The substitution `θ ↦ na/θ` is injective on `[a, 1]`, for `a > 0`, `n ≥ 1`. -/
theorem injOn_recip {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) : InjOn (fun θ => n * a / θ) (Icc a 1) := by
  intro x hx y hy hxy
  have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hy0 : y ≠ 0 := (ha.trans_le hy.1).ne'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hna : (n : ℝ) * a ≠ 0 := by positivity
  have h := hxy
  simp only at h
  rw [div_eq_div_iff hx0 hy0] at h
  exact (mul_left_cancel₀ hna h).symm

/-- The Jacobian weight: `(a/θ)² = (a/n)|−na/θ²|` for `θ > 0`, `n ≥ 1`. -/
theorem sq_div_eq_jac {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) {n : ℕ} (hn : 1 ≤ n) :
    (a / θ) ^ 2 = a / n * |-(n * a) / θ ^ 2| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hneg : -(n * a) / θ ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)
  rw [abs_of_nonpos hneg]
  field_simp

/-- One summand of the window energy: `∫_{[a,1]} (a/θ)² F(na/θ) = (a/n)∫_{image} F`, by `u = na/θ`. -/
theorem integral_term_eq {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) (F : ℝ → ℝ) :
    ∫ θ in Icc a 1, (a / θ) ^ 2 * F (n * a / θ)
      = a / n * ∫ u in (fun θ => n * a / θ) '' Icc a 1, F u := by
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Icc (hasDerivWithinAt_recip ha n)
    (injOn_recip ha hn), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  simp only [smul_eq_mul]
  rw [sq_div_eq_jac ha (ha.trans_le hθ.1) hn]
  ring

/-- **The window norm**: `∫ k_G² ≤ H_⌊1/a⌋ ∫_{[0,1]} G²` for `a > 0` (Cauchy–Schwarz over the at most `1/a`
summands, then `u = na/θ` in each). -/
theorem integral_window_sq_le {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ}
    (hG : IntegrableOn (fun u => G u ^ 2) (Icc 0 1)) :
    ∫ θ, window a G θ ^ 2 ≤ (harmonic ⌊1 / a⌋₊ : ℝ) * ∫ u in Icc (0 : ℝ) 1, G u ^ 2 := by
  set N := ⌊1 / a⌋₊ with hN
  set Gc := (Icc (0 : ℝ) 1).indicator G with hGc
  set I := ∫ u in Icc (0 : ℝ) 1, G u ^ 2 with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have hGc2 : (fun u => Gc u ^ 2) = (Icc (0 : ℝ) 1).indicator (fun u => G u ^ 2) := by
    funext u; by_cases h : u ∈ Icc (0 : ℝ) 1 <;> simp [hGc, h]
  have hGci : Integrable (fun u => Gc u ^ 2) := by
    rw [hGc2]; exact (integrable_indicator_iff measurableSet_Icc).mpr hG
  have hGcI : ∫ u, Gc u ^ 2 = I := by rw [hGc2, integral_indicator measurableSet_Icc]
  -- the window energy is the energy on `[a, 1]`
  have hw : ∫ θ, window a G θ ^ 2 = ∫ θ in Icc a 1, eimage a G θ ^ 2 := by
    rw [← integral_indicator measurableSet_Icc]
    congr 1; funext θ
    unfold window
    by_cases h : θ ∈ Icc a 1 <;> simp [h]
  rw [hw]
  -- each summand
  have hterm : ∀ n ∈ Finset.Icc 1 N, IntegrableOn (fun θ => (a / θ) ^ 2 * Gc (n * a / θ) ^ 2) (Icc a 1) ∧
      ∫ θ in Icc a 1, (a / θ) ^ 2 * Gc (n * a / θ) ^ 2 ≤ a / n * I := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hint := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
      (hasDerivWithinAt_recip ha n) (injOn_recip ha hn1) (fun u => Gc u ^ 2)).mp hGci.integrableOn
    refine ⟨?_, ?_⟩
    · refine IntegrableOn.congr_fun (hint.const_mul (a / n)) (fun θ hθ => ?_) measurableSet_Icc
      simp only [smul_eq_mul]
      rw [sq_div_eq_jac ha (ha.trans_le hθ.1) hn1]
      ring
    · rw [integral_term_eq ha hn1 (fun u => Gc u ^ 2)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← hGcI]
      exact setIntegral_le_integral hGci (ae_of_all _ fun _ => sq_nonneg _)
  -- Cauchy–Schwarz pointwise
  have hpt : ∀ θ ∈ Icc a 1, eimage a G θ ^ 2
      ≤ N * ∑ n ∈ Finset.Icc 1 N, (a / θ) ^ 2 * Gc (n * a / θ) ^ 2 := by
    intro θ hθ
    have hθ0 : 0 < θ := ha.trans_le hθ.1
    rw [eimage_eq_sum_indicator ha hθ0 hθ.2, mul_pow, ← Finset.mul_sum]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 N) (f := fun n : ℕ => Gc (n * a / θ))
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcs
    have : 0 ≤ (a / θ) ^ 2 := sq_nonneg _
    nlinarith
  have hsumi : IntegrableOn (fun θ => (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (a / θ) ^ 2 * Gc (n * a / θ) ^ 2)
      (Icc a 1) :=
    (integrable_finsetSum _ fun n hn => (hterm n hn).1).const_mul _
  have hstep : ∫ θ in Icc a 1, eimage a G θ ^ 2
      ≤ ∫ θ in Icc a 1, (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, (a / θ) ^ 2 * Gc (n * a / θ) ^ 2 :=
    integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hsumi
      ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ hpt))
  rw [integral_const_mul, integral_finsetSum _ fun n hn => (hterm n hn).1] at hstep
  have hsum : ∑ n ∈ Finset.Icc 1 N, ∫ θ in Icc a 1, (a / θ) ^ 2 * Gc (n * a / θ) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 N, a / n * I := Finset.sum_le_sum fun n hn => (hterm n hn).2
  have hH : ∑ n ∈ Finset.Icc 1 N, a / n * I = a * I * (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hNa : (N : ℝ) * a ≤ 1 := by
    have := Nat.floor_le (show 0 ≤ 1 / a by positivity)
    rw [← hN] at this
    rwa [le_div_iff₀ ha] at this
  have hHn : (0 : ℝ) ≤ harmonic N := by
    rw [harmonic_eq_sum_Icc]; push_cast; exact Finset.sum_nonneg fun i _ => by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc ∫ θ in Icc a 1, eimage a G θ ^ 2
      ≤ N * ∑ n ∈ Finset.Icc 1 N, ∫ θ in Icc a 1, (a / θ) ^ 2 * Gc (n * a / θ) ^ 2 := hstep
    _ ≤ N * (a * I * (harmonic N : ℝ)) := by
        rw [← hH]; exact mul_le_mul_of_nonneg_left hsum hN0
    _ = (N * a) * ((harmonic N : ℝ) * I) := by ring
    _ ≤ 1 * ((harmonic N : ℝ) * I) := mul_le_mul_of_nonneg_right hNa (mul_nonneg hHn hI0)
    _ = (harmonic N : ℝ) * I := one_mul _

/-- **The window norm against `‖G‖²_{[−1,1]}`**: for `G` even and continuous on `[−1, 1]`,
`∫ k_G² ≤ (H_⌊1/a⌋/2) ∫_{−1}^{1} G²`. -/
theorem integral_window_sq_le_half {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} (hGc : ContinuousOn G (Icc (-1 : ℝ) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) :
    ∫ θ, window a G θ ^ 2 ≤ (harmonic ⌊1 / a⌋₊ : ℝ) / 2 * ∫ s in (-1 : ℝ)..1, G s ^ 2 := by
  have hG01 : ContinuousOn (fun u => G u ^ 2) (Icc (0 : ℝ) 1) :=
    (hGc.mono (Icc_subset_Icc (by norm_num) le_rfl)).pow 2
  have h := integral_window_sq_le ha hG01.integrableOn_Icc
  rw [Cvs.Prolate.AngularBesselInequality.integral_sq_even hGc heven, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  linarith

/-! ### The pole-free coefficients -/

/-- **The pole-free coefficients are square-summable**: for `hᵢ` orthonormal on `[−1, 1]` and `g₀` the normalised
even ground state (`psi c g₀ = μ₀g₀`), `Σᵢ (∫hᵢ/∫g₀)² ≤ 2c/(πλ₀)`, `λ₀ = (μ₀√(c/2π))²`. -/
theorem sum_alpha_sq_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (h : ι → ℝ → ℝ)
    (hh : ∀ i ∈ S, ContinuousOn (h i) (uIcc (-1) 1))
    (horth : ∀ i ∈ S, ∀ j ∈ S, ∫ s in (-1 : ℝ)..1, h i s * h j s = if i = j then 1 else 0)
    {g₀ g₁ g₂ : ℝ → ℝ} {c χ μ₀ : ℝ} (hc : 0 < c)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₀ (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g₀ s + χ * g₀ s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g₀ (-s) = g₀ s)
    (h0 : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio χ).ncard = 0)
    (hnorm : ∫ s in (-1 : ℝ)..1, g₀ s ^ 2 = 1) (hμ₀ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g₀ s = μ₀ * g₀ s) :
    ∑ i ∈ S, ((∫ s in (-1 : ℝ)..1, h i s) / ∫ s in (-1 : ℝ)..1, g₀ s) ^ 2
      ≤ 2 * c / (π * (μ₀ * √(c / (2 * π))) ^ 2) := by
  have hB := Cvs.Prolate.AngularBesselInequality.sum_sq_integral_le S h (f := fun _ => 1) continuousOn_const hh horth
  simp only [one_mul, one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hB
  rw [show (1 : ℝ) - -1 = 2 by norm_num] at hB
  have hhalf := Cvs.Prolate.AngularBesselInequality.half_le_ground_sq hg hg₁ hang heven h0 hnorm
  have hsq := Cvs.Prolate.AngularBesselInequality.integral_sq_eq hc hμ₀
  set L := (μ₀ * √(c / (2 * π))) ^ 2 with hL
  set J := ∫ s in (-1 : ℝ)..1, g₀ s with hJ
  have hpi := pi_pos
  have hL0 : 0 ≤ L := sq_nonneg _
  rw [Finset.sum_congr rfl fun i _ => div_pow _ _ 2, ← Finset.sum_div]
  rcases hL0.eq_or_lt with hLz | hLp
  · have : J ^ 2 = 0 := by rw [hsq, ← hLz]; ring
    rw [this, div_zero, ← hLz, mul_zero, div_zero]
  · have hJ2 : π / c * L ≤ J ^ 2 := by
      rw [hsq]
      have := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2 * π / c * L by positivity)
      calc π / c * L = 2 * π / c * L * (1 / 2) := by ring
        _ ≤ _ := this
    have hJp : 0 < J ^ 2 := lt_of_lt_of_le (by positivity) hJ2
    rw [div_le_div_iff₀ hJp (by positivity)]
    calc (∑ i ∈ S, (∫ s in (-1 : ℝ)..1, h i s) ^ 2) * (π * L) ≤ 2 * (π * L) :=
          mul_le_mul_of_nonneg_right hB (by positivity)
      _ = 2 * c * (π / c * L) := by field_simp
      _ ≤ 2 * c * J ^ 2 := mul_le_mul_of_nonneg_left hJ2 (by positivity)

end Cvs.Xi.EImageWindowPoisson
