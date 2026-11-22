import Mathlib
import Cvs.Finite.ExponentialKernelValue
import Cvs.StepA.OneZeroParitySectors
import Cvs.Upstream.CauchySchwarzInterval
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.CompactTestAdmissibility
import Cvs.Zeta.ExplicitFormula.PrefactorClosedForm

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two-edge split of the centred transform at a common depth

At `w = γ − iδ`, `δ > 0`, the centred transform of an even profile, or of `F(t + L/2) − F(L/2 − t)`
with `F` vanishing past `a`, splits at the two window edges, so `Re ctr²` is
`±e^{δL} Re(e^{iγL}(∫₀^a F e^{−(δ+iγ)u})²)` up to `O(e^{δL/2})`; a finite family's even block is
bounded below, and its odd block above, by its edge form.
-/

noncomputable section

open Real MeasureTheory

namespace Cvs.StepA.Edge.TwoEdgeSplit
open Cvs.ZeroCounting

/-! ### The edge form of a finite family at a common depth -/

/-- The edge pairing `∫₀^a F(u) e^{−(δ + iγ)u} du`. -/
def edgePair (δ γ : ℝ) (F : ℝ → ℝ) (a : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..a, ((F u : ℝ) : ℂ) * Complex.exp (-((δ : ℂ) + γ * Complex.I) * u)

/-- The edge form of a finite family at common depth `δ`: `∑ᵢ mᵢ Re(e^{iγᵢL} edgePairᵢ²)`. -/
def edgeForm {α : Type*} (s : Finset α) (m γ : α → ℝ) (δ L : ℝ) (F : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∑ i ∈ s, m i * (Complex.exp (γ i * L * Complex.I) * edgePair δ (γ i) F a ^ 2).re

/-! ### The exponential integrals -/

/-- `∫₀^a e^{cu} du = (e^{ca} − 1)/c` for `c ≠ 0`. -/
theorem integral_exp_mul_eq {c : ℝ} (hc : c ≠ 0) (a : ℝ) :
    ∫ u in (0 : ℝ)..a, Real.exp (c * u) = (Real.exp (c * a) - 1) / c := by
  rw [Cvs.Finite.ExponentialKernelValue.integral_exp_mul hc 0 a, mul_zero, Real.exp_zero]

/-- `∫₀^a e^{−2δu} du ≤ 1/(2δ)` for `δ > 0`. -/
theorem integral_exp_neg_le {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    ∫ u in (0 : ℝ)..a, Real.exp (-(2 * δ) * u) ≤ 1 / (2 * δ) := by
  rw [integral_exp_mul_eq (by linarith) a]
  have h1 : 0 < Real.exp (-(2 * δ) * a) := Real.exp_pos _
  rw [show (Real.exp (-(2 * δ) * a) - 1) / -(2 * δ) = (1 - Real.exp (-(2 * δ) * a)) / (2 * δ) by
    rw [div_neg, ← neg_div]; ring_nf]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- `∫₀^a e^{2δu} du ≤ e^{2δa}/(2δ)` for `δ > 0`. -/
theorem integral_exp_pos_le {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    ∫ u in (0 : ℝ)..a, Real.exp (2 * δ * u) ≤ Real.exp (2 * δ * a) / (2 * δ) := by
  rw [integral_exp_mul_eq (by positivity) a]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-! ### The edge pairing against the profile's energy -/

/-- The norm of `∫₀^a F(u) e^{−iuw} du` against the energy: for `a ≥ 0`,
`‖∫₀^a F e^{−iuw}‖² ≤ (∫₀^a F²)(∫₀^a e^{2u Im w})`. -/
theorem norm_sq_integral_le {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a) (w : ℂ) :
    ‖∫ u in (0 : ℝ)..a, ((F u : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u)‖ ^ 2
      ≤ (∫ u in (0 : ℝ)..a, F u ^ 2) * ∫ u in (0 : ℝ)..a, Real.exp (2 * w.im * u) := by
  have hn : ∀ u : ℝ, ‖((F u : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u)‖
      = |F u| * Real.exp (w.im * u) := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, Complex.mul_im]
  have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun u : ℝ => ((F u : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u)) ha
  simp only [hn] at h1
  have h2 := Cvs.Upstream.CauchySchwarzInterval.intervalIntegral_mul_sq_le (f := fun u => |F u|)
    (g := fun u => Real.exp (w.im * u)) ha hF.abs (by fun_prop)
  have e1 : ∀ u, |F u| ^ 2 = F u ^ 2 := fun u => sq_abs _
  have e2 : ∀ u, Real.exp (w.im * u) ^ 2 = Real.exp (2 * w.im * u) := fun u => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp only [e1, e2] at h2
  have h0 : 0 ≤ ‖∫ u in (0 : ℝ)..a, ((F u : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u)‖ :=
    norm_nonneg _
  calc ‖∫ u in (0 : ℝ)..a, ((F u : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u)‖ ^ 2
      ≤ (∫ u in (0 : ℝ)..a, |F u| * Real.exp (w.im * u)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

/-- The pairing `∫₀^a F(u) e^{−iuw} du` of a profile on `[0, a]` with the exponential at `w`. -/
def expPair (w : ℂ) (F : ℝ → ℝ) (a : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..a, ((F u : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u)

/-- The edge pairing is `expPair` at `w = γ − iδ`. -/
theorem edgePair_eq_expPair (δ γ : ℝ) (F : ℝ → ℝ) (a : ℝ) :
    edgePair δ γ F a = expPair ((γ : ℂ) - δ * Complex.I) F a := by
  unfold edgePair expPair
  refine intervalIntegral.integral_congr fun u _ => ?_
  have h : -((δ : ℂ) + γ * Complex.I) * u = -(Complex.I * ((γ : ℂ) - δ * Complex.I)) * u := by
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [h]

/-- **The edge pairing against the energy**: `‖edgePair‖² ≤ (∫₀^a F²)/(2δ)` for `δ > 0`, `a ≥ 0`. -/
theorem norm_sq_edgePair_le {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ}
    (ha : 0 ≤ a) : ‖edgePair δ γ F a‖ ^ 2 ≤ (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := by
  rw [edgePair_eq_expPair]
  refine (norm_sq_integral_le hF ha _).trans ?_
  have him : ((γ : ℂ) - δ * Complex.I).im = -δ := by simp
  rw [him]
  have hE := integral_exp_neg_le hδ a
  have hF0 : 0 ≤ ∫ u in (0 : ℝ)..a, F u ^ 2 :=
    intervalIntegral.integral_nonneg ha fun u _ => sq_nonneg _
  calc (∫ u in (0 : ℝ)..a, F u ^ 2) * ∫ u in (0 : ℝ)..a, Real.exp (2 * -δ * u)
      = (∫ u in (0 : ℝ)..a, F u ^ 2) * ∫ u in (0 : ℝ)..a, Real.exp (-(2 * δ) * u) := by
        congr 2; funext u; ring_nf
    _ ≤ (∫ u in (0 : ℝ)..a, F u ^ 2) * (1 / (2 * δ)) := mul_le_mul_of_nonneg_left hE hF0
    _ = (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := by ring

/-! ### The centred transform split at the two edges -/

/-- **The centred transform from the left edge**: `ctr g w = e^{iLw/2} ∫₀^L g(u − L/2) e^{−iuw}
du`. -/
theorem ctr_eq_expPair (L : ℝ) (g : ℝ → ℝ) (w : ℂ) :
    Cvs.StepA.OneZeroParitySectors.ctr L g w
      = Complex.exp (Complex.I * L * w / 2) * expPair w (fun u => g (u - L / 2)) L := by
  unfold Cvs.StepA.OneZeroParitySectors.ctr expPair
  rw [← intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_sub_right
    (fun t : ℝ => Complex.exp (-((t : ℂ) * w) * Complex.I) * ((g t : ℝ) : ℂ))
    (a := 0) (b := L) (L / 2)
  rw [show (0 : ℝ) - L / 2 = -(L / 2) by ring, show L - L / 2 = L / 2 by ring] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [mul_comm (Complex.exp (-(((u - L / 2 : ℝ) : ℂ) * w) * Complex.I)), mul_left_comm,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Reflection**: `∫₀^L F(L − u) e^{−iuw} du = e^{−iLw} ∫₀^L F(v) e^{ivw} dv`. -/
theorem expPair_reflect (L : ℝ) (F : ℝ → ℝ) (w : ℂ) :
    expPair w (fun u => F (L - u)) L = Complex.exp (-(Complex.I * L * w)) * expPair (-w) F L := by
  unfold expPair
  rw [← intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_sub_left
    (fun v : ℝ => ((F v : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * ((L - v : ℝ) : ℂ)))
    (a := 0) (b := L) L
  rw [sub_self, sub_zero] at h
  simp only [sub_sub_cancel] at h
  rw [h]
  refine intervalIntegral.integral_congr fun v _ => ?_
  rw [show Complex.exp (-(Complex.I * L * w))
        * (((F v : ℝ) : ℂ) * Complex.exp (-(Complex.I * -w) * v))
      = ((F v : ℝ) : ℂ) * (Complex.exp (-(Complex.I * L * w)) * Complex.exp (-(Complex.I * -w) * v))
      by ring, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A continuous real profile times an exponential is interval integrable. -/
theorem intervalIntegrable_expPair {F : ℝ → ℝ} (hF : Continuous F) (w : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => ((F u : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u))
      volume a b :=
  (by fun_prop : Continuous fun u : ℝ =>
    ((F u : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u)).intervalIntegrable _ _

/-- **The even split**: for an even continuous `g` and `F(u) = g(u − L/2)`,
`∫₀^L F e^{−iuw} = ∫₀^{L/2} F e^{−iuw} + e^{−iLw} ∫₀^{L/2} F e^{iuw}`. -/
theorem expPair_even_split (L : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (heven : ∀ t, g (-t) = g t)
    (w : ℂ) :
    expPair w (fun u => g (u - L / 2)) L
      = expPair w (fun u => g (u - L / 2)) (L / 2)
        + Complex.exp (-(Complex.I * L * w)) * expPair (-w) (fun u => g (u - L / 2)) (L / 2) := by
  have hF : Continuous fun u => g (u - L / 2) := hg.comp (continuous_sub_right _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_expPair hF w 0 (L / 2)) (intervalIntegrable_expPair hF w (L / 2) L)
  unfold expPair
  rw [← hsplit]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => ((g (u - L / 2) : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u))
    (a := 0) (b := L / 2) L
  rw [sub_zero, show L - L / 2 = L / 2 by ring] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun v _ => ?_
  simp only
  have hg' : g (L - v - L / 2) = g (v - L / 2) := by
    rw [show L - v - L / 2 = -(v - L / 2) by ring, heven]
  rw [hg', mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The even profile at the two edges**: for even continuous `g`, `F(u) = g(u − L/2)`,
`ctr g w = e^{iLw/2} ∫₀^{L/2} F e^{−iuw} + e^{−iLw/2} ∫₀^{L/2} F e^{iuw}`. -/
theorem ctr_even_split (L : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (heven : ∀ t, g (-t) = g t) (w : ℂ) :
    Cvs.StepA.OneZeroParitySectors.ctr L g w
      = Complex.exp (Complex.I * L * w / 2) * expPair w (fun u => g (u - L / 2)) (L / 2)
        + Complex.exp (-(Complex.I * L * w / 2))
          * expPair (-w) (fun u => g (u - L / 2)) (L / 2) := by
  rw [ctr_eq_expPair, expPair_even_split L hg heven, mul_add, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring_nf

/-- The odd profile built from `F` at the two edges: `g(t) = F(t + L/2) − F(L/2 − t)`. -/
def oddEdge (L : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ := F (t + L / 2) - F (L / 2 - t)

/-- The odd edge profile is odd. -/
theorem oddEdge_neg (L : ℝ) (F : ℝ → ℝ) (t : ℝ) : oddEdge L F (-t) = -oddEdge L F t := by
  unfold oddEdge
  rw [show -t + L / 2 = L / 2 - t by ring, show L / 2 - -t = t + L / 2 by ring]
  ring

/-- The odd edge profile of a continuous `F` is continuous. -/
theorem continuous_oddEdge (L : ℝ) {F : ℝ → ℝ} (hF : Continuous F) : Continuous (oddEdge L F) := by
  unfold oddEdge; fun_prop

/-- **The odd edge profile at the two edges**:
`ctr (oddEdge F) w = e^{iLw/2} ∫₀^L F e^{−iuw} − e^{−iLw/2} ∫₀^L F e^{iuw}`. -/
theorem ctr_oddEdge (L : ℝ) {F : ℝ → ℝ} (hF : Continuous F) (w : ℂ) :
    Cvs.StepA.OneZeroParitySectors.ctr L (oddEdge L F) w
      = Complex.exp (Complex.I * L * w / 2) * expPair w F L
        - Complex.exp (-(Complex.I * L * w / 2)) * expPair (-w) F L := by
  rw [ctr_eq_expPair]
  have e : (fun u => oddEdge L F (u - L / 2)) = fun u => F u - F (L - u) := by
    funext u; unfold oddEdge; congr 2 <;> ring
  have hsub : expPair w (fun u => F u - F (L - u)) L
      = expPair w F L - expPair w (fun u => F (L - u)) L := by
    unfold expPair
    rw [← intervalIntegral.integral_sub (intervalIntegrable_expPair hF w 0 L)
      (intervalIntegrable_expPair (F := fun u => F (L - u)) (by fun_prop) w 0 L)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only
    push_cast
    ring
  rw [e, hsub, expPair_reflect, mul_sub, ← mul_assoc, ← Complex.exp_add]
  congr 3
  ring

/-! ### Squares at the two edges -/

/-- `e^{iLw/2}·e^{−iLw/2} = 1`. -/
theorem exp_half_mul_exp_neg_half (L : ℝ) (w : ℂ) :
    Complex.exp (Complex.I * L * w / 2) * Complex.exp (-(Complex.I * L * w / 2)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- `(e^{iLw/2})² = e^{iLw}`. -/
theorem exp_half_sq (L : ℝ) (w : ℂ) :
    Complex.exp (Complex.I * L * w / 2) ^ 2 = Complex.exp (Complex.I * L * w) := by
  rw [sq, ← Complex.exp_add]; congr 1; ring

/-- `(e^{−iLw/2})² = e^{−iLw}`. -/
theorem exp_neg_half_sq (L : ℝ) (w : ℂ) :
    Complex.exp (-(Complex.I * L * w / 2)) ^ 2 = Complex.exp (-(Complex.I * L * w)) := by
  rw [sq, ← Complex.exp_add]; congr 1; ring

/-- The two-edge square, sign `s`: `(e^{iLw/2}P + s e^{−iLw/2}Q)² = e^{iLw}P² + 2sPQ + e^{−iLw}Q²`
for `s² = 1`. -/
theorem two_edge_sq (L : ℝ) (w P Q s : ℂ) (hs : s ^ 2 = 1) :
    (Complex.exp (Complex.I * L * w / 2) * P + s * (Complex.exp (-(Complex.I * L * w / 2)) * Q)) ^ 2
      = Complex.exp (Complex.I * L * w) * P ^ 2 + 2 * s * P * Q
        + Complex.exp (-(Complex.I * L * w)) * Q ^ 2 := by
  have h1 := exp_half_mul_exp_neg_half L w
  have h2 := exp_half_sq L w
  have h3 := exp_neg_half_sq L w
  linear_combination (2 * s * P * Q) * h1 + P ^ 2 * h2 + (s ^ 2 * Q ^ 2) * h3
    + Complex.exp (-(Complex.I * L * w)) * Q ^ 2 * hs

/-- **The real part of a two-edge square from below**: for `‖s‖ = 1`,
`Re(EP² + 2sPQ + E'Q²) ≥ Re(EP²) − 2‖P‖‖Q‖ − ‖E'‖‖Q‖²`. -/
theorem re_two_edge_ge (E E' P Q s : ℂ) (hs : ‖s‖ = 1) :
    (E * P ^ 2).re - 2 * ‖P‖ * ‖Q‖ - ‖E'‖ * ‖Q‖ ^ 2
      ≤ (E * P ^ 2 + 2 * s * P * Q + E' * Q ^ 2).re := by
  have h1 : -(2 * ‖P‖ * ‖Q‖) ≤ (2 * s * P * Q).re := by
    have := neg_le_of_abs_le (Complex.abs_re_le_norm (2 * s * P * Q))
    simpa [norm_mul, hs] using this
  have h2 : -(‖E'‖ * ‖Q‖ ^ 2) ≤ (E' * Q ^ 2).re := by
    have := neg_le_of_abs_le (Complex.abs_re_le_norm (E' * Q ^ 2))
    simpa [norm_mul, norm_pow] using this
  rw [Complex.add_re, Complex.add_re]
  linarith

/-! ### One point at depth `δ`, in each sector -/

/-- `e^{iL(γ − iδ)} = e^{δL} e^{iγL}`. -/
theorem exp_I_mul_w (L δ γ : ℝ) :
    Complex.exp (Complex.I * L * ((γ : ℂ) - δ * Complex.I))
      = (Real.exp (δ * L) : ℂ) * Complex.exp (γ * L * Complex.I) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `‖e^{−iL(γ − iδ)}‖ = e^{−δL}`. -/
theorem norm_exp_neg_I_mul_w (L δ γ : ℝ) :
    ‖Complex.exp (-(Complex.I * L * ((γ : ℂ) - δ * Complex.I)))‖ = Real.exp (-(δ * L)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- `Re(e^{iL(γ − iδ)} P²) = e^{δL} Re(e^{iγL} P²)`. -/
theorem re_exp_I_mul_w_mul (L δ γ : ℝ) (P : ℂ) :
    (Complex.exp (Complex.I * L * ((γ : ℂ) - δ * Complex.I)) * P ^ 2).re
      = Real.exp (δ * L) * (Complex.exp (γ * L * Complex.I) * P ^ 2).re := by
  rw [exp_I_mul_w, mul_assoc, Complex.re_ofReal_mul]

/-- The energy bound for the reversed edge: `‖∫₀^a F e^{iuw}‖² ≤ (∫₀^a F²) e^{2δa}/(2δ)` at
`w = γ − iδ`, `δ > 0`, `a ≥ 0`. -/
theorem norm_sq_expPair_neg_le {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ}
    (ha : 0 ≤ a) :
    ‖expPair (-((γ : ℂ) - δ * Complex.I)) F a‖ ^ 2
      ≤ (∫ u in (0 : ℝ)..a, F u ^ 2) * (Real.exp (2 * δ * a) / (2 * δ)) := by
  have h := norm_sq_integral_le hF ha (-((γ : ℂ) - δ * Complex.I))
  have him : (-((γ : ℂ) - δ * Complex.I)).im = δ := by simp
  rw [him] at h
  have hF0 : 0 ≤ ∫ u in (0 : ℝ)..a, F u ^ 2 :=
    intervalIntegral.integral_nonneg ha fun u _ => sq_nonneg _
  exact h.trans (mul_le_mul_of_nonneg_left (integral_exp_pos_le hδ a) hF0)

/-- **One point in the even sector, from below**: for `δ > 0`, `L ≥ 0`, even continuous `g`,
`F(u) = g(u − L/2)` and `A = ∫₀^{L/2} F²`,
`Re(ctr(g, γ − iδ)²) ≥ e^{δL} Re(e^{iγL} edgePair(F, L/2)²) − A(2e^{δL/2} + 1)/(2δ)`. -/
theorem re_ctr_sq_even_ge {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℝ}
    (hg : Continuous g) (heven : ∀ t, g (-t) = g t) :
    Real.exp (δ * L) * (Complex.exp (γ * L * Complex.I)
        * edgePair δ γ (fun u => g (u - L / 2)) (L / 2) ^ 2).re
      - (∫ u in (0 : ℝ)..L / 2, g (u - L / 2) ^ 2) * (2 * Real.exp (δ * L / 2) + 1) / (2 * δ)
      ≤ (Cvs.StepA.OneZeroParitySectors.ctr L g ((γ : ℂ) - δ * Complex.I) ^ 2).re := by
  have hF : Continuous fun u => g (u - L / 2) := hg.comp (continuous_sub_right _)
  have hL2 : 0 ≤ L / 2 := by linarith
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ u in (0 : ℝ)..L / 2, g (u - L / 2) ^ 2 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := hA ▸ intervalIntegral.integral_nonneg hL2 fun u _ => sq_nonneg _
  obtain ⟨P, hP⟩ : ∃ P, P = expPair ((γ : ℂ) - δ * Complex.I) (fun u => g (u - L / 2)) (L / 2) :=
    ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = expPair (-((γ : ℂ) - δ * Complex.I)) (fun u => g (u - L / 2)) (L / 2) :=
    ⟨_, rfl⟩
  have hctr : Cvs.StepA.OneZeroParitySectors.ctr L g ((γ : ℂ) - δ * Complex.I)
      = Complex.exp (Complex.I * L * ((γ : ℂ) - δ * Complex.I) / 2) * P
        + 1 * (Complex.exp (-(Complex.I * L * ((γ : ℂ) - δ * Complex.I) / 2)) * Q) := by
    rw [one_mul, hP, hQ]; exact ctr_even_split L hg heven _
  rw [hctr, two_edge_sq L _ P Q 1 (by norm_num), edgePair_eq_expPair, ← hP, ← hA]
  have hlow := re_two_edge_ge (Complex.exp (Complex.I * L * ((γ : ℂ) - δ * Complex.I)))
    (Complex.exp (-(Complex.I * L * ((γ : ℂ) - δ * Complex.I)))) P Q 1 (by simp)
  rw [re_exp_I_mul_w_mul, norm_exp_neg_I_mul_w] at hlow
  have hP2 : ‖P‖ ^ 2 ≤ A / (2 * δ) := by
    rw [hP, hA, ← edgePair_eq_expPair]; exact norm_sq_edgePair_le hδ γ hF hL2
  have hQ2 : ‖Q‖ ^ 2 ≤ A * (Real.exp (δ * L) / (2 * δ)) := by
    have h := norm_sq_expPair_neg_le hδ γ hF hL2
    rw [show 2 * δ * (L / 2) = δ * L by ring, ← hQ, ← hA] at h
    exact h
  have hPQ : ‖P‖ * ‖Q‖ ≤ A * Real.exp (δ * L / 2) / (2 * δ) := by
    have hsq : (‖P‖ * ‖Q‖) ^ 2 ≤ (A * Real.exp (δ * L / 2) / (2 * δ)) ^ 2 := by
      rw [mul_pow]
      calc ‖P‖ ^ 2 * ‖Q‖ ^ 2 ≤ A / (2 * δ) * (A * (Real.exp (δ * L) / (2 * δ))) :=
            mul_le_mul hP2 hQ2 (sq_nonneg _) (by positivity)
        _ = (A * Real.exp (δ * L / 2) / (2 * δ)) ^ 2 := by
            rw [Cvs.Detection.exp_half_sq (δ * L)]; field_simp
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have hQ' : Real.exp (-(δ * L)) * ‖Q‖ ^ 2 ≤ A / (2 * δ) := by
    calc Real.exp (-(δ * L)) * ‖Q‖ ^ 2 ≤ Real.exp (-(δ * L)) * (A * (Real.exp (δ * L) / (2 * δ))) :=
          mul_le_mul_of_nonneg_left hQ2 (Real.exp_pos _).le
      _ = A / (2 * δ) := by
          rw [show Real.exp (-(δ * L)) * (A * (Real.exp (δ * L) / (2 * δ)))
              = A * (Real.exp (-(δ * L)) * Real.exp (δ * L)) / (2 * δ) by ring, ← Real.exp_add,
            neg_add_cancel, Real.exp_zero, mul_one]
  have hfin : A * (2 * Real.exp (δ * L / 2) + 1) / (2 * δ)
      = 2 * (A * Real.exp (δ * L / 2) / (2 * δ)) + A / (2 * δ) := by ring
  have hPQ2 : 2 * ‖P‖ * ‖Q‖ ≤ 2 * (A * Real.exp (δ * L / 2) / (2 * δ)) := by
    rw [mul_assoc]; linarith
  rw [hfin]
  refine le_trans ?_ hlow
  linarith

/-- The pairing over `[0, L]` of a profile vanishing on `[a, ∞)`, `a ≤ L`, is the pairing over
`[0, a]`. -/
theorem expPair_eq_of_vanish {F : ℝ → ℝ} (hF : Continuous F) {a L : ℝ} (haL : a ≤ L)
    (hsupp : ∀ u, a ≤ u → F u = 0) (w : ℂ) : expPair w F L = expPair w F a := by
  unfold expPair
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
    (intervalIntegrable_expPair hF w 0 a) (intervalIntegrable_expPair hF w a L)]
  have h0 : ∫ u in a..L, ((F u : ℝ) : ℂ) * Complex.exp (-(Complex.I * w) * u) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => ?_]
    · simp
    · rw [Set.uIcc_of_le haL] at hu
      simp [hsupp u hu.1]
  rw [h0, add_zero]

/-- The odd-witness constant `2‖P₊‖‖P₋‖ + ‖P₋‖²` at `w = γ − iδ`. -/
def oddConst (δ γ : ℝ) (F : ℝ → ℝ) (a : ℝ) : ℝ :=
  2 * ‖expPair ((γ : ℂ) - δ * Complex.I) F a‖ * ‖expPair (-((γ : ℂ) - δ * Complex.I)) F a‖
    + ‖expPair (-((γ : ℂ) - δ * Complex.I)) F a‖ ^ 2

/-- **One point in the odd sector, from above, for an edge profile**: for `δ ≥ 0`, `L ≥ 0` and
continuous `F` vanishing on `[a, ∞)` with `a ≤ L`,
`−Re(ctr(oddEdge F, γ − iδ)²) ≤ −e^{δL} Re(e^{iγL} edgePair(F, a)²) + oddConst`. -/
theorem neg_re_ctr_sq_oddEdge_le {δ : ℝ} (hδ : 0 ≤ δ) (γ : ℝ) {L : ℝ} (hL : 0 ≤ L) {F : ℝ → ℝ}
    (hF : Continuous F) {a : ℝ} (haL : a ≤ L) (hsupp : ∀ u, a ≤ u → F u = 0) :
    -(Cvs.StepA.OneZeroParitySectors.ctr L (oddEdge L F) ((γ : ℂ) - δ * Complex.I) ^ 2).re
      ≤ -(Real.exp (δ * L) * (Complex.exp (γ * L * Complex.I) * edgePair δ γ F a ^ 2).re)
        + oddConst δ γ F a := by
  obtain ⟨P, hP⟩ : ∃ P, P = expPair ((γ : ℂ) - δ * Complex.I) F a := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = expPair (-((γ : ℂ) - δ * Complex.I)) F a := ⟨_, rfl⟩
  have hctr : Cvs.StepA.OneZeroParitySectors.ctr L (oddEdge L F) ((γ : ℂ) - δ * Complex.I)
      = Complex.exp (Complex.I * L * ((γ : ℂ) - δ * Complex.I) / 2) * P
        + (-1) * (Complex.exp (-(Complex.I * L * ((γ : ℂ) - δ * Complex.I) / 2)) * Q) := by
    rw [ctr_oddEdge L hF _, expPair_eq_of_vanish hF haL hsupp, expPair_eq_of_vanish hF haL hsupp,
      hP, hQ]
    ring
  rw [hctr, two_edge_sq L _ P Q (-1) (by norm_num), edgePair_eq_expPair, ← hP]
  have hlow := re_two_edge_ge (Complex.exp (Complex.I * L * ((γ : ℂ) - δ * Complex.I)))
    (Complex.exp (-(Complex.I * L * ((γ : ℂ) - δ * Complex.I)))) P Q (-1) (by simp)
  rw [re_exp_I_mul_w_mul, norm_exp_neg_I_mul_w] at hlow
  have he : Real.exp (-(δ * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hQ' : Real.exp (-(δ * L)) * ‖Q‖ ^ 2 ≤ ‖Q‖ ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) he
  unfold oddConst
  rw [← hP, ← hQ]
  linarith

/-! ### The two energies -/

/-- For an even continuous `g`, `∫_{−L/2}^{L/2} g² = 2 ∫₀^{L/2} g(u − L/2)²`. -/
theorem integral_sq_even (L : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (heven : ∀ t, g (-t) = g t) :
    ∫ t in -(L / 2)..L / 2, g t ^ 2 = 2 * ∫ u in (0 : ℝ)..L / 2, g (u - L / 2) ^ 2 := by
  have h1 : ∫ u in (0 : ℝ)..L / 2, g (u - L / 2) ^ 2 = ∫ t in -(L / 2)..0, g t ^ 2 := by
    have h := intervalIntegral.integral_comp_sub_right (fun t => g t ^ 2) (a := 0) (b := L / 2)
      (L / 2)
    rw [zero_sub, sub_self] at h
    exact h
  have h2 : ∫ t in (0 : ℝ)..L / 2, g t ^ 2 = ∫ t in -(L / 2)..0, g t ^ 2 := by
    have h := intervalIntegral.integral_comp_neg (fun t => g t ^ 2) (a := 0) (b := L / 2)
    rw [neg_zero] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun t _ => by simp only [heven]
  have hc : Continuous fun t => g t ^ 2 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), h1, h2]
  ring

/-- The square integral over `[0, L]` of a profile vanishing on `[a, ∞)`, `a ≤ L`, is that over
`[0, a]`. -/
theorem integral_sq_eq_of_vanish {F : ℝ → ℝ} (hF : Continuous F) {a L : ℝ} (haL : a ≤ L)
    (hsupp : ∀ u, a ≤ u → F u = 0) :
    ∫ u in (0 : ℝ)..L, F u ^ 2 = ∫ u in (0 : ℝ)..a, F u ^ 2 := by
  have hc : Continuous fun u => F u ^ 2 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) (hc.intervalIntegrable 0 a)
    (hc.intervalIntegrable a L)]
  have h0 : ∫ u in a..L, F u ^ 2 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_]
    · simp
    · rw [Set.uIcc_of_le haL] at hu
      simp [hsupp u hu.1]
  rw [h0, add_zero]

/-- **The energy of the odd edge profile**: for continuous `F` vanishing on `[a, ∞)` with
`0 ≤ a`, `2a ≤ L`, `∫_{−L/2}^{L/2} (oddEdge F)² = 2 ∫₀^a F²`. -/
theorem integral_oddEdge_sq {F : ℝ → ℝ} (hF : Continuous F) {a L : ℝ} (ha : 0 ≤ a) (haL : 2 * a ≤ L)
    (hsupp : ∀ u, a ≤ u → F u = 0) :
    ∫ t in -(L / 2)..L / 2, oddEdge L F t ^ 2 = 2 * ∫ u in (0 : ℝ)..a, F u ^ 2 := by
  have hpt : ∀ t, oddEdge L F t ^ 2 = F (t + L / 2) ^ 2 + F (L / 2 - t) ^ 2 := by
    intro t
    have hcross : F (t + L / 2) * F (L / 2 - t) = 0 := by
      rcases le_or_gt 0 t with ht | ht
      · rw [hsupp (t + L / 2) (by linarith), zero_mul]
      · rw [hsupp (L / 2 - t) (by linarith), mul_zero]
    unfold oddEdge
    linear_combination (-2 : ℝ) * hcross
  simp_rw [hpt]
  have c1 : Continuous fun t => F (t + L / 2) ^ 2 := by fun_prop
  have c2 : Continuous fun t => F (L / 2 - t) ^ 2 := by fun_prop
  rw [intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
  have h1 : ∫ t in -(L / 2)..L / 2, F (t + L / 2) ^ 2 = ∫ u in (0 : ℝ)..L, F u ^ 2 := by
    have h := intervalIntegral.integral_comp_add_right (fun u => F u ^ 2) (a := -(L / 2))
      (b := L / 2) (L / 2)
    rw [neg_add_cancel, add_halves] at h
    exact h
  have h2 : ∫ t in -(L / 2)..L / 2, F (L / 2 - t) ^ 2 = ∫ u in (0 : ℝ)..L, F u ^ 2 := by
    have h := intervalIntegral.integral_comp_sub_left (fun u => F u ^ 2) (a := -(L / 2))
      (b := L / 2) (L / 2)
    rw [sub_self, sub_neg_eq_add, add_halves] at h
    exact h
  rw [h1, h2, integral_sq_eq_of_vanish hF (by linarith) hsupp]
  ring

/-! ### The sector pairings through the centred transform -/

/-- For an even interval-integrable `g`, `Re(ctr(g, z)²) = (∫ g ue)² − (∫ g ve)²`. -/
theorem re_ctr_sq_of_even (L : ℝ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2)) (heven : ∀ t, g (-t) = g t) (z : ℂ) :
    (Cvs.StepA.OneZeroParitySectors.ctr L g z ^ 2).re
      = (∫ t in -(L / 2)..L / 2, g t * Cvs.StepA.OneZeroParitySectors.ue z t) ^ 2
        - (∫ t in -(L / 2)..L / 2, g t * Cvs.StepA.OneZeroParitySectors.ve z t) ^ 2 := by
  have h := Cvs.StepA.OneZeroParitySectors.re_sqTransform_of_even L hg heven z
  rwa [Cvs.StepA.OneZeroParitySectors.sqTransform_eq_ctr, (Cvs.StepA.OneZeroParitySectors.ctr_of_even L hg heven z).2,
    ← sq] at h

/-- For an odd interval-integrable `g`, `−Re(ctr(g, z)²) = (∫ g uo)² − (∫ g vo)²`. -/
theorem neg_re_ctr_sq_of_odd (L : ℝ) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2)) (hodd : ∀ t, g (-t) = -g t) (z : ℂ) :
    -(Cvs.StepA.OneZeroParitySectors.ctr L g z ^ 2).re
      = (∫ t in -(L / 2)..L / 2, g t * Cvs.StepA.OneZeroParitySectors.uo z t) ^ 2
        - (∫ t in -(L / 2)..L / 2, g t * Cvs.StepA.OneZeroParitySectors.vo z t) ^ 2 := by
  have h := Cvs.StepA.OneZeroParitySectors.re_sqTransform_of_odd L hg hodd z
  rwa [Cvs.StepA.OneZeroParitySectors.sqTransform_eq_ctr, (Cvs.StepA.OneZeroParitySectors.ctr_of_odd L hg hodd z).2,
    mul_neg, ← sq, Complex.neg_re] at h

/-- For an even or odd `g`, `ctr(g, −z)² = ctr(g, z)²`. -/
theorem ctr_neg_sq (L : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-(L / 2)) (L / 2))
    (hpar : (∀ t, g (-t) = g t) ∨ ∀ t, g (-t) = -g t) (z : ℂ) :
    Cvs.StepA.OneZeroParitySectors.ctr L g (-z) ^ 2 = Cvs.StepA.OneZeroParitySectors.ctr L g z ^ 2 := by
  rcases hpar with h | h
  · rw [(Cvs.StepA.OneZeroParitySectors.ctr_of_even L hg h z).2]
  · rw [(Cvs.StepA.OneZeroParitySectors.ctr_of_odd L hg h z).2, neg_sq]

/-! ### The edge form: bounds and phase dependence -/

/-- `‖e^{iγL}‖ = 1`. -/
theorem norm_exp_phase (γ L : ℝ) : ‖Complex.exp (γ * L * Complex.I)‖ = 1 := by
  have := Complex.norm_exp_ofReal_mul_I (γ * L)
  push_cast at this
  exact this

/-- One term of the edge form is at most the squared edge pairing. -/
theorem abs_re_phase_mul_le (θ : ℂ) (hθ : ‖θ‖ = 1) (P : ℂ) : |(θ * P ^ 2).re| ≤ ‖P‖ ^ 2 := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, hθ, one_mul, norm_pow]

/-- **The edge form against the energy**: for `δ > 0`, `a ≥ 0`, `m ≥ 0` and continuous `F`,
`|edgeForm| ≤ (∑ m)(∫₀^a F²)/(2δ)`. -/
theorem abs_edgeForm_le {α : Type*} (s : Finset α) {m : α → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) (γ : α → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (L : ℝ) {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a) :
    |edgeForm s m γ δ L F a| ≤ (∑ i ∈ s, m i) * (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := by
  unfold edgeForm
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [abs_mul, abs_of_nonneg (hm i hi), mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hm i hi)
  exact (abs_re_phase_mul_le _ (norm_exp_phase _ _) _).trans (norm_sq_edgePair_le hδ _ hF ha)

/-- The phase distance `∑ mᵢ ‖e^{iγᵢL} − e^{iγᵢL'}‖` of two scales. -/
def phaseDist {α : Type*} (s : Finset α) (m γ : α → ℝ) (L L' : ℝ) : ℝ :=
  ∑ i ∈ s, m i * ‖Complex.exp (γ i * L * Complex.I) - Complex.exp (γ i * L' * Complex.I)‖

/-- **The edge form moves with the phases**: for `δ > 0`, `a ≥ 0`, `m ≥ 0`,
`|edgeForm(L) − edgeForm(L')| ≤ phaseDist(L, L') (∫₀^a F²)/(2δ)`. -/
theorem abs_edgeForm_sub_le {α : Type*} (s : Finset α) {m : α → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i)
    (γ : α → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (L L' : ℝ) {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ} (ha : 0 ≤ a) :
    |edgeForm s m γ δ L F a - edgeForm s m γ δ L' F a|
      ≤ phaseDist s m γ L L' * (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := by
  unfold edgeForm phaseDist
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  set θ := Complex.exp (γ i * L * Complex.I)
  set θ' := Complex.exp (γ i * L' * Complex.I)
  set P := edgePair δ (γ i) F a
  have h1 : |m i * (θ * P ^ 2).re - m i * (θ' * P ^ 2).re| = m i * |((θ - θ') * P ^ 2).re| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (hm i hi), sub_mul, Complex.sub_re]
  have h2 : |((θ - θ') * P ^ 2).re| ≤ ‖θ - θ'‖ * ((∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ)) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (norm_sq_edgePair_le hδ _ hF ha) (norm_nonneg _)
  rw [h1]
  calc m i * |((θ - θ') * P ^ 2).re|
      ≤ m i * (‖θ - θ'‖ * ((∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ))) :=
        mul_le_mul_of_nonneg_left h2 (hm i hi)
    _ = m i * ‖θ - θ'‖ * (∫ u in (0 : ℝ)..a, F u ^ 2) / (2 * δ) := by ring

/-! ### The top block of a finite family, in each sector -/

section Block

variable {α : Type*} (s : Finset α) {m : α → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) (γ : α → ℝ)

include hm in
/-- **The even block from below**: for `δ > 0`, `L ≥ 0`, an edge lower bound `λ` at `L` and an even
continuous `g`, `∑ᵢ mᵢ Re(ctr(g, γᵢ − iδ)²) ≥ (e^{δL}λ/2 − (∑ m)(2e^{δL/2} + 1)/(4δ)) ∫ g²`. -/
theorem even_block_ge {δ : ℝ} (hδ : 0 < δ) {L : ℝ} (hL : 0 ≤ L) {lam : ℝ}
    (hlam : ∀ F : ℝ → ℝ, ∀ a : ℝ, Continuous F → 0 ≤ a →
      lam * ∫ u in (0 : ℝ)..a, F u ^ 2 ≤ edgeForm s m γ δ L F a)
    {g : ℝ → ℝ} (hg : Continuous g) (heven : ∀ t, g (-t) = g t) :
    (Real.exp (δ * L) * lam / 2 - (∑ i ∈ s, m i) * (2 * Real.exp (δ * L / 2) + 1) / (4 * δ))
        * ∫ t in -(L / 2)..L / 2, g t ^ 2
      ≤ ∑ i ∈ s, m i * (Cvs.StepA.OneZeroParitySectors.ctr L g ((γ i : ℂ) - δ * Complex.I) ^ 2).re := by
  set F : ℝ → ℝ := fun u => g (u - L / 2) with hFdef
  have hF : Continuous F := hg.comp (continuous_sub_right _)
  have hL2 : 0 ≤ L / 2 := by linarith
  set A := ∫ u in (0 : ℝ)..L / 2, F u ^ 2 with hA
  set c := (2 * Real.exp (δ * L / 2) + 1) / (2 * δ) with hc
  have hterm : ∀ i ∈ s, m i * (Real.exp (δ * L) * (Complex.exp (γ i * L * Complex.I)
        * edgePair δ (γ i) F (L / 2) ^ 2).re) - m i * (A * c)
      ≤ m i * (Cvs.StepA.OneZeroParitySectors.ctr L g ((γ i : ℂ) - δ * Complex.I) ^ 2).re := by
    intro i hi
    have h := re_ctr_sq_even_ge hδ (γ i) hL hg heven
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (hm i hi)
    rw [hc, ← mul_div_assoc]
    exact h
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  have hform : ∑ i ∈ s, m i * (Real.exp (δ * L) * (Complex.exp (γ i * L * Complex.I)
        * edgePair δ (γ i) F (L / 2) ^ 2).re)
      = Real.exp (δ * L) * edgeForm s m γ δ L F (L / 2) := by
    unfold edgeForm
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hform] at hsum
  have hlo := mul_le_mul_of_nonneg_left (hlam F (L / 2) hF hL2) (Real.exp_pos (δ * L)).le
  rw [integral_sq_even L hg heven, ← hA]
  have : (Real.exp (δ * L) * lam / 2 - (∑ i ∈ s, m i) * (2 * Real.exp (δ * L / 2) + 1) / (4 * δ))
      * (2 * A) = Real.exp (δ * L) * (lam * A) - (∑ i ∈ s, m i) * (A * c) := by
    rw [hc]; field_simp; ring
  rw [this]
  linarith

include hm in
/-- **The odd block from above, at an edge profile**: for `δ ≥ 0`, continuous `F` vanishing on
`[a, ∞)` with `0 ≤ a`, `2a ≤ L`,
`∑ᵢ mᵢ (−Re(ctr(oddEdge F, γᵢ − iδ)²)) ≤ −e^{δL} edgeForm(F, a) + ∑ᵢ mᵢ oddConst`. -/
theorem odd_block_le {δ : ℝ} (hδ : 0 ≤ δ) {L : ℝ} {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ}
    (ha : 0 ≤ a) (haL : 2 * a ≤ L) (hsupp : ∀ u, a ≤ u → F u = 0) :
    ∑ i ∈ s, m i * -(Cvs.StepA.OneZeroParitySectors.ctr L (oddEdge L F) ((γ i : ℂ) - δ * Complex.I) ^ 2).re
      ≤ -(Real.exp (δ * L) * edgeForm s m γ δ L F a) + ∑ i ∈ s, m i * oddConst δ (γ i) F a := by
  have hL : 0 ≤ L := by linarith
  have hterm : ∀ i ∈ s,
      m i * -(Cvs.StepA.OneZeroParitySectors.ctr L (oddEdge L F) ((γ i : ℂ) - δ * Complex.I) ^ 2).re
        ≤ -(Real.exp (δ * L) * (m i * (Complex.exp (γ i * L * Complex.I)
            * edgePair δ (γ i) F a ^ 2).re)) + m i * oddConst δ (γ i) F a := by
    intro i hi
    have h := neg_re_ctr_sq_oddEdge_le hδ (γ i) hL hF (by linarith) hsupp
    have h2 := mul_le_mul_of_nonneg_left h (hm i hi)
    linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  unfold edgeForm
  rw [Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]

end Block

end Cvs.StepA.Edge.TwoEdgeSplit
