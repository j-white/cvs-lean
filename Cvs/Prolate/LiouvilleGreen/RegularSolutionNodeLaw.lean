import Mathlib
import Cvs.Prolate.LiouvilleGreen.PerturbedPairNodeLaws
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.TopRungZeroSplitHalf
import Cvs.Upstream.SecondOrderOdeEnergyBounds
import Cvs.Upstream.SingularVolterraAsinh

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The node law for the regular prolate solution on `T ≥ 1`

For `y_T = regSol (sqC c) (c²T)`, a zero `t ∈ [0, t₁]` puts `cI_t(T)/π + ¼ + Ecorr(cA(T))/π` within
`(arcsin(e^{3.6/x₁} − 1 + ρ) + 1/(4x₁))/π ≤ C ln c/c` of `ℤ`, given Dunster's Liouville frame, the Coulomb comparison
function and variation of constants at the regular singular point; `y ≥ 1` on `[√τ, 1]`; and Theorems A\*, P, C as
statements about `y`.
-/
noncomputable section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace Cvs.Prolate.LiouvilleGreen.RegularSolutionNodeLaw

open Cvs.Prolate.RegularSolutionEdge (regSol sqC)

/-! ### The objects -/

/-- The Coulomb potential `Q_κ(x) = ¼ + κ/x + 1/(4x²)`. -/
def coulombQ (κ x : ℝ) : ℝ := 1 / 4 + κ / x + 1 / (4 * x ^ 2)

/-- The Coulomb phase `Φ_κ(x) = ∫₀ˣ √(¼ + κ/v) dv`. -/
def coulombPhase (κ x : ℝ) : ℝ := ∫ v in (0 : ℝ)..x, √(1 / 4 + κ / v)

/-- The prolate phase integral `I_t(T) = ∫_t^{min(1, √T)} √((T − τ²)/(1 − τ²)) dτ`. -/
def phaseI (T t : ℝ) : ℝ := ∫ τ in t..min 1 √T, √((T - τ ^ 2) / (1 - τ ^ 2))

/-- The complete elliptic integral of the first kind, `K(m) = ∫₀^{π/2} (1 − m sin²θ)^{−1/2} dθ`. -/
def ellipK (m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..π / 2, (√(1 - m * sin θ ^ 2))⁻¹

/-- The Whittaker parameter `A(T) = (1/π)∫_T^1 K(1 − τ) dτ`. -/
def whitA (T : ℝ) : ℝ := 1 / π * ∫ τ in T..1, ellipK (1 - τ)

/-- Binet's kernel `h(s) = s⁻¹(1/(2 sinh(s/2)) − 1/s)`. -/
def binetKernel (s : ℝ) : ℝ := (1 / (2 * sinh (s / 2)) - 1 / s) / s

/-- The Stirling phase correction in Binet form, `Ecorr(y) = −∫₀^∞ h(s) sin(ys/2) ds`. -/
def ecorr (y : ℝ) : ℝ := -∫ s in Ioi 0, binetKernel s * sin (y * s / 2)

/-- The lower physical endpoint `2c(1 − t₁)²/(√(1 − t₁ + Λ′) + √Λ′)²`, `Λ′ = |A(1 + A)|`. -/
def xLowR (A t₁ c : ℝ) : ℝ :=
  2 * c * ((1 - t₁) ^ 2 / (√(1 - t₁ + |whitA (1 + A)|) + √|whitA (1 + A)|) ^ 2)

/-- The upper physical endpoint `πc√(1 + A)`. -/
def xUpR (A c : ℝ) : ℝ := π * c * √(1 + A)

/-- The amplitude bound `B₁ = (2/√π)e^{0.9}`. -/
def B₁ : ℝ := 2 / √π * exp 0.9

/-- The Volterra error `ρ = √(2π)(Ψ/2c)(4 + B₁ ln(x/4))e^{(Ψ/c) asinh x}`. -/
def rhoR (Ψ c x : ℝ) : ℝ := √(2 * π) * (Ψ / (2 * c) * (4 + B₁ * log (x / 4))) * exp (Ψ / c * arsinh x)

/-! ### Elementary facts -/

/-- `Ecorr` is odd. -/
theorem ecorr_neg (y : ℝ) : ecorr (-y) = -ecorr y := by
  unfold ecorr
  rw [neg_neg, ← MeasureTheory.integral_neg]
  congr 1; ext s
  rw [show -y * s / 2 = -(y * s / 2) by ring, sin_neg]; ring

/-- `K(m) ≥ 0`. -/
theorem ellipK_nonneg (m : ℝ) : 0 ≤ ellipK m :=
  integral_nonneg (by linarith [pi_pos]) fun _ _ => inv_nonneg.mpr (sqrt_nonneg _)

/-- `A(T) ≤ 0` for `T ≥ 1`. -/
theorem whitA_nonpos {T : ℝ} (hT : 1 ≤ T) : whitA T ≤ 0 := by
  unfold whitA
  rw [integral_symm]
  have : 0 ≤ ∫ τ in (1 : ℝ)..T, ellipK (1 - τ) := integral_nonneg hT fun τ _ => ellipK_nonneg _
  have hp : 0 < 1 / π := by positivity
  nlinarith

/-- `Q_κ ≥ ¼` for `κ ≥ 0`. -/
theorem quarter_le_coulombQ {κ x : ℝ} (hκ : 0 ≤ κ) (hx : 0 < x) : 1 / 4 ≤ coulombQ κ x := by
  unfold coulombQ
  have : 0 ≤ κ / x := div_nonneg hκ hx.le
  have : 0 ≤ 1 / (4 * x ^ 2) := by positivity
  linarith

/-- `Q_κ' = −κ/x² − 1/(2x³)`. -/
theorem hasDerivAt_coulombQ (κ : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (coulombQ κ) (-(κ / x ^ 2) - 1 / (2 * x ^ 3)) x := by
  have h1 : HasDerivAt (fun y => κ / y) (-(κ / x ^ 2)) x := by
    have := (hasDerivAt_inv hx).const_mul κ
    refine this.congr_deriv ?_
    field_simp
  have h2 : HasDerivAt (fun y => 1 / (4 * y ^ 2)) (-(1 / (2 * x ^ 3))) x := by
    have := ((hasDerivAt_pow 2 x).const_mul 4).inv (by positivity)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => by simp [one_div])
    field_simp
    ring
  have := (h1.const_add (1 / 4)).add h2
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [coulombQ]

/-- `Q_κ^{−1/4} ≤ √2` for `κ ≥ 0`. -/
theorem inv_sqrt_sqrt_coulombQ_le {κ x : ℝ} (hκ : 0 ≤ κ) (hx : 0 < x) : 1 / √(√(coulombQ κ x)) ≤ √2 := by
  have hQ := quarter_le_coulombQ hκ hx
  have hs : 1 / 2 ≤ √(coulombQ κ x) := by
    rw [show (1 : ℝ) / 2 = √(1 / 4) by rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hQ
  have hss : 1 / √2 ≤ √(√(coulombQ κ x)) := by
    rw [show 1 / √2 = √(1 / 2) by rw [sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), sqrt_one]]
    exact sqrt_le_sqrt hs
  have h2 : 0 < √2 := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hss)]
  rw [div_le_iff₀ h2] at hss
  linarith

/-- **The `Φ` integral**: if `f ≤ Cv^{−1/2}` on `(0, 4)` and `f ≤ CB/v` on `(4, x)`, then
`∫₀ˣ f ≤ C(4 + B ln(x/4))`. -/
theorem integral_le_phiStar {f : ℝ → ℝ} {C B x : ℝ} (hx : 4 ≤ x) (hf : IntervalIntegrable f volume 0 x)
    (h1 : ∀ v ∈ Ioo (0 : ℝ) 4, f v ≤ C * v ^ (-(1 / 2) : ℝ)) (h2 : ∀ v ∈ Ioo 4 x, f v ≤ C * B * v⁻¹) :
    ∫ v in (0 : ℝ)..x, f v ≤ C * (4 + B * log (x / 4)) := by
  have hf1 : IntervalIntegrable f volume 0 4 := hf.mono_set (by
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl hx)
  have hf2 : IntervalIntegrable f volume 4 x := hf.mono_set (by
    rw [uIcc_of_le hx, uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by norm_num) le_rfl)
  rw [← integral_add_adjacent_intervals hf1 hf2]
  have i1 : ∫ v in (0 : ℝ)..4, f v ≤ C * 4 := by
    have hr : IntervalIntegrable (fun v : ℝ => C * v ^ (-(1 / 2) : ℝ)) volume 0 4 :=
      (intervalIntegrable_rpow' (by norm_num)).const_mul C
    refine (integral_mono_on_of_le_Ioo (by norm_num) hf1 hr h1).trans_eq ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num, zero_rpow (by norm_num), sub_zero,
      show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← rpow_mul (by norm_num)]
    norm_num
  have i2 : ∫ v in (4 : ℝ)..x, f v ≤ C * B * log (x / 4) := by
    have hr : IntervalIntegrable (fun v : ℝ => C * B * v⁻¹) volume 4 x :=
      ((continuousOn_inv₀.mono fun v hv => by
        rw [uIcc_of_le hx] at hv; exact (show (0 : ℝ) < v by linarith [hv.1]).ne').intervalIntegrable).const_mul _
    refine (integral_mono_on_of_le_Ioo hx hf2 hr h2).trans_eq ?_
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) (by linarith)]
  linarith

/-! ### The inputs -/

/-- **Dunster's Liouville frame on `T ≥ 1`** (Dunster 1994 (2.1)–(2.10), `m = 0`, H7): a recessive solution of
`Y'' + (Q_κ − p)Y = 0`, `κ = c|A(T)|/2`, `|p| ≤ Ψ/(2cx)`, vanishing at `x(t)` for each zero `t ∈ [0, t₁]` of `y_T`,
with `Φ_κ(x(t)) = cI_t(T)` and `x_low ≤ x(t) ≤ x(0) ≤ x_up`. -/
def DunsterFrameR (A t₁ Ψ c₀ : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → c₀ ≤ c → ∀ T ∈ Icc 1 (1 + A), ∃ X Y Y₁ p : ℝ → ℝ,
    (∀ t ∈ Icc 0 t₁, xLowR A t₁ c ≤ X t ∧ X t ≤ X 0) ∧ X 0 ≤ xUpR A c ∧
    (∀ t ∈ Icc 0 t₁, regSol (sqC c) (c ^ 2 * T) t = 0 → Y (X t) = 0) ∧
    (∀ t ∈ Icc 0 t₁, coulombPhase (c * |whitA T| / 2) (X t) = c * phaseI T t) ∧
    (∀ x ∈ Ioc 0 (X 0), HasDerivAt Y (Y₁ x) x ∧
      HasDerivAt Y₁ (-((coulombQ (c * |whitA T| / 2) x - p x) * Y x)) x) ∧
    ContinuousOn p (Ioc 0 (X 0)) ∧ (∀ x ∈ Ioc 0 (X 0), |p x| ≤ Ψ / (2 * c) / x) ∧
    (∃ C, ∀ x ∈ Ioc 0 (X 0), |Y x| ≤ C * √x) ∧ ∃ x ∈ Ioc 0 (X 0), Y x ≠ 0

/-- **The Coulomb comparison function** (DLMF 13.14.2, 13.2.39, 5.4.4, 13.7.2 and Liouville–Green): for `κ ≥ 0`,
`V₀ = √x G`, `xG'' + G' + (κ + x/4)G = 0`, `G(0⁺) = 1`, `G'(0⁺) = −κ`, solves `V'' + Q_κV = 0`, and for `x ≥ 1`
`V₀ = (N/√2)Q_κ^{−1/4}(cos ϑ + ε₀)`, `|ε₀| ≤ e^{3.6/x} − 1`, `ϑ = Φ_κ − Ecorr(2κ) − π/4 + D`, `−1/(4x) ≤ D ≤ 0`. -/
def CoulombLG : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ (V₀ V₀' G G₁ G₂ ϑ ε₀ D : ℝ → ℝ) (N : ℝ),
    (∀ x, 0 < x → V₀ x = √x * G x) ∧
    (∀ x, 0 < x → HasDerivAt G (G₁ x) x ∧ HasDerivAt G₁ (G₂ x) x ∧
      x * G₂ x + G₁ x + (κ + x / 4) * G x = 0) ∧
    Tendsto G (𝓝[>] 0) (𝓝 1) ∧ Tendsto G₁ (𝓝[>] 0) (𝓝 (-κ)) ∧
    (∀ x, 0 < x → HasDerivAt V₀ (V₀' x) x ∧ HasDerivAt V₀' (-(coulombQ κ x * V₀ x)) x) ∧
    √(2 / π) ≤ N ∧ N ≤ 2 / √π ∧
    ∀ x, 1 ≤ x → V₀ x = N / √2 * (1 / √(√(coulombQ κ x))) * (cos (ϑ x) + ε₀ x) ∧
      |ε₀ x| ≤ exp (3.6 / x) - 1 ∧ ϑ x = coulombPhase κ x - ecorr (2 * κ) - π / 4 + D x ∧
      -(1 / (4 * x)) ≤ D x ∧ D x ≤ 0

/-- **Variation of constants at the regular singular point `0`** (indicial exponents `½, ½`): a nonzero `O(√x)`
solution of `Y'' + (Q_κ − p)Y = 0`, `p` continuous, `|p| ≤ P̄/x`, is a nonzero multiple of `V₀ + e`,
`e = ∫₀ˣ K(x, v)p(v)(V₀ + e)(v)dv` with `K(·, v)` the kernel solution, for a nonzero solution `|V₀| ≤ √x`. -/
def VariationOfConstants : Prop :=
  ∀ (κ X Pb C : ℝ) (V₀ V₀' Y Y₁ p : ℝ → ℝ), 0 ≤ κ → 0 < X →
    (∀ x ∈ Ioc 0 X, HasDerivAt V₀ (V₀' x) x ∧ HasDerivAt V₀' (-(coulombQ κ x * V₀ x)) x) →
    (∀ x ∈ Ioc 0 X, |V₀ x| ≤ √x) → (∃ x ∈ Ioc 0 X, V₀ x ≠ 0) →
    (∀ x ∈ Ioc 0 X, HasDerivAt Y (Y₁ x) x ∧ HasDerivAt Y₁ (-((coulombQ κ x - p x) * Y x)) x) →
    ContinuousOn p (Ioc 0 X) → (∀ x ∈ Ioc 0 X, |p x| ≤ Pb / x) → (∀ x ∈ Ioc 0 X, |Y x| ≤ C * √x) →
    (∃ x ∈ Ioc 0 X, Y x ≠ 0) →
    ∃ μ : ℝ, μ ≠ 0 ∧ ∃ (e : ℝ → ℝ) (K K₁ : ℝ → ℝ → ℝ),
      (∀ x ∈ Ioc 0 X, μ * Y x = V₀ x + e x) ∧
      (∀ v ∈ Ioc 0 X, K v v = 0 ∧ K₁ v v = 1 ∧ ∀ x ∈ Icc v X,
        HasDerivAt (fun y => K y v) (K₁ x v) x ∧ HasDerivAt (fun y => K₁ y v) (-(coulombQ κ x * K x v)) x) ∧
      (∀ x ∈ Ioc 0 X, e x = ∫ v in (0 : ℝ)..x, K x v * p v * (V₀ v + e v)) ∧
      IntervalIntegrable (fun v => |p v| * |V₀ v|) volume 0 X ∧
      IntervalIntegrable (fun v => |p v| * |e v|) volume 0 X ∧
      IntervalIntegrable (fun v => |p v| * (1 / √(coulombQ κ v))) volume 0 X ∧
      ContinuousOn (fun v => |p v| * |e v|) (Ioo 0 X)

/-! ### The node law -/

/-- **Theorem R, node law**: under the three inputs, for `c > 0`, `T ∈ [1, 1 + A]`, `Ψ ≥ 0` and `x_low ≥ 4`, every zero
`t ∈ [0, t₁]` of `y_T` puts `cI_t(T)/π + ¼ + Ecorr(cA(T))/π` within
`(arcsin(e^{3.6/x_low} − 1 + ρ(x_up)) + 1/(4x_low))/π` of `ℤ`. -/
theorem nodeLaw_of_frame {A t₁ Ψ c₀ : ℝ} (hF : DunsterFrameR A t₁ Ψ c₀) (hC : CoulombLG) (hV : VariationOfConstants)
    {c T : ℝ} (hc : 0 < c) (hc₀ : c₀ ≤ c) (hT : T ∈ Icc 1 (1 + A)) (hΨ : 0 ≤ Ψ) (hlow : 4 ≤ xLowR A t₁ c)
    {t : ℝ} (ht : t ∈ Icc 0 t₁) (h0 : regSol (sqC c) (c ^ 2 * T) t = 0) :
    ∃ n : ℤ, |c * phaseI T t / π + 1 / 4 + ecorr (c * whitA T) / π - n| ≤
      (arcsin (exp (3.6 / xLowR A t₁ c) - 1 + rhoR Ψ c (xUpR A c)) + 1 / (4 * xLowR A t₁ c)) / π := by
  obtain ⟨X, Y, Y₁, p, hXb, hX0, hzero, hphase, hode, hpc, hpb, ⟨CY, hCY⟩, hYne⟩ := hF c hc hc₀ T hT
  set κ := c * |whitA T| / 2 with hκdef
  have hκ : 0 ≤ κ := by positivity
  obtain ⟨V₀, V₀', G, G₁, G₂, ϑ, ε₀, D, N, hVG, hGode, hG0, hG₁0, hV₀d, hN1, hN2, hLG⟩ := hC κ hκ
  set xl := xLowR A t₁ c
  set X₀ := X 0
  have ht0 : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  have hX₀ : 0 < X₀ := lt_of_lt_of_le (by linarith) (hXb 0 ht0).1
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN1
  -- `|V₀| ≤ √x`
  have hV₀sq : ∀ x, 0 < x → |V₀ x| ≤ √x := by
    intro x hx
    rw [hVG x hx, abs_mul, abs_of_nonneg (sqrt_nonneg _)]
    have := Cvs.Upstream.SecondOrderOdeEnergyBounds.abs_le_one_of_coulomb hκ (fun y hy => (hGode y hy).1)
      (fun y hy => (hGode y hy).2.1) (fun y hy => (hGode y hy).2.2) hG0 hG₁0 hx
    nlinarith [sqrt_nonneg x]
  -- `V₀ ≢ 0` near `0`
  have hV₀ne : ∃ x ∈ Ioc 0 X₀, V₀ x ≠ 0 := by
    have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), 1 / 2 < G y ∧ y ∈ Ioo 0 X₀ :=
      (hG0.eventually (lt_mem_nhds (by norm_num))).and (Ioo_mem_nhdsGT hX₀)
    obtain ⟨y, hy1, hy2⟩ := hev.exists
    refine ⟨y, ⟨hy2.1, hy2.2.le⟩, ?_⟩
    rw [hVG y hy2.1]
    exact mul_ne_zero (sqrt_pos.mpr hy2.1).ne' (by linarith)
  obtain ⟨μ, hμ, e, K, K₁, hrep, hK, hvol, hiV, hie, hiP, hce⟩ :=
    hV κ X₀ (Ψ / (2 * c)) CY V₀ V₀' Y Y₁ p hκ hX₀ (fun x hx => hV₀d x hx.1) (fun x hx => hV₀sq x hx.1)
      hV₀ne hode hpc hpb hCY hYne
  -- the zero
  set x := X t with hxdef
  have hxl : xl ≤ x := (hXb t ht).1
  have hxX : x ≤ X₀ := (hXb t ht).2
  have hx0 : 0 < x := by linarith
  have hx4 : 4 ≤ x := le_trans hlow hxl
  have hsum : V₀ x + e x = 0 := by rw [← hrep x ⟨hx0, hxX⟩, hzero t ht h0, mul_zero]
  -- kernel bound
  have hQd : ∀ y, 0 < y → HasDerivAt (coulombQ κ) (-(κ / y ^ 2) - 1 / (2 * y ^ 3)) y :=
    fun y hy => hasDerivAt_coulombQ κ hy.ne'
  have hKb : ∀ v ∈ Ioc 0 X₀, ∀ w ∈ Icc v X₀, |K w v| ≤ 1 / √(coulombQ κ w) := by
    intro v hv w hw
    obtain ⟨hKv, hK₁v, hKd⟩ := hK v hv
    have hv0 : 0 < v := hv.1
    exact (Cvs.Upstream.SecondOrderOdeEnergyBounds.abs_kernel_le_of_antitone (g := fun y => K y v) (g₁ := fun y => K₁ y v)
      (Q := coulombQ κ) (Q₁ := fun y => -(κ / y ^ 2) - 1 / (2 * y ^ 3)) (a := v) (b := X₀)
      (fun y hy => (hKd y hy).1) (fun y hy => (hKd y hy).2) (fun y hy => hQd y (by linarith [hy.1]))
      (fun y hy => by
        have hy0 : 0 < y := by linarith [hy.1]
        have : 0 ≤ κ / y ^ 2 := by positivity
        have : 0 ≤ 1 / (2 * y ^ 3) := by positivity
        linarith)
      (fun y hy => lt_of_lt_of_le (by norm_num) (quarter_le_coulombQ hκ (by linarith [hy.1]))) hKv hK₁v w hw).1
  -- integrability on subintervals
  have hsub : ∀ y ∈ Icc 0 X₀, uIcc 0 y ⊆ uIcc 0 X₀ := fun y hy => by
    rw [uIcc_of_le hy.1, uIcc_of_le hX₀.le]; exact Icc_subset_Icc le_rfl hy.2
  have one_mul_fun : ∀ f : ℝ → ℝ, (fun v => (fun _ : ℝ => (1 : ℝ)) v * |p v| * f v) = fun v => |p v| * f v :=
    fun f => by funext v; ring
  -- the Volterra bound at every point of `(0, X₀]`
  have hbd : ∀ y ∈ Ioc 0 X₀, |e y| ≤ (1 / √(coulombQ κ y)) *
      ((∫ v in (0 : ℝ)..y, (fun _ : ℝ => (1 : ℝ)) v * |p v| * |V₀ v|) +
        ∫ v in (0 : ℝ)..y, (fun _ : ℝ => (1 : ℝ)) v * |p v| * |e v|) := by
    intro y hy
    refine Cvs.Upstream.SingularVolterraAsinh.abs_le_of_volterra_eq (K := K) (R := fun _ => 1)
      (P := fun y => 1 / √(coulombQ κ y)) hy.1.le
      (fun v hv => by rw [mul_one]; exact hKb v ⟨hv.1, hv.2.trans hy.2⟩ y ⟨hv.2, hy.2⟩) ?_ ?_ ?_
    · rw [one_mul_fun]; exact hiV.mono_set (hsub y ⟨hy.1.le, hy.2⟩)
    · rw [one_mul_fun]; exact hie.mono_set (hsub y ⟨hy.1.le, hy.2⟩)
    · rw [hvol y hy]
  have hsumle := Cvs.Upstream.SingularVolterraAsinh.volterra_sum_le (F := V₀) (e := e) (p := p)
    (P := fun y => 1 / √(coulombQ κ y)) (R := fun _ => 1) hx0.le (fun _ _ => zero_le_one)
    (fun _ _ => by positivity)
    (by rw [one_mul_fun]; exact hiV.mono_set (hsub x ⟨hx0.le, hxX⟩))
    (by rw [one_mul_fun]; exact hie.mono_set (hsub x ⟨hx0.le, hxX⟩))
    (by rw [one_mul_fun]; exact hiP.mono_set (hsub x ⟨hx0.le, hxX⟩))
    (by rw [one_mul_fun]; exact hce.mono (Ioo_subset_Ioo le_rfl hxX))
    (by
      rw [one_mul_fun]
      refine ContinuousOn.mul (continuous_abs.comp_continuousOn (hpc.mono fun v hv => ⟨hv.1, hv.2.le.trans hxX⟩))
        (ContinuousOn.div continuousOn_const (ContinuousOn.sqrt ?_) fun v hv => ?_)
      · exact fun v hv => (hQd v hv.1).continuousAt.continuousWithinAt
      · exact (sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (quarter_le_coulombQ hκ hv.1))).ne')
    (fun y hy => hbd y ⟨hy.1, hy.2.le.trans hxX⟩)
  simp only [one_mul_fun] at hsumle hbd
  set Φx := ∫ v in (0 : ℝ)..x, |p v| * |V₀ v|
  set Λx := ∫ v in (0 : ℝ)..x, |p v| * (1 / √(coulombQ κ v))
  set Bx := Φx * exp Λx
  have hQx := quarter_le_coulombQ hκ hx0
  have hΦnn : 0 ≤ Φx := integral_nonneg hx0.le fun v _ => by positivity
  have hBx : 0 ≤ Bx := by positivity
  have hex : |e x| ≤ Bx / √(coulombQ κ x) := by
    have h1 := hbd x ⟨hx0, hxX⟩
    have h2 : 0 ≤ 1 / √(coulombQ κ x) := by positivity
    calc |e x| ≤ 1 / √(coulombQ κ x) * (Φx + ∫ v in (0 : ℝ)..x, |p v| * |e v|) := h1
      _ ≤ 1 / √(coulombQ κ x) * Bx := mul_le_mul_of_nonneg_left hsumle h2
      _ = Bx / √(coulombQ κ x) := by ring
  have hnorm := (Cvs.Prolate.LiouvilleGreen.PerturbedPairNodeLaws.normalise_volterra (e₁ := 0) hQx hNpos hBx hex (by simpa using hBx)).1
  obtain ⟨hV₀x, hε₀x, hϑx, hD1, hD2⟩ := hLG x (by linarith)
  obtain ⟨n, hn⟩ := Cvs.Prolate.LiouvilleGreen.PerturbedPairNodeLaws.exists_int_of_zero (div_pos hNpos (by positivity))
    (by positivity) hV₀x hε₀x hnorm hϑx hsum
  refine ⟨n, ?_⟩
  -- identify the phase and the correction
  have hA : whitA T ≤ 0 := whitA_nonpos hT.1
  have hE : -(ecorr (2 * κ) / π) = ecorr (c * whitA T) / π := by
    rw [hκdef, show 2 * (c * |whitA T| / 2) = -(c * whitA T) by rw [abs_of_nonpos hA]; ring, ecorr_neg]; ring
  have hΦ : coulombPhase κ x = c * phaseI T t := hphase t ht
  rw [hΦ, sub_eq_add_neg (c * phaseI T t / π + 1 / 4), hE] at hn
  refine hn.trans (div_le_div_of_nonneg_right ?_ pi_pos.le)
  -- the error terms
  have hDb : |D x| ≤ 1 / (4 * xl) := by
    rw [abs_le]
    have : 1 / (4 * x) ≤ 1 / (4 * xl) := one_div_le_one_div_of_le (by linarith) (by linarith)
    constructor <;> linarith
  refine add_le_add (arcsin_le_arcsin (add_le_add ?_ ?_)) hDb
  · have : 3.6 / x ≤ 3.6 / xl := div_le_div_of_nonneg_left (by norm_num) (by linarith) hxl
    linarith [exp_le_exp.mpr this]
  · -- `2B/N ≤ ρ`
    have hXup : x ≤ xUpR A c := hxX.trans hX0
    have h2N : 2 / N ≤ √(2 * π) := by
      rw [div_le_iff₀ hNpos]
      have hsp : √(2 / π) * √(2 * π) = 2 := by
        rw [← sqrt_mul (by positivity), show 2 / π * (2 * π) = 2 ^ 2 by field_simp,
          sqrt_sq (by norm_num)]
      nlinarith [sqrt_nonneg (2 * π)]
    have hΛ : Λx ≤ Ψ / c * arsinh (xUpR A c) := by
      refine (Cvs.Upstream.SingularVolterraAsinh.integral_le_mul_arsinh hx0.le (hiP.mono_set (hsub x ⟨hx0.le, hxX⟩))
        fun v hv => ?_).trans (mul_le_mul_of_nonneg_left (arsinh_le_arsinh.mpr hXup) (by positivity))
      have := Cvs.Upstream.SingularVolterraAsinh.inv_sqrt_coulombQ_mul_le (pv := p v) hκ hv.1 hc
        (by rw [show Ψ / (2 * c * v) = Ψ / (2 * c) / v by field_simp]; exact hpb v ⟨hv.1, hv.2.le.trans hxX⟩)
      unfold coulombQ
      rw [one_div]; linarith
    have hΦb : Φx ≤ Ψ / (2 * c) * (4 + B₁ * log (xUpR A c / 4)) := by
      refine (integral_le_phiStar (C := Ψ / (2 * c)) (B := B₁) hx4 (hiV.mono_set (hsub x ⟨hx0.le, hxX⟩))
        (fun v hv => ?_) (fun v hv => ?_)).trans ?_
      · have hp := hpb v ⟨hv.1, by linarith [hv.2]⟩
        have hV := hV₀sq v hv.1
        have e1 : Ψ / (2 * c) * v ^ (-(1 / 2) : ℝ) = Ψ / (2 * c) / v * √v := by
          rw [rpow_neg hv.1.le, ← sqrt_eq_rpow]
          have hs := sq_sqrt hv.1.le
          have hs0 : 0 < √v := sqrt_pos.mpr hv.1
          have hv0 : v ≠ 0 := hv.1.ne'
          field_simp
          rw [hs]
        rw [e1]
        exact mul_le_mul hp hV (abs_nonneg _) (div_nonneg (by positivity) hv.1.le)
      · have hv1 : 1 ≤ v := by linarith [hv.1]
        have hp := hpb v ⟨by linarith [hv.1], hv.2.le.trans hxX⟩
        obtain ⟨hV₀v, hε₀v, -, -, -⟩ := hLG v hv1
        have hq := inv_sqrt_sqrt_coulombQ_le hκ (by linarith [hv.1] : (0 : ℝ) < v)
        have hcos : |cos (ϑ v) + ε₀ v| ≤ exp 0.9 := by
          have : 3.6 / v ≤ 0.9 := by rw [div_le_iff₀ (by linarith [hv.1])]; linarith [hv.1]
          have := exp_le_exp.mpr this
          linarith [abs_add_le (cos (ϑ v)) (ε₀ v), abs_cos_le_one (ϑ v)]
        have hVb : |V₀ v| ≤ B₁ := by
          rw [hV₀v, abs_mul, abs_mul, abs_of_pos (div_pos hNpos (by positivity)),
            abs_of_nonneg (by positivity)]
          have h1 : N / √2 * (1 / √(√(coulombQ κ v))) ≤ 2 / √π := by
            calc N / √2 * (1 / √(√(coulombQ κ v))) ≤ N / √2 * √2 :=
                  mul_le_mul_of_nonneg_left hq (by positivity)
              _ = N := by field_simp
              _ ≤ 2 / √π := hN2
          calc N / √2 * (1 / √(√(coulombQ κ v))) * |cos (ϑ v) + ε₀ v| ≤ 2 / √π * exp 0.9 :=
                mul_le_mul h1 hcos (abs_nonneg _) (by positivity)
            _ = B₁ := rfl
        calc |p v| * |V₀ v| ≤ Ψ / (2 * c) / v * B₁ := mul_le_mul hp hVb (abs_nonneg _) (by positivity)
          _ = Ψ / (2 * c) * B₁ * v⁻¹ := by ring
      · have hB₁ : 0 ≤ B₁ := by unfold B₁; positivity
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hB₁)) (by positivity)
        exact log_le_log (by linarith) (by linarith)
    have hρ : 2 * Bx / N ≤ rhoR Ψ c (xUpR A c) := by
      unfold rhoR
      have hΦ' : 0 ≤ Ψ / (2 * c) * (4 + B₁ * log (xUpR A c / 4)) := le_trans hΦnn hΦb
      calc 2 * Bx / N = 2 / N * (Φx * exp Λx) := by ring
        _ ≤ √(2 * π) * (Ψ / (2 * c) * (4 + B₁ * log (xUpR A c / 4)) * exp (Ψ / c * arsinh (xUpR A c))) :=
          mul_le_mul h2N (mul_le_mul hΦb (exp_le_exp.mpr hΛ) (exp_pos _).le hΦ') (by positivity) (by positivity)
        _ = _ := by ring
    exact hρ

/-! ### No zeros in the forbidden zone (Lemma C1) -/

/-- **Lemma C1**: the regular solution `y = regSol (sqC c) (c²τ)` has `y ≥ 1` on `[√τ, 1]`. -/
theorem one_le_regSol {c τ : ℝ} :
    ∀ ξ ∈ Icc √τ 1, 1 ≤ regSol (sqC c) (c ^ 2 * τ) ξ := by
  set χ := c ^ 2 * τ
  set y := regSol (sqC c) χ
  have hsτ : 0 ≤ √τ := sqrt_nonneg τ
  have hgt : ∀ ξ ∈ Icc √τ 1, -1 < ξ := fun ξ hξ => by linarith [hξ.1]
  have hcont : ContinuousOn y (Icc √τ 1) := fun ξ hξ =>
    (Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regSol (sqC c) χ (hgt ξ hξ)).continuousAt.continuousWithinAt
  have hy1 : y 1 = 1 := Cvs.Prolate.RegularSolutionEdge.regSol_one _ _
  -- the integrand `(c²s² − χ)y(s)` is nonnegative where `y ≥ 0` and `s ≥ √τ`
  have hq : ∀ s, √τ ≤ s → 0 ≤ sqC c s - χ := by
    intro s hs
    have : τ ≤ s ^ 2 := by
      exact (sqrt_le_left (hsτ.trans hs)).mp hs
    show 0 ≤ c ^ 2 * s ^ 2 - c ^ 2 * τ
    nlinarith [sq_nonneg c]
  -- `y' ≤ 0` at `ξ ∈ [√τ, 1)` when `y ≥ 0` on `[ξ, 1]`
  have hderiv : ∀ ξ ∈ Ico √τ 1, (∀ s ∈ Icc ξ 1, 0 ≤ y s) →
      Cvs.Prolate.RegularSolutionEdge.regV (sqC c) χ ξ ≤ 0 := by
    intro ξ hξ hpos
    have hξ1 : -1 < ξ := by linarith [hξ.1]
    have h := Cvs.Prolate.RegularSolutionEdge.pP_mul_regV (sqC c) χ hξ1
    have hU : 0 ≤ Cvs.Prolate.RegularSolutionEdge.regU (sqC c) χ ξ := by
      unfold Cvs.Prolate.RegularSolutionEdge.regU
      rw [integral_symm, neg_neg]
      exact integral_nonneg hξ.2.le fun s hs => mul_nonneg (hq s (hξ.1.trans hs.1)) (hpos s hs)
    have hp : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP ξ < 0 := by
      unfold Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP; nlinarith [hξ.2, hξ.1]
    by_contra hcon
    push Not at hcon
    have : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP ξ * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) χ ξ < 0 := mul_neg_of_neg_of_pos hp hcon
    linarith
  -- `y > 0` on `[√τ, 1]`
  have hpos : ∀ ξ ∈ Icc √τ 1, 0 < y ξ := by
    by_contra hcon
    push Not at hcon
    set S := Icc √τ 1 ∩ y ⁻¹' Iic 0
    have hSne : S.Nonempty := by obtain ⟨ξ, hξ, h⟩ := hcon; exact ⟨ξ, hξ, h⟩
    have hScl : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSbdd : BddAbove S := ⟨1, fun ξ hξ => hξ.1.2⟩
    set s₀ := sSup S
    have hs₀ : s₀ ∈ S := hScl.csSup_mem hSne hSbdd
    have hs₀1 : s₀ < 1 := by
      rcases eq_or_lt_of_le hs₀.1.2 with h | h
      · have : y s₀ ≤ 0 := hs₀.2
        rw [h, hy1] at this; norm_num at this
      · exact h
    have hright : ∀ s ∈ Ioc s₀ 1, 0 < y s := by
      intro s hs
      by_contra h
      push Not at h
      have : s ≤ s₀ := le_csSup hSbdd ⟨⟨hs₀.1.1.trans hs.1.le, hs.2⟩, h⟩
      linarith [hs.1]
    have hmono := Cvs.Upstream.SecondOrderOdeEnergyBounds.le_of_deriv_nonpos hs₀1.le
      (hcont.mono (Icc_subset_Icc hs₀.1.1 le_rfl))
      (fun ξ hξ => Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regSol (sqC c) χ (by linarith [hξ.1, hs₀.1.1]))
      (fun ξ hξ => hderiv ξ ⟨hs₀.1.1.trans hξ.1.le, hξ.2⟩ fun s hs => (hright s ⟨hξ.1.trans_le hs.1, hs.2⟩).le)
    have : y s₀ ≤ 0 := hs₀.2
    rw [hy1] at hmono
    linarith
  intro ξ hξ
  rcases eq_or_lt_of_le hξ.2 with h | h
  · rw [h]; exact hy1.ge
  · have := Cvs.Upstream.SecondOrderOdeEnergyBounds.le_of_deriv_nonpos h.le (hcont.mono (Icc_subset_Icc hξ.1 le_rfl))
      (fun ζ hζ => Cvs.Prolate.RegularSolutionEdge.hasDerivAt_regSol (sqC c) χ (by linarith [hζ.1, hξ.1]))
      (fun ζ hζ => hderiv ζ ⟨hξ.1.trans hζ.1.le, hζ.2⟩ fun s hs => (hpos s ⟨hξ.1.trans (hζ.1.le.trans hs.1),
        hs.2⟩).le)
    rwa [hy1] at this

/-! ### The laws as statements -/

/-- The node law at `(c, T)` on `[0, t₁]` with error `ε`. -/
def NodeLaw (c T t₁ ε : ℝ) : Prop :=
  ∀ t ∈ Icc 0 t₁, regSol (sqC c) (c ^ 2 * T) t = 0 →
    ∃ n : ℤ, |c * phaseI T t / π + 1 / 4 + ecorr (c * whitA T) / π - n| ≤ ε

/-- The Neumann law at `(c, T)` with error `ε`. -/
def NeumannLaw (c T ε : ℝ) : Prop :=
  Cvs.Prolate.RegularSolutionEdge.regV (sqC c) (c ^ 2 * T) 0 = 0 →
    ∃ n : ℤ, |c * phaseI T 0 / π - 1 / 4 + ecorr (c * whitA T) / π - n| ≤ ε

/-- **Theorem A\***: the node and Neumann laws hold with error `C ln c/c`, uniformly in `T ∈ [1 − A, 1 + A]`. -/
def TheoremAStar (A t₁ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ c, c₀ ≤ c → ∀ T ∈ Icc (1 - A) (1 + A),
    NodeLaw c T t₁ (C * log c / c) ∧ NeumannLaw c T (C * log c / c)

/-- **Theorem P**: for `T ≥ 1 + A`, `(cy(½), ¾y'(½)) = R(cos ϑ, κ̃ sin ϑ)` with `R > 0` and
`ϑ ≡ cI_½(T) − π/4 + O(1/(c√T)) (mod 2π)`, `κ̃ = √(¾(T − ¼))(1 + 1/(4c²I_½(T)²))^{1/2}`. -/
def TheoremP (A : ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ c, c₀ ≤ c → ∀ T, 1 + A ≤ T → ∃ R ϑ : ℝ, 0 < R ∧
    c * regSol (sqC c) (c ^ 2 * T) (1 / 2) = R * cos ϑ ∧
    3 / 4 * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) (c ^ 2 * T) (1 / 2) =
      R * (√(3 / 4 * (T - 1 / 4)) * √(1 + 1 / (4 * c ^ 2 * phaseI T (1 / 2) ^ 2))) * sin ϑ ∧
    ∃ m : ℤ, |ϑ - (c * phaseI T (1 / 2) - π / 4) - 2 * π * m| ≤ C / (c * √T)

/-- **Theorem C**: for `c ≥ 1`, `0 < τ ≤ ¾`, `0 ≤ a < √τ`, the number of zeros of `y` in `(a, 1)` is within
`7 + 4/π + (4√2/π)·300^{3/2}` of `(c/π)I_a(τ)`. -/
def TheoremC : Prop :=
  ∀ c, 1 ≤ c → ∀ τ ∈ Ioc (0 : ℝ) (3 / 4), ∀ a ∈ Ico 0 √τ, ∃ k : ℕ,
    Cvs.Prolate.TopRungZeroSplitHalf.ZerosOn (regSol (sqC c) (c ^ 2 * τ)) (Ioo a 1) k ∧
    (∀ k' : ℕ, Cvs.Prolate.TopRungZeroSplitHalf.ZerosOn (regSol (sqC c) (c ^ 2 * τ)) (Ioo a 1) k' → k' ≤ k) ∧
    |(k : ℝ) - c / π * phaseI τ a| ≤ 7 + 4 / π + 4 * √2 / π * 300 ^ (3 / 2 : ℝ)

/-- **Theorem R in `NodeLaw` form**: under the three inputs, `NodeLaw` holds on `T ∈ [1, 1 + A]` with the explicit
error `(arcsin(e^{3.6/x_low} − 1 + ρ(x_up)) + 1/(4x_low))/π`. -/
theorem nodeLaw_R {A t₁ Ψ c₀ : ℝ} (hF : DunsterFrameR A t₁ Ψ c₀) (hC : CoulombLG) (hV : VariationOfConstants)
    {c T : ℝ} (hc : 0 < c) (hc₀ : c₀ ≤ c) (hT : T ∈ Icc 1 (1 + A)) (hΨ : 0 ≤ Ψ) (hlow : 4 ≤ xLowR A t₁ c) :
    NodeLaw c T t₁
      ((arcsin (exp (3.6 / xLowR A t₁ c) - 1 + rhoR Ψ c (xUpR A c)) + 1 / (4 * xLowR A t₁ c)) / π) :=
  fun _ ht h0 => nodeLaw_of_frame hF hC hV hc hc₀ hT hΨ hlow ht h0

/-! ### The rate -/

/-- `NodeLaw` is monotone in the error. -/
theorem NodeLaw.mono {c T t₁ ε ε' : ℝ} (h : NodeLaw c T t₁ ε) (hε : ε ≤ ε') : NodeLaw c T t₁ ε' :=
  fun t ht h0 => (h t ht h0).imp fun _ hn => hn.trans hε

/-- `arcsin z ≤ 2z` for `0 ≤ z ≤ ½`. -/
theorem arcsin_le_two_mul {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2) : arcsin z ≤ 2 * z := by
  rcases h0.eq_or_lt with h | h
  · subst h; simp
  rw [arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩ ⟨by linarith [pi_gt_three], by linarith [pi_gt_three]⟩]
  have := sin_gt_sub_cube (by linarith : (0 : ℝ) < 2 * z)
  have h2 : 0 ≤ z * (1 - 4 / 3 * z ^ 2) := mul_nonneg h0 (by nlinarith)
  nlinarith

/-- `e^y − 1 ≤ 2y` for `0 ≤ y ≤ ½`. -/
theorem exp_sub_one_le_two_mul {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / 2) : exp y - 1 ≤ 2 * y := by
  rcases h0.eq_or_lt with h | h
  · subst h; simp
  have := exp_bound_div_one_sub_of_interval' h (by linarith)
  have hd : 1 / (1 - y) ≤ 1 + 2 * y := by rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- `asinh z ≤ 2z` for `z ≥ 0`. -/
theorem arsinh_le_two_mul {z : ℝ} (hz : 0 ≤ z) : arsinh z ≤ 2 * z := by
  unfold arsinh
  have hs : √(1 + z ^ 2) ≤ 1 + z := by
    rw [sqrt_le_left (by linarith)]; nlinarith
  have := log_le_sub_one_of_pos (add_pos_of_nonneg_of_pos hz (sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + z ^ 2)))
  linarith

/-- **Theorem R, uniform rate**: under the three inputs with `A ≥ 0`, `0 ≤ t₁ < 1`, `Ψ ≥ 0`, there are `C`, `c₀` with
`NodeLaw c T t₁ (C ln c/c)` for every `c ≥ c₀` and `T ∈ [1, 1 + A]`. -/
theorem nodeLaw_R_log {A t₁ Ψ cD : ℝ} (hA : 0 ≤ A) (ht₁ : t₁ ∈ Ico 0 1) (hΨ : 0 ≤ Ψ) (hF : DunsterFrameR A t₁ Ψ cD)
    (hC : CoulombLG) (hV : VariationOfConstants) :
    ∃ C c₀ : ℝ, ∀ c, c₀ ≤ c → ∀ T ∈ Icc 1 (1 + A), NodeLaw c T t₁ (C * log c / c) := by
  set L := |whitA (1 + A)|
  set g := (1 - t₁) ^ 2 / (√(1 - t₁ + L) + √L) ^ 2 with hg
  have hg0 : 0 < g := by
    have h1 : 0 < 1 - t₁ := by linarith [ht₁.2]
    have h2 : 0 < √(1 - t₁ + L) := sqrt_pos.mpr (by positivity)
    positivity
  set u := π * √(1 + A) with hu
  have hu0 : 0 < u := mul_pos pi_pos (sqrt_pos.mpr (by linarith))
  have hxl : ∀ c, xLowR A t₁ c = 2 * c * g := fun c => rfl
  have hxu : ∀ c, xUpR A c = c * u := fun c => by simp only [xUpR, hu]; ring
  have hB₁ : 0 ≤ B₁ := by unfold B₁; positivity
  set K₁ := 4 + B₁ * (1 + |log (u / 4)|) with hK₁def
  have hK₁ : 0 ≤ K₁ := by positivity
  set M := √(2 * π) * (Ψ / 2) * K₁ * exp (2 * Ψ * u) with hMdef
  have hM : 0 ≤ M := by positivity
  set W := 3.6 / g + M with hW
  have hW0 : 0 ≤ W := by positivity
  have hlim := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).eventually
    (ge_mem_nhds (show (0 : ℝ) < 1 / (2 * (W + 1)) by positivity))
  obtain ⟨c₀, hc₀⟩ := (hlim.and ((eventually_ge_atTop (2 / g)).and ((eventually_ge_atTop (3.6 / g)).and
    ((eventually_ge_atTop (exp 1)).and (eventually_ge_atTop (4 / u)))))).exists_forall_of_atTop
  refine ⟨(7.2 / g + 2 * M + 1 / (8 * g)) / π, max c₀ cD, fun c hc T hT => ?_⟩
  obtain ⟨hlc, hc1, hc2, hc3, hc4⟩ := hc₀ c (le_trans (le_max_left _ _) hc)
  simp only [pow_one, one_mul, add_zero] at hlc
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hc1
  have hlog1 : 1 ≤ log c := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) hc3
  have hlow : 4 ≤ xLowR A t₁ c := by
    rw [hxl]; rw [div_le_iff₀ hg0] at hc1; linarith
  refine (nodeLaw_R hF hC hV hcpos (le_trans (le_max_right _ _) hc) hT hΨ hlow).mono ?_
  rw [hxl, hxu]
  -- the three error terms
  have hy : 3.6 / (2 * c * g) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; rw [div_le_iff₀ hg0] at hc2; nlinarith
  have hη : exp (3.6 / (2 * c * g)) - 1 ≤ 3.6 / (c * g) := by
    have := exp_sub_one_le_two_mul (by positivity) hy
    have e : 2 * (3.6 / (2 * c * g)) = 3.6 / (c * g) := by field_simp
    linarith
  have hlogu : 0 ≤ log (c * u / 4) := by
    apply log_nonneg; rw [le_div_iff₀ (by norm_num)]; rw [div_le_iff₀ hu0] at hc4; linarith
  have hρ : rhoR Ψ c (c * u) ≤ M * log c / c := by
    unfold rhoR
    have h1 : exp (Ψ / c * arsinh (c * u)) ≤ exp (2 * Ψ * u) := by
      apply exp_le_exp.mpr
      have := arsinh_le_two_mul (by positivity : (0 : ℝ) ≤ c * u)
      calc Ψ / c * arsinh (c * u) ≤ Ψ / c * (2 * (c * u)) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 2 * Ψ * u := by field_simp
    have h2 : 4 + B₁ * log (c * u / 4) ≤ K₁ * log c := by
      have : log (c * u / 4) ≤ log c * (1 + |log (u / 4)|) := by
        rw [show c * u / 4 = c * (u / 4) by ring, log_mul hcpos.ne' (by positivity)]
        nlinarith [le_abs_self (log (u / 4)), abs_nonneg (log (u / 4))]
      rw [hK₁def]
      nlinarith [mul_le_mul_of_nonneg_left this hB₁]
    have h3 : 0 ≤ 4 + B₁ * log (c * u / 4) := by positivity
    calc √(2 * π) * (Ψ / (2 * c) * (4 + B₁ * log (c * u / 4))) * exp (Ψ / c * arsinh (c * u))
        ≤ √(2 * π) * (Ψ / (2 * c) * (K₁ * log c)) * exp (2 * Ψ * u) := by
          gcongr
      _ = M * log c / c := by rw [hMdef]; field_simp
  have hsmall : exp (3.6 / (2 * c * g)) - 1 + rhoR Ψ c (c * u) ≤ W * (log c / c) := by
    have : 3.6 / (c * g) ≤ 3.6 / g * (log c / c) := by
      rw [show 3.6 / g * (log c / c) = 3.6 * log c / (c * g) by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have e : M * log c / c = M * (log c / c) := by ring
    have e2 : W * (log c / c) = 3.6 / g * (log c / c) + M * (log c / c) := by rw [hW]; ring
    linarith
  have hηnn : 0 ≤ exp (3.6 / (2 * c * g)) - 1 := by
    have h1 := add_one_le_exp (3.6 / (2 * c * g))
    have h2 : 0 ≤ 3.6 / (2 * c * g) := by positivity
    linarith
  have hρnn : 0 ≤ rhoR Ψ c (c * u) := by
    unfold rhoR; have := hlogu; positivity
  have hhalf : W * (log c / c) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hlc hW0
    calc W * (log c / c) ≤ W * (1 / (2 * (W + 1))) := this
      _ ≤ 1 / 2 := by rw [mul_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (W + 1))]; linarith
  have hz2 : exp (3.6 / (2 * c * g)) - 1 + rhoR Ψ c (c * u) ≤ 1 / 2 := le_trans hsmall hhalf
  have harc := arcsin_le_two_mul (z := exp (3.6 / (2 * c * g)) - 1 + rhoR Ψ c (c * u)) (add_nonneg hηnn hρnn) hz2
  have hlast : 1 / (4 * (2 * c * g)) ≤ 1 / (8 * g) * (log c / c) := by
    rw [show 1 / (8 * g) * (log c / c) = log c / (8 * c * g) by field_simp]
    rw [show 4 * (2 * c * g) = 8 * c * g by ring]
    exact div_le_div_of_nonneg_right hlog1 (by positivity)
  have hC : (7.2 / g + 2 * M + 1 / (8 * g)) / π * log c / c =
      (2 * (W * (log c / c)) + 1 / (8 * g) * (log c / c)) / π := by rw [hW]; ring
  rw [hC]
  refine div_le_div_of_nonneg_right ?_ pi_pos.le
  linarith

end Cvs.Prolate.LiouvilleGreen.RegularSolutionNodeLaw
