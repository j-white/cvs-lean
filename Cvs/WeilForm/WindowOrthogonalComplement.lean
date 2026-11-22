import Mathlib
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-!
# The window is an orthogonal complement, hence closed and complete

    window L = (coWindow L)ᗮ

the completeness that an operator-norm limit argument on the window needs, and the pole's
finite-rank factorisation.
-/

noncomputable section

open MeasureTheory

namespace Cvs.WeilForm.WindowOrthogonalComplement

variable {L : ℝ}

/-- **The classes vanishing a.e. on the window**, the orthogonal partner of `Cvs.WeilForm.WeilFormOnWindowL2.window`. -/
def coWindow (L : ℝ) : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) where
  carrier := {φ | ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc (0:ℝ) L → (φ : ℝ → ℝ) x = 0}
  add_mem' := by
    intro φ ψ hφ hψ
    filter_upwards [hφ, hψ, Lp.coeFn_add φ ψ] with x hx hy hadd hmem
    rw [hadd]; simp [hx hmem, hy hmem]
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure ℝ))] with x hx _
    rw [hx]; rfl
  smul_mem' := by
    intro c φ hφ
    filter_upwards [hφ, Lp.coeFn_smul c φ] with x hx hsmul hmem
    rw [hsmul]; simp [hx hmem]

/-- **Membership in `coWindow` is vanishing a.e. on `(0, L]`.** -/
theorem mem_coWindow {φ : Lp ℝ 2 (volume : Measure ℝ)} :
    φ ∈ coWindow L ↔
      ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc (0:ℝ) L → (φ : ℝ → ℝ) x = 0 := Iff.rfl

/-- **Membership in the window is vanishing a.e. off `(0, L]`.** -/
theorem mem_window {φ : Lp ℝ 2 (volume : Measure ℝ)} :
    φ ∈ Cvs.WeilForm.WeilFormOnWindowL2.window L ↔
      ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.Ioc (0:ℝ) L → (φ : ℝ → ℝ) x = 0 := Iff.rfl

/-- **The inner product on `L²` is the integral of the product.** -/
theorem inner_eq_integral (φ ψ : Lp ℝ 2 (volume : Measure ℝ)) :
    (inner ℝ φ ψ : ℝ) = ∫ x : ℝ, (φ : ℝ → ℝ) x * (ψ : ℝ → ℝ) x := by
  rw [MeasureTheory.L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [RCLike.inner_apply, mul_comm])

/-- **The window is the orthogonal complement of the classes supported off it.** -/
theorem window_eq_orthogonal (L : ℝ) :
    Cvs.WeilForm.WeilFormOnWindowL2.window L = (coWindow L)ᗮ := by
  ext φ
  constructor
  · intro hφ
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [inner_eq_integral]
    have hae : (fun x : ℝ => (u : ℝ → ℝ) x * (φ : ℝ → ℝ) x) =ᵐ[volume] fun _ => 0 := by
      filter_upwards [hu, hφ] with x hx hy
      by_cases hmem : x ∈ Set.Ioc (0:ℝ) L
      · rw [hx hmem]; ring
      · rw [hy hmem]; ring
    rw [integral_congr_ae hae, integral_zero]
  · intro hφ
    -- the complementary cut of `φ` lies in `coWindow`, and pairing it with `φ` gives `∫ φ² = 0`
    have hmeas : MeasurableSet ((Set.Ioc (0:ℝ) L)ᶜ) := measurableSet_Ioc.compl
    have hmem : MemLp ((Set.Ioc (0:ℝ) L)ᶜ.indicator (φ : ℝ → ℝ)) 2 (volume : Measure ℝ) :=
      (Lp.memLp φ).indicator hmeas.nullMeasurableSet
    set u : Lp ℝ 2 (volume : Measure ℝ) := hmem.toLp _ with hu_def
    have hu_ae : (u : ℝ → ℝ) =ᵐ[volume] (Set.Ioc (0:ℝ) L)ᶜ.indicator (φ : ℝ → ℝ) :=
      hmem.coeFn_toLp
    have hu_mem : u ∈ coWindow L := by
      rw [mem_coWindow]
      filter_upwards [hu_ae] with x hx hmemx
      rw [hx, Set.indicator_of_notMem (by simpa using hmemx)]
    have hzero : (inner ℝ u φ : ℝ) = 0 := (Submodule.mem_orthogonal _ _).mp hφ u hu_mem
    rw [inner_eq_integral] at hzero
    have hint : (fun x : ℝ => (u : ℝ → ℝ) x * (φ : ℝ → ℝ) x)
        =ᵐ[volume] fun x => (Set.Ioc (0:ℝ) L)ᶜ.indicator (fun y => (φ : ℝ → ℝ) y ^ 2) x := by
      filter_upwards [hu_ae] with x hx
      by_cases hmemx : x ∈ (Set.Ioc (0:ℝ) L)ᶜ
      · rw [hx, Set.indicator_of_mem hmemx, Set.indicator_of_mem hmemx]; ring
      · rw [hx, Set.indicator_of_notMem hmemx, Set.indicator_of_notMem hmemx]; ring
    rw [integral_congr_ae hint] at hzero
    have hnn : 0 ≤ᵐ[volume]
        fun x => (Set.Ioc (0:ℝ) L)ᶜ.indicator (fun y => (φ : ℝ → ℝ) y ^ 2) x := by
      filter_upwards with x
      exact Set.indicator_nonneg (fun y _ => sq_nonneg _) x
    have hintegrable : Integrable
        (fun x => (Set.Ioc (0:ℝ) L)ᶜ.indicator (fun y => (φ : ℝ → ℝ) y ^ 2) x)
        (volume : Measure ℝ) := by
      have hsq : Integrable (fun x => (φ : ℝ → ℝ) x * (φ : ℝ → ℝ) x) (volume : Measure ℝ) :=
        (Lp.memLp φ).integrable_mul (Lp.memLp φ)
      have : Integrable (fun x => (φ : ℝ → ℝ) x ^ 2) (volume : Measure ℝ) := by
        simpa [pow_two] using hsq
      exact this.indicator hmeas
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae hnn hintegrable).mp hzero
    rw [mem_window]
    filter_upwards [hae0] with x hx hmemx
    have hx' : (Set.Ioc (0:ℝ) L)ᶜ.indicator (fun y => (φ : ℝ → ℝ) y ^ 2) x = 0 := hx
    rw [Set.indicator_of_mem (by simpa using hmemx)] at hx'
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx'

/-- **The window is closed.** -/
theorem isClosed_window (L : ℝ) :
    IsClosed ((Cvs.WeilForm.WeilFormOnWindowL2.window L : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ))) :
      Set (Lp ℝ 2 (volume : Measure ℝ))) := by
  rw [window_eq_orthogonal]
  exact Submodule.isClosed_orthogonal _

/-- **The window is complete.** -/
instance completeSpace_window (L : ℝ) :
    CompleteSpace (Cvs.WeilForm.WeilFormOnWindowL2.window L) :=
  (isClosed_window L).completeSpace_coe

/-! ### The cut exponentials, and the pole's finite rank -/

/-- **The window's inner product is the integral of the representatives' product.** -/
theorem inner_rep (ξ φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    (inner ℝ ξ φ : ℝ)
      = ∫ x, Cvs.WeilForm.WindowRepresentative.rep ξ x * Cvs.WeilForm.WindowRepresentative.rep φ x := by
  have h : (inner ℝ ξ φ : ℝ)
      = inner ℝ (ξ : Lp ℝ 2 (volume : Measure ℝ)) (φ : Lp ℝ 2 (volume : Measure ℝ)) := rfl
  rw [h, inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [Cvs.WeilForm.WindowRepresentative.ae_eq_rep ξ, Cvs.WeilForm.WindowRepresentative.ae_eq_rep φ]
    with x hx hy
  show Cvs.WeilForm.WindowRepresentative.fn ξ x * Cvs.WeilForm.WindowRepresentative.fn φ x = _
  rw [hx, hy]

/-! ### The channel integral's modulus of continuity -/

variable {b : ℝ}

end Cvs.WeilForm.WindowOrthogonalComplement
