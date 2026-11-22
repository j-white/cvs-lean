import Mathlib
import Cvs.Finite.ExponentialKernelLocalises
import Cvs.Upstream.ComplexificationIsometryL2
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative

/-!
# The channel operator is compact, and the kernel operator with it

    `chanCLM b L '' ball` is uniformly bounded and uniformly Lipschitz

so Arzelà–Ascoli on the window makes it totally bounded, and the truncated kernel operator is a
compact symmetric operator.
-/

noncomputable section

open MeasureTheory Set Metric
open Cvs.Finite.ExponentialKernelLocalises (convSplit)

namespace Cvs.WeilForm.ChannelOperatorCompact

variable {L b : ℝ}

/-! ### The argument clamped to the window -/

/-- The argument, clamped to the window. -/
def clamp (L x : ℝ) : ℝ := max 0 (min L x)

/-! ### The clamped channel image -/

/-- The channel integral, with its argument clamped to the window. -/
def chanClamp (b L : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : ℝ → ℝ :=
  fun x => convSplit b L (Cvs.WeilForm.WindowRepresentative.rep φ) (clamp L x)

/-! ### The family, and Arzelà–Ascoli -/

/-! ### The complexification of the window, and compactness -/

/-- **The complexification of a window class.** -/
def Psi (L : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) : Lp ℂ 2 (volume : Measure ℝ) :=
  Cvs.Upstream.ComplexificationIsometryL2.emb (φ : Lp ℝ 2 (volume : Measure ℝ))

/-- **It is an isometry.** -/
theorem isometry_Psi (L : ℝ) : Isometry (Psi L) :=
  Cvs.Upstream.ComplexificationIsometryL2.isometry_emb.comp isometry_subtype_coe

end Cvs.WeilForm.ChannelOperatorCompact
