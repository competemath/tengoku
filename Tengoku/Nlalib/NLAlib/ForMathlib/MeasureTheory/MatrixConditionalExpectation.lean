import Tengoku.Seed.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conditional expectation preserves positive semidefinite matrix order

The closed convex positive semidefinite cone gives conditional positivity and
Loewner monotonicity on arbitrary underlying measurable spaces.
-/

noncomputable section

open MeasureTheory Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace MeasureTheory

variable {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] [DecidableEq n]
variable {μ : Measure Ω}

omit [Fintype n] [DecidableEq n] in
/-- The cone of positive semidefinite complex matrices is convex as a real set.
Source: quadratic-form positivity; helper for Tropp 2011 (matrix Freedman)
and atlas `matrix-freedman`.
@isnad1 id=convex.0h1v.s6.c23a3e4840fa from=translated src=- shape=6a9fa97d vocab=38bd7064
-/
theorem _root_.Matrix.convex_setOf_posSemidef :
    Convex ℝ {A : Matrix n n ℂ | A.PosSemidef} := by
  intro A hA B hB a b ha hb hab
  exact (hA.smul ha).add (hB.smul hb)

/-- The cone of positive semidefinite complex matrices is closed.
Source: the closed positive cone of a C-star algebra; helper for operator
rederivations Section 3.1 and atlas `matrix-freedman`.
@isnad1 id=isclosed.0h1v.s5.43070aafa054 from=translated src=- shape=30f73824 vocab=7f203280
-/
theorem _root_.Matrix.isClosed_setOf_posSemidef :
    IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
  simpa only [Set.Ici, Matrix.nonneg_iff_posSemidef] using
    (isClosed_Ici : IsClosed (Set.Ici (0 : Matrix n n ℂ)))

/-- Conditional expectation preserves positive semidefinite matrix values almost
everywhere. Closed convex conditional-mean membership proves this for arbitrary `Ω`.
Source: Mathlib conditional Jensen membership; Tropp 2011 (matrix Freedman).
@isnad1 id=eventual.3h6v.s7.72351da5d1ee from=translated src=- shape=cacde69a vocab=a22be2af
-/
theorem ae_posSemidef_condExp_of_ae_posSemidef (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {X : Ω → Matrix n n ℂ} (hX : Integrable X μ) (hpos : ∀ᵐ ω ∂μ, (X ω).PosSemidef) :
    ∀ᵐ ω ∂μ, (μ[X | m] ω).PosSemidef :=
  Matrix.convex_setOf_posSemidef.condExp_mem hm hX Matrix.isClosed_setOf_posSemidef hpos

/-- Conditional expectations preserve Loewner order for integrable complex matrix
functions. This is derived from conditional positivity of the difference.
Source: Tropp 2011 (matrix Freedman); atlas `matrix-freedman` (helper).
@isnad1 id=eventual.4h7v.s8.cfa67f19b523 from=translated src=- shape=72239d8e vocab=347c5d99
-/
theorem ae_condExp_le_condExp_of_ae_le (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {X Y : Ω → Matrix n n ℂ} (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY : X ≤ᵐ[μ] Y) : μ[X | m] ≤ᵐ[μ] μ[Y | m] := by
  have hpos := ae_posSemidef_condExp_of_ae_posSemidef hm (hY.sub hX)
    (hXY.mono fun ω hω => Matrix.le_iff.mp hω)
  filter_upwards [hpos, condExp_sub hY hX m] with ω hpos heq
  rw [heq] at hpos
  exact Matrix.le_iff.mpr hpos

end MeasureTheory
