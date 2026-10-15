/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A discriminant factor used in the Odlyzko-bound argument. -/
def CompletedZeta.discriminantFactor (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)

/-- An archimedean factor used in the Odlyzko-bound argument. -/
def CompletedZeta.archimedeanFactor (s : ℂ) : ℂ :=
  Complex.Gammaℝ s ^ nrRealPlaces K * (Complex.Gammaℂ s / 2) ^ nrComplexPlaces K

/-- A completed used in the Odlyzko-bound argument. -/
def CompletedZeta.completed (s : ℂ) : ℂ :=
  CompletedZeta.discriminantFactor K s * CompletedZeta.archimedeanFactor K s * dedekindZeta K s

/--
@isnad1 id=lt.0h1v.s4.82cd6e3d2a1a from=translated src=- shape=0d3e45f9 vocab=a11760cd
-/
theorem discr_abs_pos : 0 < |(discr K : ℝ)| := by
  exact abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

/--
@isnad1 id=ne.0h2v.s4.15cc5d091f66 from=translated src=- shape=f1a1ee7f vocab=5a5f4971
-/
theorem dedekindDiscriminantFactor_ne_zero (s : ℂ) :
    CompletedZeta.discriminantFactor K s ≠ 0 := by
  rw [CompletedZeta.discriminantFactor, cpow_ne_zero_iff]
  exact Or.inl (ofReal_ne_zero.mpr (discr_abs_pos K).ne')

/--
@isnad1 id=differen.0h1v.s6.ebf42c8efdb3 from=translated src=- shape=34ad9530 vocab=318771ec
-/
theorem differentiable_dedekindDiscriminantFactor :
    Differentiable ℂ (CompletedZeta.discriminantFactor K) := by
  unfold CompletedZeta.discriminantFactor
  exact (differentiable_id.div_const _).const_cpow <|
    Or.inl (ofReal_ne_zero.mpr (discr_abs_pos K).ne')

end NumberField.Odlyzko
