/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.KL

/-!
# Non-absolutely-continuous KL example

This opt-in module records the finite PMF example that makes the support guard
on real-valued KL equality essential. Two disjoint pure laws have infinite
`ENNReal`-valued KL divergence, but applying `ENNReal.toReal` to that value
returns zero even though the laws are unequal.
-/

namespace LeanInfoTheory
namespace Examples
namespace KLTop

open Shannon

noncomputable section

local instance : MeasurableSpace Bool := ⊤

local instance : MeasurableSingletonClass Bool where
  measurableSet_singleton _ := trivial

/-- The pure law at `false`. -/
def leftLaw : PMF Bool := PMF.pure false

/-- The pure law at `true`, whose support is disjoint from `leftLaw`. -/
def rightLaw : PMF Bool := PMF.pure true

/-- The two pure laws are unequal.
@isnad1 id=ne.0h0v.s2.5f402a06084d from=translated src=- shape=836e6cbb vocab=d63296fc
-/
theorem laws_ne : leftLaw ≠ rightLaw := by
  intro h
  have hmass := congrArg (fun p : PMF Bool => p false) h
  simp [leftLaw, rightLaw] at hmass

/-- `leftLaw` is not absolutely continuous with respect to `rightLaw`.
@isnad1 id=not.0h0v.s3.22ac735a84b3 from=translated src=- shape=10b7b816 vocab=1b69be4b
-/
theorem not_absolutelyContinuous :
    Not (MeasureTheory.Measure.AbsolutelyContinuous
      leftLaw.toMeasure rightLaw.toMeasure) := by
  rw [toMeasure_absolutelyContinuous_iff_support_subset]
  simp [leftLaw, rightLaw]

/-- Failed support inclusion makes the KL divergence infinite.
@isnad1 id=eq.0h0v.s4.57cc8c786291 from=translated src=- shape=74013df7 vocab=65ff3d40
-/
theorem klDiv_eq_top :
    InformationTheory.klDiv leftLaw.toMeasure rightLaw.toMeasure = ⊤ := by
  apply (klDiv_pmf_eq_top_iff_not_support_subset leftLaw rightLaw).2
  simp [leftLaw, rightLaw]

/-- Taking `ENNReal.toReal` sends the infinite KL value to zero.
@isnad1 id=eq.0h0v.s4.5acd24cc1ab5 from=translated src=- shape=6d39fe5e vocab=625c3f40
-/
theorem toReal_klDiv_eq_zero :
    (InformationTheory.klDiv leftLaw.toMeasure rightLaw.toMeasure).toReal = 0 := by
  rw [klDiv_eq_top]
  simp

/--
Without absolute continuity, real-valued KL can be zero for two unequal laws;
this is the branch excluded by `toReal_klDiv_pmf_eq_zero_iff`.
@isnad1 id=and.0h0v.s5.0dc1281d8529 from=translated src=- shape=08f80bdd vocab=7432c03b
-/
theorem toReal_zero_trap :
    (InformationTheory.klDiv leftLaw.toMeasure rightLaw.toMeasure).toReal = 0 ∧
      leftLaw ≠ rightLaw ∧
        Not (MeasureTheory.Measure.AbsolutelyContinuous
          leftLaw.toMeasure rightLaw.toMeasure) :=
  ⟨toReal_klDiv_eq_zero, laws_ne, not_absolutelyContinuous⟩

end

end KLTop
end Examples
end LeanInfoTheory
