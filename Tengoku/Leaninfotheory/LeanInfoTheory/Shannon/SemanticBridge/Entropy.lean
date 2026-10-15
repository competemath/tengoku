/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.Entropy
import Tengoku

/-!
# Entropy and expected self-information

This focused semantic-bridge module relates the lightweight finite-sum entropy
definition to expected self-information with respect to `PMF.toMeasure`. It
owns the measure-theoretic import needed for that bridge while leaving the core
finite entropy module lightweight.
-/

namespace LeanInfoTheory
namespace Shannon

open MeasureTheory
open scoped BigOperators

noncomputable section

universe u

/--
Self-information of an atom under a finite PMF, in nats.

It is `-log p(a)` when the real mass of `a` is nonzero, and `0` on zero-mass
atoms. The zero branch is the usual entropy convention that zero-probability
outcomes contribute no expected information.
-/
def selfInfo {alpha : Type u} (p : PMF alpha) (a : alpha) : Real :=
  if (p a).toReal = 0 then 0 else -Real.log (p a).toReal

/-- A zero-mass atom has zero self-information by convention.
@isnad1 id=eq.1h3v.s5.c10473fd4c8c from=translated src=- shape=5ec5da81 vocab=d8465b2a
-/
@[simp]
theorem selfInfo_of_toReal_eq_zero {alpha : Type u} (p : PMF alpha) {a : alpha}
    (ha : (p a).toReal = 0) :
    selfInfo p a = 0 := by
  simp [selfInfo, ha]

/-- A nonzero-mass atom has self-information `-log p(a)`.
@isnad1 id=eq.1h3v.s5.ddecf5acbd14 from=translated src=- shape=34262361 vocab=4ab70ceb
-/
theorem selfInfo_of_toReal_ne_zero {alpha : Type u} (p : PMF alpha) {a : alpha}
    (ha : (p a).toReal ≠ 0) :
    selfInfo p a = -Real.log (p a).toReal := by
  simp [selfInfo, ha]

/--
Multiplying self-information by the atom mass recovers the `Real.negMulLog`
entropy summand.
@isnad1 id=eq.0h3v.s5.7c5eaf3bdad5 from=translated src=- shape=f6839f60 vocab=3ef4df92
-/
theorem toReal_mul_selfInfo {alpha : Type u} (p : PMF alpha) (a : alpha) :
    (p a).toReal * selfInfo p a = Real.negMulLog (p a).toReal := by
  by_cases ha : (p a).toReal = 0
  · simp [selfInfo, ha]
  · simp [selfInfo, ha, Real.negMulLog]

/--
Semantic bridge for finite entropy: the finite-sum definition of
`Shannon.entropy` is the expected self-information with respect to
`PMF.toMeasure`.

Informally, this is the textbook identity `H(P) = E[-log P(X)]`, with the
zero-mass convention handled by `selfInfo`.
@isnad1 id=eq.0h2v.s5.39f4df495451 from=translated src=- shape=5b264c23 vocab=49c6c68d
-/
theorem entropy_eq_integral_selfInfo {alpha : Type u}
    [Fintype alpha] [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p : PMF alpha) :
    entropy p = ∫ a, selfInfo p a ∂p.toMeasure := by
  rw [entropy_eq_sum, PMF.integral_eq_sum]
  exact Finset.sum_congr rfl fun a _ha => by
    rw [smul_eq_mul, toReal_mul_selfInfo]

end

end Shannon
end LeanInfoTheory
