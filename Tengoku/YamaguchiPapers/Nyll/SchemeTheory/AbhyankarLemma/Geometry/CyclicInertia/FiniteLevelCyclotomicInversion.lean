/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.CyclotomicRestriction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cyclotomic inversion in finite-level inertia

The normal residue extension attached to a decomposition group is embedded in
a genuine separable closure.  Cyclotomic inversion restricts to that normal
extension and the residue exact sequence lifts it back to the decomposition
group.  The selected residue field itself need not be a separable closure.
-/

noncomputable section

universe u v

namespace TameAbhyankar.SGA1

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

section IntegerBase

local instance : IsDomain (ULift.{v} ℤ) :=
  (ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

private abbrev integerGenericResidueField : Type v :=
  AlgebraicGeometry.Scheme.residueField
    (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{v} ℤ)))
    (_root_.genericPoint
      (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{v} ℤ))))

end IntegerBase

end TameAbhyankar.SGA1

end
