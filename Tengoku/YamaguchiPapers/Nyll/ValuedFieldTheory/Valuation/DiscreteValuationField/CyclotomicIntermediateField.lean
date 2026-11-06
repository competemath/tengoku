/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.NumberTheory.Cyclotomic.Basic
import Tengoku.Seed.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cyclotomic intermediate fields inside an algebraic closure

A primitive root in the given closure generates an actual cyclotomic
intermediate field. The characteristic only needs to avoid the root order.
-/

namespace ValuationTheory.DiscreteValuationField

/-- An algebraic closure contains a cyclotomic intermediate field whenever
the root order is nonzero in the base field.
@isnad1 id=ex.0h3v.s7.85ca6be1ddcd from=translated src=- shape=ceddeb39 vocab=2b446ae9
-/
theorem exists_cyclotomic_intermediateField
    (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (n : ℕ) [NeZero (n : K)] :
    ∃ E : IntermediateField K Ω, IsCyclotomicExtension {n} K E := by
  have : NeZero n := .of_neZero_natCast K
  have : NeZero (n : Ω) := by
    simpa only [map_natCast] using
      (‹NeZero (n : K)›.of_injective (algebraMap K Ω).injective)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  exact ⟨IntermediateField.adjoin K {ζ},
    hζ.intermediateField_adjoin_isCyclotomicExtension K⟩

end ValuationTheory.DiscreteValuationField
