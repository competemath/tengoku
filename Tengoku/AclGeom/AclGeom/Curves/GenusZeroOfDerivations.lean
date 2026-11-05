/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Derivations
import Tengoku.AclGeom.AclGeom.Curves.Genus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genus zero from two independent regular derivations

A function field of one variable over an algebraically closed field `K` which has two
`K`-linearly independent everywhere-regular `K`-derivations has genus zero
(`genus_eq_zero_of_linearIndependent_derivations`).

In genus at least two every regular derivation vanishes
(`derivation_eq_zero_of_two_le_genus`). In genus one, a suitable nonzero combination of the
two derivations vanishes at a chosen place: its value at a uniformizer has residue zero, and
then it maps the whole valuation ring into the maximal ideal. Such a derivation is zero
(`derivation_eq_zero_of_genus_eq_one`).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#21). An input of the genus argument for
Hrushovski–Weil curves.
-/

namespace AclGeom

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [IsAlgClosed K]
  [IsFunctionFieldOneVar K E]

omit [IsAlgClosed K] [IsFunctionFieldOneVar K E] in
/-- A derivation preserving every proper valuation subring containing `K` is regular.
@isnad1 id=derivati.1h3v.s8.4ba3c1e4daac from=translated src=- shape=61cd1b2e vocab=36a76566
-/
theorem derivationIsRegular_of_forall_valuationSubring {D : Derivation K E E}
    (h : ∀ V : ValuationSubring E, (∀ c : K, algebraMap K E c ∈ V) → V ≠ ⊤ →
      ∀ x ∈ V, D x ∈ V) :
    DerivationIsRegular D := fun P x hx ↦
  Place.mem_toSubmodule_iff.2 ((P.val.valuation_le_one_iff _).2
    (h P.val P.algebraMap_mem P.ne_top x
      ((P.val.valuation_le_one_iff x).1 (Place.mem_toSubmodule_iff.1 hx))))

end

end AclGeom
