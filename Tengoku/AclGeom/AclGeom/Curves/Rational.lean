/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Genus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rational function fields have genus zero

The converse of the genus-zero checkpoint. A generator `t` has a single
simple pole `P∞`; each shift `t − a` has a single simple zero and the
same pole, and every place away from `P∞` is such a zero (residues), so
divisors of degree zero are principal by taking products of shifts —
partial fractions in divisor form. Every defect then reduces to that of
a multiple of `P∞`, where the powers of `t` fill the Riemann–Roch space:
all defects are `≤ 0` and the genus is zero.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]
variable {t : F}

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- A generator witnesses `[F : k(t)] = 1`.
@isnad1 id=eq.1h3v.s8.24c135c78ebe from=translated src=- shape=fa439600 vocab=a069799d
-/
theorem finrank_adjoin_eq_one_of_eq_top
    (htop : adjoin k ({t} : Set F) = ⊤) :
    Module.finrank (↥(adjoin k ({t} : Set F))) F = 1 := by
  rw [htop]
  exact IntermediateField.finrank_top

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- Shifting by a constant preserves transcendence.
@isnad1 id=transcen.1h4v.s7.52fb40900c8f from=translated src=- shape=15feef34 vocab=e02b9a64
-/
theorem transcendental_sub_algebraMap (htr : Transcendental k t)
    (a : k) : Transcendental k (t - algebraMap k F a) := by
  intro halg
  refine htr ?_
  have h1 : IsIntegral k (t - algebraMap k F a + algebraMap k F a) :=
    halg.isIntegral.add isIntegral_algebraMap
  rw [show t - algebraMap k F a + algebraMap k F a = t by ring] at h1
  exact h1.isAlgebraic

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- Shifting by a constant preserves the generator property.
@isnad1 id=eq.1h4v.s8.b818f2fed43b from=translated src=- shape=cde8c91d vocab=ad3d19b5
-/
theorem adjoin_sub_algebraMap_eq_top
    (htop : adjoin k ({t} : Set F) = ⊤) (a : k) :
    adjoin k ({t - algebraMap k F a} : Set F) = ⊤ := by
  rw [eq_top_iff, ← htop, adjoin_le_iff, Set.singleton_subset_iff]
  have h1 : t - algebraMap k F a ∈
      adjoin k ({t - algebraMap k F a} : Set F) := subset_adjoin k _ rfl
  have h2 := add_mem h1
    (IntermediateField.algebraMap_mem
      (adjoin k ({t - algebraMap k F a} : Set F)) a)
  rw [show t - algebraMap k F a + algebraMap k F a = t by ring] at h2
  exact h2

end

end AclGeom
