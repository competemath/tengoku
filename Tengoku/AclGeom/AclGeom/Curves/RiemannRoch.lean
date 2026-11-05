/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Residues

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Riemann–Roch spaces

The space `L(D)` of a divisor: elements whose principal divisor is
bounded below by `-D`. This file provides the definitional layer of the
Riemann–Roch machinery (issue #13, P3): `L(D)` is a `k`-submodule of `F`,
monotone in the divisor, containing the constants at effective divisors.
The dimension bounds and Riemann's inequality build on this layer.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P3).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The **Riemann–Roch space** of a divisor `D`: the `k`-submodule of
elements whose order at every place is at least `-D`.-/
noncomputable def RiemannSpace (D : Divisor k F) : Submodule k F where
  carrier := {f : F | f = 0 ∨ ∀ P : Place k F, -(D P) ≤ P.ord f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    rcases eq_or_ne f 0 with rfl | hf0
    · simpa using hg
    rcases eq_or_ne g 0 with rfl | hg0
    · simpa using hf
    rcases eq_or_ne (f + g) 0 with hfg | hfg
    · exact Or.inl hfg
    rcases hf with rfl | hf
    · exact absurd rfl hf0
    rcases hg with rfl | hg
    · exact absurd rfl hg0
    refine Or.inr fun P ↦ ?_
    exact le_trans (le_min (hf P) (hg P)) (P.min_ord_le_ord_add hf0 hg0 hfg)
  smul_mem' := by
    intro c f hf
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl (zero_smul k f)
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Or.inl (smul_zero c)
    rcases hf with rfl | hf
    · exact absurd rfl hf0
    refine Or.inr fun P ↦ ?_
    have h1 : P.ord (c • f) = P.ord f := by
      rw [Algebra.smul_def,
        P.ord_mul ((map_ne_zero (algebraMap k F)).2 hc0) hf0,
        P.ord_algebraMap hc0, zero_add]
    rw [h1]
    exact hf P

/--
@isnad1 id=iff.0h4v.s7.9232a0c1b698 from=translated src=- shape=4d367f9e vocab=1c423348
-/
theorem mem_riemannSpace_iff {D : Divisor k F} {f : F} :
    f ∈ RiemannSpace D ↔
      f = 0 ∨ ∀ P : Place k F, -(D P) ≤ P.ord f := Iff.rfl

section OneStep

end OneStep

section Dimension

/-- The positive part of a divisor.-/
noncomputable def Divisor.pos (D : Divisor k F) : Divisor k F :=
  D.mapRange (fun m ↦ max m 0) (by simp)

end Dimension

section PoleDivisor

variable (k) in
/-- The **pole divisor** `(f)_∞` of an element: the positive part of the
negated principal divisor.-/
noncomputable def poleDivisor (f : F) : Divisor k F :=
  (-(divisorOf k f)).pos

end PoleDivisor

section RiemannBound

end RiemannBound

end

end AclGeom
