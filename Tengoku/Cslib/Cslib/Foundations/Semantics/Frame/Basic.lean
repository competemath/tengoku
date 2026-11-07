/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Init
public import Tengoku.Cslib.Cslib.Foundations.Data.PFunctor.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/leanprover/cslib@e806c8e639ed, `Cslib/Foundations/Semantics/Frame/Basic.lean`: removed 4 tag(s) of the custom grind set(s) `modal` from declarations. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! # Modal Frames

A frame is a structure of relations, each with its own arity.

## Implementation notes

Frames for general modal logic were formulated with modal similarity types [Blackburn2001], which
we generalise here to arbitrary polynomial functors.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

@[expose] public section

namespace Cslib

/-- A frame is an indexed structure of general relations that can differ in argument positions.

Frames are typically used in combination with modal logics or akin concepts. This is why we use
`op` (for operator) to range over relation indexes.

The definition generalises Definition 1.23 in [Blackburn2001] to general operator signatures given
as `PFunctor`s and possibly-empty world types.-/
structure Frame (World : Type u) (τ : PFunctor) where
  /-- Accessibility relations.-/
  r : (op : τ.A) → World → (τ.B op → World) → Prop

namespace Frame

/-- The binary relation obtained by observing position `i` of the worlds accessible via `op`.-/
def project (f : Frame World τ) (op : τ.A) (i : τ.B op) : World → World → Prop :=
  fun w w' => ∃ ws, f.r op w ws ∧ ws i = w'

/-- The binary relation induced by restricting the accessibility relation of `op`
to constant tuples of worlds.-/
@[instance_reducible]
def diagonal (f : Frame World τ) (op : τ.A) : World → World → Prop :=
  fun w w' => f.r op w (fun _ => w')

/--
@isnad1 id=r.1h6v.s5.29cd86e4d7c5 from=translated src=- shape=05d91ba3 vocab=df42106d
-/
@[scoped grind →]
theorem r_const_of_diagonal {f : Frame World τ} (h : f.diagonal op w w') :
    f.r op w (fun _ => w') := by grind [Frame.diagonal]

/--
@isnad1 id=diagonal.1h6v.s5.8560cb699dd3 from=translated src=- shape=1da52c50 vocab=f251b24b
-/
@[scoped grind →]
theorem diagonal_of_r [PFunctor.Unary τ] {f : Frame World τ} (h : f.r op w ws) :
    f.diagonal op w (ws default) := by grind [Frame.diagonal, PFunctor.Unary.fun_eq_const op ws]

/-- A frame is diagonally symmetric at `op` if, whenever `w` accesses `ws`, some component of `ws`
accesses the constant sequence at `w`.-/
class DiagonalSymm (f : Frame World τ) (op : τ.A) where
  symm w ws : f.r op w ws → ∃ i, f.r op (ws i) (fun _ => w)

/-- A frame is transitive at `op` if accessibility can be composed through any accessible component:
whenever `w` accesses `ws₁` and `ws₁ i` accesses `ws₂`, then `w` accesses `ws₂`.-/
class Trans (f : Frame World τ) (op : τ.A) where
  trans w ws₁ i ws₂ : f.r op w ws₁ → f.r op (ws₁ i) ws₂ → f.r op w ws₂

/-- A frame is right Euclidean at `op` if, whenever a world `w` accesses two tuples `ws₁` and
`ws₂`, some component of `ws₂` accesses `ws₁`.-/
class RightEuclidean (f : Frame World τ) (op : τ.A) where
  rightEuclidean w ws₁ ws₂ : f.r op w ws₁ → f.r op w ws₂ → ∃ i, f.r op (ws₂ i) ws₁

/-- A predicate map `Ps` is preserved from `P` by `op` if, whenever `P` holds at a world `w`,
then for every tuple `ws` accessible from `w` via `op`, each component `ws i` satisfies the
corresponding predicate `Ps i`.-/
def PreservesMap (f : Frame α τ) (op : τ.A) (P : α → Prop) (Ps : τ.B op → α → Prop) : Prop :=
  ∀ w ws, f.r op w ws → P w → ∃ i, Ps i (ws i)

/-- Builds a unary frame from an indexed family of binary relations.-/
def ofRelations {τ : PFunctor} [τ.Unary] (r : τ.A → World → World → Prop) :
    Frame World τ where
  r i w ws := r i w (ws default)

/--
@isnad1 id=iff.0h6v.s5.0b8b397b8ad2 from=translated src=- shape=c907b45b vocab=17efbf01
-/
@[scoped grind =]
lemma ofRelations_iff {τ : PFunctor} [τ.Unary] (r : τ.A → World → World → Prop) (i : τ.A)
    (w : World) (ws : τ.B i → World) : (ofRelations r).r i w ws ↔ r i w (ws default) := by rfl

/--
@isnad1 id=iff.0h6v.s5.17d5b00e3b8d from=translated src=- shape=10196d16 vocab=39d3e55b
-/
@[simp, scoped grind =]
lemma ofRelations_diagonal_iff {τ : PFunctor} [τ.Unary]
    (r : τ.A → World → World → Prop) (i : τ.A) (w w' : World) :
    (ofRelations r).diagonal i w w' ↔ r i w w' := by
  rfl

end Frame

end Cslib
