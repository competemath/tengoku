import Tengoku.Seed.Analysis.Normed.Group.Basic
import Tengoku.Seed.MeasureTheory.Group.Pointwise
import Tengoku.Seed.MeasureTheory.Measure.AEDisjoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/jaumededios/Tiling@00f80c7de5ac, `Tiling/Basic.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/


/-!
# Translational tilings

This file models tilings of a normed additive group, including `ℤ`, `ℝ`, and finite-dimensional
Euclidean spaces.  A prototile is a nonempty measurable set; in particular, its support need not
be bounded.  Its label is kept separate from its support, so differently oriented or decorated
copies may have the same underlying set.

A placement is a translation vector together with a prototile label.  Measurable tilings are
countable, pairwise almost-everywhere disjoint, and cover almost every point.  Compatibility
conditions are encoded in the geometry of the prototile supports themselves.
-/

open scoped Pointwise
open Function MeasureTheory

namespace Tiling

universe u v

/-- A nonempty measurable set used as a translational prototile.-/
structure Prototile (E : Type u) [MeasurableSpace E] where
  /-- The measurable set occupied by the unplaced prototile.-/
  support : Set E
  /-- The prototile support is measurable.-/
  measurableSet_support : MeasurableSet support
  /-- Prototiles are not empty.-/
  nonempty_support : support.Nonempty

/-- A labelled family of prototiles.  The type `P` carries identity, orientation, or decoration;
the function supplies the geometric prototile attached to each label.-/
abbrev PrototileFamily (E : Type u) (P : Type v) [MeasurableSpace E] :=
  P → Prototile E

/-- A placement consists of a translation vector and a prototile label.-/
abbrev Placement (E : Type u) (P : Type v) := E × P

/-- A candidate tiling is a set of translated, labelled prototiles.-/
abbrev ProtoTiling (E : Type u) (P : Type v) := Set (Placement E P)

section Geometry

variable {E : Type u} {P : Type v}
variable [NormedAddCommGroup E] [MeasureSpace E]

/-- The set occupied by the translate `(x, p)`.-/
def placedTile (T : PrototileFamily E P) (i : Placement E P) : Set E :=
  i.1 +ᵥ (T i.2).support

/-- Distinct placements have almost-everywhere disjoint supports.-/
def IsPacking (T : PrototileFamily E P) (A : ProtoTiling E P) : Prop :=
  A.Pairwise (AEDisjoint volume on placedTile T)

/-- Almost every point belongs to the union of the placed supports.-/
def IsCover (T : PrototileFamily E P) (A : ProtoTiling E P) : Prop :=
  ∀ᵐ x, x ∈ ⋃ i : A, placedTile T i

/-- A countable measurable translational tiling.-/
structure IsTiling (T : PrototileFamily E P) (A : ProtoTiling E P) : Prop where
  countable : A.Countable
  isPacking : IsPacking T A
  isCover : IsCover T A

end Geometry

end Tiling
