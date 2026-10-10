/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Marks.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Marks.Internal

/-!
# Endpoint marks record boundary edges and degree loss

Each cut edge supplies one outside mark. For a restoration family, marks
at vertices outside all regions count exactly their incident deleted edges.
The original degree is the sum of the remaining degree and these marks.
On a set avoiding every region, marks count the region cuts crossing it;
these are the incidences that require compensation during restoration.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V) (P : Finset V)

/-- Every boundary edge gives exactly one outside mark. -/
theorem degree_boundaryMarks : (boundaryMarks B P).degree = (B.cutFinset P).card :=
  RestorationFamily.Internal.degree_boundaryMarks B P

/-- On a set disjoint from a region, its marks count exactly the shared cut edges. -/
theorem sum_boundaryMarks {X : Finset V} (fresh : Disjoint X P) :
    (∑ v ∈ X, boundaryMarks B P v) = (B.cutFinset P ∩ B.cutFinset X).card :=
  RestorationFamily.Internal.sum_boundaryMarks B P fresh

namespace RestorationFamily

variable {E ι : Type} [Fintype ι] {B : SimpleGraph V} {R : Multigraph V E}
  (F : RestorationFamily B R ι)

/-- Total endpoint marks equal the sum of the region boundary sizes. -/
theorem degree_endpointMarks : F.endpointMarks.degree = ∑ i, (B.cutFinset (F.region i)).card :=
  Internal.degree_endpointMarks F

/-- Marks on an outside set count all region boundaries meeting its cut. -/
theorem sum_endpointMarks {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i)) :
    (∑ v ∈ X, F.endpointMarks v) = ∑ i, (B.cutFinset (F.region i) ∩ B.cutFinset X).card :=
  Internal.sum_endpointMarks F fresh

end RestorationFamily

end Algebraic.Cutwidth.Bisection.RedBlack
