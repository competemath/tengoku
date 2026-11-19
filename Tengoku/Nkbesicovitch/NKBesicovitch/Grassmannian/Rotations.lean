/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Basic
public import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint
public import Tengoku.Seed.Topology.Algebra.Star.Unitary
public import Tengoku.Seed.MeasureTheory.Measure.Haar.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Orthogonal operators and their Haar probability measure

The full orthogonal group is realized as the unitary continuous endomorphisms
of a real Euclidean space, with the operator norm topology.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace

namespace NKBesicovitch

/-- The full orthogonal group of Euclidean n-space, including reflections.-/
noncomputable abbrev Rotations (n : ℕ) :=
  unitary (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

namespace Rotations

variable {n : ℕ}

noncomputable instance : MeasurableSpace (Rotations n) := borel (Rotations n)

instance : BorelSpace (Rotations n) := ⟨rfl⟩

end Rotations

end NKBesicovitch
