/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Stalk
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Dimension
import Tengoku.Hironaka.Hironaka.Scheme.Snc.RelativeDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A smooth scheme with preconnected underlying space has one relative dimension

[Kol07, Notation 64 (1)] asks the ambient scheme to be smooth of one relative dimension; the smooth
locus `X^{ns}` of an integral scheme is irreducible, hence preconnected, and so is smooth of a
single relative dimension `d` — the codimension `n − d` of `X^{ns}` in a smooth ambient of relative
dimension `n` is then the same at every closed point, which is what the étale equivalence of two
smooth points of `X` in the proof of [Kol07, Theorem 27] ("any two smooth points of `X` are étale
equivalent", [Kol07, 4.2]) needs. `Hironaka.Resolution.Algebraic.Kol07.Thm36.IsoOverSmoothLocus` and
`Hironaka.Resolution.Algebraic.Hir64.SingleCenter` use it to speak of the relative dimension of the
smooth locus.

* `ringKrullDim_stalk_add_trdeg_of_isStandardSmoothOfRelativeDimension`: on an affine open `V` whose
  section ring is standard smooth of relative dimension `m` over `k`, every point `x ∈ V` has
  `dim 𝒪_{X,x} + trdeg_k κ(x) = m` (the body of
  `Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension`, with the chart
  given instead of chosen).
* `isLocallyConstant_dimCount`: for `f` smooth, `x ↦ dim 𝒪_{X,x} + trdeg_k κ(x)` is locally constant
  — each point has a standard smooth affine chart, of some relative dimension
  (`exists_affineOpen_isStandardSmoothOfRelativeDimension'`).
* `exists_smoothOfRelativeDimension_of_preconnectedSpace`: a smooth `f : X ⟶ Spec k` with `X`
  preconnected and nonempty is smooth of one relative dimension (a locally constant function on a
  preconnected space is constant; `smoothOfRelativeDimension_of_forall_exists_affineOpen`).

Sources: [Kol07, Notation 64; Theorem 27; 4.2]; [Sta, Tag 0A21].
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The dimension count `x ↦ dim 𝒪_{X,x} + trdeg_k κ(x)` of a scheme over `k`, as a function to
`WithBot ℕ∞`.-/
noncomputable def dimCount (f : X ⟶ Spec (.of k)) (x : X) : WithBot ℕ∞ :=
  letI := f.stalkAlgebra x
  ringKrullDim (X.presheaf.stalk x) +
    ((Cardinal.toENat (Algebra.trdeg k (ResidueField (X.presheaf.stalk x))) : ℕ∞) : WithBot ℕ∞)

/-- Every point of a scheme smooth over `k` has an affine neighbourhood whose section ring is
standard smooth of SOME relative dimension over `k`.-/
theorem exists_affineOpen_isStandardSmoothOfRelativeDimension' (f : X ⟶ Spec (.of k)) [Smooth f]
    (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (m : ℕ),
      letI := f.sectionsAlgebra V
      Algebra.IsStandardSmoothOfRelativeDimension m k Γ(X, V) := by
  obtain ⟨V, hV, hxV, hstd⟩ := exists_affineOpen_isStandardSmooth f x
  let := f.sectionsAlgebra V
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hstd.out
  exact ⟨V, hV, hxV, P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

end AlgebraicGeometry
