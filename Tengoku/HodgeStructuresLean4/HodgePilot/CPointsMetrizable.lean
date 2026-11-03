import Tengoku.HodgeStructuresLean4.HodgePilot.AnalyticGlue
import Tengoku.Seed.Topology.Metrizable.Basic
import Tengoku.Seed.Topology.Metrizable.Uniformity
import Tengoku.Seed.Topology.EMetricSpace.Paracompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Metrizability of the analytic point-space of a finite-type ℂ-algebra

For a finitely generated (finite-type) ℂ-algebra `A`, the analytic point-space
`CPoints A` (`HodgePilot.Analytic`) is metrizable: evaluation at a finite
generating family is a topological embedding into `ℂ^N`
(`isEmbedding_evalGen`), and metrizability passes to subspaces.
Paracompactness follows by endowing the space with a compatible metric —
every pseudo-e-metric space is paracompact.  The same statements transport to
the scheme-level analytic point-space `SPoints (structMor A)` of the affine
ℂ-scheme `Spec A` along the homeomorphism `affineSPointsHomeomorph`
(`HodgePilot.AnalyticGlue`).

* `metrizableSpace_of_evalGen` — generator form: evaluation at a finite
  generating family of the ℂ-algebra `A` makes `CPoints A` metrizable.
* `instMetrizableSpaceCPoints` — `CPoints A` is metrizable for `A` of finite
  type.
* `instParacompactSpaceCPoints` — `CPoints A` is paracompact for `A` of finite
  type.  (`CPoints A` is Hausdorff for *every* `A`: `instT2SpaceCPoints` in
  `HodgePilot.Analytic`.)
* `instT2SpaceSPointsAffine`, `instMetrizableSpaceSPointsAffine`,
  `instParacompactSpaceSPointsAffine` — the same three properties for the
  scheme-level point-space of the affine ℂ-scheme `Spec A` (Hausdorffness for
  every `A`; metrizability and paracompactness at finite type).

Everything in this file is a topological property of the analytic point-space:
pure point-set topology at the stated affine scope.  No analytic-space or
manifold structure is used or claimed, and nothing beyond point-set topology
is stated.
-/

open Topology

noncomputable section

universe u v

namespace HodgePilot.Analytic

/-! ## The affine point-space `CPoints A` -/

section Affine

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- **Metrizability of the analytic point-space, generator form**: evaluation
at a finite generating family `g : ι → A` of the ℂ-algebra `A` is a
topological embedding `CPoints A ↪ ℂ^ι` (`isEmbedding_evalGen`), and the
finite product `ι → ℂ` is metrizable, so the analytic topology on the
ℂ-points is metrizable.
@isnad1 id=metrizab.1h3v.s7.2d730fb1ef2a from=translated src=- shape=30b5bcb7 vocab=c2349edc
-/
theorem metrizableSpace_of_evalGen {ι : Type v} [Finite ι] (g : ι → A)
    (hg : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    TopologicalSpace.MetrizableSpace (CPoints A) :=
  (isEmbedding_evalGen g hg).metrizableSpace

/-- The analytic point-space of a finite-type ℂ-algebra is metrizable (choose
a finite presentation; the ℂ-points embed as a closed subspace of some
`ℂⁿ`).
@isnad1 id=metrizab.0h1v.s5.227a70204a1b from=translated src=- shape=af58d91a vocab=1f79131d
-/
instance instMetrizableSpaceCPoints [Algebra.FiniteType ℂ A] :
    TopologicalSpace.MetrizableSpace (CPoints A) := by
  obtain ⟨n, e, he⟩ := exists_isClosedEmbedding_of_finiteType A
  exact he.isEmbedding.metrizableSpace

end Affine

/-! ## The scheme-level point-space of an affine ℂ-scheme

The three properties transport along the homeomorphism
`affineSPointsHomeomorph : CPoints A ≃ₜ SPoints (structMor A)`. -/

section AffineScheme

variable (A : Type) [CommRing A] [Algebra ℂ A]

/-- The scheme-level analytic point-space of an affine ℂ-scheme of finite type
is metrizable (transport of `instMetrizableSpaceCPoints` along
`affineSPointsHomeomorph`).
@isnad1 id=metrizab.0h1v.s5.74eb3b52fd61 from=translated src=- shape=1d064726 vocab=7c0b1b3a
-/
instance instMetrizableSpaceSPointsAffine [Algebra.FiniteType ℂ A] :
    TopologicalSpace.MetrizableSpace (SPoints (structMor A)) :=
  (affineSPointsHomeomorph A).symm.isEmbedding.metrizableSpace

end AffineScheme

end HodgePilot.Analytic
