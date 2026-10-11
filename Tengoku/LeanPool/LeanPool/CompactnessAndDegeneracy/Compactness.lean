/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import Tengoku

/-!
# A counterexample to the Erdős--Simonovits compactness conjecture

This file constructs a finite family of connected bipartite cyclic graphs whose
family extremal number grows strictly more slowly than that of every member.
-/

namespace CompactnessConjecture

noncomputable section Foundations

open Filter Finset SimpleGraph
open scoped Topology

/-- A finite simple graph packaged with its vertex count. -/
public structure FiniteGraph where
  /-- The number of vertices. -/
  order : ℕ
  /-- The graph on the standard finite vertex type. -/
  graph : SimpleGraph (Fin order)

/-- A host graph contains no member of the forbidden family. -/
public def FamilyFree (family : Finset FiniteGraph) {n : ℕ}
    (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

/-- The maximum edge count of a host avoiding every member of a finite family. -/
public noncomputable def familyExtremal (family : Finset FiniteGraph)
    (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (FamilyFree family)).sup
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)

end Foundations

noncomputable section DensityReduction

open Finset SimpleGraph

end DensityReduction

noncomputable section Patterns

open SimpleGraph

end Patterns

noncomputable section Quotients

open Finset SimpleGraph

end Quotients

noncomputable section Geometry

open SimpleGraph

section SymplecticGeometry

variable (K : Type*) [Field K]

end SymplecticGeometry

section NumericalParameters

end NumericalParameters

end Geometry

noncomputable section Cyclicity

open Finset SimpleGraph

end Cyclicity

noncomputable section CharacteristicAvoidance

open SimpleGraph

section PointClass

variable (K : Type*) [Field K]

end PointClass

end CharacteristicAvoidance

noncomputable section SubdivisionLineExtraction

open SimpleGraph

variable (K : Type*) [Field K]

end SubdivisionLineExtraction

noncomputable section Padding

open SimpleGraph

end Padding

noncomputable section LocalGeometry

open SimpleGraph

section FourPathCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

end FourPathCounting

end LocalGeometry

noncomputable section BreadthFirstCounting

open SimpleGraph

section BreadthFirstPaths

variable {V : Type*} [Fintype V] [DecidableEq V]

end BreadthFirstPaths

end BreadthFirstCounting

noncomputable section SubdivisionCounting

open SimpleGraph

section SubdivisionCopies

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

end SubdivisionCopies

end SubdivisionCounting

noncomputable section QuotientWitnesses

open SimpleGraph

end QuotientWitnesses

section CommutativeRing

variable {K : Type*} [CommRing K]

end CommutativeRing

section CharacteristicTwo

variable {K : Type*} [Field K] [CharP K 2]

end CharacteristicTwo

section Field

variable {K : Type*} [Field K]

end Field

noncomputable section Separation

open Filter Finset SimpleGraph
open scoped Topology

private def extremalScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((4 : ℝ) / 3)

private def FamilyLittleO (family : Finset FiniteGraph) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (familyExtremal family n : ℝ) ≤ ε * extremalScale n

/-- Every member of a forbidden family has a uniform extremal-number lower bound. -/
public def UniformMemberLower (family : Finset FiniteGraph) (c : ℝ) : Prop :=
  ∀ forbidden ∈ family,
    ∀ᶠ n : ℕ in atTop,
      c * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ)

private structure SeparationCertificate (family : Finset FiniteGraph) where
  lowerConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  family_littleO : FamilyLittleO family
  member_lower : UniformMemberLower family lowerConstant

end Separation

noncomputable section Supersaturation

open Finset SimpleGraph

section FiniteHeavyFibers

end FiniteHeavyFibers

section ActualFourPathFibers

variable {V : Type*} [Fintype V] [DecidableEq V]

end ActualFourPathFibers

section ActualThetaExtensions

variable {V : Type*} [Fintype V] [DecidableEq V]

end ActualThetaExtensions

section ActualCommonCenterTriples

variable {V : Type*} [Fintype V] [DecidableEq V]

end ActualCommonCenterTriples

section CubicBinomialSupersaturation

end CubicBinomialSupersaturation

section ActualTripleSupersaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

end ActualTripleSupersaturation

section OrderedThetaTripleCounting

end OrderedThetaTripleCounting

section ActualGammaAndKForcing

variable {V : Type*} [Fintype V] [DecidableEq V]

end ActualGammaAndKForcing

section ActualBadVertexEdgeCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

end ActualBadVertexEdgeCounting

end Supersaturation

noncomputable section BadVertexCounting

open Finset SimpleGraph

section ActualIndependentTriples

variable {V : Type*} [Fintype V] [DecidableEq V]

end ActualIndependentTriples

end BadVertexCounting

noncomputable section TripleMassIncidence

open Finset SimpleGraph

section TripleIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]

end TripleIncidence

end TripleMassIncidence

noncomputable section QuantitativeBadVertexBound

open Finset SimpleGraph

end QuantitativeBadVertexBound

noncomputable section LineCoordinates

variable (K : Type*) [Field K]

section CharacteristicTwo

variable [CharP K 2] [Finite K]

end CharacteristicTwo

end LineCoordinates

noncomputable section ArbitraryLineNormalization

open SimpleGraph

variable (K : Type*) [Field K]

end ArbitraryLineNormalization

noncomputable section JQuotientAvoidanceReduction

open SimpleGraph

end JQuotientAvoidanceReduction

noncomputable section JTemplateLineAvoidanceReduction

open SimpleGraph

variable (K : Type*) [Field K]

end JTemplateLineAvoidanceReduction

noncomputable section CharacteristicTwoLineAvoidance

open SimpleGraph

variable (K : Type*) [Field K] [CharP K 2] [Finite K]

end CharacteristicTwoLineAvoidance

noncomputable section UpperBoundReduction

open Filter Finset SimpleGraph
open scoped Topology

end UpperBoundReduction

noncomputable section AsymptoticExtraction

open Filter Finset SimpleGraph
open scoped Topology

end AsymptoticExtraction

noncomputable section CycleBounds

open Filter Finset SimpleGraph
open scoped Topology

end CycleBounds

noncomputable section Counterexample

open SimpleGraph

end Counterexample

noncomputable section Connectedness

open Finset SimpleGraph

end Connectedness

noncomputable section Bipartiteness

open Finset SimpleGraph

end Bipartiteness

noncomputable section FamilyExtremal

open Finset SimpleGraph

end FamilyExtremal

noncomputable section MainTheorem

open Finset SimpleGraph

end MainTheorem

end CompactnessConjecture
