/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Tengoku.Seed.AlgebraicGeometry.Geometrically.Irreducible
import Tengoku.Seed.AlgebraicGeometry.Fiber
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.RingTheory.Jacobson.Ring
import Tengoku.Seed.RingTheory.TensorProduct.Nontrivial
import Tengoku.Seed.RingTheory.TensorProduct.Free
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.LinearAlgebra.TensorProduct.Finiteness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric irreducibility over an algebraically closed field

An irreducible scheme over an algebraically closed field remains irreducible
after extension of the base field. Affine algebra arguments and local affine
charts supply the comparison.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace IsAlgClosed
open _root_.IsAlgClosed
namespace BaseChangeIrreducible
open _root_.IsAlgClosed

section FiniteType

variable {K : Type u} [Field K]

/--
@isnad1 id=bijectiv.0h3v.s7.99e9b7680962 from=translated src=- shape=dd9a6330 vocab=13027893
-/
theorem algebraMap_quotient_bijective [IsAlgClosed K] {A : Type v} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    Function.Bijective (algebraMap K (A ⧸ m)) := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  have : Algebra.IsIntegral K (A ⧸ m) := inferInstance
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

variable (K) in
/-- The `K`-valued point obtained by identifying the residue field of a maximal ideal with `K`.-/
noncomputable def pointOfMaximal [IsAlgClosed K] {A : Type v} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] : A →ₐ[K] K :=
  let e := RingEquiv.ofBijective (algebraMap K (A ⧸ m)) (algebraMap_quotient_bijective m)
  { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
    commutes' := fun k => by
      change e.symm (Ideal.Quotient.mk m (algebraMap K A k)) = k
      rw [Ideal.Quotient.mk_algebraMap]
      exact e.symm_apply_apply k }

/--
@isnad1 id=iff.0h4v.s7.e5fa2bf8ed48 from=translated src=- shape=f8353326 vocab=fce3b937
-/
theorem pointOfMaximal_eq_zero_iff [IsAlgClosed K] {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] (a : A) :
    pointOfMaximal K m a = 0 ↔ a ∈ m := by
  change (RingEquiv.ofBijective (algebraMap K (A ⧸ m))
    (algebraMap_quotient_bijective m)).symm (Ideal.Quotient.mk m a) = 0 ↔ a ∈ m
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

end FiniteType

section Fields

variable (k : Type u) [Field k] [IsAlgClosed k]

end Fields

section Schemes

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (K : Type u) [Field K] [Algebra k K]

end Schemes

end IsAlgClosed.BaseChangeIrreducible

end GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
