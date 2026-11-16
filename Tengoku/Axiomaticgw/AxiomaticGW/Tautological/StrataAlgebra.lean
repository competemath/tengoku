/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Tautological.StrataModule
public import Tengoku.Seed.LinearAlgebra.BilinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Certified products on the strata module

The strata algebra product is obtained geometrically by enumerating common
refinements of two stable graphs and inserting the excess Chern classes of
the boundary normal bundles. This file records the algebraic contract that
such an enumeration must satisfy. It is intentionally a data structure rather
than an unproved global instance: no product is installed until its
common-refinement calculation supplies bilinearity, grading, symmetry,
associativity, and a unit.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

/-- A certified strata-algebra product in fixed genus and with fixed external
labels. The `product` field is the result of a finite common-refinement and
excess-intersection computation; the remaining fields are its mathematical
checks.-/
structure CertifiedStrataProduct (g : ℕ) (S : Type) [Fintype S] where
  /-- Bilinear product on the free module of decorated strata.-/
  product : StrataModule g S →ₗ[ℚ] StrataModule g S →ₗ[ℚ] StrataModule g S
  /-- Fundamental-class stratum used as the unit.-/
  unit : TautologicalStratum g S
  /-- The product is homogeneous for codimension.-/
  product_degree : ∀ x y,
    product (StrataModule.basis x) (StrataModule.basis y) ∈
      StrataModule.degree (x.codimension + y.codimension)
  /-- The product is commutative.-/
  product_comm : ∀ a b, product a b = product b a
  /-- The product is associative.-/
  product_assoc : ∀ a b c,
    product (product a b) c = product a (product b c)
  /-- The chosen fundamental class is a left unit.-/
  unit_left : ∀ a, product (StrataModule.basis unit) a = a
  /-- The chosen fundamental class is a right unit.-/
  unit_right : ∀ a, product a (StrataModule.basis unit) = a
  /-- The unit is in codimension zero.-/
  unit_degree : unit.codimension = 0

namespace CertifiedStrataProduct

variable {g : ℕ} {S : Type} [Fintype S]

/--
@isnad1 id=mem.0h5v.s9.14983bd3cca1 from=translated src=- shape=5a7fe539 vocab=a579da27
-/
theorem product_degree_basis (P : CertifiedStrataProduct g S)
    (x y : TautologicalStratum g S) :
    P.product (StrataModule.basis x) (StrataModule.basis y) ∈
      StrataModule.degree (x.codimension + y.codimension) :=
  P.product_degree x y

/--
@isnad1 id=eq.0h5v.s10.18ca8f3eef7b from=translated src=- shape=d7db7fa2 vocab=b428dc3d
-/
theorem comm (P : CertifiedStrataProduct g S)
    (a b : StrataModule g S) : P.product a b = P.product b a :=
  P.product_comm a b

/--
@isnad1 id=eq.0h6v.s11.ccb82dd6b95f from=translated src=- shape=0b823295 vocab=b428dc3d
-/
theorem assoc (P : CertifiedStrataProduct g S)
    (a b c : StrataModule g S) :
    P.product (P.product a b) c = P.product a (P.product b c) :=
  P.product_assoc a b c

/--
@isnad1 id=eq.0h4v.s9.f4ec451f5c67 from=translated src=- shape=2de9b40b vocab=7ee09729
-/
@[simp]
theorem left_unit (P : CertifiedStrataProduct g S) (a : StrataModule g S) :
    P.product (StrataModule.basis P.unit) a = a :=
  P.unit_left a

/--
@isnad1 id=eq.0h4v.s9.b2ddc7b0f16c from=translated src=- shape=bc1e4587 vocab=7ee09729
-/
@[simp]
theorem right_unit (P : CertifiedStrataProduct g S) (a : StrataModule g S) :
    P.product a (StrataModule.basis P.unit) = a :=
  P.unit_right a

end CertifiedStrataProduct

/-- A submodule is a two-sided product ideal for a certified strata product.
This is the exact condition needed before the algebra product can descend to
a quotient by known tautological relations.-/
structure ProductIdeal {g : ℕ} {S : Type} [Fintype S]
    (P : CertifiedStrataProduct g S)
    (relations : Submodule ℚ (StrataModule g S)) : Prop where
  left_mem : ∀ {r}, r ∈ relations → ∀ a, P.product r a ∈ relations
  right_mem : ∀ {r}, r ∈ relations → ∀ a, P.product a r ∈ relations

end AxiomaticGW
