/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Vertex.HVertexOperator
public import Tengoku.Seed.Data.Int.Interval

/-!
# Vertex operators

In this file we introduce vertex operators as linear maps to Laurent series.

## Definitions
* `VertexOperator` is an `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
* `VertexOperator.ncoeff` is the coefficient of a vertex operator under normalized indexing.

## TODO
* `HasseDerivative` : A divided-power derivative.
* `Locality` : A weak form of commutativity.
* `Residue products` : A family of products on `VertexOperator R V` parametrized by integers.

## References
* [G. Mason, *Vertex rings and Pierce bundles*][mason2017]
* [A. Matsuo, K. Nagatomo, *On axioms for a vertex algebra and locality of quantum
  fields*][matsuo1997]
-/

@[expose] public section

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to
Laurent series with coefficients in `V`.  We write this as a specialization of the heterogeneous
case. -/
abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] := HVertexOperator ℤ R V V

namespace VertexOperator

open HVertexOperator

/--
@isnad1 id=eq.1h4v.s9.1eb2c688f1b5 from=seed src=0 shape=4d2f2866 vocab=974daac5
-/
@[ext]
theorem ext (A B : VertexOperator R V) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

/-- The coefficient of a vertex operator under normalized indexing. -/
def ncoeff : VertexOperator R V →ₗ[R] ℤ → Module.End R V where
  toFun A n := HVertexOperator.coeff A (-n - 1)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/--
@isnad1 id=eq.0h4v.s11.0463c51d605d from=seed src=0 shape=2baf9162 vocab=d52bad2f
-/
theorem ncoeff_apply (A : VertexOperator R V) (n : ℤ) : ncoeff A n = coeff A (-n - 1) :=
  rfl

/-- In the literature, the `n`th normalized coefficient of a vertex operator `A` is written as
either `Aₙ` or `A(n)`. -/
scoped[VertexOperator] notation A "[[" n "]]" => ncoeff A n

/--
@isnad1 id=eq.0h4v.s11.b091fc15e180 from=seed src=0 shape=5adb1b56 vocab=d52bad2f
-/
@[simp]
theorem coeff_eq_ncoeff (A : VertexOperator R V)
    (n : ℤ) : HVertexOperator.coeff A n = A[[-n - 1]] := by
  rw [ncoeff_apply, neg_sub, Int.sub_neg, add_sub_cancel_left]

/--
@isnad1 id=eq.1h5v.s11.c360be1d128c from=seed src=0 shape=bfe99713 vocab=af24e263
-/
theorem ncoeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : -n - 1 < HahnSeries.order ((HahnModule.of R).symm (A x))) : (A[[n]]) x = 0 := by
  simp only [ncoeff, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

/--
@isnad1 id=eq.1h5v.s11.bc6d29466f4a from=seed src=0 shape=96217ca5 vocab=7805af85
-/
theorem coeff_eq_zero_of_lt_order (A : VertexOperator R V) (n : ℤ) (x : V)
    (h : n < HahnSeries.order ((HahnModule.of R).symm (A x))) : coeff A n x = 0 := by
  rw [coeff_eq_ncoeff, ncoeff_eq_zero_of_lt_order A (-n - 1) x]
  lia

/-- Given an endomorphism-valued function on integers satisfying a pointwise bounded-pole condition,
we produce a vertex operator. -/
noncomputable def of_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x, BddBelow (Function.support fun y ↦ f y x)) : VertexOperator R V :=
  HVertexOperator.of_coeff f fun x ↦ (BddBelow.isWF (hf x)).isPWO

/--
@isnad1 id=eq.1h5v.s10.389ec8c79ba4 from=seed src=0 shape=93e25796 vocab=edf75750
-/
@[simp]
theorem of_coeff_apply_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x, BddBelow (Function.support fun y ↦ f y x)) (x : V) (n : ℤ) :
    ((HahnModule.of R).symm ((of_coeff f hf) x)).coeff n = (f n) x := by
  rfl

/--
@isnad1 id=eq.1h4v.s10.97f92c0d476f from=seed src=0 shape=ab978a4a vocab=7aec941b
-/
@[simp]
theorem ncoeff_of_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x, BddBelow (Function.support fun y ↦ f y x)) (n : ℤ) :
    (of_coeff f hf)[[n]] = f (-n - 1) := by
  ext v
  rw [ncoeff_apply, coeff_apply_apply, of_coeff_apply_coeff]

end VertexOperator
