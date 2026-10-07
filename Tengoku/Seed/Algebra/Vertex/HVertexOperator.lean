/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.RingTheory.HahnSeries.Multiplication

/-!
# Vertex operators

In this file we introduce heterogeneous vertex operators using Hahn series.  When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of "meromorphic left-moving 2D field".  The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.

## Definitions
* `HVertexOperator` : An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* The coefficient function as an `R`-linear map.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.

## Main results
* Ext

## TODO
* curry for tensor product inputs
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials.

## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]

-/

@[expose] public section

assert_not_exists Cardinal

noncomputable section

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`. -/
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace HVertexOperator

section Coeff

open HahnModule

/--
@isnad1 id=eq.1h6v.s9.e2d96e5934dd from=seed src=0 shape=2ded834c vocab=a935dd48
-/
@[ext]
theorem ext (A B : HVertexOperator Γ R V W) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

set_option backward.isDefEq.respectTransparency false in
/-- The coefficients of a heterogeneous vertex operator, viewed as a linear map to formal power
series with coefficients in linear maps. -/
@[simps]
def coeff : HVertexOperator Γ R V W →ₗ[R] Γ → V →ₗ[R] W where
  toFun A n := {
    toFun v := ((of R).symm (A v)).coeff n
    map_add' u v := by simp
    map_smul' r v := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/--
@isnad1 id=ispwo.0h6v.s10.3664050a9174 from=seed src=0 shape=2cfa3b50 vocab=8120f610
-/
theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO :=
  ((of R).symm (A v)).isPWO_support'

/--
@isnad1 id=injectiv.0h4v.s10.cc6ccae3e2ae from=seed src=0 shape=ad4b2fb9 vocab=b3184766
-/
@[ext]
theorem coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W →ₗ[R] Γ → (V →ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

set_option backward.isDefEq.respectTransparency false in
/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
def of_coeff (f : Γ → V →ₗ[R] W) (hf : ∀ (x : V), (Function.support (f · x)).IsPWO) :
    HVertexOperator Γ R V W where
  toFun x := (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/--
@isnad1 id=eq.1h5v.s10.6e7967fc6756 from=seed src=0 shape=2c9d03e4 vocab=8c751840
-/
@[simp]
theorem coeff_of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀ (x : V), (Function.support (fun g => f g x)).IsPWO) : (of_coeff f hf).coeff = f :=
  rfl

/--
@isnad1 id=eq.0h5v.s10.bc7e1b1776c1 from=seed src=0 shape=41a1d1ec vocab=f009e4ee
-/
@[simp]
theorem of_coeff_coeff (A : HVertexOperator Γ R V W) : of_coeff A.coeff A.coeff_isPWOsupport = A :=
  rfl

end Coeff

section Products

variable {Γ Γ' : Type*} [PartialOrder Γ] [PartialOrder Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)

open HahnModule

set_option backward.isDefEq.respectTransparency false in
/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
series. -/
@[simps]
def compHahnSeries (u : U) : HahnSeries Γ' (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp only [coeff_apply_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    intro g' hg' hAB
    exact hg' (by simp [hAB])

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h10v.s8.e9e3911dd685 from=seed src=0 shape=2d903cb0 vocab=15898a04
-/
@[simp]
theorem compHahnSeries_add (u v : U) :
    compHahnSeries A B (u + v) = compHahnSeries A B u + compHahnSeries A B v := by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply_apply, HahnSeries.coeff_add', Pi.add_apply]
  rw [← HahnSeries.coeff_add]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h10v.s8.0a54592ca765 from=seed src=0 shape=21c054c0 vocab=cbc5bec4
-/
@[simp]
theorem compHahnSeries_smul (r : R) (u : U) :
    compHahnSeries A B (r • u) = r • compHahnSeries A B u := by
  ext
  simp only [compHahnSeries_coeff, map_smul, coeff_apply_apply, HahnSeries.coeff_smul]
  rw [← HahnSeries.coeff_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The composite of two heterogeneous vertex operators, as a heterogeneous vertex operator. -/
@[simps]
def comp : HVertexOperator (Γ' ×ₗ Γ) R U W where
  toFun u := HahnModule.of R (HahnSeries.ofIterate (compHahnSeries A B u))
  map_add' := by
    intro u v
    ext g
    simp [HahnSeries.ofIterate]
  map_smul' := by
    intro r x
    ext g
    simp [HahnSeries.ofIterate]

/--
@isnad1 id=eq.0h9v.s12.4cd8c862cdeb from=seed src=0 shape=c880bfa3 vocab=aaedc9bf
-/
@[simp]
theorem coeff_comp (g : Γ' ×ₗ Γ) :
    (comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl

end Products

end HVertexOperator
