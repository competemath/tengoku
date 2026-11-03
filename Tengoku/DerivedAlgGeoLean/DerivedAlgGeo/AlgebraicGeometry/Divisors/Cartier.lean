/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.AlgebraicGeometry.OrderOfVanishing
import Tengoku.Seed.GroupTheory.QuotientGroup.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cartier divisors on an integral scheme

This file defines Cartier divisors without inventing a meromorphic-function sheaf that Mathlib
does not yet have. For an integral scheme `X`, the function field `K(X)` is upstream. At a point
`x`, the local Cartier group is

`K(X)ˣ / 𝒪_{X,x}ˣ`,

where local units enter `K(X)ˣ` through the canonical map from the stalk. A Cartier divisor is a
section of these stalkwise quotients that is locally represented by one nonzero rational
function. This is the usual local-equations definition of a Cartier divisor on an integral
scheme, expressed without a sheaf quotient.

The construction provides:

* the abelian group `Scheme.CartierDivisor X`;
* principal divisors and the explicit quotient `CartierDivisor.ClassGroup X`;
* codimension-one coefficients through Mathlib's `Scheme.ord`;
* pullback from explicit function-field data that carries local units to local units.

## Deliberate boundaries

Mathlib v4.32.1 does not construct a function-field map for an arbitrary morphism of integral
schemes, so this file does not claim an unconditional pullback. `CartierPullbackData` states the
exact missing hypotheses. Likewise, `coefficient` is not packaged as an `AlgebraicCycle`: the
upstream order-of-vanishing API does not yet prove local finiteness of its support. No cycle
infrastructure is duplicated here.
-/

open Additive CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

section LocalClasses

variable (X : Scheme.{u}) [IsIntegral X]

/-- Units in the local ring at `x`, viewed as units of the function field.-/
def localUnitHom (x : X) : (X.presheaf.stalk x)ˣ →* X.functionFieldˣ :=
  Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom

/-- Rational functions that are units in the local ring at `x`, in additive notation.-/
def localUnits (x : X) : AddSubgroup (Additive X.functionFieldˣ) :=
  (localUnitHom X x).range.toAddSubgroup

/-- A germ of a Cartier divisor at `x`: a rational function modulo local units.-/
abbrev LocalCartierClass (x : X) := Additive X.functionFieldˣ ⧸ localUnits X x

/-- The local Cartier class of a nonzero rational function.-/
def localCartierClass (x : X) : Additive X.functionFieldˣ →+ LocalCartierClass X x :=
  QuotientAddGroup.mk' (localUnits X x)

/--
@isnad1 id=eq.0h2v.s9.567f05741809 from=translated src=- shape=2b257445 vocab=c7fff1c2
-/
@[simp]
lemma localCartierClass_zero (x : X) : localCartierClass X x 0 = 0 :=
  map_zero _

/--
@isnad1 id=eq.0h4v.s10.ed8277ff0321 from=translated src=- shape=38fed95b vocab=d283fc70
-/
@[simp]
lemma localCartierClass_add (x : X) (f g : Additive X.functionFieldˣ) :
    localCartierClass X x (f + g) =
      localCartierClass X x f + localCartierClass X x g :=
  map_add _ _ _

/-- Two local equations give the same germ precisely when their quotient is a local unit.
@isnad1 id=iff.0h4v.s10.16f0258a7c24 from=translated src=- shape=defbf621 vocab=ca864be0
-/
lemma localCartierClass_eq_iff (x : X) (f g : Additive X.functionFieldˣ) :
    localCartierClass X x f = localCartierClass X x g ↔ f - g ∈ localUnits X x :=
  QuotientAddGroup.eq_iff_sub_mem

end LocalClasses

section Divisors

variable (X : Scheme.{u}) [IsIntegral X]

/-- A family of local Cartier classes is Cartier when it is locally represented by a single
nonzero rational function.-/
def IsCartier (D : ∀ x : X, LocalCartierClass X x) : Prop :=
  ∀ x, ∃ U : X.Opens, x ∈ U ∧ ∃ f : Additive X.functionFieldˣ,
    ∀ y, y ∈ U → D y = localCartierClass X y f

/--
@isnad1 id=iscartie.0h1v.s7.4d4781108b27 from=translated src=- shape=1940ab29 vocab=61dbd711
-/
lemma isCartier_zero : IsCartier X 0 := by
  intro x
  refine ⟨⊤, Set.mem_univ x, 0, ?_⟩
  intro y hy
  simp

/--
@isnad1 id=iscartie.2h3v.s7.80bd0f25c5fd from=translated src=- shape=d39e74e4 vocab=82ab1425
-/
lemma IsCartier.add {D E : ∀ x : X, LocalCartierClass X x}
    (hD : IsCartier X D) (hE : IsCartier X E) : IsCartier X (D + E) := by
  intro x
  obtain ⟨U, hxU, f, hf⟩ := hD x
  obtain ⟨V, hxV, g, hg⟩ := hE x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, f + g, ?_⟩
  intro y hy
  rw [Pi.add_apply, hf y hy.1, hg y hy.2, localCartierClass_add]

/--
@isnad1 id=iscartie.1h2v.s7.ea41ebfc72b4 from=translated src=- shape=f707b46e vocab=e8a131a1
-/
lemma IsCartier.neg {D : ∀ x : X, LocalCartierClass X x}
    (hD : IsCartier X D) : IsCartier X (-D) := by
  intro x
  obtain ⟨U, hxU, f, hf⟩ := hD x
  refine ⟨U, hxU, -f, ?_⟩
  intro y hy
  rw [Pi.neg_apply, hf y hy, map_neg]

/-- The additive subgroup of locally representable families: Cartier divisors on `X`.-/
def cartierDivisor : AddSubgroup (∀ x : X, LocalCartierClass X x) where
  carrier := IsCartier X
  zero_mem' := isCartier_zero X
  add_mem' := IsCartier.add X
  neg_mem' := IsCartier.neg X

/-- Cartier divisors on an integral scheme.-/
abbrev CartierDivisor := cartierDivisor X

namespace CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

/-- Cartier divisors are equal when all of their local classes are equal.
@isnad1 id=eq.1h3v.s11.b8434e88f3d1 from=translated src=- shape=aec5ec51 vocab=6b7de271
-/
@[ext]
lemma ext {D E : CartierDivisor X} (h : ∀ x, D.1 x = E.1 x) : D = E :=
  Subtype.ext (funext h)

/--
@isnad1 id=eq.0h2v.s10.5f83e5ce3489 from=translated src=- shape=aea42301 vocab=6b7de271
-/
@[simp]
lemma zero_apply (x : X) : (0 : CartierDivisor X).1 x = 0 :=
  rfl

/--
@isnad1 id=eq.0h4v.s12.8b5f2e769c26 from=translated src=- shape=528d4d2f vocab=d4a27140
-/
@[simp]
lemma add_apply (D E : CartierDivisor X) (x : X) : (D + E).1 x = D.1 x + E.1 x :=
  rfl

/--
@isnad1 id=eq.0h3v.s11.d7c958571dca from=translated src=- shape=9656f0bb vocab=c3843500
-/
@[simp]
lemma neg_apply (D : CartierDivisor X) (x : X) : (-D).1 x = -D.1 x :=
  rfl

/-- Every Cartier divisor admits a rational local equation around every point.
@isnad1 id=ex.0h3v.s10.ccef82e84b0c from=translated src=- shape=0c2e9957 vocab=bdcf5191
-/
lemma exists_localEquation (D : CartierDivisor X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ f : Additive X.functionFieldˣ,
      ∀ y, y ∈ U → D.1 y = localCartierClass X y f :=
  D.2 x

/-- Principal Cartier divisors, as an additive homomorphism from the multiplicative function
field written additively.-/
def principal (X : Scheme.{u}) [IsIntegral X] :
    Additive X.functionFieldˣ →+ CartierDivisor X where
  toFun f := ⟨fun x ↦ localCartierClass X x f, by
    intro x
    exact ⟨⊤, Set.mem_univ x, f, fun y _ ↦ rfl⟩⟩
  map_zero' := by ext; simp
  map_add' f g := by ext; simp

/-- The principal divisor attached to a nonzero rational function.-/
def ofRationalFunction (X : Scheme.{u}) [IsIntegral X] (f : X.functionFieldˣ) :
    CartierDivisor X :=
  principal X (.ofMul f)

/-- The subgroup of principal Cartier divisors.-/
def principalDivisors (X : Scheme.{u}) [IsIntegral X] : AddSubgroup (CartierDivisor X) :=
  (principal X).range

/--
@isnad1 id=normal.0h1v.s9.d6a11dfd5ea5 from=translated src=- shape=0aa5af32 vocab=a8ea64c5
-/
instance principalDivisors_normal (X : Scheme.{u}) [IsIntegral X] :
    (principalDivisors X).Normal := by
  refine ⟨?_⟩
  intro n hn g
  rw [add_comm g n, add_assoc, add_neg_cancel, add_zero]
  exact hn

/-- Cartier divisor classes: Cartier divisors modulo principal equivalence.-/
abbrev ClassGroup (X : Scheme.{u}) [IsIntegral X] :=
  CartierDivisor X ⧸ principalDivisors X

/-- The quotient map from Cartier divisors to Cartier divisor classes.-/
def toClass (X : Scheme.{u}) [IsIntegral X] : CartierDivisor X →+ ClassGroup X :=
  QuotientAddGroup.mk' (principalDivisors X)

/-- The quotient relation defining Cartier divisor classes.
@isnad1 id=iff.0h3v.s14.3c40f0d9f9d0 from=translated src=- shape=0f565aeb vocab=c978611c
-/
theorem toClass_eq_iff (D E : CartierDivisor X) :
    toClass X D = toClass X E ↔ D - E ∈ principalDivisors X :=
  QuotientAddGroup.eq_iff_sub_mem

/-- Explicit principal-equivalence form of the quotient relation.
@isnad1 id=iff.0h3v.s14.7865a1c3b711 from=translated src=- shape=14699de8 vocab=561327e0
-/
theorem toClass_eq_iff_exists (D E : CartierDivisor X) :
    toClass X D = toClass X E ↔
      ∃ f : Additive X.functionFieldˣ, principal X f = D - E := by
  rw [toClass_eq_iff]
  exact AddMonoidHom.mem_range

/--
@isnad1 id=eq.0h2v.s13.7fe4c733d5c7 from=translated src=- shape=f5b722b9 vocab=f8502ab6
-/
@[simp]
theorem toClass_principal (f : Additive X.functionFieldˣ) :
    toClass X (principal X f) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨f, rfl⟩

section Order

variable [IsLocallyNoetherian X]

/-- Order of vanishing of nonzero rational functions, as an additive homomorphism.-/
def ordUnitHom (x : X) : Additive X.functionFieldˣ →+ ℤ where
  toFun f := X.ord (f.toMul : X.functionField) x
  map_zero' := by
    change X.ord (1 : X.functionField) x = 0
    by_cases hx : coheight x = 1
    · rw [Scheme.ord_eq_iff hx one_ne_zero]
      simp
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hx 1
  map_add' f g := by
    change X.ord ((f.toMul * g.toMul : X.functionFieldˣ) : X.functionField) x = _
    exact Scheme.ord_mul f.toMul.ne_zero g.toMul.ne_zero

/--
@isnad1 id=eq.1h3v.s9.e5f28c9f5c3c from=translated src=- shape=027f1171 vocab=f7bb467f
-/
lemma ordUnitHom_eq_zero_of_mem_localUnits (x : X) (f : Additive X.functionFieldˣ)
    (hf : f ∈ localUnits X x) : ordUnitHom x f = 0 := by
  obtain ⟨u, rfl⟩ := hf
  change X.ord
    ((Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u :
      X.functionFieldˣ) : X.functionField) x = 0
  by_cases hx : coheight x = 1
  · rw [Scheme.ord_eq_iff hx]
    · letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
        krullDimLE_of_coheight_le hx.le
      change Ring.ordFrac (X.presheaf.stalk x)
        (algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x)) = 1
      exact Ring.ordFrac_of_isUnit u.isUnit
    · simp
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

/-- Order of vanishing descends to a local Cartier class because local units have order zero.-/
def localOrder (x : X) : LocalCartierClass X x →+ ℤ :=
  QuotientAddGroup.lift (localUnits X x) (ordUnitHom x)
    (ordUnitHom_eq_zero_of_mem_localUnits x)

/--
@isnad1 id=eq.0h3v.s10.161cd853066e from=translated src=- shape=19dbd143 vocab=6088cca2
-/
@[simp]
lemma localOrder_localCartierClass (x : X) (f : Additive X.functionFieldˣ) :
    localOrder x (localCartierClass X x f) = X.ord (f.toMul : X.functionField) x :=
  rfl

/-- The codimension-one coefficient of a Cartier divisor. At other points this uses the upstream
junk value `0` of `Scheme.ord`.-/
def coefficient (D : CartierDivisor X) (x : X) : ℤ :=
  localOrder x (D.1 x)

/--
@isnad1 id=eq.0h4v.s11.d005abba17ef from=translated src=- shape=d78b5a0c vocab=429b072a
-/
@[simp]
lemma coefficient_add (D E : CartierDivisor X) (x : X) :
    coefficient (D + E) x = coefficient D x + coefficient E x :=
  map_add (localOrder x) (D.1 x) (E.1 x)

/--
@isnad1 id=eq.0h3v.s12.fe91e0d4fc63 from=translated src=- shape=5ff4dc17 vocab=d4c58f0d
-/
@[simp]
lemma coefficient_principal (f : Additive X.functionFieldˣ) (x : X) :
    coefficient (principal X f) x = X.ord (f.toMul : X.functionField) x :=
  rfl

/--
@isnad1 id=eq.1h3v.s9.94884bf980bd from=translated src=- shape=2adf8041 vocab=1722e317
-/
lemma coefficient_eq_zero_of_coheight_ne_one (D : CartierDivisor X) (x : X)
    (hx : coheight x ≠ 1) : coefficient D x = 0 := by
  obtain ⟨U, hxU, f, hf⟩ := exists_localEquation D x
  change localOrder x (D.1 x) = 0
  rw [hf x hxU, localOrder_localCartierClass,
    Scheme.ord_eq_zero_of_coheight_neq_one hx]

end Order

end CartierDivisor

end Divisors

section Pullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)

/-- Data sufficient to pull Cartier divisors back along a scheme morphism.

The field map and the condition that it carries local units to local units are explicit because
Mathlib v4.32.1 provides no such map for an arbitrary scheme morphism.-/
structure CartierPullbackData where
  fieldMap : Additive Y.functionFieldˣ →+ Additive X.functionFieldˣ
  map_localUnits : ∀ x, localUnits Y (f x) ≤ (localUnits X x).comap fieldMap

namespace CartierPullbackData

variable (p : CartierPullbackData f)

/-- The induced map on local Cartier classes.-/
def localMap (x : X) : LocalCartierClass Y (f x) →+ LocalCartierClass X x :=
  QuotientAddGroup.map (localUnits Y (f x)) (localUnits X x)
    p.fieldMap (p.map_localUnits x)

/--
@isnad1 id=eq.0h6v.s12.fbd699f3be08 from=translated src=- shape=2e0f4b65 vocab=9f10266f
-/
@[simp]
lemma localMap_localCartierClass (x : X) (g : Additive Y.functionFieldˣ) :
    localMap f p x (localCartierClass Y (f x) g) =
      localCartierClass X x (p.fieldMap g) :=
  rfl

/-- Pullback of Cartier divisors from explicit compatible function-field data.-/
def pullback : CartierDivisor Y →+ CartierDivisor X where
  toFun D := ⟨fun x ↦ localMap f p x (D.1 (f x)), by
    intro x
    obtain ⟨U, hxU, g, hg⟩ := D.2 (f x)
    refine ⟨f ⁻¹ᵁ U, hxU, p.fieldMap g, ?_⟩
    intro y hy
    change localMap f p y (D.1 (f y)) = localCartierClass X y (p.fieldMap g)
    rw [hg (f y) hy, localMap_localCartierClass f p]⟩
  map_zero' := by ext; simp
  map_add' D E := by ext; simp

/--
@isnad1 id=eq.0h5v.s14.09b4202ceaf7 from=translated src=- shape=52416356 vocab=a2483ef1
-/
@[simp]
lemma pullback_principal (g : Additive Y.functionFieldˣ) :
    pullback f p (CartierDivisor.principal Y g) =
      CartierDivisor.principal X (p.fieldMap g) := by
  ext
  rfl

end CartierPullbackData

end Pullback

end

end AlgebraicGeometry.Scheme
