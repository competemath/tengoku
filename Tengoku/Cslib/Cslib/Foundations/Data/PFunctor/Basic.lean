/-
Copyright (c) 2026 Fabrizio Montesi, PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Devon Tuma, Quang Dao
-/

module

public import Tengoku.Cslib.Cslib.Init
public import Tengoku.Seed.Data.PFunctor.Univariate.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial Functors

Definitions of common `PFunctor` constructions:
- `monomial A B`: constant direction `B` for any shape `a : A`
- `P + Q`: shapes are a disjoint sum, directions are defined by sum elimination on `a : P.A ⊕ Q.A`
- `P * Q`: shapes are pairs of underlying shapes, directions are a disjoint sum over both shapes.

Special cases `C`, `linear`, `selfMonomial`, `purePower`, the indeterminate `y`,
and canonical choices of `0` and `1` are defined as abbreviations or instances over `monomial`.
The scoped notations `A y^ B` and `y^ B` denote `monomial A B` and `purePower B`, respectively.

The child-map API includes `const`, `Unary`, and `DecidableEqChildren`.
-/

@[expose] public section

universe uA uB uA₁ uA₂ uB₁ uB₂

namespace PFunctor

/-- Two polynomial functors are equal if their head types are equal and their child types
agree over that equality.
@isnad1 id=eq.2h2v.s5.01d075d66d47 from=translated src=- shape=e1041972 vocab=cf6aac7c
-/
@[ext (iff := false)]
theorem ext {P Q : PFunctor.{uA, uB}} (h : P.A = Q.A) (h' : ∀ a, P.B a = Q.B (h ▸ a)) :
    P = Q := by
  cases P; cases Q; simp only [mk.injEq] at h h' ⊢; subst h
  simp_all only [heq_eq_eq, true_and]; funext; exact h' _

/-- The constant child map for `a`.-/
def const {P : PFunctor} (a : P.A) (x : α) : P.B a → α := fun _ => x

/--
@isnad1 id=eq.0h5v.s4.ebfe82b1f8d7 from=translated src=- shape=399dfa21 vocab=42ecc290
-/
@[simp, scoped grind =]
theorem const_apply {P : PFunctor} (a : P.A) (x : α) (i : P.B a) : PFunctor.const a x i = x := rfl

section monomial

/-- The monomial `PFunctor` with head type `A` and constant `B` for any `a : A`.-/
abbrev monomial (A : Type uA) (B : Type uB) : PFunctor := ⟨A, fun _ => B⟩

@[inherit_doc] scoped[PFunctor] infixr:82 " y^ " => monomial

/--
@isnad1 id=eq.0h2v.s3.8e0ccda694fc from=translated src=- shape=1043f9b7 vocab=2070a3ee
-/
lemma monomial_A (A : Type uA) (B : Type uB) : (monomial A B).A = A := rfl

/--
@isnad1 id=eq.0h3v.s4.2b3b9dd027fe from=translated src=- shape=276eeb17 vocab=15a8ca62
-/
lemma monomial_B (A : Type uA) (B : Type uB) (a : (monomial A B).A) :
    (monomial A B).B a = B := rfl

end monomial

section zero

/-- The zero polynomial functor, defined as `A = PEmpty` and `B _ = PEmpty`, is the identity with
respect to sum (up to equivalence).-/
@[simps] instance instZeroPFunctor : Zero PFunctor where zero := monomial PEmpty PEmpty

-- The head type is independent of the child universe. Fixing it to `0` avoids an
-- unconstrained universe metavariable when these head instances are synthesized.

end zero

section one

/-- The unit polynomial functor, defined as `A = PUnit` and `B _ = PEmpty`, is the identity with
respect to product (up to equivalence).-/
@[simps] instance instOnePFunctor : One PFunctor where one := monomial PUnit PEmpty

instance instUniqueOneA : Unique (1 : PFunctor.{uA, 0}).A := inferInstanceAs (Unique PUnit)

end one

/-- The constant polynomial functor `P(y) = A y^ PEmpty = A`.-/
abbrev C (A : Type uA) : PFunctor := monomial A PEmpty

/-- The linear polynomial functor `P(y) = A y`.-/
abbrev linear (A : Type uA) : PFunctor := monomial A PUnit

/-- The self-monomial polynomial functor `P(y) = S y^ S`.-/
abbrev selfMonomial (S : Type uA) : PFunctor.{uA, uA} := monomial S S

/-- The pure-power polynomial functor `y^ B`, representable on `B`.-/
abbrev purePower (B : Type uB) : PFunctor := monomial PUnit B

@[inherit_doc purePower] scoped[PFunctor] notation:100 "y^" B:100 => purePower B

/-- The indeterminate polynomial functor `P(y) = y`, the identity with respect to
composition and tensor product (up to equivalence).-/
abbrev y : PFunctor := monomial PUnit PUnit

/- Note: no explicit `IsEmpty`/`Unique` instances are needed for the positions and directions
of the abbreviations above: being reducible, they unfold to `PEmpty`/`PUnit` during instance
search. Only `0` and `1` need the explicit instances above, since the `Zero`/`One` instance
projections are not reducible. -/

/--
@isnad1 id=eq.0h0v.s3.4e127da115ec from=translated src=- shape=b0ae1d2b vocab=9f70a322
-/
@[simp] lemma C_pempty : C PEmpty = 0 := rfl

/--
@isnad1 id=eq.0h0v.s3.eb9b031d8d1c from=translated src=- shape=b0ae1d2b vocab=12fe5310
-/
@[simp] lemma C_punit : C PUnit = 1 := rfl

/--
@isnad1 id=eq.0h0v.s2.5552e83e35bc from=translated src=- shape=4b736592 vocab=ef03c7e6
-/
@[simp] lemma linear_punit : linear PUnit = y := rfl

/--
@isnad1 id=eq.0h0v.s2.a394ef707873 from=translated src=- shape=4b736592 vocab=c8588e19
-/
@[simp] lemma selfMonomial_punit : selfMonomial PUnit = y := rfl

/--
@isnad1 id=eq.0h0v.s2.8c7f12ad3f60 from=translated src=- shape=4b736592 vocab=2515e290
-/
@[simp] lemma purePower_punit : purePower PUnit = y := rfl

section add

/-- The sum of two polynomial functors `P` and `Q`, written as `P + Q`,
defined as the sum of the head types and the dependent sum recursor for the child types.

The child universes must agree. The named spelling `P.add Q` can elaborate in contexts where
`P + Q` fails to infer universes, such as under `PFunctor.W`; see `CslibTests.PFunctor`.-/
@[implicit_reducible] def add (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    PFunctor.{max uA₁ uA₂, uB} :=
  ⟨P.A ⊕ Q.A, @Sum.rec P.A Q.A (fun _ => Type uB) P.B Q.B⟩

@[simps!] instance instHAddPFunctor :
    HAdd PFunctor.{uA₁, uB} PFunctor.{uA₂, uB} PFunctor.{max uA₁ uA₂, uB} where
  hAdd := add

/- Both named operations and arithmetic notation are available; `simp` normalizes to the
notation, for both addition and multiplication. -/
/--
@isnad1 id=eq.0h2v.s4.6448ce59df44 from=translated src=- shape=895a5e7f vocab=51876ea3
-/
@[simp] lemma add_eq_add (P : PFunctor.{uA₁, uB}) (Q : PFunctor.{uA₂, uB}) :
    P.add Q = P + Q := rfl

end add

section prod

/-- The product of two polynomial functors `P` and `Q`, written as `P * Q`,
defined as the product of the head types and the sum of the child types.-/
@[implicit_reducible] def prod (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    PFunctor.{max uA₁ uA₂, max uB₁ uB₂} := ⟨P.A × Q.A, fun ab => P.B ab.1 ⊕ Q.B ab.2⟩

@[simps!] instance instHMulPFunctor :
    HMul PFunctor.{uA₁, uB₁} PFunctor.{uA₂, uB₂} PFunctor.{max uA₁ uA₂, max uB₁ uB₂} where
  hMul := prod

/--
@isnad1 id=eq.0h2v.s4.41fd64b1ad49 from=translated src=- shape=895a5e7f vocab=74349b09
-/
@[simp] lemma prod_eq_mul (P : PFunctor.{uA₁, uB₁}) (Q : PFunctor.{uA₂, uB₂}) :
    P.prod Q = P * Q := rfl

end prod

section Unary

/-- A polynomial functor is unary if all child types have exactly one element.-/
class Unary (P : PFunctor) where
  unary (a : P.A) : Unique (P.B a)

attribute [instance_reducible, instance] PFunctor.Unary.unary

/--
@isnad1 id=eq.0h4v.s5.7e67e3df79ab from=translated src=- shape=f3cfe79b vocab=f794c796
-/
theorem Unary.fun_eq_const [Unary P]
    (a : P.A) (f : P.B a → α) : f = fun _ => f default := by
  funext i
  exact congrArg f (Subsingleton.elim i default)

/-- A polynomial functor has children with decidable equality.-/
class DecidableEqChildren (P : PFunctor) where
  decidableEq (a : P.A) : DecidableEq (P.B a)

attribute [instance_reducible, instance] DecidableEqChildren.decidableEq

/-- A unary polynomial functor has decidable child equality.-/
instance (P : PFunctor) [P.Unary] : P.DecidableEqChildren where
  decidableEq _ _ _ := isTrue (Subsingleton.elim _ _)

/-- Constructs a unary polynomial functor.-/
abbrev mkUnary (A : Type*) : PFunctor where
  A := A
  B := fun _ => Unit

instance (A : Type uA) : (linear.{uA, uB} A).Unary where
  unary _ := inferInstanceAs (Unique PUnit)

end Unary

end PFunctor
