/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Finite-support semantics

`FiniteSupport M` is the idempotent support carrier used by monotone
arithmetic interpretations.  Addition unions supports, while multiplication
takes all pairwise products.  No algebraic laws on `M` are imposed here: the
arithmetic circuit syntax only needs total binary operations, and concrete
applications can add monoid or exponent-vector structure as needed.
-/

@[expose] public section

namespace Algebraic

/-- A semantic value represented only by its finite set of monomials. -/
structure FiniteSupport (M : Type u) where
  /-- Monomials present with nonzero coefficient. -/
  monomials : Finset M
  deriving DecidableEq

namespace FiniteSupport

/-- The support consisting of one monomial. -/
def singleton
    (monomial : M) : FiniteSupport M :=
  ⟨{monomial}⟩

/-- The empty support. -/
def empty (M : Type u) : FiniteSupport M :=
  ⟨∅⟩

instance [DecidableEq M] : Add (FiniteSupport M) where
  add left right := ⟨left.monomials ∪ right.monomials⟩

instance [DecidableEq M] [Mul M] : Mul (FiniteSupport M) where
  mul left right :=
    ⟨left.monomials.image₂ (· * ·) right.monomials⟩

/--
@isnad1 id=eq.0h2v.s4.9a122ec5c278 from=translated src=- shape=6f50cb78 vocab=7c234d57
-/
@[simp] theorem monomials_singleton
    (monomial : M) :
    (singleton monomial).monomials = {monomial} := rfl

/--
@isnad1 id=eq.0h1v.s3.e6949e5d1df6 from=translated src=- shape=78677137 vocab=ab8dae3c
-/
@[simp] theorem monomials_empty :
    (empty M).monomials = ∅ := rfl

/--
@isnad1 id=eq.0h3v.s5.d2448b02a249 from=translated src=- shape=c4226983 vocab=ae016877
-/
@[simp] theorem monomials_add
    [DecidableEq M]
    (left right : FiniteSupport M) :
    (left + right).monomials = left.monomials ∪ right.monomials := rfl

/--
@isnad1 id=iff.0h4v.s6.1e4aa99ba2b1 from=translated src=- shape=30004b34 vocab=f2964adb
-/
theorem mem_add
    [DecidableEq M]
    (monomial : M)
    (left right : FiniteSupport M) :
    monomial ∈ (left + right).monomials ↔
      monomial ∈ left.monomials ∨ monomial ∈ right.monomials := by
  simp

/--
@isnad1 id=eq.0h3v.s5.cdc2e30df9f0 from=translated src=- shape=f83a39a7 vocab=6400da87
-/
@[simp] theorem monomials_mul
    [DecidableEq M]
    [Mul M]
    (left right : FiniteSupport M) :
    (left * right).monomials =
      left.monomials.image₂ (· * ·) right.monomials := rfl

/--
@isnad1 id=iff.0h4v.s6.5e82295148e6 from=translated src=- shape=3e49a1c1 vocab=4dfdb7a8
-/
theorem mem_mul
    [DecidableEq M]
    [Mul M]
    (monomial : M)
    (left right : FiniteSupport M) :
    monomial ∈ (left * right).monomials ↔
      ∃ leftMonomial ∈ left.monomials,
        ∃ rightMonomial ∈ right.monomials,
          leftMonomial * rightMonomial = monomial := by
  simp

/-- Pairwise multiplication produces at most the Cartesian-product number of
monomials.
@isnad1 id=le.0h3v.s5.1f96ba4c6412 from=translated src=- shape=67cc6b88 vocab=ca293638
-/
theorem card_mul_le
    [DecidableEq M]
    [Mul M]
    (left right : FiniteSupport M) :
    (left * right).monomials.card ≤
      left.monomials.card * right.monomials.card := by
  exact Finset.card_image₂_le _ _ _

end FiniteSupport
end Algebraic
