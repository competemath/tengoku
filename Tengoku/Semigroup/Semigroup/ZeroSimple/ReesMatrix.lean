/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Tengoku.Seed.Algebra.Group.Defs
import Tengoku.Seed.Algebra.GroupWithZero.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Rees Matrix Semigroup with Zero

This file defines the Rees matrix semigroup over a group with sandwich matrix
entries in `Option G` (a `none` entry encodes a zero product) and equips it with
its `SemigroupWithZero` structure. The Rees theorem itself — every completely
0-simple semigroup is isomorphic to such a Rees matrix semigroup — is proved in
`Semigroup.ZeroSimple.ReesTheorem`.

## Main definitions

* `ReesMatrix`: the Rees matrix semigroup over a group `G` with row index set `I`,
  column index set `Λ`, and sandwich matrix `P : Λ → I → Option G`.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/
namespace Tengoku.Semigroup end Tengoku.Semigroup open Tengoku.Semigroup
/-- The Rees matrix semigroup over a group `G` with row index set `I`, column
index set `Λ`, and sandwich matrix `P : Λ → I → Option G`: elements are `zero`
together with triples `elem i g l` with `i : I`, `g : G`, `l : Λ`.-/
inductive _root_.Tengoku.Semigroup.ReesMatrix (G : Type*) (I Λ : Type*) (P : Λ → I → Option G) : Type _
  | zero : ReesMatrix G I Λ P
  | elem (i : I) (g : G) (l : Λ) : ReesMatrix G I Λ P

namespace Tengoku.Semigroup.ReesMatrix

variable {G : Type*} [Group G] {I Λ : Type*} {P : Λ → I → Option G}

/-- Multiplication in the Rees matrix semigroup:
`elem i a l * elem j b m = elem i (a * P l j * b) m` when the sandwich entry
`P l j` is defined, and `zero` otherwise; `zero` is absorbing.-/
protected def mul : ReesMatrix G I Λ P → ReesMatrix G I Λ P → ReesMatrix G I Λ P
  | zero, _ => zero
  | _, zero => zero
  | elem i a l, elem j b m =>
    match P l j with
    | none => zero
    | some p => elem i (a * p * b) m

/-- `zero` is right-absorbing for `ReesMatrix.mul`.
@isnad1 id=eq.0h5v.s5.65ae741a6410 from=translated src=- shape=a6fb6008 vocab=006bd4aa
-/
protected lemma mul_zero' (x : ReesMatrix G I Λ P) : ReesMatrix.mul x zero = zero := by
  cases x <;> rfl

/-- `zero` is left-absorbing for `ReesMatrix.mul`.
@isnad1 id=eq.0h5v.s5.976b16f778cf from=translated src=- shape=6bb5e916 vocab=006bd4aa
-/
protected lemma zero_mul' (x : ReesMatrix G I Λ P) : ReesMatrix.mul zero x = zero := by
  cases x <;> rfl

/-- The product of two triples is `zero` when the sandwich entry `P l j` is `none`.
@isnad1 id=eq.1h10v.s6.3c425915cce6 from=translated src=- shape=0ad1170c vocab=31ee15c2
-/
protected lemma mul_elem_of_none {l : Λ} {j : I} (h : P l j = none)
    (i : I) (a b : G) (m : Λ) :
    ReesMatrix.mul (elem i a l) (elem j b m) = (zero : ReesMatrix G I Λ P) := by
  change (match P l j with
    | none => zero
    | some p => elem i (a * p * b) m) = (zero : ReesMatrix G I Λ P)
  rw [h]

/-- The product of two triples is `elem i (a * p * b) m` when the sandwich entry
`P l j` is `some p`.
@isnad1 id=eq.1h11v.s6.2b69da42bcb6 from=translated src=- shape=3c1f6469 vocab=3cae17f3
-/
protected lemma mul_elem_of_some {l : Λ} {j : I} {p : G} (h : P l j = some p)
    (i : I) (a b : G) (m : Λ) :
    ReesMatrix.mul (elem i a l) (elem j b m) = (elem i (a * p * b) m : ReesMatrix G I Λ P) := by
  change (match P l j with
    | none => zero
    | some q => elem i (a * q * b) m) = (elem i (a * p * b) m : ReesMatrix G I Λ P)
  rw [h]

/-- Multiplication in the Rees matrix semigroup is associative.
@isnad1 id=eq.0h7v.s6.57097f8d04b4 from=translated src=- shape=fbf64ab9 vocab=d4f23671
-/
protected theorem mul_assoc' (x y z : ReesMatrix G I Λ P) :
    ReesMatrix.mul (ReesMatrix.mul x y) z = ReesMatrix.mul x (ReesMatrix.mul y z) := by
  rcases x with _ | ⟨i, a, l⟩
  · rw [ReesMatrix.zero_mul', ReesMatrix.zero_mul', ReesMatrix.zero_mul']
  rcases y with _ | ⟨j, b, m⟩
  · rw [ReesMatrix.mul_zero', ReesMatrix.zero_mul', ReesMatrix.mul_zero']
  rcases z with _ | ⟨k, c, n⟩
  · rw [ReesMatrix.mul_zero', ReesMatrix.mul_zero', ReesMatrix.mul_zero']
  rcases hp : P l j with _ | p
  · rw [ReesMatrix.mul_elem_of_none hp, ReesMatrix.zero_mul']
    rcases hq : P m k with _ | q
    · rw [ReesMatrix.mul_elem_of_none hq, ReesMatrix.mul_zero']
    · rw [ReesMatrix.mul_elem_of_some hq, ReesMatrix.mul_elem_of_none hp]
  · rw [ReesMatrix.mul_elem_of_some hp]
    rcases hq : P m k with _ | q
    · rw [ReesMatrix.mul_elem_of_none hq, ReesMatrix.mul_elem_of_none hq,
        ReesMatrix.mul_zero']
    · rw [ReesMatrix.mul_elem_of_some hq, ReesMatrix.mul_elem_of_some hq,
        ReesMatrix.mul_elem_of_some hp]
      congr 1
      simp [mul_assoc]

/-- The Rees matrix semigroup is a semigroup with zero.-/
instance : SemigroupWithZero (ReesMatrix G I Λ P) where
  mul := ReesMatrix.mul
  zero := zero
  mul_assoc := ReesMatrix.mul_assoc'
  zero_mul := ReesMatrix.zero_mul'
  mul_zero := ReesMatrix.mul_zero'

/-- The product `elem i a l * elem j b m` is `0` when the sandwich entry `P l j`
is `none`.
@isnad1 id=eq.1h10v.s7.615667b5d0e1 from=translated src=- shape=bb2bfb85 vocab=a4eabb76
-/
@[simp] lemma elem_mul_of_none {l : Λ} {j : I} (h : P l j = none)
    (i : I) (a b : G) (m : Λ) :
    (elem i a l : ReesMatrix G I Λ P) * elem j b m = 0 :=
  ReesMatrix.mul_elem_of_none h i a b m

/-- The product `elem i a l * elem j b m` is `elem i (a * p * b) m` when the
sandwich entry `P l j` is `some p`.
@isnad1 id=eq.1h11v.s7.e255a0474d25 from=translated src=- shape=ac0418c5 vocab=8b6ac438
-/
@[simp] lemma elem_mul_of_some {l : Λ} {j : I} {p : G} (h : P l j = some p)
    (i : I) (a b : G) (m : Λ) :
    (elem i a l : ReesMatrix G I Λ P) * elem j b m = elem i (a * p * b) m :=
  ReesMatrix.mul_elem_of_some h i a b m

/-- The zero of the `SemigroupWithZero` structure is the constructor `zero`.
@isnad1 id=eq.0h4v.s5.b7c5c0bc9575 from=translated src=- shape=8d8f6c13 vocab=41fecba7
-/
lemma zero_def : (0 : ReesMatrix G I Λ P) = zero := rfl

/-- The zero of the Rees matrix semigroup is distinct from every triple.
@isnad1 id=ne.0h7v.s6.ae26632ce4b3 from=translated src=- shape=a5ba4e65 vocab=d4e891a5
-/
@[simp] lemma zero_ne_elem {i : I} {g : G} {l : Λ} :
    (0 : ReesMatrix G I Λ P) ≠ elem i g l := fun h => by
  rw [zero_def] at h
  cases h

/-- Every triple of the Rees matrix semigroup is nonzero.
@isnad1 id=ne.0h7v.s6.371e1ae47f50 from=translated src=- shape=8af1aa52 vocab=d4e891a5
-/
@[simp] lemma elem_ne_zero {i : I} {g : G} {l : Λ} :
    (elem i g l : ReesMatrix G I Λ P) ≠ 0 := fun h => by
  rw [zero_def] at h
  cases h

end Tengoku.Semigroup.ReesMatrix
-- Tengoku: root names of this library moved to Tengoku.Semigroup so they do not collide with other libraries (generated)
