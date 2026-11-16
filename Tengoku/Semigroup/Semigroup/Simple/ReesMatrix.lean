/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Tengoku.Seed.Algebra.Group.Defs
import Tengoku.Seed.Tactic.Ext

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Rees Matrix Semigroup without Zero

This file defines the zero-free Rees matrix semigroup `M(G; I, Λ; P)` over a
group `G` with an everywhere-defined sandwich matrix `P`, and equips it with its
`Semigroup` structure. The Rees theorem for completely simple semigroups is
proved in `Semigroup.Simple.ReesTheorem`.

## Main definitions

* `ReesMatrixSimple`: the Rees matrix semigroup `M(G; I, Λ; P)` without zero, on triples
  `(i, g, l)` with `(i, a, l) * (j, b, m) = (i, a * P l j * b, m)`.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/
namespace Tengoku.Semigroup end Tengoku.Semigroup open Tengoku.Semigroup
/-- The Rees matrix semigroup `M(G; I, Λ; P)` over a group `G` with an
everywhere-defined sandwich matrix `P` and no zero: triples `(i, g, l)`
multiplying by `(i, a, l) * (j, b, m) = (i, a * P l j * b, m)`.-/
@[ext]
structure _root_.Tengoku.Semigroup.ReesMatrixSimple (G : Type*) (I Λ : Type*) (P : Λ → I → G) where
  row : I
  mid : G
  col : Λ

namespace Tengoku.Semigroup.ReesMatrixSimple

variable {G : Type*} [Semigroup G] {I Λ : Type*} {P : Λ → I → G}

/-- Multiplication of Rees matrix triples:
`(i, a, l) * (j, b, m) = (i, a * P l j * b, m)`.-/
instance : Mul (ReesMatrixSimple G I Λ P) :=
  ⟨fun x y => ⟨x.row, x.mid * P x.col y.row * y.mid, y.col⟩⟩

/-- Unfolding lemma for multiplication in `ReesMatrixSimple`.
@isnad1 id=eq.0h6v.s6.693f23861451 from=translated src=- shape=9f37b222 vocab=003fe9f6
-/
@[simp] lemma mul_def (x y : ReesMatrixSimple G I Λ P) :
    x * y = ⟨x.row, x.mid * P x.col y.row * y.mid, y.col⟩ := rfl

/-- The Rees matrix multiplication is associative, so `ReesMatrixSimple G I Λ P` is a
semigroup.-/
instance : Semigroup (ReesMatrixSimple G I Λ P) where
  mul_assoc x y z := by simp only [mul_def, mul_assoc]

end Tengoku.Semigroup.ReesMatrixSimple
-- Tengoku: root names of this library moved to Tengoku.Semigroup so they do not collide with other libraries (generated)
