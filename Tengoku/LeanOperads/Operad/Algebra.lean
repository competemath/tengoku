/-
# Algebras over an operad

An algebra over `P` on a module `V` is exactly a morphism of operads `P → End V`. This is the
universal property that makes `End` the operad every other operad maps into.
-/
import Tengoku.LeanOperads.Operad.Constructions
import Tengoku.LeanOperads.Operad.Endomorphism

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w x

namespace Operad

open NSOperad

/-- An algebra over the operad `P`, structured on the module `V`.-/
abbrev Algebra (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
    (V : Type w) [AddCommGroup V] [Module R V] : Type (max v w) :=
  NSOperadHom R P (End R V)

namespace Algebra

variable {R : Type u} [CommRing R]
  {P : ℕ → Type v} [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
  {V : Type w} [AddCommGroup V] [Module R V]

/-- The `n`-ary operation on `V` determined by `α : P n`.-/
def act (A : Algebra R P V) {n : ℕ} (α : P n) (v : Fin n → V) : V := A.app n α v

/--
@isnad1 id=eq.0h7v.s8.6b198a0d0ca0 from=translated src=- shape=ed775a78 vocab=e4252cd6
-/
lemma act_def (A : Algebra R P V) {n : ℕ} (α : P n) (v : Fin n → V) :
    A.act α v = A.app n α v := rfl

/-- The identity operation of `P` acts as the identity.
@isnad1 id=eq.0h5v.s6.ff51822b71ae from=translated src=- shape=eb54820d vocab=720aa363
-/
@[simp] lemma act_one (A : Algebra R P V) (v : Fin 1 → V) :
    A.act (one (R := R) (P := P)) v = v 0 := by
  rw [act, A.app_one]; rfl

/-- The defining compatibility: acting by a composite is composing the actions.
@isnad1 id=eq.0h10v.s10.6453a7cbd48f from=translated src=- shape=f81fd5d8 vocab=69e98c00
-/
lemma act_comp (A : Algebra R P V) (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n)
    (v : Fin (a + n + b) → V) :
    A.act (comp (R := R) a b α β) v
      = A.act α (End.insTuple a b (A.act β (End.midTuple a b v)) v) := by
  rw [act, A.app_comp]; rfl

/-- Acting by an operation is linear in the operation.
@isnad1 id=eq.0h8v.s7.ae074d701b4b from=translated src=- shape=75cd56af vocab=898d7760
-/
@[simp] lemma act_add (A : Algebra R P V) {n : ℕ} (α α' : P n) (v : Fin n → V) :
    A.act (α + α') v = A.act α v + A.act α' v := by
  rw [act, map_add]; rfl

/--
@isnad1 id=eq.0h8v.s8.266dac7629df from=translated src=- shape=34611ba0 vocab=facf3f5e
-/
@[simp] lemma act_smul (A : Algebra R P V) {n : ℕ} (r : R) (α : P n) (v : Fin n → V) :
    A.act (r • α) v = r • A.act α v := by
  rw [act, map_smul]; rfl

/--
@isnad1 id=eq.0h6v.s7.48e096734f4d from=translated src=- shape=ae7c2424 vocab=418d0f5e
-/
@[simp] lemma act_zero (A : Algebra R P V) {n : ℕ} (v : Fin n → V) :
    A.act (0 : P n) v = 0 := by
  rw [act, map_zero]; rfl

/-- Every module is tautologically an algebra over its own endomorphism operad.-/
def self (R : Type u) [CommRing R] (V : Type w) [AddCommGroup V] [Module R V] :
    Algebra R (End R V) V :=
  NSOperadHom.id

/--
@isnad1 id=eq.0h5v.s7.79db7761382b from=translated src=- shape=0fdd434e vocab=6131aced
-/
@[simp] lemma self_act {n : ℕ} (α : End R V n) (v : Fin n → V) :
    (Algebra.self R V).act α v = α v := rfl

variable {Q : ℕ → Type x} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

/-- Restrict an algebra along a morphism of operads: a `Q`-algebra becomes a `P`-algebra.-/
def comap (f : NSOperadHom R P Q) (A : Algebra R Q V) : Algebra R P V :=
  A.comp f

/--
@isnad1 id=eq.0h9v.s8.297e1605cbbf from=translated src=- shape=2b7ede55 vocab=861ba20b
-/
@[simp] lemma comap_act (f : NSOperadHom R P Q) (A : Algebra R Q V) {n : ℕ} (α : P n)
    (v : Fin n → V) :
    (A.comap f).act α v = A.act (f.app n α) v := rfl

end Algebra

end Operad
