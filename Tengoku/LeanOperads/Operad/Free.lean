/-
# The free non-symmetric operad on a collection of generators

`Operad.Tree` proved the four operad laws for planar trees under grafting. This file linearises:
`Free R E n` is the free `R`-module on trees of arity `n`, and grafting extends bilinearly to
the operadic composition.

Carrying the arity as a *proof* rather than an index pays off here. Grafting at the positional
slot `a` produces a tree of arity `(a + 1 + b) - 1 + n`, which is not syntactically `a + n + b`;
because the arity sits in a `Subtype` proof field rather than in the type, the two are reconciled
by supplying a different proof, with no transport at all.
-/
import Tengoku.LeanOperads.Operad.Tree
import Tengoku.LeanOperads.Operad.Basic
import Tengoku.Seed.LinearAlgebra.Finsupp.LSum
import Tengoku.Seed.LinearAlgebra.Span.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

/-- A planar tree together with a proof that it has arity `n`.-/
def TreeOfArity (E : ℕ → Type v) (n : ℕ) : Type v := {t : Tree E // t.arity = n}

namespace TreeOfArity

variable {E : ℕ → Type v}

/--
@isnad1 id=eq.1h4v.s5.f412671b59b8 from=translated src=- shape=84e36169 vocab=947d9e57
-/
@[ext] lemma ext {n : ℕ} {s t : TreeOfArity E n} (h : s.val = t.val) : s = t := Subtype.ext h

/-- The operadic identity: the bare leaf.-/
def one : TreeOfArity E 1 := ⟨.leaf, rfl⟩

/-- Grafting at the positional slot `a`: the slot sits after `a` leaves and before `b`.-/
def graft (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b)) (s : TreeOfArity E n) :
    TreeOfArity E (a + n + b) :=
  ⟨t.val.graft a s.val, by
    have ht := t.property
    have hs := s.property
    rw [Tree.arity_graft t.val a s.val (by omega), ht, hs]
    omega⟩

/--
@isnad1 id=eq.0h6v.s6.c82bf873631b from=translated src=- shape=e5792bb8 vocab=04900a02
-/
@[simp] lemma graft_val (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b)) (s : TreeOfArity E n) :
    (graft a b t s).val = t.val.graft a s.val := rfl

end TreeOfArity

/-- The free non-symmetric operad on the collection `E`: the free `R`-module on planar trees
of each arity, with vertices labelled by `E`.-/
abbrev Free (R : Type u) [CommRing R] (E : ℕ → Type v) (n : ℕ) : Type (max u v) :=
  TreeOfArity E n →₀ R

namespace Free

variable {R : Type u} [CommRing R] {E : ℕ → Type v}

/-- The basis element attached to a tree.-/
noncomputable def gen {n : ℕ} (t : TreeOfArity E n) : Free R E n := Finsupp.single t 1

/--
@isnad1 id=eq.0h5v.s6.392ad1cd4b2b from=translated src=- shape=22affe56 vocab=48256ab1
-/
lemma smul_gen {n : ℕ} (t : TreeOfArity E n) (r : R) :
    r • gen (R := R) t = Finsupp.single t r := by
  rw [gen, Finsupp.smul_single, smul_eq_mul, mul_one]

/--
@isnad1 id=eq.0h4v.s5.701a0945f59e from=translated src=- shape=216e8507 vocab=3d945672
-/
lemma gen_def {n : ℕ} (t : TreeOfArity E n) : gen (R := R) t = Finsupp.single t 1 := rfl

/-- Grafting, extended bilinearly.-/
noncomputable def compL (a b : ℕ) {n : ℕ} :
    Free R E (a + 1 + b) →ₗ[R] Free R E n →ₗ[R] Free R E (a + n + b) :=
  Finsupp.lsum R fun t =>
    LinearMap.toSpanSingleton R _ <|
      Finsupp.lsum R fun s =>
        LinearMap.toSpanSingleton R _ (gen (R := R) (TreeOfArity.graft a b t s))

/--
@isnad1 id=eq.0h7v.s10.8b7f5977ee5f from=translated src=- shape=6259a555 vocab=b72c524e
-/
@[simp] lemma compL_gen (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b))
    (s : TreeOfArity E n) :
    compL (R := R) a b (gen t) (gen s) = gen (TreeOfArity.graft a b t s) := by
  simp only [compL, gen, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply_one]

/-- Reindexing a generator only changes the arity proof it carries.
@isnad1 id=eq.1h5v.s9.79757739ef1f from=translated src=- shape=07380e9b vocab=301475a3
-/
lemma reindex_gen {m n : ℕ} (h : m = n) (x : TreeOfArity E m) :
    reindex R (Free R E) h (gen x) = gen ⟨x.val, by rw [x.property, h]⟩ := by
  subst h
  rw [reindex_self]
  exact congrArg gen (Subtype.ext rfl)

/--
@isnad1 id=eq.0h9v.s10.89a265448859 from=translated src=- shape=18b8e5a5 vocab=8b7d5cb4
-/
lemma compL_single (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b)) (r : R)
    (s : TreeOfArity E n) (r' : R) :
    compL (R := R) a b (Finsupp.single t r) (Finsupp.single s r')
      = Finsupp.single (TreeOfArity.graft a b t s) (r * r') := by
  rw [← smul_gen, ← smul_gen, map_smul, map_smul, LinearMap.smul_apply, compL_gen, smul_smul,
    smul_gen, mul_comm]

/-- Reindexing a `single` only changes the arity proof the tree carries.
@isnad1 id=eq.1h6v.s9.c7e5e9bad8b6 from=translated src=- shape=3b8e3539 vocab=a4f10b7a
-/
lemma reindex_single {m n : ℕ} (h : m = n) (x : TreeOfArity E m) (r : R) :
    reindex R (Free R E) h (Finsupp.single x r)
      = Finsupp.single ⟨x.val, by rw [x.property, h]⟩ r := by
  subst h
  rw [reindex_self]
  exact congrArg (fun y => Finsupp.single y r) (Subtype.ext rfl)

end Free

end Operad
