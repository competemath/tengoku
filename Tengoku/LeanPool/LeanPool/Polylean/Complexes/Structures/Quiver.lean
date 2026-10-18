/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/
module

@[expose] public section

namespace LeanPool.Polylean

universe u v w

/-- A `Quiver` `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
    a type `a ⟶ b` of arrows from `a` to `b`.

    It is a common generalisation of multigraphs and categories.
    This definition is taken from `mathlib`:
    https://leanprover-community.github.io/mathlib_docs/combinatorics/quiver/basic.html#quiver. -/
class Quiver (V : Sort u) where
  /-- The type of arrows from one vertex to another. -/
  hom : V → V → Sort v

/-- Arrow notation for the hom type of a quiver. -/
scoped infixr:10 " ⟶ " => Quiver.hom -- type using `\-->` or `\hom`

namespace Quiver

/-- A pre-functor is a morphism of quivers. -/
structure PreFunctor {V V' : Sort _} (Q : Quiver V) (Q' : Quiver V') where
  /-- The map on vertices. -/
  obj : V → V'
  /-- The map on arrows. -/
  map : {X Y : V} → (X ⟶ Y) → (obj X ⟶ obj Y)

namespace PreFunctor

/-- The identity morphism between quivers. -/
@[simp] protected def id (V : Sort _) [Q : Quiver V] : PreFunctor Q Q :=
{ obj := id, map := id }

instance (V : Sort _) [Q : Quiver V] : Inhabited (PreFunctor Q Q) := ⟨PreFunctor.id V⟩

/-- Composition of morphisms between quivers. -/
@[simp] def comp {U V W : Sort _} {QU : Quiver U} {QV : Quiver V} {QW : Quiver W}
  (F : PreFunctor QU QV) (G : PreFunctor QV QW) : PreFunctor QU QW :=
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map }

end PreFunctor

end Quiver

/-- Paths in a quiver. -/
inductive Path {V : Sort _} [Quiver V] : V → V → Sort _
  | nil : {A : V} → Path A A
  | cons : {A B C : V} → (A ⟶ B) → Path B C → Path A C

namespace Quiver

/-- Convert a single quiver arrow to a path. -/
def toPath {V : Sort _} [Quiver V] {A B : V} (e : A ⟶ B) : Path A B :=
  .cons e .nil

end Quiver

namespace Path

variable {V : Sort _} [Quiver V] {A B C D : V}

/-- The empty path at a vertex, with its vertex explicit for pattern matching. -/
@[match_pattern] abbrev nil' (A : V) : Path A A := Path.nil
/-- A path formed by adding an edge to the front, with endpoints explicit for matching. -/
@[match_pattern] abbrev cons' (A B C : V) :
  (A ⟶ B) → Path B C → Path A C := Path.cons

/-- Concatenate an edge to the end of a path. -/
@[match_pattern]
abbrev snoc : {A B C : V} → Path A B → (B ⟶ C) → Path A C
  | _, _, _, .nil, e => .cons e .nil
  | _, _, _, .cons e p', e' => .cons e (snoc p' e')

/-- Append an edge to the end of a path, with endpoints explicit for matching. -/
@[match_pattern]
abbrev snoc' (A B C : V) : Path A B → (B ⟶ C) → Path A C := Path.snoc

/-- Concatenation of paths. -/
def append : {A B C : V} → Path A B → Path B C → Path A C
  | _, _, _, .nil, p => p
  | _, _, _, .cons e p', p => cons e (append p' p)

/-- The length of a path. -/
def length : {A B : V} → Path A B → Nat
  | _, _, .nil => .zero
  | _, _, .cons _ p => .succ (length p)

/--
@isnad1 id=eq.0h4v.s5.e83e5901ef8c from=translated src=- shape=519f6f99 vocab=85900b64
-/
@[simp] theorem nil_append (p : Path A B) : .append .nil p = p := rfl

/--
@isnad1 id=eq.0h4v.s5.77483f1702e5 from=translated src=- shape=3ce052f0 vocab=85900b64
-/
@[simp] theorem append_nil (p : Path A B) : .append p .nil = p := by
  induction p
  · rfl
  · simp [append, *]

/--
@isnad1 id=eq.0h8v.s6.bd125c5dc7cb from=translated src=- shape=94b06c0d vocab=605e91a9
-/
theorem snoc_cons (e : A ⟶ B) (p : Path B C) (e' : C ⟶ D) :
  snoc (cons e p) e' = cons e (snoc p e') := by cases p <;> simp

/--
@isnad1 id=eq.0h8v.s6.0e2fac64b3fc from=translated src=- shape=90e81d5a vocab=17373202
-/
theorem append_snoc (p : Path A B) (p' : Path B C) (e : C ⟶ D) :
    append p (snoc p' e) = snoc (append p p') e := by
  induction p
  · case nil => rfl
  · case cons ih => simp [append, ih p']

/--
@isnad1 id=eq.0h8v.s6.a1eafa6f357d from=translated src=- shape=284be5ce vocab=69e60014
-/
theorem append_cons (p : Path A B) (e : B ⟶ C) (p' : Path C D) :
    append p (cons e p') = append (snoc p e) p' := by
  induction p
  · case nil => rfl
  · case cons ih => dsimp [append]; rw [ih]

/--
@isnad1 id=eq.0h8v.s6.c26089462af4 from=translated src=- shape=a9c80524 vocab=33f0cc12
-/
theorem append_assoc (p : Path A B) (q : Path B C) (r : Path C D) :
    append (append p q) r = append p (append q r) := by
  induction p
  · case nil => rfl
  · case cons ih => simp [append]; apply ih

-- TODO Rephrase this to work for general paths, not just loops
/--
@isnad1 id=iff.0h3v.s5.ce6fee86dcf7 from=translated src=- shape=cb605521 vocab=86a0c19e
-/
theorem nil_length {A : V} : (p : Path A A) → p.length = .zero ↔ p = .nil' A
  | .nil => ⟨λ _ => rfl, λ _ => rfl⟩
  | .cons _ p => by apply Iff.intro <;> (intro; simp [length] at *)

/--
@isnad1 id=eq.0h6v.s5.a09ba8960c1e from=translated src=- shape=dc399f59 vocab=58ea38e2
-/
theorem snoc_length {A B C : V} : (p : Path A B) → (e : B ⟶ C) → length (.snoc p e) = .succ (length p)
  | .nil, _ => rfl
  | .cons _ p', e => by simp [length, snoc_length p' e]

/--
@isnad1 id=eq.0h6v.s5.1f3a7819b34e from=translated src=- shape=a8b6532a vocab=f966cff2
-/
theorem length_append {A B C : V} : (p : Path A B) → (q : Path B C) → (append p q).length = p.length + q.length
  | .nil, q => by rw [Nat.add_comm]; rfl
  | .cons _ p', q => by
    dsimp [append, length]
    simpa [Nat.succ_add] using congrArg Nat.succ (length_append p' q)

/-- The end-point of the first edge in the path. -/
def first : Path A B → V
  | .nil' v => v
  | .cons' _ v _ _ _ => v

/-- The source of the last end in the path. -/
def last : {A B : V} → Path A B → V
  | _, _, .nil' v => v
  | .(v), _, .cons' v _ _ _ .nil => v
  | _, _, .cons' _ _ _ _ (.cons e p) => last (.cons e p)

/--
@isnad1 id=eq.0h6v.s5.e41cb9fa3f16 from=translated src=- shape=f51ef74e vocab=be780076
-/
theorem first_cons (A B C : V) (e : A ⟶ B) (p : Path B C) : first (cons e p) = B := rfl

/--
@isnad1 id=eq.0h6v.s5.8291ee29709c from=translated src=- shape=f51ef74e vocab=b317986b
-/
theorem last_snoc : (A B C : V) → (p : Path A B) → (e : B ⟶ C) → last (snoc p e) = B
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons' _ _ _ _ .nil, _ => by rw [snoc_cons]; rfl
  | _, _, _, .cons' _ _ _ _ (.cons _ _), _ => by rw [snoc_cons, snoc, last, ← snoc_cons]; apply last_snoc

end Path

/-- A loop is a path whose source and target are the same vertex. -/
abbrev Loop {V : Sort _} [Quiver V] (A : V) := Path A A

namespace Loop

variable {V : Sort _} [Quiver V] (A : V)

/-- Regard a loop as a path. -/
def toPath : Loop A → Path A A := id

/-- The empty loop. -/
abbrev nil : Loop A := Path.nil

/-- The next vertex reached by the first edge of a loop. -/
abbrev next : Loop A → V := Path.first

/-- Concatenate two loops. -/
abbrev concat : Loop A → Loop A → Loop A := Path.append

end Loop
end LeanPool.Polylean
-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)
