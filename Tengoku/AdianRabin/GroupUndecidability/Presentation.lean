import Tengoku.Seed.Computability.RE
import Tengoku.Seed.GroupTheory.FreeGroup.Reduce
import Tengoku.Seed.GroupTheory.PresentedGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Undecidability

/-- A letter in a word on `n` generators. The Boolean records the sign.-/
abbrev SignedGenerator (n : ℕ) := Fin n × Bool

/-- A word on `n` generators.-/
abbrev Word (n : ℕ) := List (SignedGenerator n)

namespace Word

/-- The empty word.-/
def one : Word n :=
  []

/-- A positive generator as a one-letter word.-/
def generator (i : Fin n) : Word n :=
  [(i, true)]

/-- Formal inverse of a word.-/
def inverse (w : Word n) : Word n :=
  (w.reverse.map fun x => (x.1, !x.2))

/-- Multiplication of words is concatenation.-/
def mul (u v : Word n) : Word n :=
  u ++ v

/-- Concatenate a finite list of words.-/
def product (ws : List (Word n)) : Word n :=
  ws.flatten

/-- A nonnegative power of a word.-/
def pow (w : Word n) (k : ℕ) : Word n :=
  (List.replicate k w).flatten

/-- Reindex the generators occurring in a word.-/
def mapGenerators (f : Fin n → Fin k) (w : Word n) : Word k :=
  w.map fun x => (f x.1, x.2)

/-- Interpret a positive two-letter word by substituting two group words.-/
def substitutePositive (s₁ s₂ : Word n) (w : List (Fin 2)) : Word n :=
  w.flatMap fun i => if i = 0 then s₁ else s₂

/-- Substitute a word for every signed generator in a word.-/
def substitute {A : Type*} (s : A → Word n) (w : List (A × Bool)) : Word n :=
  w.flatMap fun x => if x.2 then s x.1 else inverse (s x.1)

/-- The relator corresponding to the equation `lhs = rhs`.-/
def relation (lhs rhs : Word n) : Word n :=
  mul lhs (inverse rhs)

/-- The commutator convention `[u,v] = u⁻¹v⁻¹uv` used in the paper.-/
def commutator (u v : Word n) : Word n :=
  mul (inverse u) (mul (inverse v) (mul u v))

/--
@isnad1 id=eq.0h3v.s4.d1b03a2810ad from=translated src=- shape=e617d6f0 vocab=3dae3ed3
-/
@[simp]
theorem inverse_mul (u v : Word n) :
    inverse (mul u v) = mul (inverse v) (inverse u) := by
  simp [inverse, mul, List.reverse_append]

/--
@isnad1 id=eq.0h2v.s3.e2767f6855cd from=translated src=- shape=6ddf6d3e vocab=c59463a4
-/
@[simp]
theorem inverse_inverse (w : Word n) : inverse (inverse w) = w := by
  simp [inverse, Function.comp_def]

/--
@isnad1 id=eq.0h5v.s5.9a9ef8ffe549 from=translated src=- shape=4c6697c8 vocab=5e1e0953
-/
@[simp]
theorem substitute_append {A : Type*} (s : A → Word n)
    (u v : List (A × Bool)) :
    substitute s (u ++ v) = mul (substitute s u) (substitute s v) := by
  simp [substitute, mul]

/--
@isnad1 id=eq.0h4v.s4.56070d895444 from=translated src=- shape=a7330973 vocab=0a95fa13
-/
@[simp]
theorem substitute_invRev {A : Type*} (s : A → Word n)
    (w : List (A × Bool)) :
    substitute s (FreeGroup.invRev w) = inverse (substitute s w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨i, sign⟩
      rw [show FreeGroup.invRev ((i, sign) :: w) =
        FreeGroup.invRev w ++ [(i, !sign)] by
          simp [FreeGroup.invRev]]
      rw [substitute_append, ih]
      cases sign with
      | false =>
          simp only [substitute, Bool.not_false, Bool.false_eq_true,
            ite_false, ite_true, List.flatMap_cons, List.flatMap_nil,
            List.append_nil]
          change mul (inverse (substitute s w)) (s i) =
            inverse (mul (inverse (s i)) (substitute s w))
          rw [inverse_mul, inverse_inverse]
      | true =>
          simp only [substitute, Bool.not_true,
            ite_true, List.flatMap_cons, List.flatMap_nil,
            List.append_nil]
          change mul (inverse (substitute s w)) (inverse (s i)) =
            inverse (mul (s i) (substitute s w))
          rw [inverse_mul]

/--
@isnad1 id=eq.0h4v.s5.6331a3f8f24e from=translated src=- shape=9efe2eb0 vocab=2cc33d9d
-/
@[simp]
theorem substitute_flatten {A : Type*} (s : A → Word n)
    (ws : List (List (A × Bool))) :
    substitute s ws.flatten = product (ws.map (substitute s)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      change substitute s (w ++ ws.flatten) =
        mul (substitute s w) (product (ws.map (substitute s)))
      rw [substitute_append, ih]

/-- Evaluate a syntactic word after choosing values for its generators.-/
def eval {G : Type*} [Group G] (x : Fin n → G) (w : Word n) : G :=
  FreeGroup.lift x (FreeGroup.mk w)

/--
@isnad1 id=eq.0h4v.s4.0b9dbdaa47a8 from=translated src=- shape=b6e6378a vocab=9a9843c7
-/
@[simp]
theorem eval_generator {G : Type*} [Group G]
    (x : Fin n → G) (i : Fin n) :
    eval x (generator i) = x i := by
  simp [eval, generator]

/--
@isnad1 id=eq.0h5v.s5.d7230e188f4c from=translated src=- shape=770d2149 vocab=aff5e3de
-/
@[simp]
theorem eval_mul {G : Type*} [Group G]
    (x : Fin n → G) (u v : Word n) :
    eval x (mul u v) = eval x u * eval x v :=
  map_mul (FreeGroup.lift x) (FreeGroup.mk u) (FreeGroup.mk v)

/--
@isnad1 id=eq.0h5v.s6.0320abb06580 from=translated src=- shape=bcc31bcf vocab=7acec1b5
-/
@[simp]
theorem eval_append {G : Type*} [Group G]
    (x : Fin n → G) (u v : Word n) :
    eval x (u ++ v) = eval x u * eval x v :=
  eval_mul x u v

/--
@isnad1 id=eq.0h2v.s4.8a2ee6272659 from=translated src=- shape=ac96ee11 vocab=7a49c9b0
-/
theorem mk_inverse (w : Word n) :
    FreeGroup.mk (inverse w) = (FreeGroup.mk w)⁻¹ := by
  rw [FreeGroup.inv_mk]
  simp only [inverse, FreeGroup.invRev, List.map_reverse]

/--
@isnad1 id=eq.0h4v.s5.368e4ad0499f from=translated src=- shape=ae579020 vocab=6c2c7fda
-/
@[simp]
theorem eval_inverse {G : Type*} [Group G]
    (x : Fin n → G) (w : Word n) :
    eval x (inverse w) = (eval x w)⁻¹ := by
  rw [eval, mk_inverse]
  exact map_inv (FreeGroup.lift x) (FreeGroup.mk w)

/--
@isnad1 id=eq.0h5v.s5.159619076d28 from=translated src=- shape=3b45f66d vocab=0fb5215f
-/
@[simp]
theorem eval_pow {G : Type*} [Group G]
    (x : Fin n → G) (w : Word n) (k : ℕ) :
    eval x (pow w k) = eval x w ^ k := by
  rw [eval, pow, ← FreeGroup.pow_mk]
  exact map_pow (FreeGroup.lift x) (FreeGroup.mk w) k

/--
@isnad1 id=eq.0h4v.s5.325cfd58da4e from=translated src=- shape=88e2cb85 vocab=8e64a4db
-/
@[simp]
theorem eval_product {G : Type*} [Group G]
    (x : Fin n → G) (ws : List (Word n)) :
    eval x (product ws) = (ws.map (eval x)).prod := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      change eval x (mul w (product ws)) = _
      simp [ih]

/--
@isnad1 id=eq.0h6v.s5.b317118d63f1 from=translated src=- shape=2020d182 vocab=64511773
-/
@[simp]
theorem eval_mapGenerators {G : Type*} [Group G]
    (x : Fin k → G) (f : Fin n → Fin k) (w : Word n) :
    eval x (mapGenerators f w) = eval (x ∘ f) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨i, sign⟩
      cases sign <;>
        simp [eval, mapGenerators, FreeGroup.lift_mk, Function.comp_def]

/--
@isnad1 id=eq.0h6v.s7.35f889b95279 from=translated src=- shape=387ff89b vocab=3a81fb95
-/
theorem map_eval {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : Fin n → G) (w : Word n) :
    f (eval x w) = eval (f ∘ x) w := by
  change (f.comp (FreeGroup.lift x)) (FreeGroup.mk w) =
    (FreeGroup.lift (f ∘ x)) (FreeGroup.mk w)
  congr 1
  apply FreeGroup.ext_hom
  intro i
  simp [Function.comp_def]

/--
@isnad1 id=eq.0h6v.s7.c3bd96b12db4 from=translated src=- shape=fbdaa626 vocab=ebbc73a4
-/
@[simp]
theorem eval_substitutePositive {G : Type*} [Group G]
    (x : Fin n → G) (s₁ s₂ : Word n) (w : List (Fin 2)) :
    eval x (substitutePositive s₁ s₂ w) =
      (w.map fun i => if i = 0 then eval x s₁ else eval x s₂).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change eval x
          ((if i = 0 then s₁ else s₂) ++ substitutePositive s₁ s₂ w) =
        (if i = 0 then eval x s₁ else eval x s₂) *
          (w.map fun j => if j = 0 then eval x s₁ else eval x s₂).prod
      rw [eval_append, ih]
      split <;> rfl

/--
@isnad1 id=eq.0h6v.s5.4427806fd289 from=translated src=- shape=18a6b5d1 vocab=46b5b27c
-/
@[simp]
theorem eval_substitute {G : Type*} [Group G]
    (x : Fin k → G) (s : Fin n → Word k) (w : Word n) :
    eval x (substitute s w) = eval (fun i => eval x (s i)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨i, sign⟩
      change eval x
          (mul (if sign then s i else inverse (s i)) (substitute s w)) =
        eval (fun i => eval x (s i)) ([(i, sign)] ++ w)
      rw [eval_mul, ih]
      cases sign
      · simp only [Bool.false_eq_true, ite_false]
        rw [eval_inverse]
        simp [eval, FreeGroup.lift_mk]
      · simp only [ite_true]
        simp [eval, FreeGroup.lift_mk]

/--
@isnad1 id=eq.0h5v.s6.a6791360834a from=translated src=- shape=ac2967f7 vocab=3083f13c
-/
@[simp]
theorem eval_relation {G : Type*} [Group G]
    (x : Fin n → G) (lhs rhs : Word n) :
    eval x (relation lhs rhs) = eval x lhs * (eval x rhs)⁻¹ := by
  simp [relation]

/--
@isnad1 id=iff.0h5v.s5.e7fd48211349 from=translated src=- shape=f21f3531 vocab=2a2d71f9
-/
theorem eval_relation_eq_one_iff {G : Type*} [Group G]
    (x : Fin n → G) (lhs rhs : Word n) :
    eval x (relation lhs rhs) = 1 ↔ eval x lhs = eval x rhs := by
  rw [eval_relation]
  exact mul_inv_eq_one

/--
@isnad1 id=eq.0h5v.s6.c6dcc1941e91 from=translated src=- shape=7e76b3fd vocab=a6f20ac4
-/
@[simp]
theorem eval_commutator {G : Type*} [Group G]
    (x : Fin n → G) (u v : Word n) :
    eval x (commutator u v) =
      (eval x u)⁻¹ * (eval x v)⁻¹ * eval x u * eval x v := by
  simp [commutator, mul_assoc]

end Word

/--
Syntax for a finite group presentation with exactly `n` generator slots and
exactly `m` relator slots.-/
structure FP (n m : ℕ) where
  relator : Fin m → Word n

namespace FP

/-- The relators of a finite presentation, interpreted in the free group.-/
def relSet (P : FP n m) : Set (FreeGroup (Fin n)) :=
  Set.range fun i => FreeGroup.mk (P.relator i)

/-- The group defined by a finite presentation.-/
abbrev Group (P : FP n m) :=
  PresentedGroup P.relSet

/-- The word problem for a finite presentation.-/
def wordProblem (P : FP n m) (w : Word n) : Prop :=
  PresentedGroup.mk P.relSet (FreeGroup.mk w) = 1

/-- Evaluate a word in the group defined by a presentation.-/
def evalWord (P : FP n m) (w : Word n) : P.Group :=
  Word.eval (fun i => PresentedGroup.of i) w

/--
@isnad1 id=eq.0h4v.s7.29c91af1aa9e from=translated src=- shape=e516a060 vocab=169350e8
-/
theorem evalWord_eq_mk (P : FP n m) (w : Word n) :
    P.evalWord w = PresentedGroup.mk P.relSet (FreeGroup.mk w) := by
  change (FreeGroup.lift (fun i => PresentedGroup.of i)) (FreeGroup.mk w) = _
  congr 1
  apply FreeGroup.ext_hom
  intro i
  rfl

/--
@isnad1 id=iff.0h4v.s6.b7255590b9f8 from=translated src=- shape=06822309 vocab=b72dc0a8
-/
theorem wordProblem_iff_evalWord_eq_one (P : FP n m) (w : Word n) :
    P.wordProblem w ↔ P.evalWord w = 1 := by
  rw [evalWord_eq_mk]
  rfl

/-- Every designated relator evaluates to one in the presented group.
@isnad1 id=eq.0h4v.s5.925ee4db953b from=translated src=- shape=cd800d9c vocab=001c6f93
-/
theorem relator_eq_one (P : FP n m) (i : Fin m) :
    P.evalWord (P.relator i) = 1 := by
  rw [evalWord_eq_mk]
  apply PresentedGroup.one_of_mem
  exact ⟨i, rfl⟩

/-- Map a presented group by choosing images of its generators and proving
that the designated relators hold.-/
def homOfRelators {G : Type*} [_root_.Group G] (P : FP n m) (x : Fin n → G)
    (h : ∀ i, Word.eval x (P.relator i) = 1) : P.Group →* G :=
  PresentedGroup.toGroup fun r hr => by
    obtain ⟨i, rfl⟩ := hr
    exact h i

/--
@isnad1 id=eq.1h6v.s7.8c7ef9fc4393 from=translated src=- shape=77c9370a vocab=bcaec343
-/
@[simp]
theorem homOfRelators_of {G : Type*} [_root_.Group G] (P : FP n m)
    (x : Fin n → G) (h : ∀ i, Word.eval x (P.relator i) = 1) (i : Fin n) :
    P.homOfRelators x h (PresentedGroup.of i) = x i :=
  PresentedGroup.toGroup.of _

/--
@isnad1 id=eq.1h6v.s7.e4ecc35c031e from=translated src=- shape=b9add53d vocab=6847249b
-/
@[simp]
theorem homOfRelators_evalWord {G : Type*} [_root_.Group G] (P : FP n m)
    (x : Fin n → G) (h : ∀ i, Word.eval x (P.relator i) = 1) (w : Word n) :
    P.homOfRelators x h (P.evalWord w) = Word.eval x w := by
  rw [evalWord, Word.map_eval]
  congr 1
  funext i
  exact P.homOfRelators_of x h i

/-- A presentation presents the trivial group when every word represents `1`.-/
def presentsTrivial (P : FP n m) : Prop :=
  ∀ w : Word n, P.wordProblem w

/-- A word normally generates the group defined by `P`.-/
def NormallyGenerates (P : FP n m) (z : Word n) : Prop :=
  Subgroup.normalClosure
      ({PresentedGroup.mk P.relSet (FreeGroup.mk z)} : Set P.Group) =
    ⊤

/--
@isnad1 id=iff.0h3v.s4.e62783a26aa0 from=translated src=- shape=a10f8515 vocab=28e04a92
-/
theorem presentsTrivial_iff_subsingleton (P : FP n m) :
    P.presentsTrivial ↔ Subsingleton P.Group := by
  constructor
  · intro h
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective P.relSet a
    obtain ⟨y, rfl⟩ := PresentedGroup.mk_surjective P.relSet b
    have hx : PresentedGroup.mk P.relSet x = 1 := by
      rw [← FreeGroup.mk_toWord (x := x)]
      exact h x.toWord
    have hy : PresentedGroup.mk P.relSet y = 1 := by
      rw [← FreeGroup.mk_toWord (x := y)]
      exact h y.toWord
    exact hx.trans hy.symm
  · intro h w
    exact h.elim _ _

/-- A finite presentation is trivial when all of its canonical generators
are equal to one.
@isnad1 id=presents.1h3v.s6.0057b91c8981 from=translated src=- shape=3d76779d vocab=042d6d71
-/
theorem presentsTrivial_of_generator_eq_one (P : FP n m)
    (h : ∀ i, (PresentedGroup.of i : P.Group) = 1) : P.presentsTrivial := by
  rw [presentsTrivial_iff_subsingleton]
  constructor
  intro a b
  have hmk : PresentedGroup.mk P.relSet =
      (1 : FreeGroup (Fin n) →* P.Group) := by
    apply FreeGroup.ext_hom
    intro i
    simpa [PresentedGroup.of] using h i
  obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective P.relSet a
  obtain ⟨y, rfl⟩ := PresentedGroup.mk_surjective P.relSet b
  rw [hmk]
  rfl

/--
A family of finite presentations is effective when one algorithm computes the
`i`th relator of the `j`th presentation from `j` and `i`.-/
def Effective (A : ℕ → FP n m) : Prop :=
  Computable₂ fun j i => (A j).relator i

/--
An effective Adian--Rabin family for triviality: there is no algorithm deciding
which member of the family presents the trivial group.-/
def IsAdianRabinFamily (A : ℕ → FP n m) : Prop :=
  Effective A ∧
    ¬ ComputablePred fun j => (A j).presentsTrivial

end FP

end Undecidability
