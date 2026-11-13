/-
# Morphisms of non-symmetric operads, and a `Fin`-indexed composition wrapper

The positional convention of `Operad.Basic` is what makes the axioms tractable, but it is not
how anyone writes operads on paper. `compFin` bridges back: it takes a genuine slot index
`i : Fin m` and produces the usual `α ∘ᵢ β : P (m - 1 + n)`.
-/
import Tengoku.LeanOperads.Operad.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w w'

namespace Operad

open NSOperad

section CompFin

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- Partial composition at a slot named by `i : Fin m`, in the textbook arity `m - 1 + n`.
This is the user-facing form; `NSOperad.comp` is the form the axioms are stated in.-/
def compFin {m n : ℕ} (i : Fin m) (α : P m) (β : P n) : P (m - 1 + n) :=
  reindex R P (by have := i.isLt; omega)
    (comp (R := R) (i : ℕ) (m - (i : ℕ) - 1)
      (reindex R P (by have := i.isLt; omega) α) β)

/-- `comp` only depends on its trailing index up to equality: changing `b` to an equal `b'`
just conjugates by reindexings.
@isnad1 id=eq.1h8v.s12.7c44595c749c from=translated src=- shape=7d42be04 vocab=2a8d7de1
-/
lemma comp_index_congr (a : ℕ) {b b' : ℕ} (hb : b = b') {n : ℕ}
    (α : P (a + 1 + b)) (β : P n) :
    comp (R := R) a b' (reindex R P (by omega) α) β
      = reindex R P (by omega) (comp (R := R) a b α β) := by
  subst hb; simp

/-- `comp` only depends on the arity of its second argument up to equality. Companion to
`comp_index_congr`, which does the same for the trailing index.
@isnad1 id=eq.1h8v.s11.2dc51bcbe935 from=translated src=- shape=2581053d vocab=47077a25
-/
lemma comp_arity_congr (a b : ℕ) {n n' : ℕ} (hn : n = n') (α : P (a + 1 + b)) (β : P n) :
    comp (R := R) a b α (reindex R P hn β)
      = reindex R P (by omega) (comp (R := R) a b α β) := by
  subst hn; simp

/-- `comp` only depends on its *leading* index up to equality. The third companion to
`comp_index_congr` (trailing index) and `comp_arity_congr` (arity of the second argument).
@isnad1 id=eq.1h8v.s12.d4de2400d0b8 from=translated src=- shape=14a8d71c vocab=91e4d7a3
-/
lemma comp_leading_congr {a a' : ℕ} (ha : a = a') (b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n) :
    comp (R := R) a' b (reindex R P (by omega) α) β
      = reindex R P (by omega) (comp (R := R) a b α β) := by
  subst ha; simp

/--
@isnad1 id=eq.0h8v.s8.869dcd3f0de7 from=translated src=- shape=a7c8ff8e vocab=fe3300ee
-/
lemma compFin_add_left {m n : ℕ} (i : Fin m) (α α' : P m) (β : P n) :
    compFin (R := R) i (α + α') β = compFin (R := R) i α β + compFin (R := R) i α' β := by
  simp only [compFin, map_add, LinearMap.add_apply]

/--
@isnad1 id=eq.0h8v.s8.ca9338ac5bf6 from=translated src=- shape=808964ab vocab=fe3300ee
-/
lemma compFin_add_right {m n : ℕ} (i : Fin m) (α : P m) (β β' : P n) :
    compFin (R := R) i α (β + β') = compFin (R := R) i α β + compFin (R := R) i α β' := by
  simp only [compFin, map_add]

/--
@isnad1 id=eq.0h8v.s9.60eda40016e9 from=translated src=- shape=5a523f92 vocab=fc7aa6b5
-/
lemma compFin_smul_left {m n : ℕ} (i : Fin m) (r : R) (α : P m) (β : P n) :
    compFin (R := R) i (r • α) β = r • compFin (R := R) i α β := by
  simp only [compFin, map_smul, LinearMap.smul_apply]

/--
@isnad1 id=eq.0h8v.s9.0aa3b8489c4f from=translated src=- shape=c349f209 vocab=fc7aa6b5
-/
lemma compFin_smul_right {m n : ℕ} (i : Fin m) (r : R) (α : P m) (β : P n) :
    compFin (R := R) i α (r • β) = r • compFin (R := R) i α β := by
  simp only [compFin, map_smul]

/--
@isnad1 id=eq.0h6v.s8.08f5c9c87fde from=translated src=- shape=65bdec00 vocab=fe3300ee
-/
@[simp] lemma compFin_zero_left {m n : ℕ} (i : Fin m) (β : P n) :
    compFin (R := R) i (0 : P m) β = 0 := by
  simp only [compFin, map_zero, LinearMap.zero_apply]

/--
@isnad1 id=eq.0h6v.s8.248e7b01a952 from=translated src=- shape=bffdbb79 vocab=fe3300ee
-/
@[simp] lemma compFin_zero_right {m n : ℕ} (i : Fin m) (α : P m) :
    compFin (R := R) i α (0 : P n) = 0 := by
  simp only [compFin, map_zero]

/-- On an operation of arity `a + 1 + b`, composing at the `Fin` slot `a` agrees with the
positional composition, up to the reindexing `a + 1 + b - 1 + n = a + n + b`.
@isnad1 id=eq.0h7v.s11.a6fc5d8c4f56 from=translated src=- shape=0d2ea3e1 vocab=491c89e9
-/
lemma compFin_eq_comp (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n) :
    compFin (R := R) ⟨a, by omega⟩ α β
      = reindex R P (by omega) (comp (R := R) a b α β) := by
  unfold compFin
  simp only [Fin.val_mk]
  rw [comp_index_congr a (show b = a + 1 + b - a - 1 by omega) α β]
  simp

/-- `compFin` only depends on the arity of its first argument up to equality.
@isnad1 id=eq.2h8v.s10.d36de8766a41 from=translated src=- shape=f4cd447b vocab=404a0373
-/
lemma compFin_reindex_left {m m' n : ℕ} (h : m = m') {p : ℕ} (hp : p < m) (α : P m) (β : P n) :
    compFin (R := R) (⟨p, by omega⟩ : Fin m') (reindex R P h α) β
      = reindex R P (by omega) (compFin (R := R) ⟨p, hp⟩ α β) := by
  subst h
  simp

/-- `compFin` only depends on the arity of its second argument up to equality.
@isnad1 id=eq.2h8v.s10.b476e5a07a80 from=translated src=- shape=5bb34aad vocab=cec489bd
-/
lemma compFin_reindex_right {m n n' : ℕ} (h : n = n') {p : ℕ} (hp : p < m) (α : P m) (β : P n) :
    compFin (R := R) ⟨p, hp⟩ α (reindex R P h β)
      = reindex R P (by omega) (compFin (R := R) ⟨p, hp⟩ α β) := by
  subst h
  simp

end CompFin

/-- A morphism of non-symmetric operads: a family of linear maps preserving the identity and
all partial compositions.-/
structure NSOperadHom (R : Type u) [CommRing R]
    (P : ℕ → Type v) [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
    (Q : ℕ → Type w) [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q] where
  /-- The underlying linear map in each arity.-/
  app (n : ℕ) : P n →ₗ[R] Q n
  /-- The identity operation is preserved.-/
  app_one : app 1 (one (R := R) (P := P)) = one (R := R) (P := Q)
  /-- Partial composition is preserved.-/
  app_comp (a b : ℕ) {n : ℕ} (α : P (a + 1 + b)) (β : P n) :
    app (a + n + b) (comp (R := R) a b α β)
      = comp (R := R) a b (app (a + 1 + b) α) (app n β)

namespace NSOperadHom

variable {R : Type u} [CommRing R]
  {P : ℕ → Type v} [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]
  {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]

/-- Two morphisms agreeing in every arity are equal.
@isnad1 id=eq.1h5v.s7.b26f69522af2 from=translated src=- shape=c2a9c17c vocab=974d343e
-/
@[ext]
lemma ext {f g : NSOperadHom R P Q} (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f; cases g; congr 1; funext n; exact h n

/-- The identity morphism.-/
protected def id : NSOperadHom R P P where
  app _ := LinearMap.id
  app_one := rfl
  app_comp := by intros; rfl

/--
@isnad1 id=eq.0h3v.s7.124621df6606 from=translated src=- shape=379819c4 vocab=3b281541
-/
@[simp]
lemma id_app (n : ℕ) : (NSOperadHom.id (R := R) (P := P)).app n = LinearMap.id := rfl

variable {S : ℕ → Type w'} [∀ n, AddCommGroup (S n)] [∀ n, Module R (S n)] [NSOperad R S]

/-- Morphisms of operads commute with reindexing.
@isnad1 id=eq.1h7v.s9.91ebd04e053c from=translated src=- shape=1b743e19 vocab=07cebaa1
-/
lemma app_reindex (φ : NSOperadHom R P Q) {m n : ℕ} (h : m = n) (x : P m) :
    φ.app n (reindex R P h x) = reindex R Q h (φ.app m x) := by
  subst h
  rw [reindex_self, reindex_self]

/-- Morphisms of operads commute with `compFin`.
@isnad1 id=eq.0h9v.s9.0c769c619da1 from=translated src=- shape=f398b56a vocab=dffdbc2e
-/
lemma app_compFin (φ : NSOperadHom R P Q) {m n : ℕ} (i : Fin m) (α : P m) (β : P n) :
    φ.app (m - 1 + n) (compFin (R := R) i α β)
      = compFin (R := R) i (φ.app m α) (φ.app n β) := by
  simp only [compFin, app_reindex, φ.app_comp]

/-- Composition of morphisms of operads.-/
protected def comp (g : NSOperadHom R Q S) (f : NSOperadHom R P Q) : NSOperadHom R P S where
  app n := (g.app n).comp (f.app n)
  app_one := by
    simp only [LinearMap.comp_apply, f.app_one, g.app_one]
  app_comp := by
    intros
    simp only [LinearMap.comp_apply, f.app_comp, g.app_comp]

/--
@isnad1 id=eq.0h7v.s8.83026adf6782 from=translated src=- shape=29395f55 vocab=b3080fd1
-/
@[simp]
lemma comp_app (g : NSOperadHom R Q S) (f : NSOperadHom R P Q) (n : ℕ) :
    (g.comp f).app n = (g.app n).comp (f.app n) := rfl

/--
@isnad1 id=eq.0h4v.s7.da6c04da1a91 from=translated src=- shape=2a94bf3f vocab=60f96049
-/
@[simp]
lemma comp_id (f : NSOperadHom R P Q) : f.comp NSOperadHom.id = f := by ext n; rfl

/--
@isnad1 id=eq.0h4v.s7.d908bc457c8c from=translated src=- shape=6a98cd25 vocab=60f96049
-/
@[simp]
lemma id_comp (f : NSOperadHom R P Q) : NSOperadHom.id.comp f = f := by ext n; rfl

end NSOperadHom

end Operad
