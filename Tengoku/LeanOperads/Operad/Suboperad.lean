/-
# Suboperads

An arity-wise family of submodules closed under the identity and partial composition. The point
is `instNSOperadSub`: such a family is itself an operad, so a concrete operad can be exhibited
*inside* `End V` without re-proving any of the four axioms.
-/
import Tengoku.LeanOperads.Operad.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open NSOperad

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- A suboperad of `P`: a submodule in each arity, containing the identity and closed under
partial composition.-/
structure Suboperad (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] where
  /-- The submodule of operations of each arity.-/
  carrier (n : ℕ) : Submodule R (P n)
  /-- The identity operation belongs to the suboperad.-/
  one_mem' : one (R := R) (P := P) ∈ carrier 1
  /-- The suboperad is closed under partial composition.-/
  comp_mem' (a b : ℕ) {n : ℕ} {α : P (a + 1 + b)} {β : P n} :
    α ∈ carrier (a + 1 + b) → β ∈ carrier n → comp (R := R) a b α β ∈ carrier (a + n + b)

namespace Suboperad

variable (S : Suboperad R P)

instance : CoeSort (Suboperad R P) (ℕ → Type v) := ⟨fun S n => S.carrier n⟩

/-- Reindexing inside a suboperad agrees with reindexing in the ambient operad.-/
lemma coe_reindex {m n : ℕ} (h : m = n) (x : S.carrier m) :
    ((reindex R (fun k => (S.carrier k : Type v)) h x : S.carrier n) : P n)
      = reindex R P h (x : P m) := by
  subst h; rfl

/-- Partial composition, restricted to a suboperad.-/
def compSub (a b : ℕ) {n : ℕ} :
    (S.carrier (a + 1 + b)) →ₗ[R] (S.carrier n) →ₗ[R] (S.carrier (a + n + b)) where
  toFun α :=
    { toFun := fun β => ⟨comp (R := R) a b (α : P _) (β : P _), S.comp_mem' a b α.2 β.2⟩
      map_add' := fun β β' => by
        refine Subtype.ext ?_
        simp
      map_smul' := fun r β => by
        refine Subtype.ext ?_
        simp }
  map_add' α α' := by
    refine LinearMap.ext fun β => Subtype.ext ?_
    simp
  map_smul' r α := by
    refine LinearMap.ext fun β => Subtype.ext ?_
    simp

@[simp] lemma coe_compSub (a b : ℕ) {n : ℕ} (α : S.carrier (a + 1 + b)) (β : S.carrier n) :
    ((S.compSub a b α β : S.carrier (a + n + b)) : P (a + n + b))
      = comp (R := R) a b (α : P _) (β : P _) := rfl

end Suboperad

end Operad
