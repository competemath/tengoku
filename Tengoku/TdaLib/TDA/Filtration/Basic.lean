import Tengoku.Seed.AlgebraicTopology.SimplicialComplex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Support-aware simplicial filtrations

A filtration fixes an ambient vertex type and assigns a `PreAbstractSimplicialComplex` to each
index in a preorder. Its support consists exactly of the vertices whose singleton faces occur at
that index. In particular, the empty complex has empty support, and vertices can enter at distinct
stages.

The underlying face convention is mathlib's `PreAbstractSimplicialComplex` from
`Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean` at the pinned mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`: faces are nonempty finite sets and are closed under
nonempty subsets. The empty simplex is not included.
-/

universe u v w x

namespace TDA.Filtration

/-- A support-aware simplicial filtration on a preorder `P` with fixed ambient vertices `V`.

The value at each index is a mathlib `PreAbstractSimplicialComplex`; monotonicity means faces only
appear as the index increases. No finiteness, decidable equality, or nonemptiness assumption is
placed on the ambient vertex type.-/
abbrev SimplicialFiltration (P : Type u) [Preorder P] (V : Type v) :=
  P →o PreAbstractSimplicialComplex V

variable {P : Type u} [Preorder P] {V : Type v}

/-- The support of a filtration at `p`: precisely those ambient vertices whose singleton is a
face at that stage.-/
def support (K : SimplicialFiltration P V) (p : P) : Set V :=
  {x | ({x} : Finset V) ∈ K p}

/-- Membership in the support is equivalent to membership of the corresponding singleton face.-/
theorem mem_support_iff (K : SimplicialFiltration P V) (p : P) (x : V) :
    x ∈ support K p ↔ ({x} : Finset V) ∈ K p := Iff.rfl

/-- The bottom preabstract complex has no faces.-/
@[simp]
theorem mem_bot_iff (s : Finset V) :
    s ∈ (⊥ : PreAbstractSimplicialComplex V) ↔ False := Iff.rfl

/-- Every face present at `p` remains present at any later index `q`.-/
theorem face_mono (K : SimplicialFiltration P V) {p q : P} (hpq : p ≤ q)
    {s : Finset V} (hs : s ∈ K p) : s ∈ K q :=
  K.monotone hpq hs

/-- Support can only grow along the preorder.-/
theorem support_mono (K : SimplicialFiltration P V) {p q : P} (hpq : p ≤ q) :
    support K p ⊆ support K q := by
  intro x hx
  exact mem_support_iff K q x |>.2 (face_mono K hpq (mem_support_iff K p x |>.1 hx))

/-- A stage whose complex is bottom has no supported vertices.-/
theorem support_eq_empty_of_eq_bot (K : SimplicialFiltration P V) (p : P)
    (hp : K p = ⊥) : support K p = ∅ := by
  ext x
  simp [support, hp]

/-- The preabstract complex with exactly the singleton face `{x}`.-/
def singletonFace (x : V) : PreAbstractSimplicialComplex V where
  faces := {s | s = {x}}
  isRelLowerSet_faces := by
    intro s hs
    constructor
    · rw [hs]
      exact Finset.singleton_nonempty x
    · intro t hts ht
      change s = {x} at hs
      cases Finset.subset_singleton_iff.mp (hs ▸ hts) with
      | inl h => exact (ht.ne_empty h).elim
      | inr h => exact h

/-- A finite face belongs to `singletonFace x` exactly when it is `{x}`.-/
theorem mem_singletonFace_iff (x : V) (s : Finset V) :
    s ∈ singletonFace x ↔ s = {x} := Iff.rfl

/-- `addSingletons` inserts every ambient singleton, including one at a would-be empty stage.

This witness is conditional on an explicit ambient vertex `x`; for an empty vertex type there is
no such witness and no support change is asserted.-/
theorem addSingletons_introduces_singleton (x : V) :
    ({x} : Finset V) ∈ (⊥ : PreAbstractSimplicialComplex V).addSingletons :=
  AbstractSimplicialComplex.singleton_mem _ x

/-- Reindex a filtration by precomposition with a monotone map.-/
def reindex {Q : Type w} [Preorder Q] (u : Q →o P) (K : SimplicialFiltration P V) :
    SimplicialFiltration Q V :=
  K.comp u

/-- Evaluation of a reindexed filtration is evaluation at the mapped index.-/
@[simp]
theorem reindex_apply {Q : Type w} [Preorder Q] (u : Q →o P)
    (K : SimplicialFiltration P V) (q : Q) : reindex u K q = K (u q) := rfl

/-- Reindexing by the identity order hom leaves the filtration unchanged.-/
theorem reindex_id (K : SimplicialFiltration P V) :
    reindex (OrderHom.id : P →o P) K = K := by
  ext p
  rfl

/-- Reindexing successively by `u` and `v` is reindexing by their composite `u.comp v`.-/
theorem reindex_comp {Q : Type w} [Preorder Q] {S : Type x} [Preorder S]
    (u : Q →o P) (v : S →o Q) (K : SimplicialFiltration P V) :
    reindex v (reindex u K) = reindex (u.comp v) K := by
  ext s
  rfl

end TDA.Filtration
