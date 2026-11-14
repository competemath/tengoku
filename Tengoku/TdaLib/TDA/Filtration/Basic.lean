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

/-- Membership in the support is equivalent to membership of the corresponding singleton face.
@isnad1 id=iff.0h5v.s6.112bb66fc66c from=translated src=- shape=85eb1e1d vocab=c89eaf94
-/
theorem mem_support_iff (K : SimplicialFiltration P V) (p : P) (x : V) :
    x ∈ support K p ↔ ({x} : Finset V) ∈ K p := Iff.rfl

/-- The bottom preabstract complex has no faces.
@isnad1 id=iff.0h2v.s4.fc71df782288 from=translated src=- shape=791e3b42 vocab=83e521f5
-/
@[simp]
theorem mem_bot_iff (s : Finset V) :
    s ∈ (⊥ : PreAbstractSimplicialComplex V) ↔ False := Iff.rfl

/-- Every face present at `p` remains present at any later index `q`.
@isnad1 id=mem.2h6v.s6.c8f548c11d1f from=translated src=- shape=88562ed1 vocab=9881c99d
-/
theorem face_mono (K : SimplicialFiltration P V) {p q : P} (hpq : p ≤ q)
    {s : Finset V} (hs : s ∈ K p) : s ∈ K q :=
  K.monotone hpq hs

/-- Support can only grow along the preorder.
@isnad1 id=le.1h5v.s5.5340ab495f74 from=translated src=- shape=eb5273b9 vocab=677b505d
-/
theorem support_mono (K : SimplicialFiltration P V) {p q : P} (hpq : p ≤ q) :
    support K p ⊆ support K q := by
  intro x hx
  exact mem_support_iff K q x |>.2 (face_mono K hpq (mem_support_iff K p x |>.1 hx))

/-- A stage whose complex is bottom has no supported vertices.
@isnad1 id=eq.1h4v.s5.50a133d50f61 from=translated src=- shape=ebc7f2d4 vocab=12b3dd74
-/
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

/-- A finite face belongs to `singletonFace x` exactly when it is `{x}`.
@isnad1 id=iff.0h3v.s5.51cf72962b1e from=translated src=- shape=797472b2 vocab=bb3e33b4
-/
theorem mem_singletonFace_iff (x : V) (s : Finset V) :
    s ∈ singletonFace x ↔ s = {x} := Iff.rfl

/-- `addSingletons` inserts every ambient singleton, including one at a would-be empty stage.

This witness is conditional on an explicit ambient vertex `x`; for an empty vertex type there is
no such witness and no support change is asserted.
@isnad1 id=mem.0h2v.s4.2e98bfd57c12 from=translated src=- shape=c292e4fc vocab=2b24a40e
-/
theorem addSingletons_introduces_singleton (x : V) :
    ({x} : Finset V) ∈ (⊥ : PreAbstractSimplicialComplex V).addSingletons :=
  AbstractSimplicialComplex.singleton_mem _ x

/-- Reindex a filtration by precomposition with a monotone map.-/
def reindex {Q : Type w} [Preorder Q] (u : Q →o P) (K : SimplicialFiltration P V) :
    SimplicialFiltration Q V :=
  K.comp u

/-- Evaluation of a reindexed filtration is evaluation at the mapped index.
@isnad1 id=eq.0h6v.s6.b95be27dcbd0 from=translated src=- shape=cf733284 vocab=590f2901
-/
@[simp]
theorem reindex_apply {Q : Type w} [Preorder Q] (u : Q →o P)
    (K : SimplicialFiltration P V) (q : Q) : reindex u K q = K (u q) := rfl

/-- Reindexing by the identity order hom leaves the filtration unchanged.
@isnad1 id=eq.0h3v.s4.c96022351744 from=translated src=- shape=841bb50f vocab=af2ecd90
-/
theorem reindex_id (K : SimplicialFiltration P V) :
    reindex (OrderHom.id : P →o P) K = K := by
  ext p
  rfl

/-- Reindexing successively by `u` and `v` is reindexing by their composite `u.comp v`.
@isnad1 id=eq.0h7v.s6.3e77b22b9eb3 from=translated src=- shape=78b83cf7 vocab=1a850147
-/
theorem reindex_comp {Q : Type w} [Preorder Q] {S : Type x} [Preorder S]
    (u : Q →o P) (v : S →o Q) (K : SimplicialFiltration P V) :
    reindex v (reindex u K) = reindex (u.comp v) K := by
  ext s
  rfl

end TDA.Filtration
