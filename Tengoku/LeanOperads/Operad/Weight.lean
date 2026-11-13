/-
# The weight grading on the free operad

The weight of a tree is its number of internal vertices, and `Tree.weight_graft` says grafting
adds weights. Transported to `Free R E` this is the grading Koszul duality runs on: a presentation
is *quadratic* when its relations live in weight two, and the Koszul complex is built weight by
weight.

The statement that matters is `Free.comp_mem_weightSpan`: operadic composition of something of
weight `w₁` with something of weight `w₂` has weight `w₁ + w₂`. Note the contrast with arity,
which composition changes in a way depending on where the composition happens; weight does not
care about the slot at all.
-/
import Tengoku.LeanOperads.Operad.Free
import Tengoku.LeanOperads.Operad.TotalComp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open NSOperad

variable {R : Type u} [CommRing R] {E : ℕ → Type v}

/-- The weight of a tree of specified arity.-/
def TreeOfArity.weight {n : ℕ} (t : TreeOfArity E n) : ℕ := t.val.weight

/--
@isnad1 id=eq.0h3v.s4.1f5d4ced6201 from=translated src=- shape=5a9c60db vocab=635c414d
-/
lemma TreeOfArity.weight_def {n : ℕ} (t : TreeOfArity E n) :
    t.weight = t.val.weight := rfl

/-- **Grafting adds weights**, at the level of arity-indexed trees.
@isnad1 id=eq.0h6v.s6.c87c7c934e9d from=translated src=- shape=f45d8d23 vocab=b0f3a5cc
-/
@[simp] lemma TreeOfArity.graft_weight (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b))
    (s : TreeOfArity E n) :
    (TreeOfArity.graft a b t s).weight = t.weight + s.weight := by
  have ht := t.property
  exact Tree.weight_graft t.val a s.val (by omega)

/-- The submodule of `Free R E n` spanned by the trees of weight `w`.-/
noncomputable def Free.weightSpan (R : Type u) [CommRing R] (E : ℕ → Type v) (n w : ℕ) :
    Submodule R (Free R E n) :=
  Submodule.span R {x | ∃ t : TreeOfArity E n, t.weight = w ∧ Free.gen (R := R) t = x}

/--
@isnad1 id=mem.0h4v.s7.5c9f8b62df73 from=translated src=- shape=25679776 vocab=b6c994ec
-/
lemma Free.gen_mem_weightSpan {n : ℕ} (t : TreeOfArity E n) :
    Free.gen (R := R) t ∈ Free.weightSpan R E n t.weight :=
  Submodule.subset_span ⟨t, rfl, rfl⟩

/-- Reindexing preserves weight.
@isnad1 id=mem.2h6v.s9.ef2c0758b9b0 from=translated src=- shape=ae513e4e vocab=3c40c3f7
-/
lemma Free.reindex_mem_weightSpan {m n w : ℕ} (h : m = n) {x : Free R E m}
    (hx : x ∈ Free.weightSpan R E m w) :
    reindex R (Free R E) h x ∈ Free.weightSpan R E n w := by
  subst h
  simpa using hx

end Operad
