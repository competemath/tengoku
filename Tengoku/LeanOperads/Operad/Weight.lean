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

lemma TreeOfArity.weight_def {n : ℕ} (t : TreeOfArity E n) :
    t.weight = t.val.weight := rfl

/-- **Grafting adds weights**, at the level of arity-indexed trees.-/
@[simp] lemma TreeOfArity.graft_weight (a b : ℕ) {n : ℕ} (t : TreeOfArity E (a + 1 + b))
    (s : TreeOfArity E n) :
    (TreeOfArity.graft a b t s).weight = t.weight + s.weight := by
  have ht := t.property
  exact Tree.weight_graft t.val a s.val (by omega)

/-- The submodule of `Free R E n` spanned by the trees of weight `w`.-/
noncomputable def Free.weightSpan (R : Type u) [CommRing R] (E : ℕ → Type v) (n w : ℕ) :
    Submodule R (Free R E n) :=
  Submodule.span R {x | ∃ t : TreeOfArity E n, t.weight = w ∧ Free.gen (R := R) t = x}

lemma Free.gen_mem_weightSpan {n : ℕ} (t : TreeOfArity E n) :
    Free.gen (R := R) t ∈ Free.weightSpan R E n t.weight :=
  Submodule.subset_span ⟨t, rfl, rfl⟩

/-- Reindexing preserves weight.-/
lemma Free.reindex_mem_weightSpan {m n w : ℕ} (h : m = n) {x : Free R E m}
    (hx : x ∈ Free.weightSpan R E m w) :
    reindex R (Free R E) h x ∈ Free.weightSpan R E n w := by
  subst h
  simpa using hx

end Operad
