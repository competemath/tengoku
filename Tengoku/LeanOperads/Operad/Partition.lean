/-
# Transporting partitions along a bijection

The substitution product of species is indexed by partitions: `(F ∘ G)(S)` is a sum over the
partitions of `S`, of `F` applied to the set of blocks tensored with `G` applied to each block.
For that sum to be functorial in `S`, partitions have to be transported along bijections, and
that transport has to respect identities and composition.

This file builds exactly that indexing layer. Mathlib's `Finpartition.map` transports along an
*order* isomorphism, so the work is to turn a bijection of finite types into an order isomorphism
of their `Finset` lattices, and then to check the two functor laws.
-/
import Tengoku.Seed.Order.Partition.Finpartition
import Tengoku.Seed.Data.Finset.Image

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open Finset

variable {α : Type u} {β : Type v} {γ : Type*}

variable [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]

omit [DecidableEq α] [DecidableEq β] in
lemma map_univ_equiv (e : α ≃ β) : (univ : Finset α).map e.toEmbedding = univ := by
  ext b
  simp only [Finset.mem_map, Finset.mem_univ, true_and, iff_true]
  exact ⟨e.symm b, by simp⟩

end Operad
