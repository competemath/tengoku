/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.Seed.Combinatorics.SimpleGraph.Finite
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Finite
import Tengoku.Seed.Combinatorics.SimpleGraph.DegreeSum
import Tengoku.Seed.Data.Finset.Card
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Data.Int.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/Prerequisites/TwoFactorDefs.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Manuscript barrier quantity Δ(S,T)

Definitions matching `main.tex` Section 8:

* `h(S,T)` counts components `D` of `G - (S ∪ T)` for which `e(D,T)` is odd
  (odd *attachment*, not odd order);
* `Δ(S,T) = 2|S| - 2|T| + ∑_{t∈T} d_{G-S}(t) - h(S,T)`, valued in `ℤ`.
-/

universe u

namespace Nikoghosyan
namespace TwoFactor

open SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of ordered pairs `(a,b) ∈ A × B` with `G.Adj a b`. If `A` and `B`
are disjoint this is `e(A,B)`; if `A = B` it is twice the number of internal
edges.-/
def orderedEdgeCount (A B : Finset V) : ℕ :=
  ((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card

/-- Degree of `t` in `G - S`, i.e. `|N(t) \ S|`.-/
def degDelete (S : Finset V) (t : V) : ℕ :=
  (G.neighborFinset t \ S).card

/-- Remainder `U = V \ (S ∪ T)`. The unused graph argument records that this
is the remainder of `G` after deleting `S ∪ T`.-/
def remainderVerts (_G : SimpleGraph V) (S T : Finset V) : Finset V :=
  (Finset.univ : Finset V) \ (S ∪ T)

/-- Vertex set in `V` of a remainder component of `G.induce (S ∪ T)ᶜ`.-/
def componentVerts (S T : Finset V)
    (c : (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).ConnectedComponent) : Finset V :=
  c.supp.toFinset.image Subtype.val

/-- Number of original edges from a remainder component to `T`.-/
def componentAttach (S T : Finset V)
    (c : (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).ConnectedComponent) : ℕ :=
  orderedEdgeCount G (componentVerts G S T c) T

/-- `h(S,T)`: number of remainder components with odd attachment to `T`.-/
def hCount (S T : Finset V) : ℕ :=
  ((Finset.univ : Finset
      ((G.induce ((S ∪ T : Finset V) : Set V)ᶜ).ConnectedComponent)).filter
    fun c => Odd (componentAttach G S T c)).card

/-- Manuscript barrier value `Δ(S,T)`, valued in `ℤ`.-/
def delta (S T : Finset V) : ℤ :=
  2 * (S.card : ℤ) - 2 * (T.card : ℤ)
    + (∑ t ∈ T, (degDelete G S t : ℤ))
    - (hCount G S T : ℤ)

/--
@isnad1 id=eq.0h4v.s5.76b06b60c598 from=translated src=- shape=c01cd062 vocab=3f3d3469
-/
lemma remainderVerts_eq (S T : Finset V) :
    remainderVerts G S T = (Finset.univ : Finset V) \ (S ∪ T) := rfl

/--
@isnad1 id=eq.0h4v.s6.9db20179b13c from=translated src=- shape=cd9b19b1 vocab=822b2ee6
-/
lemma degDelete_eq (S : Finset V) (t : V) :
    degDelete G S t = (G.neighborFinset t \ S).card := rfl

/--
@isnad1 id=eq.0h3v.s5.cee5ddb0638e from=translated src=- shape=07fbdba0 vocab=3fb656ed
-/
lemma orderedEdgeCount_empty_right (A : Finset V) :
    orderedEdgeCount G A ∅ = 0 := by
  simp [orderedEdgeCount]

/--
@isnad1 id=eq.0h3v.s5.cb6b11c6622c from=translated src=- shape=82a33eeb vocab=3fb656ed
-/
lemma orderedEdgeCount_empty_left (B : Finset V) :
    orderedEdgeCount G ∅ B = 0 := by
  simp [orderedEdgeCount]

/--
@isnad1 id=eq.0h4v.s6.2fb1c0315499 from=translated src=- shape=802bd3e4 vocab=0e7212bb
-/
lemma componentAttach_empty_T (S : Finset V)
    (c : (G.induce ((S ∪ (∅ : Finset V) : Finset V) : Set V)ᶜ).ConnectedComponent) :
    componentAttach G S ∅ c = 0 := by
  simp [componentAttach, orderedEdgeCount]

/--
@isnad1 id=eq.0h3v.s5.91f4e410c6f8 from=translated src=- shape=07fbdba0 vocab=63a3dea3
-/
lemma hCount_empty_T (S : Finset V) : hCount G S ∅ = 0 := by
  simp [hCount, componentAttach, orderedEdgeCount]

/--
@isnad1 id=eq.0h3v.s5.5a710addbde3 from=translated src=- shape=6ffdb20e vocab=85e184d5
-/
lemma delta_empty_T (S : Finset V) :
    delta G S ∅ = 2 * (S.card : ℤ) := by
  simp [delta, hCount_empty_T, degDelete]

/--
@isnad1 id=eq.0h4v.s6.f6a0028e40ef from=translated src=- shape=66a69a9e vocab=ee1db999
-/
lemma neighborFinset_inter (A : Finset V) (a : V) :
    G.neighborFinset a ∩ A = A.filter (G.Adj a) := by
  ext b
  simp [mem_neighborFinset, and_comm]

/--
@isnad1 id=eq.0h3v.s6.f1c967574fac from=translated src=- shape=ba195bb0 vocab=fd90bae1
-/
lemma orderedEdgeCount_self_eq_sum (A : Finset V) :
    orderedEdgeCount G A A = ∑ a ∈ A, (G.neighborFinset a ∩ A).card := by
  simp only [orderedEdgeCount, neighborFinset_inter]
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ha => ?_
  exact (Finset.card_filter (G.Adj a) A).symm

/-- Internal original-edge count `e(T)` as half the ordered self-count. The
factor of two is proved in `TwoFactorParity`.-/
def internalEdgeCount (T : Finset V) : ℕ :=
  orderedEdgeCount G T T / 2

end TwoFactor
end Nikoghosyan
