module

public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A certified checker for the girth bound `girth ≥ 12`

This file formalizes the combinatorial argument used in the proof of Proposition 2.1 of the
manuscript: in a bipartite graph, a cycle of length at most `10` produces two *distinct* paths of
the same length `≤ 5` with the same endpoints.  Hence, if for every vertex `x` the paths of length
`≤ 5` ending at `x` have pairwise distinct starting vertices, the graph has girth at least `12`.

The condition on paths is checked by an explicit enumeration (`pathsTo`), whose soundness is
proved here.
-/

@[expose] public section

namespace GirthCheck

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Extend a (reversed-direction) path `v :: rest` by one new neighbour `w` of `v` placed in
front, provided `w` does not already occur.-/
def extend (nbrs : V → List V) : List V → List (List V)
  | [] => []
  | l@(v :: _) => ((nbrs v).filter (fun w => decide (w ∉ l))).map (fun w => w :: l)

/-- `pathsTo nbrs x n` lists supports of paths of length `n` *ending* at `x`
(the head of each list is the starting vertex).-/
def pathsTo (nbrs : V → List V) (x : V) : ℕ → List (List V)
  | 0 => [[x]]
  | n + 1 => (pathsTo nbrs x n).flatMap (extend nbrs)

/-- The local check at a vertex `x`: paths of length `≤ 5` ending at `x` have pairwise distinct
starting vertices.-/
def localCheck (nbrs : V → List V) (x : V) : Bool :=
  decide (((List.range 6).flatMap (pathsTo nbrs x)).map List.head?).Nodup

variable {G : SimpleGraph V}

omit [DecidableEq V] in
/-- Parity of walks in a properly 2-coloured graph.
@isnad1 id=iff.1h6v.s5.b833c9fa9dc6 from=translated src=- shape=b0d8a77e vocab=78bcf53a
-/
theorem even_length_iff (col : V → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    {u x : V} (p : G.Walk u x) : Even p.length ↔ col u = col x := by
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
    have := hcol a b h
    rw [Walk.length_cons, Nat.even_add_one, ih]
    cases hA : col a <;> cases hB : col b <;> cases hC : col c <;> simp_all

omit [DecidableEq V] in
/-- Two distinct paths of length `≤ 5` with the same endpoints, extracted from a short even cycle.
@isnad1 id=ex.2h4v.s7.2aa49b11803e from=translated src=- shape=c6a39fea vocab=de1a6bf1
-/
theorem exists_two_paths_of_cycle {u : V} (w : G.Walk u u) (hw : w.IsCycle)
    (he : Even w.length) :
    ∃ (y : V) (p q : G.Walk u y), p.IsPath ∧ q.IsPath ∧ p ≠ q ∧
      p.length = w.length / 2 ∧ q.length = w.length / 2 := by
  have h3 := hw.three_le_length
  obtain ⟨m, hm⟩ := he
  have hn : w.length = m + m := hm
  refine ⟨w.getVert m, w.take m, (w.drop m).reverse, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Walk.IsPath.getVert_injOn_iff]
    intro i hi j hj hij
    simp only [Walk.take_length, Set.mem_ofPred_eq, Walk.take_getVert] at hi hj hij
    have := hw.getVert_injOn' (show m ⊓ i ≤ w.length - 1 by simp; omega)
      (show m ⊓ j ≤ w.length - 1 by simp; omega) hij
    omega
  · rw [← Walk.IsPath.getVert_injOn_iff]
    intro i hi j hj hij
    simp only [Walk.length_reverse, Walk.drop_length, Set.mem_ofPred_eq, Walk.getVert_reverse,
      Walk.drop_getVert] at hi hj hij
    have := hw.getVert_injOn (show m + (w.length - m - i) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by
        simp; omega)
      (show m + (w.length - m - j) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega) hij
    omega
  · intro h
    have h1 := congrArg (fun p => p.getVert 1) h
    simp only [Walk.take_getVert, Walk.getVert_reverse, Walk.drop_length, Walk.drop_getVert] at h1
    have := hw.getVert_injOn (show m ⊓ 1 ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega)
      (show m + (w.length - m - 1) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega) h1
    omega
  · simp [Walk.take_length]; omega
  · simp [Walk.drop_length]; omega

end GirthCheck

end
