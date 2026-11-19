import Tengoku.Linearhadwiger.HadwigerLean.Graph.MassedPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Edge-incidence monotonicity

Deleting edges cannot increase the number of edges incident to a fixed
vertex set. This is used when transferring the shore condition of a
massed pair to an edge-deleted graph.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

/-- Edge-incidence count is monotone in the host graph.
@isnad1 id=le.1h4v.s5.a732542e99de from=translated src=- shape=5bda172c vocab=5a49c860
-/
theorem edgeIncidenceSetCount_mono {H G : SimpleGraph V}
    (hHG : H ≤ G) (S : Set V) :
    edgeIncidenceSetCount H S ≤ edgeIncidenceSetCount G S := by
  let f : edgeIncidenceSet H S → edgeIncidenceSet G S := fun e =>
    ⟨⟨e.1.1, (SimpleGraph.edgeSet_mono hHG) e.1.2⟩, e.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : edgeIncidenceSet G S => z.1.1) hxy
  exact Nat.card_le_card_of_injective f hinj

/-- Deleting any set of edges weakens the edge-incidence count.
@isnad1 id=le.0h4v.s4.4fbd6a0c7544 from=translated src=- shape=d41a8501 vocab=f35d93bd
-/
theorem edgeIncidenceSetCount_deleteEdges_le
    (G : SimpleGraph V) (E : Set (Sym2 V)) (S : Set V) :
    edgeIncidenceSetCount (G.deleteEdges E) S ≤
      edgeIncidenceSetCount G S :=
  edgeIncidenceSetCount_mono (G.deleteEdges_le E) S

end HadwigerLean
