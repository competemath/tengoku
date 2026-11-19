import Tengoku.Linearhadwiger.HadwigerLean.Graph.Finite
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vertex connectivity for finite simple graphs

The convention agrees with the paper: an `r`-connected graph has more than
`r` vertices, and deleting fewer than `r` vertices leaves a connected graph.
The deletion is represented by an induced graph on the complement of a finite
set. This avoids assigning a connectivity value to the empty graph.
-/

namespace HadwigerLean

variable {V : Type*} [Fintype V]

/-- `G` is `k`-vertex-connected, using the paper's strict order convention.-/
def VertexConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ U : Finset V, U.card < k → (G.induce (U : Set V)ᶜ).Connected

namespace VertexConnected

variable {G : SimpleGraph V} {k : ℕ}

/-- A `k`-connected graph has more than `k` vertices.
@isnad1 id=lt.1h3v.s4.329ddfbf4f8b from=translated src=- shape=c8b5b6db vocab=2942cf50
-/
theorem order_gt (h : VertexConnected G k) : k < Fintype.card V := h.1

/-- Deleting fewer than `k` vertices leaves a connected induced graph.
@isnad1 id=connecte.2h4v.s5.5f79b3c26865 from=translated src=- shape=a6bb913b vocab=7d1f559a
-/
theorem connected_delete (h : VertexConnected G k) (U : Finset V)
    (hU : U.card < k) : (G.induce (U : Set V)ᶜ).Connected := h.2 U hU

/-- Two successive finite deletions can be treated as one deletion.
@isnad1 id=connecte.2h5v.s6.f30d062defb0 from=translated src=- shape=088bcef2 vocab=091fb9d7
-/
theorem connected_delete_union [DecidableEq V] (h : VertexConnected G k) (U W : Finset V)
    (hUW : U.card + W.card < k) :
    (G.induce ((U ∪ W : Finset V) : Set V)ᶜ).Connected := by
  apply h.connected_delete
  exact lt_of_le_of_lt (Finset.card_union_le U W) hUW

/-- Connectivity is monotone in the connectivity parameter.
@isnad1 id=vertexco.2h4v.s4.e4b92fdb51f2 from=translated src=- shape=7bf34d27 vocab=4d1e4be1
-/
theorem of_le (h : VertexConnected G k) {l : ℕ} (hl : l ≤ k) :
    VertexConnected G l := by
  refine ⟨lt_of_le_of_lt hl h.1, ?_⟩
  intro U hU
  exact h.2 U (lt_of_lt_of_le hU hl)

/-- Adding edges does not reduce vertex connectivity.
@isnad1 id=vertexco.2h4v.s5.d4b546a4ea80 from=translated src=- shape=487eed38 vocab=4d1e4be1
-/
theorem mono_graph {H : SimpleGraph V} (h : VertexConnected G k)
    (hGH : G ≤ H) : VertexConnected H k := by
  refine ⟨h.order_gt, ?_⟩
  intro U hU
  exact (h.connected_delete U hU).mono (by
    intro x y hxy
    exact hGH hxy)

/-- Deleting vertices lowers the connectivity guarantee by at most their number.
The result is stated with an arbitrary residual lower bound.
@isnad1 id=vertexco.2h5v.s6.93118fd69217 from=translated src=- shape=17740fc0 vocab=b6c2b69b
-/
theorem induce_compl [DecidableEq V] (h : VertexConnected G k)
    (U : Finset V) (m : ℕ) (hm : U.card + m ≤ k) :
    VertexConnected (G.induce (U : Set V)ᶜ) m := by
  classical
  let s : Set V := (U : Set V)ᶜ
  have hcard : Fintype.card s + U.card = Fintype.card V := by
    have hs : Fintype.card s = (Uᶜ : Finset V).card := by
      apply Fintype.card_of_finset' (Uᶜ)
      intro x
      simp [s]
    rw [hs]
    exact Finset.card_compl_add_card U
  refine ⟨?_, ?_⟩
  · change m < Fintype.card s
    have hk := h.order_gt
    omega
  intro W hW
  let F : Finset V := U ∪ W.image (fun z : s => (z : V))
  have hF : F.card < k := by
    have h1 : F.card ≤ U.card + (W.image (fun z : s => (z : V))).card :=
      Finset.card_union_le _ _
    have h2 : (W.image (fun z : s => (z : V))).card ≤ W.card :=
      Finset.card_image_le
    omega
  have hconn : (G.induce (F : Set V)ᶜ).Connected :=
    h.connected_delete F hF
  let f : (G.induce (F : Set V)ᶜ) →g
      ((G.induce s).induce (W : Set s)ᶜ) := {
    toFun := fun z => by
      have hzF : (z : V) ∉ F := z.property
      have hzU : (z : V) ∉ U := by
        intro hz
        exact hzF (Finset.mem_union.mpr (Or.inl hz))
      have hzW : (⟨z, hzU⟩ : s) ∉ W := by
        intro hz
        apply hzF
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_image.mpr ⟨⟨z, hzU⟩, hz, rfl⟩
      exact ⟨⟨z, hzU⟩, hzW⟩
    map_rel' := by
      intro x y hxy
      exact hxy
  }
  have hf : Function.Surjective f := by
    intro z
    have hzF : (z : V) ∉ F := by
      intro hz
      rcases Finset.mem_union.mp hz with hzU | hzW
      · exact z.1.property hzU
      · obtain ⟨w, hw, hval⟩ := Finset.mem_image.mp hzW
        have hwz : w = z.1 := Subtype.ext hval
        exact z.property (hwz ▸ hw)
    refine ⟨⟨z, hzF⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  exact hconn.map f hf

/-- Positive vertex connectivity implies ordinary connectedness.
@isnad1 id=connecte.2h3v.s4.5bad5be169da from=translated src=- shape=e6884a0f vocab=825f4f9c
-/
theorem connected (h : VertexConnected G k) (hk : 0 < k) : G.Connected := by
  have h' : (G.induce ((∅ : Finset V) : Set V)ᶜ).Connected :=
    h.connected_delete ∅ (by simpa using hk)
  have hset : (((∅ : Finset V) : Set V)ᶜ) = Set.univ := by
    ext x
    simp
  rw [hset] at h'
  have h'' : (G.induce Set.univ).Connected := h'
  exact (SimpleGraph.induceUnivIso G).connected_iff.mp h''

/-- The graph remaining after any admissible deletion is nonempty.
@isnad1 id=ex.2h4v.s5.0ec3fd0a3594 from=translated src=- shape=47d81712 vocab=18a3c3f0
-/
theorem nonempty_delete (h : VertexConnected G k) (U : Finset V)
    (hU : U.card < k) : ∃ v : V, v ∉ U := by
  obtain ⟨v⟩ := (h.connected_delete U hU).nonempty
  exact ⟨v.1, v.2⟩

end VertexConnected

/-- A vertex separation has no edge between its two strict sides.-/
structure VertexSeparation (G : SimpleGraph V) where
  left : Set V
  right : Set V
  cover : left ∪ right = Set.univ
  no_cross : ∀ ⦃x y⦄, x ∈ left → x ∉ right → y ∈ right → y ∉ left → ¬ G.Adj x y

namespace VertexSeparation

variable {G : SimpleGraph V}

/-- The common vertices of the two sides.-/
def separator (S : VertexSeparation G) : Set V := S.left ∩ S.right

/-- The finite set of vertices shared by the two sides.-/
noncomputable def separatorFinset (S : VertexSeparation G) : Finset V := by
  classical
  exact S.separator.toFinset

/-- The left side after removing the separator.-/
def strictLeft (S : VertexSeparation G) : Set V := S.left \ S.right

/-- The right side after removing the separator.-/
def strictRight (S : VertexSeparation G) : Set V := S.right \ S.left

omit [Fintype V] in
/--
@isnad1 id=not.2h5v.s5.3a1ec425a4cf from=translated src=- shape=c7260b5f vocab=fc00bbc0
-/
theorem no_cross' (S : VertexSeparation G) {x y : V}
    (hx : x ∈ S.strictLeft) (hy : y ∈ S.strictRight) : ¬ G.Adj x y :=
  S.no_cross hx.1 hx.2 hy.1 hy.2

omit [Fintype V] in
/--
@isnad1 id=disjoint.0h3v.s5.fd0f0716fe90 from=translated src=- shape=0e8f0a2b vocab=759b9b69
-/
theorem strictLeft_disjoint_strictRight (S : VertexSeparation G) :
    Disjoint S.strictLeft S.strictRight := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hx.2 hy.1

/-- Reversing the sides gives another separation.-/
def symm (S : VertexSeparation G) : VertexSeparation G where
  left := S.right
  right := S.left
  cover := by simpa only [Set.union_comm] using S.cover
  no_cross := by
    intro x y hx hr hy hl hxy
    exact S.no_cross hy hl hx hr hxy.symm

end VertexSeparation

end HadwigerLean
