import Tengoku.Linearhadwiger.HadwigerLean.Graph.Finite
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting finite connected sets from induced graphs

A connected finite vertex set in an induced graph remains connected when
viewed as a set of vertices of the original graph. The lift preserves its
cardinality and, for a complement graph, avoids the deleted vertices.
-/

namespace HadwigerLean

variable {V : Type*} [DecidableEq V]

/-- The image in the ambient graph of a finite connected induced vertex set
is connected and has the same cardinality.
@isnad1 id=connecte.1h4v.s7.1736feb4313e from=translated src=- shape=1a845ec7 vocab=76189aa2
-/
theorem connected_induced_finset_image (G : SimpleGraph V) (D : Set V)
    (S : Finset D)
    (hconn : ((G.induce D).induce (S : Set D)).Connected) :
    (G.induce (S.image Subtype.val : Set V)).Connected := by
  classical
  let φ : (G.induce D).induce (S : Set D) →g
      G.induce (S.image Subtype.val : Set V) := {
    toFun := fun x => ⟨x.1.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
    map_rel' := by intro x y hxy; exact hxy
  }
  have hsurj : Function.Surjective φ := by
    rintro ⟨v, hv⟩
    obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hv
    subst v
    exact ⟨⟨x, hx⟩, rfl⟩
  exact hconn.map φ hsurj

/-- The lift of a finite set through an induced graph has equal cardinality.
@isnad1 id=eq.0h3v.s5.46f43193caa3 from=translated src=- shape=4c4ad58f vocab=46ac3ac1
-/
theorem card_induced_finset_image (D : Set V) (S : Finset D) :
    (S.image Subtype.val).card = S.card := by
  classical
  exact Finset.card_image_of_injective S Subtype.val_injective

/-- A finite set lifted from a complement graph avoids the deleted set.
@isnad1 id=disjoint.0h3v.s6.c99c2fb98165 from=translated src=- shape=f3f237af vocab=9774371a
-/
theorem disjoint_induced_compl_finset_image (U : Finset V)
    (S : Finset (↥((U : Set V)ᶜ))) :
    Disjoint (S.image Subtype.val) U := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hU
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
  exact x.2 hU

end HadwigerLean
