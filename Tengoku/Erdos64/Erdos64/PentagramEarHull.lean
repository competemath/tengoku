import Tengoku.Erdos64.Erdos64.PathIntersections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Fifteen jointly distinct hull vertices: five `c` vertices, five `a`
vertices, and five `b` vertices.  The graph may have further ambient
vertices and edges.-/
structure PentagramEarHull {V : Type u} (G : SimpleGraph V) where
  vertex : Sum (Fin 5) (Sum (Fin 5) (Fin 5)) → V
  vertex_injective : Function.Injective vertex
  c_adj : ∀ i, G.Adj (vertex (.inl i)) (vertex (.inl (i + 1)))
  ca_adj : ∀ i, G.Adj (vertex (.inl i)) (vertex (.inr (.inl i)))
  ab_adj : ∀ i, G.Adj (vertex (.inr (.inl i))) (vertex (.inr (.inr i)))
  shifted_ab_adj : ∀ i,
    G.Adj (vertex (.inr (.inl (i + 2))) )
      (vertex (.inr (.inr i)))

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

def cVertex (H : PentagramEarHull G) (i : Fin 5) : V := H.vertex (.inl i)
def aVertex (H : PentagramEarHull G) (i : Fin 5) : V := H.vertex (.inr (.inl i))
def bVertex (H : PentagramEarHull G) (i : Fin 5) : V := H.vertex (.inr (.inr i))

def hull (H : PentagramEarHull G) : Set V :=
  Set.range H.cVertex ∪ Set.range H.aVertex ∪ Set.range H.bVertex

theorem cVertex_injective (H : PentagramEarHull G) : Function.Injective H.cVertex := by
  intro i j hij
  apply Sum.inl.inj
  apply H.vertex_injective
  simpa [cVertex] using hij

theorem aVertex_injective (H : PentagramEarHull G) : Function.Injective H.aVertex := by
  intro i j hij
  apply Sum.inl.inj
  apply Sum.inr.inj
  apply H.vertex_injective
  simpa [aVertex] using hij

theorem bVertex_injective (H : PentagramEarHull G) : Function.Injective H.bVertex := by
  intro i j hij
  apply Sum.inr.inj
  apply Sum.inr.inj
  apply H.vertex_injective
  simpa [bVertex] using hij

theorem c_a_b_jointly_injective (H : PentagramEarHull G) :
    Function.Injective (fun x : Sum (Fin 5) (Sum (Fin 5) (Fin 5)) => H.vertex x) :=
  H.vertex_injective

/-- A path supplied by the ambient graph whose internal vertices avoid all
fifteen hull vertices.  The endpoints are the indicated distinct `b`s.-/
structure Connector (H : PentagramEarHull G) (i₀ j₀ : Fin 5) where
  distinct : i₀ ≠ j₀
  path : G.Walk
    (PentagramEarHull.bVertex (G := G) H i₀)
    (PentagramEarHull.bVertex (G := G) H j₀)
  isPath : path.IsPath
  length_one_to_three : path.length = 1 ∨ path.length = 2 ∨ path.length = 3
  interior_disjoint : ∀ v, v ∈ path.support.tail.dropLast → v ∉ hull H

/-- The exact graph-theoretic concatenation interface needed to close a
connector into an 8-cycle. The supplied return route must satisfy simplicity,
exact total length, disjointness, and first-step separation. This record does
not require its support to lie in the hull; `IncidenceBridgeWitness` supplies
that stronger condition in the incidence construction.-/
structure HullReturn (H : PentagramEarHull G) (i₀ j₀ : Fin 5)
    (K : PentagramEarHull.Connector (G := G) H i₀ j₀) where
  route : G.Walk
    (PentagramEarHull.bVertex (G := G) H i₀)
    (PentagramEarHull.bVertex (G := G) H j₀)
  route_isPath : route.IsPath
  route_length : route.length + K.path.length = 8
  route_disjoint :
    (K.path.take K.path.length).support.tail.Disjoint
      (route.take route.length).reverse.support.tail
  first_steps_distinct : K.path.snd ≠ route.snd

theorem cycle8_of_hull_return (H : PentagramEarHull G) (i₀ j₀ : Fin 5)
    (K : PentagramEarHull.Connector (G := G) H i₀ j₀)
    (R : PentagramEarHull.HullReturn H i₀ j₀ K) :
    ∃ c : G.Walk
        (PentagramEarHull.bVertex (G := G) H i₀)
        (PentagramEarHull.bVertex (G := G) H i₀),
      c.IsCycle ∧ c.length = 8 := by
  obtain ⟨c, hc, hlen, _hle⟩ :=
    SimpleGraph.Walk.IsPath.cycle_of_first_reunion
      K.path R.route K.isPath R.route_isPath R.first_steps_distinct
      (i := K.path.length) (j := R.route.length)
      (by
        rcases K.length_one_to_three with h | h | h <;> omega)
      (by exact Nat.le_refl _)
      (by
        have hroute := R.route_length
        rcases K.length_one_to_three with h | h | h <;> omega)
      (by exact Nat.le_refl _)
      (by simp) R.route_disjoint
  refine ⟨c, hc, ?_⟩
  have hroute := R.route_length
  omega

end PentagramEarHull

end Erdos64
