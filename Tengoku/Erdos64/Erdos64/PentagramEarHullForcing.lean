import Tengoku.Erdos64.Erdos64.PentagramEarHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

/-- An earlier certificate interface for a return route that closes a supplied
`Connector` to an eight-cycle. Its fields repeat the data in `HullReturn`;
this record does not produce the route, hull, or connector. The active local
case files construct returns for all twelve normalized endpoint/length cases.
The general dispatcher in `PentagramEarHullShortConnector.lean` remains an
excluded draft as of the 2026-09-29 audit.-/
structure ExplicitHullRoute (H : PentagramEarHull G) (i₀ j₀ : Fin 5)
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

/-- Convert explicit route data into the certified conditional return
interface.  No graph-forcing claim is made by this conversion.-/
def ExplicitHullRoute.toHullReturn
    (R : ExplicitHullRoute H i₀ j₀ K) :
    PentagramEarHull.HullReturn H i₀ j₀ K :=
  { route := R.route
    route_isPath := R.route_isPath
    route_length := R.route_length
    route_disjoint := R.route_disjoint
    first_steps_distinct := R.first_steps_distinct }

/-- Consume the supplied route certificate to construct an eight-cycle.
Existence of the hull, connector, and return route remains in the inputs.-/
theorem cycle8_of_explicit_hull_route
    (H : PentagramEarHull G) (i₀ j₀ : Fin 5)
    (K : PentagramEarHull.Connector (G := G) H i₀ j₀)
    (R : ExplicitHullRoute H i₀ j₀ K) :
    ∃ c : G.Walk
        (PentagramEarHull.bVertex (G := G) H i₀)
        (PentagramEarHull.bVertex (G := G) H i₀),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H i₀ j₀ K R.toHullReturn

end PentagramEarHull

end Erdos64
