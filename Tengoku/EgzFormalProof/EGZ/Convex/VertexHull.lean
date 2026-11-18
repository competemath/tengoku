import Tengoku.EgzFormalProof.EGZ.Convex.AffineLattice
import Tengoku.Seed.Analysis.Convex.KreinMilman

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A polytope is the convex hull of its vertices

This finite-dimensional consequence of Krein--Milman is used when a hollow
rational polytope is converted into a finite `p`-hollow family.
-/

namespace EGZ.RationalPolytope

/-- The convex hull of the actual extreme points of a rational polytope is
the whole polytope, even when its stored generating finset is redundant.
@isnad1 id=eq.0h2v.s6.d2c2e74e7f4e from=translated src=- shape=985bae14 vocab=e8caac4b
-/
theorem carrier_eq_convexHull_vertexSet {d : ℕ} (P : RationalPolytope d) :
    P.carrier = convexHull ℝ P.vertexSet := by
  have hKM : closure (convexHull ℝ P.vertexSet) = P.carrier := by
    simpa only [vertexSet] using
      (closure_convexHull_extremePoints P.isCompact P.convex)
  have hcompact : IsCompact (convexHull ℝ P.vertexSet) :=
    P.finite_vertexSet.isCompact_convexHull ℝ
  rw [hcompact.isClosed.closure_eq] at hKM
  exact hKM.symm

/-- Every point of a polytope is a convex combination of its vertices.
@isnad1 id=mem.1h3v.s6.9ec85ce6d292 from=translated src=- shape=b40908fa vocab=60727714
-/
theorem mem_convexHull_vertexSet {d : ℕ} (P : RationalPolytope d)
    {q : RealCoord d} (hq : q ∈ P.carrier) :
    q ∈ convexHull ℝ P.vertexSet := by
  rwa [← P.carrier_eq_convexHull_vertexSet]

end EGZ.RationalPolytope
