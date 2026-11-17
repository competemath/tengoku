import Tengoku.LeanEvalPlatonicClassification.Submission.RelazioniCoxeter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/--
@isnad1 id=eq.2h5v.s8.62aa7bb34632 from=translated src=- shape=3553c947 vocab=70de7fdb
-/
theorem simpleReflection_fissa_facce (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) {k : Fin n} (hk : k ≠ i) :
    (⇑(simpleReflection P hreg F i)) '' F.face k = F.face k := by
  have hmap := congrArg (fun G : P.Flag => G.face k)
    (simpleReflection_mapFlag P hreg F i)
  calc
    (⇑(simpleReflection P hreg F i)) '' F.face k =
        (adjacentFlag P hreg.1 F i).face k := by
          simpa only [mapFlag_face] using hmap
    _ = F.face k := (adjacentFlag_isAdjacent P hreg.1 F i).1 k hk

/-- I centroidi delle facce di una bandiera, seguiti dal centroide del
corpo, nell'ordine naturale dei ranghi.-/
noncomputable def centroidiBandieraCorpo (P : ConvexPolytope n) (F : P.Flag) :
    Fin (n + 1) → E n := by
  classical
  exact Fin.lastCases
    (Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ P.toSet)) id)
    (fun k =>
      Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ F.face k)) id)

open Classical in
/--
@isnad1 id=eq.0h3v.s8.f54fb5daeca6 from=translated src=- shape=cf307391 vocab=5d3e862f
-/
@[simp] theorem centroidiBandieraCorpo_last (P : ConvexPolytope n) (F : P.Flag) :
    centroidiBandieraCorpo P F (Fin.last n) =
      Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ P.toSet)) id := by
  simp [centroidiBandieraCorpo]

open Classical in
/--
@isnad1 id=eq.0h4v.s8.9afa22f257d3 from=translated src=- shape=38ee0ec8 vocab=6312ed79
-/
@[simp] theorem centroidiBandieraCorpo_castSucc (P : ConvexPolytope n)
    (F : P.Flag) (k : Fin n) :
    centroidiBandieraCorpo P F k.castSucc =
      Finset.centroid ℝ (P.vertices.filter (fun x => x ∈ F.face k)) id := by
  simp [centroidiBandieraCorpo]

end LeanEval.Geometry.PlatonicClassification
