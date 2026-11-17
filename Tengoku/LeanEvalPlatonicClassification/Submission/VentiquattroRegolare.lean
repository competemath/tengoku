import Tengoku.LeanEvalPlatonicClassification.Submission.VentiquattroBandiera

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Montaggio finale della regolarità del 24-cell tramite la macchina delle
riflessioni di parete.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Le quattro riflessioni di parete della bandiera fondamentale.-/
def riflessioniVentiquattro : Fin 4 → Isom 4 := ![r0_24, r1_24, r2_24, r3_24]

/--
@isnad1 id=issymmet.0h1v.s4.9e68cecc5512 from=translated src=- shape=f8b59328 vocab=a86a079a
-/
theorem riflessioniVentiquattro_isSymmetry (i : Fin 4) :
    ventiquattro.isSymmetry (riflessioniVentiquattro i) := by
  fin_cases i
  · exact r0_24_isSymmetry
  · exact r1_24_isSymmetry
  · exact r2_24_isSymmetry
  · exact r3_24_isSymmetry

/--
@isnad1 id=flagadja.0h1v.s4.a1a62449ed90 from=translated src=- shape=af15d3c3 vocab=f23f8b08
-/
theorem riflessioniVentiquattro_flagAdjacent (i : Fin 4) :
    FlagAdjacentAt ventiquattro ventiquattroFlag
      (mapFlag ventiquattro (riflessioniVentiquattro_isSymmetry i)
        ventiquattroFlag) i := by
  fin_cases i
  · exact r0_24_flagAdjacent
  · exact r1_24_flagAdjacent
  · exact r2_24_flagAdjacent
  · exact r3_24_flagAdjacent

end LeanEval.Geometry.PlatonicClassification
