import Tengoku.OpenaiMath.OAI.Analysis.StructuralCrouzeix.OptimizerAssembly
import Tengoku.OpenaiMath.OAI.Analysis.StructuralCrouzeix.SharedMaximum
import Tengoku.OpenaiMath.OAI.Analysis.StructuralCrouzeix.ClosedSide
import Tengoku.OpenaiMath.OAI.Analysis.StructuralCrouzeix.OrientBoundary
import Tengoku.OpenaiMath.OAI.Analysis.StructuralCrouzeix.ExteriorSupport

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker
namespace StructuralCrouzeix
open CompleteCrouzeix

lemma IsAdmissible.compact_closure {U : Set ℂ} (hU : IsAdmissible U) :
    IsCompact (closure U) :=
  isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hU.bounded.closure⟩

lemma IsAdmissible.sided_boundary {U : Set ℂ} (hU : IsAdmissible U) :
    ∀ p ∈ frontier U, LocalAnalyticBoundary U p := by
  intro p hp
  exact RegularAnalyticBoundaryAt.orient hU.isOpen hU.convex hU.nonempty hp
    (hU.regular p hp)

def bundleDomain {U : Set ℂ} (hU : IsAdmissible U) (a : ℂ) (ha : a ∈ U)
    (f : DiskCoordinate U a) (G : ExteriorCoordinate U) : AdmissibleDomain where
  domain := U
  isOpen := hU.isOpen
  convex := hU.convex
  compact_closure := hU.compact_closure
  base := a
  base_mem := ha
  interior := f
  exterior := G
  support := convex_exteriorCoordinate_support hU.isOpen hU.convex hU.nonempty G

lemma bundleDomain_boundaryPoint {U : Set ℂ} (hU : IsAdmissible U)
    (a : ℂ) (ha : a ∈ U) (f : DiskCoordinate U a) (G : ExteriorCoordinate U)
    (t : UnitAddCircle) :
    (bundleDomain hU a ha f G).G (t.toCircle : ℂ) = boundaryPoint G t := rfl

lemma bundleDomain_maximum {U : Set ℂ} (hU : IsAdmissible U)
    (a : ℂ) (ha : a ∈ U) (f : DiskCoordinate U a) (G : ExteriorCoordinate U)
    {m : ℕ} (v : ℂ → Matrix (Fin m) (Fin m) ℂ) :
    (bundleDomain hU a ha f G).analyticRangeMaximum v = analyticSupNorm U v := rfl

end StructuralCrouzeix
end

end OAI
