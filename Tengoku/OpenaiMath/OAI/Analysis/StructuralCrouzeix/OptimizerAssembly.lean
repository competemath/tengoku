import Tengoku.OpenaiMath.OAI.Analysis.StructuralCrouzeix.Model
import Tengoku.OpenaiMath.OAI.Analysis.StructuralCrouzeix.SimilarityMinimum

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker
namespace StructuralCrouzeix
open CompleteCrouzeix

lemma strictPositive_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {H : HermitianMatrix n} (hH : StrictPositive H) :
    (H : Matrix n n ℂ).PosDef := by
  obtain ⟨ε, hε, hle⟩ := hH
  have hp : ((H : Matrix n n ℂ) - ε • 1).PosSemidef := hle
  have hh := (Matrix.PosDef.one.smul hε).add_posSemidef hp
  simpa only [add_sub_cancel] using hh

lemma minimizing_posDef {n : ℕ} [Nonempty (Fin n)]
    {T H : Matrix (Fin n) (Fin n) ℂ} {τ : ℝ}
    (h : IsMinimizing T τ H) : H.PosDef := by
  have hp := (h.1.1 : (H-1).PosSemidef)
  have hh := Matrix.PosDef.one.add_posSemidef hp
  simpa only [add_sub_cancel] using hh

end StructuralCrouzeix
end

end OAI
