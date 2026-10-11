import Tengoku.OpenaiMath.OAI.Analysis.StructuralCrouzeix.SharedDensity

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def analyticRangeMaximum {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) : ℝ :=
  sSup ((fun z => ‖v z‖) '' closure D.domain)

lemma analyticRangeMaximum_bddAbove {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    BddAbove ((fun z => ‖v z‖) '' closure D.domain) := by
  exact (D.compact_closure.image_of_continuousOn hv.continuousOn.norm).bddAbove

theorem analyticRangeMaximum_attained {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    ∃ z ∈ closure D.domain, D.analyticRangeMaximum v = ‖v z‖ := by
  have hne : (closure D.domain).Nonempty := ⟨D.base, subset_closure D.base_mem⟩
  obtain ⟨z, hz, hmax⟩ := D.compact_closure.exists_isMaxOn hne hv.continuousOn.norm
  refine ⟨z, hz, ?_⟩
  change sSup ((fun w => ‖v w‖) '' closure D.domain) = ‖v z‖
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro r ⟨w, hw, rfl⟩
    exact hmax hw
  · exact le_csSup (D.analyticRangeMaximum_bddAbove v hv) ⟨z, hz, rfl⟩

lemma analyticRangeMaximum_nonneg {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    0 ≤ D.analyticRangeMaximum v := by
  obtain ⟨z, hz, he⟩ := D.analyticRangeMaximum_attained v hv
  rw [he]
  exact norm_nonneg _

lemma norm_le_analyticRangeMaximum {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain))
    {z : ℂ} (hz : z ∈ closure D.domain) : ‖v z‖ ≤ D.analyticRangeMaximum v := by
  exact le_csSup (D.analyticRangeMaximum_bddAbove v hv) ⟨z, hz, rfl⟩

end AdmissibleDomain
end CompleteCrouzeix
end
end

end OAI
