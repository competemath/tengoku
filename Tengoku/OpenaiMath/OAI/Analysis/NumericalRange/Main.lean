import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.DomainBound

namespace OAI

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
lemma polynomialValue_smul {m d : ℕ} (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ)
    (c z : ℂ) : polynomialValue (fun k => c • B k) z = c • polynomialValue B z := by
  simp only [polynomialValue,Finset.smul_sum,smul_comm (z^_) c]
lemma polynomialAt_smul {n m d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ) (c : ℂ) :
    polynomialAt A (fun k => c • B k) = c • polynomialAt A B := by
  simp only [polynomialAt,Matrix.kronecker,Matrix.kronecker_smul,Finset.smul_sum]
lemma rangeMaximum_nonneg {n m d : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ) :
    0 ≤ rangeMaximum A B := by
  obtain ⟨z,hz,he⟩ := rangeMaximum_attained hn A B
  rw [he]
  exact norm_nonneg _
lemma norm_polynomialValue_le_rangeMaximum {n m d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Fin (d+1) → Matrix (Fin m) (Fin m) ℂ)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖polynomialValue B z‖ ≤ rangeMaximum A B := by
  apply le_csSup
  · exact ((numericalRange_compact A).image (continuous_polynomialValue B).norm).bddAbove
  · exact ⟨z,hz,rfl⟩

end CompleteCrouzeix

end

end

end OAI
