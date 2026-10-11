import Tengoku.OpenaiMath.OAI.InformationTheory.AmplitudeDamping.ZeroBlockEntropy

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def thermal (X Y : Matrix ι κ ℂ) (a b c d K : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks (a • gram X+b • gram Y) (K • (X*Yᴴ))
    (K • (Y*Xᴴ)) (c • gram X+d • gram Y)

omit [DecidableEq κ] in
theorem isState_of_posSemidef_trace_re {P : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (ht : P.trace.re = 1) : IsState P := by
  refine ⟨hP, ?_⟩
  apply Complex.ext ht
  exact (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm

omit [DecidableEq ι] [DecidableEq κ] in
theorem thermal_trace (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    (a b c d K : ℝ) : (thermal X Y a b c d K).trace.re = a+b+c+d := by
  simp only [mass, Matrix.trace, Matrix.diag, Complex.re_sum] at hX hY
  simp [thermal, Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Finset.sum_add_distrib,
    ← Finset.mul_sum, hX, hY, add_assoc]

def blockSwap : Matrix.unitaryGroup (ι ⊕ ι) ℂ :=
  ⟨Matrix.fromBlocks 0 1 1 0, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]⟩

omit [DecidableEq κ] in
theorem blockSwap_conj (A B C D : Matrix ι ι ℂ) :
    Unitary.conjStarAlgAut ℂ _ (blockSwap (ι := ι)) (Matrix.fromBlocks A B C D) =
    Matrix.fromBlocks D C B A := by
  simp [Unitary.conjStarAlgAut_apply, blockSwap, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem thermal_zeroEta_gram (X Y : Matrix ι κ ℂ) {a b d K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hK : 0 ≤ K) (had : a*d = K^2) :
    thermal X Y a b 0 d K =
      gram (zeroBlock (Real.sqrt a • X) (Real.sqrt b • Y) (Real.sqrt d • Y)) := by
  have hroot : Real.sqrt a * Real.sqrt d = K := by
    rw [← Real.sqrt_mul ha, had, Real.sqrt_sq hK]
  rw [gram_zeroBlock, gram_sqrt_smul ha, gram_sqrt_smul hb, gram_sqrt_smul hd]
  simp only [thermal, zero_smul, zero_add, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hroot, mul_comm (Real.sqrt d) (Real.sqrt a)]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem thermal_mix (X Y : Matrix ι κ ℂ) (a b c d a' b' c' d' K w w' : ℝ)
    (hw : w+w'=1) :
    w • thermal X Y a b c d K + w' • thermal X Y a' b' c' d' K =
      thermal X Y (w*a+w'*a') (w*b+w'*b') (w*c+w'*c') (w*d+w'*d') K := by
  have hK : w*K+w'*K=K := by rw [← add_mul, hw, one_mul]
  simp only [thermal, Matrix.fromBlocks_smul, Matrix.fromBlocks_add, smul_add, smul_smul,
    ]
  congr 1
  · module
  · rw [← add_smul, hK]
  · rw [← add_smul, hK]
  · module

end GAD

end

end OAI
