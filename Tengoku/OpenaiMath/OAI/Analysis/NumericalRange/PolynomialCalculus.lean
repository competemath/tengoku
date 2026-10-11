import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.CompleteResolvent

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_91 u_92 u_93 u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105 u_106 u_107

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_91} [Fintype n] [DecidableEq n]

def vectorize {m : Type u_92} (X : Matrix n m ℂ) : EuclideanSpace ℂ (n × m) :=
  WithLp.toLp 2 (fun p => X p.1 p.2)

def vectorizeCLM {m : Type u_93} [Fintype m] : Matrix n m ℂ →L[ℂ] EuclideanSpace ℂ (n × m) :=
  ({ toFun := vectorize
     map_add' := by intro X Y; rfl
     map_smul' := by intro z X; rfl } : Matrix n m ℂ →ₗ[ℂ] EuclideanSpace ℂ (n × m)).toContinuousLinearMap

@[simp] lemma vectorizeCLM_apply
    {n : Type u_91} [Fintype n] [DecidableEq n] {m : Type u_94} [Fintype m] (X : Matrix n m ℂ) :
    vectorizeCLM X = vectorize X := rfl

lemma kronecker_vectorize {m : Type u_95} [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) (X : Matrix n m ℂ) :
    Matrix.toEuclideanCLM (n := n × m) (𝕜 := ℂ) (A ⊗ₖ B) (vectorize X) =
      vectorize (A*X*Bᵀ) := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  change (Matrix.kronecker A B *ᵥ (fun p => X p.1 p.2)) (i,j) = (A*X*Bᵀ) i j
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change A i l * B j k * X l k = _
  ring

def transposedTransfer (a b c d : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  dᵀ + ((z • bᵀ) * (1-z • aᵀ)⁻¹) * cᵀ

lemma transposedTransfer_eq (a b c d : Matrix n n ℂ) (z : ℂ) :
    transposedTransfer a b c d z = (d + z • (c*(1-z • a)⁻¹*b))ᵀ := by
  simp only [transposedTransfer, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
    Matrix.transpose_one, smul_mul_assoc]
  noncomm_ring

lemma transposed_resolvent_unit {a : Matrix n n ℂ} (ha : ‖a‖ ≤ 1) {z : ℂ}
    (hz : z ∈ ball (0:ℂ) 1) : IsUnit (1-z • aᵀ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hu : IsUnit (1-z • a) := isUnit_one_sub_of_norm_lt_one (by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt
      (by simpa only [mul_one] using mem_ball_zero_iff.mp hz))
  have he : (1-z • aᵀ) = (1-z • a)ᵀ := by simp
  rw [he, Matrix.det_transpose]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma matrixAnalyticEval_comp (A : Matrix n n ℂ) {f g : ℂ → ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ g (f z)) :
    matrixAnalyticEval A (fun z => g (f z)) = matrixAnalyticEval (matrixAnalyticEval A f) g := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  exact primaryEval_comp _ (fun z hz => hf z (by simpa using hz))
    (fun z hz => hg z (by simpa using hz))

lemma completeAnalyticEval_comp
    {n : Type u_96} {m : Type u_97} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) {f : ℂ → ℂ} {F : ℂ → Matrix m m ℂ}
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hF : ∀ i j, ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ (fun w => F w i j) (f z)) :
    completeAnalyticEval A (fun z => F (f z)) = completeAnalyticEval (matrixAnalyticEval A f) F := by
  ext i j
  simp only [completeAnalyticEval]
  rw [matrixAnalyticEval_comp A hf (hF _ _)]

lemma matrixAnalyticEval_intertwine (A B L : Matrix n n ℂ) (hL : A*L=L*B) (f : ℂ → ℂ) :
    matrixAnalyticEval A f * L = L * matrixAnalyticEval B f := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [map_mul, matrixAnalyticEval, AlgEquiv.apply_symm_apply]
  apply primaryEval_intertwine
  intro x
  have he := congrArg (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ)) hL
  simp only [map_mul] at he
  exact LinearMap.congr_fun he x

lemma matrixAnalyticEval_similarity {S : Matrix n n ℂ} (hS : IsUnit S)
    (A : Matrix n n ℂ) (f : ℂ → ℂ) :
    matrixAnalyticEval (S*A*S⁻¹) f = S*matrixAnalyticEval A f*S⁻¹ := by
  have hi : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hi' : S*S⁻¹=1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have he := matrixAnalyticEval_intertwine (S*A*S⁻¹) A S (by rw [mul_assoc, mul_assoc, hi, mul_one]) f
  have h := congrArg (fun M => M*S⁻¹) he
  simpa only [mul_assoc, hi', mul_one] using h

lemma completeAnalyticEval_similarity {S : Matrix n n ℂ} (hS : IsUnit S)
    (A : Matrix n n ℂ) (F : ℂ → Matrix m m ℂ) :
    completeAnalyticEval (S*A*S⁻¹) F = (S ⊗ₖ (1 : Matrix m m ℂ)) *
      completeAnalyticEval A F * (S⁻¹ ⊗ₖ (1 : Matrix m m ℂ)) := by
  ext i j
  simp only [completeAnalyticEval, matrixAnalyticEval_similarity hS, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ite_mul, zero_mul, Finset.sum_ite_eq]

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_98} {m : Type u_99} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def baseMatrixHom : Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix m m ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]

lemma baseMatrixHom_norm (A : Matrix n n ℂ) : ‖baseMatrixHom (m := m) A‖ ≤ ‖A‖ :=
  NonUnitalStarAlgHom.norm_apply_le (baseMatrixHom (m := m)) A

lemma complete_analytic_similarity_bound {S A : Matrix n n ℂ} (hS : IsUnit S)
    (F : ℂ → Matrix m m ℂ) (hF : ‖completeAnalyticEval (S*A*S⁻¹) F‖ ≤ 1) :
    ‖completeAnalyticEval A F‖ ≤ ‖S‖ * ‖S⁻¹‖ := by
  let R := baseMatrixHom (m := m) S
  let R' := baseMatrixHom (m := m) S⁻¹
  have hi : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hi' : S*S⁻¹=1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hR : R'*R=1 := by change baseMatrixHom (m := m) S⁻¹ * baseMatrixHom S=1; rw [← map_mul, hi, map_one]
  have hR' : R*R'=1 := by change baseMatrixHom (m := m) S * baseMatrixHom S⁻¹=1; rw [← map_mul, hi', map_one]
  have he : completeAnalyticEval A F = R'*completeAnalyticEval (S*A*S⁻¹) F*R := by
    rw [completeAnalyticEval_similarity hS]
    change completeAnalyticEval A F = R'*(R*completeAnalyticEval A F*R')*R
    calc _ = 1*completeAnalyticEval A F*1 := by simp
      _ = _ := by rw [← hR]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖R'‖ * ‖completeAnalyticEval (S*A*S⁻¹) F‖ * ‖R‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖S⁻¹‖ * 1 * ‖S‖ := mul_le_mul
      (mul_le_mul (baseMatrixHom_norm S⁻¹) hF (norm_nonneg _) (norm_nonneg _))
      (baseMatrixHom_norm S) (norm_nonneg _) (mul_nonneg (norm_nonneg _) zero_le_one)
    _ = _ := by ring

end

section
open Filter Topology Set Metric Module MeasureTheory
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_100} {m : Type u_101} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma matrixAnalyticEval_power_mul (A : Matrix n n ℂ) (k : ℕ) (c : ℂ) :
    matrixAnalyticEval A (fun z => z^k*c) = c • A^k := by
  have he : (fun z : ℂ => z^k*c) = fun z => (Polynomial.X^k * Polynomial.C c).eval z := by
    funext z
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [he, matrixAnalyticEval_polynomial]
  simp only [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

lemma completeAnalyticEval_polynomial
    {n : Type u_100} {m : Type u_101} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {ι : Type u_102} (s : Finset ι)
    (A : Matrix n n ℂ) (B : ι → Matrix m m ℂ) (p : ι → ℕ) :
    completeAnalyticEval A (fun z => ∑ k ∈ s, z^(p k) • B k) =
      ∑ k ∈ s, (A^(p k)) ⊗ₖ B k := by
  ext i j
  simp only [completeAnalyticEval, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [matrixAnalyticEval_sum s A (f := fun k z => z^(p k)*B k i.2 j.2)
    (fun _ _ _ _ => by fun_prop)]
  simp only [matrixAnalyticEval_power_mul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.kroneckerMap_apply]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

end

section
open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_103} {m : Type u_104} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

end

open Filter Topology Set Metric Module
open scoped Matrix.Norms.L2Operator Kronecker
variable {n : Type u_105} {m : Type u_106} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

end CompleteCrouzeix

end

end OAI
