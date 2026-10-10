import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.ConvexSelection

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal
universe u uE uH uJ uV

namespace SubpolynomialLp

section WeightedProjection
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

def weightedProjection (A : Matrix E V ℝ) (σ : E → ℝ) : Matrix E E ℝ :=
  diagonal (fun e => (Real.sqrt (σ e))⁻¹) *
    gramProjection (diagonal (fun e => Real.sqrt (σ e)) * A) *
    diagonal (fun e => Real.sqrt (σ e))

def retractions (A : Matrix E V ℝ) : Set (Matrix E E ℝ) :=
  {P | P*A=A ∧ ∃ B : Matrix V E ℝ, P=A*B}

omit [DecidableEq E] [DecidableEq V] in
lemma retractions_convex (A : Matrix E V ℝ) : Convex ℝ (retractions A) := by
  intro P hP Q hQ a b ha hb hab
  rcases hP with ⟨hPA,B,rfl⟩
  rcases hQ with ⟨hQA,C,rfl⟩
  constructor
  · rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hPA, hQA,
      ← add_smul, hab, one_smul]
  · refine ⟨a • B+b • C, ?_⟩
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]

omit [DecidableEq E] in
lemma gramProjection_factor (A : Matrix E V ℝ) :
    ∃ B : Matrix V E ℝ, gramProjection A = A*B := by
  refine ⟨((gramHermitian A).eigenvectorUnitary : Matrix V V ℝ) *
    diagonal (fun i => ((gramHermitian A).eigenvalues i)⁻¹) *
    (gramEigenMatrix A).transpose, ?_⟩
  simp only [gramProjection, gramEigenMatrix, Matrix.mul_assoc]

lemma sqrt_diagonal_inv (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) :
    diagonal (fun e => (Real.sqrt (σ e))⁻¹) * diagonal (fun e => Real.sqrt (σ e)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [inv_mul_cancel₀ (Real.sqrt_pos.2 (hσ _)).ne']
  exact diagonal_one

lemma weightedProjection_mem (A : Matrix E V ℝ) (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) :
    weightedProjection A σ ∈ retractions A := by
  let D := diagonal (fun e => Real.sqrt (σ e))
  let Di := diagonal (fun e => (Real.sqrt (σ e))⁻¹)
  have hDi : Di*D=1 := sqrt_diagonal_inv σ hσ
  have hf := gramProjection_mul_self (D*A)
  constructor
  · change Di*gramProjection (D*A)*D*A=A
    calc
      _ = Di*(gramProjection (D*A)*(D*A)) := by simp only [Matrix.mul_assoc]
      _ = Di*(D*A) := by rw [hf]
      _ = A := by rw [← Matrix.mul_assoc, hDi, Matrix.one_mul]
  · obtain ⟨B,hB⟩ := gramProjection_factor (D*A)
    refine ⟨B*D, ?_⟩
    change Di*gramProjection (D*A)*D=A*(B*D)
    rw [hB]
    calc
      _ = (Di*D)*A*(B*D) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hDi, Matrix.one_mul]

lemma hilbertMul_diagonal {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (d : E → ℝ) (x : E → H) (e : E) : hilbertMul (diagonal d) x e = d e • x e := by
  simp [hilbertMul, Matrix.diagonal_apply]

lemma weightedProjection_energy {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Matrix E V ℝ) (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) (x : E → H) :
    (∑ e, σ e * ‖hilbertMul (weightedProjection A σ) x e‖^2) ≤
      ∑ e, σ e * ‖x e‖^2 := by
  let D := diagonal (fun e => Real.sqrt (σ e))
  let Di := diagonal (fun e => (Real.sqrt (σ e))⁻¹)
  let Q := gramProjection (D*A)
  have hDD : D*Di=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (Real.sqrt_pos.2 (hσ _)).ne']
    exact diagonal_one
  have hP : D*weightedProjection A σ=Q*D := by
    change D*(Di*Q*D)=Q*D
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
  have hen (y : E → H) : (∑ e, ‖hilbertMul D y e‖^2) = ∑ e, σ e*‖y e‖^2 := by
    apply Finset.sum_congr rfl
    intro e _
    rw [hilbertMul_diagonal, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (hσ e)), mul_pow, Real.sq_sqrt (hσ e).le]
  have hc := hilbertMul_contraction Q (gramProjection_symmetric _) (gramProjection_idempotent _)
    (hilbertMul D x)
  rw [← hilbertMul_mul, ← hP, hilbertMul_mul, hen, hen] at hc
  exact hc

def matrixRowNorm (P : Matrix E E ℝ) (e : E) : ℝ := ∑ f, |P e f|

omit [DecidableEq E] in
lemma matrixRowNorm_nonneg (P : Matrix E E ℝ) (e : E) : 0 ≤ matrixRowNorm P e := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

omit [DecidableEq E] [DecidableEq V] in
lemma matrixRowNorm_convex (A : Matrix E V ℝ) (e : E) :
    ConvexOn ℝ (retractions A) (fun P => matrixRowNorm P e) := by
  refine ⟨retractions_convex A, ?_⟩
  intro P hP Q hQ a b ha hb hab
  change (∑ f, |a*P e f+b*Q e f|) ≤ a*(∑ f, |P e f|)+b*(∑ f, |Q e f|)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro f _
  simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a*P e f) (b*Q e f)

omit [DecidableEq E] [DecidableEq V] in
lemma projectionEnergy_convex {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Matrix E V ℝ) (lam : E → ℝ) (hlam : ∀ e, 0 ≤ lam e) (x : E → H) :
    ConvexOn ℝ (retractions A) (fun P => ∑ e, lam e * ‖hilbertMul P x e‖^2) := by
  refine ⟨retractions_convex A, ?_⟩
  intro P hP Q hQ a b ha hb hab
  have hn := (convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set H))).pow
    (fun _ _ => norm_nonneg _) 2
  simp only [hilbertMul_add, hilbertMul_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have hh := hn.2 (Set.mem_univ (hilbertMul P x e)) (Set.mem_univ (hilbertMul Q x e)) ha hb hab
  change ‖a • hilbertMul P x e+b • hilbertMul Q x e‖^2 ≤
    a*‖hilbertMul P x e‖^2+b*‖hilbertMul Q x e‖^2 at hh
  calc
    _ ≤ lam e*(a*‖hilbertMul P x e‖^2+b*‖hilbertMul Q x e‖^2) :=
      mul_le_mul_of_nonneg_left hh (hlam e)
    _ = _ := by ring

def normalizedGradient (src dst : E → V) (δ : E → ℝ) : Matrix E V ℝ :=
  diagonal (fun e => (δ e)⁻¹) * incidence src dst

omit [Fintype V] in
lemma scaled_normalizedGradient (src dst : E → V) (δ σ : E → ℝ)
    (hδ : ∀ e, 0 < δ e) (hσ : ∀ e, 0 < σ e) :
    diagonal (fun e => Real.sqrt (σ e)) * normalizedGradient src dst δ =
      conductorMatrix src dst (fun e => σ e/(δ e)^2) := by
  unfold normalizedGradient conductorMatrix
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  congr 1
  congr 1
  funext e
  rw [Real.sqrt_div (hσ e).le, Real.sqrt_sq (hδ e).le]
  rfl

end WeightedProjection

end SubpolynomialLp

end

end OAI
