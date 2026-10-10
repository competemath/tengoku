import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.HeatLocalization

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uE uV

namespace SubpolynomialLp

section GraphProjection
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

def conductorMatrix (src dst : E → V) (c : E → ℝ) : Matrix E V ℝ :=
  diagonal (fun e => Real.sqrt (c e)) * incidence src dst

omit [Fintype V] in
lemma conductorMatrix_gram (src dst : E → V) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
    (conductorMatrix src dst c).transpose * conductorMatrix src dst c = laplacianMatrix src dst c := by
  have he : diagonal (fun e => Real.sqrt (c e)) * diagonal (fun e => Real.sqrt (c e)) = diagonal c := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext e
    exact Real.mul_self_sqrt (hc e)
  unfold conductorMatrix laplacianMatrix
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  calc
    _ = (incidence src dst).transpose *
        (diagonal (fun e => Real.sqrt (c e)) * diagonal (fun e => Real.sqrt (c e))) * incidence src dst := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [he]

lemma conductorMatrix_mul_apply (src dst : E → V) (c : E → ℝ) (K : Matrix V V ℝ) (e : E) (v : V) :
    (conductorMatrix src dst c * K) e v = Real.sqrt (c e) * (K (src e) v - K (dst e) v) := by
  rw [conductorMatrix, Matrix.mul_assoc, Matrix.diagonal_mul]
  congr 1
  exact incidence_mulVec src dst (fun i => K i v) e

omit [DecidableEq E] in
lemma gram_heat_weighted (R : Matrix E V ℝ) (d : V → ℝ) (t : ℝ) :
    (R * diagonal d) * exp (-t • ((R * diagonal d).conjTranspose * (R * diagonal d))) *
      (R * diagonal d).transpose =
    R * weightedHeatKernel (R.transpose * R) d t * R.transpose := by
  have he : (R * diagonal d).conjTranspose * (R * diagonal d) =
      symmetricGenerator (R.transpose * R) d := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, Matrix.diagonal_transpose]
    simp only [symmetricGenerator, Matrix.mul_assoc]
  rw [he]
  simp only [weightedHeatKernel, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

omit [DecidableEq E] in
lemma gram_heat_twice (R : Matrix E V ℝ) (d μ : V → ℝ)
    (hrel : ∀ i, d i * μ i * d i = 1) (t : ℝ) (e f : E) :
    ((R * diagonal d) * exp (-(2*t) • ((R * diagonal d).conjTranspose * (R * diagonal d))) *
      (R * diagonal d).transpose) e f =
      ∑ v, μ v * (R * weightedHeatKernel (R.transpose * R) d t) e v *
        (R * weightedHeatKernel (R.transpose * R) d t) f v := by
  rw [gram_heat_weighted, two_mul, weightedHeatKernel_semigroup _ _ _ hrel]
  have hL : (R.transpose * R).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
  have he : R * (weightedHeatKernel (R.transpose * R) d t * diagonal μ *
      weightedHeatKernel (R.transpose * R) d t) * R.transpose =
      (R * weightedHeatKernel (R.transpose * R) d t) * diagonal μ *
        (R * weightedHeatKernel (R.transpose * R) d t).transpose := by
    rw [Matrix.transpose_mul, (weightedHeatKernel_symmetric _ hL d t).eq]
    simp only [Matrix.mul_assoc]
  rw [he, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro v _
  ring

omit [Fintype V] [DecidableEq E] in
lemma vertexWeight_pos (src dst : E → V) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (i : V) (hi : ∃ e, src e = i ∨ dst e = i) : 0 < vertexWeight src dst w i := by
  have hn (p : E → Prop) [DecidablePred p] : 0 ≤ ∑ e, if p e then (w e)^2 else 0 := by
    apply Finset.sum_nonneg
    intro e _
    split_ifs <;> positivity
  have hp (p : E → Prop) [DecidablePred p] (e : E) (he : p e) :
      0 < ∑ e, if p e then (w e)^2 else 0 := by
    apply Finset.sum_pos' (fun e _ => by split_ifs <;> positivity)
    exact ⟨e, Finset.mem_univ e, by simpa only [ite_eq_left he] using sq_pos_of_pos (hw e)⟩
  obtain ⟨e, he | he⟩ := hi
  · exact add_pos_of_pos_of_nonneg (hp _ e he) (hn _)
  · exact add_pos_of_nonneg_of_pos (hn _) (hp _ e he)

lemma orthogonal_sum_sq (U : Matrix E E ℝ) (hU : U.transpose * U = 1) (x : E → ℝ) :
    ∑ i, (U *ᵥ x) i ^ 2 = ∑ i, (x i)^2 := by
  have hh : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hU, Matrix.vecMul_one]
  simpa only [dotProduct, sq] using hh

lemma symmetric_quadratic_bound_sq (B : Matrix E E ℝ) (hB : B.IsSymm) (H : ℝ)
    (hb : ∀ x : E → ℝ, |x ⬝ᵥ (B *ᵥ x)| ≤ H * ∑ i, (x i)^2) (x : E → ℝ) :
    (∑ i, (B *ᵥ x) i ^ 2) ≤ H^2 * ∑ i, (x i)^2 := by
  let hS : B.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hB
  let U : Matrix E E ℝ := hS.eigenvectorUnitary
  let lam : E → ℝ := hS.eigenvalues
  have hU : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hU' : U * U.transpose = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hs : B = U * diagonal lam * U.transpose := by
    convert hS.spectral_theorem using 1
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hBU : B * U = U * diagonal lam := by
    rw [hs, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hnorm (k : E) : ∑ i, (U i k)^2 = 1 := by
    have hh := congrFun₂ hU k k
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, sq] using hh
  have hval (k : E) : |lam k| ≤ H := by
    have he : B *ᵥ (fun i => U i k) = fun i => U i k * lam k := by
      funext i
      change (B * U) i k = U i k * lam k
      rw [hBU, Matrix.mul_diagonal]
    have hh := hb (fun i => U i k)
    have hd : (fun i => U i k) ⬝ᵥ (fun i => U i k * lam k) = lam k := by
      simp only [dotProduct, ← mul_assoc, ← sq, ← Finset.sum_mul, hnorm, one_mul]
    rw [he, hd, hnorm, mul_one] at hh
    exact hh
  let y := U.transpose *ᵥ x
  have hy : ∑ i, (y i)^2 = ∑ i, (x i)^2 := by
    apply orthogonal_sum_sq
    simpa only [Matrix.transpose_transpose] using hU'
  have he : B *ᵥ x = U *ᵥ (diagonal lam *ᵥ y) := by
    rw [hs]
    simp only [Matrix.mulVec_mulVec, y, Matrix.mul_assoc]
  rw [he, orthogonal_sum_sq U hU]
  calc
    _ = ∑ i, (lam i)^2 * (y i)^2 := by simp only [Matrix.mulVec_diagonal, mul_pow]
    _ ≤ ∑ i, H^2 * (y i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (lam i)) (hval i) 2
    _ = _ := by rw [← Finset.mul_sum, hy]

end GraphProjection

end SubpolynomialLp

end

end OAI
