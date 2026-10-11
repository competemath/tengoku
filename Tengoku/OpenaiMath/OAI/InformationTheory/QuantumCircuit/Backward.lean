import Tengoku.OpenaiMath.OAI.InformationTheory.QuantumCircuit.Reflection
import Tengoku.OpenaiMath.OAI.InformationTheory.QuantumCircuit.Polynomial

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

lemma conjugate_finset_sum {A ι : Type*} [CStarAlgebra A] (U : A) (s : Finset ι) (f : ι → A) :
    conjugate U (∑ i ∈ s, f i) = ∑ i ∈ s, conjugate U (f i) := by
  simp only [conjugate,Finset.mul_sum,Finset.sum_mul]

lemma Count.polynomial_norm_le {N : ℕ} (D : Count N) (p : Polynomial ℝ) :
    ‖D.polynomial p‖ ≤ weight N p := by
  classical
  rw [D.polynomial_eq_sum]
  apply (norm_sum_le _ _).trans
  change (∑ k ∈ p.support, ‖p.coeff k • D.operator^k‖) ≤ ∑ k ∈ p.support, |p.coeff k| *(N:ℝ)^k
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) D.operator_norm_le _)

lemma Count.backward_finite {N : ℕ} (M D : Count N) (U : Operator N) (hU : U ∈ unitary (Operator N))
    (p : Polynomial ℝ) (r b A B E T : ℝ)
    (hx : ‖M.high r*conjugate U (D.polynomial p)*M.zero‖ ≤ A)
    (hp : ‖D.polynomial p‖ ≤ B)
    (he : ‖(D.zero-D.polynomial p)*D.low b‖ ≤ E)
    (ht : ‖D.high b*star U*M.zero*U*D.zero‖ ≤ T) :
    ‖M.high r*conjugate U D.zero*M.zero‖^2 ≤ A+E+(1+B)*T := by
  let Q := conjugate U D.zero
  let X := conjugate U (D.polynomial p)
  let W := conjugate U (D.high b)
  have hQ : IsStarProjection Q := conjugate_projection hU D.zero_projection
  have hQn : ‖Q‖ ≤ 1 := IsStarProjection.norm_le _ hQ
  have hXn : ‖X‖ ≤ B := by
    change ‖U*D.polynomial p*star U‖ ≤ B
    rw [norm_unitary_conjugate hU]
    exact hp
  have hn : ‖Q-X‖ ≤ 1+B := (norm_sub_le _ _).trans (add_le_add hQn hXn)
  have hlow : ‖(Q-X)*(1-W)‖ ≤ E := by
    have heq : (Q-X)*(1-W) = conjugate U ((D.zero-D.polynomial p)*D.low b) := by
      change (conjugate U D.zero-conjugate U (D.polynomial p))*(1-conjugate U (D.high b)) = _
      simp only [Count.low,conjugate_mul hU,conjugate_sub,conjugate_one hU]
    rw [heq]
    change ‖U*((D.zero-D.polynomial p)*D.low b)*star U‖ ≤ E
    rw [norm_unitary_conjugate hU]
    exact he
  have htail : ‖W*M.zero*Q‖ ≤ T := by
    have heq : W*M.zero*Q = conjugate U (D.high b*star U*M.zero*U*D.zero) := by
      dsimp only [W,Q,conjugate]
      simp only [mul_assoc]
    rw [heq]
    change ‖U*(D.high b*star U*M.zero*U*D.zero)*star U‖ ≤ T
    rw [norm_unitary_conjugate hU]
    exact ht
  have herr : ‖(Q-X)*M.zero*Q‖ ≤ E+(1+B)*T := by
    apply (norm_split_bound (Q-X) W M.zero Q (IsStarProjection.norm_le _ M.zero_projection) hQn).trans
    exact add_le_add hlow (mul_le_mul hn htail (norm_nonneg _) ((norm_nonneg _).trans hn))
  have hsquare := projection_transition_square (M.high r) M.zero Q X
    (M.high_projection r) M.zero_projection hQ
  exact hsquare.trans ((add_le_add hx herr).trans_eq (by ring))

end QAC

end

end OAI
