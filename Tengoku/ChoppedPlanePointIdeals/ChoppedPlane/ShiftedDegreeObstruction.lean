module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.DegreeObstruction
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.GradedPresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The homogeneous degree obstruction with signed component and generator shifts. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K] {n : ℕ} {ι κ : Type*} [Fintype κ]

/-- Row-dependent homogeneous degrees satisfy the same obstruction, including
negative degree spaces. Polynomial coefficients cannot lower any entry degree.
@isnad1 id=eq.4h9v.s8.15ab942b7541 from=translated src=- shape=edc8e6d0 vocab=7c8ea02c
-/
theorem signed_homogeneous_vector_zero_of_lower_degree
    (B : Matrix ι κ (Poly K n)) (δ : ι → κ → ℤ) (t : ι → ℤ)
    (hB : ∀ i j, B i j ∈ signedForms K n (δ i j))
    (ht : ∀ i j, t i < δ i j)
    (f : ι → Poly K n) (hf : ∀ i, f i ∈ signedForms K n (t i))
    (v : κ → Poly K n) (h : B.mulVec v = f) : f = 0 := by
  funext i
  by_cases hi : 0 ≤ t i
  · have hfi : (f i).IsHomogeneous (t i).toNat := by
      simpa [signedForms, hi] using hf i
    have heq := congrArg (homogeneousComponent (t i).toNat) (congrFun h i)
    rw [homogeneousComponent_eq_self hfi] at heq
    simp only [Matrix.mulVec, dotProduct, map_sum] at heq
    have hz (j : κ) : homogeneousComponent (t i).toNat (B i j * v j) = 0 := by
      by_cases hj : 0 ≤ δ i j
      · have hbij : (B i j).IsHomogeneous (δ i j).toNat := by
          simpa [signedForms, hj] using hB i j
        exact homogeneousComponent_mul_eq_zero_of_lt _ (by have := ht i j; omega) _ _ hbij
      · have hbzero : B i j = 0 := by
          simpa only [signedForms, ite_eq_right hj, Submodule.mem_bot] using hB i j
        simp only [hbzero, zero_mul, map_zero]
    simpa only [hz, Finset.sum_const_zero, Pi.zero_apply] using heq.symm
  · simpa only [signedForms, ite_eq_right hi, Submodule.mem_bot, Pi.zero_apply] using hf i

/-- In a free module with component shifts `w`, every generator has total
degree `degree j`. A homogeneous element of smaller total degree is zero.
@isnad1 id=eq.4h10v.s8.4721410bd4d8 from=translated src=- shape=6d4fbe37 vocab=dfd4d5d0
-/
theorem weighted_homogeneous_vector_zero_of_lower_degree
    (B : Matrix ι κ (Poly K n)) (w : ι → ℤ) (degree : κ → ℤ) (t : ℤ)
    (hB : ∀ i j, B i j ∈ signedForms K n (degree j - w i))
    (ht : ∀ j, t < degree j)
    (f : ι → Poly K n) (hf : ∀ i, f i ∈ signedForms K n (t - w i))
    (v : κ → Poly K n) (h : B.mulVec v = f) : f = 0 :=
  signed_homogeneous_vector_zero_of_lower_degree B (fun i j => degree j - w i)
    (fun i => t - w i) hB (fun i j => by have := ht j; omega) f hf v h

end ChoppedPlane
