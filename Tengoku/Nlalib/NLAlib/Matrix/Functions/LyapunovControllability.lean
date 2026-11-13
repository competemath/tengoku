import Tengoku.Nlalib.NLAlib.Matrix.Functions.LyapunovIntegral
import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Coeff
import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The kernel and rank of a continuous controllability Gramian

The finite power cutoff is the ambient dimension, justified by actual
Cayley–Hamilton reduction. The exponential series and improper integral
then identify precisely the unobservable vectors.
-/

noncomputable section
open Polynomial MeasureTheory Set
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

variable {n s : Type*} [Fintype n] [Fintype s] [DecidableEq n] [DecidableEq s]

omit [Fintype s] [DecidableEq s] in
/-- Cayley–Hamilton reduces finite-dimensional annihilation to powers below the dimension.
@isnad1 id=eq.1h7v.s8.0e572c4956cb from=translated src=- shape=7fe5e1e2 vocab=4b767689
-/
theorem mulVec_pow_zero_of_lt_card {K : Type*} [RCLike K] (A : Matrix n n K) (L : Matrix s n K)
    (v : n → K) (h : ∀ j < Fintype.card n, L *ᵥ (A ^ j *ᵥ v) = 0) (j : ℕ) :
    L *ᵥ (A ^ j *ᵥ v) = 0 := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn => ext i; simp [Matrix.mulVec, dotProduct]
  | inr hn =>
    let p : K[X] := (X ^ j) %ₘ A.charpoly
    have hchar : A.charpoly ≠ 1 := by
      intro hc
      have hd := congrArg Polynomial.natDegree hc
      rw [Matrix.charpoly_natDegree_eq_dim, natDegree_one] at hd
      exact (Fintype.card_pos.ne' hd)
    have hp : p.natDegree < Fintype.card n := by
      simpa only [Matrix.charpoly_natDegree_eq_dim] using natDegree_modByMonic_lt (X ^ j) A.charpoly_monic hchar
    rw [Matrix.pow_eq_aeval_mod_charpoly]
    change L *ᵥ (aeval A p *ᵥ v) = 0
    rw [aeval_eq_sum_range' hp, Matrix.sum_mulVec, Matrix.mulVec_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, h i (Finset.mem_range.mp hi), smul_zero]

omit [Fintype s] [DecidableEq s] in
/-- Annihilation of every power annihilates the actual exponential series.
@isnad1 id=eq.1h7v.s8.49518506bab5 from=translated src=- shape=1862ce46 vocab=c96f1cff
-/
theorem mulVec_matrixExp_zero_of_pow_zero {K : Type*} [RCLike K] (A : Matrix n n K) (L : Matrix s n K)
    (v : n → K) (h : ∀ j : ℕ, L *ᵥ (A ^ j *ᵥ v) = 0) (t : ℝ) :
    L *ᵥ (matrixExp (t • A) *ᵥ v) = 0 := by
  let F : Matrix n n K →ₗ[K] s → K :=
    L.mulVecLin.comp ((LinearMap.applyₗ v).comp Matrix.toLin'.toLinearMap)
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := K) (t • A)).map
    F.toContinuousLinearMap F.toContinuousLinearMap.continuous
  have hz : (F.toContinuousLinearMap ∘ fun j : ℕ => (((j.factorial : K)⁻¹) • (t • A) ^ j)) = 0 := by
    funext j
    change F (((j.factorial : K)⁻¹) • (t • A) ^ j) = 0
    change L *ᵥ ((((j.factorial : K)⁻¹) • (t • A) ^ j) *ᵥ v) = 0
    rw [smul_pow, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h j, smul_zero, smul_zero]
  change HasSum _ (L *ᵥ (matrixExp (t • A) *ᵥ v)) at hs
  rw [hz] at hs
  exact hs.unique hasSum_zero

omit [DecidableEq n] [DecidableEq s] in
/-- The kernel of a PSD Lyapunov solution is invariant and unobserved by the forcing factor.
@isnad1 id=and.3h7v.s9.b00edd52eff6 from=translated src=- shape=301dc23f vocab=91baa2fd
-/
theorem kernel_lyapunov_invariant {K : Type*} [RCLike K] (A : Matrix n n K) (B : Matrix n s K)
    (X : Matrix n n K) (hX : X.PosSemidef) (heq : A * X + X * Aᴴ + B * Bᴴ = 0)
    (v : n → K) (hv : X *ᵥ v = 0) : Bᴴ *ᵥ v = 0 ∧ X *ᵥ (Aᴴ *ᵥ v) = 0 := by
  have hrow : star v ᵥ* X = 0 := by
    have h := Matrix.star_mulVec X v
    rw [hv, star_zero, hX.isHermitian.eq] at h
    exact h.symm
  have hq := congrArg (fun M : Matrix n n K => star v ⬝ᵥ (M *ᵥ v)) heq
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.zero_mulVec,
    dotProduct_zero] at hq
  have h₁ : star v ⬝ᵥ ((A * X) *ᵥ v) = 0 := by rw [← Matrix.mulVec_mulVec, hv]; simp
  have h₂ : star v ⬝ᵥ ((X * Aᴴ) *ᵥ v) = 0 := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hrow]
    simp
  rw [h₁, h₂, zero_add, zero_add] at hq
  have hBB : (B * Bᴴ) *ᵥ v = 0 :=
    ((Matrix.posSemidef_self_mul_conjTranspose B).dotProduct_mulVec_zero_iff v).mp hq
  have hB : Bᴴ *ᵥ v = 0 := (Matrix.self_mul_conjTranspose_mulVec_eq_zero B v).mp hBB
  refine ⟨hB, ?_⟩
  have he := congrArg (fun M : Matrix n n K => M *ᵥ v) heq
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv, hB, Matrix.mulVec_zero,
    Matrix.zero_mulVec, zero_add, add_zero] at he
  exact he

/-- The actual finite controllability matrix, ordered by power and input index.-/
def controllabilityMatrix {K : Type*} [RCLike K] (A : Matrix n n K) (B : Matrix n s K) :
    Matrix n (Fin (Fintype.card n) × s) K := fun i j => (A ^ (j.1 : ℕ) * B) i j.2

end NLAlib
