import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.NormBounds
import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
import Tengoku.Seed.LinearAlgebra.Matrix.PosDef
import Tengoku.Seed.Probability.UniformOn
import Tengoku.Seed.Probability.Independence.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.SumMeasure
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact paired-vector algebra for the MSS quota step

This file proves the finite four-outcome covariance identity and the exact complementary
index quotas used in the manuscript. It does not assert the MSS selection theorem.
Any theorem passing from a supplied outcome bound to its two children states that premise
explicitly; the missing analytic existence theorem is not introduced as an axiom.
-/

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace NoEpsilon
namespace MSSSelection

variable {ι κ : Type*} [Fintype ι]

/-- A vector outer product, with the Euclidean operator interpretation.-/
noncomputable def outer (v : ι → ℂ) : Matrix ι ι ℂ := fun i j ↦ v i * star (v j)

/-- Squared Euclidean norm, written as a finite sum to avoid the function-space sup norm.-/
noncomputable def energy (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- First Boolean chooses the permutation; second Boolean chooses the relative sign.-/
noncomputable def pairedVector (a b : ι → ℂ) (q : Bool × Bool) : (ι ⊕ ι) → ℂ :=
  fun z ↦ (Real.sqrt 2 : ℂ) * Sum.elim
    (if q.1 then b else a)
    (if q.2 then -(if q.1 then a else b) else (if q.1 then a else b)) z

private theorem sqrt_two_complex_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

omit [Fintype ι] in
/-- Averaging the four independent local choices cancels the two cross-covariance blocks.
@isnad1 id=eq.0h3v.s7.388c4fb93649 from=translated src=- shape=a7288c47 vocab=1c64f16b
-/
theorem paired_covariance (a b : ι → ℂ) :
    (1 / 4 : ℂ) • ∑ q : Bool × Bool, outer (pairedVector a b q) =
      Matrix.fromBlocks (outer a + outer b) 0 0 (outer a + outer b) := by
  ext i j
  cases i <;> cases j <;>
    simp [outer, pairedVector, Fintype.sum_prod_type,
      Matrix.fromBlocks, mul_add, star_mul] <;>
    ring_nf <;> simp [sqrt_two_complex_sq] <;> ring

/-- The selected first-half vector, retaining its original index label.-/
def firstVector (a b : κ → ι → ℂ) (q : κ → Bool × Bool) (i : κ) : ι → ℂ :=
  if (q i).1 then b i else a i

/-- The complementary half; the relative sign has no effect on its covariance.-/
def secondVector (a b : κ → ι → ℂ) (q : κ → Bool × Bool) (i : κ) : ι → ℂ :=
  if (q i).1 then a i else b i

omit [Fintype ι] in
/-- Every realized first diagonal block is twice the first-half frame operator.
@isnad1 id=eq.0h5v.s7.db3d6b1ef742 from=translated src=- shape=41390b37 vocab=4e01b4a4
-/
theorem paired_first_block [Fintype κ] (a b : κ → ι → ℂ) (q : κ → Bool × Bool) :
    (∑ i, outer (pairedVector (a i) (b i) (q i))).submatrix Sum.inl Sum.inl =
      (2 : ℂ) • ∑ i, outer (firstVector a b q i) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [outer, pairedVector, firstVector, star_mul]
  ring_nf
  simp [sqrt_two_complex_sq]
  ring

omit [Fintype ι] in
/-- Every realized second diagonal block is twice the complementary frame operator.
@isnad1 id=eq.0h5v.s7.28c682775845 from=translated src=- shape=41390b37 vocab=8e442e52
-/
theorem paired_second_block [Fintype κ] (a b : κ → ι → ℂ) (q : κ → Bool × Bool) :
    (∑ i, outer (pairedVector (a i) (b i) (q i))).submatrix Sum.inr Sum.inr =
      (2 : ℂ) • ∑ i, outer (secondVector a b q i) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rcases hq : q k with ⟨s, t⟩
  cases s <;> cases t <;> simp [outer, pairedVector, secondVector, hq, star_mul] <;>
    ring_nf <;> simp [sqrt_two_complex_sq] <;> ring

omit [Fintype ι] in
/-- Summing the local expectations gives two identical copies of the original frame.
@isnad1 id=eq.0h4v.s8.bfb501b1c2c7 from=translated src=- shape=7d6732f3 vocab=49a96af3
-/
theorem paired_total_covariance [Fintype κ] (a b : κ → ι → ℂ) :
    (∑ i, (1 / 4 : ℂ) • ∑ q : Bool × Bool, outer (pairedVector (a i) (b i) q)) =
      Matrix.fromBlocks (∑ i, (outer (a i) + outer (b i))) 0 0
        (∑ i, (outer (a i) + outer (b i))) := by
  simp only [paired_covariance]
  ext i j
  cases i <;> cases j <;> simp [Matrix.sum_apply, Matrix.fromBlocks]

section Quotas

variable [DecidableEq κ]

/-- One original label from each pair.-/
def firstIndices (q : κ → Bool × Bool) (s : Finset κ) : Finset (κ × Bool) :=
  s.image (fun i ↦ (i, (q i).1))

/-- The other original label from each pair.-/
def secondIndices (q : κ → Bool × Bool) (s : Finset κ) : Finset (κ × Bool) :=
  s.image (fun i ↦ (i, !(q i).1))

/--
@isnad1 id=eq.0h3v.s4.036c5f8ef33b from=translated src=- shape=b2ae3b60 vocab=28132a4c
-/
theorem firstIndices_card (q : κ → Bool × Bool) (s : Finset κ) :
    (firstIndices q s).card = s.card :=
  Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)

/--
@isnad1 id=eq.0h3v.s4.f6a4524e0b20 from=translated src=- shape=b2ae3b60 vocab=e01115b5
-/
theorem secondIndices_card (q : κ → Bool × Bool) (s : Finset κ) :
    (secondIndices q s).card = s.card :=
  Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)

end Quotas

section OutcomeBounds

variable [DecidableEq ι]

private theorem norm_compression_le (E : Matrix (ι ⊕ ι) ι ℂ)
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (hE : ‖E‖ ≤ 1) :
    ‖E.conjTranspose * M * E‖ ≤ ‖M‖ := by
  calc
    ‖E.conjTranspose * M * E‖ ≤ ‖E.conjTranspose * M‖ * ‖E‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖E‖ * ‖M‖) * ‖E‖ := by
      rw [← Matrix.l2_opNorm_conjTranspose E]
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * ‖M‖) * 1 := by gcongr
    _ = ‖M‖ := by ring

/-- Each diagonal block is a contractive compression in the Euclidean operator norm.
@isnad1 id=and.0h2v.s7.3177e3885d31 from=translated src=- shape=a7b3912a vocab=390d76c8
-/
theorem diagonal_blocks_norm_le (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    ‖M.submatrix Sum.inl Sum.inl‖ ≤ ‖M‖ ∧
      ‖M.submatrix Sum.inr Sum.inr‖ ≤ ‖M‖ := by
  let E := Matrix.fromRows (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)
  let F := Matrix.fromRows (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
  have hE : E.conjTranspose * M * E = M.submatrix Sum.inl Sum.inl := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    simp [E, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows, Matrix.toBlocks₁₁]
    rfl
  have hF : F.conjTranspose * M * F = M.submatrix Sum.inr Sum.inr := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    simp [F, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows, Matrix.toBlocks₂₂]
    rfl
  exact ⟨by simpa only [hE] using norm_compression_le E M norm_rowEmbedding_left_le,
    by simpa only [hF] using norm_compression_le F M norm_rowEmbedding_right_le⟩

/-- A supplied good four-choice outcome controls both complementary half-frame operators.
This proves the deterministic conclusion after selection; it does not assert existence
of an outcome satisfying the displayed premise.
@isnad1 id=and.1h6v.s7.3d33619cd32b from=translated src=- shape=4179a7ae vocab=6a40e3c6
-/
theorem paired_children_bound_of_outcome [Fintype κ]
    (a b : κ → ι → ℂ) (q : κ → Bool × Bool) (T : ℝ)
    (hq : ‖∑ i, outer (pairedVector (a i) (b i) (q i))‖ ≤ T) :
    ‖∑ i, outer (firstVector a b q i)‖ ≤ T / 2 ∧
      ‖∑ i, outer (secondVector a b q i)‖ ≤ T / 2 := by
  obtain ⟨hleft, hright⟩ := diagonal_blocks_norm_le
    (∑ i, outer (pairedVector (a i) (b i) (q i)))
  rw [paired_first_block, norm_smul] at hleft
  rw [paired_second_block, norm_smul] at hright
  norm_num at hleft hright
  constructor <;> linarith

end OutcomeBounds

section Probability

open MeasureTheory ProbabilityTheory

/-- The uniform law on the four local outcomes.-/
noncomputable def pairLaw : Measure (Bool × Bool) := uniformOn Set.univ

/--
@isnad1 id=isprobab.0h0v.s3.f37cc89f5966 from=translated src=- shape=05d98aed vocab=26d436f7
-/
instance pairLaw_isProbability : IsProbabilityMeasure pairLaw := by
  unfold pairLaw
  infer_instance

/-- Independent four-choice laws, one for each pair label.-/
noncomputable def choiceLaw (κ : Type*) [Fintype κ] : Measure (κ → Bool × Bool) :=
  Measure.pi (fun _ : κ ↦ pairLaw)

omit [Fintype ι] in
/-- The paired vectors at different labels are independent random vectors.
@isnad1 id=iindepfu.0h4v.s6.acd47763bade from=translated src=- shape=f2687c4d vocab=f3d9acb6
-/
theorem paired_vectors_independent [Fintype κ] (a b : κ → ι → ℂ) :
    iIndepFun (fun i q ↦ pairedVector (a i) (b i) (q i)) (choiceLaw κ) := by
  exact iIndepFun_pi (fun i ↦ (measurable_of_countable _).aemeasurable)

/-- Product choice law is precisely the uniform law on all labelled choices.
@isnad1 id=eq.0h1v.s5.3e343cda4b7b from=translated src=- shape=76ea1f02 vocab=88f1d903
-/
theorem choiceLaw_eq_uniform [Fintype κ] :
    choiceLaw κ = uniformOn (Set.univ : Set (κ → Bool × Bool)) := by
  unfold choiceLaw pairLaw
  have hset : Set.univ.pi (fun _ : κ ↦ (Set.univ : Set (Bool × Bool))) =
      (Set.univ : Set (κ → Bool × Bool)) := Set.pi_univ Set.univ
  rw [← hset]
  exact uniformOn_pi.symm

/-- Expectations under the local law are actual arithmetic averages.
@isnad1 id=eq.0h2v.s7.3b4709923f83 from=translated src=- shape=bc08fedc vocab=8ca417cb
-/
theorem pairLaw_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (f : Bool × Bool → E) : ∫ q, f q ∂pairLaw = (1 / 4 : ℝ) • ∑ q, f q := by
  simp [pairLaw, uniformOn, ProbabilityTheory.cond, integral_smul_measure]

/-- The finite covariance algebra is also the actual matrix-valued expectation identity.
@isnad1 id=eq.0h3v.s8.98c78913869c from=translated src=- shape=b70a8ece vocab=68a0d048
-/
theorem paired_covariance_expectation [DecidableEq ι] (a b : ι → ℂ) :
    (∫ q, outer (pairedVector a b q) ∂pairLaw) =
      Matrix.fromBlocks (outer a + outer b) 0 0 (outer a + outer b) := by
  rw [pairLaw_integral]
  change (((1 / 4 : ℝ) : ℂ)) • (∑ q, outer (pairedVector a b q)) = _
  convert paired_covariance a b using 1
  norm_num

end Probability

section Positivity

omit [Fintype ι] in
/-- Each vector covariance is positive semidefinite.
@isnad1 id=possemid.0h2v.s4.77ea7b4847cb from=translated src=- shape=2ce6fcbd vocab=c78cfe3a
-/
theorem outer_posSemidef [Finite ι] (v : ι → ℂ) : (outer v).PosSemidef := by
  letI := Fintype.ofFinite ι
  exact Matrix.posSemidef_vecMulVec_self_star v

variable [DecidableEq ι]

end Positivity

end MSSSelection
end NoEpsilon
