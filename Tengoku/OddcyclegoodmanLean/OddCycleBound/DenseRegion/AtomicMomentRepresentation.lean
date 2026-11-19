import Tengoku.Seed.Analysis.InnerProductSpace.Spectrum
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Expansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators InnerProductSpace

namespace OddCycleBound.DenseRegion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def linearIter (T : E →ₗ[ℝ] E) : ℕ → E → E
  | 0 => id
  | j + 1 => fun x => T (linearIter T j x)

/--
@isnad1 id=eq.0h3v.s6.e3332bfcbe7a from=translated src=- shape=5c5bb28b vocab=880ebbf2
-/
@[simp] lemma linearIter_zero (T : E →ₗ[ℝ] E) (x : E) : linearIter T 0 x = x := rfl

/--
@isnad1 id=eq.0h4v.s7.496c928f7dc6 from=translated src=- shape=85264300 vocab=d56eb422
-/
lemma linearIter_succ (T : E →ₗ[ℝ] E) (j : ℕ) (x : E) :
    linearIter T (j + 1) x = T (linearIter T j x) := rfl

section FiniteDimensional

variable [FiniteDimensional ℝ E]

noncomputable def finiteAtomEigenvalue (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) :
    Fin (Module.finrank ℝ E) → ℝ := hT.eigenvalues rfl

noncomputable def finiteAtomWeight (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (g : E) :
    Fin (Module.finrank ℝ E) → ℝ := fun i =>
  inner ℝ g (hT.eigenvectorBasis rfl i) ^ 2

/--
@isnad1 id=le.1h4v.s7.7ce895a550ec from=translated src=- shape=d9f42186 vocab=0479baa6
-/
lemma finiteAtomWeight_nonneg (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (g : E) (i) :
    0 ≤ finiteAtomWeight T hT g i := sq_nonneg _

/--
@isnad1 id=eq.1h5v.s9.c0c72d408a92 from=translated src=- shape=a670df1e vocab=92bdd1f2
-/
lemma inner_eigenvector_linearIter (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (g : E) (j : ℕ) (i : Fin (Module.finrank ℝ E)) :
    inner ℝ (hT.eigenvectorBasis rfl i) (linearIter T j g) =
      finiteAtomEigenvalue T hT i ^ j * inner ℝ (hT.eigenvectorBasis rfl i) g := by
  induction j with
  | zero => simp [finiteAtomEigenvalue]
  | succ j ih =>
      have heigen : T (hT.eigenvectorBasis rfl i) =
          finiteAtomEigenvalue T hT i • hT.eigenvectorBasis rfl i := by
        simp [finiteAtomEigenvalue]
      rw [linearIter_succ, ← hT (hT.eigenvectorBasis rfl i) (linearIter T j g),
        heigen, real_inner_smul_left, ih]
      ring

/--
@isnad1 id=eq.1h4v.s7.20a6604a4795 from=translated src=- shape=01b0b86c vocab=8e9421b9
-/
theorem inner_linearIter_eq_atomicMoment (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (g : E) (j : ℕ) :
    inner ℝ g (linearIter T j g) =
      atomicMoment (finiteAtomWeight T hT g) (finiteAtomEigenvalue T hT) j := by
  let b := hT.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  rw [← b.sum_inner_mul_inner g (linearIter T j g)]
  unfold atomicMoment finiteAtomWeight
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvector_linearIter T hT g j i]
  rw [real_inner_comm (hT.eigenvectorBasis rfl i) g]
  ring

end FiniteDimensional

end OddCycleBound.DenseRegion
