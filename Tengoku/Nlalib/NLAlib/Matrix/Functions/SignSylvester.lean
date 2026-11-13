import Tengoku.Nlalib.NLAlib.Matrix.Functions.SignExistence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Sylvester equation in a matrix-sign block

The sign characterization determines the off-diagonal block as twice
the unique Sylvester solution. Higham, Functions of Matrices, Chapter 5;
matrix-toolkit derivations, Section `eq-sign-sylvester`.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A block upper triangular matrix has the union of its diagonal spectra.
@isnad1 id=eq.0h5v.s7.cf7c523b0cd8 from=translated src=- shape=f8cc9b5c vocab=07fba19a
-/
theorem spectrum_fromBlocks_zero₂₁ (A : Matrix m m ℂ) (C : Matrix m n ℂ)
    (B : Matrix n n ℂ) :
    spectrum ℂ (fromBlocks A C 0 B) = spectrum ℂ A ∪ spectrum ℂ B := by
  ext z
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_fromBlocks_zero₂₁,
    Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero, Set.mem_union]

/-- Positive stability is preserved by block upper triangular assembly.
@isnad1 id=ispositi.2h5v.s6.3326c6578216 from=translated src=- shape=91c7df83 vocab=c735654d
-/
theorem IsPositiveStable.fromBlocks {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : IsPositiveStable A) (hB : IsPositiveStable B) (C : Matrix m n ℂ) :
    IsPositiveStable (fromBlocks A C 0 B) := by
  intro z hz
  rw [spectrum_fromBlocks_zero₂₁] at hz
  exact hz.elim (hA z) (hB z)

/-- The off-diagonal block of the sign of `[A C;0 -B]` is twice the
Sylvester solution. Defective and nonnormal diagonal blocks are allowed.
atlas: matrix-sign-sylvester-block (partial)
@isnad1 id=eq.3h6v.s8.f702170a5f5c from=translated src=- shape=ed1d8573 vocab=23be225d
-/
theorem matrixSign_fromBlocks_sylvester
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : IsPositiveStable A)
    (hB : IsPositiveStable B) {C X : Matrix m n ℂ} (hX : A * X + X * B = C) :
    matrixSign (fromBlocks A C 0 (-B)) = fromBlocks 1 ((2 : ℂ) • X) 0 (-1) := by
  have hsep : ∀ z ∈ spectrum ℂ (fromBlocks A C 0 (-B)), z.re ≠ 0 := by
    intro z hz
    rw [spectrum_fromBlocks_zero₂₁] at hz
    rcases hz with hz | hz
    · exact (hA z hz).ne'
    · have hn : -z ∈ spectrum ℂ B := by
        rw [← spectrum.neg_eq] at hz
        exact Set.mem_neg.mp hz
      have hh := hB (-z) hn
      simp only [Complex.neg_re] at hh
      linarith
  symm
  apply IsMatrixSign.eq_matrixSign hsep
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_two, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.mul_neg, neg_neg, add_zero, zero_add, add_neg_cancel,
      Matrix.fromBlocks_one]
  · change fromBlocks A C 0 (-B) * fromBlocks 1 ((2 : ℂ) • X) 0 (-1) =
      fromBlocks 1 ((2 : ℂ) • X) 0 (-1) * fromBlocks A C 0 (-B)
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.smul_mul, neg_neg, add_zero, zero_add, smul_zero]
    congr 1
    rw [← hX]
    module
  · have heq : fromBlocks 1 ((2 : ℂ) • X) 0 (-1) * fromBlocks A C 0 (-B) =
        fromBlocks A (C - (2 : ℂ) • (X * B)) 0 B := by
      simp [Matrix.fromBlocks_multiply, Matrix.smul_mul, sub_eq_add_neg]
    rw [heq]
    exact hA.fromBlocks hB _

/-- Positive-stable diagonal blocks give exactly one Sylvester solution.
Together with `matrixSign_fromBlocks_sylvester`, this is the complete
Sylvester block-sign formula.
atlas: matrix-sign-sylvester-block (partial)
@isnad1 id=existsun.2h5v.s7.53c8f234f756 from=translated src=- shape=7c7bd4c3 vocab=5a7c9ac7
-/
theorem existsUnique_sylvester_of_positiveStable
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : IsPositiveStable A)
    (hB : IsPositiveStable B) (C : Matrix m n ℂ) :
    ∃! X : Matrix m n ℂ, A * X + X * B = C := by
  simpa only [Matrix.mul_neg, sub_neg_eq_add] using
    existsUnique_sylvester_of_disjoint_spectrum A (-B) (hA.disjoint_neg hB) C

end NLAlib
