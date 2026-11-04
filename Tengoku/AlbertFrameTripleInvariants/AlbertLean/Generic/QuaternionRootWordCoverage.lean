import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionSimilitudeWordCoverage
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FiniteQuadraticRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms central_rescale_conjugation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_twelve_word_of_multiplier_root` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_twelve_word_after_root` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.RootWordCoverage

open GroupedBridge SymplecticMatrixBridge ActualFrameCoverage WordMatrixConnection
open SimilitudeWordCoverage AlbertLean.Generic.SymplecticTransvection
open AlbertLean.Generic.FiniteQuadraticRoots

universe u
variable {K : Type u} [Field K] [CharZero K]

private theorem scalarSimilitude_one : scalarSimilitude (1 : K) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [scalarSimilitude, Matrix.one_apply]

/-- Central rescaling cancels on every matrix, without a carrier hypothesis.
@isnad1 id=eq.1h5v.s8.0e37964b4a3c from=translated src=- shape=9ba82e42 vocab=ad46db6b
-/
theorem central_rescale_conjugation (M N X : Mat6 K) (r : K) (hr : r ≠ 0) :
    (r⁻¹ • M) * X * (r • N) = M * X * N := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp [hr]

private theorem normalized_form (M : Mat6 K) (mu r : K) (hr : r ≠ 0)
    (hsq : r ^ 2 = mu)
    (hform : M.transpose * symplecticJ * M = mu • symplecticJ) :
    (r⁻¹ • M).transpose * symplecticJ * (r⁻¹ • M) = symplecticJ := by
  have hscale : (r⁻¹ * r⁻¹) * mu = 1 := by
    rw [← hsq, pow_two]
    field_simp [hr]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hform, smul_smul, hscale, one_smul]

/-- Once a root of the multiplier is available, an actual twelve-word acts
exactly as the original similitude on the entire matrix algebra.
@isnad1 id=ex.5h5v.s9.38c39f1594ae from=translated src=- shape=daf19def vocab=32eec83a
-/
theorem exists_twelve_word_of_multiplier_root
    (M N : Mat6 K) (mu r : K)
    (hMN : M * N = 1) (hNM : N * M = 1) (hr : r ≠ 0)
    (hsq : r ^ 2 = mu)
    (hform : M.transpose * symplecticJ * M = mu • symplecticJ) :
    ∃ word : List (Step (K := K) (V := Vec6 K)), word.length = 12 ∧
      ∀ X : Mat6 K, wordMatrix word * X * inverseWordMatrix word = M * X * N := by
  let A : Mat6 K := r⁻¹ • M
  let B : Mat6 K := r • N
  have hAB : A * B = 1 := by
    simp [A, B, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMN, hr]
  have hBA : B * A = 1 := by
    simp [A, B, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hNM, hr]
  have hA : A.transpose * symplecticJ * A = (1 : K) • symplecticJ := by
    simpa only [A, one_smul] using normalized_form M mu r hr hsq hform
  obtain ⟨schedule, hs⟩ :=
    exists_fixed_twelve_scalar_presentation_for_gsp_extension_agreement
      A B 1 hAB hBA one_ne_zero hA
  let word := List.ofFn schedule
  have hw : wordMatrix word = A := by
    simpa only [scalarSimilitude_one, Matrix.mul_one, word, wordMatrix,
      fixedTwelveMap] using hs.symm
  have hwi : inverseWordMatrix word = B := by
    calc
      inverseWordMatrix word = inverseWordMatrix word * 1 := (Matrix.mul_one _).symm
      _ = inverseWordMatrix word * (A * B) := by rw [hAB]
      _ = (inverseWordMatrix word * A) * B := (Matrix.mul_assoc _ _ _).symm
      _ = B := by rw [← hw, inverse_mul_wordMatrix, Matrix.one_mul]
  refine ⟨word, by exact List.length_ofFn, ?_⟩
  intro X
  rw [hw, hwi]
  exact central_rescale_conjugation M N X r hr

private theorem map_symplecticJ
    {L : Type u} [Field L] [CharZero L] (f : K →+* L) :
    f.mapMatrix (symplecticJ : Mat6 K) = symplecticJ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [symplecticJ, Matrix.one_apply]

private theorem map_similitude_form
    {L : Type u} [Field L] [CharZero L] (f : K →+* L)
    (M : Mat6 K) (mu : K)
    (hform : M.transpose * symplecticJ * M = mu • symplecticJ) :
    (f.mapMatrix M).transpose * symplecticJ * f.mapMatrix M =
      f mu • symplecticJ := by
  have ht : f.mapMatrix M.transpose = (f.mapMatrix M).transpose := rfl
  have hs : f.mapMatrix (mu • (symplecticJ : Mat6 K)) =
      f mu • f.mapMatrix (symplecticJ : Mat6 K) := by
    ext i j
    exact f.map_mul mu (symplecticJ i j)
  have h := congrArg f.mapMatrix hform
  simp only [map_mul, ht, hs, map_symplecticJ] at h
  exact h

/-- No square-root hypothesis is added to the input: one existing finite
root extension supplies an actual word and the full conjugation identity.
@isnad1 id=ex.4h4v.s11.9eea77e535ca from=translated src=- shape=b5ba874a vocab=0f41d267
-/
theorem exists_twelve_word_after_root
    (M N : Mat6 K) (mu : K)
    (hMN : M * N = 1) (hNM : N * M = 1) (hmu : mu ≠ 0)
    (hform : M.transpose * symplecticJ * M = mu • symplecticJ) :
    ∃ R : OneRootField K mu, ∃ _ : CharZero R.Carrier,
      ∃ word : List (Step (K := R.Carrier) (V := Vec6 R.Carrier)),
        word.length = 12 ∧ ∀ X : Mat6 R.Carrier,
          wordMatrix word * X * inverseWordMatrix word =
            R.embedding.mapMatrix M * X * R.embedding.mapMatrix N := by
  obtain ⟨R⟩ := oneRootField_nonempty K mu
  letI : CharZero R.Carrier := charZero_of_embedding R.embedding
  have hr : R.root ≠ 0 := by
    intro hz
    have hzero : R.embedding mu = 0 := by simpa [hz] using R.root_sq.symm
    exact hmu (R.embedding.injective (hzero.trans R.embedding.map_zero.symm))
  have hMN' : R.embedding.mapMatrix M * R.embedding.mapMatrix N = 1 := by
    rw [← map_mul, hMN, map_one]
  have hNM' : R.embedding.mapMatrix N * R.embedding.mapMatrix M = 1 := by
    rw [← map_mul, hNM, map_one]
  obtain ⟨word, hlen, hword⟩ := exists_twelve_word_of_multiplier_root
    (R.embedding.mapMatrix M) (R.embedding.mapMatrix N) (R.embedding mu) R.root
    hMN' hNM' hr R.root_sq (map_similitude_form R.embedding M mu hform)
  exact ⟨R, inferInstance, word, hlen, hword⟩

end AlbertLean.Generic.QuaternionRow.RootWordCoverage
