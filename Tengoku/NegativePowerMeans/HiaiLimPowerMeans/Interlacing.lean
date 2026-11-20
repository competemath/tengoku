import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.Shorting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cauchy--Poincaré interlacing for isometric compressions

The interlacing theorem is isolated as a named published input.  In the
notation used below it is exactly Theorem 26.1 in R. Bhatia,
*Perturbation Bounds for Matrix Eigenvalues*, SIAM, 2007.
-/

namespace HiaiLimPowerMeans

open Matrix
open scoped ComplexOrder MatrixOrder Matrix

variable {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- A compression of a Hermitian matrix is Hermitian.
@isnad1 id=ishermit.1h5v.s7.2a3593530915 from=translated src=- shape=d123cd89 vocab=63869ed6
-/
theorem compress_isHermitian
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (V : Matrix (Fin n) (Fin k) 𝕜) : (compress V A).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul V hA

/-- **Cauchy--Poincaré interlacing**, in the precise finite-matrix form
used by this development.

If `A` has decreasing eigenvalues `λ₁ ≥ ⋯ ≥ λₙ` and `V` is an
`n × k` isometry, then the decreasing eigenvalues `μ₁ ≥ ⋯ ≥ μₖ` of
`Vᴴ A V` satisfy

`λᵢ ≥ μᵢ ≥ λ_{n-k+i}`.

This is Theorem 26.1 of Bhatia's *Perturbation Bounds for Matrix
Eigenvalues*.  Its precise finite-matrix form is verified in the standalone
module `BoundaryProofs.InterlacingProof`.-/
def Interlacing (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (n k : ℕ) (hkn : k ≤ n)
    (A : Matrix (Fin n) (Fin n) 𝕜) (V : Matrix (Fin n) (Fin k) 𝕜)
    (hA : A.IsHermitian), MatrixIsometry V →
      ∀ i : Fin k,
        decreasingEigenvalues hA (Fin.castLE hkn i) ≥
            decreasingEigenvalues (compress_isHermitian hA V) i ∧
          decreasingEigenvalues (compress_isHermitian hA V) i ≥
            decreasingEigenvalues hA (bottomFinEmbedding hkn i)

/-- The upper interlacing inequality used in the paper: the `i`th largest
eigenvalue of an isometric compression is at most the `i`th largest
eigenvalue of the original Hermitian matrix.
@isnad1 id=le.4h6v.s7.a0e2bd2ff1d0 from=translated src=- shape=09e5ac23 vocab=05d3c41b
-/
theorem decreasingEigenvalues_compress_le
    (hInterlace : Interlacing 𝕜) (hkn : k ≤ n)
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    {V : Matrix (Fin n) (Fin k) 𝕜} (hV : MatrixIsometry V)
    (i : Fin k) :
    decreasingEigenvalues (compress_isHermitian hA V) i ≤
      decreasingEigenvalues hA (Fin.castLE hkn i) :=
  (hInterlace n k hkn A V hA hV i).1

/-- The exact Cauchy-interlacing step from the shorted-matrix argument,
applied to `Vᴴ B⁻¹ V`.
@isnad1 id=le.4h6v.s7.2272d662ef15 from=translated src=- shape=43117ca0 vocab=452c9a6c
-/
theorem decreasingEigenvalues_compress_inv_le
    (hInterlace : Interlacing 𝕜) (hkn : k ≤ n)
    {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosDef)
    {V : Matrix (Fin n) (Fin k) 𝕜} (hV : MatrixIsometry V)
    (i : Fin k) :
    decreasingEigenvalues (compress_isHermitian hB.inv.isHermitian V) i ≤
      decreasingEigenvalues hB.inv.isHermitian (Fin.castLE hkn i) :=
  decreasingEigenvalues_compress_le hInterlace hkn hB.inv.isHermitian hV i

/-- The shorted-matrix consequence of Cauchy interlacing used in the paper.
For `i < k`, the `i`th eigenvalue in increasing order of `S_V(B)` is at
least the `i`th eigenvalue in increasing order of `B`.
@isnad1 id=le.4h6v.s6.8e1dc44d2648 from=translated src=- shape=625b54ee vocab=23ed3025
-/
theorem increasingEigenvalues_le_shorted
    (hInterlace : Interlacing 𝕜) (hkn : k ≤ n)
    {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosDef)
    {V : Matrix (Fin n) (Fin k) 𝕜} (hV : MatrixIsometry V)
    (i : Fin k) :
    increasingEigenvalues (shorted_posDef hV hB).isHermitian i ≥
      increasingEigenvalues hB.isHermitian (Fin.castLE hkn i) := by
  let H : Matrix (Fin k) (Fin k) 𝕜 := compress V B⁻¹
  have hH : H.PosDef := compress_posDef hV hB.inv
  have hinterlace :
      decreasingEigenvalues hH.isHermitian i ≤
        decreasingEigenvalues hB.inv.isHermitian (Fin.castLE hkn i) := by
    simpa [H] using decreasingEigenvalues_compress_inv_le
      hInterlace hkn hB hV i
  have hright :
      decreasingEigenvalues hB.inv.isHermitian (Fin.castLE hkn i) =
        (decreasingEigenvalues hB.isHermitian (Fin.castLE hkn i).rev)⁻¹ :=
    Matrix.PosDef.decreasingEigenvalues_inv hB (Fin.castLE hkn i)
  have hposH : 0 < decreasingEigenvalues hH.isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos hH i
  have hinv :
      decreasingEigenvalues hB.isHermitian (Fin.castLE hkn i).rev ≤
        (decreasingEigenvalues hH.isHermitian i)⁻¹ := by
    have := inv_anti₀ hposH (hright ▸ hinterlace)
    simpa using this
  have hleft :
      increasingEigenvalues (shorted_posDef hV hB).isHermitian i =
        (decreasingEigenvalues hH.isHermitian i)⁻¹ := by
    simpa [shorted, H, increasingEigenvalues, Function.comp_def] using
      Matrix.PosDef.decreasingEigenvalues_inv hH i.rev
  calc
    increasingEigenvalues hB.isHermitian (Fin.castLE hkn i) =
        decreasingEigenvalues hB.isHermitian (Fin.castLE hkn i).rev := rfl
    _ ≤ (decreasingEigenvalues hH.isHermitian i)⁻¹ := hinv
    _ = increasingEigenvalues (shorted_posDef hV hB).isHermitian i := hleft.symm

end HiaiLimPowerMeans
