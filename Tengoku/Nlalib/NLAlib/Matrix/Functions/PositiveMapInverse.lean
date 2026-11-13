import Tengoku.Nlalib.NLAlib.Matrix.Functions.PositiveMapSpectral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inverse Jensen inequality for positive unital maps

The same spectral block construction as Kadison's inequality, with scalar
coefficients `sqrt λ` and `1/sqrt λ`, proves Choi's inverse inequality.
Strict positivity of the image follows from an actual positive scalar gap.
Tropp (2022), Theorem 12.19. Atlas: `positive-map-inverse-jensen`.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Positive scalar reciprocal blocks are positive after tensoring by a PSD matrix.
@isnad1 id=possemid.2h3v.s6.959291e518ed from=translated src=- shape=0742b61f vocab=0ff864ac
-/
theorem posSemidef_reciprocal_fromBlocks {B : Matrix m m ℂ}
    (hB : B.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (fromBlocks ((t : ℂ) • B) B B ((t : ℂ)⁻¹ • B)).PosSemidef := by
  let a : ℂ := Real.sqrt t
  have ha : a ≠ 0 := by dsimp [a]; exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have haa : a * a = (t : ℂ) := by
    dsimp [a]
    exact_mod_cast Real.mul_self_sqrt ht.le
  have hstar : star a = a := by simp [a]
  have hstari : star (a⁻¹) = a⁻¹ := by simp [a]
  have hi : a⁻¹ * a⁻¹ = (t : ℂ)⁻¹ := by rw [← _root_.mul_inv_rev, haa]
  simpa only [hstar, hstari, haa, hi, mul_inv_cancel₀ ha,
    inv_mul_cancel₀ ha, one_smul] using posSemidef_scalar_gram_fromBlocks hB a a⁻¹

/-- A Hermitian invertible matrix has the reciprocal spectral expansion.
@isnad1 id=eq.2h2v.s7.cc52aceaa078 from=translated src=- shape=a7a2657a vocab=1bf0d6d7
-/
theorem inv_eq_sum_inv_eigenvalue_smul_unitarySpectralProjector
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hu : IsUnit A) :
    A⁻¹ = ∑ i, (hA.eigenvalues i : ℂ)⁻¹ •
      unitarySpectralProjector hA.eigenvectorUnitary i := by
  calc
    A⁻¹ = Ring.inverse A := Matrix.nonsing_inv_eq_ringInverse A
    _ = cfc (fun x : ℝ => x⁻¹) A :=
      (cfc_ringInverse_id (R := ℝ) A hu hA).symm
    _ = _ := by
      rw [cfc_eq_sum_smul_unitarySpectralProjector hA]
      simp only [Complex.ofReal_inv]

end NLAlib
