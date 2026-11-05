module

public import Tengoku.Seed.Analysis.Fourier.ZMod
import Tengoku.KummerCriterion.KummerCriterion.GaussSum.SignInvariant.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the operator-theoretic and matrix-reduction part of the
finite-Fourier sign-invariant package.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-- The DFT scaled by `1 / √p`, so that its square is pullback by negation.-/
noncomputable def normalizedDft : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) :=
  ((Real.sqrt p : ℂ)⁻¹) •
    ((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap)

/--
@isnad1 id=eq.0h3v.s8.8db109a6f381 from=translated src=- shape=2a141fa5 vocab=5e7f69fb
-/
theorem normalizedDft_apply (Φ : ZMod p → ℂ) (x : ZMod p) :
    normalizedDft p Φ x = (Real.sqrt p : ℂ)⁻¹ * ZMod.dft Φ x := by
  simp [normalizedDft, smul_eq_mul]

/--
@isnad1 id=eq.0h3v.s8.a0eabd0efb06 from=translated src=- shape=94d65196 vocab=f93cf6e8
-/
theorem normalizedDft_sq_apply (Φ : ZMod p → ℂ) (x : ZMod p) :
    normalizedDft p (normalizedDft p Φ) x = Φ (-x) := by
  have hp_nonneg : (0 : ℝ) ≤ p := by
    exact_mod_cast Nat.zero_le p
  have hsqrt_ne_real : (Real.sqrt p : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (by exact_mod_cast hp.out.pos)
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_ne_real
  have hscalar :
      (Real.sqrt p : ℂ)⁻¹ * ((Real.sqrt p : ℂ)⁻¹ * (p : ℂ)) = 1 := by
    field_simp [hsqrt_ne]
    have hsqrt_sq : ((Real.sqrt p : ℂ) ^ 2) = (p : ℂ) := by
      exact_mod_cast (Real.sq_sqrt hp_nonneg)
    simpa [pow_two] using hsqrt_sq.symm
  calc
    normalizedDft p (normalizedDft p Φ) x
        = ((Real.sqrt p : ℂ)⁻¹ * ((Real.sqrt p : ℂ)⁻¹ * (p : ℂ))) * Φ (-x) := by
            simp [normalizedDft, ZMod.dft_dft, mul_assoc, mul_left_comm, mul_comm]
    _ = Φ (-x) := by simp [hscalar]

/-- The raw Fourier kernel matrix for `ZMod.dft` in the standard basis.-/
noncomputable def fourierMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k => ZMod.stdAddChar (N := p) (-(x * k))

/-- The normalized Fourier matrix, i.e. the matrix of `normalizedDft`.-/
noncomputable def normalizedFourierMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k => (Real.sqrt p : ℂ)⁻¹ * ZMod.stdAddChar (N := p) (-(x * k))

/--
@isnad1 id=eq.0h1v.s5.c463ac7b208c from=translated src=- shape=4b756370 vocab=61235615
-/
theorem normalizedFourierMatrix_eq_smul_fourierMatrix :
    normalizedFourierMatrix p = ((Real.sqrt p : ℂ)⁻¹) • fourierMatrix p := by
  ext x k
  simp [normalizedFourierMatrix, fourierMatrix, smul_eq_mul]

/-- Matrix form of the normalized DFT in the standard basis.
@isnad1 id=eq.0h1v.s10.e44a0ff6ead2 from=translated src=- shape=717cee02 vocab=508c0cc5
-/
theorem toMatrix_normalizedDft_eq_normalizedFourierMatrix :
    LinearMap.toMatrix (Pi.basisFun ℂ (ZMod p)) (Pi.basisFun ℂ (ZMod p))
        (normalizedDft p) =
      normalizedFourierMatrix p := by
  ext x k
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
  rw [normalizedDft_apply]
  simpa [normalizedFourierMatrix, mul_comm] using
    congrArg (fun z : ℂ => (Real.sqrt p : ℂ)⁻¹ * z)
      (dft_basisFun_apply (p := p) (x := k) (k := x))

/-- Determinant reduction from `normalizedDft` to its explicit Fourier matrix.
@isnad1 id=eq.0h1v.s9.29952c22767b from=translated src=- shape=77217f52 vocab=28b3966d
-/
theorem det_normalizedDft_eq_det_normalizedFourierMatrix :
    LinearMap.det (normalizedDft p) = Matrix.det (normalizedFourierMatrix p) := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (ZMod p)) (normalizedDft p),
    toMatrix_normalizedDft_eq_normalizedFourierMatrix]

/-- A fixed equivalence used to reindex `ZMod p` by `Fin p` for matrix
determinant computations.-/
noncomputable def zmodEquivFin : ZMod p ≃ Fin p := by
  exact (ZMod.finEquiv p).symm.toEquiv

/--
@isnad1 id=eq.0h2v.s6.8b632eb35b8b from=translated src=- shape=c4f14b00 vocab=21961f07
-/
theorem zmodEquivFin_symm_apply (i : Fin p) : (zmodEquivFin (p := p)).symm i = (i : ZMod p) := by
  cases p with
  | zero =>
      exact (hp.out.ne_zero rfl).elim
  | succ n =>
      apply Fin.ext
      simpa [ZMod.finEquiv] using! (ZMod.val_natCast_of_lt i.is_lt).symm

/-- The normalized Fourier matrix reindexed by `Fin p`.-/
noncomputable def normalizedFourierMatrixFin : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (zmodEquivFin (p := p)) (zmodEquivFin (p := p)) (normalizedFourierMatrix p)

/-- The raw Fourier matrix reindexed by `Fin p`.-/
noncomputable def fourierMatrixFin : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (zmodEquivFin (p := p)) (zmodEquivFin (p := p)) (fourierMatrix p)

/--
@isnad1 id=eq.0h1v.s5.9e522b23e945 from=translated src=- shape=4b756370 vocab=5b56f649
-/
theorem normalizedFourierMatrixFin_eq_smul_fourierMatrixFin :
    normalizedFourierMatrixFin p = ((Real.sqrt p : ℂ)⁻¹) • fourierMatrixFin p := by
  ext i j
  simp [normalizedFourierMatrixFin, fourierMatrixFin, normalizedFourierMatrix_eq_smul_fourierMatrix]

/-- Reindexing does not change the determinant, so the `Fin p` model is a clean
stand-in for the original normalized Fourier matrix.
@isnad1 id=eq.0h1v.s5.da47a4f86d51 from=translated src=- shape=15764c8c vocab=77bc08bc
-/
theorem det_normalizedFourierMatrix_eq_det_normalizedFourierMatrixFin :
    Matrix.det (normalizedFourierMatrix p) = Matrix.det (normalizedFourierMatrixFin p) := by
  change Matrix.det (normalizedFourierMatrix p) =
    Matrix.det (Matrix.reindex (zmodEquivFin (p := p)) (zmodEquivFin (p := p))
      (normalizedFourierMatrix p))
  exact (Matrix.det_reindex_self (zmodEquivFin (p := p)) (normalizedFourierMatrix p)).symm

end SignInvariant

end KummerCriterion
