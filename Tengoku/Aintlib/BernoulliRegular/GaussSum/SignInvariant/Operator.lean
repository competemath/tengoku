module

public import Tengoku.Aintlib.BernoulliRegular.GaussSum.SignInvariant.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the operator-theoretic and matrix-reduction part of the
finite-Fourier sign-invariant package.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-- The DFT scaled by `1 / √p`, so that its square is pullback by negation.-/
noncomputable def normalizedDft : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) :=
  ((Real.sqrt p : ℂ)⁻¹) •
    ((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap)

/-- Pullback of functions along `x ↦ -x`.-/
noncomputable def negArgumentLinearMap : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) where
  toFun Φ x := Φ (-x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h3v.s8.742bb4a32549 from=translated src=- shape=2a141fa5 vocab=2117cd25
-/
theorem normalizedDft_apply (Φ : ZMod p → ℂ) (x : ZMod p) :
    normalizedDft p Φ x = (Real.sqrt p : ℂ)⁻¹ * ZMod.dft Φ x := by
  simp [normalizedDft, smul_eq_mul]

/--
@isnad1 id=eq.0h3v.s8.4bd8b02442e7 from=translated src=- shape=94d65196 vocab=c6b56cce
-/
theorem normalizedDft_sq_apply (Φ : ZMod p → ℂ) (x : ZMod p) :
    normalizedDft p (normalizedDft p Φ) x = Φ (-x) := by
  have hp_nonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsqrt_ne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (by exact_mod_cast hp.out.pos)
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
    _ = Φ (-x) := by rw [hscalar, one_mul]

/-- The normalized DFT squares to pullback along negation.
@isnad1 id=eq.0h1v.s7.c573b33791f6 from=translated src=- shape=a6092fa7 vocab=81bc4b74
-/
theorem normalizedDft_sq_eq_negArgument :
    (normalizedDft p).comp (normalizedDft p) = negArgumentLinearMap p := by
  apply LinearMap.ext
  intro Φ
  ext x
  exact normalizedDft_sq_apply (p := p) Φ x

/-- The submodule of even functions on `ZMod p`.-/
def evenSubmodule : Submodule ℂ (ZMod p → ℂ) where
  carrier := {Φ | Function.Even Φ}
  zero_mem' := Function.Even.zero
  add_mem' hΦ hΨ := hΦ.add hΨ
  smul_mem' c _ hΦ := hΦ.const_smul c

/-- The submodule of odd functions on `ZMod p`.-/
def oddSubmodule : Submodule ℂ (ZMod p → ℂ) where
  carrier := {Φ | Function.Odd Φ}
  zero_mem' := Function.Odd.zero
  add_mem' hΦ hΨ := hΦ.add hΨ
  smul_mem' c _ hΦ := hΦ.const_smul c

/--
@isnad1 id=even.1h2v.s7.c6cbcca77893 from=translated src=- shape=5aca1c67 vocab=81c0cc22
-/
theorem normalizedDft_maps_even {Φ : ZMod p → ℂ} (hΦ : Function.Even Φ) :
    Function.Even (normalizedDft p Φ) := by
  have hdft : Function.Even (ZMod.dft Φ) := (ZMod.dft_even_iff).2 hΦ
  simpa [normalizedDft] using hdft.const_smul ((Real.sqrt p : ℂ)⁻¹)

/--
@isnad1 id=odd.1h2v.s7.2de0e61a56b1 from=translated src=- shape=5aca1c67 vocab=cf52b69d
-/
theorem normalizedDft_maps_odd {Φ : ZMod p → ℂ} (hΦ : Function.Odd Φ) :
    Function.Odd (normalizedDft p Φ) := by
  have hdft : Function.Odd (ZMod.dft Φ) := (ZMod.dft_odd_iff).2 hΦ
  simpa [normalizedDft] using hdft.const_smul ((Real.sqrt p : ℂ)⁻¹)

/-- The normalized DFT restricted to the even submodule.-/
noncomputable def normalizedDftEven :
    evenSubmodule (p := p) →ₗ[ℂ] evenSubmodule (p := p) :=
  (normalizedDft (p := p)).restrict fun _ hΦ ↦ normalizedDft_maps_even (p := p) hΦ

/-- The normalized DFT restricted to the odd submodule.-/
noncomputable def normalizedDftOdd :
    oddSubmodule (p := p) →ₗ[ℂ] oddSubmodule (p := p) :=
  (normalizedDft (p := p)).restrict fun _ hΦ ↦ normalizedDft_maps_odd (p := p) hΦ

/-- On even functions, the normalized DFT squares to the identity.
@isnad1 id=eq.1h2v.s8.f69eaf6ea9f8 from=translated src=- shape=8319193c vocab=81c0cc22
-/
theorem normalizedDft_sq_eq_self_of_even {Φ : ZMod p → ℂ} (hΦ : Function.Even Φ) :
    normalizedDft p (normalizedDft p Φ) = Φ := by
  ext x
  rw [normalizedDft_sq_apply (p := p)]
  exact hΦ x

/-- On odd functions, the normalized DFT squares to minus the identity.
@isnad1 id=eq.1h2v.s8.9862e98a0801 from=translated src=- shape=e4986e3e vocab=bf67169c
-/
theorem normalizedDft_sq_eq_neg_self_of_odd {Φ : ZMod p → ℂ} (hΦ : Function.Odd Φ) :
    normalizedDft p (normalizedDft p Φ) = -Φ := by
  ext x
  rw [normalizedDft_sq_apply (p := p)]
  simpa [Pi.neg_apply] using hΦ x

/-- The normalized DFT has square `id` on the even submodule.
@isnad1 id=eq.0h1v.s10.e49fcca5a8ec from=translated src=- shape=d0d9f9c3 vocab=a4e5aa16
-/
theorem normalizedDftEven_sq :
    (normalizedDftEven (p := p)).comp (normalizedDftEven (p := p)) =
      (LinearMap.id : evenSubmodule (p := p) →ₗ[ℂ] evenSubmodule (p := p)) := by
  ext Φ x
  exact congrFun (normalizedDft_sq_eq_self_of_even (p := p) Φ.2) x

/-- The normalized DFT has square `-id` on the odd submodule.
@isnad1 id=eq.0h1v.s10.aac2d64f6249 from=translated src=- shape=29a5400d vocab=2fea0b46
-/
theorem normalizedDftOdd_sq :
    (normalizedDftOdd (p := p)).comp (normalizedDftOdd (p := p)) =
      -(LinearMap.id : oddSubmodule (p := p) →ₗ[ℂ] oddSubmodule (p := p)) := by
  ext Φ x
  exact congrFun (normalizedDft_sq_eq_neg_self_of_odd (p := p) Φ.2) x

/-- The raw Fourier kernel matrix for `ZMod.dft` in the standard basis.-/
noncomputable def fourierMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k ↦ ZMod.stdAddChar (N := p) (-(x * k))

/-- The normalized Fourier matrix, i.e. the matrix of `normalizedDft`.-/
noncomputable def normalizedFourierMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k ↦ (Real.sqrt p : ℂ)⁻¹ * ZMod.stdAddChar (N := p) (-(x * k))

/--
@isnad1 id=eq.0h1v.s5.07861768c161 from=translated src=- shape=4b756370 vocab=88875a87
-/
theorem normalizedFourierMatrix_eq_smul_fourierMatrix :
    normalizedFourierMatrix p = ((Real.sqrt p : ℂ)⁻¹) • fourierMatrix p := by
  ext x k
  simp [normalizedFourierMatrix, fourierMatrix, smul_eq_mul]

/-- Matrix form of the unnormalized DFT in the standard basis.
@isnad1 id=eq.0h1v.s10.ee667d81a1d8 from=translated src=- shape=7918166f vocab=d74f4141
-/
theorem toMatrix_dft_eq_fourierMatrix :
    LinearMap.toMatrix (Pi.basisFun ℂ (ZMod p)) (Pi.basisFun ℂ (ZMod p))
        ((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap) =
      fourierMatrix p := by
  ext x k
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
  simpa [fourierMatrix, mul_comm] using
    (dft_basisFun_apply (p := p) (x := k) (k := x))

/-- Matrix form of the normalized DFT in the standard basis.
@isnad1 id=eq.0h1v.s10.8f4f1efeb393 from=translated src=- shape=717cee02 vocab=2a63cfaa
-/
theorem toMatrix_normalizedDft_eq_normalizedFourierMatrix :
    LinearMap.toMatrix (Pi.basisFun ℂ (ZMod p)) (Pi.basisFun ℂ (ZMod p))
        (normalizedDft p) =
      normalizedFourierMatrix p := by
  ext x k
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
  rw [normalizedDft_apply]
  simpa [normalizedFourierMatrix, mul_comm] using
    congrArg (fun z : ℂ ↦ (Real.sqrt p : ℂ)⁻¹ * z)
      (dft_basisFun_apply (p := p) (x := k) (k := x))

/-- Determinant reduction from `normalizedDft` to its explicit Fourier matrix.
@isnad1 id=eq.0h1v.s9.8230da4b6e0b from=translated src=- shape=77217f52 vocab=9117868b
-/
theorem det_normalizedDft_eq_det_normalizedFourierMatrix :
    LinearMap.det (normalizedDft p) = Matrix.det (normalizedFourierMatrix p) := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (ZMod p)) (normalizedDft p),
    toMatrix_normalizedDft_eq_normalizedFourierMatrix]

/-- A fixed equivalence used to reindex `ZMod p` by `Fin p` for matrix
determinant computations.-/
noncomputable def zmodEquivFin : ZMod p ≃ Fin p :=
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  (ZMod.finEquiv p).symm.toEquiv

/--
@isnad1 id=eq.0h2v.s6.20c6fac63f8f from=translated src=- shape=c4f14b00 vocab=8726bd3c
-/
theorem zmodEquivFin_symm_apply (i : Fin p) :
    (zmodEquivFin (p := p)).symm i = (i : ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  change ZMod.finEquiv p i = (i : ZMod p)
  cases p with
  | zero =>
      exact (hp.out.ne_zero rfl).elim
  | succ n =>
      have hrefl : ZMod.finEquiv (n + 1) i = i := rfl
      rw [hrefl]
      exact (Fin.cast_val_eq_self i).symm

/-- The normalized Fourier matrix reindexed by `Fin p`.-/
noncomputable def normalizedFourierMatrixFin : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (zmodEquivFin (p := p)) (zmodEquivFin (p := p)) (normalizedFourierMatrix p)

/-- The raw Fourier matrix reindexed by `Fin p`.-/
noncomputable def fourierMatrixFin : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (zmodEquivFin (p := p)) (zmodEquivFin (p := p)) (fourierMatrix p)

/--
@isnad1 id=eq.0h1v.s5.559ed54f0046 from=translated src=- shape=4b756370 vocab=cff07ea8
-/
theorem normalizedFourierMatrixFin_eq_smul_fourierMatrixFin :
    normalizedFourierMatrixFin p = ((Real.sqrt p : ℂ)⁻¹) • fourierMatrixFin p := by
  ext i j
  simp [normalizedFourierMatrixFin, fourierMatrixFin, normalizedFourierMatrix_eq_smul_fourierMatrix]

/-- Reindexing does not change the determinant, so the `Fin p` model is a clean
stand-in for the original normalized Fourier matrix.
@isnad1 id=eq.0h1v.s5.8f1bc32e6444 from=translated src=- shape=15764c8c vocab=7d397439
-/
theorem det_normalizedFourierMatrix_eq_det_normalizedFourierMatrixFin :
    Matrix.det (normalizedFourierMatrix p) = Matrix.det (normalizedFourierMatrixFin p) := by
  rw [normalizedFourierMatrixFin,
    Matrix.det_reindex_self (zmodEquivFin (p := p)) (normalizedFourierMatrix p)]

end SignInvariant

end BernoulliRegular
