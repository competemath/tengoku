import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.MatrixMean
import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.OrderedSpectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compressions and shorted matrices

Compressions are represented by rectangular isometric matrices.
-/

namespace HiaiLimPowerMeans

open Matrix
open scoped ComplexOrder MatrixOrder Matrix

variable {n k 𝕜 : Type*}
  [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] [RCLike 𝕜]

/-- A rectangular matrix whose columns form an orthonormal family.-/
def MatrixIsometry (V : Matrix n k 𝕜) : Prop :=
  V.conjTranspose * V = 1

/-- Compression to the column space of `V`.-/
def compress (V : Matrix n k 𝕜) (A : Matrix n n 𝕜) : Matrix k k 𝕜 :=
  V.conjTranspose * A * V

/-- The shorted matrix on the column space of an isometry `V`.-/
noncomputable def shorted (V : Matrix n k 𝕜) (A : Matrix n n 𝕜) : Matrix k k 𝕜 :=
  (compress V A⁻¹)⁻¹

/-- Ando's positive-map inequality, specialized to finite-dimensional
isometric compressions and weighted geometric means.  This is Theorem 4 of
T. Ando, *Linear Algebra Appl.* 26 (1979), 203--241, applied to the
operator-concave function `x ↦ x^t`.

Its precise finite-matrix form is verified in the standalone module
`BoundaryProofs.AndoProof`.-/
def Ando (𝕜 : Type*) [RCLike 𝕜]
    (n k : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype k] [DecidableEq k] [Nonempty k] : Prop :=
  ∀ (V : Matrix n k 𝕜) (A B : Matrix n n 𝕜) (t : ℝ),
    MatrixIsometry V → A.PosDef → B.PosDef → 0 ≤ t → t ≤ 1 →
      compress V (weightedGeometricMean A B t) ≤
        weightedGeometricMean (compress V A) (compress V B) t

omit [DecidableEq n] in
theorem MatrixIsometry.mulVec_injective
    {V : Matrix n k 𝕜} (hV : MatrixIsometry V) :
    Function.Injective V.mulVec := by
  intro x y hxy
  change V.conjTranspose * V = 1 at hV
  have h := congrArg V.conjTranspose.mulVec hxy
  simpa only [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec] using h

omit [DecidableEq n] [Fintype k] in
/-- Compression by an isometry preserves positive definiteness.-/
theorem compress_posDef [Finite k]
    {V : Matrix n k 𝕜} (hV : MatrixIsometry V)
    {A : Matrix n n 𝕜} (hA : A.PosDef) : (compress V A).PosDef := by
  letI := Fintype.ofFinite k
  exact hA.conjTranspose_mul_mul_same hV.mulVec_injective

omit [DecidableEq n] [Fintype k] [DecidableEq k] in
/-- Compression preserves the Loewner order.-/
theorem compress_mono [Finite k]
    (V : Matrix n k 𝕜) {A B : Matrix n n 𝕜}
    (hAB : A ≤ B) : compress V A ≤ compress V B := by
  letI := Fintype.ofFinite k
  classical
  change (compress V B - compress V A).PosSemidef
  have hdiff : (B - A).PosSemidef := hAB
  have hcongr := hdiff.conjTranspose_mul_mul_same V
  have heq : V.conjTranspose * (B - A) * V =
      compress V B - compress V A := by
    ext i j
    simp [compress, Matrix.mul_apply, Finset.sum_sub_distrib, mul_sub, sub_mul]
  rw [heq] at hcongr
  exact hcongr

/-- Shorting a positive-definite matrix again gives a positive-definite
matrix.-/
theorem shorted_posDef {V : Matrix n k 𝕜} (hV : MatrixIsometry V)
    {A : Matrix n n 𝕜} (hA : A.PosDef) : (shorted V A).PosDef := by
  exact (compress_posDef hV hA.inv).inv

section BottomSpectralSubspace

variable {a b : ℕ}

/-- The order-preserving embedding of `Fin a` as the final `a` indices of
`Fin b`.  For a decreasing eigenvalue list, these are the `a` smallest
eigenvalues.-/
def bottomFinEmbedding (hab : a ≤ b) : Fin a ↪ Fin b where
  toFun i := ⟨b - a + i, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    simpa using congrArg Fin.val hij

/-- The isometry whose columns are eigenvectors for the `a` smallest
eigenvalues of a positive-definite `b × b` matrix.-/
noncomputable def bottomEigenvectorIsometry
    {A : Matrix (Fin b) (Fin b) 𝕜} (hA : A.PosDef) (hab : a ≤ b) :
    Matrix (Fin b) (Fin a) 𝕜 :=
  fun p i ↦ decreasingEigenvectorUnitary hA.isHermitian p
    (bottomFinEmbedding hab i)

theorem bottomEigenvectorIsometry_isometry
    {A : Matrix (Fin b) (Fin b) 𝕜} (hA : A.PosDef) (hab : a ≤ b) :
    MatrixIsometry (bottomEigenvectorIsometry hA hab) := by
  have hU := decreasingEigenvectorUnitary_isometry hA.isHermitian
  ext i j
  have hij := congrArg
    (fun M : Matrix (Fin b) (Fin b) 𝕜 ↦
      M (bottomFinEmbedding hab i) (bottomFinEmbedding hab j)) hU
  simpa [MatrixIsometry, bottomEigenvectorIsometry, Matrix.mul_apply,
    Matrix.one_apply] using hij

/-- The selected eigenvector isometry intertwines `A` with the diagonal
matrix of its selected (smallest) eigenvalues.-/
theorem mul_bottomEigenvectorIsometry
    {A : Matrix (Fin b) (Fin b) 𝕜} (hA : A.PosDef) (hab : a ≤ b) :
    A * bottomEigenvectorIsometry hA hab =
      bottomEigenvectorIsometry hA hab * Matrix.diagonal
        (fun i ↦ RCLike.ofReal
          (decreasingEigenvalues hA.isHermitian (bottomFinEmbedding hab i))) := by
  let U := decreasingEigenvectorUnitary hA.isHermitian
  have hU := mul_decreasingEigenvectorUnitary hA.isHermitian
  ext p i
  have hi := congrArg (fun M : Matrix (Fin b) (Fin b) 𝕜 ↦
    M p (bottomFinEmbedding hab i)) hU
  rw [Matrix.mul_diagonal] at hi
  rw [Matrix.mul_diagonal]
  simpa [bottomEigenvectorIsometry, U, Matrix.mul_apply] using hi

/-- Compression to the bottom spectral subspace is exactly diagonal with
the selected smallest eigenvalues.-/
private theorem compress_bottom_eq_diagonal
    {A : Matrix (Fin b) (Fin b) 𝕜} (hA : A.PosDef) (hab : a ≤ b) :
    compress (bottomEigenvectorIsometry hA hab) A =
      Matrix.diagonal
        (fun i ↦ RCLike.ofReal
          (decreasingEigenvalues hA.isHermitian (bottomFinEmbedding hab i))) := by
  let V := bottomEigenvectorIsometry hA hab
  let D : Matrix (Fin a) (Fin a) 𝕜 := Matrix.diagonal
    (fun i ↦ RCLike.ofReal
      (decreasingEigenvalues hA.isHermitian (bottomFinEmbedding hab i)))
  have hV : MatrixIsometry V := bottomEigenvectorIsometry_isometry hA hab
  have hrel : A * V = V * D := mul_bottomEigenvectorIsometry hA hab
  calc
    compress V A = V.conjTranspose * (A * V) := by
      simp [compress, Matrix.mul_assoc]
    _ = V.conjTranspose * (V * D) := by rw [hrel]
    _ = (V.conjTranspose * V) * D := by rw [Matrix.mul_assoc]
    _ = D := by rw [hV, Matrix.one_mul]
    _ = Matrix.diagonal
        (fun i ↦ RCLike.ofReal
          (decreasingEigenvalues hA.isHermitian (bottomFinEmbedding hab i))) := rfl

/-- On a reducing bottom spectral subspace, shorting and ordinary compression
coincide.  Both are the diagonal matrix of the selected smallest
eigenvalues.-/
private theorem shorted_bottom_eq_diagonal
    {A : Matrix (Fin b) (Fin b) 𝕜} (hA : A.PosDef) (hab : a ≤ b) :
    shorted (bottomEigenvectorIsometry hA hab) A =
      Matrix.diagonal
        (fun i ↦ RCLike.ofReal
          (decreasingEigenvalues hA.isHermitian (bottomFinEmbedding hab i))) := by
  let V := bottomEigenvectorIsometry hA hab
  let D : Matrix (Fin a) (Fin a) 𝕜 := Matrix.diagonal
    (fun i ↦ RCLike.ofReal
      (decreasingEigenvalues hA.isHermitian (bottomFinEmbedding hab i)))
  have hV : MatrixIsometry V := bottomEigenvectorIsometry_isometry hA hab
  have hrel : A * V = V * D := mul_bottomEigenvectorIsometry hA hab
  have hD : D.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    simpa [D] using Matrix.PosDef.decreasingEigenvalues_pos hA
      (bottomFinEmbedding hab i)
  letI : Invertible A := hA.isUnit.invertible
  letI : Invertible D := hD.isUnit.invertible
  have hInvRel : A⁻¹ * V = V * D⁻¹ := by
    apply (Matrix.inv_mul_eq_iff_eq_mul_of_invertible A V (V * D⁻¹)).2
    calc
      V = V * (1 : Matrix (Fin a) (Fin a) 𝕜) := (Matrix.mul_one V).symm
      _ = V * (D * D⁻¹) := by rw [Matrix.mul_inv_of_invertible]
      _ = (V * D) * D⁻¹ := by rw [Matrix.mul_assoc]
      _ = (A * V) * D⁻¹ := by rw [hrel]
      _ = A * (V * D⁻¹) := by rw [Matrix.mul_assoc]
  have hcompressInv : compress V A⁻¹ = D⁻¹ := by
    calc
      compress V A⁻¹ = V.conjTranspose * (A⁻¹ * V) := by
        simp [compress, Matrix.mul_assoc]
      _ = V.conjTranspose * (V * D⁻¹) := by rw [hInvRel]
      _ = (V.conjTranspose * V) * D⁻¹ := by rw [Matrix.mul_assoc]
      _ = D⁻¹ := by rw [hV, Matrix.one_mul]
  rw [shorted, hcompressInv, Matrix.inv_inv_of_invertible]

/-- On the bottom spectral subspace, shorting agrees with compression, and
its determinant is the product of the selected smallest eigenvalues.-/
theorem shorted_bottomEigenvectors
    {A : Matrix (Fin b) (Fin b) 𝕜} (hA : A.PosDef) (hab : a ≤ b) :
    shorted (bottomEigenvectorIsometry hA hab) A =
        compress (bottomEigenvectorIsometry hA hab) A ∧
      RCLike.re (shorted (bottomEigenvectorIsometry hA hab) A).det =
        ∏ i, decreasingEigenvalues hA.isHermitian
          (bottomFinEmbedding hab i) := by
  constructor
  · rw [shorted_bottom_eq_diagonal hA hab,
      compress_bottom_eq_diagonal hA hab]
  · rw [shorted_bottom_eq_diagonal hA hab, Matrix.det_diagonal]
    rw [← RCLike.ofReal_prod]
    exact RCLike.ofReal_re _

end BottomSpectralSubspace

section Complex

variable [Nonempty n] [Nonempty k]

open scoped Matrix.Norms.L2Operator

/- The inverse-order theorem uses the standard C⋆-algebra structure on complex
matrices. -/
noncomputable local instance : CStarAlgebra (Matrix k k ℂ) where

omit [Nonempty n] [Nonempty k] in
/-- Variational characterization of the shorted matrix: it is feasible, and
it dominates every positive-definite feasible matrix.-/
theorem shorted_variational
    {V : Matrix n k ℂ} (hV : MatrixIsometry V)
    {A : Matrix n n ℂ} (hA : A.PosDef) :
    (A - V * shorted V A * V.conjTranspose).PosSemidef ∧
      ∀ {C : Matrix k k ℂ}, C.PosDef →
        (A - V * C * V.conjTranspose).PosSemidef → C ≤ shorted V A := by
  constructor
  · let H : Matrix k k ℂ := compress V A⁻¹
    have hH : H.PosDef := compress_posDef hV hA.inv
    letI : Invertible A := hA.isUnit.invertible
    letI : Invertible H := hH.isUnit.invertible
    have hzero : (H - V.conjTranspose * A⁻¹ * V).PosSemidef := by
      have heq : H - V.conjTranspose * A⁻¹ * V = 0 := by
        simp [H, compress]
      rw [heq]
      exact Matrix.PosSemidef.zero
    have hblock : (Matrix.fromBlocks A V V.conjTranspose H).PosSemidef :=
      (Matrix.PosDef.fromBlocks₁₁ V H hA).2 hzero
    have hout := (Matrix.PosDef.fromBlocks₂₂ A V hH).1 hblock
    simpa [shorted, H] using hout
  · intro C hC hres
    let H : Matrix k k ℂ := compress V A⁻¹
    have hH : H.PosDef := compress_posDef hV hA.inv
    letI : Invertible A := hA.isUnit.invertible
    letI : Invertible C := hC.isUnit.invertible
    letI : Invertible C⁻¹ := hC.inv.isUnit.invertible
    have hblock :
        (Matrix.fromBlocks A V V.conjTranspose C⁻¹).PosSemidef := by
      apply (Matrix.PosDef.fromBlocks₂₂ A V hC.inv).2
      simpa using hres
    have hschur :
        (C⁻¹ - V.conjTranspose * A⁻¹ * V).PosSemidef :=
      (Matrix.PosDef.fromBlocks₁₁ V C⁻¹ hA).1 hblock
    have hHCinv : H ≤ C⁻¹ := by
      change (C⁻¹ - H).PosSemidef
      simpa [H, compress] using hschur
    have hinv :=
      CStarAlgebra.ringInverse_le_ringInverse hHCinv hH.isStrictlyPositive
    simpa [shorted, H, Ring.inverse_of_isUnit hH.isUnit,
      Ring.inverse_of_isUnit hC.inv.isUnit] using hinv

/-- Ando compression, self-duality of the weighted geometric mean, and
order reversal under inversion give the geometric-mean inequality for
shorted matrices.-/
theorem weightedGeometricMean_shorted_le
    (hAndo : Ando ℂ n k)
    {V : Matrix n k ℂ} (hV : MatrixIsometry V)
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    weightedGeometricMean (shorted V A) (shorted V B) t ≤
      shorted V (weightedGeometricMean A B t) := by
  let HA : Matrix k k ℂ := compress V A⁻¹
  let HB : Matrix k k ℂ := compress V B⁻¹
  let L : Matrix k k ℂ :=
    compress V (weightedGeometricMean A⁻¹ B⁻¹ t)
  let R : Matrix k k ℂ := weightedGeometricMean HA HB t
  have hHA : HA.PosDef := compress_posDef hV hA.inv
  have hHB : HB.PosDef := compress_posDef hV hB.inv
  have hL : L.PosDef :=
    compress_posDef hV (weightedGeometricMean_posDef hA.inv hB.inv t)
  have hR : R.PosDef := weightedGeometricMean_posDef hHA hHB t
  have hLR : L ≤ R := by
    simpa [L, R, HA, HB] using hAndo V A⁻¹ B⁻¹ t hV hA.inv hB.inv ht0 ht1
  letI : Invertible L := hL.isUnit.invertible
  letI : Invertible R := hR.isUnit.invertible
  have hinv : R⁻¹ ≤ L⁻¹ := by
    have h := CStarAlgebra.ringInverse_le_ringInverse hLR hL.isStrictlyPositive
    simpa [Ring.inverse_of_isUnit hR.isUnit,
      Ring.inverse_of_isUnit hL.isUnit] using h
  calc
    weightedGeometricMean (shorted V A) (shorted V B) t =
        weightedGeometricMean HA⁻¹ HB⁻¹ t := by rfl
    _ = R⁻¹ := by
      rw [weightedGeometricMean_inv hHA hHB t]
    _ ≤ L⁻¹ := hinv
    _ = shorted V (weightedGeometricMean A B t) := by
      rw [shorted, weightedGeometricMean_inv hA hB t]

omit [Nonempty n] [Nonempty k] in
/-- Shorting is superadditive for finite positive weighted sums.  This is the
finite-matrix form needed after compressing the Lim--Pálfia fixed-point
equation.-/
theorem shorted_superadditive
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {V : Matrix n k ℂ} (hV : MatrixIsometry V)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j)
    (A : ι → Matrix n n ℂ) (hA : ∀ j, (A j).PosDef) :
    (∑ j, w j • shorted V (A j)) ≤
      shorted V (∑ j, w j • A j) := by
  let Asum : Matrix n n ℂ := ∑ j, w j • A j
  let Csum : Matrix k k ℂ := ∑ j, w j • shorted V (A j)
  have hAsum : Asum.PosDef := by
    apply Matrix.posDef_sum Finset.univ_nonempty
    intro j _
    exact (hA j).smul (hw j)
  have hCsum : Csum.PosDef := by
    apply Matrix.posDef_sum Finset.univ_nonempty
    intro j _
    exact (shorted_posDef hV (hA j)).smul (hw j)
  have hresEach (j : ι) :
      (w j • (A j - V * shorted V (A j) * V.conjTranspose)).PosSemidef :=
    (shorted_variational hV (hA j)).1.smul (hw j).le
  have hresSum :
      (∑ j, w j •
        (A j - V * shorted V (A j) * V.conjTranspose)).PosSemidef := by
    simpa using Matrix.posSemidef_sum Finset.univ
      (fun j _ ↦ hresEach j)
  have heq :
      Asum - V * Csum * V.conjTranspose =
        ∑ j, w j •
          (A j - V * shorted V (A j) * V.conjTranspose) := by
    dsimp [Asum, Csum]
    rw [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact (smul_sub (w j) (A j)
      (V * shorted V (A j) * V.conjTranspose)).symm
  apply (shorted_variational hV hAsum).2 hCsum
  rw [heq]
  exact hresSum

end Complex

end HiaiLimPowerMeans
