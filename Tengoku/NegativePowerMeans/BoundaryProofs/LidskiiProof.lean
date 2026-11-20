import Tengoku.NegativePowerMeans.BoundaryProofs.SpectralSubspaces
import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.LidskiiMathlib
import Tengoku.Seed.Analysis.InnerProductSpace.NormDet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The nondegenerate selected-index Gel'fand--Naimark inequality

This file proves the selected-index singular-value product inequality of
Gel'fand and Naimark for injective square factors, in the form needed for
multiplicative Lidskii.  It follows the factorization in Hiai, Theorem 1.12,
equation (1.9).  The factors in the Lidskii reduction are positive definite,
so this nondegenerate form proves the complete `Lidskii` statement without a
singular regularization argument.
-/

namespace HiaiLimPowerMeans

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- A scaled comparison of quadratic forms compares the ordered spectra by
the same factor.  The proof is the same finite-dimensional intersection
argument as Weyl monotonicity, with the scalar retained.
@isnad1 id=le.4h6v.s7.07d143557e7c from=translated src=- shape=33ed3ab2 vocab=46707a0c
-/
theorem decreasingEigenvalues_le_of_quadratic_le
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (c : ℝ) (hc : 0 ≤ c)
    (hquad : ∀ v : Fin n → 𝕜,
      realQuadraticForm A v ≤ c * realQuadraticForm B v)
    (i : Fin n) :
    decreasingEigenvalues hA i ≤ c * decreasingEigenvalues hB i := by
  obtain ⟨x, y, hx0, _hy0, hxy⟩ :=
    spectral_subspaces_intersect hA hB i
  let VA := spectralIsometry hA (topFinEmbeddingAt i)
  let VB := spectralIsometry hB (bottomFinEmbeddingAt i)
  let v : EuclideanSpace 𝕜 (Fin n) := Matrix.toEuclideanLin VA x
  have hxyRaw : VA.mulVec x.ofLp = VB.mulVec y.ofLp := by
    have h := congrArg WithLp.ofLp hxy
    simpa [VA, VB, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using h
  have hnormVA : ‖x‖ = ‖v‖ := by
    exact (norm_toEuclideanLin_of_isometry
      (spectralIsometry_isometry hA (topFinEmbeddingAt i)) x).symm
  have hnormVB : ‖y‖ = ‖v‖ := by
    have heqv : Matrix.toEuclideanLin VB y = v := hxy.symm
    rw [← heqv]
    exact (norm_toEuclideanLin_of_isometry
      (spectralIsometry_isometry hB (bottomFinEmbeddingAt i)) y).symm
  have hchain : decreasingEigenvalues hA i * ‖v‖ ^ 2 ≤
      (c * decreasingEigenvalues hB i) * ‖v‖ ^ 2 := by
    calc
      decreasingEigenvalues hA i * ‖v‖ ^ 2 =
          decreasingEigenvalues hA i * ‖x‖ ^ 2 := by rw [hnormVA]
      _ ≤ realQuadraticForm A (VA.mulVec x.ofLp) :=
        top_spectral_quadratic_lower hA i x
      _ ≤ c * realQuadraticForm B (VA.mulVec x.ofLp) := hquad _
      _ = c * realQuadraticForm B (VB.mulVec y.ofLp) := by rw [hxyRaw]
      _ ≤ c * (decreasingEigenvalues hB i * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (bottom_spectral_quadratic_upper hB i y) hc
      _ = (c * decreasingEigenvalues hB i) * ‖v‖ ^ 2 := by
        rw [hnormVB]
        ring
  have hv0 : 0 < ‖v‖ ^ 2 := by
    have hvne : v ≠ 0 := by
      intro hv
      have hx : x = 0 :=
        (toEuclideanLin_injective_of_isometry
          (spectralIsometry_isometry hA (topFinEmbeddingAt i)))
          (by simpa [v] using hv)
      exact hx0 hx
    positivity
  exact le_of_mul_le_mul_right hchain hv0

/-- **Weyl monotonicity** for the decreasingly ordered eigenvalues of
Hermitian matrices.  This is derived here from the spectral theorem and a
finite-dimensional intersection argument.
@isnad1 id=le.3h5v.s7.837aa87839a1 from=translated src=- shape=f84534ae vocab=80d8a546
-/
theorem decreasingEigenvalues_mono
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B)
    (i : Fin n) :
    decreasingEigenvalues hA i ≤ decreasingEigenvalues hB i := by
  obtain ⟨x, y, hx0, _hy0, hxy⟩ :=
    spectral_subspaces_intersect hA hB i
  let VA := spectralIsometry hA (topFinEmbeddingAt i)
  let VB := spectralIsometry hB (bottomFinEmbeddingAt i)
  let v : EuclideanSpace 𝕜 (Fin n) := Matrix.toEuclideanLin VA x
  have hxyRaw : VA.mulVec x.ofLp = VB.mulVec y.ofLp := by
    have h := congrArg WithLp.ofLp hxy
    simpa [VA, VB, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using h
  have hnormVA : ‖x‖ = ‖v‖ := by
    exact (norm_toEuclideanLin_of_isometry
      (spectralIsometry_isometry hA (topFinEmbeddingAt i)) x).symm
  have hnormVB : ‖y‖ = ‖v‖ := by
    have heqv : Matrix.toEuclideanLin VB y = v := hxy.symm
    rw [← heqv]
    exact (norm_toEuclideanLin_of_isometry
      (spectralIsometry_isometry hB (bottomFinEmbeddingAt i)) y).symm
  have hchain : decreasingEigenvalues hA i * ‖v‖ ^ 2 ≤
      decreasingEigenvalues hB i * ‖v‖ ^ 2 := by
    calc
      decreasingEigenvalues hA i * ‖v‖ ^ 2 =
          decreasingEigenvalues hA i * ‖x‖ ^ 2 := by rw [hnormVA]
      _ ≤ realQuadraticForm A (VA.mulVec x.ofLp) :=
        top_spectral_quadratic_lower hA i x
      _ ≤ realQuadraticForm B (VA.mulVec x.ofLp) :=
        realQuadraticForm_mono hAB _
      _ = realQuadraticForm B (VB.mulVec y.ofLp) := by rw [hxyRaw]
      _ ≤ decreasingEigenvalues hB i * ‖y‖ ^ 2 :=
        bottom_spectral_quadratic_upper hB i y
      _ = decreasingEigenvalues hB i * ‖v‖ ^ 2 := by rw [hnormVB]
  have hv0 : 0 < ‖v‖ ^ 2 := by
    have hvne : v ≠ 0 := by
      intro hv
      have hx : x = 0 :=
        (toEuclideanLin_injective_of_isometry
          (spectralIsometry_isometry hA (topFinEmbeddingAt i)))
          (by simpa [v] using hv)
      exact hx0 hx
    positivity
  exact le_of_mul_le_mul_right hchain hv0

/-- The Gram quadratic form of a product is the Gram quadratic form of the
left factor evaluated on the image under the right factor.
@isnad1 id=eq.0h5v.s8.b34765b1a243 from=translated src=- shape=be0bdc72 vocab=5235a384
-/
theorem realQuadraticForm_gram_mul
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (Y Z : Matrix (Fin n) (Fin n) 𝕜) (x : Fin n → 𝕜) :
    realQuadraticForm ((Y * Z).conjTranspose * (Y * Z)) x =
      realQuadraticForm (Y.conjTranspose * Y) (Z.mulVec x) := by
  have hgram : (Y * Z).conjTranspose * (Y * Z) =
      compress Z (Y.conjTranspose * Y) := by
    simp only [Matrix.conjTranspose_mul, compress]
    noncomm_ring
  rw [hgram]
  exact (realQuadraticForm_mulVec Z (Y.conjTranspose * Y) x).symm

/-- The Gram quadratic form is the squared norm after applying the matrix.
@isnad1 id=eq.0h5v.s7.f3d98dc2c4c9 from=translated src=- shape=bcbc4543 vocab=5235a384
-/
theorem realQuadraticForm_gram
    {m n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (Z : Matrix (Fin m) (Fin n) 𝕜) (x : Fin n → 𝕜) :
    realQuadraticForm (Z.conjTranspose * Z) x =
      realQuadraticForm (1 : Matrix (Fin m) (Fin m) 𝕜) (Z.mulVec x) := by
  have hcomp : compress Z (1 : Matrix (Fin m) (Fin m) 𝕜) =
      Z.conjTranspose * Z := by simp [compress]
  rw [← hcomp]
  exact (realQuadraticForm_mulVec Z 1 x).symm

/-- The singular values of a matrix product are bounded by a uniform Gram
bound for the left factor.  This is the singular-value ideal property in the
precise form needed in Hiai's factorization proof.
@isnad1 id=le.2h6v.s13.944d4796ceb4 from=translated src=- shape=2ec902db vocab=0364f8e4
-/
theorem singularValues_mul_le_of_gram_le
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (Y Z : Matrix (Fin n) (Fin n) 𝕜) (c : ℝ) (hc : 0 ≤ c)
    (hY : Y.conjTranspose * Y ≤
      Matrix.scalar (Fin n) (RCLike.ofReal (c ^ 2)))
    (i : Fin n) :
    (Matrix.toEuclideanLin (Y * Z)).singularValues i ≤
      c * (Matrix.toEuclideanLin Z).singularValues i := by
  let GYZ := (Y * Z).conjTranspose * (Y * Z)
  let GZ := Z.conjTranspose * Z
  have hquad : ∀ x : Fin n → 𝕜,
      realQuadraticForm GYZ x ≤ c ^ 2 * realQuadraticForm GZ x := by
    intro x
    calc
      realQuadraticForm GYZ x =
          realQuadraticForm (Y.conjTranspose * Y) (Z.mulVec x) := by
        exact realQuadraticForm_gram_mul Y Z x
      _ ≤ realQuadraticForm
          (Matrix.scalar (Fin n) (RCLike.ofReal (c ^ 2)))
          (Z.mulVec x) := realQuadraticForm_mono hY _
      _ = c ^ 2 * realQuadraticForm
          (1 : Matrix (Fin n) (Fin n) 𝕜) (Z.mulVec x) :=
        realQuadraticForm_scalar _ _
      _ = c ^ 2 * realQuadraticForm GZ x := by
        rw [realQuadraticForm_gram]
  have heig : decreasingEigenvalues
      (Matrix.isHermitian_conjTranspose_mul_self (Y * Z)) i ≤
      c ^ 2 * decreasingEigenvalues
        (Matrix.isHermitian_conjTranspose_mul_self Z) i := by
    exact decreasingEigenvalues_le_of_quadratic_le
      (Matrix.isHermitian_conjTranspose_mul_self (Y * Z))
      (Matrix.isHermitian_conjTranspose_mul_self Z) (c ^ 2) (sq_nonneg c)
      hquad i
  have hleft := singularValues_sq_eq_decreasingEigenvalues_gram (Y * Z) i
  have hright := singularValues_sq_eq_decreasingEigenvalues_gram Z i
  rw [← hleft, ← hright] at heig
  have hsq : (Matrix.toEuclideanLin (Y * Z)).singularValues i ^ 2 ≤
      (c * (Matrix.toEuclideanLin Z).singularValues i) ^ 2 := by
    simpa [mul_pow] using heig
  exact (sq_le_sq₀
    (LinearMap.singularValues_nonneg (Matrix.toEuclideanLin (Y * Z)) i)
    (mul_nonneg hc
      (LinearMap.singularValues_nonneg (Matrix.toEuclideanLin Z) i))).mp hsq

/-- If `XᴴX ≥ I`, left multiplication by `X` cannot decrease any singular
value.
@isnad1 id=le.1h5v.s13.c16684dcb288 from=translated src=- shape=6e388714 vocab=b112cd3d
-/
theorem singularValues_le_mul_of_one_le_gram
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (X T : Matrix (Fin n) (Fin n) 𝕜)
    (hX : (1 : Matrix (Fin n) (Fin n) 𝕜) ≤ X.conjTranspose * X)
    (i : Fin n) :
    (Matrix.toEuclideanLin T).singularValues i ≤
      (Matrix.toEuclideanLin (X * T)).singularValues i := by
  have hgram : T.conjTranspose * T ≤
      (X * T).conjTranspose * (X * T) := by
    have h := compress_mono T hX
    simpa only [compress, Matrix.conjTranspose_mul, Matrix.one_mul,
      Matrix.mul_assoc] using h
  have heig := decreasingEigenvalues_mono
    (Matrix.isHermitian_conjTranspose_mul_self T)
    (Matrix.isHermitian_conjTranspose_mul_self (X * T)) hgram i
  have hleft := singularValues_sq_eq_decreasingEigenvalues_gram T i
  have hright := singularValues_sq_eq_decreasingEigenvalues_gram (X * T) i
  rw [← hleft, ← hright] at heig
  exact (sq_le_sq₀
    (LinearMap.singularValues_nonneg (Matrix.toEuclideanLin T) i)
    (LinearMap.singularValues_nonneg (Matrix.toEuclideanLin (X * T)) i)).mp
      heig

/-- For an endomorphism of `n`-dimensional Euclidean space, the product of
its `n` singular values is its norm determinant.
@isnad1 id=eq.0h3v.s9.3b6ea6a551d0 from=translated src=- shape=70da37e6 vocab=5489f12b
-/
theorem prod_singularValues_eq_normDet
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (T : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜]
      EuclideanSpace 𝕜 (Fin n)) :
    (∏ i : Fin n, T.singularValues i) = T.normDet := by
  rw [LinearMap.normDet_eq_prod_singularValues]
  simpa using Fin.prod_univ_eq_prod_range T.singularValues n

/-- Norm determinant is multiplicative for endomorphisms.
@isnad1 id=eq.0h4v.s8.32a45408a68d from=translated src=- shape=d7f6613c vocab=60f13598
-/
theorem normDet_comp
    {E : Type*} {𝕜 : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (S T : E →ₗ[𝕜] E) :
    (S.comp T).normDet = S.normDet * T.normDet := by
  rw [LinearMap.normDet_eq_norm_det, LinearMap.normDet_eq_norm_det,
    LinearMap.normDet_eq_norm_det, LinearMap.det_comp, norm_mul]

/-- A product over an embedded subset is bounded by the full product when
all factors are at least one.
@isnad1 id=le.1h4v.s6.68cf3e9bc34f from=translated src=- shape=10422cb2 vocab=30d9c200
-/
theorem prod_embedding_le_prod
    {n k : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 1 ≤ f i)
    (e : Fin k ↪ Fin n) :
    (∏ j, f (e j)) ≤ ∏ i, f i := by
  let s : Finset (Fin n) := Finset.univ.map e
  have hsubset : s ⊆ Finset.univ := Finset.subset_univ s
  have hprod := Finset.prod_le_prod_of_subset_of_one_le hsubset
    (fun i _ ↦ le_trans (by norm_num) (hf i))
    (fun i _ _ ↦ hf i)
  simpa [s] using hprod

/-- For an expanding left factor `X` and an injective right factor `T`, the
product of any selected singular values grows by at most the total volume
factor `normDet X`.
@isnad1 id=le.2h6v.s14.8c5c09f3afcb from=translated src=- shape=8ef74b0a vocab=5b290202
-/
theorem expanding_selected_product_of_injective
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (X T : Matrix (Fin n) (Fin n) 𝕜)
    (hX : (1 : Matrix (Fin n) (Fin n) 𝕜) ≤ X.conjTranspose * X)
    (hT : Function.Injective (Matrix.toEuclideanLin T))
    (indices : Fin k ↪ Fin n) :
    (∏ j, (Matrix.toEuclideanLin (X * T)).singularValues (indices j)) ≤
      (Matrix.toEuclideanLin X).normDet *
        ∏ j, (Matrix.toEuclideanLin T).singularValues (indices j) := by
  let LX := Matrix.toEuclideanLin X
  let LT := Matrix.toEuclideanLin T
  let LXT := Matrix.toEuclideanLin (X * T)
  let ratio : Fin n → ℝ := fun i ↦
    LXT.singularValues i / LT.singularValues i
  have hTpos : ∀ i : Fin n, 0 < LT.singularValues i := by
    intro i
    have hall :=
      (LinearMap.injective_iff_forall_lt_finrank_singularValues_pos LT).mp hT
    exact hall i (by simp)
  have hmono : ∀ i : Fin n,
      LT.singularValues i ≤ LXT.singularValues i := by
    intro i
    exact singularValues_le_mul_of_one_le_gram X T hX i
  have hratio : ∀ i : Fin n, 1 ≤ ratio i := by
    intro i
    exact (le_div_iff₀ (hTpos i)).2 (by simpa using hmono i)
  have hselected : (∏ j, ratio (indices j)) ≤ ∏ i, ratio i :=
    prod_embedding_le_prod ratio hratio indices
  have hTprod : 0 < ∏ i : Fin n, LT.singularValues i :=
    Finset.prod_pos fun i _ ↦ hTpos i
  have hcomp : LXT = LX.comp LT := by
    simp [LX, LT, LXT]
  have hfull : (∏ i : Fin n, ratio i) = LX.normDet := by
    rw [show (∏ i : Fin n, ratio i) =
        (∏ i : Fin n, LXT.singularValues i) /
          ∏ i : Fin n, LT.singularValues i by
      simp [ratio, Finset.prod_div_distrib]]
    rw [prod_singularValues_eq_normDet,
      prod_singularValues_eq_normDet, hcomp, normDet_comp]
    have hTnorm : LT.normDet ≠ 0 := by
      rw [← prod_singularValues_eq_normDet]
      exact hTprod.ne'
    exact mul_div_cancel_right₀ LX.normDet hTnorm
  have hfactor : (∏ j : Fin k, LXT.singularValues (indices j)) =
      (∏ j : Fin k, ratio (indices j)) *
        ∏ j : Fin k, LT.singularValues (indices j) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    dsimp [ratio]
    field_simp [(hTpos (indices j)).ne']
  rw [hfactor]
  exact mul_le_mul_of_nonneg_right (hfull ▸ hselected)
    (Finset.prod_nonneg fun j _ ↦
      LinearMap.singularValues_nonneg LT (indices j))

/-- Hiai's factorization reduces the selected-product inequality to the two
spectral estimates proved above.
@isnad1 id=le.6h9v.s14.721f8bdc9814 from=translated src=- shape=74b61b0c vocab=6dee6ff8
-/
theorem selected_product_of_factorization
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S T X Y : Matrix (Fin n) (Fin n) 𝕜) (c : ℝ) (hc : 0 ≤ c)
    (hfactor : S = Y * X)
    (hY : Y.conjTranspose * Y ≤
      Matrix.scalar (Fin n) (RCLike.ofReal (c ^ 2)))
    (hX : (1 : Matrix (Fin n) (Fin n) 𝕜) ≤ X.conjTranspose * X)
    (hvolume : c ^ k * (Matrix.toEuclideanLin X).normDet =
      ∏ j : Fin k, (Matrix.toEuclideanLin S).singularValues j)
    (hT : Function.Injective (Matrix.toEuclideanLin T))
    (indices : Fin k ↪ Fin n) :
    (∏ j, (Matrix.toEuclideanLin (S * T)).singularValues (indices j)) ≤
      (∏ j : Fin k, (Matrix.toEuclideanLin S).singularValues j) *
        ∏ j, (Matrix.toEuclideanLin T).singularValues (indices j) := by
  have hideal : ∀ j : Fin k,
      (Matrix.toEuclideanLin (S * T)).singularValues (indices j) ≤
        c * (Matrix.toEuclideanLin (X * T)).singularValues (indices j) := by
    intro j
    have hmat : S * T = Y * (X * T) := by rw [hfactor, Matrix.mul_assoc]
    rw [hmat]
    exact singularValues_mul_le_of_gram_le Y (X * T) c hc hY (indices j)
  have hfirst :
      (∏ j, (Matrix.toEuclideanLin (S * T)).singularValues (indices j)) ≤
        c ^ k *
          ∏ j, (Matrix.toEuclideanLin (X * T)).singularValues (indices j) := by
    calc
      (∏ j, (Matrix.toEuclideanLin (S * T)).singularValues (indices j)) ≤
          ∏ j, (c *
            (Matrix.toEuclideanLin (X * T)).singularValues (indices j)) := by
        exact Finset.prod_le_prod
          (fun j _ ↦ LinearMap.singularValues_nonneg _ _) (fun j _ ↦ hideal j)
      _ = c ^ k *
          ∏ j, (Matrix.toEuclideanLin (X * T)).singularValues (indices j) := by
        calc
          (∏ j : Fin k, c *
              (Matrix.toEuclideanLin (X * T)).singularValues (indices j)) =
              (∏ _j : Fin k, c) *
                ∏ j, (Matrix.toEuclideanLin (X * T)).singularValues
                  (indices j) := by
            simpa using (Finset.prod_mul_distrib
              (s := (Finset.univ : Finset (Fin k)))
              (f := fun _j : Fin k ↦ c)
              (g := fun j : Fin k ↦
                (Matrix.toEuclideanLin (X * T)).singularValues (indices j)))
          _ = c ^ k *
                ∏ j, (Matrix.toEuclideanLin (X * T)).singularValues
                  (indices j) := by simp
  have hexpand := expanding_selected_product_of_injective X T hX hT indices
  calc
    (∏ j, (Matrix.toEuclideanLin (S * T)).singularValues (indices j)) ≤
        c ^ k *
          ∏ j, (Matrix.toEuclideanLin (X * T)).singularValues (indices j) :=
      hfirst
    _ ≤ c ^ k * ((Matrix.toEuclideanLin X).normDet *
        ∏ j, (Matrix.toEuclideanLin T).singularValues (indices j)) :=
      mul_le_mul_of_nonneg_left hexpand (pow_nonneg hc k)
    _ = (∏ j : Fin k,
          (Matrix.toEuclideanLin S).singularValues j) *
        ∏ j, (Matrix.toEuclideanLin T).singularValues (indices j) := by
      rw [← hvolume]
      ring

/-- The index of the `k`th singular value in zero-based notation.-/
def kthIndex {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) : Fin n :=
  ⟨k - 1, by omega⟩

/-- The diagonal scale in Hiai's factorization: divide the first `k`
singular values by the `k`th one and leave the remaining coordinates fixed.-/
noncomputable def hiaiScale
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n) (i : Fin n) : ℝ :=
  if i.val < k then
    (Matrix.toEuclideanLin S).singularValues i /
      (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn)
  else 1

/--
@isnad1 id=eq.3h5v.s13.23e83b365dcc from=translated src=- shape=f432c748 vocab=2f3c2e01
-/
theorem hiaiScale_eq_of_lt
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n) (i : Fin n) (hi : i.val < k) :
    hiaiScale S hk hkn i =
      (Matrix.toEuclideanLin S).singularValues i /
        (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn) := by
  simp [hiaiScale, hi]

/--
@isnad1 id=eq.3h5v.s5.e41e8d65c374 from=translated src=- shape=bdc4468f vocab=8ca0c410
-/
theorem hiaiScale_eq_one_of_le
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n) (i : Fin n) (hi : k ≤ i.val) :
    hiaiScale S hk hkn i = 1 := by
  simp [hiaiScale, not_lt.mpr hi]

/--
@isnad1 id=le.3h5v.s12.4508593b0bee from=translated src=- shape=018499ad vocab=bf353070
-/
theorem hiaiScale_one_le
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n)
    (ha : 0 < (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn))
    (i : Fin n) :
    1 ≤ hiaiScale S hk hkn i := by
  by_cases hi : i.val < k
  · rw [hiaiScale_eq_of_lt S hk hkn i hi]
    apply (le_div_iff₀ ha).2
    simpa using (LinearMap.singularValues_antitone
      (Matrix.toEuclideanLin S) (show i.val ≤ (kthIndex hk hkn).val by
        change i.val ≤ k - 1
        omega))
  · rw [hiaiScale_eq_one_of_le S hk hkn i (not_lt.mp hi)]

/--
@isnad1 id=lt.3h5v.s12.a14f807be904 from=translated src=- shape=c06844c1 vocab=bf353070
-/
theorem hiaiScale_pos
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n)
    (ha : 0 < (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn))
    (i : Fin n) :
    0 < hiaiScale S hk hkn i :=
  lt_of_lt_of_le zero_lt_one (hiaiScale_one_le S hk hkn ha i)

/--
@isnad1 id=antitone.3h4v.s12.35e83919643a from=translated src=- shape=be73b267 vocab=54cc3161
-/
theorem hiaiScale_antitone
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n)
    (ha : 0 < (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn)) :
    Antitone (hiaiScale S hk hkn) := by
  intro i j hij
  by_cases hj : j.val < k
  · have hi : i.val < k := lt_of_le_of_lt hij hj
    rw [hiaiScale_eq_of_lt S hk hkn i hi,
      hiaiScale_eq_of_lt S hk hkn j hj]
    exact div_le_div_of_nonneg_right
      (LinearMap.singularValues_antitone _ hij) ha.le
  · rw [hiaiScale_eq_one_of_le S hk hkn j (not_lt.mp hj)]
    exact hiaiScale_one_le S hk hkn ha i

/-- The squared Hiai scale remains decreasing.
@isnad1 id=antitone.3h4v.s12.95f9ea377bbc from=translated src=- shape=b074841a vocab=3c17dcef
-/
theorem hiaiScale_sq_antitone
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n)
    (ha : 0 < (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn)) :
    Antitone (fun i ↦ hiaiScale S hk hkn i ^ 2) := by
  intro i j hij
  exact pow_le_pow_left₀ (hiaiScale_pos S hk hkn ha j).le
    (hiaiScale_antitone S hk hkn ha hij) 2

/-- After conjugation by the inverse Hiai scale, every eigenvalue of the
Gram matrix is at most the square of the `k`th singular value.
@isnad1 id=le.3h5v.s13.9217c6787863 from=translated src=- shape=e42bab76 vocab=30c0d0ac
-/
theorem gramEigenvalue_div_hiaiScale_sq_le
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n)
    (ha : 0 < (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn))
    (i : Fin n) :
    decreasingEigenvalues
        (Matrix.isHermitian_conjTranspose_mul_self S) i /
          hiaiScale S hk hkn i ^ 2 ≤
      (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn) ^ 2 := by
  let a := (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn)
  let s := (Matrix.toEuclideanLin S).singularValues i
  have heig := singularValues_sq_eq_decreasingEigenvalues_gram S i
  by_cases hi : i.val < k
  · rw [← heig, hiaiScale_eq_of_lt S hk hkn i hi]
    change s ^ 2 / (s / a) ^ 2 ≤ a ^ 2
    have hai : a ≤ s := by
      exact LinearMap.singularValues_antitone (Matrix.toEuclideanLin S) <| by
        change i.val ≤ k - 1
        omega
    have hsi : 0 < s := lt_of_lt_of_le ha hai
    have hsne : s ≠ 0 := hsi.ne'
    have hane : a ≠ 0 := ha.ne'
    field_simp [hsne, hane]
    exact le_rfl
  · rw [← heig, hiaiScale_eq_one_of_le S hk hkn i (not_lt.mp hi)]
    simp only [one_pow, div_one]
    have hsi : s ≤ a := by
      exact LinearMap.singularValues_antitone (Matrix.toEuclideanLin S) <| by
        change k - 1 ≤ i.val
        omega
    exact pow_le_pow_left₀ (LinearMap.singularValues_nonneg _ _) hsi 2

/-- The determinant factor represented by the Hiai scale gives exactly the
product of the first `k` singular values after multiplication by the `k`th
singular value to the power `k`.
@isnad1 id=eq.3h4v.s13.85b245362143 from=translated src=- shape=d2e30a4a vocab=b87d5ec2
-/
theorem hiaiScale_volume_identity
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n)
    (ha : 0 < (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn)) :
    (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn) ^ k *
        (∏ i : Fin n, hiaiScale S hk hkn i) =
      ∏ j : Fin k, (Matrix.toEuclideanLin S).singularValues j := by
  let e : Fin k ↪ Fin n := Fin.castLEEmb hkn
  let s : Finset (Fin n) := Finset.univ.map e
  let a := (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn)
  have hsub : s ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ s
  have houtside : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ∉ s →
      hiaiScale S hk hkn i = 1 := by
    intro i _ hi
    have hik : k ≤ i.val := by
      by_contra hnot
      have hlt : i.val < k := Nat.lt_of_not_ge hnot
      let j : Fin k := ⟨i.val, hlt⟩
      have hej : e j = i := by apply Fin.ext; rfl
      exact hi (by
        simp only [s, Finset.mem_map, Finset.mem_univ, true_and]
        exact ⟨j, hej⟩)
    exact hiaiScale_eq_one_of_le S hk hkn i hik
  have hrestrict :
      (∏ i ∈ s, hiaiScale S hk hkn i) =
        ∏ i : Fin n, hiaiScale S hk hkn i := by
    simpa using Finset.prod_subset hsub houtside
  have hmap :
      (∏ i ∈ s, hiaiScale S hk hkn i) =
        ∏ j : Fin k, hiaiScale S hk hkn (e j) := by
    simp [s]
  have hscaleTop : ∀ j : Fin k,
      hiaiScale S hk hkn (e j) =
        (Matrix.toEuclideanLin S).singularValues j / a := by
    intro j
    rw [hiaiScale_eq_of_lt S hk hkn (e j) (by simp [e, j.isLt])]
    rfl
  have hprod : (∏ i : Fin n, hiaiScale S hk hkn i) =
      (∏ j : Fin k, (Matrix.toEuclideanLin S).singularValues j) /
        a ^ k := by
    rw [← hrestrict, hmap]
    simp_rw [hscaleTop]
    rw [Finset.prod_div_distrib]
    simp
  change a ^ k * (∏ i : Fin n, hiaiScale S hk hkn i) = _
  rw [hprod]
  exact mul_div_cancel₀ _ (pow_ne_zero k ha.ne')

/-- Hiai's explicit spectral factorization.  When the `k`th singular value
of `S` is positive, `S = YX` with `X` expanding, `Y` uniformly bounded by
that singular value, and the exact volume identity required by the
Gel'fand--Naimark product argument.
@isnad1 id=ex.3h4v.s14.afd9e21a5c34 from=translated src=- shape=c7ef48f2 vocab=fe405fce
-/
theorem exists_hiai_factorization
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n)
    (ha : 0 < (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn)) :
    ∃ X Y : Matrix (Fin n) (Fin n) 𝕜,
      S = Y * X ∧
      (1 : Matrix (Fin n) (Fin n) 𝕜) ≤ X.conjTranspose * X ∧
      Y.conjTranspose * Y ≤ Matrix.scalar (Fin n)
        (RCLike.ofReal
          ((Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn) ^ 2)) ∧
      (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn) ^ k *
          (Matrix.toEuclideanLin X).normDet =
        ∏ j : Fin k, (Matrix.toEuclideanLin S).singularValues j := by
  let G : Matrix (Fin n) (Fin n) 𝕜 := S.conjTranspose * S
  let hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self S
  let U : Matrix (Fin n) (Fin n) 𝕜 := decreasingEigenvectorUnitary hG
  let d : Fin n → ℝ := hiaiScale S hk hkn
  let D : Matrix (Fin n) (Fin n) 𝕜 :=
    Matrix.diagonal (RCLike.ofReal ∘ d)
  let E : Matrix (Fin n) (Fin n) 𝕜 :=
    Matrix.diagonal (fun i ↦ RCLike.ofReal (d i)⁻¹)
  let L : Matrix (Fin n) (Fin n) 𝕜 :=
    Matrix.diagonal (RCLike.ofReal ∘ decreasingEigenvalues hG)
  let X : Matrix (Fin n) (Fin n) 𝕜 := U * D * U.conjTranspose
  let Xinv : Matrix (Fin n) (Fin n) 𝕜 := U * E * U.conjTranspose
  let Y : Matrix (Fin n) (Fin n) 𝕜 := S * Xinv
  have hU : U.conjTranspose * U = 1 :=
    decreasingEigenvectorUnitary_isometry hG
  have hUU : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  have hdpos : ∀ i, 0 < d i := hiaiScale_pos S hk hkn ha
  have hdnonneg : ∀ i, 0 ≤ d i := fun i ↦ (hdpos i).le
  have hdone : ∀ i, 1 ≤ d i := hiaiScale_one_le S hk hkn ha
  have hdanti : Antitone d := hiaiScale_antitone S hk hkn ha
  have hDstar : D.conjTranspose = D := by
    change (Matrix.diagonal (RCLike.ofReal ∘ d)).conjTranspose =
      Matrix.diagonal (RCLike.ofReal ∘ d)
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hEstar : E.conjTranspose = E := by
    change (Matrix.diagonal (fun i ↦ RCLike.ofReal (d i)⁻¹)).conjTranspose =
      Matrix.diagonal (fun i ↦ RCLike.ofReal (d i)⁻¹)
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hDE : D * E = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Function.comp_apply, RCLike.ofReal_inv]
    exact mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr (hdpos i).ne')
  have hED : E * D = 1 := mul_eq_one_comm.mp hDE
  have hXstar : X.conjTranspose = X := by
    simp [X, Matrix.conjTranspose_mul, hDstar, Matrix.mul_assoc]
  have hXinvstar : Xinv.conjTranspose = Xinv := by
    simp [Xinv, Matrix.conjTranspose_mul, hEstar, Matrix.mul_assoc]
  have hXinvX : Xinv * X = 1 := by
    calc
      Xinv * X = U * E * (U.conjTranspose * U) * D * U.conjTranspose := by
        simp only [Xinv, X]
        noncomm_ring
      _ = U * (E * D) * U.conjTranspose := by rw [hU]; noncomm_ring
      _ = U * U.conjTranspose := by rw [hED]; simp
      _ = 1 := hUU
  have hfactor : S = Y * X := by
    have hprod : (S * Xinv) * X = S := by
      calc
        (S * Xinv) * X = S * (Xinv * X) := Matrix.mul_assoc S Xinv X
        _ = S * 1 := congrArg (fun M ↦ S * M) hXinvX
        _ = S := Matrix.mul_one S
    calc
      S = (S * Xinv) * X := hprod.symm
      _ = Y * X := by rfl
  have hDD : D * D =
      Matrix.diagonal (fun i ↦ RCLike.ofReal (d i ^ 2)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_two]
  have hdiagExpand : (D * D - 1).PosSemidef := by
    rw [hDD, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    have hi : 0 ≤ d i ^ 2 - 1 := by nlinarith [hdone i]
    simp only [Pi.zero_apply]
    rw [← RCLike.ofReal_one]
    rw [← RCLike.ofReal_sub]
    exact RCLike.ofReal_nonneg.mpr hi
  have hXX : X * X = U * (D * D) * U.conjTranspose := by
    simp only [X]
    calc
      (U * D * U.conjTranspose) * (U * D * U.conjTranspose) =
          U * D * (U.conjTranspose * U) * D * U.conjTranspose := by
        noncomm_ring
      _ = U * (D * D) * U.conjTranspose := by rw [hU]; noncomm_ring
  have hdiffExpand : X.conjTranspose * X - 1 =
      U * (D * D - 1) * U.conjTranspose := by
    rw [hXstar, hXX]
    calc
      U * (D * D) * U.conjTranspose - 1 =
          U * (D * D) * U.conjTranspose - U * U.conjTranspose := by rw [hUU]
      _ = U * (D * D - 1) * U.conjTranspose := by noncomm_ring
  have hExpandPSD : (X.conjTranspose * X - 1).PosSemidef := by
    rw [hdiffExpand]
    simpa using hdiagExpand.conjTranspose_mul_mul_same U.conjTranspose
  have hExpand : (1 : Matrix (Fin n) (Fin n) 𝕜) ≤
      X.conjTranspose * X := Matrix.le_iff.mpr hExpandPSD
  have hGrel : G * U = U * L :=
    mul_decreasingEigenvectorUnitary hG
  have hGdiag : U.conjTranspose * G * U = L := by
    calc
      U.conjTranspose * G * U = U.conjTranspose * (G * U) := by
        rw [Matrix.mul_assoc]
      _ = U.conjTranspose * (U * L) := by rw [hGrel]
      _ = (U.conjTranspose * U) * L := by rw [Matrix.mul_assoc]
      _ = L := by rw [hU, Matrix.one_mul]
  have hELE : E * L * E = Matrix.diagonal (fun i ↦
      RCLike.ofReal (decreasingEigenvalues hG i / d i ^ 2)) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, ← RCLike.ofReal_mul,
      RCLike.ofReal_inj]
    have hdi : d i ≠ 0 := (hdpos i).ne'
    field_simp [hdi]
  let a := (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn)
  have hdiagBound :
      (Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) - E * L * E).PosSemidef := by
    rw [Matrix.scalar_apply, hELE, Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    have hi : 0 ≤ a ^ 2 - decreasingEigenvalues hG i / d i ^ 2 :=
      sub_nonneg.mpr (gramEigenvalue_div_hiaiScale_sq_le S hk hkn ha i)
    simp only [Pi.zero_apply]
    rw [← RCLike.ofReal_sub]
    exact RCLike.ofReal_nonneg.mpr hi
  have hYgram : Y.conjTranspose * Y = U * (E * L * E) * U.conjTranspose := by
    rw [show Y.conjTranspose * Y = Xinv * G * Xinv by
      simp [Y, G, Matrix.conjTranspose_mul, hXinvstar, Matrix.mul_assoc]]
    simp only [Xinv]
    calc
      (U * E * U.conjTranspose) * G * (U * E * U.conjTranspose) =
          U * E * (U.conjTranspose * G * U) * E * U.conjTranspose := by
        noncomm_ring
      _ = U * (E * L * E) * U.conjTranspose := by rw [hGdiag]; noncomm_ring
  have hdiffBound :
      Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) - Y.conjTranspose * Y =
        U * (Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) - E * L * E) *
          U.conjTranspose := by
    rw [hYgram]
    have hscalarConj :
        U * Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) * U.conjTranspose =
          Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) := by
      rw [← Matrix.scalar_comm (RCLike.ofReal (a ^ 2))
        (fun r' ↦ Commute.all _ r') U, Matrix.mul_assoc, hUU, Matrix.mul_one]
    calc
      Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) -
          U * (E * L * E) * U.conjTranspose =
          U * Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) * U.conjTranspose -
            U * (E * L * E) * U.conjTranspose := by
        rw [hscalarConj]
      _ = U * (Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) - E * L * E) *
          U.conjTranspose := by noncomm_ring
  have hBoundPSD :
      (Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) -
        Y.conjTranspose * Y).PosSemidef := by
    rw [hdiffBound]
    simpa using hdiagBound.conjTranspose_mul_mul_same U.conjTranspose
  have hBound : Y.conjTranspose * Y ≤
      Matrix.scalar (Fin n) (RCLike.ofReal (a ^ 2)) :=
    Matrix.le_iff.mpr hBoundPSD
  have hXU : X * U = U * D := by
    simp only [X]
    calc
      U * D * U.conjTranspose * U = U * D * (U.conjTranspose * U) := by
        rw [Matrix.mul_assoc]
      _ = U * D := by rw [hU, Matrix.mul_one]
  let GX : Matrix (Fin n) (Fin n) 𝕜 := X.conjTranspose * X
  let hGX : GX.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self X
  have hGXeq : GX = U * (D * D) * U.conjTranspose := by
    calc
      GX = X.conjTranspose * X := by rfl
      _ = X * X := by rw [hXstar]
      _ = U * (D * D) * U.conjTranspose := hXX
  have hGXrel : GX * U = U *
      Matrix.diagonal (fun i ↦ RCLike.ofReal (d i ^ 2)) := by
    rw [hGXeq]
    calc
      U * (D * D) * U.conjTranspose * U =
          U * (D * D) * (U.conjTranspose * U) := by rw [Matrix.mul_assoc]
      _ = U * (D * D) := by rw [hU, Matrix.mul_one]
      _ = U * Matrix.diagonal (fun i ↦ RCLike.ofReal (d i ^ 2)) := by rw [hDD]
  have hGXspec : decreasingEigenvalues hGX = fun i ↦ d i ^ 2 :=
    decreasingEigenvalues_eq_of_diagonalization hGX U
      (fun i ↦ d i ^ 2) (hiaiScale_sq_antitone S hk hkn ha) hU hGXrel
  have hsingX : ∀ i : Fin n,
      (Matrix.toEuclideanLin X).singularValues i = d i := by
    intro i
    have hsquare := singularValues_sq_eq_decreasingEigenvalues_gram X i
    change (Matrix.toEuclideanLin X).singularValues i ^ 2 =
      decreasingEigenvalues hGX i at hsquare
    rw [hGXspec] at hsquare
    exact (sq_eq_sq₀ (LinearMap.singularValues_nonneg _ _) (hdnonneg i)).mp hsquare
  have hnormX : (Matrix.toEuclideanLin X).normDet = ∏ i : Fin n, d i := by
    rw [← prod_singularValues_eq_normDet]
    exact Finset.prod_congr rfl (fun i _ ↦ hsingX i)
  have hvolume : a ^ k * (Matrix.toEuclideanLin X).normDet =
      ∏ j : Fin k, (Matrix.toEuclideanLin S).singularValues j := by
    rw [hnormX]
    exact hiaiScale_volume_identity S hk hkn ha
  exact ⟨X, Y, hfactor, hExpand, by simpa [a] using hBound,
    by simpa [a] using hvolume⟩

/-- The selected-index Gel'fand--Naimark inequality when both square factors
are injective.  This is the only case needed in the multiplicative-Lidskii
application, where both factors are products of positive-definite matrices.
@isnad1 id=le.4h6v.s14.4496dea6859b from=translated src=- shape=3b645ee6 vocab=607ff258
-/
theorem selectedSingularProduct_of_injective
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S T : Matrix (Fin n) (Fin n) 𝕜)
    (hk : 0 < k) (hkn : k ≤ n)
    (hS : Function.Injective (Matrix.toEuclideanLin S))
    (hT : Function.Injective (Matrix.toEuclideanLin T))
    (indices : Fin k ↪ Fin n) :
    (∏ j, (Matrix.toEuclideanLin (S * T)).singularValues (indices j)) ≤
      (∏ j : Fin k, (Matrix.toEuclideanLin S).singularValues j) *
        ∏ j, (Matrix.toEuclideanLin T).singularValues (indices j) := by
  have ha : 0 <
      (Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn) := by
    have hall :=
      (LinearMap.injective_iff_forall_lt_finrank_singularValues_pos
        (Matrix.toEuclideanLin S)).mp hS
    apply hall
    simp
  obtain ⟨X, Y, hfactor, hX, hY, hvolume⟩ :=
    exists_hiai_factorization S hk hkn ha
  exact selected_product_of_factorization S T X Y
    ((Matrix.toEuclideanLin S).singularValues (kthIndex hk hkn)) ha.le
    hfactor hY hX hvolume hT indices

/-- The Euclidean linear map of a positive-definite square matrix is
injective.
@isnad1 id=injectiv.1h3v.s12.dad7e010c5b9 from=translated src=- shape=b530030d vocab=9e12ccf0
-/
theorem toEuclideanLin_injective_of_posDef
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) :
    Function.Injective (Matrix.toEuclideanLin A) := by
  intro x y hxy
  apply WithLp.ofLp_injective 2
  apply Matrix.mulVec_injective_of_isUnit hA.isUnit
  have h := congrArg WithLp.ofLp hxy
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using h

/-- Squared Gram-matrix form of the selected-product inequality for
injective square factors.
@isnad1 id=le.4h6v.s13.1b9a11bc03cf from=translated src=- shape=e0a52dc0 vocab=c430d9a5
-/
theorem selectedGramProduct_of_injective
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S T : Matrix (Fin n) (Fin n) 𝕜)
    (hS : Function.Injective (Matrix.toEuclideanLin S))
    (hT : Function.Injective (Matrix.toEuclideanLin T))
    (p : Equiv.Perm (Fin n))
    (hk0 : 0 < k) (hk : k < n) :
    prefixProd (fun i ↦ decreasingEigenvalues
      (Matrix.isHermitian_conjTranspose_mul_self (S * T)) (p i))
        k hk.le ≤
      prefixProd (decreasingEigenvalues
        (Matrix.isHermitian_conjTranspose_mul_self S)) k hk.le *
      prefixProd (fun i ↦ decreasingEigenvalues
        (Matrix.isHermitian_conjTranspose_mul_self T) (p i)) k hk.le := by
  let indices : Fin k ↪ Fin n :=
    ⟨fun j ↦ p (Fin.castLE hk.le j), by
      intro a b hab
      apply Fin.ext
      have hpEq : p (Fin.castLE hk.le a) = p (Fin.castLE hk.le b) := hab
      exact congrArg (fun z : Fin n ↦ z.val) (p.injective hpEq)⟩
  have h := selectedSingularProduct_of_injective
    S T hk0 hk.le hS hT indices
  let lhs : ℝ := ∏ j,
    (Matrix.toEuclideanLin (S * T)).singularValues (indices j)
  let rhs : ℝ :=
    (∏ j : Fin k, (Matrix.toEuclideanLin S).singularValues j) *
      ∏ j, (Matrix.toEuclideanLin T).singularValues (indices j)
  have hlhs : 0 ≤ lhs := Finset.prod_nonneg fun j _ ↦
    LinearMap.singularValues_nonneg _ _
  have hsquare : lhs * lhs ≤ rhs * rhs :=
    mul_self_le_mul_self hlhs (by simpa [lhs, rhs] using h)
  unfold prefixProd
  simp_rw [← singularValues_sq_eq_decreasingEigenvalues_gram]
  change
    (∏ j : Fin k,
      (Matrix.toEuclideanLin (S * T)).singularValues (indices j) ^ 2) ≤
      (∏ j : Fin k, (Matrix.toEuclideanLin S).singularValues j ^ 2) *
        ∏ j : Fin k, (Matrix.toEuclideanLin T).singularValues (indices j) ^ 2
  rw [Finset.prod_pow, Finset.prod_pow, Finset.prod_pow]
  dsimp [lhs, rhs] at hsquare
  nlinarith

/-- The selected ratio products required by multiplicative Lidskii follow
from the injective selected-product theorem.  The two factors introduced in
the square-root reduction are positive definite, so no singular
regularization is needed here.
@isnad1 id=lidskiis.0h1v.s3.b0767f1d6eef from=translated src=- shape=c6850a32 vocab=eea8ec68
-/
theorem lidskiiSelectedProducts_from_gelfandNaimark
    {𝕜 : Type*} [RCLike 𝕜] : LidskiiSelectedProducts 𝕜 := by
  intro n _ B Y hB hY p k hk0 hk
  let R : Matrix (Fin n) (Fin n) 𝕜 := B ^ (1 / 2 : ℝ)
  let Q : Matrix (Fin n) (Fin n) 𝕜 := Y ^ (1 / 2 : ℝ)
  let Z : Matrix (Fin n) (Fin n) 𝕜 := Y ^ (-(1 / 2 : ℝ))
  let S : Matrix (Fin n) (Fin n) 𝕜 := R * Z
  have hRpos : R.PosDef := Matrix.PosDef.rpow hB _
  have hQpos : Q.PosDef := Matrix.PosDef.rpow hY _
  have hZpos : Z.PosDef := Matrix.PosDef.rpow hY _
  have hRinj := toEuclideanLin_injective_of_posDef hRpos
  have hQinj := toEuclideanLin_injective_of_posDef hQpos
  have hZinj := toEuclideanLin_injective_of_posDef hZpos
  have hSinj : Function.Injective (Matrix.toEuclideanLin S) := by
    rw [show Matrix.toEuclideanLin S =
        (Matrix.toEuclideanLin R).comp (Matrix.toEuclideanLin Z) by
      exact toEuclideanLin_mul R Z]
    exact hRinj.comp hZinj
  have hRstar : R.conjTranspose = R := hRpos.isHermitian.eq
  have hQstar : Q.conjTranspose = Q := hQpos.isHermitian.eq
  have hZstar : Z.conjTranspose = Z := hZpos.isHermitian.eq
  have hRR : R * R = B := by
    simpa [R] using Matrix.PosDef.half_mul_half hB
  have hQQ : Q * Q = Y := by
    simpa [Q] using Matrix.PosDef.half_mul_half hY
  have hZQ : Z * Q = 1 := by
    simpa [Z, Q] using Matrix.PosDef.invHalf_mul_half hY
  have hST : S * Q = R := by
    simp only [S]
    rw [Matrix.mul_assoc, hZQ, Matrix.mul_one]
  have hSTgram : (S * Q).conjTranspose * (S * Q) = B := by
    rw [hST, hRstar, hRR]
  have hSgram : S.conjTranspose * S = relativeMatrix Y B := by
    simp only [S, Matrix.conjTranspose_mul, hRstar, hZstar]
    calc
      (Z * R) * (R * Z) = Z * (R * R) * Z := by noncomm_ring
      _ = Z * B * Z := by rw [hRR]
      _ = relativeMatrix Y B := rfl
  have hQgram : Q.conjTranspose * Q = Y := by rw [hQstar, hQQ]
  have h := selectedGramProduct_of_injective S Q hSinj hQinj p hk0 hk
  have hSTeigs := decreasingEigenvalues_congr
    (Matrix.isHermitian_conjTranspose_mul_self (S * Q)) hB.isHermitian hSTgram
  have hSeigs := decreasingEigenvalues_congr
    (Matrix.isHermitian_conjTranspose_mul_self S)
    (relativeMatrix_posDef hY hB).isHermitian hSgram
  have hQeigs := decreasingEigenvalues_congr
    (Matrix.isHermitian_conjTranspose_mul_self Q) hY.isHermitian hQgram
  rw [hSTeigs, hSeigs, hQeigs] at h
  have hprodY : 0 < prefixProd
      (fun i ↦ decreasingEigenvalues hY.isHermitian (p i)) k hk.le :=
    prefixProd_pos
      (fun i ↦ Matrix.PosDef.decreasingEigenvalues_pos hY _) k hk.le
  rw [prefixProd, prefixProd, Finset.prod_div_distrib]
  apply (div_le_iff₀ hprodY).2
  simpa [prefixProd, mul_comm] using h

/-- Multiplicative Lidskii in the exact form used by the paper, derived from
Mathlib and the nondegenerate Gel'fand--Naimark proof above.
@isnad1 id=lidskii.0h1v.s3.cc72a47301f0 from=translated src=- shape=c6850a32 vocab=214a9450
-/
theorem lidskii_from_gelfandNaimark
    {𝕜 : Type*} [RCLike 𝕜] : Lidskii 𝕜 :=
  lidskii_of_properPrefix
    (lidskiiProperPrefix_of_ratioProducts
      (ratioProducts_of_selectedProducts
        lidskiiSelectedProducts_from_gelfandNaimark))

end HiaiLimPowerMeans
