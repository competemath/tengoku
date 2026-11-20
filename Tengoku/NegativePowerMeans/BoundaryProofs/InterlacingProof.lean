import Tengoku.NegativePowerMeans.BoundaryProofs.SpectralSubspaces

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Standalone verification of Cauchy--Poincaré interlacing

This file proves the published `Interlacing` ingredient.  The proof uses the
common finite-dimensional spectral-subspace and quadratic-form machinery in
`BoundaryProofs.SpectralSubspaces`; the assembly module supplies the result
to the unconditional paper-facing results.
-/

namespace HiaiLimPowerMeans

open Matrix
open scoped ComplexOrder MatrixOrder

/-- The product of two matrix isometries is a matrix isometry.-/
theorem matrixIsometry_mul
    {n k l : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {V : Matrix (Fin n) (Fin k) 𝕜}
    {W : Matrix (Fin k) (Fin l) 𝕜}
    (hV : MatrixIsometry V) (hW : MatrixIsometry W) :
    MatrixIsometry (V * W) := by
  change (V * W).conjTranspose * (V * W) = 1
  rw [Matrix.conjTranspose_mul]
  calc
    W.conjTranspose * V.conjTranspose * (V * W) =
        W.conjTranspose * ((V.conjTranspose * V) * W) := by
      simp only [Matrix.mul_assoc]
    _ = W.conjTranspose * W := by rw [hV, Matrix.one_mul]
    _ = 1 := hW

/-- Two isometric subspaces of dimensions whose sum exceeds the ambient
dimension have a common nonzero vector.-/
theorem isometry_ranges_intersect
    {n p q : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (V : Matrix (Fin n) (Fin p) 𝕜)
    (W : Matrix (Fin n) (Fin q) 𝕜)
    (hV : MatrixIsometry V) (hW : MatrixIsometry W)
    (hdim : n < p + q) :
    ∃ (x : EuclideanSpace 𝕜 (Fin p))
      (y : EuclideanSpace 𝕜 (Fin q)),
        x ≠ 0 ∧ y ≠ 0 ∧ V.mulVec x.ofLp = W.mulVec y.ofLp := by
  let LV := Matrix.toEuclideanLin V
  let LW := Matrix.toEuclideanLin W
  let F :
      (EuclideanSpace 𝕜 (Fin p) × EuclideanSpace 𝕜 (Fin q)) →ₗ[𝕜]
        EuclideanSpace 𝕜 (Fin n) :=
    LV.comp (LinearMap.fst 𝕜 _ _) - LW.comp (LinearMap.snd 𝕜 _ _)
  have hrank : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) <
      Module.finrank 𝕜
        (EuclideanSpace 𝕜 (Fin p) × EuclideanSpace 𝕜 (Fin q)) := by
    simpa using hdim
  have hker : F.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hrank
  obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rcases z with ⟨x, y⟩
  have hzero : F (x, y) = 0 := hzmem
  have heq : LV x = LW y := by
    have : LV x - LW y = 0 := by simpa [F] using hzero
    exact sub_eq_zero.mp this
  have hLV : Function.Injective LV :=
    toEuclideanLin_injective_of_isometry hV
  have hLW : Function.Injective LW :=
    toEuclideanLin_injective_of_isometry hW
  have hx0 : x ≠ 0 := by
    intro hx
    have hy : y = 0 := hLW (by simpa [hx] using heq.symm)
    exact hz0 (by simp [hx, hy])
  have hy0 : y ≠ 0 := by
    intro hy
    have hx : x = 0 := hLV (by simpa [hy] using heq)
    exact hz0 (by simp [hx, hy])
  have hraw : V.mulVec x.ofLp = W.mulVec y.ofLp := by
    have h := congrArg WithLp.ofLp heq
    simpa [LV, LW, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using h
  exact ⟨x, y, hx0, hy0, hraw⟩

/-- The upper Cauchy--Poincaré inequality for an isometric compression.-/
theorem decreasingEigenvalues_compress_le_proved
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (hkn : k ≤ n)
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    {V : Matrix (Fin n) (Fin k) 𝕜} (hV : MatrixIsometry V)
    (i : Fin k) :
    decreasingEigenvalues (compress_isHermitian hA V) i ≤
      decreasingEigenvalues hA (Fin.castLE hkn i) := by
  let B : Matrix (Fin k) (Fin k) 𝕜 := compress V A
  let hB : B.IsHermitian := compress_isHermitian hA V
  let UB : Matrix (Fin k) (Fin (i.val + 1)) 𝕜 :=
    spectralIsometry hB (topFinEmbeddingAt i)
  let j : Fin n := Fin.castLE hkn i
  let WA : Matrix (Fin n) (Fin (n - j.val)) 𝕜 :=
    spectralIsometry hA (bottomFinEmbeddingAt j)
  let W : Matrix (Fin n) (Fin (i.val + 1)) 𝕜 := V * UB
  have hUB : MatrixIsometry UB :=
    spectralIsometry_isometry hB (topFinEmbeddingAt i)
  have hWA : MatrixIsometry WA :=
    spectralIsometry_isometry hA (bottomFinEmbeddingAt j)
  have hW : MatrixIsometry W := matrixIsometry_mul hV hUB
  have hdim : n < (i.val + 1) + (n - j.val) := by
    dsimp [j]
    omega
  obtain ⟨x, y, hx0, _hy0, hxy⟩ :=
    isometry_ranges_intersect W WA hW hWA hdim
  let v : EuclideanSpace 𝕜 (Fin n) := Matrix.toEuclideanLin W x
  have hxyRaw :
      V.mulVec (UB.mulVec x.ofLp) = WA.mulVec y.ofLp := by
    simpa [W, Matrix.mulVec_mulVec] using hxy
  have hnormX : ‖x‖ = ‖v‖ := by
    exact (norm_toEuclideanLin_of_isometry hW x).symm
  have hnormY : ‖y‖ = ‖v‖ := by
    have heq : Matrix.toEuclideanLin WA y = v := by
      apply WithLp.ofLp_injective 2
      simpa [v, W, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.mulVec_mulVec] using hxy.symm
    rw [← heq]
    exact (norm_toEuclideanLin_of_isometry hWA y).symm
  have hchain : decreasingEigenvalues hB i * ‖v‖ ^ 2 ≤
      decreasingEigenvalues hA j * ‖v‖ ^ 2 := by
    calc
      decreasingEigenvalues hB i * ‖v‖ ^ 2 =
          decreasingEigenvalues hB i * ‖x‖ ^ 2 := by rw [hnormX]
      _ ≤ realQuadraticForm B (UB.mulVec x.ofLp) :=
        top_spectral_quadratic_lower hB i x
      _ = realQuadraticForm A (V.mulVec (UB.mulVec x.ofLp)) :=
        (realQuadraticForm_mulVec V A (UB.mulVec x.ofLp)).symm
      _ = realQuadraticForm A (WA.mulVec y.ofLp) := by rw [hxyRaw]
      _ ≤ decreasingEigenvalues hA j * ‖y‖ ^ 2 :=
        bottom_spectral_quadratic_upper hA j y
      _ = decreasingEigenvalues hA j * ‖v‖ ^ 2 := by rw [hnormY]
  have hv0 : 0 < ‖v‖ ^ 2 := by
    have hvne : v ≠ 0 := by
      intro hv
      have hx : x = 0 :=
        (toEuclideanLin_injective_of_isometry hW) (by simpa [v] using hv)
      exact hx0 hx
    positivity
  exact le_of_mul_le_mul_right hchain hv0

end HiaiLimPowerMeans
