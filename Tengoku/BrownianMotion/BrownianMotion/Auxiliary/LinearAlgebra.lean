module

public import Tengoku

@[expose] public section

/--
@isnad1 id=eq.0h3v.s6.3efe4c7c577a from=translated src=- shape=ae36750a vocab=675d24b7
-/
lemma sum_single_apply {ι : Type*} (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)] [Fintype ι]
    [DecidableEq ι] (v : (i : ι) → φ i) :
    ∑ i, Pi.single i (v i) = v := by
  ext i
  simp

/--
@isnad1 id=le.1h4v.s6.26eb91ec229a from=translated src=- shape=dae937dd vocab=0577a810
-/
lemma Matrix.PosSemidef.nonneg_apply_self {n R : Type*} [CommRing R] [PartialOrder R]
    [StarRing R] {M : Matrix n n R} (hM : M.PosSemidef) (i : n) : 0 ≤ M i i := by
  classical
  convert hM.2 (Finsupp.single i 1)
  simp

section mkContinuous₂

namespace LinearMap

variable {E F G 𝕜 : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (f : E →ₗ[𝕜] F →ₗ[𝕜] G)

/-- Given a bilinear map whose codomains are finite dimensional, outputs the continuous
version. -/
def mkContinuous₂OfFiniteDimensional : E →L[𝕜] F →L[𝕜] G :=
  letI g x : F →L[𝕜] G := (f x).toContinuousLinearMap
  letI h : E →ₗ[𝕜] F →L[𝕜] G :=
    { toFun := g
      map_add' x y := by ext z; simp [g]
      map_smul' m x := by ext y; simp [g] }
  h.toContinuousLinearMap

/--
@isnad1 id=eq.0h7v.s11.3b5de025a3a1 from=translated src=- shape=c679253c vocab=4073c532
-/
@[simp]
lemma mkContinuous₂OfFiniteDimensional_apply (x : E) (y : F) :
    f.mkContinuous₂OfFiniteDimensional x y = f x y := rfl

end LinearMap

end mkContinuous₂

section InnerProductSpace

open scoped InnerProductSpace

/--
@isnad1 id=eq.0h6v.s7.5575694b5942 from=translated src=- shape=54d46132 vocab=475e8f4c
-/
lemma OrthonormalBasis.inner_eq {𝕜 E ι : Type*} [NormedAddCommGroup E] [RCLike 𝕜]
    [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) {i j : ι} :
    ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 := by
  by_cases h : i = j
  · simp only [h, ↓reduceIte]
    apply RCLike.ext
    · simp
    · simp
  · simp [h]

/--
@isnad1 id=eq.0h4v.s6.36518681db96 from=translated src=- shape=49e1a665 vocab=a01de223
-/
lemma OrthonormalBasis.norm_sq_eq_sum_sq_inner_right {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪b i, x⟫_ℝ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]
  simp

/--
@isnad1 id=eq.0h4v.s6.206d4b59118a from=translated src=- shape=b611088f vocab=a01de223
-/
lemma OrthonormalBasis.norm_sq_eq_sum_sq_inner_left {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪x, b i⟫_ℝ ^ 2 := by
  simp_rw [b.norm_sq_eq_sum_sq_inner_right, real_inner_comm]

/--
@isnad1 id=eq.0h3v.s7.a8ca48e035ac from=translated src=- shape=58aba33b vocab=854d29b7
-/
lemma EuclideanSpace.real_inner_eq {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
  nth_rw 1 [← (EuclideanSpace.basisFun ι ℝ).sum_repr' x, sum_inner]
  simp_rw [real_inner_smul_left, basisFun_inner]

/--
@isnad1 id=eq.0h3v.s11.8379bef1a27b from=translated src=- shape=a0a36ce5 vocab=9c3e1ba3
-/
@[simp]
lemma inner_toDual_symm_eq_self {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (L : StrongDual 𝕜 E) :
  inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm L) = L := by ext; simp

/--
@isnad1 id=eq.0h4v.s9.7f8113e41866 from=translated src=- shape=16837bc5 vocab=ae47ac7f
-/
@[simp]
lemma LinearIsometryEquiv.coe_coe_eq_coe {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F) :
    ⇑f.toLinearIsometry.toContinuousLinearMap = ⇑f := rfl

end InnerProductSpace
