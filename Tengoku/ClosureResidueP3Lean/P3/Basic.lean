import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open scoped BigOperators
open Matrix

namespace P3

/-- Full finite matrix algebra A_N = M_V(C).-/
abbrev A (V : Type*) := Matrix V V ℂ

/-- Vertex-coordinate Hilbert space C^V with the standard l2 inner product.-/
abbrev VertexSpace (V : Type*) [Fintype V] := EuclideanSpace ℂ V

section Basic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Forget only the L2 norm wrapper; algebraically this is the identity C^V ≃ C^V.-/
def vertexEquiv : VertexSpace V ≃ₗ[ℂ] (V → ℂ) :=
  WithLp.linearEquiv 2 ℂ (V → ℂ)

/-- Embed vertex coordinates as a diagonal matrix.-/
def diagonalEmbedding : VertexSpace V →ₗ[ℂ] A V :=
  (Matrix.diagonalLinearMap V ℂ ℂ).comp
    (vertexEquiv (V := V)).toLinearMap

/-- Extract the diagonal of a matrix as a vector in C^V.-/
def diagonalCoordinates : A V →ₗ[ℂ] VertexSpace V :=
  (vertexEquiv (V := V)).symm.toLinearMap.comp
    (Matrix.diagLinearMap V ℂ ℂ)

/--
@isnad1 id=eq.0h2v.s8.4a0e666ecebf from=translated src=- shape=ec485f81 vocab=a9b2c5e4
-/
@[simp]
theorem diagonalEmbedding_apply (x : VertexSpace V) :
    diagonalEmbedding (V := V) x = Matrix.diagonal x.ofLp := by
  simp [diagonalEmbedding, vertexEquiv]

omit [DecidableEq V] in
/--
@isnad1 id=eq.0h2v.s7.3b63f739df1e from=translated src=- shape=7bd2ab67 vocab=f5ce1956
-/
@[simp]
theorem diagonalCoordinates_apply (M : A V) :
    diagonalCoordinates (V := V) M = WithLp.toLp 2 M.diag := by
  apply (vertexEquiv (V := V)).injective
  ext i
  simp [diagonalCoordinates, vertexEquiv]

/--
@isnad1 id=eq.0h2v.s8.318a6114edd0 from=translated src=- shape=0ebdf5e7 vocab=2f3a4b4f
-/
@[simp]
theorem diagonalCoordinates_diagonalEmbedding (x : VertexSpace V) :
    diagonalCoordinates (V := V) (diagonalEmbedding (V := V) x) = x := by
  apply (vertexEquiv (V := V)).injective
  simp [vertexEquiv]

/-- The diagonal observational projection Delta_D.-/
def delta : A V →ₗ[ℂ] A V :=
  (diagonalEmbedding (V := V)).comp (diagonalCoordinates (V := V))

/--
@isnad1 id=eq.0h2v.s6.90d93d9d0b8e from=translated src=- shape=91579c65 vocab=d0b6da20
-/
@[simp]
theorem delta_apply (M : A V) :
    delta (V := V) M = Matrix.diagonal M.diag := by
  simp [delta]

/--
@isnad1 id=eq.0h2v.s9.c40230647454 from=translated src=- shape=4cdf5bfa vocab=f63a7be1
-/
@[simp]
theorem delta_diagonalEmbedding (x : VertexSpace V) :
    delta (V := V) (diagonalEmbedding (V := V) x) = diagonalEmbedding (V := V) x := by
  simp [delta]

/-- A3: Delta_D is idempotent.
@isnad1 id=eq.0h1v.s7.d646142a3881 from=translated src=- shape=8417785c vocab=c473a55b
-/
theorem delta_idempotent :
    (delta (V := V)).comp (delta (V := V)) = delta (V := V) := by
  ext M i j
  simp [delta_apply]

/-- The off-diagonal projection Q = I - Delta_D.-/
def offProjection : A V →ₗ[ℂ] A V :=
  LinearMap.id - delta (V := V)

/--
@isnad1 id=eq.0h2v.s7.cf32eeb43411 from=translated src=- shape=c93f4f30 vocab=540ca20a
-/
@[simp]
theorem offProjection_apply (M : A V) :
    offProjection (V := V) M = M - delta (V := V) M := by
  rfl

/--
@isnad1 id=eq.0h2v.s7.951ebf4c1741 from=translated src=- shape=51c8d845 vocab=602ddf0c
-/
@[simp]
theorem delta_add_offProjection (M : A V) :
    delta (V := V) M + offProjection (V := V) M = M := by
  simp [offProjection]

/--
@isnad1 id=eq.0h2v.s7.33ffcfa1be9d from=translated src=- shape=51c8d845 vocab=602ddf0c
-/
@[simp]
theorem offProjection_add_delta (M : A V) :
    offProjection (V := V) M + delta (V := V) M = M := by
  simp [offProjection]

/-- Diagonal observational subspace D_N.-/
def diagonalSubmodule : Submodule ℂ (A V) :=
  LinearMap.range (diagonalEmbedding (V := V))

/-- The diagonal embedding is injective because diagonalCoordinates is a left inverse.
@isnad1 id=injectiv.0h1v.s7.d470a0290f29 from=translated src=- shape=3e814608 vocab=cb5891e5
-/
theorem diagonalEmbedding_injective :
    Function.Injective (diagonalEmbedding (V := V)) := by
  intro x y h
  have h' := congrArg (diagonalCoordinates (V := V)) h
  simpa using h'

/-- A1: vertex coordinates are linearly equivalent to the diagonal observational subspace.-/
noncomputable def diagonalEmbeddingEquiv :
    VertexSpace V ≃ₗ[ℂ] diagonalSubmodule (V := V) where
  toFun x := ⟨diagonalEmbedding (V := V) x, ⟨x, rfl⟩⟩
  invFun y := diagonalCoordinates (V := V) y.1
  left_inv x := by
    simp
  right_inv y := by
    rcases y with ⟨M, hM⟩
    rcases hM with ⟨x, rfl⟩
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- A1 in the paper's direction D_N ≃ C^V.-/
noncomputable def diagonalCoordinatesEquiv :
    diagonalSubmodule (V := V) ≃ₗ[ℂ] VertexSpace V :=
  (diagonalEmbeddingEquiv (V := V)).symm

/-- Off-diagonal sector QA_N = ker Delta_D.-/
def OffDiag : Submodule ℂ (A V) :=
  LinearMap.ker (delta (V := V))

/-- A4: range(Q) = ker(Delta_D).
@isnad1 id=eq.0h1v.s6.a1d0fba22f73 from=translated src=- shape=ee606324 vocab=741940a1
-/
theorem offProjection_range_eq_ker :
    LinearMap.range (offProjection (V := V)) = OffDiag (V := V) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change delta (V := V) (offProjection (V := V) x) = 0
    ext i j
    simp [offProjection, delta_apply]
  · intro x hx
    change delta (V := V) x = 0 at hx
    refine ⟨x, ?_⟩
    simp [offProjection, hx]

/-- Coordinate-sum map C^V -> C.-/
def coordinateSumFn : (V → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, x i
  map_add' x y := by
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Finset.mul_sum]

/-- Coordinate-sum map on EuclideanSpace.-/
def coordinateSum : VertexSpace V →ₗ[ℂ] ℂ :=
  (coordinateSumFn (V := V)).comp (vertexEquiv (V := V)).toLinearMap

/-- Traceless diagonal coordinate sector D_N^0.-/
def DiagZero : Submodule ℂ (VertexSpace V) :=
  LinearMap.ker (coordinateSum (V := V))

omit [DecidableEq V] in
/--
@isnad1 id=eq.0h2v.s7.38ab8c6658a7 from=translated src=- shape=a5602aef vocab=df8b3f58
-/
@[simp]
theorem coordinateSum_apply (x : VertexSpace V) :
    coordinateSum (V := V) x = ∑ i, x.ofLp i := by
  simp [coordinateSum, coordinateSumFn, vertexEquiv]

/--
@isnad1 id=eq.0h2v.s8.633c02b506af from=translated src=- shape=0d1ad635 vocab=236c2f6f
-/
@[simp]
theorem trace_diagonalEmbedding (x : VertexSpace V) :
    (diagonalEmbedding (V := V) x).trace = ∑ i, x.ofLp i := by
  simp [diagonalEmbedding_apply]

/-- Coordinate tracelessness is exactly matrix tracelessness after diagonal embedding.
@isnad1 id=iff.0h2v.s8.a3266141e1fa from=translated src=- shape=646280ad vocab=f0ca79c1
-/
theorem mem_DiagZero_iff_trace_diagonalEmbedding_eq_zero (x : VertexSpace V) :
    x ∈ DiagZero (V := V) ↔ (diagonalEmbedding (V := V) x).trace = 0 := by
  simp [DiagZero, coordinateSum_apply]

/-- Matrix realization of D_N^0: the image of coordinate-traceless vectors under diagonal embedding.-/
def diagonalTracelessSubmodule : Submodule ℂ (A V) :=
  Submodule.map (diagonalEmbedding (V := V)) (DiagZero (V := V))

/-- A2: coordinate D_N^0 is linearly equivalent to its matrix realization.-/
noncomputable def diagZeroEquiv :
    DiagZero (V := V) ≃ₗ[ℂ] diagonalTracelessSubmodule (V := V) :=
  Submodule.equivMapOfInjective
    (diagonalEmbedding (V := V))
    (diagonalEmbedding_injective (V := V))
    (DiagZero (V := V))

/-- The matrix realization is exactly: diagonal and trace zero.
@isnad1 id=iff.0h2v.s7.5f025aa91ee6 from=translated src=- shape=24419d87 vocab=bf786132
-/
theorem mem_diagonalTracelessSubmodule_iff (M : A V) :
    M ∈ diagonalTracelessSubmodule (V := V) ↔
      M ∈ diagonalSubmodule (V := V) ∧ M.trace = 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩,
      (mem_DiagZero_iff_trace_diagonalEmbedding_eq_zero (V := V) x).mp hx⟩
  · rintro ⟨⟨x, rfl⟩, htr⟩
    refine ⟨x, ?_, rfl⟩
    exact (mem_DiagZero_iff_trace_diagonalEmbedding_eq_zero (V := V) x).mpr htr

/-- Hilbert--Schmidt pairing on diagonal matrices agrees with the standard coordinate pairing.
@isnad1 id=eq.0h3v.s9.93207fb4a068 from=translated src=- shape=8acae0a8 vocab=b3c221b5
-/
theorem trace_conjTranspose_diagonalEmbedding_mul (x y : VertexSpace V) :
    ((diagonalEmbedding (V := V) x).conjTranspose *
      diagonalEmbedding (V := V) y).trace
      = ∑ i, star (x.ofLp i) * y.ofLp i := by
  simp [diagonalEmbedding_apply]

/-- The coordinate-sum functional is onto whenever V is nonempty.
@isnad1 id=surjecti.0h1v.s7.89bc41689bb6 from=translated src=- shape=aa221e58 vocab=fc8d4dfc
-/
theorem coordinateSum_surjective [Nonempty V] :
    Function.Surjective (coordinateSum (V := V)) := by
  intro c
  let v0 : V := Classical.choice (inferInstance : Nonempty V)
  let x : VertexSpace V :=
    WithLp.toLp 2 (fun i => if i = v0 then c else 0)
  refine ⟨x, ?_⟩
  simp [coordinateSum_apply, x, v0]

/-- A5, first part: dim_C D_N = |V|.
@isnad1 id=eq.0h1v.s7.387290004c46 from=translated src=- shape=eb54d51c vocab=25ee84f5
-/
theorem diagonalSubmodule_finrank :
    Module.finrank ℂ (diagonalSubmodule (V := V)) = Fintype.card V := by
  calc
    Module.finrank ℂ (diagonalSubmodule (V := V))
        = Module.finrank ℂ (VertexSpace V) :=
          (diagonalEmbeddingEquiv (V := V)).finrank_eq.symm
    _ = Fintype.card V := finrank_euclideanSpace

/-- A5, second part: for nonempty V, dim_C D_N^0 = |V| - 1.
@isnad1 id=eq.0h1v.s8.a932f00e780b from=translated src=- shape=9d1a9149 vocab=11b0f453
-/
theorem diagZero_finrank [Nonempty V] :
    Module.finrank ℂ (DiagZero (V := V)) = Fintype.card V - 1 := by
  have hrange : LinearMap.range (coordinateSum (V := V)) = ⊤ :=
    LinearMap.range_eq_top.mpr (coordinateSum_surjective (V := V))
  have h := LinearMap.finrank_range_add_finrank_ker (coordinateSum (V := V))
  rw [hrange, finrank_top, CommSemiring.finrank_self, finrank_euclideanSpace] at h
  have hdim :
      1 + Module.finrank ℂ (DiagZero (V := V)) = Fintype.card V := h
  exact Nat.eq_sub_of_add_eq' hdim

/-- The same N-1 dimension statement in the matrix realization.
@isnad1 id=eq.0h1v.s7.356b97e7f485 from=translated src=- shape=9d1a9149 vocab=6ac5a540
-/
theorem diagonalTracelessSubmodule_finrank [Nonempty V] :
    Module.finrank ℂ (diagonalTracelessSubmodule (V := V)) = Fintype.card V - 1 := by
  calc
    Module.finrank ℂ (diagonalTracelessSubmodule (V := V))
        = Module.finrank ℂ (DiagZero (V := V)) :=
          (diagZeroEquiv (V := V)).finrank_eq.symm
    _ = Fintype.card V - 1 := diagZero_finrank (V := V)

end Basic

end P3
