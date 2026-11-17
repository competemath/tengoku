import Tengoku.ClosureResidueP3Lean.P3.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open scoped BigOperators
open Matrix

namespace P3

section QuadraticReturn

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Directed off-diagonal edge `(i,j)` with `i ≠ j`.-/
abbrev Edge (V : Type*) [DecidableEq V] := {p : V × V // p.1 ≠ p.2}

/-- Complex directed-edge coordinate space E_N.-/
abbrev EdgeSpace (V : Type*) [Fintype V] [DecidableEq V] :=
  EuclideanSpace ℂ (Edge V)

/-- Restrict an off-diagonal matrix to directed-edge coordinates.-/
def offDiagToEdge : OffDiag (V := V) →ₗ[ℂ] EdgeSpace V where
  toFun z := WithLp.toLp 2 (fun e => z.1 e.1.1 e.1.2)
  map_add' z w := by
    apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
    ext e
    rfl
  map_smul' c z := by
    apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
    ext e
    rfl

@[simp]
theorem offDiagToEdge_apply (z : OffDiag (V := V)) (e : Edge V) :
    (offDiagToEdge (V := V) z).ofLp e = z.1 e.1.1 e.1.2 := by
  rfl

/-- An element of `OffDiag` has zero diagonal entries.-/
theorem offDiag_diag_zero (z : OffDiag (V := V)) (i : V) :
    z.1 i i = 0 := by
  have hz : delta (V := V) z.1 = 0 := z.2
  have h := congrArg (fun M : A V => M i i) hz
  simpa [delta_apply] using h

/-- Raw matrix reconstructed from directed-edge coordinates.-/
def edgeMatrix (f : EdgeSpace V) : A V :=
  fun i j => if h : i = j then 0 else f.ofLp ⟨(i, j), h⟩

@[simp]
theorem edgeMatrix_diag (f : EdgeSpace V) (i : V) :
    edgeMatrix (V := V) f i i = 0 := by
  simp [edgeMatrix]

@[simp]
theorem edgeMatrix_offdiag (f : EdgeSpace V) {i j : V} (h : i ≠ j) :
    edgeMatrix (V := V) f i j = f.ofLp ⟨(i, j), h⟩ := by
  simp [edgeMatrix, h]

/-- The reconstructed edge matrix is off-diagonal.-/
theorem delta_edgeMatrix_zero (f : EdgeSpace V) :
    delta (V := V) (edgeMatrix (V := V) f) = 0 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [delta_apply, edgeMatrix]
  · simp [delta_apply, h]

/-- Reconstruct an off-diagonal matrix from directed-edge coordinates.-/
def edgeToOffDiag : EdgeSpace V →ₗ[ℂ] OffDiag (V := V) where
  toFun f := ⟨edgeMatrix (V := V) f, delta_edgeMatrix_zero (V := V) f⟩
  map_add' f g := by
    apply Subtype.ext
    ext i j
    by_cases h : i = j
    · subst j
      simp [edgeMatrix]
    · simp [edgeMatrix, h]
  map_smul' c f := by
    apply Subtype.ext
    ext i j
    by_cases h : i = j
    · subst j
      simp [edgeMatrix]
    · simp [edgeMatrix, h]

@[simp]
theorem edgeToOffDiag_offdiag_apply (f : EdgeSpace V) {i j : V} (h : i ≠ j) :
    (edgeToOffDiag (V := V) f).1 i j = f.ofLp ⟨(i, j), h⟩ := by
  simp [edgeToOffDiag, edgeMatrix, h]

@[simp]
theorem edgeToOffDiag_diag_apply (f : EdgeSpace V) (i : V) :
    (edgeToOffDiag (V := V) f).1 i i = 0 := by
  simp [edgeToOffDiag, edgeMatrix]

/-- C1: off-diagonal matrices are linearly equivalent to directed-edge coordinates.-/
noncomputable def offDiagEdgeEquiv : OffDiag (V := V) ≃ₗ[ℂ] EdgeSpace V where
  toFun := offDiagToEdge (V := V)
  invFun := edgeToOffDiag (V := V)
  left_inv z := by
    apply Subtype.ext
    ext i j
    by_cases h : i = j
    · subst j
      rw [edgeToOffDiag_diag_apply, offDiag_diag_zero]
    · rw [edgeToOffDiag_offdiag_apply (h := h)]
      rfl
  right_inv f := by
    apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
    ext e
    change (offDiagToEdge (V := V) (edgeToOffDiag (V := V) f)).ofLp e = f.ofLp e
    rw [offDiagToEdge_apply]
    simpa using edgeToOffDiag_offdiag_apply (V := V) f e.2
  map_add' z w := (offDiagToEdge (V := V)).map_add z w
  map_smul' c z := (offDiagToEdge (V := V)).map_smul c z

/-- Hadamard hidden flow `z ⊙ \bar w` on directed edges.-/
def hadamardFlow (z w : OffDiag (V := V)) : EdgeSpace V :=
  WithLp.toLp 2 (fun e => z.1 e.1.1 e.1.2 * star (w.1 e.1.1 e.1.2))

@[simp]
theorem hadamardFlow_apply (z w : OffDiag (V := V)) (e : Edge V) :
    (hadamardFlow (V := V) z w).ofLp e =
      z.1 e.1.1 e.1.2 * star (w.1 e.1.1 e.1.2) := by
  rfl

/-- C2: additive in the first variable.-/
theorem hadamardFlow_add_left (z₁ z₂ w : OffDiag (V := V)) :
    hadamardFlow (V := V) (z₁ + z₂) w =
      hadamardFlow (V := V) z₁ w + hadamardFlow (V := V) z₂ w := by
  apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
  ext e
  simp [hadamardFlow, add_mul]

/-- C2: complex linear in the first variable.-/
theorem hadamardFlow_smul_left (c : ℂ) (z w : OffDiag (V := V)) :
    hadamardFlow (V := V) (c • z) w =
      c • hadamardFlow (V := V) z w := by
  apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
  ext e
  simp [hadamardFlow, mul_assoc]

/-- C2: additive in the second variable.-/
theorem hadamardFlow_add_right (z w₁ w₂ : OffDiag (V := V)) :
    hadamardFlow (V := V) z (w₁ + w₂) =
      hadamardFlow (V := V) z w₁ + hadamardFlow (V := V) z w₂ := by
  apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
  ext e
  simp [hadamardFlow, mul_add]

/-- C2: conjugate-linear in the second variable.-/
theorem hadamardFlow_smul_right (c : ℂ) (z w : OffDiag (V := V)) :
    hadamardFlow (V := V) z (c • w) =
      star c • hadamardFlow (V := V) z w := by
  apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
  ext e
  simp [hadamardFlow, mul_left_comm]

/-! ## C3: divergence on directed-edge flows -/

/-- Coordinate divergence before imposing the traceless constraint:
outgoing flow minus incoming flow at each vertex.-/
def divergenceRaw : EdgeSpace V →ₗ[ℂ] VertexSpace V where
  toFun f :=
    WithLp.toLp 2 (fun i =>
      (∑ j, edgeMatrix (V := V) f i j) -
      (∑ j, edgeMatrix (V := V) f j i))
  map_add' f g := by
    apply (vertexEquiv (V := V)).injective
    ext i
    change
      (∑ j, edgeMatrix (V := V) (f + g) i j) -
          (∑ j, edgeMatrix (V := V) (f + g) j i) =
        ((∑ j, edgeMatrix (V := V) f i j) -
          (∑ j, edgeMatrix (V := V) f j i)) +
        ((∑ j, edgeMatrix (V := V) g i j) -
          (∑ j, edgeMatrix (V := V) g j i))
    have hout :
        (∑ j, edgeMatrix (V := V) (f + g) i j) =
          (∑ j, edgeMatrix (V := V) f i j) +
          (∑ j, edgeMatrix (V := V) g i j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : i = j
      · subst j
        simp [edgeMatrix]
      · simp [edgeMatrix, h]
    have hin :
        (∑ j, edgeMatrix (V := V) (f + g) j i) =
          (∑ j, edgeMatrix (V := V) f j i) +
          (∑ j, edgeMatrix (V := V) g j i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : j = i
      · subst j
        simp [edgeMatrix]
      · simp [edgeMatrix, h]
    rw [hout, hin]
    ring
  map_smul' c f := by
    apply (vertexEquiv (V := V)).injective
    ext i
    change
      (∑ j, edgeMatrix (V := V) (c • f) i j) -
          (∑ j, edgeMatrix (V := V) (c • f) j i) =
        c * ((∑ j, edgeMatrix (V := V) f i j) -
          (∑ j, edgeMatrix (V := V) f j i))
    have hout :
        (∑ j, edgeMatrix (V := V) (c • f) i j) =
          c * ∑ j, edgeMatrix (V := V) f i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : i = j
      · subst j
        simp [edgeMatrix]
      · simp [edgeMatrix, h]
    have hin :
        (∑ j, edgeMatrix (V := V) (c • f) j i) =
          c * ∑ j, edgeMatrix (V := V) f j i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : j = i
      · subst j
        simp [edgeMatrix]
      · simp [edgeMatrix, h]
    rw [hout, hin, mul_sub]

@[simp]
theorem divergenceRaw_apply (f : EdgeSpace V) (i : V) :
    (divergenceRaw (V := V) f).ofLp i =
      (∑ j, edgeMatrix (V := V) f i j) -
      (∑ j, edgeMatrix (V := V) f j i) := by
  rfl

/-- The total divergence vanishes.-/
theorem coordinateSum_divergenceRaw (f : EdgeSpace V) :
    coordinateSum (V := V) (divergenceRaw (V := V) f) = 0 := by
  rw [coordinateSum_apply]
  simp only [divergenceRaw_apply, Finset.sum_sub_distrib]
  have hswap :
      (∑ i : V, ∑ j : V, edgeMatrix (V := V) f j i) =
        ∑ i : V, ∑ j : V, edgeMatrix (V := V) f i j := by
    simpa using
      (Finset.sum_comm :
        (∑ i : V, ∑ j : V, edgeMatrix (V := V) f i j) =
          ∑ j : V, ∑ i : V, edgeMatrix (V := V) f i j).symm
  rw [hswap]
  exact sub_self _

/-- C3: divergence lands canonically in the traceless diagonal coordinate sector.-/
def divergence : EdgeSpace V →ₗ[ℂ] DiagZero (V := V) where
  toFun f :=
    ⟨divergenceRaw (V := V) f, by
      change coordinateSum (V := V) (divergenceRaw (V := V) f) = 0
      exact coordinateSum_divergenceRaw (V := V) f⟩
  map_add' f g := by
    apply Subtype.ext
    exact (divergenceRaw (V := V)).map_add f g
  map_smul' c f := by
    apply Subtype.ext
    exact (divergenceRaw (V := V)).map_smul c f

@[simp]
theorem divergence_apply (f : EdgeSpace V) (i : V) :
    ((divergence (V := V) f).1).ofLp i =
      (∑ j, edgeMatrix (V := V) f i j) -
      (∑ j, edgeMatrix (V := V) f j i) := by
  rfl

/-! ## C4: diagonal entries of the quadratic commutator -/

/-- Edge-matrix realization of a Hadamard flow, including the diagonal case.-/
@[simp]
theorem edgeMatrix_hadamardFlow_apply
    (z w : OffDiag (V := V)) (i j : V) :
    edgeMatrix (V := V) (hadamardFlow (V := V) z w) i j =
      z.1 i j * star (w.1 i j) := by
  by_cases h : i = j
  · subst j
    simp [edgeMatrix, offDiag_diag_zero]
  · simp [edgeMatrix, h, hadamardFlow_apply]

/-- Coordinate form of divergence for a hidden Hadamard flow.-/
theorem divergence_hadamardFlow_apply
    (z w : OffDiag (V := V)) (i : V) :
    ((divergence (V := V) (hadamardFlow (V := V) z w)).1).ofLp i =
      (∑ j, z.1 i j * star (w.1 i j)) -
      (∑ j, z.1 j i * star (w.1 j i)) := by
  rw [divergence_apply]
  simp_rw [edgeMatrix_hadamardFlow_apply]

/-- C4: the i-th diagonal entry of `[z,w*]` is outgoing minus incoming
edgewise pairing.-/
theorem commutator_conjTranspose_diagonal_entry
    (z w : OffDiag (V := V)) (i : V) :
    (z.1 * w.1.conjTranspose - w.1.conjTranspose * z.1) i i =
      (∑ j, z.1 i j * star (w.1 i j)) -
      (∑ j, z.1 j i * star (w.1 j i)) := by
  simp [Matrix.mul_apply, mul_comm]

/-! ## C5: Flow--Residue Factorization (Theorem 6.1) -/

/-- Quadratic diagonal return defined directly from the diagonal of the
commutator `[z,w*]`.  This definition is independent of `divergence`.-/
def quadraticReturn (z w : OffDiag (V := V)) : DiagZero (V := V) := by
  let x : VertexSpace V :=
    WithLp.toLp 2 (fun i =>
      (z.1 * w.1.conjTranspose - w.1.conjTranspose * z.1) i i)
  refine ⟨x, ?_⟩
  change coordinateSum (V := V) x = 0
  rw [coordinateSum_apply]
  simp only [x]
  simp_rw [commutator_conjTranspose_diagonal_entry]
  rw [Finset.sum_sub_distrib]
  have hswap :
      (∑ i : V, ∑ j : V, z.1 j i * star (w.1 j i)) =
        ∑ i : V, ∑ j : V, z.1 i j * star (w.1 i j) := by
    simpa using
      (Finset.sum_comm :
        (∑ i : V, ∑ j : V, z.1 i j * star (w.1 i j)) =
          ∑ j : V, ∑ i : V, z.1 i j * star (w.1 i j)).symm
  rw [hswap]
  exact sub_self _

@[simp]
theorem quadraticReturn_apply
    (z w : OffDiag (V := V)) (i : V) :
    ((quadraticReturn (V := V) z w).1).ofLp i =
      (z.1 * w.1.conjTranspose - w.1.conjTranspose * z.1) i i := by
  rfl

/-- The coordinate return is exactly the divergence of the hidden Hadamard flow.-/
theorem quadraticReturn_eq_divergence
    (z w : OffDiag (V := V)) :
    quadraticReturn (V := V) z w =
      divergence (V := V) (hadamardFlow (V := V) z w) := by
  apply Subtype.ext
  apply (vertexEquiv (V := V)).injective
  ext i
  change
    ((quadraticReturn (V := V) z w).1).ofLp i =
      ((divergence (V := V) (hadamardFlow (V := V) z w)).1).ofLp i
  rw [quadraticReturn_apply, divergence_hadamardFlow_apply]
  exact commutator_conjTranspose_diagonal_entry (V := V) z w i

/-- Matrix realization of the quadratic return: embedding its diagonal coordinates
recovers the diagonal projection of the commutator.-/
theorem diagonalEmbedding_quadraticReturn
    (z w : OffDiag (V := V)) :
    diagonalEmbedding (V := V) (quadraticReturn (V := V) z w).1 =
      delta (V := V)
        (z.1 * w.1.conjTranspose - w.1.conjTranspose * z.1) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagonalEmbedding_apply, delta_apply, quadraticReturn_apply]
  · simp [diagonalEmbedding_apply, delta_apply, h]

/-- C5 / Theorem 6.1 in the paper, in matrix form:
`Delta_D([z,w*]) = div(z ⊙ conjugate(w))`, with the divergence embedded back
into the traceless diagonal matrix sector.-/
theorem flowResidueFactorization
    (z w : OffDiag (V := V)) :
    delta (V := V)
        (z.1 * w.1.conjTranspose - w.1.conjTranspose * z.1) =
      diagonalEmbedding (V := V)
        (divergence (V := V) (hadamardFlow (V := V) z w)).1 := by
  rw [← quadraticReturn_eq_divergence (V := V) z w]
  exact (diagonalEmbedding_quadraticReturn (V := V) z w).symm

/-! ## C6: self-return / intensity difference -/

/-- C6: for `w = z`, the diagonal quadratic return is outgoing hidden
intensity minus incoming hidden intensity at each vertex.  Here the complex
intensity is written algebraically as `a * star a` (i.e. `|a|^2`).-/
theorem quadraticReturn_self_entry
    (z : OffDiag (V := V)) (i : V) :
    ((quadraticReturn (V := V) z z).1).ofLp i =
      (∑ j, z.1 i j * star (z.1 i j)) -
      (∑ j, z.1 j i * star (z.1 j i)) := by
  rw [quadraticReturn_apply]
  exact commutator_conjTranspose_diagonal_entry (V := V) z z i

/-- Equivalent divergence form of the self-return intensity identity.-/
theorem divergence_self_hadamard_entry
    (z : OffDiag (V := V)) (i : V) :
    ((divergence (V := V) (hadamardFlow (V := V) z z)).1).ofLp i =
      (∑ j, z.1 i j * star (z.1 i j)) -
      (∑ j, z.1 j i * star (z.1 j i)) := by
  exact divergence_hadamardFlow_apply (V := V) z z i

end QuadraticReturn

end P3
