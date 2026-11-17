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

/--
@isnad1 id=eq.0h3v.s9.ed739147da8e from=translated src=- shape=981dec30 vocab=956fea36
-/
@[simp]
theorem offDiagToEdge_apply (z : OffDiag (V := V)) (e : Edge V) :
    (offDiagToEdge (V := V) z).ofLp e = z.1 e.1.1 e.1.2 := by
  rfl

/-- An element of `OffDiag` has zero diagonal entries.
@isnad1 id=eq.0h3v.s7.ea65e78f95a7 from=translated src=- shape=0573ca9d vocab=00e51c26
-/
theorem offDiag_diag_zero (z : OffDiag (V := V)) (i : V) :
    z.1 i i = 0 := by
  have hz : delta (V := V) z.1 = 0 := z.2
  have h := congrArg (fun M : A V => M i i) hz
  simpa [delta_apply] using h

/-- Raw matrix reconstructed from directed-edge coordinates.-/
def edgeMatrix (f : EdgeSpace V) : A V :=
  fun i j => if h : i = j then 0 else f.ofLp ⟨(i, j), h⟩

/--
@isnad1 id=eq.0h3v.s4.d06414acfe92 from=translated src=- shape=13c21902 vocab=cd902715
-/
@[simp]
theorem edgeMatrix_diag (f : EdgeSpace V) (i : V) :
    edgeMatrix (V := V) f i i = 0 := by
  simp [edgeMatrix]

/--
@isnad1 id=eq.1h4v.s6.446127900a77 from=translated src=- shape=fdfc86f4 vocab=00f1d254
-/
@[simp]
theorem edgeMatrix_offdiag (f : EdgeSpace V) {i j : V} (h : i ≠ j) :
    edgeMatrix (V := V) f i j = f.ofLp ⟨(i, j), h⟩ := by
  simp [edgeMatrix, h]

/-- The reconstructed edge matrix is off-diagonal.
@isnad1 id=eq.0h2v.s7.2933fe2ce9d5 from=translated src=- shape=4b3c1ea2 vocab=92877306
-/
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

/--
@isnad1 id=eq.1h4v.s9.afcf68de9c9e from=translated src=- shape=3d2fe009 vocab=eb914c6f
-/
@[simp]
theorem edgeToOffDiag_offdiag_apply (f : EdgeSpace V) {i j : V} (h : i ≠ j) :
    (edgeToOffDiag (V := V) f).1 i j = f.ofLp ⟨(i, j), h⟩ := by
  simp [edgeToOffDiag, edgeMatrix, h]

/--
@isnad1 id=eq.0h3v.s9.edab8da31b82 from=translated src=- shape=0c76df4f vocab=3db73bb2
-/
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

/--
@isnad1 id=eq.0h4v.s8.db2ba674cdbc from=translated src=- shape=d15ec36e vocab=55b11588
-/
@[simp]
theorem hadamardFlow_apply (z w : OffDiag (V := V)) (e : Edge V) :
    (hadamardFlow (V := V) z w).ofLp e =
      z.1 e.1.1 e.1.2 * star (w.1 e.1.1 e.1.2) := by
  rfl

/-- C2: additive in the first variable.
@isnad1 id=eq.0h4v.s9.40962edf31f5 from=translated src=- shape=5ea81aa8 vocab=d5f27631
-/
theorem hadamardFlow_add_left (z₁ z₂ w : OffDiag (V := V)) :
    hadamardFlow (V := V) (z₁ + z₂) w =
      hadamardFlow (V := V) z₁ w + hadamardFlow (V := V) z₂ w := by
  apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
  ext e
  simp [hadamardFlow, add_mul]

/-- C2: complex linear in the first variable.
@isnad1 id=eq.0h4v.s8.3bca829b1290 from=translated src=- shape=4b6c1a61 vocab=e870fc72
-/
theorem hadamardFlow_smul_left (c : ℂ) (z w : OffDiag (V := V)) :
    hadamardFlow (V := V) (c • z) w =
      c • hadamardFlow (V := V) z w := by
  apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
  ext e
  simp [hadamardFlow, mul_assoc]

/-- C2: additive in the second variable.
@isnad1 id=eq.0h4v.s9.17c8677c532f from=translated src=- shape=3e3aef02 vocab=d5f27631
-/
theorem hadamardFlow_add_right (z w₁ w₂ : OffDiag (V := V)) :
    hadamardFlow (V := V) z (w₁ + w₂) =
      hadamardFlow (V := V) z w₁ + hadamardFlow (V := V) z w₂ := by
  apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
  ext e
  simp [hadamardFlow, mul_add]

/-- C2: conjugate-linear in the second variable.
@isnad1 id=eq.0h4v.s9.6a3aa06533d3 from=translated src=- shape=91e4753a vocab=ae3849d5
-/
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

/--
@isnad1 id=eq.0h3v.s8.3ed2ca13c050 from=translated src=- shape=baf1e95d vocab=7fdb1486
-/
@[simp]
theorem divergenceRaw_apply (f : EdgeSpace V) (i : V) :
    (divergenceRaw (V := V) f).ofLp i =
      (∑ j, edgeMatrix (V := V) f i j) -
      (∑ j, edgeMatrix (V := V) f j i) := by
  rfl

/-- The total divergence vanishes.
@isnad1 id=eq.0h2v.s9.1f97b609577c from=translated src=- shape=ccaeb154 vocab=ecca4497
-/
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

/--
@isnad1 id=eq.0h3v.s10.232bfcc1a7df from=translated src=- shape=fa22a237 vocab=63a0d87d
-/
@[simp]
theorem divergence_apply (f : EdgeSpace V) (i : V) :
    ((divergence (V := V) f).1).ofLp i =
      (∑ j, edgeMatrix (V := V) f i j) -
      (∑ j, edgeMatrix (V := V) f j i) := by
  rfl

/-! ## C4: diagonal entries of the quadratic commutator -/

/-- Edge-matrix realization of a Hadamard flow, including the diagonal case.
@isnad1 id=eq.0h5v.s8.0e6d68b8aa3c from=translated src=- shape=548843d3 vocab=33a3478a
-/
@[simp]
theorem edgeMatrix_hadamardFlow_apply
    (z w : OffDiag (V := V)) (i j : V) :
    edgeMatrix (V := V) (hadamardFlow (V := V) z w) i j =
      z.1 i j * star (w.1 i j) := by
  by_cases h : i = j
  · subst j
    simp [edgeMatrix, offDiag_diag_zero]
  · simp [edgeMatrix, h, hadamardFlow_apply]

/-- Coordinate form of divergence for a hidden Hadamard flow.
@isnad1 id=eq.0h4v.s11.8bbb6efea7eb from=translated src=- shape=8f102941 vocab=cc302a67
-/
theorem divergence_hadamardFlow_apply
    (z w : OffDiag (V := V)) (i : V) :
    ((divergence (V := V) (hadamardFlow (V := V) z w)).1).ofLp i =
      (∑ j, z.1 i j * star (w.1 i j)) -
      (∑ j, z.1 j i * star (w.1 j i)) := by
  rw [divergence_apply]
  simp_rw [edgeMatrix_hadamardFlow_apply]

/-- C4: the i-th diagonal entry of `[z,w*]` is outgoing minus incoming
edgewise pairing.
@isnad1 id=eq.0h4v.s9.1723b045cf07 from=translated src=- shape=6e82aca9 vocab=cf8168d7
-/
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

/--
@isnad1 id=eq.0h4v.s9.fd566cf356a0 from=translated src=- shape=2117b4cb vocab=55b190f5
-/
@[simp]
theorem quadraticReturn_apply
    (z w : OffDiag (V := V)) (i : V) :
    ((quadraticReturn (V := V) z w).1).ofLp i =
      (z.1 * w.1.conjTranspose - w.1.conjTranspose * z.1) i i := by
  rfl

/-- The coordinate return is exactly the divergence of the hidden Hadamard flow.
@isnad1 id=eq.0h3v.s10.42061d49173b from=translated src=- shape=d102376a vocab=797b0d18
-/
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
recovers the diagonal projection of the commutator.
@isnad1 id=eq.0h3v.s10.cced05ed2276 from=translated src=- shape=8e94a2e1 vocab=d6d119d0
-/
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
into the traceless diagonal matrix sector.
@isnad1 id=eq.0h3v.s11.3d10ea5d65c3 from=translated src=- shape=f3c67902 vocab=7e40197a
-/
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
intensity is written algebraically as `a * star a` (i.e. `|a|^2`).
@isnad1 id=eq.0h3v.s9.00efe18e9ae4 from=translated src=- shape=76ba6908 vocab=d15de660
-/
theorem quadraticReturn_self_entry
    (z : OffDiag (V := V)) (i : V) :
    ((quadraticReturn (V := V) z z).1).ofLp i =
      (∑ j, z.1 i j * star (z.1 i j)) -
      (∑ j, z.1 j i * star (z.1 j i)) := by
  rw [quadraticReturn_apply]
  exact commutator_conjTranspose_diagonal_entry (V := V) z z i

/-- Equivalent divergence form of the self-return intensity identity.
@isnad1 id=eq.0h3v.s11.c1c10a038591 from=translated src=- shape=80484bf2 vocab=cc302a67
-/
theorem divergence_self_hadamard_entry
    (z : OffDiag (V := V)) (i : V) :
    ((divergence (V := V) (hadamardFlow (V := V) z z)).1).ofLp i =
      (∑ j, z.1 i j * star (z.1 i j)) -
      (∑ j, z.1 j i * star (z.1 j i)) := by
  exact divergence_hadamardFlow_apply (V := V) z z i

end QuadraticReturn

end P3
