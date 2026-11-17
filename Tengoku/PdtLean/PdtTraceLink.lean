import Tengoku
import Tengoku.PdtLean.PdtNorm
import Tengoku.PdtLean.PdtSignature
import Tengoku.PdtLean.PdtSignatureRho

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The integer matrices `M` and `Mρ` are the trace-form Gram matrices

`PdtSignature` fixes the integer matrix

  `M = !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]`,  `det M = -283`,

and `PdtSignatureRho` fixes

  `Mρ = !![3,0,2; 0,2,3; 2,3,2]`,  `det Mρ = -23`.

Both are introduced there by hand, with Newton's identities quoted in a
comment. This file *proves* the link: `M` and `Mρ` really are the Gram
matrices of the trace form `(x, y) ↦ Tr_{K/ℚ}(x y)` in the power basis
`1, r, r², …` of `K = ℚ[X]/(f)` for `f = X⁴ − X − 1` resp. `X³ − X − 1`,
and their determinants are the power-basis discriminants `Algebra.discr`.

Everything is done with `AdjoinRoot`, `PowerBasis` and `Algebra.traceMatrix`.
-/

namespace PDT

open Polynomial Module

/-! ### The two polynomials

`fQ = X⁴ − X − 1` and `fρ = X³ − X − 1` are taken from `PdtNorm` rather than
re-declared here, so that this module and `PdtNorm` can be imported together. -/

/--
@isnad1 id=monic.0h0v.s2.637623437421 from=translated src=- shape=25b03439 vocab=f442ba14
-/
theorem fQ_monic : fQ.Monic := by
  unfold fQ; monicity!

/--
@isnad1 id=monic.0h0v.s2.81564fd4acda from=translated src=- shape=25b03439 vocab=ff49a5df
-/
theorem fρ_monic : fρ.Monic := by
  unfold fρ; monicity!

/--
@isnad1 id=eq.0h0v.s3.6f3b8655be37 from=translated src=- shape=b3c4969c vocab=a9d5ff1b
-/
theorem fQ_natDegree : fQ.natDegree = 4 := by
  unfold fQ; compute_degree!

/--
@isnad1 id=eq.0h0v.s3.3c63bd907ba3 from=translated src=- shape=b3c4969c vocab=8fbf0bd9
-/
theorem fρ_natDegree : fρ.natDegree = 3 := by
  unfold fρ; compute_degree!

/-! ### The power bases -/

/-- The power basis `1, r, r², r³` of `ℚ[X]/(X⁴ − X − 1)`.-/
noncomputable def pbQ : PowerBasis ℚ (AdjoinRoot fQ) := AdjoinRoot.powerBasis' fQ_monic

/-- The power basis `1, r, r²` of `ℚ[X]/(X³ − X − 1)`.-/
noncomputable def pbρ : PowerBasis ℚ (AdjoinRoot fρ) := AdjoinRoot.powerBasis' fρ_monic

/--
@isnad1 id=eq.0h0v.s5.ceb6766a6e3f from=translated src=- shape=b6447e33 vocab=1c6e6351
-/
theorem pbQ_dim : pbQ.dim = 4 := fQ_natDegree

/--
@isnad1 id=eq.0h0v.s5.8ec61e65b3a1 from=translated src=- shape=b6447e33 vocab=041839a0
-/
theorem pbρ_dim : pbρ.dim = 3 := fρ_natDegree

/--
@isnad1 id=eq.0h0v.s5.902887d9711e from=translated src=- shape=5719ffc4 vocab=d0ab1836
-/
theorem pbQ_gen : pbQ.gen = AdjoinRoot.root fQ := rfl

/--
@isnad1 id=eq.0h0v.s5.b78bc0eb0668 from=translated src=- shape=5719ffc4 vocab=17c01888
-/
theorem pbρ_gen : pbρ.gen = AdjoinRoot.root fρ := rfl

/-! ### The defining relations satisfied by the roots -/

/--
@isnad1 id=eq.0h0v.s7.129fc2718a65 from=translated src=- shape=69ea745c vocab=b701890a
-/
theorem rQ_pow_four : (AdjoinRoot.root fQ) ^ 4 = AdjoinRoot.root fQ + 1 := by
  have h : (Polynomial.aeval (AdjoinRoot.root fQ)) fQ = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h2 : (Polynomial.aeval (AdjoinRoot.root fQ)) (X ^ 4 - X - 1 : ℚ[X]) = 0 := h
  simp only [map_sub, map_pow, map_one, Polynomial.aeval_X] at h2
  linear_combination h2

/--
@isnad1 id=eq.0h0v.s7.dc31df5ebaff from=translated src=- shape=69ea745c vocab=6c0d7485
-/
theorem rρ_pow_three : (AdjoinRoot.root fρ) ^ 3 = AdjoinRoot.root fρ + 1 := by
  have h : (Polynomial.aeval (AdjoinRoot.root fρ)) fρ = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h2 : (Polynomial.aeval (AdjoinRoot.root fρ)) (X ^ 3 - X - 1 : ℚ[X]) = 0 := h
  simp only [map_sub, map_pow, map_one, Polynomial.aeval_X] at h2
  linear_combination h2

/--
@isnad1 id=eq.0h0v.s7.e47112e3ad74 from=translated src=- shape=f481da74 vocab=b701890a
-/
theorem rQ_pow_five :
    (AdjoinRoot.root fQ) ^ 5 = (AdjoinRoot.root fQ) ^ 2 + AdjoinRoot.root fQ := by
  linear_combination (AdjoinRoot.root fQ) * rQ_pow_four

/--
@isnad1 id=eq.0h0v.s7.68c03501d9a3 from=translated src=- shape=90b414db vocab=b701890a
-/
theorem rQ_pow_six :
    (AdjoinRoot.root fQ) ^ 6 = (AdjoinRoot.root fQ) ^ 3 + (AdjoinRoot.root fQ) ^ 2 := by
  linear_combination (AdjoinRoot.root fQ) ^ 2 * rQ_pow_four

/--
@isnad1 id=eq.0h0v.s7.348755031259 from=translated src=- shape=f481da74 vocab=6c0d7485
-/
theorem rρ_pow_four :
    (AdjoinRoot.root fρ) ^ 4 = (AdjoinRoot.root fρ) ^ 2 + AdjoinRoot.root fρ := by
  linear_combination (AdjoinRoot.root fρ) * rρ_pow_three

/-! ### The power bases, reindexed by `Fin 4` and `Fin 3` -/

/-- The power basis of `ℚ[X]/(X⁴ − X − 1)`, indexed by `Fin 4`.-/
noncomputable def bQ : Basis (Fin 4) ℚ (AdjoinRoot fQ) :=
  pbQ.basis.reindex (finCongr pbQ_dim)

/-- The power basis of `ℚ[X]/(X³ − X − 1)`, indexed by `Fin 3`.-/
noncomputable def bρ : Basis (Fin 3) ℚ (AdjoinRoot fρ) :=
  pbρ.basis.reindex (finCongr pbρ_dim)

/--
@isnad1 id=eq.0h1v.s7.9108c693c582 from=translated src=- shape=1e6b2a01 vocab=f225a7c6
-/
theorem bQ_apply (i : Fin 4) : bQ i = AdjoinRoot.root fQ ^ (i : ℕ) := by
  show (pbQ.basis.reindex (finCongr pbQ_dim)) i = _
  rw [Basis.reindex_apply, pbQ.basis_eq_pow, pbQ_gen]
  simp

/--
@isnad1 id=eq.0h1v.s7.e50fadd9bd90 from=translated src=- shape=1e6b2a01 vocab=932d9d9d
-/
theorem bρ_apply (i : Fin 3) : bρ i = AdjoinRoot.root fρ ^ (i : ℕ) := by
  show (pbρ.basis.reindex (finCongr pbρ_dim)) i = _
  rw [Basis.reindex_apply, pbρ.basis_eq_pow, pbρ_gen]
  simp

/--
@isnad1 id=eq.0h0v.s7.e0352b3a7281 from=translated src=- shape=5a0a820a vocab=e96680a9
-/
theorem bQ0 : bQ 0 = 1 := by simp [bQ_apply]
/--
@isnad1 id=eq.0h0v.s7.fc5ccf47afe1 from=translated src=- shape=b2817cd3 vocab=6d120791
-/
theorem bQ1 : bQ 1 = AdjoinRoot.root fQ := by simp [bQ_apply]
/--
@isnad1 id=eq.0h0v.s7.36375a802a05 from=translated src=- shape=6b9c1609 vocab=8144a9f2
-/
theorem bQ2 : bQ 2 = AdjoinRoot.root fQ ^ 2 := by simp [bQ_apply]
/--
@isnad1 id=eq.0h0v.s7.aead045fe331 from=translated src=- shape=6b9c1609 vocab=8144a9f2
-/
theorem bQ3 : bQ 3 = AdjoinRoot.root fQ ^ 3 := by simp [bQ_apply]

/--
@isnad1 id=eq.0h0v.s7.d3236df17013 from=translated src=- shape=5a0a820a vocab=ae6f6a54
-/
theorem bρ0 : bρ 0 = 1 := by simp [bρ_apply]
/--
@isnad1 id=eq.0h0v.s7.23075a0e94da from=translated src=- shape=b2817cd3 vocab=472f8ad0
-/
theorem bρ1 : bρ 1 = AdjoinRoot.root fρ := by simp [bρ_apply]
/--
@isnad1 id=eq.0h0v.s7.a3b2ec1f9f5e from=translated src=- shape=6b9c1609 vocab=1d45050c
-/
theorem bρ2 : bρ 2 = AdjoinRoot.root fρ ^ 2 := by simp [bρ_apply]

/-! ### The trace, expanded in the power basis -/

/--
@isnad1 id=eq.0h1v.s11.7f21407ec6a0 from=translated src=- shape=4e234201 vocab=34549a08
-/
theorem traceQ_eq (x : AdjoinRoot fQ) :
    Algebra.trace ℚ (AdjoinRoot fQ) x
      = bQ.repr (x * bQ 0) 0 + bQ.repr (x * bQ 1) 1
        + bQ.repr (x * bQ 2) 2 + bQ.repr (x * bQ 3) 3 := by
  rw [Algebra.trace_eq_matrix_trace bQ x]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Fin.sum_univ_four]

/--
@isnad1 id=eq.0h1v.s11.44fc57b171a9 from=translated src=- shape=b7fa0053 vocab=c0e6a662
-/
theorem traceρ_eq (x : AdjoinRoot fρ) :
    Algebra.trace ℚ (AdjoinRoot fρ) x
      = bρ.repr (x * bρ 0) 0 + bρ.repr (x * bρ 1) 1 + bρ.repr (x * bρ 2) 2 := by
  rw [Algebra.trace_eq_matrix_trace bρ x]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Fin.sum_univ_three]

/-! ### The higher powers of the root, expanded in the power basis -/

/--
@isnad1 id=eq.0h0v.s8.19185acce2a2 from=translated src=- shape=23cef0cf vocab=21d7929e
-/
theorem powQ4 : AdjoinRoot.root fQ ^ 4 = bQ 0 + bQ 1 := by
  rw [bQ0, bQ1]; linear_combination rQ_pow_four

/--
@isnad1 id=eq.0h0v.s8.713485799f78 from=translated src=- shape=23cef0cf vocab=21d7929e
-/
theorem powQ5 : AdjoinRoot.root fQ ^ 5 = bQ 1 + bQ 2 := by
  rw [bQ1, bQ2]; linear_combination rQ_pow_five

/--
@isnad1 id=eq.0h0v.s8.b8c227ced1fd from=translated src=- shape=23cef0cf vocab=21d7929e
-/
theorem powQ6 : AdjoinRoot.root fQ ^ 6 = bQ 2 + bQ 3 := by
  rw [bQ2, bQ3]; linear_combination rQ_pow_six

/--
@isnad1 id=eq.0h0v.s8.e552254b5af1 from=translated src=- shape=23cef0cf vocab=0e276e0c
-/
theorem powρ3 : AdjoinRoot.root fρ ^ 3 = bρ 0 + bρ 1 := by
  rw [bρ0, bρ1]; linear_combination rρ_pow_three

/--
@isnad1 id=eq.0h0v.s8.9c68f5b96400 from=translated src=- shape=23cef0cf vocab=0e276e0c
-/
theorem powρ4 : AdjoinRoot.root fρ ^ 4 = bρ 1 + bρ 2 := by
  rw [bρ1, bρ2]; linear_combination rρ_pow_four

/-! ### The power sums `p_k = Tr(r^k)` -/

/--
@isnad1 id=eq.0h0v.s8.1f3b417b2c5e from=translated src=- shape=5c5d9984 vocab=6e5d646c
-/
theorem tQ0 : Algebra.trace ℚ (AdjoinRoot fQ) 1 = 4 := by
  simpa using Algebra.trace_algebraMap_of_basis bQ (1 : ℚ)

/--
@isnad1 id=eq.0h0v.s7.439098895d69 from=translated src=- shape=cf7a9615 vocab=5c797ca7
-/
theorem tQ1 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ) = 0 := by
  rw [traceQ_eq]
  have e0 : AdjoinRoot.root fQ * bQ 0 = bQ 1 := by rw [bQ0, bQ1]; ring
  have e1 : AdjoinRoot.root fQ * bQ 1 = bQ 2 := by rw [bQ1, bQ2]; ring
  have e2 : AdjoinRoot.root fQ * bQ 2 = bQ 3 := by rw [bQ2, bQ3]; ring
  have e3 : AdjoinRoot.root fQ * bQ 3 = bQ 0 + bQ 1 := by rw [← powQ4, bQ3]; ring
  rw [e0, e1, e2, e3]
  simp

/--
@isnad1 id=eq.0h0v.s8.56d399a9204e from=translated src=- shape=49577604 vocab=56d6f005
-/
theorem tQ2 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 2) = 0 := by
  rw [traceQ_eq]
  have e0 : AdjoinRoot.root fQ ^ 2 * bQ 0 = bQ 2 := by rw [bQ0, bQ2]; ring
  have e1 : AdjoinRoot.root fQ ^ 2 * bQ 1 = bQ 3 := by rw [bQ1, bQ3]; ring
  have e2 : AdjoinRoot.root fQ ^ 2 * bQ 2 = bQ 0 + bQ 1 := by rw [← powQ4, bQ2]; ring
  have e3 : AdjoinRoot.root fQ ^ 2 * bQ 3 = bQ 1 + bQ 2 := by rw [← powQ5, bQ3]; ring
  rw [e0, e1, e2, e3]
  simp

/--
@isnad1 id=eq.0h0v.s8.a3be915fe548 from=translated src=- shape=49577604 vocab=56d6f005
-/
theorem tQ3 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 3) = 3 := by
  rw [traceQ_eq]
  have e0 : AdjoinRoot.root fQ ^ 3 * bQ 0 = bQ 3 := by rw [bQ0, bQ3]; ring
  have e1 : AdjoinRoot.root fQ ^ 3 * bQ 1 = bQ 0 + bQ 1 := by rw [← powQ4, bQ1]; ring
  have e2 : AdjoinRoot.root fQ ^ 3 * bQ 2 = bQ 1 + bQ 2 := by rw [← powQ5, bQ2]; ring
  have e3 : AdjoinRoot.root fQ ^ 3 * bQ 3 = bQ 2 + bQ 3 := by rw [← powQ6, bQ3]; ring
  rw [e0, e1, e2, e3]
  simp
  norm_num

/--
@isnad1 id=eq.0h0v.s8.29d4c87db217 from=translated src=- shape=49577604 vocab=56d6f005
-/
theorem tQ4 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 4) = 4 := by
  rw [rQ_pow_four, map_add, tQ1, tQ0]; norm_num

/--
@isnad1 id=eq.0h0v.s8.d9c3066ecd5d from=translated src=- shape=49577604 vocab=56d6f005
-/
theorem tQ5 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 5) = 0 := by
  rw [rQ_pow_five, map_add, tQ2, tQ1]; norm_num

/--
@isnad1 id=eq.0h0v.s8.168e6d995d99 from=translated src=- shape=49577604 vocab=56d6f005
-/
theorem tQ6 : Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ 6) = 3 := by
  rw [rQ_pow_six, map_add, tQ3, tQ2]; norm_num

/--
@isnad1 id=eq.0h0v.s8.b274b94f5af5 from=translated src=- shape=5c5d9984 vocab=6f81dd83
-/
theorem tρ0 : Algebra.trace ℚ (AdjoinRoot fρ) 1 = 3 := by
  simpa using Algebra.trace_algebraMap_of_basis bρ (1 : ℚ)

/--
@isnad1 id=eq.0h0v.s7.2e9af78ef3e0 from=translated src=- shape=cf7a9615 vocab=6473687c
-/
theorem tρ1 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ) = 0 := by
  rw [traceρ_eq]
  have e0 : AdjoinRoot.root fρ * bρ 0 = bρ 1 := by rw [bρ0, bρ1]; ring
  have e1 : AdjoinRoot.root fρ * bρ 1 = bρ 2 := by rw [bρ1, bρ2]; ring
  have e2 : AdjoinRoot.root fρ * bρ 2 = bρ 0 + bρ 1 := by rw [← powρ3, bρ2]; ring
  rw [e0, e1, e2]
  simp

/--
@isnad1 id=eq.0h0v.s8.299c35cec990 from=translated src=- shape=49577604 vocab=d081bf5f
-/
theorem tρ2 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ 2) = 2 := by
  rw [traceρ_eq]
  have e0 : AdjoinRoot.root fρ ^ 2 * bρ 0 = bρ 2 := by rw [bρ0, bρ2]; ring
  have e1 : AdjoinRoot.root fρ ^ 2 * bρ 1 = bρ 0 + bρ 1 := by rw [← powρ3, bρ1]; ring
  have e2 : AdjoinRoot.root fρ ^ 2 * bρ 2 = bρ 1 + bρ 2 := by rw [← powρ4, bρ2]; ring
  rw [e0, e1, e2]
  simp
  norm_num

/--
@isnad1 id=eq.0h0v.s8.77437b40ccf3 from=translated src=- shape=49577604 vocab=d081bf5f
-/
theorem tρ3 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ 3) = 3 := by
  rw [rρ_pow_three, map_add, tρ1, tρ0]; norm_num

/--
@isnad1 id=eq.0h0v.s8.26be358c3ce3 from=translated src=- shape=49577604 vocab=d081bf5f
-/
theorem tρ4 : Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ 4) = 2 := by
  rw [rρ_pow_four, map_add, tρ2, tρ1]; norm_num

/-! ### The Gram matrices of the trace form -/

/--
@isnad1 id=eq.0h2v.s8.f6c5eacdef7c from=translated src=- shape=00566e13 vocab=77a3dcd4
-/
theorem traceMatrix_bQ_apply (i j : Fin 4) :
    Algebra.traceMatrix ℚ (⇑bQ) i j
      = Algebra.trace ℚ (AdjoinRoot fQ) (AdjoinRoot.root fQ ^ ((i : ℕ) + (j : ℕ))) := by
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bQ_apply, bQ_apply, ← pow_add]

/--
@isnad1 id=eq.0h2v.s8.b4ddd8487535 from=translated src=- shape=00566e13 vocab=6800db25
-/
theorem traceMatrix_bρ_apply (i j : Fin 3) :
    Algebra.traceMatrix ℚ (⇑bρ) i j
      = Algebra.trace ℚ (AdjoinRoot fρ) (AdjoinRoot.root fρ ^ ((i : ℕ) + (j : ℕ))) := by
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, bρ_apply, bρ_apply, ← pow_add]

/-- **The quartic link.** The integer matrix `M` of `PdtSignature` is the Gram matrix
of the trace form of `ℚ[X]/(X⁴ − X − 1)` in the power basis `1, r, r², r³`.
@isnad1 id=eq.0h0v.s7.f3f67d46ba01 from=translated src=- shape=7446b32c vocab=319cea89
-/
theorem traceMatrix_bQ : Algebra.traceMatrix ℚ (⇑bQ) = M := by
  ext i j
  rw [traceMatrix_bQ_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [M, tQ0, tQ1, tQ2, tQ3, tQ4, tQ5, tQ6]

/-- **The cubic link.** The integer matrix `Mρ` of `PdtSignatureRho` is the Gram matrix
of the trace form of `ℚ[X]/(X³ − X − 1)` in the power basis `1, r, r²`.
@isnad1 id=eq.0h0v.s7.853518eef015 from=translated src=- shape=7446b32c vocab=9f3715c1
-/
theorem traceMatrix_bρ : Algebra.traceMatrix ℚ (⇑bρ) = Mρ := by
  ext i j
  rw [traceMatrix_bρ_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Mρ, tρ0, tρ1, tρ2, tρ3, tρ4]

/-- The same statement, phrased for the unreindexed `PowerBasis` of `AdjoinRoot fQ`.
@isnad1 id=eq.0h2v.s8.56379c029d72 from=translated src=- shape=5c19a5c9 vocab=97c8a907
-/
theorem traceMatrix_Q (i j : Fin pbQ.dim) :
    Algebra.traceMatrix ℚ (⇑pbQ.basis) i j = M (Fin.cast pbQ_dim i) (Fin.cast pbQ_dim j) := by
  have h : Algebra.traceMatrix ℚ (⇑bQ) (finCongr pbQ_dim i) (finCongr pbQ_dim j)
      = Algebra.traceMatrix ℚ (⇑pbQ.basis) i j := by
    show Algebra.traceMatrix ℚ (⇑(pbQ.basis.reindex (finCongr pbQ_dim)))
        (finCongr pbQ_dim i) (finCongr pbQ_dim j) = _
    rw [Algebra.traceMatrix_reindex]
    simp
  rw [← h, traceMatrix_bQ]
  rfl

/-- The same statement, phrased for the unreindexed `PowerBasis` of `AdjoinRoot fρ`.
@isnad1 id=eq.0h2v.s8.1e9bacb53f29 from=translated src=- shape=5c19a5c9 vocab=1d556dc2
-/
theorem traceMatrix_ρ (i j : Fin pbρ.dim) :
    Algebra.traceMatrix ℚ (⇑pbρ.basis) i j = Mρ (Fin.cast pbρ_dim i) (Fin.cast pbρ_dim j) := by
  have h : Algebra.traceMatrix ℚ (⇑bρ) (finCongr pbρ_dim i) (finCongr pbρ_dim j)
      = Algebra.traceMatrix ℚ (⇑pbρ.basis) i j := by
    show Algebra.traceMatrix ℚ (⇑(pbρ.basis.reindex (finCongr pbρ_dim)))
        (finCongr pbρ_dim i) (finCongr pbρ_dim j) = _
    rw [Algebra.traceMatrix_reindex]
    simp
  rw [← h, traceMatrix_bρ]
  rfl

/-! ### The power-basis discriminants -/

/-- **The discriminant of the power basis of `ℚ[X]/(X⁴ − X − 1)` is `−283`.**
@isnad1 id=eq.0h0v.s8.be908cbe06f4 from=translated src=- shape=5318c8c7 vocab=23e63e1b
-/
theorem discr_Q : Algebra.discr ℚ pbQ.basis = -283 := by
  have h : Algebra.discr ℚ (⇑bQ) = Algebra.discr ℚ (⇑pbQ.basis) := by
    show Algebra.discr ℚ (⇑(pbQ.basis.reindex (finCongr pbQ_dim))) = _
    rw [Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ pbQ.basis (finCongr pbQ_dim)
  rw [← h, Algebra.discr_def, traceMatrix_bQ, det_M]

/-- **The discriminant of the power basis of `ℚ[X]/(X³ − X − 1)` is `−23`.**
@isnad1 id=eq.0h0v.s8.85b842e7b819 from=translated src=- shape=5318c8c7 vocab=332f84b0
-/
theorem discr_ρ : Algebra.discr ℚ pbρ.basis = -23 := by
  have h : Algebra.discr ℚ (⇑bρ) = Algebra.discr ℚ (⇑pbρ.basis) := by
    show Algebra.discr ℚ (⇑(pbρ.basis.reindex (finCongr pbρ_dim))) = _
    rw [Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ pbρ.basis (finCongr pbρ_dim)
  rw [← h, Algebra.discr_def, traceMatrix_bρ, detMρ]

end PDT
