import Tengoku
import Tengoku.PdtLean.PdtSignature
import Tengoku.PdtLean.PdtSignatureRho
import Tengoku.PdtLean.PdtTraceLink
import Tengoku.PdtLean.PdtTraceSignature
import Tengoku.PdtLean.PdtIrreducible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The trace form of the compositum `ℚ(ρ, Q) = ℚ[x]/(x³ − x − 1) ⊗ ℚ[x]/(x⁴ − x − 1)`

Let `k = ℚ[x]/(x³ − x − 1)` and `K = ℚ[x]/(x⁴ − x − 1)` and let `L = k ⊗[ℚ] K` be their
tensor product, a commutative `ℚ`-algebra of dimension `12`.  This file proves that the
trace form of `L` is the tensor product of the trace forms of the two factors:

* `trace_tmul`      : `Tr_L (x ⊗ y) = Tr_k x · Tr_K y`;
* `traceForm_tmul`  : `⟨x ⊗ u, y ⊗ v⟩_L = ⟨x, y⟩_k · ⟨u, v⟩_K`;
* `traceMatrix_bL`  : the Gram matrix in the tensor basis `ρⁱ ⊗ Qʲ` is the Kronecker
  product `Mρ ⊗ₖ M` of the two power-basis Gram matrices;
* `discr_bL`        : the discriminant of the tensor basis is `(−23)⁴ · (−283)³`;
* `sigPos_traceL`, `sigNeg_traceL` : the trace form of `L` has Sylvester signature `(7, 5)`.

The signature is obtained from the tensor product `cρ ⊗ cQ` of the two diagonalising bases of
`PdtTraceSignature`: it is orthogonal for the trace form of `L` with weights
`Dρ i i · D j j`, of which `2·3 + 1·1 = 7` are positive and `2·1 + 1·3 = 5` are negative.
-/

namespace PDT

open Module TensorProduct QuadraticMap
open scoped Kronecker

/-- The compositum, as the tensor product of the cubic and the quartic algebras.-/
noncomputable abbrev L := (AdjoinRoot fρ) ⊗[ℚ] (AdjoinRoot fQ)

instance : Module.Finite ℚ (AdjoinRoot fρ) := Module.Finite.of_basis bρ
instance : Module.Finite ℚ (AdjoinRoot fQ) := Module.Finite.of_basis bQ

/-- The tensor basis `ρⁱ ⊗ Qʲ`, indexed by `Fin 3 × Fin 4`.-/
noncomputable def bL : Basis (Fin 3 × Fin 4) ℚ L := bρ.tensorProduct bQ

/--
@isnad1 id=eq.0h1v.s9.3991efa5968a from=translated src=- shape=92badb24 vocab=e07362da
-/
theorem bL_apply (p : Fin 3 × Fin 4) : bL p = bρ p.1 ⊗ₜ bQ p.2 :=
  Basis.tensorProduct_apply' bρ bQ p

/-! ### (A) The trace of a pure tensor is the product of the traces -/

/-- Left multiplication by a pure tensor is the tensor product of the left multiplications.
@isnad1 id=eq.0h2v.s11.8c9d1008b8d2 from=translated src=- shape=b13eac46 vocab=1b9936d5
-/
theorem lmul_tmul (x : AdjoinRoot fρ) (y : AdjoinRoot fQ) :
    Algebra.lmul ℚ L (x ⊗ₜ y)
      = TensorProduct.map (Algebra.lmul ℚ (AdjoinRoot fρ) x) (Algebra.lmul ℚ (AdjoinRoot fQ) y) := by
  apply TensorProduct.ext'
  intro a b
  simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', TensorProduct.map_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- **The trace of a pure tensor is the product of the traces.**
@isnad1 id=eq.0h2v.s10.aba53bd612fe from=translated src=- shape=1d3d33c5 vocab=dd624a4b
-/
theorem trace_tmul (x : AdjoinRoot fρ) (y : AdjoinRoot fQ) :
    Algebra.trace ℚ L (x ⊗ₜ y)
      = Algebra.trace ℚ (AdjoinRoot fρ) x * Algebra.trace ℚ (AdjoinRoot fQ) y := by
  simp only [Algebra.trace_apply, lmul_tmul, LinearMap.trace_tensorProduct']

/-- **The trace form of `L` on pure tensors is the product of the trace forms.**
@isnad1 id=eq.0h4v.s11.18b52ff9bc3b from=translated src=- shape=c8ec1311 vocab=7a284810
-/
theorem traceForm_tmul (x y : AdjoinRoot fρ) (u v : AdjoinRoot fQ) :
    Algebra.traceForm ℚ L (x ⊗ₜ u) (y ⊗ₜ v)
      = Algebra.traceForm ℚ (AdjoinRoot fρ) x y * Algebra.traceForm ℚ (AdjoinRoot fQ) u v := by
  simp only [Algebra.traceForm_apply, Algebra.TensorProduct.tmul_mul_tmul, trace_tmul]

/-! ### (B) The Gram matrix is the Kronecker product -/

/-- **The Gram matrix of the trace form of `L` in the tensor basis is `Mρ ⊗ₖ M`.**
@isnad1 id=eq.0h0v.s9.418682d8b872 from=translated src=- shape=5138a782 vocab=7f02d603
-/
theorem traceMatrix_bL : Algebra.traceMatrix ℚ (⇑bL) = Mρ ⊗ₖ M := by
  ext p q
  rw [Algebra.traceMatrix_apply, bL_apply, bL_apply, traceForm_tmul, Matrix.kroneckerMap_apply,
    traceForm_bρ, traceForm_bQ]

/-! ### (C) The discriminant of the tensor basis -/

/-! ### (D) The Sylvester signature `(7, 5)` -/

/-- The trace form of `L`, as a quadratic form `x ↦ Tr_L(x²)`.-/
noncomputable def qTraceL : QuadraticForm ℚ L :=
  LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm ℚ L)

/-- The diagonalising basis `cρ` of `PdtTraceSignature` is `bρ ᵥ* Pρ` (its `i`-th vector is
the `i`-th column of `Pρ`).
@isnad1 id=eq.0h0v.s8.25f949f8651d from=translated src=- shape=5e819806 vocab=dfa8245c
-/
theorem coe_cρ : ⇑cρ = Matrix.vecMul (⇑bρ) (Pρ.map (algebraMap ℚ (AdjoinRoot fρ))) := by
  ext i
  rw [cρ_apply]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def]
  exact Finset.sum_congr rfl fun j _ => Algebra.commutes _ _

/--
@isnad1 id=eq.0h0v.s8.cde3b620bd85 from=translated src=- shape=5e819806 vocab=0a0a1f19
-/
theorem coe_cQ : ⇑cQ = Matrix.vecMul (⇑bQ) (P.map (algebraMap ℚ (AdjoinRoot fQ))) := by
  ext i
  rw [cQ_apply]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def]
  exact Finset.sum_congr rfl fun j _ => Algebra.commutes _ _

/-- The Gram matrix of the cubic trace form in the basis `cρ` is `Dρ = diag(3, 2, −23/6)`.
@isnad1 id=eq.0h0v.s7.9d38315d9292 from=translated src=- shape=7446b32c vocab=d2b65b7c
-/
theorem traceMatrix_cρ : Algebra.traceMatrix ℚ (⇑cρ) = Dρ := by
  rw [coe_cρ, Algebra.traceMatrix_of_matrix_vecMul, traceMatrix_bρ, congruenceρ]

/-- The Gram matrix of the quartic trace form in the basis `cQ` is `D = diag(4, 4, −9/4, 283/36)`.
@isnad1 id=eq.0h0v.s7.7eb37fd84184 from=translated src=- shape=7446b32c vocab=557cc281
-/
theorem traceMatrix_cQ : Algebra.traceMatrix ℚ (⇑cQ) = D := by
  rw [coe_cQ, Algebra.traceMatrix_of_matrix_vecMul, traceMatrix_bQ, congruence]

/--
@isnad1 id=eq.0h2v.s10.de750719b7b2 from=translated src=- shape=09393d67 vocab=988090f1
-/
theorem traceForm_cρ (i j : Fin 3) :
    Algebra.traceForm ℚ (AdjoinRoot fρ) (cρ i) (cρ j) = Dρ i j := by
  have h := congrFun (congrFun traceMatrix_cρ i) j
  rwa [Algebra.traceMatrix_apply] at h

/--
@isnad1 id=eq.0h2v.s10.0bed77dcba31 from=translated src=- shape=09393d67 vocab=0e8c2af9
-/
theorem traceForm_cQ (i j : Fin 4) :
    Algebra.traceForm ℚ (AdjoinRoot fQ) (cQ i) (cQ j) = D i j := by
  have h := congrFun (congrFun traceMatrix_cQ i) j
  rwa [Algebra.traceMatrix_apply] at h

/-- The tensor product of the two diagonalising bases.-/
noncomputable def cL : Basis (Fin 3 × Fin 4) ℚ L := cρ.tensorProduct cQ

/--
@isnad1 id=eq.0h1v.s9.8bd521034a5c from=translated src=- shape=92badb24 vocab=3c23be8d
-/
theorem cL_apply (p : Fin 3 × Fin 4) : cL p = cρ p.1 ⊗ₜ cQ p.2 :=
  Basis.tensorProduct_apply' cρ cQ p

/-- The Gram matrix of the trace form of `L` in the basis `cL` is the Kronecker product
`Dρ ⊗ₖ D`, entrywise.
@isnad1 id=eq.0h2v.s11.b06397f28e5c from=translated src=- shape=a4cea862 vocab=09526de4
-/
theorem traceForm_cL (p q : Fin 3 × Fin 4) :
    Algebra.traceForm ℚ L (cL p) (cL q) = Dρ p.1 q.1 * D p.2 q.2 := by
  rw [cL_apply, cL_apply, traceForm_tmul, traceForm_cρ, traceForm_cQ]

/-- `cL` is orthogonal for the trace form of `L`.
@isnad1 id=eq.1h2v.s11.f994cb911adf from=translated src=- shape=afd3d918 vocab=7969810f
-/
theorem traceForm_cL_ne {p q : Fin 3 × Fin 4} (h : p ≠ q) :
    Algebra.traceForm ℚ L (cL p) (cL q) = 0 := by
  rw [traceForm_cL]
  rcases ne_or_eq p.1 q.1 with h1 | h1
  · rw [Dρ_isDiag h1, zero_mul]
  · have h2 : p.2 ≠ q.2 := fun h2 => h (Prod.ext h1 h2)
    rw [D_isDiag h2, mul_zero]

/-- The values of the trace form of `L` on the basis `cL` are the products of the diagonal
entries of `Dρ` and `D`.
@isnad1 id=eq.0h1v.s10.4c771251b312 from=translated src=- shape=46256d8b vocab=3bac5f63
-/
theorem qTraceL_cL (p : Fin 3 × Fin 4) : qTraceL (cL p) = Dρ p.1 p.1 * D p.2 p.2 := by
  rw [qTraceL, LinearMap.BilinMap.toQuadraticMap_apply, traceForm_cL]

local instance : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero

/--
@isnad1 id=isortho.0h0v.s12.597811cd9be7 from=translated src=- shape=258b2932 vocab=bbdd785c
-/
theorem cL_isOrtho : (associated (R := ℚ) qTraceL).IsOrthoᵢ cL := by
  intro p q hpq
  show associatedHom ℚ qTraceL (cL p) (cL q) = 0
  rw [qTraceL, associated_toQuadraticMap, traceForm_cL_ne hpq, traceForm_cL_ne hpq.symm, add_zero,
    smul_zero]

/-- The basis representation of the trace form of `L` in the basis `cL` is the weighted sum of
squares with weights `Dρ i i · D j j`.
@isnad1 id=eq.0h0v.s8.3eef5e70cbc1 from=translated src=- shape=5aca0d0a vocab=4bf03873
-/
theorem basisRepr_cL :
    qTraceL.basisRepr cL
      = weightedSumSquares ℚ (fun p : Fin 3 × Fin 4 => Dρ p.1 p.1 * D p.2 p.2) := by
  rw [basisRepr_eq_of_iIsOrtho qTraceL cL cL_isOrtho]
  simp only [qTraceL_cL]

/-- **The trace form of `L` is equivalent to the diagonal form `Dρ ⊗ₖ D`.**
@isnad1 id=equivale.0h0v.s8.4470bbcd0133 from=translated src=- shape=e3c9ba57 vocab=1af407d4
-/
theorem qTraceL_equiv :
    QuadraticMap.Equivalent qTraceL
      (weightedSumSquares ℚ (fun p : Fin 3 × Fin 4 => Dρ p.1 p.1 * D p.2 p.2)) := by
  refine ⟨?_⟩
  rw [← basisRepr_cL]
  exact QuadraticMap.isometryEquivBasisRepr qTraceL cL

/-- The positive weights: the six `(+,+)` pairs and the one `(−,−)` pair.
@isnad1 id=eq.0h0v.s10.bbf95222a624 from=translated src=- shape=26a1699f vocab=545bc1da
-/
theorem posSet_eq :
    {p : Fin 3 × Fin 4 | 0 < Dρ p.1 p.1 * D p.2 p.2}
      = ↑({(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (1, 3), (2, 2)} : Finset (Fin 3 × Fin 4)) := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [Dρ, D]
  norm_num

/-- The negative weights: the three `(−,+)` pairs and the two `(+,−)` pairs.
@isnad1 id=eq.0h0v.s9.8e22d432276c from=translated src=- shape=b3ad89f1 vocab=545bc1da
-/
theorem negSet_eq :
    {p : Fin 3 × Fin 4 | Dρ p.1 p.1 * D p.2 p.2 < 0}
      = ↑({(0, 2), (1, 2), (2, 0), (2, 1), (2, 3)} : Finset (Fin 3 × Fin 4)) := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [Dρ, D] <;> norm_num

/-- **The trace form of the compositum has seven positive squares.**
@isnad1 id=eq.0h0v.s7.5dddf6254c86 from=translated src=- shape=34bef2d9 vocab=70a32b52
-/
theorem sigPos_traceL : sigPos qTraceL = 7 := by
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares qTraceL_equiv, posSet_eq,
    Set.ncard_coe_finset]
  rfl

/-- **The trace form of the compositum has five negative squares.**
@isnad1 id=eq.0h0v.s7.c944d3845784 from=translated src=- shape=34bef2d9 vocab=b8806e27
-/
theorem sigNeg_traceL : sigNeg qTraceL = 5 := by
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares qTraceL_equiv, negSet_eq,
    Set.ncard_coe_finset]
  rfl

/-- **Signature `(7, 5)` for the compositum `ℚ(ρ, Q)`, as an intrinsic invariant.**
@isnad1 id=and.0h0v.s8.739177a4e304 from=translated src=- shape=b5f30536 vocab=ea6dbaea
-/
theorem traceForm_signature_L : sigPos qTraceL = 7 ∧ sigNeg qTraceL = 5 :=
  ⟨sigPos_traceL, sigNeg_traceL⟩

/-! ### (E) The compositum is a field

Both factors are fields (`x³ − x − 1` and `x⁴ − x − 1` are irreducible over `ℚ`,
`PdtIrreducible`), of degrees `3` and `4`.  Since `3` and `4` are coprime, the images of the two
factors in any common extension field are linearly disjoint
(`IntermediateField.LinearDisjoint.of_finrank_coprime`), and therefore their tensor product is
a field (`IntermediateField.LinearDisjoint.isField_of_forall`). -/

instance : Fact (Irreducible fρ) := ⟨cubicQ_irreducible⟩
instance : Fact (Irreducible fQ) := ⟨quarticQ_irreducible⟩

/--
@isnad1 id=eq.0h0v.s6.ed89c514fd14 from=translated src=- shape=73abb57c vocab=cdaddd3a
-/
theorem finrank_ρ : Module.finrank ℚ (AdjoinRoot fρ) = 3 := by
  rw [Module.finrank_eq_card_basis bρ, Fintype.card_fin]

/--
@isnad1 id=eq.0h0v.s6.d3e57677a449 from=translated src=- shape=73abb57c vocab=102db38d
-/
theorem finrank_Q : Module.finrank ℚ (AdjoinRoot fQ) = 4 := by
  rw [Module.finrank_eq_card_basis bQ, Fintype.card_fin]

/--
@isnad1 id=eq.0h0v.s7.9663df165108 from=translated src=- shape=b3c4969c vocab=cbb165b7
-/
theorem finrank_L : Module.finrank ℚ L = 12 := by
  rw [Module.finrank_eq_card_basis bL, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- The tensor product of two field extensions of coprime degrees is a field.  (Stated over a
generic base field `F`: over the concrete base `ℚ` the instance `DivisionRing.toRatAlgebra`
competes with `IntermediateField.algebra'` and blocks unification.)
@isnad1 id=isfield.1h3v.s7.4407861ac443 from=translated src=- shape=0dd0f104 vocab=7bc00c80
-/
theorem isField_tensor_of_finrank_coprime {F A B : Type*} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (h : (Module.finrank F A).Coprime (Module.finrank F B)) : IsField (A ⊗[F] B) := by
  refine IntermediateField.LinearDisjoint.isField_of_forall F A B ?_
  intro K _ _ fa fb
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  rwa [← (AlgHom.equivFieldRange (f := fa)).toLinearEquiv.finrank_eq,
    ← (AlgHom.equivFieldRange (f := fb)).toLinearEquiv.finrank_eq]

/-- **The compositum `ℚ(ρ, Q) = k ⊗[ℚ] K` is a field**, because `3` and `4` are coprime.
@isnad1 id=isfield.0h0v.s6.fd6d20a1ac70 from=translated src=- shape=49959d42 vocab=bf21c645
-/
theorem L_isField : IsField L :=
  isField_tensor_of_finrank_coprime (by rw [finrank_ρ, finrank_Q]; decide)

/-- The field structure on the compositum.-/
@[reducible] noncomputable def fieldL : Field L := L_isField.toField

end PDT
