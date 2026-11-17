import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The trace form of `K = ℚ[x]/(xⁿ − x − 1)` is the power-sum matrix (GENUINE)

For `f = X^n - X - 1` (n = 4 and n = 3), `K = AdjoinRoot f` is the rank-`n`
number field `ℚ(root)`.  We compute the *genuine* `Algebra.trace ℚ K (root^k)`
and show it equals the `k`-th Newton power sum `p_k` of the roots of `f`, and
that the Gram matrix of `Algebra.traceForm ℚ K` in the power basis
`{1, root, …, root^{n-1}}` equals the explicit integer matrix used in
`PdtSignature` / `PdtSignatureRho`.

The computation is fully structural:
`Algebra.trace_eq_matrix_trace` reduces the trace to a matrix trace of the
left-multiplication matrix, whose diagonal entries are
`pb.basis.repr (root^k · root^j) j`; the relation `root^n = root + 1`
(from `aeval root f = 0`) reduces every `root^m` to the power basis, and the
basis-`repr` reads off the coefficient.

No `sorry`, no `native_decide`.
-/

open Polynomial AdjoinRoot Algebra Matrix

namespace PDT

noncomputable section

/-! ## Quartic: `f₄ = X⁴ − X − 1` -/

abbrev f4 : ℚ[X] := X^4 - X - 1

/--
@isnad1 id=monic.0h0v.s2.3e7a59ece0ff from=translated src=- shape=25b03439 vocab=8c24af0a
-/
theorem f4_monic : (f4).Monic := by
  show ((X^4 - X - 1 : ℚ[X])).Monic
  have : (X^4 - X - 1 : ℚ[X]) = X^4 + (- X - 1) := by ring
  rw [this]; apply monic_X_pow_add; compute_degree!

/--
@isnad1 id=ne.0h0v.s4.7cf677db2fcf from=translated src=- shape=2d527563 vocab=a1ab2a95
-/
theorem f4_ne : f4 ≠ 0 := f4_monic.ne_zero

/--
@isnad1 id=eq.0h0v.s3.54283785dd7e from=translated src=- shape=b3c4969c vocab=f5ae2993
-/
theorem f4_deg : f4.natDegree = 4 := by
  show (X^4 - X - 1 : ℚ[X]).natDegree = 4; compute_degree!

/-- The number field `ℚ(root)` for `X⁴ − X − 1`, with its power basis.-/
abbrev pb4 := AdjoinRoot.powerBasis f4_ne
abbrev r4 := root f4

/--
@isnad1 id=eq.0h0v.s5.b29f494c2f61 from=translated src=- shape=b6447e33 vocab=d4b89652
-/
theorem pb4_dim : pb4.dim = 4 := f4_deg

/-- The defining relation `root⁴ = root + 1`.
@isnad1 id=eq.0h0v.s7.8aaf3aa5d009 from=translated src=- shape=b6dd541a vocab=55150769
-/
theorem r4_pow4 : r4^4 = r4 + 1 := by
  have h : aeval r4 f4 = 0 := by rw [aeval_eq, mk_self]
  show (root f4)^4 = root f4 + 1
  simp only [f4, map_sub, map_pow, map_one, aeval_X] at h
  linear_combination h

/-- Reductions of `root^m` to the power basis (via `root⁴ = root + 1`).
@isnad1 id=eq.0h0v.s7.941f6535b39b from=translated src=- shape=03e9e35c vocab=55150769
-/
theorem r4_pow5 : r4^5 = r4^2 + r4 := by
  linear_combination (r4) * r4_pow4
/--
@isnad1 id=eq.0h0v.s7.4fe9fa395e94 from=translated src=- shape=2917b40f vocab=55150769
-/
theorem r4_pow6 : r4^6 = r4^3 + r4^2 := by
  linear_combination (r4^2) * r4_pow4
/--
@isnad1 id=eq.0h0v.s7.58a949a5c094 from=translated src=- shape=c23eda6d vocab=55150769
-/
theorem r4_pow7 : r4^7 = r4^3 + r4 + 1 := by
  linear_combination (r4^3 + 1) * r4_pow4
/--
@isnad1 id=eq.0h0v.s8.9fe71c78376d from=translated src=- shape=478a7d9d vocab=d091300e
-/
theorem r4_pow8 : r4^8 = r4^2 + 2 * r4 + 1 := by
  linear_combination (r4^4 + r4 + 1) * r4_pow4
/--
@isnad1 id=eq.0h0v.s8.6d64a64eb992 from=translated src=- shape=7f5d03ea vocab=d091300e
-/
theorem r4_pow9 : r4^9 = r4^3 + 2 * r4^2 + r4 := by
  linear_combination (r4^5 + r4^2 + r4) * r4_pow4

/-- cast `Fin 4 → Fin pb4.dim`.-/
abbrev ι (i : Fin 4) : Fin pb4.dim := Fin.cast pb4_dim.symm i

/--
@isnad1 id=eq.0h1v.s8.ec80db7fa0cd from=translated src=- shape=2675c9c8 vocab=fbb849d1
-/
theorem basis_val (i : Fin 4) : pb4.basis (ι i) = r4 ^ (i:ℕ) := by
  rw [PowerBasis.coe_basis]; rfl

/--
@isnad1 id=eq.0h0v.s8.0d892a95dbb8 from=translated src=- shape=66429139 vocab=a1937d61
-/
theorem basis_val0 : pb4.basis (ι 0) = r4^(0:ℕ) := by rw [basis_val]; norm_num
/--
@isnad1 id=eq.0h0v.s8.c2bd1d1e7b54 from=translated src=- shape=66429139 vocab=a1937d61
-/
theorem basis_val1 : pb4.basis (ι 1) = r4^(1:ℕ) := by rw [basis_val]; norm_num
/--
@isnad1 id=eq.0h0v.s8.407227ef6545 from=translated src=- shape=66429139 vocab=a1937d61
-/
theorem basis_val2 : pb4.basis (ι 2) = r4^(2:ℕ) := by rw [basis_val]; norm_num
/--
@isnad1 id=eq.0h0v.s8.7d3d693ef899 from=translated src=- shape=66429139 vocab=a1937d61
-/
theorem basis_val3 : pb4.basis (ι 3) = r4^(3:ℕ) := by rw [basis_val]; norm_num

/-- The fundamental `repr` engine: a power-basis combination, read off at `ι j`.
@isnad1 id=eq.0h5v.s10.29235effa0f9 from=translated src=- shape=64e811f1 vocab=efd5be5a
-/
theorem repr_comb (a b c d : ℚ) (j : Fin 4) :
    pb4.basis.repr (a • r4^(0:ℕ) + b • r4^(1:ℕ) + c • r4^(2:ℕ) + d • r4^(3:ℕ)) (ι j)
      = ![a,b,c,d] j := by
  rw [← basis_val0, ← basis_val1, ← basis_val2, ← basis_val3]
  simp only [map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
    Pi.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul]
  fin_cases j <;> simp [ι, Fin.ext_iff]

-- Direct repr values for the powers 0..6, as the j-th coefficient.
/--
@isnad1 id=eq.0h1v.s10.2e3b2d798ea2 from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr0 (j : Fin 4) : pb4.basis.repr (r4^(0:ℕ)) (ι j) = ![1,0,0,0] j := by
  have := repr_comb 1 0 0 0 j; simpa using this
/--
@isnad1 id=eq.0h1v.s10.ff0dd952e605 from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr1 (j : Fin 4) : pb4.basis.repr (r4^(1:ℕ)) (ι j) = ![0,1,0,0] j := by
  have := repr_comb 0 1 0 0 j; simpa using this
/--
@isnad1 id=eq.0h1v.s10.a0a03c656d9d from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr2 (j : Fin 4) : pb4.basis.repr (r4^(2:ℕ)) (ι j) = ![0,0,1,0] j := by
  have := repr_comb 0 0 1 0 j; simpa using this
/--
@isnad1 id=eq.0h1v.s10.d132b47876ed from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr3 (j : Fin 4) : pb4.basis.repr (r4^(3:ℕ)) (ι j) = ![0,0,0,1] j := by
  have := repr_comb 0 0 0 1 j; simpa using this
/--
@isnad1 id=eq.0h1v.s10.69affac0763a from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr4 (j : Fin 4) : pb4.basis.repr (r4^(4:ℕ)) (ι j) = ![1,1,0,0] j := by
  have h := repr_comb 1 1 0 0 j
  rw [r4_pow4]
  rw [show (r4 + 1 : AdjoinRoot f4)
        = (1:ℚ) • r4^(0:ℕ) + (1:ℚ) • r4^(1:ℕ) + (0:ℚ) • r4^(2:ℕ) + (0:ℚ) • r4^(3:ℕ) by
        simp only [Algebra.smul_def, map_ofNat, map_one, map_zero]; ring]
  exact h
/--
@isnad1 id=eq.0h1v.s10.7144c65ad8a3 from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr5 (j : Fin 4) : pb4.basis.repr (r4^(5:ℕ)) (ι j) = ![0,1,1,0] j := by
  have h := repr_comb 0 1 1 0 j
  rw [r4_pow5]
  rw [show (r4^2 + r4 : AdjoinRoot f4)
        = (0:ℚ) • r4^(0:ℕ) + (1:ℚ) • r4^(1:ℕ) + (1:ℚ) • r4^(2:ℕ) + (0:ℚ) • r4^(3:ℕ) by
        simp only [Algebra.smul_def, map_ofNat, map_one, map_zero]; ring]
  exact h
/--
@isnad1 id=eq.0h1v.s10.3436915d06be from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr6 (j : Fin 4) : pb4.basis.repr (r4^(6:ℕ)) (ι j) = ![0,0,1,1] j := by
  have h := repr_comb 0 0 1 1 j
  rw [r4_pow6]
  rw [show (r4^3 + r4^2 : AdjoinRoot f4)
        = (0:ℚ) • r4^(0:ℕ) + (0:ℚ) • r4^(1:ℕ) + (1:ℚ) • r4^(2:ℕ) + (1:ℚ) • r4^(3:ℕ) by
        simp only [Algebra.smul_def, map_ofNat, map_one, map_zero]; ring]
  exact h
/--
@isnad1 id=eq.0h1v.s10.7177828d29fd from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr7 (j : Fin 4) : pb4.basis.repr (r4^(7:ℕ)) (ι j) = ![1,1,0,1] j := by
  have h := repr_comb 1 1 0 1 j
  rw [r4_pow7]
  rw [show (r4^3 + r4 + 1 : AdjoinRoot f4)
        = (1:ℚ) • r4^(0:ℕ) + (1:ℚ) • r4^(1:ℕ) + (0:ℚ) • r4^(2:ℕ) + (1:ℚ) • r4^(3:ℕ) by
        simp only [Algebra.smul_def, map_ofNat, map_one, map_zero]; ring]
  exact h
/--
@isnad1 id=eq.0h1v.s10.cfd2ad89dc94 from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr8 (j : Fin 4) : pb4.basis.repr (r4^(8:ℕ)) (ι j) = ![1,2,1,0] j := by
  have h := repr_comb 1 2 1 0 j
  rw [r4_pow8]
  rw [show (r4^2 + 2 * r4 + 1 : AdjoinRoot f4)
        = (1:ℚ) • r4^(0:ℕ) + (2:ℚ) • r4^(1:ℕ) + (1:ℚ) • r4^(2:ℕ) + (0:ℚ) • r4^(3:ℕ) by
        simp only [Algebra.smul_def, map_ofNat, map_one, map_zero]; ring]
  exact h
/--
@isnad1 id=eq.0h1v.s10.ddd4e9fef8bf from=translated src=- shape=c73704ee vocab=7113253c
-/
theorem repr9 (j : Fin 4) : pb4.basis.repr (r4^(9:ℕ)) (ι j) = ![0,1,2,1] j := by
  have h := repr_comb 0 1 2 1 j
  rw [r4_pow9]
  rw [show (r4^3 + 2 * r4^2 + r4 : AdjoinRoot f4)
        = (0:ℚ) • r4^(0:ℕ) + (1:ℚ) • r4^(1:ℕ) + (2:ℚ) • r4^(2:ℕ) + (1:ℚ) • r4^(3:ℕ) by
        simp only [Algebra.smul_def, map_ofNat, map_one, map_zero]; ring]
  exact h

/-- Convert the `Algebra.trace` to the explicit `Fin 4` sum of
`repr (root^{k+j})_j`.
@isnad1 id=eq.0h1v.s10.ad5d8fc85d21 from=translated src=- shape=bb841a07 vocab=020b0c0f
-/
theorem trace_eq_sum (k : ℕ) :
    Algebra.trace ℚ (AdjoinRoot f4) (r4^k)
      = ∑ j : Fin 4, pb4.basis.repr (r4^(k + (j:ℕ))) (ι j) := by
  rw [Algebra.trace_eq_matrix_trace pb4.basis, Matrix.trace]
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  refine Fintype.sum_equiv (finCongr pb4_dim.symm)
        (fun j => pb4.basis.repr (r4^(k + (j:ℕ))) (ι j))
        (fun j => pb4.basis.repr (r4^k * pb4.basis j) j) (fun j => ?_) |>.symm
  have hb : pb4.basis (ι j) = r4^(j:ℕ) := basis_val j
  show pb4.basis.repr (r4^(k + (j:ℕ))) (ι j)
      = pb4.basis.repr (r4^k * pb4.basis (ι j)) (ι j)
  rw [hb, ← pow_add]

/-! ### The power sums (Newton sums) as genuine traces. -/

/--
@isnad1 id=eq.0h0v.s8.f5ddbfbcc07e from=translated src=- shape=93b561e0 vocab=63124655
-/
theorem trace_r4_pow0 : Algebra.trace ℚ (AdjoinRoot f4) (r4^0) = 4 := by
  rw [trace_eq_sum]
  rw [Fin.sum_univ_four]
  rw [show (0:ℕ)+((0:Fin 4):ℕ) = 0 by rfl, show (0:ℕ)+((1:Fin 4):ℕ) = 1 by rfl,
      show (0:ℕ)+((2:Fin 4):ℕ) = 2 by rfl, show (0:ℕ)+((3:Fin 4):ℕ) = 3 by rfl,
      repr0, repr1, repr2, repr3]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

/--
@isnad1 id=eq.0h0v.s8.0a8f24512799 from=translated src=- shape=93b561e0 vocab=63124655
-/
theorem trace_r4_pow1 : Algebra.trace ℚ (AdjoinRoot f4) (r4^1) = 0 := by
  rw [trace_eq_sum]
  rw [Fin.sum_univ_four]
  rw [show (1:ℕ)+((0:Fin 4):ℕ) = 1 by rfl, show (1:ℕ)+((1:Fin 4):ℕ) = 2 by rfl,
      show (1:ℕ)+((2:Fin 4):ℕ) = 3 by rfl, show (1:ℕ)+((3:Fin 4):ℕ) = 4 by rfl,
      repr1, repr2, repr3, repr4]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

/--
@isnad1 id=eq.0h0v.s8.ff109f0343a9 from=translated src=- shape=93b561e0 vocab=63124655
-/
theorem trace_r4_pow2 : Algebra.trace ℚ (AdjoinRoot f4) (r4^2) = 0 := by
  rw [trace_eq_sum]
  rw [Fin.sum_univ_four]
  rw [show (2:ℕ)+((0:Fin 4):ℕ) = 2 by rfl, show (2:ℕ)+((1:Fin 4):ℕ) = 3 by rfl,
      show (2:ℕ)+((2:Fin 4):ℕ) = 4 by rfl, show (2:ℕ)+((3:Fin 4):ℕ) = 5 by rfl,
      repr2, repr3, repr4, repr5]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

/--
@isnad1 id=eq.0h0v.s8.45c7dae622b3 from=translated src=- shape=93b561e0 vocab=63124655
-/
theorem trace_r4_pow3 : Algebra.trace ℚ (AdjoinRoot f4) (r4^3) = 3 := by
  rw [trace_eq_sum]
  rw [Fin.sum_univ_four]
  rw [show (3:ℕ)+((0:Fin 4):ℕ) = 3 by rfl, show (3:ℕ)+((1:Fin 4):ℕ) = 4 by rfl,
      show (3:ℕ)+((2:Fin 4):ℕ) = 5 by rfl, show (3:ℕ)+((3:Fin 4):ℕ) = 6 by rfl,
      repr3, repr4, repr5, repr6]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

/--
@isnad1 id=eq.0h0v.s8.c5fc737f2126 from=translated src=- shape=93b561e0 vocab=63124655
-/
theorem trace_r4_pow4 : Algebra.trace ℚ (AdjoinRoot f4) (r4^4) = 4 := by
  have : Algebra.trace ℚ (AdjoinRoot f4) (r4^4)
      = Algebra.trace ℚ (AdjoinRoot f4) (r4 + 1) := by rw [r4_pow4]
  rw [this, map_add]
  have h1 : Algebra.trace ℚ (AdjoinRoot f4) (r4) = 0 := by
    have := trace_r4_pow1; simpa using this
  have h0 : Algebra.trace ℚ (AdjoinRoot f4) (1 : AdjoinRoot f4) = 4 := by
    have := trace_r4_pow0; simpa using this
  rw [h1, h0]; norm_num

/--
@isnad1 id=eq.0h0v.s8.b3083aa23369 from=translated src=- shape=93b561e0 vocab=63124655
-/
theorem trace_r4_pow5 : Algebra.trace ℚ (AdjoinRoot f4) (r4^5) = 0 := by
  rw [trace_eq_sum, Fin.sum_univ_four]
  rw [show (5:ℕ)+((0:Fin 4):ℕ) = 5 by rfl, show (5:ℕ)+((1:Fin 4):ℕ) = 6 by rfl,
      show (5:ℕ)+((2:Fin 4):ℕ) = 7 by rfl, show (5:ℕ)+((3:Fin 4):ℕ) = 8 by rfl]
  rw [repr5, repr6, repr7, repr8]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

/--
@isnad1 id=eq.0h0v.s8.8ef4fff2f9e0 from=translated src=- shape=93b561e0 vocab=63124655
-/
theorem trace_r4_pow6 : Algebra.trace ℚ (AdjoinRoot f4) (r4^6) = 3 := by
  rw [trace_eq_sum, Fin.sum_univ_four]
  rw [show (6:ℕ)+((0:Fin 4):ℕ) = 6 by rfl, show (6:ℕ)+((1:Fin 4):ℕ) = 7 by rfl,
      show (6:ℕ)+((2:Fin 4):ℕ) = 8 by rfl, show (6:ℕ)+((3:Fin 4):ℕ) = 9 by rfl]
  rw [repr6, repr7, repr8, repr9]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

/-! ### The genuine trace-form Gram matrix equals `PdtSignature.M`. -/

/-- The explicit integer trace-form matrix of `PdtSignature`.-/
def M4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]

/-- General Gram entry: `traceForm K (root^i) (root^j) = trace (root^{i+j})`.
@isnad1 id=eq.0h2v.s10.7efb82551ed0 from=translated src=- shape=0aeab040 vocab=e0a4db08
-/
theorem traceForm_basis (i j : Fin 4) :
    Algebra.traceForm ℚ (AdjoinRoot f4) (pb4.basis (ι i)) (pb4.basis (ι j))
      = Algebra.trace ℚ (AdjoinRoot f4) (r4^((i:ℕ) + (j:ℕ))) := by
  rw [Algebra.traceForm_apply, basis_val i, basis_val j, ← pow_add]

/-- **The genuine trace form is the power-sum matrix.**  Each Gram entry
`traceForm K (root^i) (root^j)` of the `Algebra.traceForm` (NOT a hand-written
matrix) equals the corresponding entry of `M4 = PdtSignature.M`.
@isnad1 id=eq.0h2v.s10.3c0fb7397b2d from=translated src=- shape=d6946be3 vocab=8f9f2664
-/
theorem traceForm_eq_M4 (i j : Fin 4) :
    Algebra.traceForm ℚ (AdjoinRoot f4) (pb4.basis (ι i)) (pb4.basis (ι j))
      = M4 i j := by
  rw [traceForm_basis]
  have e0 := trace_r4_pow0; have e1 := trace_r4_pow1; have e2 := trace_r4_pow2
  have e3 := trace_r4_pow3; have e4 := trace_r4_pow4; have e5 := trace_r4_pow5
  have e6 := trace_r4_pow6
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue,
      show ((3:Fin 4):ℕ) = 3 from rfl, Nat.reduceAdd, e0, e1, e2, e3, e4, e5, e6] <;>
    rfl

end
end PDT
