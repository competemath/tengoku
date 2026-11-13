import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite coloring and averaged characteristic-polynomial harness

This file isolates the finite-dimensional algebraic layer used by mixed
determinantal-polynomial approaches to restricted invertibility.  It contains no
analytic root bound and introduces no axioms.
-/

open scoped BigOperators Polynomial

namespace CommutatorTheorem.BTMixedDet

/-- An `r`-coloring of `n` coordinates.-/
abbrev Coloring (n r : ℕ) := Fin n → Fin r

/-- The coordinates carrying a specified color.-/
abbrev ColorFiber {n r : ℕ} (c : Coloring n r) (a : Fin r) :=
  {i : Fin n // c i = a}

/-- The genuine principal compression to a color fiber.-/
def principalCompression {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) :
    Matrix (ColorFiber c a) (ColorFiber c a) ℂ :=
  A.submatrix Subtype.val Subtype.val

/--
@isnad1 id=eq.0h7v.s6.85820a51b5b5 from=translated src=- shape=fbaba31e vocab=40922d35
-/
@[simp] lemma principalCompression_apply {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r)
    (i j : ColorFiber c a) :
    principalCompression A c a i j = A i.1 j.1 := rfl

/--
@isnad1 id=ishermit.1h5v.s6.1985ea1cb78d from=translated src=- shape=6505f8f5 vocab=78f5fd9f
-/
lemma principalCompression_isHermitian {n r : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (c : Coloring n r) (a : Fin r) :
    (principalCompression A c a).IsHermitian :=
  hA.submatrix Subtype.val

/--
@isnad1 id=eq.0h5v.s7.4dd7feb19437 from=translated src=- shape=e9afebbb vocab=2081ed73
-/
lemma trace_principalCompression {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r) :
    (principalCompression A c a).trace =
      ∑ i : ColorFiber c a, A i.1 i.1 := by
  rfl

/-- Compress every member of a finite Hermitian family to the same color fiber.-/
def compressedFamily {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) (j : Fin k) :
    Matrix (ColorFiber c a) (ColorFiber c a) ℂ :=
  principalCompression (A j) c a

/--
@isnad1 id=ishermit.1h7v.s6.e866b2dd4ad4 from=translated src=- shape=27b8268d vocab=0b62fd97
-/
lemma compressedFamily_isHermitian {n r k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ j, (A j).IsHermitian) (c : Coloring n r) (a : Fin r) (j : Fin k) :
    (compressedFamily A c a j).IsHermitian :=
  principalCompression_isHermitian (hA j) c a

/-- Fixed-size version of a principal compression: entries outside the chosen
color are zero.  Keeping the ambient `Fin n` makes all characteristic polynomials
have the same degree.-/
def maskedCompression {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if c i = a ∧ c j = a then A i j else 0

/--
@isnad1 id=eq.0h7v.s6.054bbed26e59 from=translated src=- shape=58659972 vocab=23f66eb0
-/
@[simp] lemma maskedCompression_apply {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r)
    (i j : Fin n) :
    maskedCompression A c a i j = if c i = a ∧ c j = a then A i j else 0 := rfl

/--
@isnad1 id=ishermit.1h5v.s6.6fecc3410cfb from=translated src=- shape=e1ec5b5f vocab=1f0e2a8d
-/
lemma maskedCompression_isHermitian {n r : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (c : Coloring n r) (a : Fin r) :
    (maskedCompression A c a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hi : c i = a <;> by_cases hj : c j = a <;>
    simp [maskedCompression, hi, hj, hA.apply]

/--
@isnad1 id=eq.0h5v.s6.7d32658dd3f7 from=translated src=- shape=d4f8d2f5 vocab=49c586f3
-/
lemma trace_maskedCompression {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r) :
    (maskedCompression A c a).trace =
      ∑ i : Fin n, if c i = a then A i i else 0 := by
  simp [Matrix.trace, maskedCompression]

/-- Sum of the masked compressions of a finite matrix family.-/
noncomputable def jointMaskedCompression {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j, maskedCompression (A j) c a

/--
@isnad1 id=ishermit.1h6v.s6.8e8938e64c9c from=translated src=- shape=36175f06 vocab=1fbb85b9
-/
lemma jointMaskedCompression_isHermitian {n r k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ j, (A j).IsHermitian) (c : Coloring n r) (a : Fin r) :
    (jointMaskedCompression A c a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [jointMaskedCompression, Matrix.sum_apply]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact (maskedCompression_isHermitian (hA t) c a).apply i j

/--
@isnad1 id=eq.0h6v.s6.a7fec3e4a1f9 from=translated src=- shape=ceb275be vocab=3d2bfa3b
-/
lemma trace_jointMaskedCompression {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) :
    (jointMaskedCompression A c a).trace =
      ∑ i : Fin n, if c i = a then ∑ j : Fin k, A j i i else 0 := by
  rw [jointMaskedCompression, Matrix.trace_sum]
  simp_rw [trace_maskedCompression]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : c i = a <;> simp [hi]

/-- Uniform average of the fixed-size characteristic polynomials over all colorings.-/
noncomputable def averageCharpoly {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) : ℂ[X] :=
  ((Fintype.card (Coloring n r) : ℂ)⁻¹) •
    ∑ c : Coloring n r, (jointMaskedCompression A c a).charpoly

/-- Uniform average of the corresponding traces.-/
noncomputable def averageTrace {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) : ℂ :=
  ((Fintype.card (Coloring n r) : ℂ)⁻¹) *
    ∑ c : Coloring n r, (jointMaskedCompression A c a).trace

private lemma charpoly_coeff_dim {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.coeff n = 1 := by
  simpa using M.charpoly_monic.coeff_natDegree

/--
@isnad1 id=le.0h5v.s5.db39d1eabb2b from=translated src=- shape=376c9503 vocab=3ec06a43
-/
lemma averageCharpoly_natDegree_le {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).natDegree ≤ n := by
  rw [averageCharpoly]
  apply le_trans (Polynomial.natDegree_smul_le _ _)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c _
  simp

/--
@isnad1 id=eq.0h2v.s5.dc21853c5023 from=translated src=- shape=8fcd210a vocab=589e8fb2
-/
lemma coloring_card (n r : ℕ) : Fintype.card (Coloring n r) = r ^ n := by
  simp [Coloring]

/--
@isnad1 id=eq.1h5v.s5.8e1558766151 from=translated src=- shape=a5c42189 vocab=36753558
-/
lemma averageCharpoly_coeff_dim {n r k : ℕ} (hr : 0 < r)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff n = 1 := by
  classical
  have hcoeff :
      (∑ c : Coloring n r, (jointMaskedCompression A c a).charpoly).coeff n =
        ∑ c : Coloring n r, (jointMaskedCompression A c a).charpoly.coeff n := by
    let S : Finset (Coloring n r) := Finset.univ
    change (∑ c ∈ S, (jointMaskedCompression A c a).charpoly).coeff n =
      ∑ c ∈ S, (jointMaskedCompression A c a).charpoly.coeff n
    induction S using Finset.induction_on with
    | empty => simp
    | @insert c S hc ih => simp [Finset.sum_insert hc, ih]
  rw [averageCharpoly, Polynomial.coeff_smul]
  rw [hcoeff]
  simp_rw [charpoly_coeff_dim]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, coloring_card]
  rw [smul_eq_mul]
  have hrpow : r ^ n ≠ 0 := pow_ne_zero n (Nat.ne_of_gt hr)
  have hrpowC : ((r ^ n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hrpow
  exact inv_mul_cancel₀ hrpowC

/--
@isnad1 id=monic.1h5v.s5.fe9c29477ce4 from=translated src=- shape=c7c69578 vocab=06406935
-/
theorem averageCharpoly_monic {n r k : ℕ} (hr : 0 < r)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
    (averageCharpoly_natDegree_le A a) (averageCharpoly_coeff_dim hr A a)

/-! ## The first lower coefficient and its coloring average -/

/-- The coefficient immediately below the leading coefficient of a matrix
characteristic polynomial is minus its trace.  In dimension zero the exponent
`n - 1` is still zero, so it selects the constant coefficient of the polynomial
`1`; the conditional records this unavoidable boundary case.
@isnad1 id=eq.0h2v.s6.9eed594b8a6a from=translated src=- shape=c038a654 vocab=63a3c81d
-/
lemma charpoly_coeff_pred_dim {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.coeff (n - 1) = if n = 0 then 1 else -M.trace := by
  cases n with
  | zero => simp
  | succ n =>
      have h := Matrix.trace_eq_neg_charpoly_coeff M
      simpa using (congrArg Neg.neg h).symm

private lemma sum_coloring_indicator {n r : ℕ} (i : Fin n) (a : Fin r) (z : ℂ) :
    (∑ c : Coloring n r, if c i = a then z else 0) = (r ^ (n - 1) : ℕ) • z := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  congr 1
  simpa [Coloring] using
    (Fintype.card_filter_piFinset_const_eq_of_mem
      (s := (Finset.univ : Finset (Fin r))) i (x := a) (Finset.mem_univ a))

/-- Uniformly averaged two-coordinate weight.  This is the finite probability
space needed for second-moment and second Newton-coefficient computations.-/
noncomputable def averagePairWeight {n r : ℕ} (w : Fin n → Fin n → ℂ)
    (a : Fin r) : ℂ :=
  ((Fintype.card (Coloring n r) : ℂ)⁻¹) *
    ∑ c : Coloring n r, ∑ i : Fin n, ∑ l : Fin n,
      if c i = a ∧ c l = a then w i l else 0

/-! ## The second Newton numerator -/

/-- Sum of the input family before applying a common color mask.-/
noncomputable def familySum {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j, A j

/--
@isnad1 id=eq.0h5v.s5.06ae6d981ac7 from=translated src=- shape=09f89182 vocab=bcd3f111
-/
@[simp] lemma familySum_apply {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (i l : Fin n) :
    familySum A i l = ∑ j : Fin k, A j i l := by
  simp only [familySum, Matrix.sum_apply]

/--
@isnad1 id=eq.0h8v.s6.5a7d89600abc from=translated src=- shape=55451772 vocab=278e48f2
-/
lemma jointMaskedCompression_apply {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (c : Coloring n r) (a : Fin r) (i l : Fin n) :
    jointMaskedCompression A c a i l =
      if c i = a ∧ c l = a then familySum A i l else 0 := by
  simp only [jointMaskedCompression, Matrix.sum_apply]
  by_cases h : c i = a ∧ c l = a <;>
    simp [maskedCompression_apply, familySum_apply, h]

/-- The numerator in the degree-two Newton identity:
`2 e₂ = trace(M)² - trace(M²)`.-/
noncomputable def secondNewtonNumerator {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  M.trace ^ 2 - (M * M).trace

/-- The off-diagonal kernel whose sum is the second Newton numerator.-/
def secondNewtonKernel {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (i l : Fin n) : ℂ :=
  M i i * M l l - M i l * M l i

/--
@isnad1 id=eq.0h3v.s4.328098d9ab3a from=translated src=- shape=91c7390c vocab=e1b5cdd7
-/
@[simp] lemma secondNewtonKernel_diag {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    secondNewtonKernel M i i = 0 := by
  simp [secondNewtonKernel]

/-- Uniform average of the second Newton numerator over all common masks.-/
noncomputable def averageSecondNewtonNumerator {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) : ℂ :=
  ((Fintype.card (Coloring n r) : ℂ)⁻¹) *
    ∑ c : Coloring n r, secondNewtonNumerator (jointMaskedCompression A c a)

/-- Closed form for the uniform coloring average of the trace.  Each diagonal
coordinate survives with probability `1 / r`.
@isnad1 id=eq.0h5v.s6.565573690036 from=translated src=- shape=4dd43b1d vocab=f06fe776
-/
theorem averageTrace_eq_inv_mul_sum_trace {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    averageTrace A a = (r : ℂ)⁻¹ * ∑ j : Fin k, (A j).trace := by
  classical
  have hr : 0 < r := Fin.pos_iff_nonempty.mpr ⟨a⟩
  by_cases hn : n = 0
  · subst n
    simp [averageTrace]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [averageTrace]
    simp_rw [trace_jointMaskedCompression]
    rw [Finset.sum_comm]
    simp_rw [sum_coloring_indicator]
    rw [coloring_card]
    simp only [nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    have hpow : (r : ℂ) ^ n = (r : ℂ) * (r : ℂ) ^ (n - 1) := by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [pow_succ']
    push_cast
    rw [hpow]
    field_simp
    rw [Finset.sum_comm]
    rfl

/-- In positive dimension the next coefficient of the averaged characteristic
polynomial is minus the averaged trace.
@isnad1 id=eq.1h5v.s5.6e05cf72e611 from=translated src=- shape=345c0b0f vocab=e89af370
-/
lemma averageCharpoly_coeff_pred_dim {n r k : ℕ} (hn : 0 < n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 1) = -averageTrace A a := by
  classical
  simp [averageCharpoly, averageTrace, charpoly_coeff_pred_dim, hn.ne']

/-- Boundary-aware form of the preceding coefficient identity.  At `n = 0`,
`n - 1 = 0` and the averaged characteristic polynomial is the constant `1`.
@isnad1 id=eq.0h5v.s6.74fd38864e23 from=translated src=- shape=54a4e899 vocab=7fef0103
-/
theorem averageCharpoly_coeff_pred_dim_boundary {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 1) =
      if n = 0 then 1 else -averageTrace A a := by
  by_cases hn : n = 0
  · subst n
    simpa using averageCharpoly_coeff_dim (Fin.pos_iff_nonempty.mpr ⟨a⟩) A a
  · simpa [hn] using averageCharpoly_coeff_pred_dim (Nat.pos_of_ne_zero hn) A a

/-- Combining the coefficient identity with the closed trace count gives an
explicit first lower coefficient for the averaged characteristic polynomial.
@isnad1 id=eq.1h5v.s6.b9a63a8c4ae3 from=translated src=- shape=1f3af818 vocab=ba1991ef
-/
theorem averageCharpoly_coeff_pred_dim_eq {n r k : ℕ} (hn : 0 < n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 1) =
      -((r : ℂ)⁻¹ * ∑ j : Fin k, (A j).trace) := by
  rw [averageCharpoly_coeff_pred_dim hn, averageTrace_eq_inv_mul_sum_trace]

/-! ## The degree-two characteristic-polynomial coefficient -/

/--
@isnad1 id=ishermit.1h3v.s6.443ba9e1f517 from=translated src=- shape=e303977b vocab=8a1a2433
-/
lemma familySum_isHermitian {n k : ℕ}
    {A : Fin k → Matrix (Fin n) (Fin n) ℂ} (hA : ∀ j, (A j).IsHermitian) :
    (familySum A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i l
  simp only [familySum, Matrix.sum_apply, star_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (hA j).apply i l

end CommutatorTheorem.BTMixedDet
