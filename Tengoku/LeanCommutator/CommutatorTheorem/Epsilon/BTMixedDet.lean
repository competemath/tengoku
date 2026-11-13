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

@[simp] lemma principalCompression_apply {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r)
    (i j : ColorFiber c a) :
    principalCompression A c a i j = A i.1 j.1 := rfl

lemma principalCompression_isHermitian {n r : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (c : Coloring n r) (a : Fin r) :
    (principalCompression A c a).IsHermitian :=
  hA.submatrix Subtype.val

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

@[simp] lemma maskedCompression_apply {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (c : Coloring n r) (a : Fin r)
    (i j : Fin n) :
    maskedCompression A c a i j = if c i = a ∧ c j = a then A i j else 0 := rfl

lemma maskedCompression_isHermitian {n r : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (c : Coloring n r) (a : Fin r) :
    (maskedCompression A c a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hi : c i = a <;> by_cases hj : c j = a <;>
    simp [maskedCompression, hi, hj, hA.apply]

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

lemma averageCharpoly_natDegree_le {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).natDegree ≤ n := by
  rw [averageCharpoly]
  apply le_trans (Polynomial.natDegree_smul_le _ _)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c _
  simp

lemma coloring_card (n r : ℕ) : Fintype.card (Coloring n r) = r ^ n := by
  simp [Coloring]

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

theorem averageCharpoly_monic {n r k : ℕ} (hr : 0 < r)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
    (averageCharpoly_natDegree_le A a) (averageCharpoly_coeff_dim hr A a)

/-! ## The first lower coefficient and its coloring average -/

/-- The coefficient immediately below the leading coefficient of a matrix
characteristic polynomial is minus its trace.  In dimension zero the exponent
`n - 1` is still zero, so it selects the constant coefficient of the polynomial
`1`; the conditional records this unavoidable boundary case.-/
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

@[simp] lemma familySum_apply {n k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (i l : Fin n) :
    familySum A i l = ∑ j : Fin k, A j i l := by
  simp only [familySum, Matrix.sum_apply]

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
coordinate survives with probability `1 / r`.-/
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
polynomial is minus the averaged trace.-/
lemma averageCharpoly_coeff_pred_dim {n r k : ℕ} (hn : 0 < n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 1) = -averageTrace A a := by
  classical
  simp [averageCharpoly, averageTrace, charpoly_coeff_pred_dim, hn.ne']

/-- Boundary-aware form of the preceding coefficient identity.  At `n = 0`,
`n - 1 = 0` and the averaged characteristic polynomial is the constant `1`.-/
theorem averageCharpoly_coeff_pred_dim_boundary {n r k : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 1) =
      if n = 0 then 1 else -averageTrace A a := by
  by_cases hn : n = 0
  · subst n
    simpa using averageCharpoly_coeff_dim (Fin.pos_iff_nonempty.mpr ⟨a⟩) A a
  · simpa [hn] using averageCharpoly_coeff_pred_dim (Nat.pos_of_ne_zero hn) A a

/-- Combining the coefficient identity with the closed trace count gives an
explicit first lower coefficient for the averaged characteristic polynomial.-/
theorem averageCharpoly_coeff_pred_dim_eq {n r k : ℕ} (hn : 0 < n)
    (A : Fin k → Matrix (Fin n) (Fin n) ℂ) (a : Fin r) :
    (averageCharpoly A a).coeff (n - 1) =
      -((r : ℂ)⁻¹ * ∑ j : Fin k, (A j).trace) := by
  rw [averageCharpoly_coeff_pred_dim hn, averageTrace_eq_inv_mul_sum_trace]

/-! ## The degree-two characteristic-polynomial coefficient -/

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
