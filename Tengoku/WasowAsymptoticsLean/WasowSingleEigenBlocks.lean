import Tengoku.WasowAsymptoticsLean.WasowNilpotentNormalized
import Tengoku.WasowAsymptoticsLean.WasowMultiBlockReduction
import Tengoku.WasowAsymptoticsLean.WasowPencilReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms lastRowForm_of_blocks` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms diagonalBlock_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms diagonalBlock_pow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms diagonalBlock_nilpotent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms lowerBlocks_sub_scalar` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms diagonalBlock_sub_scalar` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms offDiagonalBlock_sub_scalar` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms lastRowForm_diagonal_rows` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms lastRowForm_offDiagonal_rows` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_shift_diagonal_similarity` (it only prints; the queue checks the axioms of every declaration). -/

/-! Concrete constant similarities for a normalized lower block matrix
with one eigenvalue. Nilpotence of the translated full matrix is inherited
by each diagonal block and its Krylov basis is then assembled. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace WasowSingleEigenBlocks
open WasowMultiShiftReduction WasowMultiBlockReduction
open WasowNilpotentNormalized WasowPencilReduction
variable {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]

def LowerBlocks {h : σ → ℕ} (C : Matrix (Index h) (Index h) ℂ) : Prop :=
  C.BlockTriangular (fun p => OrderDual.toDual p.1)

omit [DecidableEq σ] in
/--
@isnad1 id=eq.2h5v.s8.92eac343412c from=translated src=- shape=859f83c3 vocab=44d01472
-/
theorem diagonalBlock_mul {h : σ → ℕ}
    (C D : Matrix (Index h) (Index h) ℂ) (hC : LowerBlocks C) (hD : LowerBlocks D)
    (a : σ) : block (C*D) a a = block C a a * block D a a := by
  ext i j
  simp only [block,Matrix.mul_apply,← Finset.univ_sigma_univ,Finset.sum_sigma]
  rw [Fintype.sum_eq_single a]
  intro b hba
  apply Finset.sum_eq_zero
  intro l _
  rcases lt_or_gt_of_ne hba with hb | hb
  · rw [hD (show OrderDual.toDual a < OrderDual.toDual b from hb),mul_zero]
  · rw [hC (show OrderDual.toDual b < OrderDual.toDual a from hb),zero_mul]

/--
@isnad1 id=eq.1h5v.s8.0d1aebd5532a from=translated src=- shape=271fd596 vocab=b64e75d7
-/
theorem diagonalBlock_pow {h : σ → ℕ}
    (C : Matrix (Index h) (Index h) ℂ) (hC : LowerBlocks C) (a : σ) (k : ℕ) :
    block (C^k) a a = (block C a a)^k := by
  induction k with
  | zero => ext i j; simp [block,Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ,diagonalBlock_mul _ _ (hC.pow k) hC,ih,pow_succ]

/--
@isnad1 id=isnilpot.2h4v.s8.19a37ac33605 from=translated src=- shape=b49eff6d vocab=d8c6f4fe
-/
theorem diagonalBlock_nilpotent {h : σ → ℕ}
    (C : Matrix (Index h) (Index h) ℂ) (hC : LowerBlocks C)
    (hN : IsNilpotent C) (a : σ) : IsNilpotent (block C a a) := by
  obtain ⟨k,hk⟩ := hN
  refine ⟨k,?_⟩
  rw [← diagonalBlock_pow C hC a k,hk]
  rfl

omit [Fintype σ] in
/--
@isnad1 id=lowerblo.1h4v.s7.826c6e1238d9 from=translated src=- shape=78eebc3a vocab=9104a192
-/
theorem lowerBlocks_sub_scalar {h : σ → ℕ}
    (C : Matrix (Index h) (Index h) ℂ) (hC : LowerBlocks C) (α : ℂ) :
    LowerBlocks (C-α • 1) := by
  intro i j hij
  have hne : i≠j := by intro he; subst j; exact lt_irrefl _ hij
  simp only [Matrix.sub_apply,hC hij,Matrix.smul_apply,Matrix.one_apply,
    ite_eq_right hne,smul_zero,sub_zero]

omit [Fintype σ] [LinearOrder σ] in
/--
@isnad1 id=eq.0h5v.s9.062b949f4cc4 from=translated src=- shape=fe6e39af vocab=478920ed
-/
theorem diagonalBlock_sub_scalar {h : σ → ℕ}
    (C : Matrix (Index h) (Index h) ℂ) (α : ℂ) (a : σ) :
    block (C-α • 1) a a = block C a a - α • 1 := by
  ext i j
  simp [block,Matrix.one_apply]

omit [Fintype σ] [LinearOrder σ] in
/--
@isnad1 id=eq.1h6v.s7.211978f1da54 from=translated src=- shape=d342f88e vocab=478920ed
-/
theorem offDiagonalBlock_sub_scalar {h : σ → ℕ}
    (C : Matrix (Index h) (Index h) ℂ) (α : ℂ) (a b : σ) (hab : a≠b) :
    block (C-α • 1) a b = block C a b := by
  ext i j
  have he : (⟨a,i⟩ : Index h) ≠ ⟨b,j⟩ := fun he => hab (congrArg Sigma.fst he)
  simp [block,he]

omit [Fintype σ] [LinearOrder σ] in
/--
@isnad1 id=eq.2h6v.s7.e3842a9170f0 from=translated src=- shape=c4cce1d9 vocab=d6305f04
-/
theorem lastRowForm_diagonal_rows {h : σ → ℕ}
    (C : Matrix (Index h) (Index h) ℂ) (hC : LastRowForm h C) (a : σ) :
    ∀ i j, i.val < h a → block C a a i j = if j.val=i.val+1 then 1 else 0 := by
  intro i j hi
  have hh := hC a ⟨i.val,hi⟩ ⟨a,j⟩
  change C ⟨a,i⟩ ⟨a,j⟩ = _
  simpa [Fin.ext_iff] using hh

omit [Fintype σ] [LinearOrder σ] in
/--
@isnad1 id=eq.3h7v.s6.569093b5ff43 from=translated src=- shape=1694efd1 vocab=7c1d2692
-/
theorem lastRowForm_offDiagonal_rows {h : σ → ℕ}
    (C : Matrix (Index h) (Index h) ℂ) (hC : LastRowForm h C)
    (a b : σ) (hab : a≠b) : ∀ i j, i.val < h a → block C a b i j=0 := by
  intro i j hi
  have hh := hC a ⟨i.val,hi⟩ ⟨b,j⟩
  have he : (⟨b,j⟩ : Index h) ≠ ⟨a,(⟨i.val,hi⟩ : Fin (h a)).succ⟩ :=
    fun he => hab (congrArg Sigma.fst he).symm
  change C ⟨a,i⟩ ⟨b,j⟩ = 0
  have hiEq : (⟨i.val,hi⟩ : Fin (h a)).castSucc=i := Fin.ext rfl
  simpa only [ite_eq_right he,hiEq] using hh

omit [Fintype σ] [LinearOrder σ] in
/-- The block conclusions give exactly the input format of the polynomial
pencil reduction, with no additional row-normalization premise.
@isnad1 id=lastrowf.2h3v.s7.dbd1ab123838 from=translated src=- shape=8a7cf6aa vocab=38cceded
-/
theorem lastRowForm_of_blocks {h : σ → ℕ}
    (T : Matrix (Index h) (Index h) ℂ)
    (hdiag : ∀ a, block T a a=WasowShiftReduction.shift (h a))
    (hoff : ∀ a b, a≠b → ∀ i j, i.val<h a → block T a b i j=0) :
    LastRowForm h T := by
  intro a i j
  rcases j with ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    change block T a a i.castSucc j = _
    rw [hdiag]
    simp [WasowShiftReduction.shift,Fin.ext_iff]
  · have he : (⟨b,j⟩ : Index h) ≠ ⟨a,i.succ⟩ :=
      fun he => hab (congrArg Sigma.fst he).symm
    rw [ite_eq_right he]
    exact hoff a b hab i.castSucc j i.isLt

/-- A single actual similarity simultaneously restores every diagonal
shift block and preserves every nonzero off-diagonal last-row block.
@isnad1 id=ex.3h4v.s10.373a1e5e5d00 from=translated src=- shape=cf2e9dcf vocab=1e52168f
-/
theorem exists_shift_diagonal_similarity {h : σ → ℕ}
    (C : Matrix (Index h) (Index h) ℂ) (α : ℂ)
    (hrows : LastRowForm h C) (hlower : LowerBlocks C)
    (hN : IsNilpotent (C-α • 1)) :
    ∃ L R T : Matrix (Index h) (Index h) ℂ,
      L*R=1 ∧ R*L=1 ∧ T=L*(C-α • 1)*R ∧
      (∀ a, block T a a=WasowShiftReduction.shift (h a)) ∧
      (∀ a b, a≠b → ∀ i j, i.val < h a → block T a b i j=0) ∧
      LowerBlocks T ∧
      (∀ a b, a≠b → (block T a b≠0 ↔ block C a b≠0)) := by
  have hnil (a : σ) : IsNilpotent (block C a a-α • 1) := by
    rw [← diagonalBlock_sub_scalar]
    exact diagonalBlock_nilpotent _ (lowerBlocks_sub_scalar C hlower α) hN a
  choose P Q hPQ hQP hsim hlast using fun a =>
    normalized_single_eigenvalue_similarity (block C a a) α
      (lastRowForm_diagonal_rows C hrows a) (hnil a)
  let L := Matrix.blockDiagonal' P
  let R := Matrix.blockDiagonal' Q
  let T := L*(C-α • 1)*R
  have hLR : L*R=1 := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [hPQ]
    change Matrix.blockDiagonal' (1 : ∀ a, Matrix (Fin (h a+1)) (Fin (h a+1)) ℂ)=1
    exact Matrix.blockDiagonal'_one
  have hRL : R*L=1 := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [hQP]
    change Matrix.blockDiagonal' (1 : ∀ a, Matrix (Fin (h a+1)) (Fin (h a+1)) ℂ)=1
    exact Matrix.blockDiagonal'_one
  have hb (a b : σ) : block T a b=P a*block (C-α • 1) a b*Q b := by
    change block (Matrix.blockDiagonal' P*(C-α • 1)*Matrix.blockDiagonal' Q) a b = _
    rw [block_mul_diagonal,block_diagonal_mul]
  have hoff (a b : σ) (hab : a≠b) : block T a b=block C a b*Q b := by
    rw [hb,offDiagonalBlock_sub_scalar C α a b hab,
      left_mul_last_row _ (hlast a) _ (lastRowForm_offDiagonal_rows C hrows a b hab)]
  refine ⟨L,R,T,hLR,hRL,rfl,?_,?_,?_,?_⟩
  · intro a
    rw [hb,diagonalBlock_sub_scalar]
    exact hsim a
  · intro a b hab
    rw [hoff a b hab]
    exact right_mul_last_row _ _ (lastRowForm_offDiagonal_rows C hrows a b hab)
  · intro i j hij
    have hab : i.1≠j.1 := ne_of_lt hij
    change block T i.1 j.1 i.2 j.2=0
    rw [hoff i.1 j.1 hab]
    have hz : block C i.1 j.1=0 := by
      ext k l
      exact hlower hij
    rw [hz,Matrix.zero_mul]
    rfl
  · intro a b hab
    rw [hoff a b hab]
    constructor
    · intro ht hc
      exact ht (by rw [hc,Matrix.zero_mul])
    · exact right_mul_nonzero _ _ _ (hQP b)

end WasowSingleEigenBlocks
