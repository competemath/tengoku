import Tengoku.Nlalib.NLAlib.Matrix.Basic.PositiveDefiniteClosure
import Tengoku.Nlalib.NLAlib.ForMathlib.LinearAlgebra.Matrix.PrincipalMinorExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Principal minors and their fixed-cardinality products

The definitions are the subtype-indexed determinants and finite
products; their immediate positivity and continuity API supports Szász's
inequality. Source: Horn--Johnson (2013), Section 7.8;
supports `hadamard-fischer-inequalities`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder
namespace NLAlib
variable {n : Type*} [DecidableEq n]

/-- The principal minor `det A[S, S]` on a finite coordinate set `S` (Mathlib's block
determinant). The leading principal minors are `leadingMinor` (`Matrix/Basic/LeadingMinor.lean`).
Horn–Johnson 2013, §0.7.1 and §7.8; supports `hadamard-fischer-inequalities`.-/
def principalMinor (A : Matrix n n ℝ) (S : Finset n) : ℝ :=
  (A.toBlock (· ∈ S) (· ∈ S)).det

/-- A principal minor is exactly its Mathlib block determinant.
Horn--Johnson (2013), Section 7.8; definition bridge.
@isnad1 id=eq.0h3v.s6.feafc82845ae from=translated src=- shape=0b2aa071 vocab=83e9669e
-/
theorem principalMinor_eq_det_toBlock (A : Matrix n n ℝ) (S : Finset n) :
    principalMinor A S = (A.toBlock (· ∈ S) (· ∈ S)).det := rfl

/-- Every principal minor of a positive definite matrix is positive,
including the empty minor one. Horn--Johnson (2013), Section 7.8.
@isnad1 id=lt.1h3v.s5.a3df76f60e88 from=translated src=- shape=99e66a93 vocab=0ee0f4b7
-/
theorem principalMinor_pos {A : Matrix n n ℝ} (hA : A.PosDef) (S : Finset n) :
    0 < principalMinor A S :=
  (hA.submatrix (Subtype.val_injective : Function.Injective (Subtype.val : S → n))).det_pos

/-- Every principal minor of a PSD matrix is nonnegative.
Horn--Johnson (2013), Section 7.8.
@isnad1 id=le.1h3v.s5.81250b40953f from=translated src=- shape=99e66a93 vocab=8d4bd167
-/
theorem principalMinor_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) (S : Finset n) :
    0 ≤ principalMinor A S := (hA.submatrix (Subtype.val : S → n)).det_nonneg

/-- A fixed principal minor is continuous in its ambient matrix.
Horn--Johnson (2013), Section 7.8; immediate determinant continuity.
@isnad1 id=continuo.0h2v.s5.77edf32e5186 from=translated src=- shape=818c69d8 vocab=97864e33
-/
@[fun_prop] theorem continuous_principalMinor (S : Finset n) :
    Continuous (fun A : Matrix n n ℝ => principalMinor A S) := by
  unfold principalMinor Matrix.toBlock
  fun_prop

variable [Fintype n]

/-- Adding the identity to a PSD matrix gives determinant at least one, including
singular matrices and dimension zero. The principal-minor expansion supplies
nonnegative terms and the empty minor one. Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-law (partial)
@isnad1 id=le.1h2v.s6.83978c50b06c from=translated src=- shape=44767b68 vocab=fb211e35
-/
theorem _root_.Matrix.PosSemidef.one_le_det_one_add {L : Matrix n n ℝ}
    (hL : L.PosSemidef) : 1 ≤ (1 + L).det := by
  classical
  rw [Matrix.det_one_add_eq_sum_principal_minors]
  have h := Finset.single_le_sum (fun S (_ : S ∈ (Finset.univ : Finset (Finset n))) =>
    (hL.submatrix (Subtype.val : S → n)).det_nonneg) (Finset.mem_univ (∅ : Finset n))
  simpa only [Matrix.det_isEmpty] using h

/-- Product of every principal minor of a specified cardinality.
The empty product convention also defines it outside the dimension range.
Horn--Johnson (2013), Theorem 7.8.11; supports Szász's inequality.-/
def principalMinorProduct (A : Matrix n n ℝ) (k : ℕ) : ℝ :=
  ∏ S ∈ (Finset.univ : Finset n).powersetCard k, principalMinor A S

/-- The fixed-cardinality principal-minor product is its defining finite
product of determinants. Horn--Johnson (2013), Theorem 7.8.11.
@isnad1 id=eq.0h3v.s5.7e987f7985a1 from=translated src=- shape=91feedb1 vocab=484fe328
-/
theorem principalMinorProduct_eq_prod (A : Matrix n n ℝ) (k : ℕ) :
    principalMinorProduct A k = ∏ S ∈ (Finset.univ : Finset n).powersetCard k, principalMinor A S := rfl

/-- Principal-minor products of a positive definite matrix are positive.
Horn--Johnson (2013), Section 7.8.
@isnad1 id=lt.1h3v.s5.f489901bfe71 from=translated src=- shape=06f22004 vocab=c82d08c7
-/
theorem principalMinorProduct_pos {A : Matrix n n ℝ} (hA : A.PosDef) (k : ℕ) :
    0 < principalMinorProduct A k := Finset.prod_pos (fun S _ => principalMinor_pos hA S)

/-- Principal-minor products of a PSD matrix are nonnegative.
Horn--Johnson (2013), Section 7.8.
@isnad1 id=le.1h3v.s5.d13338795667 from=translated src=- shape=06f22004 vocab=b9264e89
-/
theorem principalMinorProduct_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) (k : ℕ) :
    0 ≤ principalMinorProduct A k := Finset.prod_nonneg (fun S _ => principalMinor_nonneg hA S)

/-- Each fixed-cardinality principal-minor product is continuous.
Horn--Johnson (2013), Section 7.8; immediate finite-product continuity.
@isnad1 id=continuo.0h2v.s5.40c2d9f64c55 from=translated src=- shape=eac86745 vocab=17ca60b5
-/
@[fun_prop] theorem continuous_principalMinorProduct (k : ℕ) :
    Continuous (fun A : Matrix n n ℝ => principalMinorProduct A k) := by
  unfold principalMinorProduct
  fun_prop

omit [Fintype n] in
/-- Deleting a coordinate inside a principal block gives the corresponding
erased principal minor of the ambient matrix, with an explicit subtype
equivalence. Horn--Johnson (2013), Lemma 7.8.8.
@isnad1 id=eq.0h4v.s9.a9028e087388 from=translated src=- shape=4241e134 vocab=6313af7b
-/
theorem det_toBlock_complement_eq_principalMinor_erase
    (A : Matrix n n ℝ) (T : Finset n) (i : T) :
    ((A.toBlock (· ∈ T) (· ∈ T)).toBlock (fun j => j ≠ i) (fun j => j ≠ i)).det =
      principalMinor A (T.erase i.val) := by
  classical
  let e : {j : T // j ≠ i} ≃ (T.erase i.val : Finset n) :=
    { toFun := fun j => ⟨j.val.val, Finset.mem_erase.mpr
        ⟨fun h => j.property (Subtype.ext h), j.val.property⟩⟩
      invFun := fun j => ⟨⟨j.val, (Finset.mem_erase.mp j.property).2⟩,
        fun h => (Finset.mem_erase.mp j.property).1 (congrArg Subtype.val h)⟩
      left_inv := by intro j; rfl
      right_inv := by intro j; rfl }
  have he : (A.toBlock (· ∈ T.erase i.val) (· ∈ T.erase i.val)).submatrix e e =
      (A.toBlock (· ∈ T) (· ∈ T)).toBlock (fun j => j ≠ i) (fun j => j ≠ i) := by
    rfl
  rw [← he, Matrix.det_submatrix_equiv_self]
  rfl

end NLAlib
