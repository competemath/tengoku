module

public import Tengoku.Seed.LinearAlgebra.Matrix.Block
public import Tengoku.Seed.Algebra.BigOperators.Fin
public import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Maximal minors of the bidiagonal Ferrers relation matrix. -/

namespace ChoppedPlane

open scoped BigOperators

variable {R : Type*} [CommRing R] {c : ℕ}

/-- The rectangular relation matrix, with diagonal entries `f` and the entries
immediately below the diagonal `g`.-/
def ferrersBidiagonal (f g : Fin (c + 1) → R) : Matrix (Fin (c + 1)) (Fin c) R :=
  fun i j => if i.val = j.val then f i else if i.val = j.val + 1 then g i else 0

/-- The square maximal minor obtained by deleting row `k`, keeping the natural
order of the remaining rows.-/
def ferrersDeletedRow (f g : Fin (c + 1) → R) (k : Fin (c + 1)) :
    Matrix (Fin c) (Fin c) R :=
  (ferrersBidiagonal f g).submatrix k.succAbove id

/--
@isnad1 id=eq.1h7v.s7.263a2ff89581 from=translated src=- shape=ad25ac29 vocab=fd3f68e7
-/
theorem ferrersDeletedRow_before (f g : Fin (c + 1) → R) (k : Fin (c + 1))
    (i j : Fin c) (hi : i.val < k.val) :
    ferrersDeletedRow f g k i j =
      if i.val = j.val then f i.castSucc else if i.val = j.val + 1 then g i.castSucc else 0 := by
  rw [ferrersDeletedRow, Matrix.submatrix_apply, Fin.succAbove_of_castSucc_lt]
  · rfl
  · exact hi

/--
@isnad1 id=eq.1h7v.s7.775b9d9f5f1a from=translated src=- shape=ea0619f1 vocab=64cf1aea
-/
theorem ferrersDeletedRow_after (f g : Fin (c + 1) → R) (k : Fin (c + 1))
    (i j : Fin c) (hi : ¬i.val < k.val) :
    ferrersDeletedRow f g k i j =
      if i.val + 1 = j.val then f i.succ else if i.val = j.val then g i.succ else 0 := by
  rw [ferrersDeletedRow, Matrix.submatrix_apply, Fin.succAbove_of_le_castSucc]
  · simp [ferrersBidiagonal]
  · exact Nat.le_of_not_gt hi

/-- The deleted matrix separates into a lower triangular block before the hole
and an upper triangular block after the hole.
@isnad1 id=eq.0h5v.s8.c567f5b865f2 from=translated src=- shape=79c37938 vocab=92c34c9e
-/
theorem ferrersDeletedRow_det_subtype (f g : Fin (c + 1) → R) (k : Fin (c + 1)) :
    (ferrersDeletedRow f g k).det =
      (∏ i : {i : Fin c // i.val < k.val}, f i.val.castSucc) *
      (∏ i : {i : Fin c // ¬i.val < k.val}, g i.val.succ) := by
  classical
  let A := ferrersDeletedRow f g k
  let p : Fin c → Prop := fun i => i.val < k.val
  have hsplit : ∀ i, ¬p i → ∀ j, p j → A i j = 0 := by
    intro i hi j hj
    change ferrersDeletedRow f g k i j = 0
    rw [ferrersDeletedRow_after f g k i j hi]
    simp only [p] at hj
    have hij : i.val ≠ j.val := by omega
    have hij' : i.val + 1 ≠ j.val := by omega
    simp [hij, hij']
  rw [Matrix.twoBlockTriangular_det A p hsplit]
  have hleft : (A.toSquareBlockProp p).IsLowerTriangular := by
    intro i j hij
    change ferrersDeletedRow f g k i.val j.val = 0
    rw [ferrersDeletedRow_before f g k i.val j.val i.property]
    have hijv : i.val.val < j.val.val := hij
    have hne : i.val.val ≠ j.val.val := by omega
    have hne' : i.val.val ≠ j.val.val + 1 := by omega
    simp [hne, hne']
  have hright : (A.toSquareBlockProp (fun i => ¬p i)).IsUpperTriangular := by
    intro i j hij
    change ferrersDeletedRow f g k i.val j.val = 0
    rw [ferrersDeletedRow_after f g k i.val j.val i.property]
    have hijv : j.val.val < i.val.val := hij
    have hne : i.val.val ≠ j.val.val := by omega
    have hne' : i.val.val + 1 ≠ j.val.val := by omega
    simp [hne, hne']
  rw [Matrix.det_of_isLowerTriangular _ hleft, Matrix.det_of_isUpperTriangular hright]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    change ferrersDeletedRow f g k i.val i.val = f i.val.castSucc
    rw [ferrersDeletedRow_before f g k i.val i.val i.property]
    simp
  · apply Finset.prod_congr rfl
    intro i _
    change ferrersDeletedRow f g k i.val i.val = g i.val.succ
    rw [ferrersDeletedRow_after f g k i.val i.val i.property]
    simp

private def ferrersBeforeRowEquiv (k : Fin (c + 1)) :
    {i : Fin c // i.val < k.val} ≃ {i : Fin (c + 1) // i.val < k.val} where
  toFun i := ⟨i.val.castSucc, i.property⟩
  invFun i := ⟨⟨i.val.val, by have := k.isLt; have := i.property; omega⟩, i.property⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv i := by apply Subtype.ext; apply Fin.ext; rfl

private def ferrersAfterRowEquiv (k : Fin (c + 1)) :
    {i : Fin c // ¬i.val < k.val} ≃ {i : Fin (c + 1) // k.val < i.val} where
  toFun i := ⟨i.val.succ, by have := i.property; simp only [Fin.val_succ]; omega⟩
  invFun i := ⟨⟨i.val.val - 1, by have := i.val.isLt; have := i.property; omega⟩,
    by change ¬i.val.val - 1 < k.val; have := i.property; omega⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; simp
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have := i.property
    simp only [Fin.val_succ]
    omega

/-- The ordered maximal minor has no sign factor: it is the product of the
diagonal entries before the deleted row and the subdiagonal entries after it.
@isnad1 id=eq.0h5v.s8.80c0e888b79b from=translated src=- shape=52319268 vocab=21a5a779
-/
theorem ferrersDeletedRow_det (f g : Fin (c + 1) → R) (k : Fin (c + 1)) :
    (ferrersDeletedRow f g k).det =
      (∏ i ∈ Finset.univ.filter (fun i : Fin (c + 1) => i.val < k.val), f i) *
      (∏ i ∈ Finset.univ.filter (fun i : Fin (c + 1) => k.val < i.val), g i) := by
  classical
  rw [ferrersDeletedRow_det_subtype]
  congr 1
  · rw [Fintype.prod_equiv (ferrersBeforeRowEquiv k)
      (fun i => f i.val.castSucc) (fun i => f i.val) (fun _ => rfl)]
    exact (Finset.prod_subtype _ (by simp) f).symm
  · rw [Fintype.prod_equiv (ferrersAfterRowEquiv k)
      (fun i => g i.val.succ) (fun i => g i.val) (fun _ => rfl)]
    exact (Finset.prod_subtype _ (by simp) g).symm

/-- Signed maximal minors use the usual alternating row convention.-/
def ferrersSignedCofactor (f g : Fin (c + 1) → R) (k : Fin (c + 1)) : R :=
  (-1) ^ k.val * (ferrersDeletedRow f g k).det

/--
@isnad1 id=eq.0h5v.s8.40fb0c6bbb92 from=translated src=- shape=1c744b3b vocab=091db381
-/
theorem ferrersSignedCofactor_eq (f g : Fin (c + 1) → R) (k : Fin (c + 1)) :
    ferrersSignedCofactor f g k = (-1) ^ k.val *
      ((∏ i ∈ Finset.univ.filter (fun i : Fin (c + 1) => i.val < k.val), f i) *
       (∏ i ∈ Finset.univ.filter (fun i : Fin (c + 1) => k.val < i.val), g i)) := by
  rw [ferrersSignedCofactor, ferrersDeletedRow_det]

end ChoppedPlane
