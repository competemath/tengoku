import Tengoku.Seed.LinearAlgebra.Matrix.RowCol
import Tengoku.Seed.LinearAlgebra.Matrix.PosDef
import Tengoku.Seed.Analysis.RCLike.Basic
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Piecewise
import Tengoku.Seed.Data.List.OfFn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Gram matrices of finite row lists and zero-row insertion

These are finite matrix identities for row-stream algorithms. Replacing a zero row
adds exactly the incoming row Gram matrix; no rank or nonzero condition is needed.
-/

noncomputable section
open scoped Matrix
namespace Matrix

/-- Interpret a finite row list as its positional rectangular matrix.-/
def ofRowList {n α : Type*} (rows : List (n → α)) : Matrix (Fin rows.length) n α :=
  fun i => rows.get i

variable {𝕜 m n : Type*} [RCLike 𝕜]

/-- The Gram matrix of a row list is the finite sum of its individual row Grams.
@isnad1 id=eq.0h3v.s8.0c98ef9c6350 from=translated src=- shape=a0b432d8 vocab=095eea1f
-/
theorem conjTranspose_ofRowList_mul_ofRowList (rows : List (n → 𝕜)) :
    (ofRowList rows)ᴴ * ofRowList rows =
      (rows.map (fun a => vecMulVec (star a) a)).sum := by
  have hm : (rows.map (fun a => vecMulVec (star a) a)).sum =
      ∑ i : Fin rows.length, vecMulVec (star (rows.get i)) (rows.get i) := by
    rw [← List.ofFn_getElem_eq_map rows (fun a => vecMulVec (star a) a), List.sum_ofFn]
    rfl
  rw [hm]
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, ofRowList]

/-- The native positional row enumeration has the original Gram matrix.
@isnad1 id=eq.0h4v.s8.f1c26e3bcfdd from=translated src=- shape=07a02aba vocab=4be3b85a
-/
theorem sum_rowGrams_ofFn {N : ℕ} (A : Matrix (Fin N) n 𝕜) :
    ((List.ofFn (fun i => A i)).map (fun a => vecMulVec (star a) a)).sum = Aᴴ * A := by
  rw [List.map_ofFn, List.sum_ofFn]
  ext j k
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Function.comp_apply, Matrix.vecMulVec_apply, Pi.star_apply]

/-- Inserting a row into a zero row adds its Gram exactly. This is the source of the
Frequent Directions covariance invariant, including zero incoming rows.
@isnad1 id=eq.1h6v.s8.9ba67328e5d5 from=translated src=- shape=6964c55c vocab=35184767
-/
theorem conjTranspose_updateRow_mul_updateRow_eq_add [Fintype m] [DecidableEq m]
    (B : Matrix m n 𝕜) (i : m) (a : n → 𝕜) (hi : B i = 0) :
    (B.updateRow i a)ᴴ * B.updateRow i a = Bᴴ * B + vecMulVec (star a) a := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, Pi.star_apply]
  rw [← Finset.sum_erase_add Finset.univ
    (fun t => star ((B.updateRow i a) t j) * (B.updateRow i a) t k) (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ
    (fun t => star (B t j) * B t k) (Finset.mem_univ i)]
  have he : (∑ t ∈ Finset.univ.erase i,
      star ((B.updateRow i a) t j) * (B.updateRow i a) t k) =
      ∑ t ∈ Finset.univ.erase i, star (B t j) * B t k := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Matrix.updateRow_ne (Finset.mem_erase.mp ht).1]
  rw [he]
  simp only [Matrix.updateRow_self, hi, Pi.zero_apply, star_zero, zero_mul, add_zero]

end Matrix
