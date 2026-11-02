import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

private theorem productForm_add_left (x₁ x₂ y : Coord) :
    productForm (x₁ + x₂) y = productForm x₁ y + productForm x₂ y := by
  funext k
  fin_cases k <;> simp [productForm, v, q] <;> ring

private theorem productForm_smul_left (a : ℚ) (x y : Coord) :
    productForm (a • x) y = a • productForm x y := by
  funext k
  fin_cases k <;> simp [productForm, v, q] <;> ring

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
theorem productForm_commutative (x y : Coord) :
    productForm x y = productForm y x := by
  funext k
  fin_cases k <;> simp [productForm, v, q] <;> ring

theorem productQBilinear : IsQBilinear structuredProduct := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x₁ x₂ y
    simp only [structuredProduct_eq_productForm]
    exact productForm_add_left x₁ x₂ y
  · intro a x y
    simp only [structuredProduct_eq_productForm]
    exact productForm_smul_left a x y
  · intro x y₁ y₂
    simp only [structuredProduct_eq_productForm]
    rw [productForm_commutative x (y₁ + y₂), productForm_add_left,
      productForm_commutative y₁ x, productForm_commutative y₂ x]
  · intro a x y
    simp only [structuredProduct_eq_productForm]
    rw [productForm_commutative x (a • y), productForm_smul_left,
      productForm_commutative y x]

theorem productCommutative (x y : Coord) :
    structuredProduct x y = structuredProduct y x := by
  rw [structuredProduct_eq_productForm,
    structuredProduct_eq_productForm]
  exact productForm_commutative x y

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
theorem productForm_one_left (x : Coord) : productForm one x = x := by
  funext k
  fin_cases k <;> simp [productForm, one, v, q] <;> ring

theorem unitLaw (x : Coord) :
    structuredProduct one x = x ∧ structuredProduct x one = x := by
  constructor
  · rw [structuredProduct_eq_productForm]
    exact productForm_one_left x
  · rw [productCommutative x one, structuredProduct_eq_productForm]
    exact productForm_one_left x

end AlbertLean
