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
/--
@isnad1 id=eq.0h2v.s3.1c8186bdf725 from=translated src=- shape=1013c0ce vocab=c3740baa
-/
theorem productForm_commutative (x y : Coord) :
    productForm x y = productForm y x := by
  funext k
  fin_cases k <;> simp [productForm, v, q] <;> ring

/--
@isnad1 id=isqbilin.0h0v.s1.d962d3c18c1a from=translated src=- shape=49959d42 vocab=6cb65a4e
-/
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

/--
@isnad1 id=eq.0h2v.s3.065f6f382fe8 from=translated src=- shape=1013c0ce vocab=55ab3ef6
-/
theorem productCommutative (x y : Coord) :
    structuredProduct x y = structuredProduct y x := by
  rw [structuredProduct_eq_productForm,
    structuredProduct_eq_productForm]
  exact productForm_commutative x y

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s3.d5ce629e6dcc from=translated src=- shape=29edb2d9 vocab=ae27ca31
-/
theorem productForm_one_left (x : Coord) : productForm one x = x := by
  funext k
  fin_cases k <;> simp [productForm, one, v, q] <;> ring

/--
@isnad1 id=and.0h1v.s3.47937b10b1d2 from=translated src=- shape=b0371990 vocab=87022af2
-/
theorem unitLaw (x : Coord) :
    structuredProduct one x = x ∧ structuredProduct x one = x := by
  constructor
  · rw [structuredProduct_eq_productForm]
    exact productForm_one_left x
  · rw [productCommutative x one, structuredProduct_eq_productForm]
    exact productForm_one_left x

end AlbertLean
