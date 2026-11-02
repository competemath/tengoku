import Tengoku.AlbertFrameTripleInvariants.AlbertLean.JordanLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

private theorem product_sub_left (x y z : Coord) :
    structuredProduct (x - y) z = structuredProduct x z - structuredProduct y z := by
  rw [sub_eq_add_neg, productQBilinear.1]
  rw [show -y = (-1 : ℚ) • y by simp]
  rw [productQBilinear.2.1]
  simp
  rw [sub_eq_add_neg]

private theorem product_sub_right (x y z : Coord) :
    structuredProduct x (y - z) = structuredProduct x y - structuredProduct x z := by
  rw [sub_eq_add_neg, productQBilinear.2.2.1]
  rw [show -z = (-1 : ℚ) • z by simp]
  rw [productQBilinear.2.2.2]
  simp
  rw [sub_eq_add_neg]

private theorem product_smul_left (a : ℚ) (x y : Coord) :
    structuredProduct (a • x) y = a • structuredProduct x y :=
  productQBilinear.2.1 a x y

private theorem product_smul_right (a : ℚ) (x y : Coord) :
    structuredProduct x (a • y) = a • structuredProduct x y :=
  productQBilinear.2.2.2 a x y

private theorem encoder_cube (c : Coord) (hc : LawfulEncoder c) :
    structuredProduct c (structuredProduct c c) = c := by
  rcases hc with ⟨hT, hS, hN⟩
  have h := characteristicIdentity c
  rw [hT, hS, hN] at h
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg] using h

private theorem encoder_square_idempotent (c : Coord) (hc : LawfulEncoder c) :
    structuredProduct (structuredProduct c c) (structuredProduct c c) =
      structuredProduct c c := by
  have h := jordanIdentity c c
  rw [encoder_cube c hc] at h
  exact h

theorem lawfulFrame_of_lawfulEncoder (c : Coord) (hc : LawfulEncoder c) :
    LawfulFrame c := by
  let a := structuredProduct c c
  have hcube : structuredProduct c a = c := encoder_cube c hc
  have hsquare : structuredProduct a a = a := encoder_square_idempotent c hc
  have hac : structuredProduct a c = c := by
    rw [productCommutative]
    exact hcube
  have hTa : traceN a = 2 := by
    rw [traceN_structuredProduct_eq_traceForm]
    have hT := hc.1
    have hS := hc.2.1
    have hSB : spurBilinear c c = -2 := by
      unfold spurN at hS
      unfold spurBilinear
      linarith
    rw [traceForm, hT, hSB]
    norm_num
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · constructor
      · change structuredProduct ((2 : ℚ)⁻¹ • (a - c)) ((2 : ℚ)⁻¹ • (a - c)) =
          (2 : ℚ)⁻¹ • (a - c)
        rw [product_smul_left, product_smul_right, product_sub_left,
          product_sub_right, product_sub_right, hsquare, hac, hcube]
        norm_num
        module
      · change traceN ((2 : ℚ)⁻¹ • (a - c)) = 1
        rw [traceN_smul, traceN_sub, hTa, hc.1]
        norm_num
    · constructor
      · change structuredProduct (one - a) (one - a) = one - a
        rw [product_sub_left, product_sub_right, product_sub_right,
          (unitLaw one).1, (unitLaw a).1, (unitLaw a).2, hsquare]
        module
      · change traceN (one - a) = 1
        rw [traceN_sub, traceN_one, hTa]
        norm_num
    · constructor
      · change structuredProduct ((2 : ℚ)⁻¹ • (a + c)) ((2 : ℚ)⁻¹ • (a + c)) =
          (2 : ℚ)⁻¹ • (a + c)
        rw [product_smul_left, product_smul_right, productQBilinear.1,
          productQBilinear.2.2.1, productQBilinear.2.2.1,
          hsquare, hac, hcube]
        norm_num
        module
      · change traceN ((2 : ℚ)⁻¹ • (a + c)) = 1
        rw [traceN_smul, traceN_add, hTa, hc.1]
        norm_num
  · have hp01 : structuredProduct (projector c 0) (projector c 1) = 0 := by
      change structuredProduct ((2 : ℚ)⁻¹ • (a - c)) (one - a) = 0
      rw [product_smul_left, product_sub_left, product_sub_right,
        product_sub_right, (unitLaw a).2, hsquare, (unitLaw c).2, hcube]
      module
    have hp02 : structuredProduct (projector c 0) (projector c 2) = 0 := by
      change structuredProduct ((2 : ℚ)⁻¹ • (a - c))
        ((2 : ℚ)⁻¹ • (a + c)) = 0
      rw [product_smul_left, product_smul_right, product_sub_left,
        productQBilinear.2.2.1, productQBilinear.2.2.1,
        hsquare, hac, hcube]
      norm_num
      module
    have hp12 : structuredProduct (projector c 1) (projector c 2) = 0 := by
      change structuredProduct (one - a) ((2 : ℚ)⁻¹ • (a + c)) = 0
      rw [product_smul_right, productQBilinear.2.2.1,
        product_sub_left, product_sub_left,
        (unitLaw a).1, hsquare, (unitLaw c).1, hac]
      module
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hp01
    · exact hp02
    · rw [productCommutative]
      exact hp01
    · exact (hij rfl).elim
    · exact hp12
    · rw [productCommutative]
      exact hp02
    · rw [productCommutative]
      exact hp12
    · exact (hij rfl).elim
  · change (2 : ℚ)⁻¹ • (a - c) + (one - a) + (2 : ℚ)⁻¹ • (a + c) = one
    norm_num
    module
  · change (2 : ℚ)⁻¹ • (a + c) - (2 : ℚ)⁻¹ • (a - c) = c
    norm_num
    module

end AlbertLean
