import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairReflection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms evenV_eq_of_centers` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenV_eq_fixing` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Triality.SourceVectorPairDephase

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceEvenReflections SourceVectorReflectionTransport SourceVectorPairReflection

universe u
variable {K : Type u} [Field K] [CharZero K]

theorem evenV_eq_of_centers (e x y : VCoord K)
    (he : nV e ≠ 0) (hxy : nV x = nV y) (hx : nV x ≠ 0)
    (hey : BV e y = 0) :
    ∃ A B : VCoord K,
      nV A ≠ 0 ∧ nV B ≠ 0 ∧ evenV A B x = y := by
  by_cases hd : nV (x - y) = 0
  · have hy : nV y ≠ 0 := by simpa only [← hxy] using hx
    have hs : nV (x + y) ≠ 0 := by
      rw [nV_sum_eq_four x y hxy hd]
      exact mul_ne_zero (by norm_num) hx
    refine ⟨y, x + y, hy, hs, ?_⟩
    rw [evenV, reflect_sum x y hxy hd hs, reflect_neg_self y hy]
  · refine ⟨e, x - y, he, hd, ?_⟩
    rw [evenV, reflect_difference x y hxy hd,
      reflectV_eq_of_orthogonal e y hey]

theorem evenV_eq_fixing (e f x y : VCoord K)
    (he : nV e ≠ 0) (hxy : nV x = nV y) (hx : nV x ≠ 0)
    (hey : BV e y = 0) (hfe : BV f e = 0)
    (hfx : BV f x = 0) (hfy : BV f y = 0) :
    ∃ A B : VCoord K,
      nV A ≠ 0 ∧ nV B ≠ 0 ∧ BV f A = 0 ∧ BV f B = 0 ∧
      evenV A B x = y ∧ evenV A B f = f := by
  by_cases hd : nV (x - y) = 0
  · have hy : nV y ≠ 0 := by simpa only [← hxy] using hx
    have hs : nV (x + y) ≠ 0 := by
      rw [nV_sum_eq_four x y hxy hd]
      exact mul_ne_zero (by norm_num) hx
    refine ⟨y, x + y, hy, hs, hfy, ?_, ?_, ?_⟩
    · rw [BV_add_right, hfx, hfy, add_zero]
    · rw [evenV, reflect_sum x y hxy hd hs, reflect_neg_self y hy]
    · rw [evenV, reflectV_eq_of_orthogonal (x + y) f,
        reflectV_eq_of_orthogonal y f]
      · rw [BV_symmetric, hfy]
      · rw [BV_symmetric, BV_add_right, hfx, hfy, add_zero]
  · refine ⟨e, x - y, he, hd, hfe, ?_, ?_, ?_⟩
    · rw [sub_eq_add_neg, BV_add_right, BV_neg_right, hfx, hfy]
      simp
    · rw [evenV, reflect_difference x y hxy hd,
        reflectV_eq_of_orthogonal e y hey]
    · rw [evenV, reflectV_eq_of_orthogonal (x - y) f,
        reflectV_eq_of_orthogonal e f]
      · rw [BV_symmetric, hfe]
      · rw [BV_symmetric, sub_eq_add_neg, BV_add_right, BV_neg_right,
          hfx, hfy]
        simp

end AlbertLean.Triality.SourceVectorPairDephase
