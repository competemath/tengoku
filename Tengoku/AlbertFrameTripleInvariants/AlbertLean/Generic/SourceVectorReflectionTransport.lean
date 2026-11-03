import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceEvenReflections
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms reflect_difference` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms nV_sum_eq_four` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_reflection_transport` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Householder transport for one anisotropic source vector.  The witnesses are
explicit (`x - y`, or `x + y` followed by `y`), so no abstract orthogonal-group
or complement argument enters.
-/

noncomputable section
namespace AlbertLean.Triality.SourceVectorReflectionTransport

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceEvenReflections

universe u
variable {K : Type u} [Field K] [CharZero K]

theorem nV_neg (v : VCoord K) : nV (-v) = nV v := by
  rw [← neg_one_smul K v, nV_smul]
  ring

theorem BV_neg_left (v w : VCoord K) : BV (-v) w = -BV v w := by
  rw [← neg_one_smul K v, BV_smul_left]
  ring

theorem BV_neg_right (v w : VCoord K) : BV v (-w) = -BV v w := by
  rw [BV_symmetric, BV_neg_left, BV_symmetric w v]

theorem nV_sub (v w : VCoord K) :
    nV (v - w) = nV v + nV w - BV v w := by
  rw [sub_eq_add_neg, nV_add, nV_neg, BV_neg_right]
  ring

theorem difference_pairing (x y : VCoord K) (hn : nV x = nV y) :
    BV (x - y) x = nV (x - y) := by
  rw [nV_sub, sub_eq_add_neg, BV_add_left, BV_neg_left,
    BV_symmetric y x, ← hn, BV_self_eq_two_nV]
  ring

/-- If the difference is anisotropic, its reflection sends `x` to `y`.-/
theorem reflect_difference (x y : VCoord K) (hn : nV x = nV y)
    (hd : nV (x - y) ≠ 0) :
    reflectV (x - y) x = y := by
  rw [reflectV, difference_pairing x y hn, div_self hd]
  module

theorem sum_pairing (x y : VCoord K) (hn : nV x = nV y)
    (hd : nV (x - y) = 0) :
    BV (x + y) x = nV (x + y) := by
  have hxy : BV x y = 2 * nV x := by
    have h := nV_sub x y
    rw [hd, ← hn] at h
    linear_combination h
  rw [nV_add, BV_add_left, BV_self_eq_two_nV, BV_symmetric y x, hxy, hn]
  ring

theorem nV_sum_eq_four (x y : VCoord K) (hn : nV x = nV y)
    (hd : nV (x - y) = 0) :
    nV (x + y) = 4 * nV x := by
  have hxy : BV x y = 2 * nV x := by
    have h := nV_sub x y
    rw [hd, ← hn] at h
    linear_combination h
  rw [nV_add, ← hn, hxy]
  ring

/-- In the isotropic-difference branch, reflection in the anisotropic sum
sends `x` to `-y`.-/
theorem reflect_sum (x y : VCoord K) (hn : nV x = nV y)
    (hd : nV (x - y) = 0) (hs : nV (x + y) ≠ 0) :
    reflectV (x + y) x = -y := by
  rw [reflectV, sum_pairing x y hn hd, div_self hs]
  module

theorem reflect_neg_self (y : VCoord K) (hy : nV y ≠ 0) :
    reflectV y (-y) = y := by
  have hcoef : BV y (-y) / nV y = (-2 : K) := by
    rw [BV_neg_right, BV_self_eq_two_nV]
    field_simp [hy]
  rw [reflectV, hcoef]
  module

/-- Equal nonzero norms have an explicit one- or two-reflection transport.
The disjunction records the actual anisotropic denominators used.-/
theorem exists_reflection_transport (x y : VCoord K)
    (hn : nV x = nV y) (hx : nV x ≠ 0) :
    (∃ a, nV a ≠ 0 ∧ reflectV a x = y) ∨
      (∃ a b, nV a ≠ 0 ∧ nV b ≠ 0 ∧ reflectV b (reflectV a x) = y) := by
  by_cases hd : nV (x - y) = 0
  · have hy : nV y ≠ 0 := by
      intro hy0
      apply hx
      rw [hn, hy0]
    have hs : nV (x + y) ≠ 0 := by
      rw [nV_sum_eq_four x y hn hd]
      exact mul_ne_zero (by norm_num) hx
    right
    refine ⟨x + y, y, hs, hy, ?_⟩
    rw [reflect_sum x y hn hd hs, reflect_neg_self y hy]
  · left
    exact ⟨x - y, hd, reflect_difference x y hn hd⟩

end AlbertLean.Triality.SourceVectorReflectionTransport
