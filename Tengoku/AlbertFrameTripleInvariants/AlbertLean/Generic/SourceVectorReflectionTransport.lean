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

/--
@isnad1 id=eq.0h2v.s5.6e671188a5b8 from=translated src=- shape=d629a323 vocab=87101bf5
-/
theorem nV_neg (v : VCoord K) : nV (-v) = nV v := by
  rw [← neg_one_smul K v, nV_smul]
  ring

/--
@isnad1 id=eq.0h3v.s6.b5acfe3e15cf from=translated src=- shape=f4d93213 vocab=2127650f
-/
theorem BV_neg_left (v w : VCoord K) : BV (-v) w = -BV v w := by
  rw [← neg_one_smul K v, BV_smul_left]
  ring

/--
@isnad1 id=eq.0h3v.s6.07fb4367333f from=translated src=- shape=4d807bf5 vocab=2127650f
-/
theorem BV_neg_right (v w : VCoord K) : BV v (-w) = -BV v w := by
  rw [BV_symmetric, BV_neg_left, BV_symmetric w v]

/--
@isnad1 id=eq.0h3v.s6.87850e0eaa1c from=translated src=- shape=559c8b62 vocab=24894975
-/
theorem nV_sub (v w : VCoord K) :
    nV (v - w) = nV v + nV w - BV v w := by
  rw [sub_eq_add_neg, nV_add, nV_neg, BV_neg_right]
  ring

/--
@isnad1 id=eq.1h3v.s6.d709ad73d3fa from=translated src=- shape=11085d78 vocab=1d930749
-/
theorem difference_pairing (x y : VCoord K) (hn : nV x = nV y) :
    BV (x - y) x = nV (x - y) := by
  rw [nV_sub, sub_eq_add_neg, BV_add_left, BV_neg_left,
    BV_symmetric y x, ← hn, BV_self_eq_two_nV]
  ring

/-- If the difference is anisotropic, its reflection sends `x` to `y`.
@isnad1 id=eq.2h3v.s7.87a1b4387be3 from=translated src=- shape=df91e675 vocab=cbb57e06
-/
theorem reflect_difference (x y : VCoord K) (hn : nV x = nV y)
    (hd : nV (x - y) ≠ 0) :
    reflectV (x - y) x = y := by
  rw [reflectV, difference_pairing x y hn, div_self hd]
  module

/--
@isnad1 id=eq.2h3v.s7.48016f8976de from=translated src=- shape=6b6068ba vocab=24894975
-/
theorem sum_pairing (x y : VCoord K) (hn : nV x = nV y)
    (hd : nV (x - y) = 0) :
    BV (x + y) x = nV (x + y) := by
  have hxy : BV x y = 2 * nV x := by
    have h := nV_sub x y
    rw [hd, ← hn] at h
    linear_combination h
  rw [nV_add, BV_add_left, BV_self_eq_two_nV, BV_symmetric y x, hxy, hn]
  ring

/--
@isnad1 id=eq.2h3v.s7.8d4548eafc2f from=translated src=- shape=96f5c41f vocab=192e638c
-/
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
sends `x` to `-y`.
@isnad1 id=eq.3h3v.s7.398dd4bccbd2 from=translated src=- shape=5f9410dd vocab=6bb6081d
-/
theorem reflect_sum (x y : VCoord K) (hn : nV x = nV y)
    (hd : nV (x - y) = 0) (hs : nV (x + y) ≠ 0) :
    reflectV (x + y) x = -y := by
  rw [reflectV, sum_pairing x y hn hd, div_self hs]
  module

/--
@isnad1 id=eq.1h2v.s6.c7ed9fc8872b from=translated src=- shape=437a9d84 vocab=8cea1096
-/
theorem reflect_neg_self (y : VCoord K) (hy : nV y ≠ 0) :
    reflectV y (-y) = y := by
  have hcoef : BV y (-y) / nV y = (-2 : K) := by
    rw [BV_neg_right, BV_self_eq_two_nV]
    field_simp [hy]
  rw [reflectV, hcoef]
  module

/-- Equal nonzero norms have an explicit one- or two-reflection transport.
The disjunction records the actual anisotropic denominators used.
@isnad1 id=or.2h3v.s7.038100248ba5 from=translated src=- shape=829d66b5 vocab=ae3db609
-/
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
