import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.FrameIdeal
import Tengoku.Seed.Algebra.Field.Subfield.Basic
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms triple_mem_of_pair_sums` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrix_entries_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms determinant_sum_mem` (it only prints; the queue checks the axioms of every declaration). -/

/-!

The final triangular inverse of the paper's Appendix A, phrased entirely
as subfield membership. The scalar inputs are literal matrix measurements;
they are not assumed to generate an invariant field or the public ledger.
`ResidualSourceMeasurements.lean` derives their source-coordinate meanings.
-/

namespace AlbertLean.Generic.ResidualMomentSubfield

variable {K : Type*} [Field K]

/-- The determinant-two inverse used three times earlier in the paper's
dictionary: Gram entries, mixed trialities, then mixed-adjoint pairings.
@isnad1 id=and.3h5v.s7.4c05b36e9c8b from=translated src=- shape=b4eac0d5 vocab=e1f2cf34
-/
theorem triple_mem_of_pair_sums [CharZero K] (F : Subfield K) (x y z : K)
    (hxy : x + y ∈ F) (hyz : y + z ∈ F) (hzx : z + x ∈ F) :
    x ∈ F ∧ y ∈ F ∧ z ∈ F := by
  have h2 : (2 : K) ∈ F := by simpa using F.add_mem F.one_mem F.one_mem
  have hx : x = ((x + y) + (z + x) - (y + z)) / 2 := by ring
  have hy : y = ((x + y) + (y + z) - (z + x)) / 2 := by ring
  have hz : z = ((y + z) + (z + x) - (x + y)) / 2 := by ring
  constructor
  · rw [hx]
    exact F.div_mem (F.sub_mem (F.add_mem hxy hzx) hyz) h2
  constructor
  · rw [hy]
    exact F.div_mem (F.sub_mem (F.add_mem hxy hyz) hzx) h2
  · rw [hz]
    exact F.div_mem (F.sub_mem (F.add_mem hyz hzx) hxy) h2

/-- One Cramer inversion supplies every nontrivial step of the residual
moment inverse. This is independent of algebraic geometry and degree APIs.
@isnad1 id=and.7h8v.s8.a95f58d78b2e from=translated src=- shape=4b203298 vocab=a5b5ef06
-/
theorem pair_mem_of_linear_mem (F : Subfield K)
    (a b c d x y : K)
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hd : d ∈ F)
    (hdet : a * d - b * c ≠ 0)
    (hfirst : a * x + b * y ∈ F)
    (hsecond : c * x + d * y ∈ F) : x ∈ F ∧ y ∈ F := by
  have hx : x = (d * (a * x + b * y) - b * (c * x + d * y)) /
      (a * d - b * c) := by
    apply (eq_div_iff hdet).2
    ring
  have hy : y = (a * (c * x + d * y) - c * (a * x + b * y)) /
      (a * d - b * c) := by
    apply (eq_div_iff hdet).2
    ring
  have hden := F.sub_mem (F.mul_mem ha hd) (F.mul_mem hb hc)
  constructor
  · rw [hx]
    exact F.div_mem (F.sub_mem (F.mul_mem hd hfirst)
      (F.mul_mem hb hsecond)) hden
  · rw [hy]
    exact F.div_mem (F.sub_mem (F.mul_mem ha hsecond)
      (F.mul_mem hc hfirst)) hden

/-- Four diagonal norms, two Gram sums, eight mixed trialities and two
mixed-adjoint pairings recover all sixteen entries over the gauge field.
Only the orientation determinant must be nonzero.
@isnad1 id=mem.11h9v.s10.fb7a8763cf33 from=translated src=- shape=b1ec5934 vocab=0b14c6e5
-/
theorem matrix_entries_mem (F : Subfield K)
    (M : Matrix (Fin 4) (Fin 4) K) (r1 z1 r2 z2 : K)
    (hr1 : r1 ∈ F) (hz1 : z1 ∈ F) (hr2 : r2 ∈ F) (hz2 : z2 ∈ F)
    (hk : r1 * z2 - r2 * z1 ≠ 0)
    (hdiag : ∀ i, M i i ∈ F)
    (hS : M 0 1 + M 1 0 ∈ F)
    (hC : M 2 3 + M 3 2 ∈ F)
    (hUC : r1 * z2 * M 0 1 + r2 * z1 * M 1 0 ∈ F)
    (hUS : r2 * z1 * M 2 3 + r1 * z2 * M 3 2 ∈ F)
    (ht : ∀ i j, (i = 0 ∨ i = 1) → (j = 2 ∨ j = 3) →
      (r1 * M i j + z1 * M j i ∈ F) ∧
      (r2 * M i j + z2 * M j i ∈ F)) :
    ∀ i j, M i j ∈ F := by
  have hk' : r1 * z2 - z1 * r2 ≠ 0 := by
    simpa only [mul_comm z1 r2] using hk
  have h01 := pair_mem_of_linear_mem F 1 1 (r1 * z2) (r2 * z1)
    (M 0 1) (M 1 0) F.one_mem F.one_mem
    (F.mul_mem hr1 hz2) (F.mul_mem hr2 hz1)
    (by intro h; apply hk; linear_combination -h)
    (by simpa only [one_mul] using hS) hUC
  have h23 := pair_mem_of_linear_mem F 1 1 (r2 * z1) (r1 * z2)
    (M 2 3) (M 3 2) F.one_mem F.one_mem
    (F.mul_mem hr2 hz1) (F.mul_mem hr1 hz2)
    (by simpa only [one_mul] using hk)
    (by simpa only [one_mul] using hC) hUS
  have cross (i j : Fin 4) (hi : i = 0 ∨ i = 1) (hj : j = 2 ∨ j = 3) :
      M i j ∈ F ∧ M j i ∈ F :=
    pair_mem_of_linear_mem F r1 z1 r2 z2 (M i j) (M j i)
      hr1 hz1 hr2 hz2 hk' (ht i j hi hj).1 (ht i j hi hj).2
  have h02 := cross 0 2 (Or.inl rfl) (Or.inl rfl)
  have h03 := cross 0 3 (Or.inl rfl) (Or.inr rfl)
  have h12 := cross 1 2 (Or.inr rfl) (Or.inl rfl)
  have h13 := cross 1 3 (Or.inr rfl) (Or.inr rfl)
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hdiag _
    | exact h01.1 | exact h01.2 | exact h23.1 | exact h23.2
    | exact h02.1 | exact h02.2 | exact h03.1 | exact h03.2
    | exact h12.1 | exact h12.2 | exact h13.1 | exact h13.2

open AlbertLean.Residual.TrialitySquares

/--
@isnad1 id=mem.1h3v.s6.cb79813d1485 from=translated src=- shape=eac3c535 vocab=6375176f
-/
theorem exteriorQ_mem (F : Subfield K)
    (M : Matrix (Fin 4) (Fin 4) K) (h : ∀ i j, M i j ∈ F) :
    exteriorQ M ∈ F := by
  exact F.sub_mem
    (F.add_mem
      (F.sub_mem
        (F.add_mem (F.add_mem (F.mul_mem (h 2 0) (h 1 3))
          (F.mul_mem (h 3 1) (h 0 2))) (F.mul_mem (h 1 0) (h 3 2)))
        (F.mul_mem (h 1 2) (h 3 0)))
      (F.mul_mem (h 0 1) (h 2 3)))
    (F.mul_mem (h 0 3) (h 2 1))

/-- The already proved exterior identity supplies the final retained
symmetric determinant coordinate. No determinant expansion is needed.
@isnad1 id=mem.2h6v.s7.eee2cb4f4340 from=translated src=- shape=0535ce20 vocab=628a5d1b
-/
theorem determinant_sum_mem [CharZero K] (F : Subfield K)
    (s1 s2 : AlbertLean.Triality.ExteriorSix.SCoord K)
    (c1 c2 : AlbertLean.Triality.ExteriorSix.CCoord K)
    (hM : ∀ i j, momentMatrix s1 s2 c1 c2 i j ∈ F)
    (hUV : normalizedUV s1 s2 c1 c2 ∈ F) :
    deltaX s1 s2 c1 c2 + deltaStarA s1 s2 c1 c2 ∈ F := by
  have heq := normalizedUV_exterior_identity s1 s2 c1 c2
  have hs : deltaX s1 s2 c1 c2 + deltaStarA s1 s2 c1 c2 =
      exteriorQ (momentMatrix s1 s2 c1 c2) - normalizedUV s1 s2 c1 c2 := by
    rw [heq]
    ring
  rw [hs]
  exact F.sub_mem (exteriorQ_mem F _ hM) hUV

end AlbertLean.Generic.ResidualMomentSubfield
