import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ThreeIdempotents
import Tengoku.Seed.Tactic.Abel
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms encoder_identities` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms literal_projectors` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms trace_encoder` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# A cubic encoder from an ordered three-idempotent frame

Multiplication is commutative and distributive but
is not assumed associative. No Albert model is defined here.
-/

noncomputable section

namespace AlbertLean.Generic.FrameEncoder

open ThreeIdempotents

universe u v

section DivisionFree

variable {A : Type u} [NonAssocRing A]

/-- Division-free encoder closure for three idempotents summing to one. The
three final equalities are exactly the numerators of the usual spectral
projector formulas.-/
theorem encoder_identities
    (e0 e1 e2 : A)
    (hcomm : ∀ a b : A, a * b = b * a)
    (htwo : ∀ a : A, a + a = 0 → a = 0)
    (h0 : e0 * e0 = e0) (h1 : e1 * e1 = e1) (h2 : e2 * e2 = e2)
    (hsum : e0 + e1 + e2 = 1) :
    let x := e2 - e0
    x * x = e0 + e2 ∧
    x * (x * x) = x ∧
    x * x - x = e0 + e0 ∧
    1 - x * x = e1 ∧
    x * x + x = e2 + e2 := by
  dsimp only
  rcases pairwise_mul_eq_zero_of_sum_eq_one e0 e1 e2 hcomm htwo
      h0 h1 h2 hsum with ⟨h01, h02, h12⟩
  have h20 : e2 * e0 = 0 := by rw [hcomm, h02]
  have hxeq : (e2 - e0) * (e2 - e0) = e0 + e2 := by
    simp only [sub_mul, mul_sub, h0, h2, h02, h20, sub_zero, zero_sub]
    abel
  constructor
  · exact hxeq
  constructor
  · rw [hxeq]
    simp only [sub_mul, mul_add, h20, h2, h0, h02]
    abel
  constructor
  · rw [hxeq]
    abel
  constructor
  · rw [hxeq]
    calc
      1 - (e0 + e2) = (e0 + e1 + e2) - (e0 + e2) := by rw [hsum]
      _ = e1 := by abel
  · rw [hxeq]
    abel

end DivisionFree

section ProjectorsAndTrace

variable {K : Type u} {A : Type v}
variable [Field K] [NonAssocRing A] [Module K A]

/-- The division-free numerator identities recover the literal half-projector
formulas over a field in which two is nonzero.-/
theorem literal_projectors
    (e0 e1 e2 x : A) (htwoK : (2 : K) ≠ 0)
    (hminus : x * x - x = e0 + e0)
    (hmiddle : 1 - x * x = e1)
    (hplus : x * x + x = e2 + e2) :
    (2 : K)⁻¹ • (x * x - x) = e0 ∧
    1 - x * x = e1 ∧
    (2 : K)⁻¹ • (x * x + x) = e2 := by
  constructor
  · rw [hminus, ← two_smul K e0, smul_smul]
    simp [htwoK]
  constructor
  · exact hmiddle
  · rw [hplus, ← two_smul K e2, smul_smul]
    simp [htwoK]

omit [Module K A] in
/-- An additive trace taking value one on the two endpoint idempotents sends
the encoder to zero and its square to two.-/
theorem trace_encoder
    (trace : A →+ K) (e0 e2 x : A)
    (hx : x = e2 - e0) (hsquare : x * x = e0 + e2)
    (htr0 : trace e0 = 1)
    (htr2 : trace e2 = 1) :
    trace x = 0 ∧ trace (x * x) = 2 := by
  constructor
  · rw [hx, map_sub, htr2, htr0, sub_self]
  · rw [hsquare, map_add, htr0, htr2]
    norm_num

end ProjectorsAndTrace

end AlbertLean.Generic.FrameEncoder
