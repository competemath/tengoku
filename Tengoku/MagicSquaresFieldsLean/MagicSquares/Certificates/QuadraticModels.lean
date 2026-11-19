import Tengoku.MagicSquaresFieldsLean.MagicSquares.PrunedSearch
import Tengoku.MagicSquaresFieldsLean.MagicSquares.FieldTransport
import Tengoku.Seed.Algebra.QuadraticAlgebra.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.Certificates

instance quadraticFintype {R : Type*} [Fintype R] (a b : R) :
    Fintype (QuadraticAlgebra R a b) :=
  Fintype.ofEquiv (R × R) (QuadraticAlgebra.equivProd a b).symm

instance quadraticDecidableEq {R : Type*} [DecidableEq R] (a b : R) :
    DecidableEq (QuadraticAlgebra R a b) :=
  (QuadraticAlgebra.equivProd a b).injective.decidableEq

/--
@isnad1 id=eq.0h3v.s5.f353e1178749 from=translated src=- shape=7cdd011a vocab=5a19fca8
-/
@[simp] theorem quadratic_card {R : Type*} [Fintype R] (a b : R) :
    Fintype.card (QuadraticAlgebra R a b) = Fintype.card R ^ 2 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd a b), Fintype.card_prod, pow_two]

/-- A concrete model of the field with 25 elements, with `α² = 2`.-/
abbrev Field25 := QuadraticAlgebra (ZMod 5) 2 0

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (∀ r : ZMod 5, r ^ 2 ≠ 2 + 0 * r) := ⟨by decide +kernel⟩

/-- A concrete model of the field with 49 elements, with `α² = -1`.-/
abbrev Field49 := QuadraticAlgebra (ZMod 7) (-1) 0

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (∀ r : ZMod 7, r ^ 2 ≠ -1 + 0 * r) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The published `x = α` witness over the field of order 49.
@isnad1 id=ismagico.0h0v.s9.e3898fbc0ab2 from=translated src=- shape=5a5174db vocab=5a604e5b
-/
theorem square_witness_49 :
    IsMagicOfPowers 2 (Square3.centerZero (⟨0, 1⟩ : Field49)) := by
  apply (normalizedPowerConditions_iff (by decide : 0 < 2)
    (Square3.centerZero_isMagic _)).mp
  decide +kernel

end MagicSquares.Certificates
