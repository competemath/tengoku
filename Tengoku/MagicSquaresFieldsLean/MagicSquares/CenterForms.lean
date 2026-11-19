import Tengoku.MagicSquaresFieldsLean.MagicSquares.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {R : Type*} [CommRing R]

/-- The center-zero one-parameter family `M₀(x)` used in Section 6.-/
def centerZero (x : R) : Square3 R :=
  parametrized 0 x 1

/-- The center-one two-parameter family used in Sections 7 and 14.-/
def centerOne (u v : R) : Square3 R :=
  parametrized 1 u v

/-- The flexible center-one line `u = t`, `v = b t`.-/
def centerOneLine (t b : R) : Square3 R :=
  centerOne t (b * t)

@[simp] theorem centerZero_a (x : R) : (centerZero x).a = x := by
  simp [centerZero, parametrized]
@[simp] theorem centerZero_b (x : R) : (centerZero x).b = -x - 1 := by
  simp [centerZero, parametrized]
@[simp] theorem centerZero_c (x : R) : (centerZero x).c = 1 := by
  simp [centerZero, parametrized]
@[simp] theorem centerZero_d (x : R) : (centerZero x).d = 1 - x := by
  simp [centerZero, parametrized]; ring
@[simp] theorem centerZero_e (x : R) : (centerZero x).e = 0 := by
  simp [centerZero, parametrized]
@[simp] theorem centerZero_f (x : R) : (centerZero x).f = x - 1 := by
  simp [centerZero, parametrized]
@[simp] theorem centerZero_g (x : R) : (centerZero x).g = -1 := by
  simp [centerZero, parametrized]
@[simp] theorem centerZero_h (x : R) : (centerZero x).h = x + 1 := by
  simp [centerZero, parametrized]
@[simp] theorem centerZero_i (x : R) : (centerZero x).i = -x := by
  simp [centerZero, parametrized]

/-- The center-zero family is automatically magic.-/
theorem centerZero_isMagic (x : R) : IsMagic (centerZero x) := by
  exact parametrized_isMagic 0 x 1

/-- The center-one family is automatically magic.-/
theorem centerOne_isMagic (u v : R) : IsMagic (centerOne u v) := by
  exact parametrized_isMagic 1 u v

/-- Algebraic verification of the eight coefficients on the flexible line.-/
theorem centerOneLine_entries (t b : R) :
    (centerOneLine t b).a = 1 + t ∧
    (centerOneLine t b).b = 1 - (1 + b) * t ∧
    (centerOneLine t b).c = 1 + b * t ∧
    (centerOneLine t b).d = 1 + (b - 1) * t ∧
    (centerOneLine t b).e = 1 ∧
    (centerOneLine t b).f = 1 + (1 - b) * t ∧
    (centerOneLine t b).g = 1 - b * t ∧
    (centerOneLine t b).h = 1 + (1 + b) * t ∧
    (centerOneLine t b).i = 1 - t := by
  unfold centerOneLine centerOne parametrized
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end Square3
end MagicSquares
