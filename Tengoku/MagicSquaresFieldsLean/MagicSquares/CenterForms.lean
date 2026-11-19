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

/--
@isnad1 id=eq.0h2v.s4.ea3ce5badfc0 from=translated src=- shape=1c9622f3 vocab=e1cf79f8
-/
@[simp] theorem centerZero_a (x : R) : (centerZero x).a = x := by
  simp [centerZero, parametrized]
/--
@isnad1 id=eq.0h2v.s6.8202d5e2f64a from=translated src=- shape=548d4ba9 vocab=2cefb691
-/
@[simp] theorem centerZero_b (x : R) : (centerZero x).b = -x - 1 := by
  simp [centerZero, parametrized]
/--
@isnad1 id=eq.0h2v.s4.841db1bdf052 from=translated src=- shape=713098bd vocab=27173e8e
-/
@[simp] theorem centerZero_c (x : R) : (centerZero x).c = 1 := by
  simp [centerZero, parametrized]
/--
@isnad1 id=eq.0h2v.s5.71097bba5d6a from=translated src=- shape=3424be87 vocab=756f035d
-/
@[simp] theorem centerZero_d (x : R) : (centerZero x).d = 1 - x := by
  simp [centerZero, parametrized]; ring
/--
@isnad1 id=eq.0h2v.s4.50181271837c from=translated src=- shape=713098bd vocab=782d3c02
-/
@[simp] theorem centerZero_e (x : R) : (centerZero x).e = 0 := by
  simp [centerZero, parametrized]
/--
@isnad1 id=eq.0h2v.s5.80c5e556f493 from=translated src=- shape=e1341f6e vocab=8b91c001
-/
@[simp] theorem centerZero_f (x : R) : (centerZero x).f = x - 1 := by
  simp [centerZero, parametrized]
/--
@isnad1 id=eq.0h2v.s5.b6f2766c27b5 from=translated src=- shape=63d8182d vocab=26078b9e
-/
@[simp] theorem centerZero_g (x : R) : (centerZero x).g = -1 := by
  simp [centerZero, parametrized]
/--
@isnad1 id=eq.0h2v.s5.ab894b5c2178 from=translated src=- shape=e1341f6e vocab=4044093d
-/
@[simp] theorem centerZero_h (x : R) : (centerZero x).h = x + 1 := by
  simp [centerZero, parametrized]
/--
@isnad1 id=eq.0h2v.s5.d2fe2e4f99f8 from=translated src=- shape=fca1e1b8 vocab=1ac293c8
-/
@[simp] theorem centerZero_i (x : R) : (centerZero x).i = -x := by
  simp [centerZero, parametrized]

/-- The center-zero family is automatically magic.
@isnad1 id=ismagic.0h2v.s4.318b56c0e033 from=translated src=- shape=101348a6 vocab=89f455a1
-/
theorem centerZero_isMagic (x : R) : IsMagic (centerZero x) := by
  exact parametrized_isMagic 0 x 1

/-- The center-one family is automatically magic.
@isnad1 id=ismagic.0h3v.s4.3a43d69f90e2 from=translated src=- shape=ce8ffaa7 vocab=8f3b1b68
-/
theorem centerOne_isMagic (u v : R) : IsMagic (centerOne u v) := by
  exact parametrized_isMagic 1 u v

/-- Algebraic verification of the eight coefficients on the flexible line.
@isnad1 id=and.0h3v.s9.348177f17b3d from=translated src=- shape=164dd5ca vocab=fdae437f
-/
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
