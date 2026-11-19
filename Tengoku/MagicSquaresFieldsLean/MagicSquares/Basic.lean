import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

/-- A 3 × 3 array, named according to the notation in the paper.-/
@[ext]
structure Square3 (R : Type*) where
  a : R
  b : R
  c : R
  d : R
  e : R
  f : R
  g : R
  h : R
  i : R

namespace Square3

variable {R : Type*}

/-- The eight line sums of a 3 × 3 square are all equal.  We use the
first row as the reference line.-/
def IsMagic [Add R] (M : Square3 R) : Prop :=
  M.a + M.b + M.c = M.d + M.e + M.f ∧
  M.a + M.b + M.c = M.g + M.h + M.i ∧
  M.a + M.b + M.c = M.a + M.d + M.g ∧
  M.a + M.b + M.c = M.b + M.e + M.h ∧
  M.a + M.b + M.c = M.c + M.f + M.i ∧
  M.a + M.b + M.c = M.a + M.e + M.i ∧
  M.a + M.b + M.c = M.c + M.e + M.g

/-- The universal three-parameter family from Proposition 1.-/
def parametrized [Ring R] (E U V : R) : Square3 R where
  a := E + U
  b := E - U - V
  c := E + V
  d := E - U + V
  e := E
  f := E + U - V
  g := E - V
  h := E + U + V
  i := E - U

/-- Every square in the universal family is magic, with magic sum `3 * E`.-/
theorem parametrized_isMagic [CommRing R] (E U V : R) :
    IsMagic (parametrized E U V) := by
  unfold IsMagic parametrized
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
  · ring

/-- The common magic sum is three times the center entry.  This is Theorem 2.1.-/
theorem magicSum_eq_three_center [CommRing R] (M : Square3 R) (hM : IsMagic M) :
    M.a + M.b + M.c = 3 * M.e := by
  rcases hM with ⟨hr2, hr3, hc1, hc2, hc3, hd1, hd2⟩
  linear_combination hc2 + hd1 + hd2 - hr3

/-- Opposite corner entries add to twice the center.-/
theorem a_add_i_eq_two_center [CommRing R] (M : Square3 R) (hM : IsMagic M) :
    M.a + M.i = 2 * M.e := by
  rcases hM with ⟨hr2, hr3, hc1, hc2, hc3, hd1, hd2⟩
  have hs : M.a + M.b + M.c = 3 * M.e := by
    linear_combination hc2 + hd1 + hd2 - hr3
  linear_combination hs - hd1

/-- The second pair of opposite entries adds to twice the center.-/
theorem b_add_h_eq_two_center [CommRing R] (M : Square3 R) (hM : IsMagic M) :
    M.b + M.h = 2 * M.e := by
  rcases hM with ⟨hr2, hr3, hc1, hc2, hc3, hd1, hd2⟩
  have hs : M.a + M.b + M.c = 3 * M.e := by
    linear_combination hc2 + hd1 + hd2 - hr3
  linear_combination hs - hc2

/-- The third pair of opposite entries adds to twice the center.-/
theorem c_add_g_eq_two_center [CommRing R] (M : Square3 R) (hM : IsMagic M) :
    M.c + M.g = 2 * M.e := by
  rcases hM with ⟨hr2, hr3, hc1, hc2, hc3, hd1, hd2⟩
  have hs : M.a + M.b + M.c = 3 * M.e := by
    linear_combination hc2 + hd1 + hd2 - hr3
  linear_combination hs - hd2

/-- The fourth pair of opposite entries adds to twice the center.-/
theorem d_add_f_eq_two_center [CommRing R] (M : Square3 R) (hM : IsMagic M) :
    M.d + M.f = 2 * M.e := by
  rcases hM with ⟨hr2, hr3, hc1, hc2, hc3, hd1, hd2⟩
  have hs : M.a + M.b + M.c = 3 * M.e := by
    linear_combination hc2 + hd1 + hd2 - hr3
  linear_combination hs - hr2

/-- Converse direction of Proposition 1: every 3 × 3 magic square has the
universal form, with `U = A - E` and `V = C - E`.-/
theorem universal_form [CommRing R] (M : Square3 R) (hM : IsMagic M) :
    M = parametrized M.e (M.a - M.e) (M.c - M.e) := by
  rcases hM with ⟨hr2, hr3, hc1, hc2, hc3, hd1, hd2⟩
  have hs : M.a + M.b + M.c = 3 * M.e := by
    linear_combination hc2 + hd1 + hd2 - hr3
  have hb : M.b = 3 * M.e - M.a - M.c := by
    linear_combination hs
  have hi : M.i = 2 * M.e - M.a := by
    linear_combination hs - hd1
  have hg : M.g = 2 * M.e - M.c := by
    linear_combination hs - hd2
  have hh : M.h = M.a + M.c - M.e := by
    linear_combination -hc2
  have hd : M.d = M.e - M.a + M.c := by
    linear_combination hs - hc1 - hg
  have hf : M.f = M.e + M.a - M.c := by
    linear_combination hs - hr2 - hd
  ext <;> simp [parametrized, hb, hd, hf, hg, hh, hi] <;> ring

/-- The entries of a square, in row-major order.-/
def entries (M : Square3 R) : Fin 9 → R :=
  ![M.a, M.b, M.c, M.d, M.e, M.f, M.g, M.h, M.i]

/-- The nine entries are pairwise distinct.-/
def PairwiseDistinct (M : Square3 R) : Prop :=
  Function.Injective M.entries

end Square3

end MagicSquares
