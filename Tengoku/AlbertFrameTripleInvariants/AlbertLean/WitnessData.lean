import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.C0Polar
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean

open Generated

def Theta1ESquare : Coord := fun i =>
  match i.val with
  | 0 => q 1 1
  | 2 => q 1 1
  | _ => 0

def Theta1FSquare : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-17) 18
  | 2 => q 59 18
  | 3 => q 1 3
  | 4 => q (-245) 54
  | 5 => q (-1295) 108
  | 6 => q 8 1
  | 7 => q (-140) 27
  | 8 => q 3 1
  | 9 => q 35 12
  | 10 => q (-3) 1
  | 11 => q 1 1
  | 13 => q 1 1
  | 15 => q 3 2
  | 16 => q (-2) 1
  | 17 => q (-245) 54
  | 18 => q (-3) 2
  | 21 => q (-4) 3
  | 23 => q 3 2
  | 24 => q 2 3
  | 25 => q (-35) 18
  | 26 => q (-25) 6
  | _ => 0

def Theta1KSquare : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-4) 9
  | 2 => q 25 9
  | 3 => q (-91) 27
  | 4 => q 4 3
  | 5 => q 13 6
  | 6 => q (-52) 27
  | 7 => q (-91) 18
  | 8 => q 25 18
  | 9 => q (-5) 4
  | 10 => q 283 54
  | 12 => q 1 1
  | 15 => q (-1) 2
  | 16 => q (-64) 27
  | 17 => q (-3) 2
  | 18 => q (-4) 9
  | 20 => q 1 1
  | 22 => q (-4) 3
  | 23 => q (-2) 1
  | 24 => q 364 81
  | 26 => q 52 27
  | _ => 0

def ThetaMFSquare : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-17) 18
  | 2 => q 59 18
  | 3 => q 1 3
  | 4 => q (-245) 54
  | 5 => q (-69930) 410231
  | 6 => q 451055 410231
  | 7 => q (-140) 27
  | 8 => q 17496 410231
  | 9 => q 35 12
  | 10 => q (-3) 1
  | 11 => q 1 1
  | 13 => q 1 1
  | 15 => q 3 2
  | 16 => q (-2) 1
  | 17 => q (-245) 54
  | 18 => q (-8748) 410231
  | 21 => q (-4) 3
  | 23 => q 3 2
  | 24 => q 2 3
  | 25 => q (-35) 18
  | 26 => q (-24300) 410231
  | _ => 0

def ThetaMKSquare : Coord := fun i =>
  match i.val with
  | 0 => q (-1) 3
  | 1 => q (-4) 9
  | 2 => q 25 9
  | 3 => q (-91) 27
  | 4 => q 4 3
  | 5 => q 12636 410231
  | 6 => q (-11232) 410231
  | 7 => q (-91) 18
  | 8 => q 8100 410231
  | 9 => q 397109 5832
  | 10 => q 283 54
  | 12 => q 1 1
  | 15 => q (-1) 2
  | 16 => q (-64) 27
  | 17 => q (-3) 2
  | 18 => q (-2592) 410231
  | 20 => q 1 1
  | 22 => q (-410231) 4374
  | 23 => q (-2) 1
  | 24 => q 364 81
  | 26 => q 11232 410231
  | _ => 0

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h0v.s2.a7c96266bd05 from=translated src=- shape=1f28ec23 vocab=6604c2d3
-/
theorem theta1E_square : structuredProduct theta1E theta1E = Theta1ESquare := by
  rw [structuredProduct_eq_productForm]
  funext k
  fin_cases k <;> norm_num [productForm, theta1E, Theta1ESquare, v, q]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h0v.s2.51b4226fc73b from=translated src=- shape=1f28ec23 vocab=f8e97d65
-/
theorem theta1F_square : structuredProduct theta1F theta1F = Theta1FSquare := by
  rw [structuredProduct_eq_productForm]
  funext k
  fin_cases k <;> norm_num [productForm, theta1F, Theta1FSquare, v, q]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h0v.s2.8435f71e8f60 from=translated src=- shape=1f28ec23 vocab=efbd09c2
-/
theorem theta1K_square : structuredProduct theta1K theta1K = Theta1KSquare := by
  rw [structuredProduct_eq_productForm]
  funext k
  fin_cases k <;> norm_num [productForm, theta1K, Theta1KSquare, v, q]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h0v.s2.d6ac3f779ae0 from=translated src=- shape=1f28ec23 vocab=7eb7b1d0
-/
theorem thetaMF_square : structuredProduct thetaMF thetaMF = ThetaMFSquare := by
  rw [structuredProduct_eq_productForm]
  funext k
  fin_cases k <;> norm_num [productForm, thetaMF, ThetaMFSquare, v, q]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h0v.s2.481bd887fdc2 from=translated src=- shape=1f28ec23 vocab=ee1b4a0d
-/
theorem thetaMK_square : structuredProduct thetaMK thetaMK = ThetaMKSquare := by
  rw [structuredProduct_eq_productForm]
  funext k
  fin_cases k <;> norm_num [productForm, thetaMK, ThetaMKSquare, v, q]

def traceLinearForm (x : Coord) : ℚ := v x 0 + v x 1 + v x 2

def spurPairForm (x y : Coord) : ℚ :=
  v x 0 * v y 1 + v x 1 * v y 0 +
  v x 0 * v y 2 + v x 2 * v y 0 +
  v x 1 * v y 2 + v x 2 * v y 1 -
  (v x 3 * v y 4 + v x 4 * v y 3) -
  (v x 5 * v y 10 + v x 10 * v y 5) +
  (v x 6 * v y 9 + v x 9 * v y 6) -
  (v x 7 * v y 8 + v x 8 * v y 7) -
  (v x 11 * v y 15 + v x 15 * v y 11) -
  (v x 12 * v y 16 + v x 16 * v y 12) -
  (v x 13 * v y 17 + v x 17 * v y 13) -
  (v x 14 * v y 18 + v x 18 * v y 14) -
  (v x 19 * v y 23 + v x 23 * v y 19) -
  (v x 20 * v y 24 + v x 24 * v y 20) -
  (v x 21 * v y 25 + v x 25 * v y 21) -
  (v x 22 * v y 26 + v x 26 * v y 22)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s3.13f209f4a133 from=translated src=- shape=b70c6bb1 vocab=ee5fa869
-/
theorem traceN_eq_traceLinearForm (x : Coord) :
    traceN x = traceLinearForm x := by
  rw [traceN, cubicPolar_eq_polarForm]
  simp [polarForm, traceLinearForm, one, v, q]
  ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h2v.s3.357dad5a2beb from=translated src=- shape=e4af5fdd vocab=c43d23ca
-/
theorem spurBilinear_eq_spurPairForm (x y : Coord) :
    spurBilinear x y = spurPairForm x y := by
  rw [spurBilinear, cubicPolar_eq_polarForm]
  simp [polarForm, spurPairForm, one, v, q]
  ring

/--
@isnad1 id=eq.0h2v.s4.35f0440635cf from=translated src=- shape=a760c453 vocab=10ffa1eb
-/
theorem traceForm_eq_fast (x y : Coord) :
    traceForm x y = traceLinearForm x * traceLinearForm y - spurPairForm x y := by
  rw [traceForm, traceN_eq_traceLinearForm, traceN_eq_traceLinearForm,
    spurBilinear_eq_spurPairForm]

/--
@isnad1 id=eq.0h0v.s2.f80660bed17f from=translated src=- shape=54c8eceb vocab=efe30fe6
-/
theorem thetaME_eq_theta1E_fast : thetaME = theta1E := by
  funext i
  fin_cases i <;> norm_num [thetaME, theta1E, q]

/-- The standard frame projectors extract diagonal coordinates on the left.
@isnad1 id=eq.0h2v.s4.9281e5ef6fc0 from=translated src=- shape=a355b90d vocab=08647ad3
-/
theorem traceForm_projector_theta1E_left (i : Fin 3) (z : Coord) :
    traceForm (projector theta1E i) z = v z i.val := by
  fin_cases i <;>
    simp only [projector, theta1E_square, traceForm_eq_fast]
  all_goals
    norm_num [traceLinearForm, spurPairForm, Theta1ESquare, theta1E, one, v, q] <;>
      ring

/-- The standard frame projectors extract diagonal coordinates on the right.
@isnad1 id=eq.0h2v.s4.5c5b166783a4 from=translated src=- shape=ff1a7807 vocab=08647ad3
-/
theorem traceForm_projector_theta1E_right (i : Fin 3) (z : Coord) :
    traceForm z (projector theta1E i) = v z i.val := by
  fin_cases i <;>
    simp only [projector, theta1E_square, traceForm_eq_fast]
  all_goals
    norm_num [traceLinearForm, spurPairForm, Theta1ESquare, theta1E, one, v, q] <;>
      ring

end AlbertLean
