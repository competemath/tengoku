/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/

/-!
# The bcs net distance function

Exact closed form of the graph distance from the base vertex (1, (0,0,0)) of the
bcs periodic net to the state (v, (x,y,z)): the maximum of six affine forms
(one per surviving octahedron facet; the (+,+,-) and (-,-,+) facets are absorbed
by the cheap (1,1,-1) direction), plus a +2 correction on two exceptional lines
(classes 1 and 8 only). Discovered from BFS data and verified exhaustively on
ball(15) (7467 states) before formalization; the theorems in `Lipschitz.lean`
and `Descent.lean` prove it is *the* graph distance for all states.
-/

namespace Bcs

/-- Distance from the base vertex to states of class 1.-/
def D1 (x y z : Int) : Int :=
  (max (2*x + 2*y + 2*z) <| max (2*x - 2*y + 2*z) <| max (-2*x + 2*y + 2*z) <| max (-2*x - 2*y - 2*z) <| max (2*x - 2*y - 2*z) (-2*x + 2*y - 2*z)) + (if x = y ∧ y = -z ∧ x ≠ 0 then 2 else 0)

/-- Distance from the base vertex to states of class 2.-/
def D2 (x y z : Int) : Int :=
  max (2*x + 2*y + 2*z - 1) <| max (2*x - 2*y + 2*z - 1) <| max (-2*x + 2*y + 2*z - 1) <| max (-2*x - 2*y - 2*z + 1) <| max (2*x - 2*y - 2*z + 1) (-2*x + 2*y - 2*z + 1)

/-- Distance from the base vertex to states of class 3.-/
def D3 (x y z : Int) : Int :=
  max (2*x + 2*y + 2*z - 1) <| max (2*x - 2*y + 2*z + 1) <| max (-2*x + 2*y + 2*z - 1) <| max (-2*x - 2*y - 2*z + 1) <| max (2*x - 2*y - 2*z + 1) (-2*x + 2*y - 2*z - 1)

/-- Distance from the base vertex to states of class 4.-/
def D4 (x y z : Int) : Int :=
  max (2*x + 2*y + 2*z - 1) <| max (2*x - 2*y + 2*z - 1) <| max (-2*x + 2*y + 2*z + 1) <| max (-2*x - 2*y - 2*z + 1) <| max (2*x - 2*y - 2*z - 1) (-2*x + 2*y - 2*z + 1)

/-- Distance from the base vertex to states of class 5.-/
def D5 (x y z : Int) : Int :=
  max (2*x + 2*y + 2*z) <| max (2*x - 2*y + 2*z - 2) <| max (-2*x + 2*y + 2*z - 2) <| max (-2*x - 2*y - 2*z) <| max (2*x - 2*y - 2*z + 2) (-2*x + 2*y - 2*z + 2)

/-- Distance from the base vertex to states of class 6.-/
def D6 (x y z : Int) : Int :=
  max (2*x + 2*y + 2*z - 2) <| max (2*x - 2*y + 2*z) <| max (-2*x + 2*y + 2*z - 2) <| max (-2*x - 2*y - 2*z + 2) <| max (2*x - 2*y - 2*z + 2) (-2*x + 2*y - 2*z)

/-- Distance from the base vertex to states of class 7.-/
def D7 (x y z : Int) : Int :=
  max (2*x + 2*y + 2*z) <| max (2*x - 2*y + 2*z) <| max (-2*x + 2*y + 2*z - 2) <| max (-2*x - 2*y - 2*z) <| max (2*x - 2*y - 2*z + 2) (-2*x + 2*y - 2*z)

/-- Distance from the base vertex to states of class 8.-/
def D8 (x y z : Int) : Int :=
  (max (2*x + 2*y + 2*z - 1) <| max (2*x - 2*y + 2*z - 3) <| max (-2*x + 2*y + 2*z - 3) <| max (-2*x - 2*y - 2*z + 1) <| max (2*x - 2*y - 2*z + 3) (-2*x + 2*y - 2*z + 3)) + (if x = y ∧ z = 1 - x then 2 else 0)

end Bcs
