import Tengoku.Erdos64.Erdos64.PentagramEarHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

def bToC0 (H : PentagramEarHull G) (i : Fin 5) :
    G.Walk (bVertex H i) (cVertex H i) :=
  SimpleGraph.Walk.cons (H.ab_adj i).symm
    (SimpleGraph.Walk.cons (H.ca_adj i).symm .nil)

def bToC2 (H : PentagramEarHull G) (i : Fin 5) :
    G.Walk (bVertex H i) (cVertex H (i + 2)) :=
  SimpleGraph.Walk.cons (H.shifted_ab_adj i).symm
    (SimpleGraph.Walk.cons (H.ca_adj (i + 2)).symm .nil)

def cForward (H : PentagramEarHull G) (i : Fin 5) : G.Walk
    (cVertex H i) (cVertex H (i + 1)) :=
  SimpleGraph.Walk.cons (H.c_adj i) .nil

def cForward2 (H : PentagramEarHull G) (i : Fin 5) : G.Walk
    (cVertex H i) (cVertex H (i + 2)) :=
  (H.cForward i).append (H.cForward (i + 1)) |>.copy rfl (by
    apply congrArg (cVertex H)
    apply Fin.ext
    omega)

def cForward3 (H : PentagramEarHull G) (i : Fin 5) : G.Walk
    (cVertex H i) (cVertex H (i + 3)) :=
  (H.cForward2 i).append (H.cForward (i + 2)) |>.copy rfl (by
    apply congrArg (cVertex H)
    apply Fin.ext
    omega)

def connectorArcLength (r : Fin 3) : Nat := 3 - r.val

end PentagramEarHull

end Erdos64
