import Tengoku.Seed.NumberTheory.Zsqrtd.Basic
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Notation
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FLT.ExplicitLift

open Matrix Zsqrtd

/--
@isnad1 id=eq.0h0v.s8.774be0b920dc from=translated src=- shape=0e6411df vocab=336e32d7
-/
theorem neg_one_sq_eq_neg_two : (-1 : ZMod 3) * (-1) = ((-2 : ℤ) : ZMod 3) := by decide

noncomputable def red : ℤ√(-2) →+* ZMod 3 :=
  Zsqrtd.lift ⟨-1, neg_one_sq_eq_neg_two⟩

def sbar : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![-1, 1; -1, 0]

def tbar : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, -1; 1, 1]

def Slift : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) := !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩]

def Tlift : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) := !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩]

end FLT.ExplicitLift
