import Tengoku.Erdos64.Erdos64.PentagramEarHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

namespace PentagramEarHull

/-- Translation of indices around the pentagram.-/
def rotate5 (k i : Fin 5) : Fin 5 :=
  ⟨(k.val + i.val) % 5, Nat.mod_lt _ (by decide)⟩

/-- Reflection of indices around the pentagram.-/
def reflect5 (k i : Fin 5) : Fin 5 :=
  ⟨(k.val + 5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩

@[simp] theorem rotate5_bijective (k : Fin 5) :
    Function.Bijective (rotate5 k) := by
  fin_cases k <;> decide

@[simp] theorem reflect5_bijective (k : Fin 5) :
    Function.Bijective (reflect5 k) := by
  fin_cases k <;> decide

/-- Rotations preserve the directed cyclic successor relation.-/
theorem rotate5_succ (k i : Fin 5) :
    rotate5 k (i + 1) = rotate5 k i + 1 := by
  fin_cases k <;> fin_cases i <;> decide

/-- Reflections reverse the directed cyclic successor relation.-/
theorem reflect5_succ (k i : Fin 5) :
    reflect5 k (i + 1) = reflect5 k i + 4 := by
  fin_cases k <;> fin_cases i <;> decide

/-- Every distinct ordered endpoint pair is translated to `0,d` for a
nonzero `d`.  No identification of `d` with a particular route case is made.-/
theorem exists_cyclic_endpoint_normalization
    (i j : Fin 5) (hij : i ≠ j) :
    ∃ k d : Fin 5,
      d ≠ 0 ∧ rotate5 k i = 0 ∧ rotate5 k j = d := by
  fin_cases i <;> fin_cases j <;> simp_all [rotate5] <;> decide

end PentagramEarHull

end Erdos64
