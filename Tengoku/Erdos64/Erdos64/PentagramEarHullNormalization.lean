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

/--
@isnad1 id=bijectiv.0h1v.s4.244b9a4d7bd4 from=translated src=- shape=bac0a165 vocab=730b2061
-/
@[simp] theorem rotate5_bijective (k : Fin 5) :
    Function.Bijective (rotate5 k) := by
  fin_cases k <;> decide

/--
@isnad1 id=bijectiv.0h1v.s4.711cd92ce2a6 from=translated src=- shape=bac0a165 vocab=e8937c96
-/
@[simp] theorem reflect5_bijective (k : Fin 5) :
    Function.Bijective (reflect5 k) := by
  fin_cases k <;> decide

/-- Rotations preserve the directed cyclic successor relation.
@isnad1 id=eq.0h2v.s6.ce1312c32fb2 from=translated src=- shape=ecedb06a vocab=86e38902
-/
theorem rotate5_succ (k i : Fin 5) :
    rotate5 k (i + 1) = rotate5 k i + 1 := by
  fin_cases k <;> fin_cases i <;> decide

/-- Reflections reverse the directed cyclic successor relation.
@isnad1 id=eq.0h2v.s6.1d7d2b1c7cd6 from=translated src=- shape=ecedb06a vocab=76a3236e
-/
theorem reflect5_succ (k i : Fin 5) :
    reflect5 k (i + 1) = reflect5 k i + 4 := by
  fin_cases k <;> fin_cases i <;> decide

/-- Every distinct ordered endpoint pair is translated to `0,d` for a
nonzero `d`.  No identification of `d` with a particular route case is made.
@isnad1 id=ex.1h2v.s6.7c3f6acf08c5 from=translated src=- shape=a0e4bd8e vocab=723a0701
-/
theorem exists_cyclic_endpoint_normalization
    (i j : Fin 5) (hij : i ≠ j) :
    ∃ k d : Fin 5,
      d ≠ 0 ∧ rotate5 k i = 0 ∧ rotate5 k j = d := by
  fin_cases i <;> fin_cases j <;> simp_all [rotate5] <;> decide

end PentagramEarHull

end Erdos64
