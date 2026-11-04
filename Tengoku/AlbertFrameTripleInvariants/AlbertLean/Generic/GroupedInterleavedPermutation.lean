import Tengoku.Seed.Tactic.FinCases
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GroupedSymplecticBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms blockify_grouped_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms blockStar_blockify_grouped` (it only prints; the queue checks the axioms of every declaration). -/

/-! Explicit permutation from the grouped `W ⊕ W*` basis to the pre-existing
interleaved `Fin 3 × Fin 2` block basis. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.GroupedPermutation

open AlbertLean.Generic.QuaternionRow.ScalarFibre
open AlbertLean.Generic.QuaternionRow.GroupedBridge

universe u
variable {K : Type u} [Field K] [CharZero K]

def groupedToInterleaved : Ix6 ≃ (Fin 3 × Fin 2) where
  toFun
    | Sum.inl i => (i, 0)
    | Sum.inr i => (i, 1)
  invFun p := Fin.cases (Sum.inl p.1) (fun _ => Sum.inr p.1) p.2
  left_inv x := by rcases x with i | i <;> rfl
  right_inv p := by rcases p with ⟨i, q⟩; fin_cases q <;> rfl

def interleaveMatrix (P : Mat6 K) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) K :=
  fun i j => P (groupedToInterleaved.symm i) (groupedToInterleaved.symm j)

abbrev Mat2 (K : Type u) := Matrix (Fin 2) (Fin 2) K
abbrev Block3 (K : Type u) := Matrix (Fin 3) (Fin 3) (Mat2 K)

def blockify (P : Mat6 K) : Block3 K :=
  fun i j p q => interleaveMatrix P (i, p) (j, q)

/-- The split-quaternion star, defined here to keep the bridge independent.-/
def mat2Star (A : Mat2 K) : Mat2 K :=
  !![A 1 1, -A 0 1; -A 1 0, A 0 0]

def blockStar (A : Block3 K) : Block3 K := fun i j => mat2Star (A j i)

/-- Exact entry dictionary after applying the displayed permutation.
@isnad1 id=eq.0h6v.s8.66ab9e6f267c from=translated src=- shape=824b4b71 vocab=4e81b2ed
-/
theorem blockify_grouped_apply
    (a : Mat3 K) (u v : Vec3 K) (i j : Fin 3) :
    blockify (grouped a u v) i j =
      !![a i j, hat u i j; hat v i j, a j i] := by
  ext p q
  fin_cases p <;> fin_cases q <;> rfl

/-- Thus the grouped symplectic-selfadjoint carrier lands in precisely the
existing block-star-fixed carrier, with no suppressed basis permutation.
@isnad1 id=eq.0h4v.s5.c86d3178e172 from=translated src=- shape=3ff52eda vocab=55ef069e
-/
theorem blockStar_blockify_grouped
    (a : Mat3 K) (u v : Vec3 K) :
    blockStar (blockify (grouped a u v)) = blockify (grouped a u v) := by
  ext i j p q
  fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;>
    simp [blockStar, mat2Star, blockify_grouped_apply, hat]

end AlbertLean.Generic.QuaternionRow.GroupedPermutation
