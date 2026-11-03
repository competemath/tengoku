import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms structuredEquivK` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Generic adapted coordinates for the structured cubic source

This module defines the 27-coordinate carrier and the literal structured
flattening over an arbitrary characteristic-zero field.  It is source-only:
it does not import the frozen F0 tensor, and no multiplication is transported
through the equivalence.
-/

namespace AlbertLean.Triality.GenericCoordinates

open ExteriorSix CoordinateTensor StructuredCubic

variable (K : Type*) [Field K] [CharZero K]

/-- The 27-coordinate carrier over `K`.-/
abbrev F0Coord := Fin 27 → K

/-- The literal adapted flattening, in the independently locked block order.-/
def structuredToF0K (x : JCoord K) : F0Coord K := fun i ↦
  match i.val with
  | 0 => x.d1
  | 1 => x.d2
  | 2 => x.d3
  | 3 => x.v.r
  | 4 => x.v.z
  | 5 => x.v.omega .i12
  | 6 => x.v.omega .i13
  | 7 => x.v.omega .i14
  | 8 => x.v.omega .i23
  | 9 => x.v.omega .i24
  | 10 => x.v.omega .i34
  | 11 => x.s.p 0
  | 12 => x.s.p 1
  | 13 => x.s.p 2
  | 14 => x.s.p 3
  | 15 => x.s.phi 0
  | 16 => x.s.phi 1
  | 17 => x.s.phi 2
  | 18 => x.s.phi 3
  | 19 => x.c.q 0
  | 20 => x.c.q 1
  | 21 => x.c.q 2
  | 22 => x.c.q 3
  | 23 => x.c.psi 0
  | 24 => x.c.psi 1
  | 25 => x.c.psi 2
  | 26 => x.c.psi 3
  | _ => 0

/-- Literal inverse block unflattening in the same order.-/
def f0ToStructuredK (x : F0Coord K) : JCoord K :=
  { d1 := x 0
    d2 := x 1
    d3 := x 2
    v :=
      { r := x 3
        z := x 4
        omega := fun
          | .i12 => x 5
          | .i13 => x 6
          | .i14 => x 7
          | .i23 => x 8
          | .i24 => x 9
          | .i34 => x 10 }
    s :=
      { p := ![x 11, x 12, x 13, x 14]
        phi := ![x 15, x 16, x 17, x 18] }
    c :=
      { q := ![x 19, x 20, x 21, x 22]
        psi := ![x 23, x 24, x 25, x 26] } }

/--
@isnad1 id=eq.0h2v.s4.31b41f1a0262 from=translated src=- shape=e17ccb0b vocab=b7354ab4
-/
theorem f0ToStructuredK_structuredToF0K (x : JCoord K) :
    f0ToStructuredK K (structuredToF0K K x) = x := by
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · apply VCoord.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> rfl
  · apply SCoord.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  · apply CCoord.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl

/--
@isnad1 id=eq.0h2v.s4.c546eded6aa8 from=translated src=- shape=e17ccb0b vocab=1a561aee
-/
theorem structuredToF0K_f0ToStructuredK (x : F0Coord K) :
    structuredToF0K K (f0ToStructuredK K x) = x := by
  funext i
  fin_cases i <;> rfl

/-- The generic adapted-coordinate linear equivalence.-/
def structuredEquivK : JCoord K ≃ₗ[K] F0Coord K where
  toFun := structuredToF0K K
  invFun := f0ToStructuredK K
  left_inv := f0ToStructuredK_structuredToF0K K
  right_inv := structuredToF0K_f0ToStructuredK K
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' a x := by
    funext i
    fin_cases i <;> rfl

/--
@isnad1 id=eq.0h2v.s8.8d16e219c7a8 from=translated src=- shape=62f77d1b vocab=218ad7d1
-/
@[simp] theorem structuredEquivK_apply (x : JCoord K) :
    structuredEquivK K x = structuredToF0K K x := rfl

/--
@isnad1 id=eq.0h2v.s9.04e935a78ed7 from=translated src=- shape=71f9b53b vocab=d7b26b7e
-/
@[simp] theorem structuredEquivK_symm_apply (x : F0Coord K) :
    (structuredEquivK K).symm x = f0ToStructuredK K x := rfl

end AlbertLean.Triality.GenericCoordinates
