/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.H6Completion
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A4Q15Coordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PrimitiveGlue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

inductive RankSixKind | ternary | fifteenPlus | fifteenMinus | seventyFive deriving DecidableEq

abbrev RankSixKind.threeShape : RankSixKind → PrimaryShape
  | .ternary | .fifteenPlus => .two
  | .fifteenMinus | .seventyFive => .four

abbrev RankSixKind.fiveShape : RankSixKind → PrimaryShape
  | .ternary => .zero
  | .fifteenPlus => .two
  | .fifteenMinus => .four
  | .seventyFive => .binary

/--
@isnad1 id=ex.1h2v.s5.10396326f50d from=translated src=- shape=a9f5e445 vocab=a3993756
-/
theorem exists_rankSixKind (s t : PrimaryShape)
    (h8 : 8 ∣ 18 + primaryModelRank .three s + primaryModelRank .five t) :
    ∃ k : RankSixKind, k.threeShape = s ∧ k.fiveShape = t := by
  rcases (eight_dvd_mixed_rank_iff s t).mp h8 with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨.ternary, rfl, rfl⟩
  · exact ⟨.fifteenPlus, rfl, rfl⟩
  · exact ⟨.fifteenMinus, rfl, rfl⟩
  · exact ⟨.seventyFive, rfl, rfl⟩

abbrev rankSixSpace : RankSixKind → Type
  | .ternary => mixedPrimarySpace .two .zero
  | .fifteenPlus => H6Coordinates.Space
  | .fifteenMinus => mixedPrimarySpace .four .four
  | .seventyFive => A4Q15Coordinates.Space

instance : (k : RankSixKind) → AddCommGroup (rankSixSpace k)
  | .ternary => inferInstanceAs (AddCommGroup (mixedPrimarySpace .two .zero))
  | .fifteenPlus => inferInstanceAs (AddCommGroup H6Coordinates.Space)
  | .fifteenMinus => inferInstanceAs (AddCommGroup (mixedPrimarySpace .four .four))
  | .seventyFive => inferInstanceAs (AddCommGroup A4Q15Coordinates.Space)
instance : (k : RankSixKind) → Module ℚ (rankSixSpace k)
  | .ternary => inferInstanceAs (Module ℚ (mixedPrimarySpace .two .zero))
  | .fifteenPlus => inferInstanceAs (Module ℚ H6Coordinates.Space)
  | .fifteenMinus => inferInstanceAs (Module ℚ (mixedPrimarySpace .four .four))
  | .seventyFive => inferInstanceAs (Module ℚ A4Q15Coordinates.Space)
instance : (k : RankSixKind) → Module.Finite ℚ (rankSixSpace k)
  | .ternary => inferInstanceAs (Module.Finite ℚ (mixedPrimarySpace .two .zero))
  | .fifteenPlus => inferInstanceAs (Module.Finite ℚ H6Coordinates.Space)
  | .fifteenMinus => inferInstanceAs (Module.Finite ℚ (mixedPrimarySpace .four .four))
  | .seventyFive => inferInstanceAs (Module.Finite ℚ A4Q15Coordinates.Space)

def rankSixForm : (k : RankSixKind) → LinearMap.BilinForm ℚ (rankSixSpace k)
  | .ternary => mixedPrimaryForm .two .zero
  | .fifteenPlus => H6Coordinates.form
  | .fifteenMinus => mixedPrimaryForm .four .four
  | .seventyFive => A4Q15Coordinates.form

def rankSixBase : (k : RankSixKind) → Submodule ℤ (rankSixSpace k)
  | .ternary => mixedPrimaryBase .two .zero
  | .fifteenPlus => H6Coordinates.lattice
  | .fifteenMinus => mixedPrimaryBase .four .four
  | .seventyFive => A4Q15Coordinates.lattice

def rankSixVector : (k : RankSixKind) →
    Fin k.threeShape.arity ⊕ Fin k.fiveShape.arity → rankSixSpace k
  | .ternary => mixedPrimaryVector .two .zero
  | .fifteenPlus => H6Coordinates.matchingVector
  | .fifteenMinus => mixedPrimaryVector .four .four
  | .seventyFive => A4Q15Coordinates.matchingVector

/--
@isnad1 id=issymm.0h1v.s4.c0cf6998da1e from=translated src=- shape=b70c6bb1 vocab=f6daae89
-/
theorem rankSixForm_isSymm (k : RankSixKind) : (rankSixForm k).IsSymm := by
  cases k
  · exact prodForm_isSymm (primaryModel_isSymm .three .two) (primaryModel_isSymm .five .zero)
  · exact H6Coordinates.form_isSymm
  · exact prodForm_isSymm (primaryModel_isSymm .three .four) (primaryModel_isSymm .five .four)
  · exact A4Q15Coordinates.form_isSymm

/--
@isnad1 id=lt.1h2v.s8.f5e4da10b15f from=translated src=- shape=ce4d0db5 vocab=9f0b31f8
-/
theorem rankSixForm_posDef (k : RankSixKind) :
    ∀ z : rankSixSpace k, z ≠ 0 → 0 < rankSixForm k z z := by
  cases k
  · exact prodForm_posDef (primaryModel_posDef .three .two) (primaryModel_posDef .five .zero)
  · exact H6Coordinates.form_posDef
  · exact prodForm_posDef (primaryModel_posDef .three .four) (primaryModel_posDef .five .four)
  · exact A4Q15Coordinates.form_posDef

/--
@isnad1 id=islattic.0h1v.s4.d30ebaaadc71 from=translated src=- shape=11d42590 vocab=3857f50d
-/
theorem rankSixBase_isLattice (k : RankSixKind) : IsLattice ℚ (rankSixBase k) := by
  cases k
  · exact isLattice_prod (primaryModel_isLattice .three .two) (primaryModel_isLattice .five .zero)
  · exact H6Coordinates.lattice_isLattice
  · exact isLattice_prod (primaryModel_isLattice .three .four) (primaryModel_isLattice .five .four)
  · exact A4Q15Coordinates.lattice_isLattice

/--
@isnad1 id=eq.0h1v.s4.944df420ecbd from=translated src=- shape=8e1bdd70 vocab=e235e92d
-/
theorem rankSixSpace_finrank (k : RankSixKind) : Module.finrank ℚ (rankSixSpace k) = 6 := by
  cases k
  · exact (mixedPrimary_finrank .two .zero).trans rfl
  · exact H6Coordinates.finrank_space
  · exact (mixedPrimary_finrank .four .four).trans rfl
  · exact A4Q15Coordinates.space_finrank

/--
@isnad1 id=eq.0h1v.s7.ed0639108c1c from=translated src=- shape=2b9a3e6a vocab=49f2ca1e
-/
theorem rankSixBase_dual (k : RankSixKind) :
    (rankSixForm k).dualSubmodule (rankSixBase k) =
      rankSixBase k ⊔ Submodule.span ℤ (Set.range (rankSixVector k)) := by
  cases k
  · exact mixedPrimary_dual .two .zero
  · exact H6Coordinates.matchingVector_dual
  · exact mixedPrimary_dual .four .four
  · exact A4Q15Coordinates.matchingVector_dual

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}

def rankSixCompletionLattice (k : RankSixKind)
    (S : PrimaryFamily B N .three k.threeShape) (T : PrimaryFamily B N .five k.fiveShape) :
    Submodule ℤ (W × rankSixSpace k) :=
  glueLattice N (rankSixBase k) (fun i => (mixedPrimarySource S T i, rankSixVector k i))

/--
@isnad1 id=and.5h6v.s8.c775ae03b832 from=translated src=- shape=fea820e3 vocab=ff05a660
-/
theorem complete_rankSix (k : RankSixKind)
    (S : PrimaryFamily B N .three k.threeShape) (T : PrimaryFamily B N .five k.fiveShape)
    (hs : B.IsSymm) (hl : IsLattice ℚ N) (hi : IsIntegral B N) (he : IsEven B N)
    (hd : B.dualSubmodule N = torsionPart B N 3 ⊔ torsionPart B N 5) :
    IsLattice ℚ (rankSixCompletionLattice k S T) ∧
      IsEven (prodForm B (rankSixForm k)) (rankSixCompletionLattice k S T) ∧
      (prodForm B (rankSixForm k)).dualSubmodule (rankSixCompletionLattice k S T) =
        rankSixCompletionLattice k S T := by
  cases k
  · exact complete_mixed_primary S T hs hl hi he hd
  · exact complete_h6 S T hs hl hi he hd
  · exact complete_mixed_primary S T hs hl hi he hd
  · exact complete_a4Q15 S T hs hl hi he hd

/--
@isnad1 id=lt.2h4v.s9.f0182818aa48 from=translated src=- shape=3d672479 vocab=ad90c932
-/
theorem rankSixCompletion_posDef (k : RankSixKind) (hpd : ∀ x : W, x ≠ 0 → 0 < B x x) :
    ∀ z : W × rankSixSpace k, z ≠ 0 → 0 < prodForm B (rankSixForm k) z z :=
  prodForm_posDef hpd (rankSixForm_posDef k)

/--
@isnad1 id=eq.0h2v.s6.13c8ce7f9eb6 from=translated src=- shape=ebe877d1 vocab=1b2601f0
-/
theorem rankSixCompletion_finrank [Module.Finite ℚ W] (k : RankSixKind) :
    Module.finrank ℚ (W × rankSixSpace k) = Module.finrank ℚ W + 6 := by
  rw [Module.finrank_prod, rankSixSpace_finrank]

end SRG266.Lattice
