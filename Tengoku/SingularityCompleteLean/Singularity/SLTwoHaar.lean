import Tengoku.SingularityCompleteLean.Singularity.ShearContraction
import Tengoku.Seed.MeasureTheory.Group.ModularCharacter
import Tengoku.Seed.GroupTheory.Abelianization.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unimodularity of SL(2,ℝ)

The group is perfect, so its modular character is trivial. Therefore its
regular left Haar measures are also right invariant. The compactness and
Polish-space instances are obtained from the closed determinant-one locus.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped MatrixGroups

namespace Singularity

/--
@isnad1 id=locallyc.0h0v.s5.997899069767 from=translated src=- shape=b781e9e2 vocab=79048773
-/
theorem slTwo_locallyCompactSpace : LocallyCompactSpace SL(2, ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

/--
@isnad1 id=polishsp.0h0v.s5.3ab1cf1832a6 from=translated src=- shape=b781e9e2 vocab=4a48d1cc
-/
theorem slTwo_polishSpace : PolishSpace SL(2, ℝ) := by
  let : PolishSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (PolishSpace (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace

/-- Every character into a commutative monoid is trivial on SL(2,ℝ).
@isnad1 id=eq.0h3v.s8.c68841aa66a5 from=translated src=- shape=d0f3aea1 vocab=2af01502
-/
theorem slTwo_character_eq_one {C : Type*} [CommMonoid C]
    (f : SL(2, ℝ) →* C) (g : SL(2, ℝ)) : f g = 1 := by
  have hp : commutator SL(2, ℝ) = ⊤ :=
    Matrix.SL2.commutator_eq_top (a := (2 : ℝ)) (by norm_num) (by norm_num)
  have hk := Abelianization.commutator_subset_ker f.toHomUnits
  rw [hp] at hk
  have hg : f.toHomUnits g = 1 := hk (Subgroup.mem_top g)
  exact congrArg (fun u : Cˣ => (u : C)) hg

/-- The actual modular character is identically one.
@isnad1 id=eq.0h1v.s6.2f57b1e64c76 from=translated src=- shape=ab296cc5 vocab=c4352526
-/
theorem slTwo_modularCharacter_eq_one (g : SL(2, ℝ)) :
    letI := slTwo_locallyCompactSpace
    modularCharacterFun g = 1 := by
  let := slTwo_locallyCompactSpace
  exact slTwo_character_eq_one modularCharacter g

/-- A regular left Haar measure on SL(2,ℝ) is also right invariant.
@isnad1 id=ismulrig.0h1v.s8.650054b7fd08 from=translated src=- shape=4c81dfc6 vocab=d257c234
-/
theorem slTwo_haar_rightInvariant [MeasurableSpace SL(2, ℝ)] [BorelSpace SL(2, ℝ)]
    (ν : Measure SL(2, ℝ)) [IsHaarMeasure ν] [ν.InnerRegular] : ν.IsMulRightInvariant := by
  let := slTwo_locallyCompactSpace
  refine ⟨fun g => ?_⟩
  rw [map_right_mul_eq_modularCharacterFun_smul ν g, slTwo_modularCharacter_eq_one, one_smul]

end Singularity
