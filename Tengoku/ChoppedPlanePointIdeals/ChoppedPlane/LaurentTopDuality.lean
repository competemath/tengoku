module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LaurentWeightedPairing
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LaurentChartComplex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The factorial-weighted perfect pairing on the actual graded top Laurent
representatives. Its composition with the actual chart projection is
surjective and has exactly the actual chart difference as kernel. -/
noncomputable section
namespace ChoppedPlane.LaurentChartComplex
open LaurentPairing Module
variable {K : Type*} [Field K] {J : Type*}

/-- Actual finite top grade perfectly dual to the complementary polynomial
grade, with literal auxiliary factorial weights.-/
def topGradeAuxiliaryResidueDualEquiv [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ) :
    topGrade (K := K) (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r) ≃ₗ[K]
      Module.Dual K (positiveGrade (K := K) (auxiliaryGeneratorWeights g t) r) :=
  (topGradeNegativeEquiv (K := K) (auxiliaryGeneratorWeights g t) r).trans
    (auxiliaryResidueDualEquiv g r t)

/-- The actual overlap-to-dual map, obtained by top Laurent projection and
the literal factorial-weighted residue pairing.-/
def topAuxiliaryResidueMap [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ) :
    overlapGrade (K := K) (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r) →ₗ[K]
      Module.Dual K (positiveGrade (K := K) (auxiliaryGeneratorWeights g t) r) :=
  (topGradeAuxiliaryResidueDualEquiv g r t).toLinearMap.comp
    (topProjection (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r))

/--
@isnad1 id=surjecti.0h5v.s12.6b4c8ef14c5f from=translated src=- shape=9c82776c vocab=ea6251f0
-/
theorem topAuxiliaryResidueMap_surjective [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ) :
    Function.Surjective (topAuxiliaryResidueMap (K := K) g r t) :=
  (topGradeAuxiliaryResidueDualEquiv g r t).surjective.comp
    (topProjection_surjective (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r))

/-- The actual chart boundaries are exactly the kernel of the surjective
perfect residue map, proving the top cohomology quotient interpretation.
@isnad1 id=eq.0h5v.s12.7036b8b687df from=translated src=- shape=ceb0dad8 vocab=feede01c
-/
theorem ker_topAuxiliaryResidueMap [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ) :
    LinearMap.ker (topAuxiliaryResidueMap (K := K) g r t) =
      LinearMap.range (chartDifference (K := K)
        (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r)) := by
  rw [← ker_topProjection]
  ext p
  simp only [LinearMap.mem_ker, topAuxiliaryResidueMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  exact (topGradeAuxiliaryResidueDualEquiv g r t).map_eq_zero_iff

end ChoppedPlane.LaurentChartComplex
