module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.GradedBinaryLaurentOperators
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LaurentProjectedResidueOperators
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LaurentAuxiliaryScalarOperators
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylActualChartMaps
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.CyclicScalarTower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The concrete polynomial profile operators and their projected Laurent
adjoints, on the actual weighted homogeneous coefficient spaces. -/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module
variable {K : Type*} [Field K] {ι : Type*}

/--
@isnad1 id=eq.0h6v.s9.42d7b512659f from=translated src=- shape=a8e61a03 vocab=6dacb782
-/
theorem vectorResidueFunctional_scalar_transpose [Fintype ι] (w : ι → K)
    (c : BinaryLaurent K) (q p : ι → BinaryLaurent K) :
    vectorResidueFunctional w q (fun i => c * p i) =
      vectorResidueFunctional w (fun i => c * q i) p := by
  rw [vectorResidueFunctional_apply, vectorResidueFunctional_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, mul_comm (q i) c]

/--
@isnad1 id=mem.1h5v.s9.8eea911d61bc from=translated src=- shape=f4454b60 vocab=c1c3970a
-/
theorem freeNegativePart_mem_negativeGrade_of_overlap (g : ι → ℤ) (r : ℤ)
    (p : FreeLaurent K ι)
    (hp : p ∈ LaurentChartComplex.overlapGrade (fun i => 2 - g i) (-r)) :
    freeNegativePart p ∈ negativeGrade (K := K) g r := by
  classical
  apply (Finsupp.mem_supported K _).mpr
  rintro ⟨i,e⟩ he
  have hn : freeNegativePart p (i,e) ≠ 0 := Finsupp.mem_support_iff.mp he
  rw [freeNegativePart_apply] at hn
  split_ifs at hn with hneg
  · have hdeg := (Finsupp.mem_supported K p).mp hp (Finsupp.mem_support_iff.mpr hn)
    exact ⟨hneg.1,hneg.2,hdeg⟩
  · exact False.elim (hn rfl)

/--
@isnad1 id=mem.0h5v.s9.3dd7c1ff6b76 from=translated src=- shape=830da090 vocab=db1a5f0e
-/
theorem negativeGrade_mem_overlap (g : ι → ℤ) (r : ℤ)
    (p : negativeGrade (K := K) g r) :
    p.val ∈ LaurentChartComplex.overlapGrade (fun i => 2 - g i) (-r) := by
  apply (Finsupp.mem_supported K p.val).mpr
  intro e he
  exact ((Finsupp.mem_supported K p.val).mp p.property he).2.2

end ChoppedPlane.LaurentPairing

namespace ChoppedPlane.QWeyl
open MvPolynomial Module LaurentPairing LaurentChartComplex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K]

/-- The actual `u`, `v`, and forward cyclic actions on free Laurent vectors.-/
def rawLaurentProfileOperators (q : K) (s : CubicProfile) :
    Fin 3 → (FreeLaurent K (Fin 3) →ₗ[K] FreeLaurent K (Fin 3)) :=
  ![laurentScalar U, laurentScalar V, laurentCyclicZ q s]

/-- The actual coefficientwise dual actions before top-Laurent projection.-/
def rawLaurentProfileDualOperators (q : K) (s : CubicProfile) :
    Fin 3 → (FreeLaurent K (Fin 3) →ₗ[K] FreeLaurent K (Fin 3)) :=
  ![laurentScalar U, laurentScalar V, laurentCyclicZDual q s]

/--
@isnad1 id=eq.0h1v.s5.79b7cef08205 from=translated src=- shape=ce08f92e vocab=25466d4b
-/
theorem dualGeneratorWeights_int (s : CubicProfile) :
    (fun i => (dualGeneratorWeights s i : ℤ)) =
      (fun i => 2 - (generatorWeights s i : ℤ)) := by
  funext i
  cases s <;> fin_cases i <;> norm_num [dualGeneratorWeights, generatorWeights]

/-- The raw dual Laurent operators are precisely the three actions of the
actual chart cubic quotient ring.
@isnad1 id=eq.1h5v.s12.f8ed1ad69f60 from=translated src=- shape=6569aa54 vocab=d37d414e
-/
theorem rawLaurentProfileDualOperators_chart_action
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    letI := cyclicModuleScalarTower (K := K)
      (binaryChartLaurentMap (binaryCubic K))
      (chartDualZ binaryChartLaurentMap q s)
      (chartDualZ_cube binaryChartLaurentMap q hq s)
    ∀ (i : Fin 3) (p : FreeLaurent K (Fin 3)),
      freeLaurentEquiv (rawLaurentProfileDualOperators q s i p) =
        scalarAction (K := K) (chartLinearForm (binaryChartLaurentMap (K := K)) i)
          (freeLaurentEquiv p) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  let := cyclicModuleScalarTower (K := K)
    (binaryChartLaurentMap (binaryCubic K))
    (chartDualZ binaryChartLaurentMap q s)
    (chartDualZ_cube binaryChartLaurentMap q hq s)
  intro i p
  rw [scalarAction_apply]
  fin_cases i
  · change freeLaurentEquiv (laurentScalar U p) =
      cyclicCoefficientHom _ (binaryChartLaurentMap (binaryU K)) • freeLaurentEquiv p
    rw [cyclicModule_coefficient_smul, binaryChartLaurentMap_binaryU]
    funext j
    simp only [freeLaurentEquiv_laurentScalar, Pi.smul_apply, smul_eq_mul]
  · change freeLaurentEquiv (laurentScalar V p) =
      cyclicCoefficientHom _ (binaryChartLaurentMap (binaryV K)) • freeLaurentEquiv p
    rw [cyclicModule_coefficient_smul, binaryChartLaurentMap_binaryV]
    funext j
    simp only [freeLaurentEquiv_laurentScalar, Pi.smul_apply, smul_eq_mul]
  · change freeLaurentEquiv (laurentCyclicZDual q s p) = cyclicRoot _ • freeLaurentEquiv p
    rw [cyclicModule_root_smul, freeLaurentEquiv_laurentCyclicZDual]
    rfl

end ChoppedPlane.QWeyl
