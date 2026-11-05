module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QuarticKernelGlobal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The global quartic symmetric-kernel theorem specialized to the literal
cyclic binary coefficient modules, including their dual actions. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
variable {K : Type*} [Field K] [CharZero K]

/-- Both transpose choices are genuine cubic-ring coefficient modules.-/
def quarticCyclicZ {A : Type*} [CommRing A] (dual : Bool) (γ : Fin 3 → A) :
    End A (Fin 3 → A) := if dual then cyclicZDual γ else cyclicZ γ

theorem quarticCyclicZ_cube {A : Type*} [CommRing A]
    (dual : Bool) (γ : Fin 3 → A) :
    quarticCyclicZ dual γ ^ 3 = (γ 0 * γ 1 * γ 2) • 1 := by
  cases dual
  · exact cyclicZ_cube γ
  · exact cyclicZDual_cube γ

theorem quarticCyclicZ_baseChange {A A' : Type*} [CommRing A] [CommRing A']
    (φ : A →+* A') (dual : Bool) (γ : Fin 3 → A) (m : Fin 3 → A) :
    cyclicVectorBaseChange φ (quarticCyclicZ dual γ m) =
      quarticCyclicZ dual (fun i => φ (γ i)) (cyclicVectorBaseChange φ m) := by
  cases dual
  · exact cyclicZ_baseChange φ γ m
  · exact cyclicZDual_baseChange φ γ m

theorem quarticU_binary_ne_zero :
    quarticU (binaryU K) (binaryV K) ≠ 0 := by
  intro h
  have he := congrArg (eval ![1,0]) h
  simp [quarticU, binaryU, binaryV] at he

theorem quarticV_binary_ne_zero :
    quarticV (binaryU K) (binaryV K) ≠ 0 := by
  intro h
  have he := congrArg (eval ![0,1]) h
  simp [quarticV, binaryU, binaryV] at he

end ChoppedPlane.QWeyl
