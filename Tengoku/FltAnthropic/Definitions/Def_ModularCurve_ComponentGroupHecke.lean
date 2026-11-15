import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup
import Tengoku.Seed.LinearAlgebra.Dual.Defs
import Tengoku.Seed.Data.Matrix.Basic
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset

section DivisorAction
variable {ι : Type*} [Fintype ι]

def heckeDivisorAction (B : Matrix ι ι ℤ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) :=
  LinearMap.pi fun j => ∑ i : ι, B i j • LinearMap.proj i

/--
@isnad1 id=eq.0h4v.s7.7c5587088202 from=translated src=- shape=7fe00bb6 vocab=52e69f16
-/
@[simp] theorem heckeDivisorAction_apply (B : Matrix ι ι ℤ) (D : ι → ℤ) (j : ι) :
    heckeDivisorAction B D j = ∑ i : ι, B i j * D i := by
  simp [heckeDivisorAction, LinearMap.pi_apply, LinearMap.sum_apply]

abbrev HeckeRowSums (B : Matrix ι ι ℤ) (n : ℤ) : Prop :=
  ∀ i : ι, ∑ j : ι, B i j = n

abbrev HeckeWeightSymm (e : ι → ℕ) (B : Matrix ι ι ℤ) : Prop :=
  ∀ i j : ι, (e j : ℤ) * B i j = (e i : ℤ) * B j i

abbrev HeckeOffDiagDivides (e : ι → ℕ) (B : Matrix ι ι ℤ) : Prop :=
  ∀ i j : ι, i ≠ j → (e i : ℤ) ∣ B i j

/--
@isnad1 id=eq.1h4v.s8.e198b8a2623c from=translated src=- shape=cb7b6f2a vocab=228aae7b
-/
theorem degreeOn_heckeDivisorAction {B : Matrix ι ι ℤ} {n : ℤ} (h : HeckeRowSums B n)
    (D : ι → ℤ) : degreeOn ι (heckeDivisorAction B D) = n * degreeOn ι D := by
  simp only [degreeOn_apply, heckeDivisorAction_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, h i]

/--
@isnad1 id=mem.2h4v.s8.be80790b702a from=translated src=- shape=dc90fc94 vocab=c00e2c36
-/
theorem heckeDivisorAction_mem_characterLattice {B : Matrix ι ι ℤ} {n : ℤ}
    (h : HeckeRowSums B n) {D : ι → ℤ} (hD : D ∈ characterLattice ι) :
    heckeDivisorAction B D ∈ characterLattice ι := by
  rw [mem_characterLattice] at hD ⊢
  have := degreeOn_heckeDivisorAction h D
  rw [degreeOn_apply, degreeOn_apply, hD, mul_zero] at this
  exact this

def heckeCharacterAction (B : Matrix ι ι ℤ) {n : ℤ} (h : HeckeRowSums B n) :
    characterLattice ι →ₗ[ℤ] characterLattice ι :=
  (heckeDivisorAction B).restrict fun _ hD => heckeDivisorAction_mem_characterLattice h hD

/--
@isnad1 id=eq.1h4v.s10.61b6d4551558 from=translated src=- shape=8ac8cbb8 vocab=d7b080d8
-/
@[simp] theorem heckeCharacterAction_coe (B : Matrix ι ι ℤ) {n : ℤ} (h : HeckeRowSums B n)
    (D : characterLattice ι) :
    (heckeCharacterAction B h D : ι → ℤ) = heckeDivisorAction B D.1 :=
  rfl

end DivisorAction

section Equivariance
variable {ι : Type*} [Fintype ι]

/--
@isnad1 id=eq.1h5v.s10.e7126b0e9871 from=translated src=- shape=a9a80da6 vocab=ca2e675e
-/
theorem widthPairing_heckeDivisorAction {e : ι → ℕ} {B : Matrix ι ι ℤ}
    (hsym : HeckeWeightSymm e B) (D D' : ι → ℤ) :
    widthPairing e (heckeDivisorAction B D) D' =
      widthPairing e D (heckeDivisorAction B D') := by
  simp only [widthPairing_apply, heckeDivisorAction_apply]
  have lhs_eq : ∀ j : ι, (e j : ℤ) * ((∑ i : ι, B i j * D i) * D' j) =
      ∑ i : ι, (e j : ℤ) * B i j * (D i * D' j) := fun j => by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have rhs_eq : ∀ i : ι, (e i : ℤ) * (D i * ∑ j : ι, B j i * D' j) =
      ∑ j : ι, (e i : ℤ) * B j i * (D i * D' j) := fun i => by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [lhs_eq, rhs_eq]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    linear_combination (D i * D' j) * hsym i j

/--
@isnad1 id=eq.2h5v.s13.e2d73d5ff3bf from=translated src=- shape=da1d6bfe vocab=5e1e2a53
-/
theorem gramMap_heckeCharacterAction {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (h : HeckeRowSums B n) (hsym : HeckeWeightSymm e B) (D : characterLattice ι) :
    gramMap e (heckeCharacterAction B h D) =
      (heckeCharacterAction B h).dualMap (gramMap e D) := by
  apply LinearMap.ext
  intro D'
  rw [LinearMap.dualMap_apply']
  show widthPairing e (heckeCharacterAction B h D : ι → ℤ) D'.1 =
    widthPairing e D.1 (heckeCharacterAction B h D' : ι → ℤ)
  rw [heckeCharacterAction_coe, heckeCharacterAction_coe]
  exact widthPairing_heckeDivisorAction hsym D.1 D'.1

/--
@isnad1 id=le.2h4v.s13.7c6e8ed18eeb from=translated src=- shape=2721fb60 vocab=73c1688d
-/
theorem range_gramMap_le_comap_dualMap {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (h : HeckeRowSums B n) (hsym : HeckeWeightSymm e B) :
    LinearMap.range (gramMap e) ≤
      Submodule.comap (heckeCharacterAction B h).dualMap (LinearMap.range (gramMap e)) := by
  rintro _ ⟨D, rfl⟩
  exact ⟨heckeCharacterAction B h D, gramMap_heckeCharacterAction h hsym D⟩

def heckeComponentAction (e : ι → ℕ) (B : Matrix ι ι ℤ) {n : ℤ} (h : HeckeRowSums B n)
    (hsym : HeckeWeightSymm e B) : componentGroup e →ₗ[ℤ] componentGroup e :=
  Submodule.mapQ _ _ (heckeCharacterAction B h).dualMap
    (range_gramMap_le_comap_dualMap h hsym)

/--
@isnad1 id=eq.2h5v.s15.7f0c23db0c0e from=translated src=- shape=20db416c vocab=e162ee8d
-/
@[simp] theorem componentGroupProj_heckeComponentAction {e : ι → ℕ} {B : Matrix ι ι ℤ} {n : ℤ}
    (h : HeckeRowSums B n) (hsym : HeckeWeightSymm e B)
    (φ : Module.Dual ℤ (characterLattice ι)) :
    heckeComponentAction e B h hsym (componentGroupProj e φ) =
      componentGroupProj e ((heckeCharacterAction B h).dualMap φ) :=
  rfl

end Equivariance

end ModularCurve
