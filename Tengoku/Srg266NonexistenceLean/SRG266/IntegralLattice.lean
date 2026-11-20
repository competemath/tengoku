/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.ProjectorClasses
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm
import Tengoku.Seed.LinearAlgebra.Quotient.Bilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def integralGramForm (x : V) :
    LinearMap.BilinForm ℤ
      (SecondSubconstituent G x → ℤ) :=
  Matrix.toBilin' (localGramMatrix G x)

/--
@isnad1 id=issymm.0h3v.s6.382abd13ede2 from=translated src=- shape=5838eae1 vocab=be7668f6
-/
theorem integralGramForm_isSymm (x : V) :
    (integralGramForm G x).IsSymm := by
  rw [integralGramForm, Matrix.isSymm_toBilin'_iff_isSymm]
  exact localGramMatrix_isSymm G x

/--
@isnad1 id=isrefl.0h3v.s6.35656d7ea669 from=translated src=- shape=5838eae1 vocab=a7db974f
-/
theorem integralGramForm_isRefl (x : V) :
    (integralGramForm G x).IsRefl :=
  (integralGramForm_isSymm G x).isRefl

def integralGramRelations (x : V) :
    Submodule ℤ (SecondSubconstituent G x → ℤ) :=
  (integralGramForm G x).ker

def integralGramKernel (x : V) :
    Submodule ℤ (SecondSubconstituent G x → ℤ) :=
  LinearMap.ker (localGramMatrix G x).mulVecLin

/--
@isnad1 id=eq.0h3v.s6.05e8c00604b8 from=translated src=- shape=17ad61eb vocab=fd3d1573
-/
theorem integralGramKernel_eq_relations (x : V) :
    integralGramKernel G x = integralGramRelations G x := by
  ext z
  constructor
  · intro hz
    rw [integralGramRelations, LinearMap.mem_ker]
    apply LinearMap.ext
    intro y
    change Matrix.toBilin' (localGramMatrix G x) z y = 0
    rw [Matrix.toBilin'_apply]
    calc
      (∑ i, ∑ j, z i * localGramMatrix G x i j * y j) =
          ∑ j, (∑ i, localGramMatrix G x j i * z i) * y j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [localGramMatrix_comm G x i j]
        ring
      _ = 0 := by
        have hz' :
            localGramMatrix G x *ᵥ z = 0 := by
          exact (LinearMap.mem_ker.mp hz)
        apply Finset.sum_eq_zero
        intro j _
        have hj :
            ∑ i, localGramMatrix G x j i * z i = 0 := by
          have := congrFun hz' j
          simpa [Matrix.mulVec_apply, dotProduct] using this
        rw [hj, zero_mul]
  · intro hz
    rw [integralGramKernel, LinearMap.mem_ker]
    funext B
    have hz' :
        integralGramForm G x z = 0 :=
      LinearMap.mem_ker.mp hz
    have hB := congrArg
      (fun φ : (SecondSubconstituent G x → ℤ) →ₗ[ℤ] ℤ =>
        φ (Pi.single B 1)) hz'
    change
      Matrix.toBilin' (localGramMatrix G x) z (Pi.single B 1) = 0 at hB
    change
      ∑ C, localGramMatrix G x B C * z C = 0
    simpa [Matrix.toBilin'_apply, Pi.single_apply,
      localGramMatrix_comm G x, mul_comm] using hB

abbrev IntegralGramLattice (x : V) :=
  (SecondSubconstituent G x → ℤ) ⧸ integralGramRelations G x

def integralGramPairing (x : V) :
    LinearMap.BilinForm ℤ (IntegralGramLattice G x) :=
  LinearMap.IsRefl.liftQ₂
    (integralGramForm G x)
    (integralGramRelations G x)
    (integralGramForm_isRefl G x)
    le_rfl

def integralGramGenerator (x : V)
    (B : SecondSubconstituent G x) :
    IntegralGramLattice G x :=
  Submodule.Quotient.mk (Pi.single B 1)

/--
@isnad1 id=eq.0h5v.s10.56d812f95cfe from=translated src=- shape=6c816d6c vocab=7df511f1
-/
@[simp]
theorem integralGramPairing_generator_generator
    (x : V) (B C : SecondSubconstituent G x) :
    integralGramPairing G x
        (integralGramGenerator G x B)
        (integralGramGenerator G x C) =
      localGramMatrix G x B C := by
  change
    Matrix.toBilin' (localGramMatrix G x)
        (Pi.single B 1) (Pi.single C 1) =
      localGramMatrix G x B C
  exact Matrix.toBilin'_single (localGramMatrix G x) B C

def integralGramGeneratorSum (x : V) :
    IntegralGramLattice G x :=
  ∑ B, integralGramGenerator G x B

/--
@isnad1 id=eq.0h3v.s7.11d894cb3062 from=translated src=- shape=dd3af504 vocab=764f739c
-/
theorem integralGramGeneratorSum_eq_mk_one
    (x : V) :
    integralGramGeneratorSum G x =
      (Submodule.Quotient.mk
        (1 : SecondSubconstituent G x → ℤ) :
          IntegralGramLattice G x) := by
  rw [integralGramGeneratorSum]
  change
    (∑ B, (integralGramRelations G x).mkQ (Pi.single B 1)) =
      (integralGramRelations G x).mkQ 1
  rw [← map_sum]
  congr 1
  funext C
  simp [Pi.single_apply]

/--
@isnad1 id=eq.1h4v.s10.60c10e705c38 from=translated src=- shape=78da79df vocab=ae035fa5
-/
theorem integralGramPairing_sum_generator
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    integralGramPairing G x
        (integralGramGeneratorSum G x)
        (integralGramGenerator G x B) = 165 := by
  rw [integralGramGeneratorSum, map_sum, LinearMap.sum_apply]
  change
    (∑ C, integralGramPairing G x
      (integralGramGenerator G x C)
      (integralGramGenerator G x B)) = 165
  simp_rw [integralGramPairing_generator_generator G x]
  rw [← localGramMatrix_row_sum G hG x B]
  apply Finset.sum_congr rfl
  intro C _
  exact localGramMatrix_comm G x C B

/--
@isnad1 id=eq.1h3v.s10.87940adbad0d from=translated src=- shape=e039423d vocab=d9c1b1e3
-/
theorem integralGramPairing_sum_sum
    (hG : IsHypothetical G) (x : V) :
    integralGramPairing G x
        (integralGramGeneratorSum G x)
        (integralGramGeneratorSum G x) = 36300 := by
  rw [integralGramGeneratorSum, map_sum]
  calc
    (∑ B, integralGramPairing G x
        (∑ C, integralGramGenerator G x C)
        (integralGramGenerator G x B)) =
        ∑ _B : SecondSubconstituent G x, (165 : ℤ) := by
      apply Finset.sum_congr rfl
      intro B _
      rw [map_sum, LinearMap.sum_apply]
      simp_rw [integralGramPairing_generator_generator G x]
      rw [← localGramMatrix_row_sum G hG x B]
      apply Finset.sum_congr rfl
      intro C _
      exact localGramMatrix_comm G x C B
    _ = 36300 := by
      simp [secondSubconstituent_card G hG x]

def HasMod11KernelLift (x : V) : Prop :=
  ∃ z : SecondSubconstituent G x → ℤ,
    z ∈ integralGramRelations G x ∧
      ∀ B, ∃ a : ℤ, 1 - z B = 11 * a

/--
@isnad1 id=ex.1h3v.s7.b036adb69ed9 from=translated src=- shape=b658ee9f vocab=a1e11a9e
-/
theorem exists_integral_centroid_of_mod11KernelLift
    (x : V) (hlift : HasMod11KernelLift G x) :
    ∃ c : IntegralGramLattice G x,
      (11 : ℤ) • c = integralGramGeneratorSum G x := by
  rcases hlift with ⟨z, hz, hcongr⟩
  choose a ha using hcongr
  let c : IntegralGramLattice G x :=
    Submodule.Quotient.mk a
  refine ⟨c, ?_⟩
  have hone :
      (1 : SecondSubconstituent G x → ℤ) =
        (11 : ℤ) • a + z := by
    funext B
    have h := ha B
    change 1 = 11 * a B + z B
    omega
  calc
    (11 : ℤ) • c =
        Submodule.Quotient.mk ((11 : ℤ) • a) := by
      change
        (11 : ℤ) • Submodule.Quotient.mk a =
          Submodule.Quotient.mk ((11 : ℤ) • a)
      exact (Submodule.Quotient.mk_smul
        (integralGramRelations G x) (11 : ℤ) a).symm
    _ = Submodule.Quotient.mk ((11 : ℤ) • a + z) := by
      rw [Submodule.Quotient.mk_add,
        (Submodule.Quotient.mk_eq_zero _).mpr hz, add_zero]
    _ = Submodule.Quotient.mk
        (1 : SecondSubconstituent G x → ℤ) := by
      rw [← hone]
    _ = integralGramGeneratorSum G x :=
      (integralGramGeneratorSum_eq_mk_one G x).symm

/--
@isnad1 id=eq.2h5v.s10.42336fecae8c from=translated src=- shape=b2a1d69e vocab=2b2c3f50
-/
theorem integral_centroid_pairing_generator
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    integralGramPairing G x c (integralGramGenerator G x B) = 15 := by
  have h := congrArg
    (fun u => integralGramPairing G x u (integralGramGenerator G x B)) hc
  rw [integralGramPairing_sum_generator G hG x B] at h
  simp at h
  omega

/--
@isnad1 id=eq.2h4v.s10.552fc83f98c4 from=translated src=- shape=05175be3 vocab=c477bedc
-/
theorem integral_centroid_norm
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    integralGramPairing G x c c = 300 := by
  have h := congrArg₂
    (fun u v => integralGramPairing G x u v) hc hc
  rw [integralGramPairing_sum_sum G hG x] at h
  simp at h
  nlinarith

end SRG266
