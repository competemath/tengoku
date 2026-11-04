/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveSpace
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual coordinate hyperplanes over a commutative ring

Setting the first variable to zero gives a graded polynomial restriction with a
homogeneous right inverse. Its homogeneous localizations are surjective, so the
actual Proj morphism is a closed immersion. Its polynomial kernel is exactly the
first-coordinate ideal; surjective homogeneous prime correspondence identifies
its image with the coordinate zero locus. No field hypothesis or assumed
immersion is used.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace SchemeProjectiveSpace
attribute [local instance] gradedAlgebra
variable (R : Type u) [CommRing R] (n : ℕ)

/-- Set the first coordinate to zero and retain the remaining coordinates.-/
def coordinateRestriction : Polynomial R (n + 1) →+* Polynomial R n :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 0 MvPolynomial.X)

/--
@isnad1 id=eq.0h3v.s9.864ae682326a from=translated src=- shape=98ed974b vocab=4749454a
-/
@[simp] theorem coordinateRestriction_C (r : R) :
    coordinateRestriction R n (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [coordinateRestriction]

/--
@isnad1 id=eq.0h2v.s8.e33e1dd02c05 from=translated src=- shape=a0e460c1 vocab=e5509ac9
-/
@[simp] theorem coordinateRestriction_X_zero :
    coordinateRestriction R n (MvPolynomial.X 0) = 0 := by
  simp [coordinateRestriction]

/--
@isnad1 id=eq.0h3v.s8.061dadfaa775 from=translated src=- shape=f6c6ca2a vocab=477e1548
-/
@[simp] theorem coordinateRestriction_X_succ (i : Fin (n + 1)) :
    coordinateRestriction R n (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [coordinateRestriction]

/-- The coordinate restriction preserves every homogeneous degree.-/
def coordinateRestrictionGraded : grading R (n + 1) →+*ᵍ grading R n where
  toRingHom := coordinateRestriction R n
  map_mem {i} {p} hp := by
    change MvPolynomial.IsHomogeneous _ i
    simpa only [one_mul, coordinateRestriction, MvPolynomial.coe_eval₂Hom] using hp.eval₂ MvPolynomial.C
      (Fin.cases 0 MvPolynomial.X) (fun r => MvPolynomial.isHomogeneous_C (Fin (n + 1)) r)
      (fun j => Fin.cases (MvPolynomial.isHomogeneous_zero (Fin (n + 1)) R 1)
        (fun k => MvPolynomial.isHomogeneous_X R k) j)

/-- Renaming into the retained coordinates is a right inverse.
@isnad1 id=eq.0h3v.s10.b674cd14e08c from=translated src=- shape=2170c7cf vocab=a1bb6b0f
-/
theorem coordinateRestriction_rename (p : Polynomial R n) :
    coordinateRestriction R n (MvPolynomial.rename Fin.succ p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Every homogeneous polynomial has a lift in the same degree.
@isnad1 id=ex.1h4v.s10.718ad80957ea from=translated src=- shape=b698c827 vocab=6f9212c3
-/
theorem coordinateRestriction_degree_surjective (d : ℕ) (p : Polynomial R n)
    (hp : p ∈ grading R n d) :
    ∃ a ∈ grading R (n + 1) d, coordinateRestrictionGraded R n a = p :=
  ⟨MvPolynomial.rename Fin.succ p, hp.rename_isHomogeneous,
    coordinateRestriction_rename R n p⟩

/-- The positivity condition defining the actual projective morphism.
@isnad1 id=le.0h2v.s10.808b39913552 from=translated src=- shape=b5fbf898 vocab=8ba6772d
-/
theorem coordinateRestriction_irrelevant_le :
    HomogeneousIdeal.irrelevant (grading R n) ≤
      (HomogeneousIdeal.irrelevant (grading R (n + 1))).map
        (coordinateRestrictionGraded R n) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro d hd p hp
  obtain ⟨a, ha, rfl⟩ := coordinateRestriction_degree_surjective R n d p hp
  exact Ideal.mem_map_of_mem (coordinateRestrictionGraded R n)
    (HomogeneousIdeal.mem_irrelevant_of_mem (grading R (n + 1)) hd ha)

/-- The actual coordinate hyperplane embedding in projective space.-/
def coordinateHyperplaneι : space R n ⟶ space R (n + 1) :=
  Proj.map (coordinateRestrictionGraded R n) (coordinateRestriction_irrelevant_le R n)

/-- The first-coordinate equation generates the kernel.
@isnad1 id=mem.0h3v.s10.664e7b7ca0cf from=translated src=- shape=9a273252 vocab=84f98584
-/
theorem coordinateRestriction_sub_rename_mem (p : Polynomial R (n + 1)) :
    p - MvPolynomial.rename Fin.succ (coordinateRestriction R n p) ∈
      Ideal.span {MvPolynomial.X (R := R) (0 : Fin (n + 2))} := by
  let I : Ideal (Polynomial R (n + 1)) := Ideal.span {MvPolynomial.X 0}
  change _ ∈ I
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
      simpa only [map_add, add_sub_add_comm] using I.add_mem hp hq
  | mul_X p i hp =>
      induction i using Fin.cases with
      | zero =>
          simp only [map_mul, coordinateRestriction_X_zero, mul_zero, map_zero, sub_zero]
          exact I.mul_mem_left p (Ideal.subset_span (Set.mem_singleton _))
      | succ j =>
          simp only [map_mul, coordinateRestriction_X_succ, MvPolynomial.rename_X]
          rw [← sub_mul]
          exact I.mul_mem_right _ hp

end SchemeProjectiveSpace
