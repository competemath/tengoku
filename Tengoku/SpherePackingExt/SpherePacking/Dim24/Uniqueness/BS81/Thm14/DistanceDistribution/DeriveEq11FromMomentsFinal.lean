module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.DistanceDistribution.Defs
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.InnerMvPoly24
import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgInnerMoments24Final
import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgMoments
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deriving BS81 equation (11) from moment identities

This file derives the BS81 distance distribution (equation (11)) from:

* the finite support constraint `⟪u,v⟫ ∈ {1, -1, ±1/2, ±1/4, 0}`, and
* the spherical-design moment identities up to degree `4`.

## Main statement
* `dist_eq11_of_design10_and_support`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

open MeasureTheory Polynomial

open Uniqueness.BS81

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Expanding sums over the explicit support finset

`bs81Support24 : Finset ℝ` is a concrete `Finset` literal. To avoid relying on `simp` making
progress through `Finset` sums over `ℝ`, we use a dedicated expansion lemma.
-/

lemma sum_bs81Support24 (f : ℝ → ℝ) :
    (∑ t ∈ bs81Support24, f t) =
      f (1 : ℝ) + f (-1 : ℝ) + f (1 / 2 : ℝ) + f (-1 / 2 : ℝ) +
        f (1 / 4 : ℝ) + f (-1 / 4 : ℝ) + f (0 : ℝ) := by
  have h1 :
      (1 : ℝ) ∉
        ({(-1 : ℝ), (1 / 2 : ℝ), (-1 / 2 : ℝ), (1 / 4 : ℝ), (-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hneg1 :
      (-1 : ℝ) ∉ ({(1 / 2 : ℝ), (-1 / 2 : ℝ), (1 / 4 : ℝ), (-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hhalf :
      (1 / 2 : ℝ) ∉ ({(-1 / 2 : ℝ), (1 / 4 : ℝ), (-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hneghalf :
      (-1 / 2 : ℝ) ∉ ({(1 / 4 : ℝ), (-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hquarter :
      (1 / 4 : ℝ) ∉ ({(-1 / 4 : ℝ), (0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_insert, Finset.mem_singleton]
    grind
  have hnegquarter : (-1 / 4 : ℝ) ∉ ({(0 : ℝ)} : Finset ℝ) := by
    simp [Finset.mem_singleton]
  unfold bs81Support24
  rw [Finset.sum_insert h1]
  rw [Finset.sum_insert hneg1]
  rw [Finset.sum_insert hhalf]
  rw [Finset.sum_insert hneghalf]
  rw [Finset.sum_insert hquarter]
  rw [Finset.sum_insert hnegquarter]
  simp [Finset.sum_singleton]
  ac_rfl

/-!
## A homogeneous polynomial encoding `v ↦ ⟪u,v⟫`
-/

attribute [grind =] mvPolyEval24_innerMvPoly24_pow

/-!
## Odd spherical moments vanish by symmetry
-/

/-!
## Main derivation: solve for the distance distribution
-/

lemma r13_of_e13 (d1 d2 : ℝ)
    (e13 :
      (1 / 2 : ℝ) * d1 + (1 / 4 : ℝ) * d2 = (1 / 8 : ℝ) * d1 + (1 / 64 : ℝ) * d2) :
    (8 : ℝ) * d1 + (5 : ℝ) * d2 = 0 := by
  nlinarith

lemma r35_of_e35 (d1 d2 : ℝ)
    (e35 :
      (1 / 8 : ℝ) * d1 + (1 / 64 : ℝ) * d2 = (1 / 32 : ℝ) * d1 + (1 / 1024 : ℝ) * d2) :
    (32 : ℝ) * d1 + (5 : ℝ) * d2 = 0 := by
  nlinarith

lemma d1_eq_zero_of_r13_r35 (d1 d2 : ℝ)
    (r13 : (8 : ℝ) * d1 + (5 : ℝ) * d2 = 0) (r35 : (32 : ℝ) * d1 + (5 : ℝ) * d2 = 0) :
    d1 = 0 := by
  nlinarith

lemma d2_eq_zero_of_r13_d1 (d1 d2 : ℝ) (r13 : (8 : ℝ) * d1 + (5 : ℝ) * d2 = 0) (hd1 : d1 = 0) :
    d2 = 0 := by
  nlinarith

lemma solve_odd_subsystem (Aneg1 Ahalf Aneghalf Aquarter Anegquarter : ℝ)
    (hm1 :
      1 - Aneg1 + (1 / 2 : ℝ) * (Ahalf - Aneghalf) + (1 / 4 : ℝ) * (Aquarter - Anegquarter) = 0)
    (hm3 :
      1 - Aneg1 + (1 / 8 : ℝ) * (Ahalf - Aneghalf) + (1 / 64 : ℝ) * (Aquarter - Anegquarter) = 0)
    (hm5 :
      1 - Aneg1 + (1 / 32 : ℝ) * (Ahalf - Aneghalf) +
          (1 / 1024 : ℝ) * (Aquarter - Anegquarter) = 0) :
    Ahalf = Aneghalf ∧ Aquarter = Anegquarter ∧ Aneg1 = 1 := by
  grind only

lemma solve_even_subsystem (Aneg1 Ahalf Aneghalf Aquarter Anegquarter Azero : ℝ)
    (hAhalf : Ahalf = Aneghalf) (hAquarter : Aquarter = Anegquarter) (hAneg1 : Aneg1 = 1)
    (hm2 :
      1 + Aneg1 + (1 / 4 : ℝ) * (Ahalf + Aneghalf) + (1 / 16 : ℝ) * (Aquarter + Anegquarter) = 8190)
    (hm4 :
      1 + Aneg1 + (1 / 16 : ℝ) * (Ahalf + Aneghalf) +
          (1 / 256 : ℝ) * (Aquarter + Anegquarter) = 945)
    (hcountR : Aneg1 + Ahalf + Aneghalf + Aquarter + Anegquarter + Azero = 196559) :
    Ahalf = 4600 ∧ Aquarter = 47104 ∧ Azero = 93150 := by
  grind only

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
