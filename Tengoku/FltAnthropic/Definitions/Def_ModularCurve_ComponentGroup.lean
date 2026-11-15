import Tengoku.Seed.LinearAlgebra.Dual.Defs
import Tengoku.Seed.Data.ZMod.QuotientRing
import Tengoku.Seed.Algebra.Exact
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset

section CharacterLattice
variable {ι : Type*} [Fintype ι]

def degreeOn (ι : Type*) [Fintype ι] : (ι → ℤ) →ₗ[ℤ] ℤ :=
  ∑ x : ι, LinearMap.proj x

/--
@isnad1 id=eq.0h2v.s6.ab8fe11c9723 from=translated src=- shape=62a9ba2c vocab=202bdfa6
-/
@[simp] theorem degreeOn_apply (D : ι → ℤ) : degreeOn ι D = ∑ x : ι, D x := by
  simp [degreeOn]

def characterLattice (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (degreeOn ι)

/--
@isnad1 id=iff.0h2v.s6.98657f8e985f from=translated src=- shape=e7c9b847 vocab=fe15ddc7
-/
theorem mem_characterLattice {D : ι → ℤ} :
    D ∈ characterLattice ι ↔ ∑ x : ι, D x = 0 := by
  simp [characterLattice, LinearMap.mem_ker]

end CharacterLattice

section Pairing
variable {ι : Type*} [Fintype ι]

def widthPairing (e : ι → ℕ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun D D' => ∑ x : ι, (e x : ℤ) * (D x * D' x))
    (fun D₁ D₂ D' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun D D'₁ D'₂ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)

/--
@isnad1 id=eq.0h4v.s9.d9a84ed22295 from=translated src=- shape=53778754 vocab=08e43d0f
-/
@[simp] theorem widthPairing_apply (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = ∑ x : ι, (e x : ℤ) * (D x * D' x) :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.97f63802a11e from=translated src=- shape=12cb909b vocab=6481a894
-/
theorem widthPairing_comm (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = widthPairing e D' D := by
  simp only [widthPairing_apply]
  exact Finset.sum_congr rfl fun x _ => by ring

def gramMap (e : ι → ℕ) :
    characterLattice ι →ₗ[ℤ] Module.Dual ℤ (characterLattice ι) :=
  (widthPairing e).domRestrict₁₂ (characterLattice ι) (characterLattice ι)

/--
@isnad1 id=eq.0h4v.s12.01fe1e4fc874 from=translated src=- shape=e6f3f6d4 vocab=a4df5d83
-/
@[simp] theorem gramMap_apply (e : ι → ℕ) (D D' : characterLattice ι) :
    gramMap e D D' = ∑ x : ι, (e x : ℤ) * (D.1 x * D'.1 x) :=
  rfl

abbrev componentGroup (e : ι → ℕ) :=
  Module.Dual ℤ (characterLattice ι) ⧸ LinearMap.range (gramMap e)

abbrev componentGroupProj (e : ι → ℕ) :
    Module.Dual ℤ (characterLattice ι) →ₗ[ℤ] componentGroup e :=
  (LinearMap.range (gramMap e)).mkQ

end Pairing

end ModularCurve
