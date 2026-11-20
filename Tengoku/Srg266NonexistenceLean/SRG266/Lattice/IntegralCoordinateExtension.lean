/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.Algebra.Module.Rat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped Matrix BigOperators

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
variable [AddCommGroup X] [Module ℚ X]

noncomputable def rationalCoordinateExtension (φ : (ι → ℤ) →ₗ[ℤ] X) :
    (ι → ℚ) →ₗ[ℚ] X :=
  Fintype.linearCombination ℚ (fun i => φ (Pi.single i 1))

/--
@isnad1 id=eq.0h4v.s7.6839d681e790 from=translated src=- shape=a644370a vocab=92d92e59
-/
theorem rationalCoordinateExtension_intCast (φ : (ι → ℤ) →ₗ[ℤ] X) (z : ι → ℤ) :
    rationalCoordinateExtension φ (fun i => (z i : ℚ)) = φ z := by
  have hz : (∑ i, (z i) • (Pi.single i 1 : ι → ℤ)) = z := by
    ext j
    simp [Pi.single_apply, mul_ite]
  calc
    _ = ∑ i, (z i) • φ (Pi.single i 1) := by
      simp only [rationalCoordinateExtension, Fintype.linearCombination_apply,
        Int.cast_smul_eq_zsmul]
    _ = φ (∑ i, (z i) • (Pi.single i 1 : ι → ℤ)) := by
      simp only [map_sum, map_zsmul]
    _ = φ z := congrArg φ hz

/--
@isnad1 id=surjecti.2h4v.s8.db7fc06ee072 from=translated src=- shape=d39591c5 vocab=a348fd2a
-/
theorem rationalCoordinateExtension_surjective
    (φ : (ι → ℤ) →ₗ[ℤ] X) (R : Set X)
    (hspan : Submodule.span ℚ R = ⊤) (hcover : ∀ r ∈ R, ∃ z, φ z = r) :
    Function.Surjective (rationalCoordinateExtension φ) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro r hr
  obtain ⟨z, hz⟩ := hcover r hr
  exact ⟨fun i => (z i : ℚ), (rationalCoordinateExtension_intCast φ z).trans hz⟩

/--
@isnad1 id=ex.3h4v.s9.446ae6ed7969 from=translated src=- shape=e263b350 vocab=67eed870
-/
theorem exists_rationalCoordinateEquiv
    (φ : (ι → ℤ) →ₗ[ℤ] X) (R : Set X)
    (hspan : Submodule.span ℚ R = ⊤) (hcover : ∀ r ∈ R, ∃ z, φ z = r)
    (hrank : Module.finrank ℚ X = Fintype.card ι) :
    ∃ e : (ι → ℚ) ≃ₗ[ℚ] X,
      (∀ z : ι → ℤ, e (fun i => (z i : ℚ)) = φ z) ∧
      e.toLinearMap = rationalCoordinateExtension φ := by
  have hsurj := rationalCoordinateExtension_surjective φ R hspan hcover
  let : Module.Finite ℚ X := Module.Finite.of_surjective _ hsurj
  have hdim : Module.finrank ℚ (ι → ℚ) = Module.finrank ℚ X := by
    simpa using hrank.symm
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  let e := LinearEquiv.ofBijective (rationalCoordinateExtension φ) ⟨hinj, hsurj⟩
  exact ⟨e, rationalCoordinateExtension_intCast φ, rfl⟩

end SRG266.Lattice
