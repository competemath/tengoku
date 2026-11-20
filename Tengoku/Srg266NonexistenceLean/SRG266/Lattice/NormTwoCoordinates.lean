/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRationalCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntegerCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

theorem normTwo_integer_coordinates
    {X : Type*} [AddCommGroup X] [Module ℚ X]
    (F : LinearMap.BilinForm ℚ X) (L : Submodule ℤ X)
    {n m : ℕ} (N : PDUnimodularLattice n) [Finite (NormTwoRoot N)]
    (e : L ≃ₗ[ℤ] N.carrier)
    (hpairN : ∀ u v : L, ((N.pairing (e u) (e v) : ℤ) : ℚ) = F u v)
    {f : N.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot N, f r.1 ≠ 0)
    (coord : Fin m ≃ simpleRootSet f) (ψ : (Fin m → ℚ) ≃ₗ[ℚ] X)
    (hψ : ∀ z : Fin m → ℤ, ψ (fun i => (z i : ℚ)) =
      (e.symm (coordinateRootMap coord z) : X))
    {r : X} (hr : r ∈ L) (hnorm : F r r = 2) :
    ψ.symm r ∈ coordinateIntegerLattice m := by
  have hnN : N.pairing (e ⟨r, hr⟩) (e ⟨r, hr⟩) = 2 := by
    have h := (hpairN ⟨r, hr⟩ ⟨r, hr⟩).trans hnorm
    exact_mod_cast h
  obtain ⟨z, hz⟩ := coordinateRootMap_covers_normTwoRoots hf coord ⟨e ⟨r, hr⟩, hnN⟩
  refine ⟨z, ?_⟩
  apply ψ.injective
  rw [LinearEquiv.apply_symm_apply]
  change ψ (fun i => (z i : ℚ)) = r
  rw [hψ, hz, LinearEquiv.symm_apply_apply]

end SRG266.Lattice
