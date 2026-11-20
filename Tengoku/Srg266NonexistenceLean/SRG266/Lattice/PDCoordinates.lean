/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PDUnimodular
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntegerCoordinates
import Tengoku.Seed.Algebra.Module.LocalizedModule.Int
import Tengoku.Seed.LinearAlgebra.Dimension.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open Module

variable {n : ℕ}

noncomputable def pdFinBasis (L : PDUnimodularLattice n) :
    Basis (Fin n) ℤ L.carrier := by
  let := L.moduleFree
  let := L.moduleFinite
  exact Module.finBasisOfFinrankEq ℤ L.carrier L.rank

noncomputable def pdGram (L : PDUnimodularLattice n) : Matrix (Fin n) (Fin n) ℤ :=
  LinearMap.BilinForm.toMatrix (pdFinBasis L) L.pairing

noncomputable def pdRatForm (L : PDUnimodularLattice n) :
    LinearMap.BilinForm ℚ (Fin n → ℚ) :=
  Matrix.toBilin' fun i j => ((pdGram L i j : ℤ) : ℚ)

noncomputable def pdCoordEquiv (L : PDUnimodularLattice n) :
    (Fin n → ℤ) ≃ₗ[ℤ] L.carrier :=
  (pdFinBasis L).equivFun.symm

/--
@isnad1 id=ex.0h2v.s7.15cc5f4fd797 from=translated src=- shape=2957b1ee vocab=d3c957ae
-/
theorem exists_intCoords_multiple (v : Fin n → ℚ) :
    ∃ d : nonZeroDivisors ℤ, ∃ z : Fin n → ℤ,
      ∀ i, (z i : ℚ) = (d.1 : ℚ) * v i := by
  obtain ⟨d, hd⟩ := IsLocalizedModule.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (Algebra.linearMap ℤ ℚ) v
  refine ⟨d, fun i => (hd i).choose, ?_⟩
  intro i
  exact (hd i).choose_spec

end SRG266.Lattice
