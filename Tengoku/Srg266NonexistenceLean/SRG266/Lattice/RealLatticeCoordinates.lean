/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PDCoordinates
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.LinearAlgebra.Dual.Basis
import Tengoku.Seed.LinearAlgebra.Matrix.ToLinearEquiv
import Tengoku.Seed.Topology.Algebra.Order.Archimedean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace SRG266.Lattice

open scoped Matrix MatrixOrder

variable {n : ℕ}

noncomputable def pdPairingEquiv (L : PDUnimodularLattice n) :
    L.carrier ≃ₗ[ℤ] Module.Dual ℤ L.carrier :=
  LinearEquiv.ofBijective L.pairing L.unimodular

/--
@isnad1 id=eq.0h2v.s11.5e2ece9cfd1a from=translated src=- shape=8821f3ab vocab=fb751873
-/
theorem pdPairing_toMatrix (L : PDUnimodularLattice n) :
    LinearMap.toMatrix (pdFinBasis L) (pdFinBasis L).dualBasis
        L.pairing =
      pdGram L := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr,
    pdGram, LinearMap.BilinForm.toMatrix_apply]
  exact L.symmetric.eq (pdFinBasis L j) (pdFinBasis L i)

/--
@isnad1 id=isunit.0h2v.s4.7ce8e03b56f1 from=translated src=- shape=6b83b589 vocab=41975e4b
-/
theorem pdGram_det_isUnit (L : PDUnimodularLattice n) :
    IsUnit (pdGram L).det := by
  have he := (pdPairingEquiv L).isUnit_det
    (pdFinBasis L) (pdFinBasis L).dualBasis
  change IsUnit (LinearMap.toMatrix (pdFinBasis L)
    (pdFinBasis L).dualBasis L.pairing).det at he
  rw [pdPairing_toMatrix] at he
  exact he

noncomputable def pdGramCoordEquiv (L : PDUnimodularLattice n) :
    (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (pdFinBasis L).equivFun.symm |>.trans <|
    (pdPairingEquiv L |>.trans (pdFinBasis L).dualBasis.equivFun)

/--
@isnad1 id=eq.0h3v.s8.be24d2b03cc0 from=translated src=- shape=472814d3 vocab=0336484e
-/
theorem pdGramCoordEquiv_apply (L : PDUnimodularLattice n)
    (x : Fin n → ℤ) :
    pdGramCoordEquiv L x = Matrix.mulVec (pdGram L) x := by
  have h := LinearMap.toMatrix_mulVec_repr (pdFinBasis L)
    (pdFinBasis L).dualBasis L.pairing ((pdFinBasis L).equivFun.symm x)
  rw [pdPairing_toMatrix] at h
  have hx :
      ⇑((pdFinBasis L).repr ((pdFinBasis L).equivFun.symm x)) = x := by
    simpa only [Module.Basis.equivFun_apply] using
      (pdFinBasis L).equivFun.apply_symm_apply x
  rw [hx] at h
  simpa [pdGramCoordEquiv, pdPairingEquiv] using h.symm

/--
@isnad1 id=eq.0h3v.s8.b77b35ce3bc9 from=translated src=- shape=fc542711 vocab=e8664a9e
-/
theorem pdGram_mulVec_equiv_symm (L : PDUnimodularLattice n)
    (x : Fin n → ℤ) :
    Matrix.mulVec (pdGram L) ((pdGramCoordEquiv L).symm x) = x := by
  rw [← pdGramCoordEquiv_apply]
  exact (pdGramCoordEquiv L).apply_symm_apply x

noncomputable def pdRealGram (L : PDUnimodularLattice n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (pdGram L).map (Int.castRingHom ℝ)

/--
@isnad1 id=eq.0h4v.s4.719e931cb189 from=translated src=- shape=30991030 vocab=fbe1392b
-/
@[simp]
theorem pdRealGram_apply (L : PDUnimodularLattice n) (i j : Fin n) :
    pdRealGram L i j = (pdGram L i j : ℝ) := rfl

/--
@isnad1 id=ne.0h2v.s4.934a819c5d3f from=translated src=- shape=07b30d77 vocab=ac593ca7
-/
theorem pdRealGram_det_ne_zero (L : PDUnimodularLattice n) :
    (pdRealGram L).det ≠ 0 := by
  change ((pdGram L).map (fun x : ℤ => (x : ℝ))).det ≠ 0
  rw [← Int.cast_det]
  exact_mod_cast (pdGram_det_isUnit L).ne_zero

/--
@isnad1 id=isunit.0h2v.s4.0cc19bd765be from=translated src=- shape=cdaaa425 vocab=09570e1d
-/
theorem pdRealGram_isUnit (L : PDUnimodularLattice n) :
    IsUnit (pdRealGram L) :=
  (Matrix.isUnit_iff_isUnit_det (pdRealGram L)).mpr
    (isUnit_iff_ne_zero.mpr (pdRealGram_det_ne_zero L))

/--
@isnad1 id=ishermit.0h2v.s5.067c2ba7aad7 from=translated src=- shape=e1abeb28 vocab=8aec6241
-/
theorem pdRealGram_isHermitian (L : PDUnimodularLattice n) :
    (pdRealGram L).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [pdRealGram_apply]
  exact congrArg (fun z : ℤ => (z : ℝ)) <| by
    simpa only [pdGram, LinearMap.BilinForm.toMatrix_apply] using
      L.symmetric.eq (pdFinBasis L j) (pdFinBasis L i)

/--
@isnad1 id=denseran.0h1v.s5.9d5cf5e41b4c from=translated src=- shape=1341c88a vocab=6ace4857
-/
theorem denseRange_ratPiCast :
    DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) := by
  let f : (Fin n → ℚ) → (Fin n → ℝ) :=
    Pi.map fun _ : Fin n => ((↑) : ℚ → ℝ)
  have hf : DenseRange f :=
    DenseRange.piMap (fun _ : Fin n => Rat.denseRange_cast)
  have hfun : f = (fun q : Fin n → ℚ => fun i => (q i : ℝ)) := by
    funext q i
    rfl
  rwa [← hfun]

noncomputable def pdSqrtGram (L : PDUnimodularLattice n) :
    Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt (pdRealGram L)

/--
@isnad1 id=issymm.0h2v.s3.74850e396e8b from=translated src=- shape=e1abeb28 vocab=00a3d85d
-/
theorem pdSqrtGram_isSymm (L : PDUnimodularLattice n) :
    (pdSqrtGram L).IsSymm := by
  rw [← Matrix.isHermitian_iff_isSymm]
  exact (CFC.sqrt_nonneg (pdRealGram L)).isSelfAdjoint

/--
@isnad1 id=eq.0h3v.s8.b5c270bbd1aa from=translated src=- shape=c1003d55 vocab=f58242d4
-/
theorem pdRealGram_mulVec_equiv_symm_cast (L : PDUnimodularLattice n)
    (x : Fin n → ℤ) :
    Matrix.mulVec (pdRealGram L)
        (fun i => (((pdGramCoordEquiv L).symm x i : ℤ) : ℝ)) =
      (fun i => (x i : ℝ)) := by
  ext i
  have hi := congrFun (pdGram_mulVec_equiv_symm L x) i
  simp only [Matrix.mulVec, dotProduct, pdRealGram_apply] at *
  exact_mod_cast hi

end SRG266.Lattice
