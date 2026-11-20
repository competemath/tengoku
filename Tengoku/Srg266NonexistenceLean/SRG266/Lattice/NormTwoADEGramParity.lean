/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IsolatedDGramParity
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoADEDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped Matrix BigOperators Classical

/--
@isnad1 id=not.6h14v.s13.f62ff37bb924 from=translated src=- shape=48f3afc6 vocab=cf7ad927
-/
theorem not_all_E6_of_integral_root_projection
    {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
    {n d : ℕ} (i j : Fin n) (hij : i ≠ j)
    (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U)
    (L : Submodule ℤ ((W × (Fin n → ℚ)) × U))
    (hD : ∀ a, (((0 : W), a), (0 : U)) ∈ L ↔ a ∈ evenCoordinateLattice n)
    (hproj : ∀ r ∈ L, prodForm (prodForm B (standardRatForm n)) C r r = 2 →
      r.1.2 ∈ coordinateIntegerLattice n)
    (N : PDUnimodularLattice d) [Finite (NormTwoRoot N)]
    (e : L ≃ₗ[ℤ] N.carrier)
    (hpairN : ∀ u v : L, ((N.pairing (e u) (e v) : ℤ) : ℚ) =
      prodForm (prodForm B (standardRatForm n)) C u v)
    {f : N.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot N, f r.1 ≠ 0)
    {ts : List ADEType} (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ a b, graphCartanMatrix (simpleRootGraph f) (coord a) (coord b) =
      (adeGram ts).2 a b) :
    ¬(∀ t ∈ ts, t = .E6) := by
  intro hall
  let F := prodForm (prodForm B (standardRatForm n)) C
  let φ : (Fin (ADEType.rankSum ts) → ℤ) →ₗ[ℤ] ((W × (Fin n → ℚ)) × U) :=
    L.subtype.comp (e.symm.toLinearMap.comp (coordinateRootMap coord))
  have hmem (z) : φ z ∈ L := (e.symm (coordinateRootMap coord z)).2
  have hdiag (a) : (adeGram ts).2 a a = 2 :=
    (hgram a a).symm.trans (graphCartanMatrix_apply_same _ _)
  have hpair (z w) : F (φ z) (φ w) = (Matrix.toBilin' (adeGram ts).2 z w : ℚ) := by
    have h := hpairN (e.symm (coordinateRootMap coord z)) (e.symm (coordinateRootMap coord w))
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans (congrArg (fun a : ℤ => (a : ℚ))
      (coordinateRootMap_pairing hf coord (adeGram ts).2 hgram z w))
  have hcover (r) (hr : r ∈ L) (hn : F r r = 2) : ∃ z, φ z = r := by
    have hnN : N.pairing (e ⟨r, hr⟩) (e ⟨r, hr⟩) = 2 := by
      have h := (hpairN ⟨r, hr⟩ ⟨r, hr⟩).trans hn
      exact_mod_cast h
    obtain ⟨z, hz⟩ := coordinateRootMap_covers_normTwoRoots hf coord ⟨e ⟨r, hr⟩, hnN⟩
    refine ⟨z, ?_⟩
    change (e.symm (coordinateRootMap coord z)).1 = r
    rw [hz, LinearEquiv.symm_apply_apply]
  exact not_two_gramDivisibility_of_integral_root_projection i j hij B C L hD hproj
    (adeGram ts).2 hdiag φ hmem hpair hcover (adeGram_two_divisibility_of_all_E6 ts hall)

end SRG266.Lattice
