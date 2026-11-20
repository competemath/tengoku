/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootBasis
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEComponentAssembly
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RootADEEmbedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open Function Set

noncomputable def coordinateRootMap
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (coord : Fin m ≃ simpleRootSet f) :
    (Fin m → ℤ) →ₗ[ℤ] L.carrier :=
  Fintype.linearCombination ℤ fun i => normTwoRootVal (coord i).1

theorem coordinateRootMap_injective
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin m ≃ simpleRootSet f) :
    Function.Injective (coordinateRootMap coord) := by
  have hli := simpleRootSet_linearIndepOn f hf
  change LinearIndependent ℤ
    (fun r : simpleRootSet f => normTwoRootVal r.1) at hli
  have hli' : LinearIndependent ℤ
      (fun i : Fin m => normTwoRootVal (coord i).1) :=
    hli.comp coord coord.injective
  intro x y hxy
  change (Fintype.linearCombination ℤ
    (fun i : Fin m => normTwoRootVal (coord i).1)) x =
      (Fintype.linearCombination ℤ
        (fun i : Fin m => normTwoRootVal (coord i).1)) y at hxy
  exact hli'.fintypeLinearCombination_injective hxy

theorem coordinateRootMap_pairing
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin m ≃ simpleRootSet f) (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) = A i j)
    (x y : Fin m → ℤ) :
    L.pairing (coordinateRootMap coord x) (coordinateRootMap coord y) =
      Matrix.toBilin' A x y := by
  classical
  rw [coordinateRootMap, bilinForm_fintypeLinearCombination, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hA i j, graphCartanMatrix_simpleRootGraph f hf]
  rfl

theorem coordinateRootMap_covers_normTwoRoots
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin m ≃ simpleRootSet f) (r : NormTwoRoot L) :
    ∃ x : Fin m → ℤ, coordinateRootMap coord x = r.1 := by
  have hr : r.1 ∈ normTwoRootSpan L :=
    Submodule.subset_span ⟨r, rfl⟩
  rw [← span_simpleRoots_eq_normTwoRootSpan f hf] at hr
  have hrange :
      Set.range (fun i : Fin m => normTwoRootVal (coord i).1) =
        Set.range (fun s : simpleRootSet f => normTwoRootVal s.1) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      exact ⟨coord i, rfl⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨coord.symm s, by simp⟩
  rw [← hrange, Submodule.mem_span_range_iff_exists_fun] at hr
  obtain ⟨x, hx⟩ := hr
  refine ⟨x, ?_⟩
  change (Fintype.linearCombination ℤ
    (fun i : Fin m => normTwoRootVal (coord i).1)) x = r.1
  simpa only [Fintype.linearCombination_apply] using hx

theorem coordinateRootMap_eq_simpleRootCombination
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (coord : Fin m ≃ simpleRootSet f) (z : Fin m → ℤ) :
    coordinateRootMap coord z =
      simpleRootCombination f (fun s => z (coord.symm s)) := by
  classical
  simp only [coordinateRootMap, simpleRootCombination, Fintype.linearCombination_apply]
  convert! Equiv.sum_comp coord
    (fun s : simpleRootSet f => z (coord.symm s) • (s.1.1 : L.carrier)) using 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Equiv.symm_apply_apply, normTwoRootVal]
    exact int_smul_eq_zsmul _ _ _
  · apply Finset.sum_congr rfl
    intro i _
    exact int_smul_eq_zsmul _ _ _

theorem coordinateRootMap_dominant_height
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (coord : Fin m ≃ simpleRootSet f) (h : ℤ)
    (hheight : ∀ (θ : NormTwoRoot L) (z : simpleRootSet f → ℤ),
      simpleRootCombination f z = θ.1 → 0 < f θ.1 →
      (∀ s : simpleRootSet f, 0 ≤ L.pairing s.1.1 θ.1) →
      (∑ s, z s) = h)
    (θ : NormTwoRoot L) (z : Fin m → ℤ)
    (hz : coordinateRootMap coord z = θ.1) (hθ : 0 < f θ.1)
    (hd : ∀ i, 0 ≤ L.pairing (coord i).1.1 θ.1) :
    (∑ i, z i) = h := by
  classical
  have hz' : simpleRootCombination f (fun s => z (coord.symm s)) = θ.1 :=
    (coordinateRootMap_eq_simpleRootCombination coord z).symm.trans hz
  have hd' (s : simpleRootSet f) : 0 ≤ L.pairing s.1.1 θ.1 := by
    simpa using hd (coord.symm s)
  have hh := hheight θ (fun s => z (coord.symm s)) hz' hθ hd'
  have he := Equiv.sum_comp coord (fun s => z (coord.symm s))
  simpa using he.trans hh

end Lattice
end SRG266
