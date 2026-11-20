/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11E6ShortEnergy
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11D7E6E6Transport
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ShortFrameLabelNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

def orientedBinaryCoordinates {ι : Type*} (ε : ℤ) (z : ι → ℤ) : ι → ℤ :=
  if ε = 1 then z else fun i => 1-z i

/--
@isnad1 id=and.3h3v.s8.d8e80a59a333 from=translated src=- shape=608cbe60 vocab=4e268ae4
-/
theorem a11_centered_orientation (ε a : ℤ) (z : Fin 12 → ℤ)
    (hε : ε = -1 ∨ ε = 1) (hz : (∑ i, z i) = a) (hbinary : ∀ i, z i = 0 ∨ z i = 1) :
    (∑ i, orientedBinaryCoordinates ε z i) = orientedALabel ε a ∧
      (∀ i, (ε : ℚ)*((z i : ℚ)-(a : ℚ)/12) =
        (orientedBinaryCoordinates ε z i : ℚ)-(orientedALabel ε a : ℚ)/12) ∧
      (∀ i, orientedBinaryCoordinates ε z i = 0 ∨ orientedBinaryCoordinates ε z i = 1) := by
  rcases hε with rfl | rfl
  · simp only [orientedBinaryCoordinates, orientedALabel, show (-1 : ℤ) ≠ 1 by omega, ite_false]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.sum_sub_distrib, hz]
      simp
    · intro i
      push_cast
      ring
    · intro i
      rcases hbinary i with h | h <;> simp [h]
  · simpa [orientedBinaryCoordinates, orientedALabel] using
      (show (∑ i, z i) = a ∧ (∀ i : Fin 12, True) ∧ (∀ i, z i = 0 ∨ z i = 1) from
        ⟨hz, fun _ => trivial, hbinary⟩)

def A11E6NormalizedType (a δ : ℤ) (u : Fin 11 → ℚ) (v : Fin 6 → ℚ) : Prop :=
  (a = 9 ∧ cartanARatForm 11 u u = 9/4 ∧ v = 0) ∨
  (a = 1 ∧ cartanARatForm 11 u u = 11/12 ∧ E6Cartan.form v v = 4/3 ∧
    ∃ w ∈ coordinateIntegerLattice 6, v = w+δ • E6Cartan.weight)

/--
@isnad1 id=a11e6nor.6h6v.s10.303b22a1d4b6 from=translated src=- shape=71b2c822 vocab=7526e0fd
-/
theorem a11E6_normalized_type {ε δ a c : ℤ} {u : Fin 11 → ℚ} {v : Fin 6 → ℚ}
    (hδ : δ = -1 ∨ δ = 1) (htype : A11E6ShortType a u v) (hlabel : ShortFrameLabel a c)
    (hcoset : ∃ w ∈ coordinateIntegerLattice 6, v = w+c • E6Cartan.weight)
    (hcompat : (orientedALabel ε a = 9 ∧ c = 0) ∨ (orientedALabel ε a = 1 ∧ c = δ))
    (hzero : E6Cartan.form v v = 0 → v = 0) :
    A11E6NormalizedType (orientedALabel ε a) δ u v := by
  rcases htype with ⟨ha, hAn, hEn⟩ | ⟨ha, hAn, hEn, _⟩
  · have hc : c = 0 := by
      rcases hlabel with h | h
      · exact h.2
      · rcases h.1 with h | h <;> omega
    rcases hcompat with h | h
    · exact Or.inl ⟨h.1, hAn, hzero hEn⟩
    · rcases hδ with hδ | hδ <;> omega
  · have hc : c ≠ 0 := by
      rcases hlabel with h | h
      · rcases h.1 with h | h <;> omega
      · rcases h.2 with h | h <;> omega
    rcases hcompat with h | h
    · exact (hc h.2).elim
    · exact Or.inr ⟨h.1, hAn, hEn, by simpa only [h.2] using hcoset⟩

variable {X : Type*} [AddCommGroup X] [Module ℚ X]

end SRG266.Lattice
