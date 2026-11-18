import Tengoku.Seed.MeasureTheory.Constructions.Pi
import Tengoku.Seed.MeasureTheory.Group.Measure
import Tengoku.Seed.MeasureTheory.Measure.Count

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/jaumededios/Tiling@00f80c7de5ac, `Tiling/Measure/Counting.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/


/-!
# Canonical counting measures for integer lattices

For this project, `ℤ` carries counting measure as its canonical `volume`.  The canonical measure on
`Fin n → ℤ` is then obtained from Mathlib's finite-product `MeasureSpace` instance.  We prove that
this product measure is equal to counting measure on the product.

Mathlib does not currently install the base `MeasureSpace ℤ` instance globally.  Keeping it and
the associated bridge instances in this small module isolates that project-level choice and the
declarations that may later be proposed for Mathlib.
-/

open MeasureTheory

namespace Tiling

noncomputable section

/-- Counting measure as the canonical measure on `ℤ`.-/
noncomputable instance instMeasureSpaceInt : MeasureSpace ℤ :=
  ⟨Measure.count⟩

/-- A finite product of counting measures is counting measure on the product.
@isnad1 id=eq.0h2v.s6.de0eb0e26d65 from=translated src=- shape=765549a8 vocab=e84eef7d
-/
theorem Measure.pi_count {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    [∀ i, Countable (α i)] :
    Measure.pi (fun i ↦ (Measure.count : Measure (α i))) =
      (Measure.count : Measure (∀ i, α i)) := by
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton]
  simp

/-- The product `volume` on the integer lattice `Fin n → ℤ` is counting measure.
@isnad1 id=eq.0h1v.s6.963cbc5c6d40 from=translated src=- shape=66ec5d80 vocab=67ddb308
-/
theorem volume_piFin_int_eq_count (n : ℕ) :
    (volume : Measure (Fin n → ℤ)) = Measure.count := by
  change Measure.pi (fun _ : Fin n ↦ (Measure.count : Measure ℤ)) = Measure.count
  exact Measure.pi_count

end

end Tiling
