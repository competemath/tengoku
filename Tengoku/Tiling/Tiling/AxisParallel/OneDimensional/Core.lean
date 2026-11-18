import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic
import Tengoku.Seed.Topology.Sets.VietorisTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/jaumededios/Tiling@00f80c7de5ac, `Tiling/AxisParallel/OneDimensional/Core.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/


open Function MeasureTheory Set
open scoped Pointwise

namespace Tiling.AxisParallel.OneDimensional

/-- A countable measure tiling by translates of `B` on the measurable target `X`.-/
def LineTilesOn (B L X : Set ℝ) : Prop :=
  MeasurableSet B ∧ MeasurableSet X ∧ L.Countable ∧
    Set.Pairwise L
      (MeasureTheory.AEDisjoint MeasureTheory.volume on
        ((· +ᵥ B) : ℝ → Set ℝ)) ∧
    ∀ᵐ x ∂MeasureTheory.volume,
      (x ∈ X ↔ ∃ l : L, x ∈ ((l : ℝ) +ᵥ B))

/-- A measure tiling of the whole real line by translates of `B`.-/
def LineTiles (B L : Set ℝ) : Prop :=
  LineTilesOn B L Set.univ

/-- A literal finite union of bounded nondegenerate open intervals.-/
def IsFiniteIntervalRegion (B : Set ℝ) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → ℝ),
    (∀ i, a i < b i) ∧ B = ⋃ i, Set.Ioo (a i) (b i)

/-- Translate a chosen centre of a line tiling to the origin.-/
def normalizeLineTiling (L : Set ℝ) (l0 : ℝ) : Set ℝ :=
  (-l0) +ᵥ L

/-- A line tiling with a distinguished centre normalized to zero.-/
structure NormalizedLineTiling (B : Set ℝ) where
  centres : Set ℝ
  tiles : LineTiles B centres
  zero_mem : 0 ∈ centres

end Tiling.AxisParallel.OneDimensional
