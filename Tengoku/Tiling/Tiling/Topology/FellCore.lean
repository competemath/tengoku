import Tengoku.Seed.Topology.Compactification.OnePoint.Basic
import Tengoku.Seed.Topology.Compactification.OnePoint.Sphere
import Tengoku.Seed.Topology.MetricSpace.Closeds
import Tengoku.Seed.Topology.Sets.VietorisTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/jaumededios/Tiling@00f80c7de5ac, `Tiling/Topology/FellCore.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Filter Set
open scoped Topology

noncomputable section

namespace Tiling.Topology

def IsUniformlySeparated {E : Type*} [PseudoMetricSpace E] (δ : ℝ) (S : Set E) :
    Prop := S.Pairwise (fun x y => δ ≤ dist x y)

def fellCompactification
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    (S : Set E) (hS : IsClosed S) :
    TopologicalSpace.NonemptyCompacts (OnePoint E) := by
  let K : Set (OnePoint E) := ((fun x : E => (x : OnePoint E)) '' S) ∪ {OnePoint.infty}
  have hKclosed : IsClosed K := by
    rw [← isOpen_compl_iff]
    have hcompl : Kᶜ = (fun x : E => (x : OnePoint E)) '' Sᶜ := by
      ext z
      refine OnePoint.rec ?_ (fun x => ?_) z
      · simp [K]
      · simp [K]
    rw [hcompl, OnePoint.isOpen_image_coe]
    exact hS.isOpen_compl
  exact ⟨⟨K, hKclosed.isCompact⟩,
    ⟨OnePoint.infty, Set.mem_union_right _ (Set.mem_singleton OnePoint.infty)⟩⟩

def LocallyFellConverges
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    (S : ℕ → Set E) (L : Set E) : Prop :=
  ∃ (hS : ∀ n, IsClosed (S n)) (hL : IsClosed L),
    Tendsto (fun n => fellCompactification (S n) (hS n)) atTop
      (𝓝 (fellCompactification L hL))

end Tiling.Topology
