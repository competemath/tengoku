import Tengoku.Erdos64.Erdos64.PentagramEarHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

/-- The exact short-path evidence needed for a connector between two
prescribed pentagram `b` vertices. Despite this module's historical name,
it contains witness conversions, with no minimum-degree or
minimal-counterexample hypothesis and no theorem deriving this evidence
from such hypotheses. Endpoint selection, short length, and hull avoidance
are supplied here.-/
structure ShortConnectorWitness (H : PentagramEarHull G) (i₀ j₀ : Fin 5) where
  path : G.Walk (bVertex H i₀) (bVertex H j₀)
  isPath : path.IsPath
  length_one_to_three : path.length = 1 ∨ path.length = 2 ∨ path.length = 3
  interior_disjoint : ∀ v, v ∈ path.support.tail.dropLast → v ∉ hull H

/-- Explicit short-path evidence yields the existing `Connector` record.-/
def connector_of_shortConnectorWitness
    (H : PentagramEarHull G) {i₀ j₀ : Fin 5} (hij : i₀ ≠ j₀)
    (h : ShortConnectorWitness H i₀ j₀) : Connector H i₀ j₀ := by
  exact
    { distinct := hij
      path := h.path
      isPath := h.isPath
      length_one_to_three := h.length_one_to_three
      interior_disjoint := h.interior_disjoint }

/-- Every existing connector supplies the corresponding short-path evidence.-/
def shortConnectorWitness_of_connector
    (H : PentagramEarHull G) {i₀ j₀ : Fin 5}
    (K : Connector H i₀ j₀) : ShortConnectorWitness H i₀ j₀ :=
  { path := K.path
    isPath := K.isPath
    length_one_to_three := K.length_one_to_three
    interior_disjoint := K.interior_disjoint }

/-- Equivalence of two presentations of supplied connector evidence: a
`Connector`, or a `ShortConnectorWitness` with distinct prescribed endpoints.
This equivalence does not establish either side from ambient graph conditions.
@isnad1 id=iff.0h5v.s5.7566efccf21b from=translated src=- shape=78883617 vocab=62a65c46
-/
theorem exists_connector_iff_shortConnectorWitness
  (H : PentagramEarHull G) {i₀ j₀ : Fin 5} :
    (∃ K : Connector H i₀ j₀, True) ↔
      i₀ ≠ j₀ ∧ Nonempty (ShortConnectorWitness H i₀ j₀) := by
  constructor
  · rintro ⟨K, -⟩
    exact ⟨K.distinct, ⟨shortConnectorWitness_of_connector H K⟩⟩
  · rintro ⟨hij, ⟨h⟩⟩
    exact ⟨connector_of_shortConnectorWitness H hij h, trivial⟩

end PentagramEarHull
end Erdos64
