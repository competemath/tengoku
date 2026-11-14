import Tengoku.TdaLib.TDA.Simplicial.Bridge
import Tengoku.Seed.Data.Finset.Sort
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordered simplicial boundary on faces

Faces are oriented by the fixed ambient linear order. Deleting an enumerated vertex
produces a face, and the signed deletion sum extends linearly to chains.
-/

universe u v

open scoped BigOperators

namespace TDA.Simplicial

variable {V : Type u} [LinearOrder V]
variable (K : PreAbstractSimplicialComplex V)

/-- Delete the vertex at position `i` from a face.-/
def deletedFace (n : ℕ) (s : Face K (n + 1)) (i : Fin (n + 2)) : Face K n := by
  have hv : s.1.orderEmbOfFin s.2.2 i ∈ s.1 :=
    Finset.orderEmbOfFin_mem s.1 s.2.2 i
  have hcard : (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).card = n + 1 := by
    rw [Finset.card_erase_of_mem hv, s.2.2]
    omega
  have hnonempty : (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; omega)
  have hmem : s.1.erase (s.1.orderEmbOfFin s.2.2 i) ∈ K :=
    (K.isRelLowerSet_faces s.2.1).2 (Finset.erase_subset _ _) hnonempty
  exact ⟨s.1.erase (s.1.orderEmbOfFin s.2.2 i), hmem, hcard⟩

/-- The increasing enumeration of the erased face is the original enumeration with
the deleted position skipped.
@isnad1 id=eq.1h6v.s10.e497692762d8 from=translated src=- shape=dad89524 vocab=c7da0c6b
-/
theorem enumerationAfterDeletion (n : ℕ) (s : Face K (n + 1)) (i : Fin (n + 2))
    (hc : (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).card = n + 1)
    (j : Fin (n + 1)) :
    (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).orderEmbOfFin hc j =
      s.1.orderEmbOfFin s.2.2 (i.succAbove j) := by
  let t := s.1.erase (s.1.orderEmbOfFin s.2.2 i)
  have hmem : ∀ j : Fin (n + 1),
      s.1.orderEmbOfFin s.2.2 (i.succAbove j) ∈ t := by
    intro j
    refine Finset.mem_erase.mpr ⟨?_, Finset.orderEmbOfFin_mem s.1 s.2.2 (i.succAbove j)⟩
    intro heq
    apply Fin.succAbove_ne i j
    exact (s.1.orderEmbOfFin s.2.2).injective heq
  have hmono : StrictMono (fun j : Fin (n + 1) =>
      s.1.orderEmbOfFin s.2.2 (i.succAbove j)) :=
    (s.1.orderEmbOfFin s.2.2).strictMono.comp (Fin.strictMono_succAbove i)
  have hunique : (fun j : Fin (n + 1) =>
      s.1.orderEmbOfFin s.2.2 (i.succAbove j)) = t.orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc hmem hmono
  simpa only [t] using (congrFun hunique j).symm

variable (R : Type v) [Ring R]

/-- The signed boundary from degree `n+1` to degree `n`.-/
noncomputable def boundary (n : ℕ) :
    Chain K R (n + 1) →ₗ[R] Chain K R n :=
  Finsupp.linearCombination R (fun s : Face K (n + 1) =>
    ∑ i : Fin (n + 2),
      Finsupp.single (deletedFace K n s i) ((-1 : R) ^ (i : ℕ)))

/-- Boundary on a basis chain is its signed ordered deletion sum.
@isnad1 id=eq.0h6v.s9.3ae27b5044b3 from=translated src=- shape=37d3e7b6 vocab=70cfc96c
-/
theorem boundary_single (n : ℕ) (s : Face K (n + 1)) (a : R) :
    boundary K R n (Finsupp.single s a) =
      a • (∑ i : Fin (n + 2),
        Finsupp.single (deletedFace K n s i) ((-1 : R) ^ (i : ℕ))) := by
  simp [boundary]

private abbrev triangleK : PreAbstractSimplicialComplex (Fin 3) := ⊤

private def triangleVertex (i : Fin 3) : Face triangleK 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 3)).Nonempty; simp, by simp⟩

private def triangleEdge01 : Face triangleK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangleEdge02 : Face triangleK 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangleEdge12 : Face triangleK 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangleFace : Face triangleK 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

end TDA.Simplicial
