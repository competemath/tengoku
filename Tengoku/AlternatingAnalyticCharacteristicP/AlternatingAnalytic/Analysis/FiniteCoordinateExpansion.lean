import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
import Tengoku.Seed.LinearAlgebra.ExteriorPower.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exterior-basis expansion

For a finite basis `e` with coordinates `ε`, an alternating map satisfies
`m y = ∑_s det (ε_{s_a} (y_b)) • m (e_{s_1}, …, e_{s_k})`, summed over increasing
tuples `s`. This is the diagonal identity in the proof of Proposition 4.1. The
coordinate index is the row index of the determinant, as in the paper.
-/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators
open Module

/-- The exterior-basis expansion of an alternating map, over any commutative ring.
@isnad1 id=eq.0h8v.s10.0d37f89555a2 from=translated src=- shape=500f2175 vocab=c12bb723
-/
theorem finiteCoordinate_expansion_algebraic
    {K H G : Type*} [CommRing K] [AddCommGroup H] [Module K H]
    [AddCommGroup G] [Module K G] {d : ℕ}
    (b : Basis (Fin d) K H) (k : ℕ) (m : H [⋀^Fin k]→ₗ[K] G)
    (y : Fin k → H) :
    (∑ s : Set.powersetCard (Fin d) k,
      (Matrix.of fun a j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s a)
        (y j)).det • m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a))) = m y := by
  classical
  let L := exteriorPower.alternatingMapLinearEquiv m
  have h := congrArg L ((b.exteriorPower k).sum_repr (exteriorPower.ιMulti K k y))
  rw [map_sum] at h
  simp only [map_smul] at h
  calc
    _ = ∑ s : Set.powersetCard (Fin d) k,
        (b.exteriorPower k).repr (exteriorPower.ιMulti K k y) s •
          L ((b.exteriorPower k) s) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
        exteriorPower.basis_apply]
      simp only [L, exteriorPower.ιMulti_family,
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      congr 1
      exact (Matrix.det_transpose _).symm
    _ = L (exteriorPower.ιMulti K k y) := h
    _ = m y := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti m y

/-- The exterior-basis expansion of a continuous alternating map. The coordinates
need not be continuous.
@isnad1 id=eq.0h8v.s10.968156a2db7c from=translated src=- shape=500f2175 vocab=6b7c0947
-/
theorem finiteCoordinate_expansion
    {K H F : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup H] [NormedSpace K H]
    [NormedAddCommGroup F] [NormedSpace K F] {d : ℕ}
    (b : Basis (Fin d) K H) (k : ℕ) (m : H [⋀^Fin k]→L[K] F)
    (y : Fin k → H) :
    (∑ s : Set.powersetCard (Fin d) k,
      (Matrix.of fun a j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s a)
        (y j)).det • m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a))) = m y :=
  finiteCoordinate_expansion_algebraic b k m.toAlternatingMap y

end AlternatingAnalytic
