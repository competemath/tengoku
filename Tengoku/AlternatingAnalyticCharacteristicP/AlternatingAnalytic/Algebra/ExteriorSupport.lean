import Tengoku.Seed.LinearAlgebra.ExteriorPower.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exterior antisymmetrization

Exterior basis coordinates factor through antisymmetrization into the tensor power,
so antisymmetrization is injective over every field.
-/

namespace AlternatingAnalytic

/-- Antisymmetrization into the tensor power is injective over any field, even when
`k! = 0`.
@isnad1 id=injectiv.0h3v.s12.300cb0771759 from=translated src=- shape=1d728cd4 vocab=e519a109
-/
theorem toTensorPower_injective
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (k : ℕ) :
    Function.Injective (exteriorPower.toTensorPower L V k) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex L V) := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis L V
  intro x y h
  apply (b.exteriorPower k).ext_elem
  intro s
  simp only [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual,
    exteriorPower.ιMulti_family, exteriorPower.pairingDual,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact congrArg (TensorPower.multilinearMapToDual L V k
    (b.coord ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) h

end AlternatingAnalytic
