/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Algebra.IntermediateFieldAlgEquivOrderIso
import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Algebra.AbelianGaloisEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Finite abelian intermediate fields under an ambient algebra equivalence

An algebra equivalence of ambient fields transports finite-dimensionality and
the abelian Galois property of every intermediate field.
-/

noncomputable section

namespace ClassFieldTheory

universe u v w

variable {F : Type u} {L : Type v} {L' : Type w}
  [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
  (e : L ≃ₐ[F] L') (E : IntermediateField F L)

/-- The equivalence of intermediate fields commutes with their base-field
embeddings.
@isnad1 id=eq.0h5v.s11.5420631d84c0 from=translated src=- shape=e0b67aa0 vocab=7b84f031
-/
theorem intermediateFieldMap_commutes :
    (algebraMap F (E.map e.toAlgHom)).comp (RingEquiv.refl F).toRingHom =
      (IntermediateField.intermediateFieldMap e E).toRingHom.comp
        (algebraMap F E) := by
  ext x
  simp

/-- Mapping an intermediate field through an ambient algebra equivalence
preserves its finite-dimensionality.
@isnad1 id=finitedi.0h5v.s9.ebb8a162548d from=translated src=- shape=01dd0c92 vocab=f0daf615
-/
theorem finiteDimensional_intermediateField_map_algEquiv
    [FiniteDimensional F E] :
    FiniteDimensional F (E.map e.toAlgHom) := by
  exact Module.Finite.of_equiv_equiv
    (RingEquiv.refl F) (IntermediateField.intermediateFieldMap e E).toRingEquiv
    (intermediateFieldMap_commutes e E)

/-- Mapping an intermediate field through an ambient algebra equivalence
preserves its abelian Galois property.
@isnad1 id=isabelia.0h5v.s8.be90a301eee2 from=translated src=- shape=01dd0c92 vocab=20ebfd36
-/
theorem isAbelianGalois_intermediateField_map_algEquiv
    [IsAbelianGalois F E] :
    IsAbelianGalois F (E.map e.toAlgHom) := by
  exact isAbelianGalois_of_equiv_equiv
    (RingEquiv.refl F) (IntermediateField.intermediateFieldMap e E).toRingEquiv
    (intermediateFieldMap_commutes e E)

end ClassFieldTheory
