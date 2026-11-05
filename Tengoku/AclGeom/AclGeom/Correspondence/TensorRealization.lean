/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Closure.Ambient
import Tengoku.AclGeom.AclGeom.Correspondence.TensorComponent
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Realization of prime function-field tensor components

Every prime component of a tensor product of finite field extensions is
realized by two embeddings into an algebraically closed ambient extension.
For actual branches, these embeddings give a represented composite of the
original germs with the selected tensor kernel. The generic
`exists_productMap_ker_of_isPrime` is also consumed by `LocusJointComponent`
to realize every middle-dominating incidence component for finite outer
tuples with the two source algebraicity clauses in an algebraically closed
ambient field. The existing scalar public statements are unchanged.
-/

namespace AclGeom

open IntermediateField
open scoped TensorProduct

/-- Every prime tensor component of two finite extensions embeds in an
algebraically closed ambient extension of the base: there are embeddings of the two factors over
the base whose multiplication map has exactly the given prime as kernel.-/
theorem exists_productMap_ker_of_isPrime
    {E F G Ω : Type*} [Field E] [Field F] [Field G] [Field Ω]
    [Algebra E F] [Algebra E G] [Algebra E Ω] [IsAlgClosed Ω]
    [FiniteDimensional E F] [FiniteDimensional E G]
    (I : Ideal (F ⊗[E] G)) [I.IsPrime] :
    ∃ (f : F →ₐ[E] Ω) (g : G →ₐ[E] Ω),
      RingHom.ker (Algebra.TensorProduct.productMap f g) = I := by
  let : IsArtinianRing (F ⊗[E] G) := IsArtinianRing.of_finite E _
  let : Field ((F ⊗[E] G) ⧸ I) := Ideal.Quotient.field I
  let e : ((F ⊗[E] G) ⧸ I) →ₐ[E] Ω := IsAlgClosed.lift
  let φ := e.comp (Ideal.Quotient.mkₐ E I)
  refine ⟨φ.comp Algebra.TensorProduct.includeLeft,
    φ.comp Algebra.TensorProduct.includeRight, ?_⟩
  have hφ : Algebra.TensorProduct.productMap
      (φ.comp Algebra.TensorProduct.includeLeft)
      (φ.comp Algebra.TensorProduct.includeRight) = φ := by
    ext <;> simp [← Algebra.TensorProduct.one_def]
  rw [hφ]
  change RingHom.ker (e.toRingHom.comp (Ideal.Quotient.mk I)) = I
  rw [RingHom.ker_comp_of_injective _ e.injective, Ideal.mk_ker]

end AclGeom
