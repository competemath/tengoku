/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.GroupConfig.Rref
import Tengoku.Seed.LinearAlgebra.TensorProduct.Pi
import Tengoku.Seed.RingTheory.Flat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Literal scalar extension of a field-defined subspace

Supplemental `def:subspace-defined`: the `F`-valued part is the actual subspace
`W ∩ F^𝓜`. Its tensor product with the ambient field maps canonically into the
coordinate space. The image is exactly the span used by `DefinedOver`, so
field-definedness is equivalent to that image being `W`. Flatness and Mathlib's
finite-product tensor equivalence give injectivity for finite coordinates.

**Status:** the literal tensor form is proved, with an actual linear equivalence
and its pure-tensor formula. Range and span statements allow arbitrary coordinate
types; the equivalence requires finite coordinates. No basis or isomorphism
certificate, order, algebraic closedness or universal domain is assumed.
-/

namespace GroupConfig

open scoped TensorProduct

noncomputable section

variable {R : Type*} [Field R] {𝓜 : Type*} (W : Submodule R (𝓜 → R)) (F : Subfield R)

/-- The `F`-subspace `W ∩ F^𝓜`, with its actual `F`-valued coordinates.-/
def coefficientFieldPart : Submodule F (𝓜 → F) :=
  (W.restrictScalars F).comap (coeVec F)

/-- The canonical scalar-extension map from `R ⊗[F] (W ∩ F^𝓜)` into the ambient space.-/
def coefficientExtension : R ⊗[F] ↥(coefficientFieldPart W F) →ₗ[R] (𝓜 → R) :=
  (TensorProduct.piScalarRightHom F R R 𝓜).comp
    ((coefficientFieldPart W F).subtype.baseChange R)

/--
@isnad1 id=eq.0h6v.s15.96c331fda722 from=translated src=- shape=c167a7ca vocab=f4cc057e
-/
@[simp]
theorem coefficientExtension_tmul (r : R) (u : coefficientFieldPart W F) :
    coefficientExtension W F (r ⊗ₜ[F] u) = r • coeVec F (u : 𝓜 → F) := by
  ext j
  simp only [coefficientExtension, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    TensorProduct.piScalarRightHom_tmul, Pi.smul_apply, coeVec_apply]
  change (u.1 j : R) * r = r * (u.1 j : R)
  exact mul_comm _ _

/-- The literal tensor extension embeds in the ambient coordinate space.
@isnad1 id=injectiv.0h4v.s14.5314a61ea78f from=translated src=- shape=00fd3cb2 vocab=dc78d419
-/
theorem coefficientExtension_injective [Finite 𝓜] :
    Function.Injective (coefficientExtension W F) := by
  classical
  let _ := Fintype.ofFinite 𝓜
  exact (TensorProduct.piScalarRight F R R 𝓜).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap
      (coefficientFieldPart W F).subtype (Submodule.injective_subtype _))

end

end GroupConfig
