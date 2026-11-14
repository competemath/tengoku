/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.ClassfieldtheoryYamaguchi end Tengoku.ClassfieldtheoryYamaguchi open Tengoku.ClassfieldtheoryYamaguchi
set_option autoImplicit false

/-!
# Principal ideles and the idele class group

This file formalizes the diagonal
embedding of `Kˣ` into the idele group and the resulting idele class group.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

namespace Tengoku.ClassfieldtheoryYamaguchi.IdeleGroup

/-- The diagonal embedding of `Kˣ` into the idele group.-/
def principalIdele : Kˣ →* IdeleGroup K :=
  (equivAdeleRingUnits (K := K)).symm.toMonoidHom.comp
    (Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)))

variable {K}

/-- The finite component of a principal idele is the image of the
underlying field element in the corresponding completion.
@isnad1 id=eq.0h3v.s12.377959c7834c from=translated src=- shape=67e18b20 vocab=e291cf36
-/
@[simp]
theorem finiteComponent_principalIdele
    (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((finiteComponent v (principalIdele K x) :
      (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : K) :=
  rfl

/-- The infinite component of a principal idele is the image of the
underlying field element in the corresponding completion.
@isnad1 id=eq.0h3v.s12.a5ae651d41d1 from=translated src=- shape=1c39b0ff vocab=a491451b
-/
@[simp]
theorem infiniteComponent_principalIdele
    (x : Kˣ) (w : InfinitePlace K) :
    ((infiniteComponent w (principalIdele K x) :
      w.Completionˣ) : w.Completion) = (x : K) :=
  rfl

variable (K)

/-- The diagonal map from field units to ideles is injective.
@isnad1 id=injectiv.0h1v.s11.d48baa32b967 from=translated src=- shape=e937283c vocab=9abf096f
-/
theorem principalIdele_injective :
    Function.Injective (principalIdele K) := by
  apply (equivAdeleRingUnits (K := K)).symm.injective.comp
  exact Units.map_injective
    (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K))

/-- The subgroup of principal ideles.-/
def principalSubgroup : Subgroup (IdeleGroup K) :=
  (principalIdele K).range

/-- The multiplicative group `Kˣ`, identified with the subgroup of principal
ideles.-/
def principalEquiv : Kˣ ≃* principalSubgroup K :=
  MonoidHom.ofInjective (principalIdele_injective K)

/--
@isnad1 id=eq.0h2v.s14.52c7513c7fda from=translated src=- shape=100b035c vocab=1b4255fa
-/
@[simp]
theorem coe_principalEquiv (x : Kˣ) :
    (principalEquiv K x : IdeleGroup K) = principalIdele K x :=
  MonoidHom.ofInjective_apply (principalIdele_injective K)

end Tengoku.ClassfieldtheoryYamaguchi.IdeleGroup

/-- The idele class group `C_K = I_K / Kˣ`.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.IdeleClassGroup :=
  IdeleGroup K ⧸ IdeleGroup.principalSubgroup K
-- Tengoku: root names of this library moved to Tengoku.ClassfieldtheoryYamaguchi so they do not collide with other libraries (generated)
