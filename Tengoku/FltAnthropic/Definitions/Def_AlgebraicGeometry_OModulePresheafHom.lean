import Tengoku

import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Separated

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite Limits

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover

variable (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}

structure Hom (F G : OModulePresheaf π) where

  app : ∀ U : V.Opens, F.obj U →ₗ[R] G.obj U
  app_smul : ∀ (U : V.Opens) (a : Γ(V, U)) (x : F.obj U), app U (a • x) = a • app U x
  naturality : ∀ {U U' : V.Opens} (h : U ≤ U'), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

structure AffHom (F G : OModulePresheaf π) where

  app : ∀ U : V.affineOpens, F.obj U.1 →ₗ[R] G.obj U.1
  app_smul : ∀ (U : V.affineOpens) (a : Γ(V, U.1)) (x : F.obj U.1), app U (a • x) = a • app U x
  naturality : ∀ {U U' : V.affineOpens} (h : U.1 ≤ U'.1), app U ∘ₗ F.res h = G.res h ∘ₗ app U'

namespace Hom

variable {F G H : OModulePresheaf π}

/--
@isnad1 id=eq.1h9v.s9.d22efc9385c4 from=translated src=- shape=97d65d7b vocab=367f9bc6
-/
theorem naturality_apply (φ : Hom F G) {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') :
    φ.app U (F.res h x) = G.res h (φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (φ.naturality h)) x

end Hom

namespace AffHom

variable {F G H : OModulePresheaf π}

/--
@isnad1 id=eq.1h9v.s11.fdc6a890448e from=translated src=- shape=33fa5a20 vocab=021f540f
-/
theorem naturality_apply (φ : AffHom F G) {U U' : V.affineOpens} (h : U.1 ≤ U'.1) (x : F.obj U'.1) :
    φ.app U (F.res h x) = G.res h (φ.app U' x) :=
  congrFun (congrArg DFunLike.coe (φ.naturality h)) x

end AffHom

section Cochains

variable [IsSeparated π] (K : V.OrderedAffineCover) {F G : OModulePresheaf π}

end Cochains

end OModulePresheaf

end AlgebraicGeometry

end
