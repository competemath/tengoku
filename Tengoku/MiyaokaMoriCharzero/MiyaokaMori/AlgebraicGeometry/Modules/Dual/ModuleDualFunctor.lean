import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Contravariance of the existing module dual

Precomposing each compatible local functional with an actual module-sheaf
morphism gives a morphism of the existing dual presheaves. The same identity-ring
sheafification used by `moduleSheafDual` then gives its contravariant functor and
transports module isomorphisms to dual isomorphisms.

Sources: Stacks Project, `modules.tex`, Internal Hom; Mathlib's module-sheaf
morphism naturality and module sheafification functor. Used for the transport of finite free dual
frames and for the canonical/exterior-dual comparison (tangent and dual coefficient blocks in §2 of
the paper).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N P : X.Modules}

set_option backward.isDefEq.respectTransparency false in
/-- Precompose every local functional with the given morphism on the same subopen.-/
def localDualSectionsPrecomp (φ : M ⟶ N) (U : X.Opens) :
    LocalDualSections X N U →ₗ[Γ(X, U)] LocalDualSections X M U where
  toFun α := ⟨fun V ↦ (α.val V).comp (φ.val.app (op V.left)).hom, by
    intro V W i x
    change α.val V (φ.app V.left (M.presheaf.map i.left.op x)) =
      X.presheaf.map i.left.op (α.val W (φ.app W.left x))
    have hφ : φ.app V.left (M.presheaf.map i.left.op x) =
        N.presheaf.map i.left.op (φ.app W.left x) :=
      ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.left.op) x
    exact (congrArg (α.val V) hφ).trans (α.property V W i (φ.app W.left x))⟩
  map_add' α β := by
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro x
    rfl
  map_smul' r α := by
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro x
    rfl

/-- The pulled-back functional evaluates the original functional on the actual image section.
@isnad1 id=eq.0h8v.s18.4e18818d7f14 from=translated src=- shape=3b0a5b23 vocab=bae4e605
-/
@[simp]
theorem localDualSectionsPrecomp_apply (φ : M ⟶ N) (U : X.Opens)
    (α : LocalDualSections X N U) (V : Over U) (x : Γ(M, V.left)) :
    (localDualSectionsPrecomp φ U α).val V x = α.val V (φ.app V.left x) := rfl

/-- Precomposition commutes with the original restriction of compatible functionals.
@isnad1 id=eq.0h8v.s20.d13d965be473 from=translated src=- shape=3d9000b3 vocab=1368cf3b
-/
theorem localDualSectionsPrecomp_restrict (φ : M ⟶ N) {U V : X.Opens}
    (i : V ⟶ U) (α : LocalDualSections X N U) :
    localDualRestrict M i (localDualSectionsPrecomp φ U α) =
      localDualSectionsPrecomp φ V (localDualRestrict N i α) := rfl

/-- Precomposition with the identity fixes every compatible functional.
@isnad1 id=eq.0h3v.s17.0505fed550b0 from=translated src=- shape=019ca2c4 vocab=09c6d3f9
-/
@[simp]
theorem localDualSectionsPrecomp_id (M : X.Modules) (U : X.Opens) :
    localDualSectionsPrecomp (𝟙 M) U = LinearMap.id := by
  apply LinearMap.ext
  intro α
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro x
  rfl

/-- Precomposition reverses the order of composition of module-sheaf morphisms.
@isnad1 id=eq.0h7v.s17.80c0864f1822 from=translated src=- shape=ff367480 vocab=3c72acac
-/
theorem localDualSectionsPrecomp_comp (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) :
    localDualSectionsPrecomp (φ ≫ ψ) U =
      (localDualSectionsPrecomp φ U).comp (localDualSectionsPrecomp ψ U) := by
  apply LinearMap.ext
  intro α
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The local precomposition maps assemble into a morphism of the existing dual presheaves.-/
def moduleDualPresheafPrecomp (φ : M ⟶ N) :
    moduleDualPresheaf N ⟶ moduleDualPresheaf M where
  app U := ModuleCat.ofHom (localDualSectionsPrecomp φ U.unop)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change localDualSectionsPrecomp φ V.unop (localDualRestrict N i.unop α) =
      localDualRestrict M i.unop (localDualSectionsPrecomp φ U.unop α)
    exact (localDualSectionsPrecomp_restrict φ i.unop α).symm

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the presheaf morphism is the original pointwise precomposition.
@isnad1 id=eq.0h8v.s17.b186499abc15 from=translated src=- shape=8cdf2241 vocab=539360a0
-/
@[simp]
theorem moduleDualPresheafPrecomp_apply (φ : M ⟶ N) (U : X.Opens)
    (α : LocalDualSections X N U) (V : Over U) (x : Γ(M, V.left)) :
    ((moduleDualPresheafPrecomp φ).app (op U) α).val V x =
      α.val V (φ.app V.left x) := rfl

/-- The dual-presheaf morphism sends an identity to the identity.
@isnad1 id=eq.0h2v.s9.3eb26dadf237 from=translated src=- shape=fb56dbe2 vocab=9121afc3
-/
@[simp]
theorem moduleDualPresheafPrecomp_id (M : X.Modules) :
    moduleDualPresheafPrecomp (𝟙 M) = 𝟙 (moduleDualPresheaf M) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  exact localDualSectionsPrecomp_id M U.unop

/-- The dual-presheaf morphism reverses the order of composition.
@isnad1 id=eq.0h6v.s9.7f7e0543a1c5 from=translated src=- shape=e971afa3 vocab=de0021c2
-/
theorem moduleDualPresheafPrecomp_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    moduleDualPresheafPrecomp (φ ≫ ψ) =
      moduleDualPresheafPrecomp ψ ≫ moduleDualPresheafPrecomp φ := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  exact localDualSectionsPrecomp_comp φ ψ U.unop

/-- The existing dual presheaf, now contravariantly functorial in the module sheaf.-/
def moduleDualPresheafFunctor (X : Scheme.{u}) : X.Modulesᵒᵖ ⥤ X.PresheafOfModules where
  obj M := moduleDualPresheaf M.unop
  map φ := moduleDualPresheafPrecomp φ.unop
  map_id M := moduleDualPresheafPrecomp_id M.unop
  map_comp φ ψ := moduleDualPresheafPrecomp_comp ψ.unop φ.unop

/-- Sheafification gives a contravariant functor with the original `moduleSheafDual` objects.-/
def moduleSheafDualFunctor (X : Scheme.{u}) : X.Modulesᵒᵖ ⥤ X.Modules :=
  moduleDualPresheafFunctor X ⋙ PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The induced morphism between the same sheafified duals.-/
def moduleSheafDualMap (φ : M ⟶ N) : moduleSheafDual N ⟶ moduleSheafDual M :=
  (moduleSheafDualFunctor X).map φ.op

/-- The dual-sheaf morphism is induced by the actual presheaf precomposition under the unit.
@isnad1 id=eq.0h4v.s16.e6d0c9755913 from=translated src=- shape=5637ecf0 vocab=c82656c9
-/
theorem moduleSheafDualMap_unit (φ : M ⟶ N) :
    moduleDualPresheafPrecomp φ ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (moduleDualPresheaf M) =
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (moduleDualPresheaf N) ≫
        (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (moduleSheafDualMap φ).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
    (moduleDualPresheafPrecomp φ)

/-- The dual-sheaf morphism sends an identity to the identity.
@isnad1 id=eq.0h2v.s5.4a4e28462bf8 from=translated src=- shape=1acb6650 vocab=fa37e889
-/
@[simp]
theorem moduleSheafDualMap_id (M : X.Modules) :
    moduleSheafDualMap (𝟙 M) = 𝟙 (moduleSheafDual M) :=
  (moduleSheafDualFunctor X).map_id (op M)

/-- The dual-sheaf morphism reverses the order of composition.
@isnad1 id=eq.0h6v.s6.36012f8a7ca4 from=translated src=- shape=779fc4c2 vocab=618c093c
-/
theorem moduleSheafDualMap_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    moduleSheafDualMap (φ ≫ ψ) = moduleSheafDualMap ψ ≫ moduleSheafDualMap φ :=
  (moduleSheafDualFunctor X).map_comp ψ.op φ.op

/-- An actual module-sheaf isomorphism gives an isomorphism of its original dual sheaves.-/
def moduleSheafDualIso (e : M ≅ N) : moduleSheafDual N ≅ moduleSheafDual M :=
  (moduleSheafDualFunctor X).mapIso e.op

/-- The forward dual isomorphism is precomposition with the original forward morphism.
@isnad1 id=eq.0h4v.s5.358d09787758 from=translated src=- shape=2dec1883 vocab=1e109ed9
-/
@[simp]
theorem moduleSheafDualIso_hom (e : M ≅ N) :
    (moduleSheafDualIso e).hom = moduleSheafDualMap e.hom := rfl

/-- The inverse dual isomorphism is precomposition with the original inverse morphism.
@isnad1 id=eq.0h4v.s5.2c2780a7147f from=translated src=- shape=5ef77cff vocab=729f08a8
-/
@[simp]
theorem moduleSheafDualIso_inv (e : M ≅ N) :
    (moduleSheafDualIso e).inv = moduleSheafDualMap e.inv := rfl

end AlgebraicGeometry.Scheme.Modules
