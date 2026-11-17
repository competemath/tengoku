import Tengoku.CharPNahodgeFormalization.LSZ.VectorFields
import Tengoku.CharPNahodgeFormalization.LSZ.SheafTensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The tangent sheaf and the Higgs tensor sheaf

The relative vector fields constructed in `LSZ.VectorFields` form a
presheaf of modules over the structure sheaf.  We sheafify that presheaf to
obtain an actual object of `X.Modules`.  The tensor product used below is
the tensor product over the sheaf of rings from `LSZ.SheafTensor`; it is not
a construction specific to schemes.
-/

open CategoryTheory Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry MonoidalCategory TensorProduct

namespace LSZ.SmoothScheme

universe u

noncomputable section

variable {k : Type u} [Field k] (X : LSZ.SmoothScheme k)

/-- The scalar action carried by the bundled `ModuleCat` section agrees
with the usual scheme-section scalar action.
@isnad1 id=eq.0h6v.s20.79348efe463e from=translated src=- shape=9c83cb93 vocab=5864d70b
-/
lemma bundled_smul_eq_smul (M : X.scheme.Modules) (U : X.scheme.Opens)
    (a : Γ(X.scheme, U)) (m : Γ(M, U)) :
    (((M.val.obj (.op U)).smul
      (show X.scheme.ringCatSheaf.obj.obj (.op U) from a)).hom m) =
      a • m := by
  rfl

namespace VectorField

/-- Scalar multiplication, named so it can be used while assembling the
presheaf-of-modules structure.-/
def smulAt (U : X.scheme.Opens) (a : Γ(X.scheme, U))
    (D : X.VectorField U) : X.VectorField U :=
  a • D

end VectorField

/-- The additive presheaf of canonical relative vector fields.-/
def vectorFieldAbPresheaf : X.scheme.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (X.VectorField U.unop)
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := fun D ↦ D.restrict (leOfHom f.unop)
      map_zero' := by ext W hW a; rfl
      map_add' := by intro D E; ext W hW a; rfl }
  map_id U := by
    ext D W hW a
    rfl
  map_comp f g := by
    ext D W hW a
    rfl

/--
@isnad1 id=eq.0h7v.s11.70e21867265d from=translated src=- shape=f6c97136 vocab=11be5790
-/
lemma vectorFieldAbPresheaf_map_smul {U V : X.scheme.Opensᵒᵖ}
    (f : U ⟶ V) (a : Γ(X.scheme, U.unop))
    (D : X.VectorField U.unop) :
    (vectorFieldAbPresheaf X).map f (a • D) =
      VectorField.smulAt X V.unop (X.scheme.presheaf.map f a)
        (D.restrict (leOfHom f.unop)) := by
  change (a • D).restrict (leOfHom f.unop) =
    VectorField.smulAt X V.unop (X.scheme.presheaf.map f a)
      (D.restrict (leOfHom f.unop))
  ext W hW b
  change X.scheme.presheaf.map
      (homOfLE (hW.trans (leOfHom f.unop))).op a *
        D.deriv W (hW.trans (leOfHom f.unop)) b =
    X.scheme.presheaf.map (homOfLE hW).op
        (X.scheme.presheaf.map f a) *
      D.deriv W (hW.trans (leOfHom f.unop)) b
  congr 1
  rw [← CommRingCat.comp_apply, ← X.scheme.presheaf.map_comp]
  rfl

/-- Canonical relative vector fields as a presheaf of modules over
`ᵊa_X`.-/
def vectorFieldPresheaf : X.scheme.PresheafOfModules := by
  letI (U : X.scheme.Opensᵒᵖ) :
      Module (X.scheme.ringCatSheaf.obj.obj U)
        ((vectorFieldAbPresheaf X).obj U) := by
    change Module Γ(X.scheme, U.unop) (X.VectorField U.unop)
    infer_instance
  apply PresheafOfModules.ofPresheaf (vectorFieldAbPresheaf X)
  intro U V f a D
  change (a • D).restrict (leOfHom f.unop) =
    VectorField.smulAt X V.unop (X.scheme.presheaf.map f a)
      (D.restrict (leOfHom f.unop))
  exact vectorFieldAbPresheaf_map_smul X f a D

/-- The tangent sheaf obtained by sheafifying the canonical presheaf of
relative vector fields.-/
def tangent : X.scheme.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.scheme.ringCatSheaf.obj)).obj
    (vectorFieldPresheaf X)

/-- The unit from canonical vector fields into the tangent sheaf.-/
def tangentUnit : vectorFieldPresheaf X ⟶ (tangent X).val :=
  (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.scheme.ringCatSheaf.obj)).unit.app (vectorFieldPresheaf X) ≫
    CommRingSheaf.unrestrictId X.scheme.sheaf (tangent X).val

/-- Regard an explicit canonical vector field as a section of the vector
field presheaf.-/
def vectorFieldAsPresheafSection (U : X.scheme.Opens) (D : X.VectorField U) :
    (vectorFieldPresheaf X).obj (.op U) := by
  unfold vectorFieldPresheaf
  exact D

/--
@isnad1 id=eq.1h5v.s16.ab4b8084407a from=translated src=- shape=a330db42 vocab=90df22ba
-/
@[simp]
lemma vectorFieldAsPresheafSection_map {U V : X.scheme.Opens}
    (hVU : V ≤ U) (D : X.VectorField U) :
    (vectorFieldPresheaf X).map (homOfLE hVU).op
        (vectorFieldAsPresheafSection X U D) =
      vectorFieldAsPresheafSection X V (D.restrict hVU) := by
  change D.restrict hVU = D.restrict hVU
  rfl

/--
@isnad1 id=eq.0h5v.s15.aa0c1a792c50 from=translated src=- shape=e9b9897b vocab=4d34a31d
-/
lemma vectorFieldAsPresheafSection_smul (U : X.scheme.Opens)
    (a : X.scheme.ringCatSheaf.obj.obj (.op U)) (D : X.VectorField U) :
    vectorFieldAsPresheafSection X U ((show Γ(X.scheme, U) from a) • D) =
      a • vectorFieldAsPresheafSection X U D := by
  rfl

/-- An explicit canonical vector field gives a section of the tangent
sheaf.-/
def tangentSection (U : X.scheme.Opens) (D : X.VectorField U) :
    Γ(tangent X, U) :=
  (tangentUnit X).app (.op U) (vectorFieldAsPresheafSection X U D)

/--
@isnad1 id=eq.0h3v.s10.9b7a8933f3c1 from=translated src=- shape=963b13ec vocab=cb8b39a0
-/
@[simp]
lemma tangentSection_zero (U : X.scheme.Opens) :
    tangentSection X U 0 = 0 := by
  exact map_zero ((tangentUnit X).app (.op U)).hom

/--
@isnad1 id=eq.0h5v.s10.36ca08bc5640 from=translated src=- shape=949596e5 vocab=adb4f6e8
-/
lemma tangentSection_add (U : X.scheme.Opens) (D E : X.VectorField U) :
    tangentSection X U (D + E) =
      tangentSection X U D + tangentSection X U E := by
  exact map_add ((tangentUnit X).app (.op U)).hom D E

/--
@isnad1 id=eq.0h5v.s12.21bb69168dd4 from=translated src=- shape=f3e4a0dd vocab=fa59c28c
-/
lemma tangentSection_smul (U : X.scheme.Opens)
    (a : Γ(X.scheme, U))
    (D : X.VectorField U) :
    tangentSection X U (a • D) = a • tangentSection X U D := by
  let a' : X.scheme.ringCatSheaf.obj.obj (.op U) := a
  change (tangentUnit X).app (.op U)
      (vectorFieldAsPresheafSection X U (a • D)) =
    a • tangentSection X U D
  rw [vectorFieldAsPresheafSection_smul X U a' D]
  exact (map_smul ((tangentUnit X).app (.op U)).hom a'
    (vectorFieldAsPresheafSection X U D)).trans
      (bundled_smul_eq_smul X (tangent X) U a (tangentSection X U D))

/--
@isnad1 id=eq.1h5v.s16.3c7739ad7114 from=translated src=- shape=88b13669 vocab=9428e50b
-/
@[simp]
lemma tangentSection_restrict {U V : X.scheme.Opens}
    (hVU : V ≤ U) (D : X.VectorField U) :
    (tangent X).val.map (homOfLE hVU).op (tangentSection X U D) =
      tangentSection X V (D.restrict hVU) := by
  rw [tangentSection, tangentSection,
    ← vectorFieldAsPresheafSection_map X hVU D]
  exact (PresheafOfModules.naturality_apply (tangentUnit X)
    (homOfLE hVU).op (vectorFieldAsPresheafSection X U D)).symm

/-- `ᵊf_X ⊗_{ᵊa_X} M`, formed using the tensor product of module
sheaves on the underlying ringed space.-/
def higgsTensor (M : X.scheme.Modules) : X.scheme.Modules :=
  CommRingSheaf.tensorObj X.scheme.sheaf (tangent X) M

/-- The pure tensor `D ⊗ m` in the Higgs tensor sheaf.-/
def higgsTmul (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D : X.VectorField U) (m : Γ(M, U)) : Γ(higgsTensor X M, U) :=
  CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
    (tangentSection X U D) m

/--
@isnad1 id=eq.0h5v.s10.4ee776e54b4c from=translated src=- shape=cd58ec2a vocab=b7fdcc1f
-/
@[simp]
lemma higgsTmul_zero_left (M : X.scheme.Modules) (U : X.scheme.Opens)
    (m : Γ(M, U)) :
    higgsTmul X M U 0 m = 0 := by
  change CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
    (tangentSection X U 0) m = 0
  calc
    _ = CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U) 0 m :=
      congrArg (fun t ↦ CommRingSheaf.tmul X.scheme.sheaf
        (tangent X) M (.op U) t m) (tangentSection_zero X U)
    _ = 0 := CommRingSheaf.zero_tmul X.scheme.sheaf
      (tangent X) M (.op U) m

/--
@isnad1 id=eq.0h7v.s11.1c0a2338aa51 from=translated src=- shape=8249b005 vocab=f96d6768
-/
lemma higgsTmul_add_left (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D E : X.VectorField U) (m : Γ(M, U)) :
    higgsTmul X M U (D + E) m =
      higgsTmul X M U D m + higgsTmul X M U E m := by
  change CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
      (tangentSection X U (D + E)) m =
    CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
        (tangentSection X U D) m +
      CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
        (tangentSection X U E) m
  calc
    _ = CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
        (tangentSection X U D + tangentSection X U E) m :=
      congrArg (fun t ↦ CommRingSheaf.tmul X.scheme.sheaf
        (tangent X) M (.op U) t m) (tangentSection_add X U D E)
    _ = _ := CommRingSheaf.add_tmul X.scheme.sheaf
      (tangent X) M (.op U) (tangentSection X U D)
        (tangentSection X U E) m

/--
@isnad1 id=eq.0h7v.s12.c3ea92400cd2 from=translated src=- shape=93ade305 vocab=4c192be9
-/
lemma higgsTmul_smul_left (M : X.scheme.Modules) (U : X.scheme.Opens)
    (a : Γ(X.scheme, U)) (D : X.VectorField U) (m : Γ(M, U)) :
    higgsTmul X M U (a • D) m = a • higgsTmul X M U D m := by
  let a' : X.scheme.ringCatSheaf.obj.obj (.op U) := a
  unfold higgsTmul
  rw [tangentSection_smul X U a D]
  change CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
        ((((tangent X).val.obj (.op U)).smul a').hom
          (tangentSection X U D)) m =
      (((higgsTensor X M).val.obj (.op U)).smul a').hom
        (CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op U)
          (tangentSection X U D) m)
  exact CommRingSheaf.smul_tmul X.scheme.sheaf
    (tangent X) M (.op U) a' (tangentSection X U D) m

/--
@isnad1 id=eq.0h5v.s11.ffdfa7ffa573 from=translated src=- shape=4085aeb6 vocab=b7fdcc1f
-/
@[simp]
lemma higgsTmul_zero_right (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D : X.VectorField U) :
    higgsTmul X M U D 0 = 0 := by
  exact CommRingSheaf.tmul_zero X.scheme.sheaf (tangent X) M (.op U)
    (tangentSection X U D)

/--
@isnad1 id=eq.0h7v.s11.a76284f1583f from=translated src=- shape=9b130758 vocab=f96d6768
-/
lemma higgsTmul_add_right (M : X.scheme.Modules) (U : X.scheme.Opens)
    (D : X.VectorField U) (m n : Γ(M, U)) :
    higgsTmul X M U D (m + n) =
      higgsTmul X M U D m + higgsTmul X M U D n := by
  exact CommRingSheaf.tmul_add X.scheme.sheaf (tangent X) M (.op U)
    (tangentSection X U D) m n

/--
@isnad1 id=eq.0h7v.s13.cef2e51a994a from=translated src=- shape=1ba452e9 vocab=4c192be9
-/
lemma higgsTmul_smul_right (M : X.scheme.Modules) (U : X.scheme.Opens)
    (a : Γ(X.scheme, U)) (D : X.VectorField U) (m : Γ(M, U)) :
    higgsTmul X M U D (a • m) = a • higgsTmul X M U D m := by
  exact CommRingSheaf.tmul_smul X.scheme.sheaf (tangent X) M (.op U) a
    (tangentSection X U D) m

/--
@isnad1 id=eq.1h7v.s12.52a3db84e8bc from=translated src=- shape=e6bd83f1 vocab=8c90c8bf
-/
@[simp]
lemma higgsTmul_restrict (M : X.scheme.Modules) {U V : X.scheme.Opens}
    (hVU : V ≤ U) (D : X.VectorField U) (m : Γ(M, U)) :
    (higgsTensor X M).presheaf.map (homOfLE hVU).op
        (higgsTmul X M U D m) =
      higgsTmul X M V (D.restrict hVU)
        (M.presheaf.map (homOfLE hVU).op m) := by
  change (higgsTensor X M).val.map (homOfLE hVU).op
      (higgsTmul X M U D m) =
    higgsTmul X M V (D.restrict hVU)
      (M.val.map (homOfLE hVU).op m)
  have h := CommRingSheaf.tmul_map X.scheme.sheaf (tangent X) M
    (homOfLE hVU).op (tangentSection X U D) m
  calc
    _ = CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op V)
        ((tangent X).val.map (homOfLE hVU).op (tangentSection X U D))
        (M.val.map (homOfLE hVU).op m) := h
    _ = _ := congrArg
      (fun t ↦ CommRingSheaf.tmul X.scheme.sheaf (tangent X) M (.op V)
        t (M.val.map (homOfLE hVU).op m))
      (tangentSection_restrict X hVU D)

/-- Functoriality of the Higgs tensor sheaf in its coefficient module.-/
def higgsTensorMap {M N : X.scheme.Modules} (f : M ⟶ N) :
    higgsTensor X M ⟶ higgsTensor X N :=
  CommRingSheaf.tensorHom X.scheme.sheaf (𝟙 (tangent X)) f

/--
@isnad1 id=eq.0h8v.s11.465f11938f32 from=translated src=- shape=0f733ed3 vocab=21f75e0d
-/
@[simp]
lemma higgsTensorMap_tmul {M N : X.scheme.Modules} (f : M ⟶ N)
    (U : X.scheme.Opens) (D : X.VectorField U) (m : Γ(M, U)) :
    (higgsTensorMap X f).app U (higgsTmul X M U D m) =
      higgsTmul X N U D (f.app U m) := by
  have h := CommRingSheaf.tensorHom_tmul X.scheme.sheaf
    (𝟙 (tangent X)) f (.op U) (tangentSection X U D) m
  exact h

/--
@isnad1 id=eq.0h3v.s6.53db60a07a3f from=translated src=- shape=f3324b3e vocab=bb0daf83
-/
@[simp]
lemma higgsTensorMap_id (M : X.scheme.Modules) :
    higgsTensorMap X (𝟙 M) = 𝟙 (higgsTensor X M) := by
  exact CommRingSheaf.tensorHom_id X.scheme.sheaf (tangent X) M

/--
@isnad1 id=eq.0h7v.s7.e5618aeb8a70 from=translated src=- shape=dd9e6572 vocab=0215139a
-/
@[simp]
lemma higgsTensorMap_comp {M N P : X.scheme.Modules}
    (f : M ⟶ N) (g : N ⟶ P) :
    higgsTensorMap X (f ≫ g) =
      higgsTensorMap X f ≫ higgsTensorMap X g := by
  exact CommRingSheaf.tensorHom_comp X.scheme.sheaf
    (𝟙 (tangent X)) (𝟙 (tangent X)) f g

end

end LSZ.SmoothScheme
