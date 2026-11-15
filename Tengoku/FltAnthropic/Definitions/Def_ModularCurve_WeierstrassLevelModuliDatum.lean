import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LevelModuliPackage
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_WeierstrassLevelCarrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace ModularCurve

structure RigidWeierstrassData (A : Type u) [CommRing A] where

  Raw : (T : Type u) → [CommRing T] → [Algebra A T] → Type u

  curve : {T : Type u} → [CommRing T] → [Algebra A T] → Raw T → WeierstrassCurve T

  isUnit_Δ : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : Raw T), IsUnit (curve x).Δ

  mapRing : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → Raw T → Raw T'

  curve_mapRing : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : Raw T), curve (mapRing f x) = (curve x).map f.toRingHom

  mapRing_id : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : Raw T), mapRing (AlgHom.id A T) x = x

  mapRing_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : Raw T), mapRing (g.comp f) x = mapRing g (mapRing f x)

  act : {T : Type u} → [CommRing T] → [Algebra A T] → WeierstrassCurve.VariableChange T → Raw T → Raw T

  act_one : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : Raw T), act (1 : WeierstrassCurve.VariableChange T) x = x

  act_mul : ∀ {T : Type u} [CommRing T] [Algebra A T] (C C' : WeierstrassCurve.VariableChange T) (x : Raw T),
    act (C * C') x = act C (act C' x)

  curve_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (x : Raw T),
    curve (act C x) = C • curve x

  mapRing_act : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (C : WeierstrassCurve.VariableChange T) (x : Raw T),
    mapRing f (act C x) = act (C.map f.toRingHom) (mapRing f x)

namespace RigidWeierstrassData

variable {A : Type u} [CommRing A] (R : RigidWeierstrassData.{u} A)

def Rel {T : Type u} [CommRing T] [Algebra A T] (x y : R.Raw T) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange T, y = R.act C x

/--
@isnad1 id=rel.0h4v.s5.74441f7a22dd from=translated src=- shape=ce4aa7a8 vocab=d79dfa8c
-/
theorem Rel.refl {T : Type u} [CommRing T] [Algebra A T] (x : R.Raw T) : R.Rel x x := ⟨1, (R.act_one x).symm⟩

/--
@isnad1 id=rel.2h6v.s6.7e31e4f273fc from=translated src=- shape=2a6a3cbd vocab=d79dfa8c
-/
theorem Rel.trans {T : Type u} [CommRing T] [Algebra A T] {x y z : R.Raw T} (h : R.Rel x y) (h' : R.Rel y z) :
    R.Rel x z := by
  obtain ⟨C, rfl⟩ := h; obtain ⟨C', rfl⟩ := h'
  exact ⟨C' * C, (R.act_mul C' C x).symm⟩

/--
@isnad1 id=eq.0h4v.s6.20f46fa3bff2 from=translated src=- shape=acb03cce vocab=691749ed
-/
theorem smul_curve_eq (T : Type u) [CommRing T] (C C' : WeierstrassCurve.VariableChange T) (W : WeierstrassCurve T) :
    (C * C') • W = C • (C' • W) := mul_smul C C' W

def Pt (T : Type u) [CommRing T] [Algebra A T] : Type u := Quot (R.Rel (T := T))

def map {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') :
    R.Pt T → R.Pt T' :=
  Quot.lift (fun x => Quot.mk _ (R.mapRing f x)) (by
    rintro x y ⟨C, rfl⟩
    exact Quot.sound ⟨C.map f.toRingHom, R.mapRing_act f C x⟩)

/--
@isnad1 id=eq.0h6v.s7.9bae2c070a4b from=translated src=- shape=bc55743c vocab=1cf52924
-/
theorem map_mk {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : R.Raw T) : R.map f (Quot.mk _ x) = Quot.mk _ (R.mapRing f x) := rfl

noncomputable def jOf {T : Type u} [CommRing T] [Algebra A T] : R.Pt T → T :=
  Quot.lift (fun x => (R.curve x).jOfUnit (R.isUnit_Δ x)) (by
    rintro x y ⟨C, rfl⟩
    show (R.curve x).jOfUnit (R.isUnit_Δ x) = (R.curve (R.act C x)).jOfUnit (R.isUnit_Δ (R.act C x))
    have key : ∀ (W' : WeierstrassCurve T) (hW' : IsUnit W'.Δ) (hEq : W' = C • R.curve x),
        W'.jOfUnit hW' = (R.curve x).jOfUnit (R.isUnit_Δ x) := by
      intro W' hW' hEq
      subst hEq
      exact (R.curve x).jOfUnit_variableChange C (R.isUnit_Δ x) hW'
    exact (key _ _ (R.curve_act C x)).symm)

/--
@isnad1 id=eq.0h4v.s6.86b096f58b31 from=translated src=- shape=05ab71ba vocab=4a71b116
-/
theorem jOf_mk {T : Type u} [CommRing T] [Algebra A T] (x : R.Raw T) :
    R.jOf (Quot.mk _ x) = (R.curve x).jOfUnit (R.isUnit_Δ x) := rfl

noncomputable def toLevelModuliDatum : LevelModuliDatum.{u} A where
  Pt := fun T _ _ => R.Pt T
  map := fun f => R.map f
  map_id := by
    intro T _ _ x
    induction x using Quot.ind with
    | mk x => rw [map_mk, R.mapRing_id]
  map_comp := by
    intro T T' T'' _ _ _ _ _ _ f g x
    induction x using Quot.ind with
    | mk x => rw [map_mk, map_mk, map_mk, R.mapRing_comp]
  jOf := fun x => R.jOf x
  jOf_map := by
    intro T T' _ _ _ _ f x
    induction x using Quot.ind with
    | mk x =>
      rw [map_mk, jOf_mk, jOf_mk]
      have key : ∀ (W' : WeierstrassCurve T') (hW' : IsUnit W'.Δ) (hEq : W' = (R.curve x).map f.toRingHom),
          W'.jOfUnit hW' = f ((R.curve x).jOfUnit (R.isUnit_Δ x)) := by
        intro W' hW' hEq
        subst hEq
        exact (R.curve x).jOfUnit_map f.toRingHom (R.isUnit_Δ x) hW'
      exact key _ _ (R.curve_mapRing f x)

end RigidWeierstrassData

end ModularCurve
