import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_TateFormal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u

noncomputable section

open WeierstrassCurve

structure KatzModularForm (R : Type u) [CommRing R] (k : ℤ) : Type (u + 1) where

  toFun : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A), IsUnit W.Δ → A

  map_toFun : ∀ ⦃A B : Type u⦄ [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (hW' : IsUnit (W.map (f : A →+* B)).Δ), toFun (W.map (f : A →+* B)) hW' = f (toFun W hW)

  toFun_variableChange : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (C : VariableChange A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (C • W).Δ),
    toFun (C • W) hW' = ((C.u⁻¹ ^ k : Aˣ) : A) * toFun W hW

namespace KatzModularForm

variable {R : Type u} [CommRing R] {k l : ℤ}

/--
@isnad1 id=injectiv.0h2v.s5.60c633149a38 from=translated src=- shape=7066c3fc vocab=be729be6
-/
theorem toFun_injective : Function.Injective (toFun : KatzModularForm R k → _) := by
  rintro ⟨F, _, _⟩ ⟨G, _, _⟩ h
  congr

/--
@isnad1 id=eq.1h4v.s6.2467d6203460 from=translated src=- shape=f8ea19b4 vocab=837b8277
-/
@[ext]
theorem ext {F G : KatzModularForm R k}
    (h : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ),
      F.toFun W hW = G.toFun W hW) : F = G :=
  toFun_injective (by funext A _ _ W hW; exact h W hW)

instance : Zero (KatzModularForm R k) :=
  ⟨{ toFun := fun _ _ _ _ _ => 0
     map_toFun := by intros; simp
     toFun_variableChange := by intros; simp }⟩

instance : Add (KatzModularForm R k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW => F.toFun W hW + G.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_add, F.map_toFun f W hW hW', G.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', G.toFun_variableChange C W hW hW', mul_add] }⟩

instance : Neg (KatzModularForm R k) :=
  ⟨fun F =>
    { toFun := fun _ _ _ W hW => -F.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_neg, F.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', mul_neg] }⟩

instance : Sub (KatzModularForm R k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW => F.toFun W hW - G.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_sub, F.map_toFun f W hW hW', G.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', G.toFun_variableChange C W hW hW', mul_sub] }⟩

instance : SMul R (KatzModularForm R k) :=
  ⟨fun c F =>
    { toFun := fun _ _ _ W hW => c • F.toFun W hW
      map_toFun := by
        intro A B _ _ _ _ f W hW hW'
        rw [map_smul, F.map_toFun f W hW hW']
      toFun_variableChange := by
        intro A _ _ C W hW hW'
        rw [F.toFun_variableChange C W hW hW', mul_smul_comm] }⟩

/--
@isnad1 id=eq.1h4v.s6.43e051262900 from=translated src=- shape=2e6f470d vocab=837b8277
-/
@[simp] theorem zero_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (0 : KatzModularForm R k).toFun W hW = 0 := rfl

/--
@isnad1 id=eq.1h6v.s6.31e97cc5e9c5 from=translated src=- shape=b20966fb vocab=02bf9ace
-/
@[simp] theorem add_toFun (F G : KatzModularForm R k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (F + G).toFun W hW = F.toFun W hW + G.toFun W hW := rfl

/--
@isnad1 id=eq.1h5v.s6.ea2117f1a3f1 from=translated src=- shape=966ba87b vocab=bcfea6c8
-/
@[simp] theorem neg_toFun (F : KatzModularForm R k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) : (-F).toFun W hW = -F.toFun W hW := rfl

/--
@isnad1 id=eq.1h6v.s6.b78991f5dcd7 from=translated src=- shape=b20966fb vocab=4754d52a
-/
@[simp] theorem sub_toFun (F G : KatzModularForm R k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (F - G).toFun W hW = F.toFun W hW - G.toFun W hW := rfl

/--
@isnad1 id=eq.1h6v.s6.3237da3dddc5 from=translated src=- shape=cb9722a7 vocab=e979c4ba
-/
@[simp] theorem smul_toFun (c : R) (F : KatzModularForm R k) {A : Type u} [CommRing A]
    [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (c • F).toFun W hW = c • F.toFun W hW := rfl

instance : AddCommGroup (KatzModularForm R k) where
  add_assoc F G H := by ext; simp [add_assoc]
  zero_add F := by ext; simp
  add_zero F := by ext; simp
  add_comm F G := by ext; simp [add_comm]
  neg_add_cancel F := by ext; simp
  sub_eq_add_neg F G := by ext; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (KatzModularForm R k) where
  one_smul F := by ext; simp
  mul_smul a b F := by ext; simp [mul_smul]
  smul_zero a := by ext; simp
  smul_add a F G := by ext; simp
  add_smul a b F := by ext; simp [add_smul]
  zero_smul F := by ext; simp

def mul (F : KatzModularForm R k) (G : KatzModularForm R l) : KatzModularForm R (k + l) where
  toFun _ _ _ W hW := F.toFun W hW * G.toFun W hW
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    rw [map_mul, F.map_toFun f W hW hW', G.map_toFun f W hW hW']
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [F.toFun_variableChange C W hW hW', G.toFun_variableChange C W hW hW', zpow_add,
      Units.val_mul]
    ring

/--
@isnad1 id=eq.1h7v.s6.61b77cb60335 from=translated src=- shape=30599d69 vocab=87bea963
-/
@[simp] theorem mul_toFun (F : KatzModularForm R k) (G : KatzModularForm R l) {A : Type u}
    [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (F.mul G).toFun W hW = F.toFun W hW * G.toFun W hW := rfl

def qExpansion (F : KatzModularForm R k) : LaurentSeries R :=
  F.toFun (ModularCurve.tateLaurent R) (ModularCurve.tateLaurent R).isUnit_Δ

/--
@isnad1 id=eq.0h2v.s6.4c79d0be7249 from=translated src=- shape=dbaaca6e vocab=bf37e2be
-/
@[simp] theorem qExpansion_zero : (0 : KatzModularForm R k).qExpansion = 0 := rfl

/--
@isnad1 id=eq.0h4v.s7.0f0c731c1040 from=translated src=- shape=bc4ad212 vocab=d4aebb64
-/
@[simp] theorem qExpansion_add (F G : KatzModularForm R k) :
    (F + G).qExpansion = F.qExpansion + G.qExpansion := rfl

/--
@isnad1 id=eq.0h3v.s6.c0b6ca4981d3 from=translated src=- shape=9f51ca24 vocab=54afe495
-/
@[simp] theorem qExpansion_neg (F : KatzModularForm R k) : (-F).qExpansion = -F.qExpansion := rfl

/--
@isnad1 id=eq.0h4v.s7.437e34760cb0 from=translated src=- shape=bc4ad212 vocab=79f83b83
-/
@[simp] theorem qExpansion_sub (F G : KatzModularForm R k) :
    (F - G).qExpansion = F.qExpansion - G.qExpansion := rfl

/--
@isnad1 id=eq.0h4v.s7.c5f89365f22e from=translated src=- shape=72569d79 vocab=e7b1166d
-/
@[simp] theorem qExpansion_smul (c : R) (F : KatzModularForm R k) :
    (c • F).qExpansion = c • F.qExpansion := by
  simp only [qExpansion, smul_toFun, Algebra.smul_def, ← HahnSeries.C_mul_eq_smul]
  congr 1
  rw [RingHom.algebraMap_toAlgebra]
  simp

/--
@isnad1 id=eq.0h5v.s6.d5088f1d0709 from=translated src=- shape=fb56fc47 vocab=c2d3f106
-/
@[simp] theorem qExpansion_mul (F : KatzModularForm R k) (G : KatzModularForm R l) :
    (F.mul G).qExpansion = F.qExpansion * G.qExpansion := rfl

variable (R)

def c₄ : KatzModularForm R 4 where
  toFun _ _ _ W _ := W.c₄
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact W.map_c₄ (f : A →+* B)
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [W.variableChange_c₄ C]
    norm_cast

def c₆ : KatzModularForm R 6 where
  toFun _ _ _ W _ := W.c₆
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact W.map_c₆ (f : A →+* B)
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [W.variableChange_c₆ C]
    norm_cast

def discr : KatzModularForm R 12 where
  toFun _ _ _ W _ := W.Δ
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact W.map_Δ (f : A →+* B)
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    rw [W.variableChange_Δ C]
    norm_cast

variable {R}

/--
@isnad1 id=eq.1h3v.s5.d5d548b8424f from=translated src=- shape=3c0e29ce vocab=223aab28
-/
@[simp] theorem c₄_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (c₄ R).toFun W hW = W.c₄ := rfl

/--
@isnad1 id=eq.1h3v.s5.b4edfae5ccdd from=translated src=- shape=3c0e29ce vocab=63cd300b
-/
@[simp] theorem c₆_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (c₆ R).toFun W hW = W.c₆ := rfl

/--
@isnad1 id=eq.1h3v.s5.47fa560e2377 from=translated src=- shape=b51f935d vocab=450bf2d8
-/
@[simp] theorem discr_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (discr R).toFun W hW = W.Δ := rfl

end KatzModularForm

end
