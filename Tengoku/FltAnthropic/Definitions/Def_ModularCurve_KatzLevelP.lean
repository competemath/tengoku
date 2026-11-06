import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_KatzLevelOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

section Elements

variable {A : Type*} [CommRing A]

def indepElt (W : WeierstrassCurve A) (p : ℕ) (x₀ x : A) : A :=
  ∏ a ∈ Finset.Icc 1 ((p - 1) / 2), (x * (W.ΨSq a).eval x₀ - (W.Φ a).eval x₀)

def InLine (W : WeierstrassCurve A) (p : ℕ) (x₀ x : A) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ a ≤ (p - 1) / 2 ∧ x * (W.ΨSq a).eval x₀ = (W.Φ a).eval x₀

end Elements

@[ext]
structure LevelPData (A : Type u) where

  xP : A

  yP : A

  xQ : A

  yQ : A

namespace LevelPData

variable {A : Type u} {B : Type v}

def swap (D : LevelPData A) : LevelPData A :=
  ⟨D.xQ, D.yQ, D.xP, D.yP⟩

/--
@isnad1 id=eq.0h2v.s3.7da6113bb68a from=translated src=- shape=fd8cce4c vocab=2a54c82c
-/
@[simp] theorem swap_xP (D : LevelPData A) : D.swap.xP = D.xQ := rfl
/--
@isnad1 id=eq.0h2v.s3.76429262f229 from=translated src=- shape=fd8cce4c vocab=359943a9
-/
@[simp] theorem swap_yP (D : LevelPData A) : D.swap.yP = D.yQ := rfl
/--
@isnad1 id=eq.0h2v.s3.2917e2d35bec from=translated src=- shape=fd8cce4c vocab=2a54c82c
-/
@[simp] theorem swap_xQ (D : LevelPData A) : D.swap.xQ = D.xP := rfl
/--
@isnad1 id=eq.0h2v.s3.0c94b82a22e2 from=translated src=- shape=fd8cce4c vocab=359943a9
-/
@[simp] theorem swap_yQ (D : LevelPData A) : D.swap.yQ = D.yP := rfl

/--
@isnad1 id=eq.0h2v.s3.c9d31dd1aa49 from=translated src=- shape=efbf31f7 vocab=b06397fc
-/
@[simp] theorem swap_swap (D : LevelPData A) : D.swap.swap = D := rfl

variable [CommRing A] [CommRing B]

def map (f : A →+* B) (D : LevelPData A) : LevelPData B :=
  ⟨f D.xP, f D.yP, f D.xQ, f D.yQ⟩

/--
@isnad1 id=eq.0h4v.s6.5b40c85db622 from=translated src=- shape=ea5c27f2 vocab=36c9501d
-/
@[simp] theorem map_xP (f : A →+* B) (D : LevelPData A) : (D.map f).xP = f D.xP := rfl
/--
@isnad1 id=eq.0h4v.s6.189f433223cf from=translated src=- shape=ea5c27f2 vocab=8af6023e
-/
@[simp] theorem map_yP (f : A →+* B) (D : LevelPData A) : (D.map f).yP = f D.yP := rfl
/--
@isnad1 id=eq.0h4v.s6.51316039c899 from=translated src=- shape=ea5c27f2 vocab=c6ee9be6
-/
@[simp] theorem map_xQ (f : A →+* B) (D : LevelPData A) : (D.map f).xQ = f D.xQ := rfl
/--
@isnad1 id=eq.0h4v.s6.27a84f6ba005 from=translated src=- shape=ea5c27f2 vocab=25f0919b
-/
@[simp] theorem map_yQ (f : A →+* B) (D : LevelPData A) : (D.map f).yQ = f D.yQ := rfl

def variableChange (C : VariableChange A) (D : LevelPData A) : LevelPData A where
  xP := ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xP - C.r)
  yP := ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yP - C.s * (D.xP - C.r) - C.t)
  xQ := ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xQ - C.r)
  yQ := ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yQ - C.s * (D.xQ - C.r) - C.t)

/--
@isnad1 id=eq.0h3v.s6.29defbe27f78 from=translated src=- shape=3186031f vocab=5577fcb7
-/
@[simp] theorem variableChange_xP (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).xP = ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xP - C.r) := rfl
/--
@isnad1 id=eq.0h3v.s7.9985bad52733 from=translated src=- shape=481b5db0 vocab=a775e0b5
-/
@[simp] theorem variableChange_yP (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).yP = ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yP - C.s * (D.xP - C.r) - C.t) := rfl
/--
@isnad1 id=eq.0h3v.s6.6c00ebf73fad from=translated src=- shape=3186031f vocab=6ce9ab12
-/
@[simp] theorem variableChange_xQ (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).xQ = ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xQ - C.r) := rfl
/--
@isnad1 id=eq.0h3v.s7.c0fc4bfeaa07 from=translated src=- shape=481b5db0 vocab=1b37e3cf
-/
@[simp] theorem variableChange_yQ (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).yQ = ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yQ - C.s * (D.xQ - C.r) - C.t) := rfl

end LevelPData

structure IsLevelPStructure {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ)
    (D : LevelPData A) : Prop where

  equation_P : W.toAffine.Equation D.xP D.yP

  equation_Q : W.toAffine.Equation D.xQ D.yQ

  preΨ_P : (W.preΨ p).eval D.xP = 0

  preΨ_Q : (W.preΨ p).eval D.xQ = 0

  isUnit_indepElt_PQ : IsUnit (indepElt W p D.xP D.xQ)

  isUnit_indepElt_QP : IsUnit (indepElt W p D.xQ D.xP)

namespace IsLevelPStructure

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] {W : WeierstrassCurve A} {p : ℕ}
  {D : LevelPData A}

/--
@isnad1 id=islevelp.1h4v.s4.eabe0ac88726 from=translated src=- shape=ea6edbc8 vocab=d190d5cd
-/
theorem swap (h : IsLevelPStructure W p D) : IsLevelPStructure W p D.swap :=
  ⟨h.equation_Q, h.equation_P, h.preΨ_Q, h.preΨ_P, h.isUnit_indepElt_QP, h.isUnit_indepElt_PQ⟩

end IsLevelPStructure

structure KatzLevelPForm (R : Type u) [CommRing R] (p : ℕ) (k : ℤ) : Type (u + 1) where

  toFun : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A), IsUnit W.Δ →
    ∀ D : LevelPData A, IsLevelPStructure W p D → A

  map_toFun : ∀ ⦃A B : Type u⦄ [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (hW' : IsUnit (W.map (f : A →+* B)).Δ) (D : LevelPData A) (hD : IsLevelPStructure W p D)
    (hD' : IsLevelPStructure (W.map (f : A →+* B)) p (D.map (f : A →+* B))),
    toFun (W.map (f : A →+* B)) hW' (D.map (f : A →+* B)) hD' = f (toFun W hW D hD)

  toFun_variableChange : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (C : VariableChange A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (C • W).Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure (C • W) p (D.variableChange C)),
    toFun (C • W) hW' (D.variableChange C) hD' = ((C.u⁻¹ ^ k : Aˣ) : A) * toFun W hW D hD

namespace KatzLevelPForm

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}

/--
@isnad1 id=injectiv.0h3v.s6.be5664ff11d2 from=translated src=- shape=eb2c050a vocab=6b73c8e4
-/
theorem toFun_injective : Function.Injective (toFun : KatzLevelPForm R p k → _) := by
  rintro ⟨F, _, _⟩ ⟨G, _, _⟩ h
  congr

/--
@isnad1 id=eq.1h5v.s6.518b710b587a from=translated src=- shape=004f005f vocab=3368643c
-/
@[ext]
theorem ext {F G : KatzLevelPForm R p k}
    (h : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
      (D : LevelPData A) (hD : IsLevelPStructure W p D), F.toFun W hW D hD = G.toFun W hW D hD) :
    F = G :=
  toFun_injective (by funext A _ _ W hW D hD; exact h W hW D hD)

instance : Zero (KatzLevelPForm R p k) :=
  ⟨{ toFun := fun _ _ _ _ _ _ _ => 0
     map_toFun := by intros; simp
     toFun_variableChange := by intros; simp }⟩

instance : Add (KatzLevelPForm R p k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW D hD => F.toFun W hW D hD + G.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_add, F.map_toFun f W hW hW' D hD hD', G.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD',
          G.toFun_variableChange C W hW hW' D hD hD', mul_add] }⟩

instance : Neg (KatzLevelPForm R p k) :=
  ⟨fun F =>
    { toFun := fun _ _ _ W hW D hD => -F.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_neg, F.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD', mul_neg] }⟩

instance : Sub (KatzLevelPForm R p k) :=
  ⟨fun F G =>
    { toFun := fun _ _ _ W hW D hD => F.toFun W hW D hD - G.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_sub, F.map_toFun f W hW hW' D hD hD', G.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD',
          G.toFun_variableChange C W hW hW' D hD hD', mul_sub] }⟩

instance : SMul R (KatzLevelPForm R p k) :=
  ⟨fun c F =>
    { toFun := fun _ _ _ W hW D hD => c • F.toFun W hW D hD
      map_toFun := by
        intro A B _ _ _ _ f W hW hW' D hD hD'
        rw [map_smul, F.map_toFun f W hW hW' D hD hD']
      toFun_variableChange := by
        intro A _ _ C W hW hW' D hD hD'
        rw [F.toFun_variableChange C W hW hW' D hD hD', mul_smul_comm] }⟩

section simp_lemmas

variable {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
  (D : LevelPData A) (hD : IsLevelPStructure W p D)

/--
@isnad1 id=eq.2h6v.s6.1b8e7835c612 from=translated src=- shape=446ef6b3 vocab=3368643c
-/
@[simp] theorem zero_toFun : (0 : KatzLevelPForm R p k).toFun W hW D hD = 0 := rfl

/--
@isnad1 id=eq.2h8v.s7.d6dc1e25c798 from=translated src=- shape=1a7bcc2a vocab=84b2f078
-/
@[simp] theorem add_toFun (F G : KatzLevelPForm R p k) :
    (F + G).toFun W hW D hD = F.toFun W hW D hD + G.toFun W hW D hD := rfl

/--
@isnad1 id=eq.2h7v.s6.71bc446a298e from=translated src=- shape=a089471d vocab=7a5b0da1
-/
@[simp] theorem neg_toFun (F : KatzLevelPForm R p k) :
    (-F).toFun W hW D hD = -F.toFun W hW D hD := rfl

/--
@isnad1 id=eq.2h8v.s7.6a127b67c705 from=translated src=- shape=1a7bcc2a vocab=c077a24a
-/
@[simp] theorem sub_toFun (F G : KatzLevelPForm R p k) :
    (F - G).toFun W hW D hD = F.toFun W hW D hD - G.toFun W hW D hD := rfl

/--
@isnad1 id=eq.2h8v.s7.46a14f95524c from=translated src=- shape=7938de22 vocab=2745f845
-/
@[simp] theorem smul_toFun (c : R) (F : KatzLevelPForm R p k) :
    (c • F).toFun W hW D hD = c • F.toFun W hW D hD := rfl

end simp_lemmas

instance : AddCommGroup (KatzLevelPForm R p k) where
  add_assoc F G H := by ext; simp [add_assoc]
  zero_add F := by ext; simp
  add_zero F := by ext; simp
  add_comm F G := by ext; simp [add_comm]
  neg_add_cancel F := by ext; simp
  sub_eq_add_neg F G := by ext; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (KatzLevelPForm R p k) where
  one_smul F := by ext; simp
  mul_smul a b F := by ext; simp [mul_smul]
  smul_zero a := by ext; simp
  smul_add a F G := by ext; simp
  add_smul a b F := by ext; simp [add_smul]
  zero_smul F := by ext; simp

def mul (F : KatzLevelPForm R p k) (G : KatzLevelPForm R p l) : KatzLevelPForm R p (k + l) where
  toFun _ _ _ W hW D hD := F.toFun W hW D hD * G.toFun W hW D hD
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    rw [map_mul, F.map_toFun f W hW hW' D hD hD', G.map_toFun f W hW hW' D hD hD']
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    rw [F.toFun_variableChange C W hW hW' D hD hD', G.toFun_variableChange C W hW hW' D hD hD',
      zpow_add, Units.val_mul]
    ring

/--
@isnad1 id=eq.2h9v.s7.b2fb7ad85a18 from=translated src=- shape=12d9edfd vocab=206f02f1
-/
@[simp] theorem mul_toFun (F : KatzLevelPForm R p k) (G : KatzLevelPForm R p l) {A : Type u}
    [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) :
    (F.mul G).toFun W hW D hD = F.toFun W hW D hD * G.toFun W hW D hD := rfl

def swap (F : KatzLevelPForm R p k) : KatzLevelPForm R p k where
  toFun _ _ _ W hW D hD := F.toFun W hW D.swap hD.swap
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    exact F.map_toFun f W hW hW' D.swap hD.swap hD'.swap
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    exact F.toFun_variableChange C W hW hW' D.swap hD.swap hD'.swap

/--
@isnad1 id=eq.2h7v.s6.149c636e5e78 from=translated src=- shape=f4eb7013 vocab=c034f566
-/
@[simp] theorem swap_toFun (F : KatzLevelPForm R p k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) :
    F.swap.toFun W hW D hD = F.toFun W hW D.swap hD.swap := rfl

/--
@isnad1 id=eq.0h4v.s5.6637e1aee41f from=translated src=- shape=3d4da7cc vocab=feac7e68
-/
@[simp] theorem swap_swap (F : KatzLevelPForm R p k) : F.swap.swap = F := rfl

/--
@isnad1 id=eq.0h3v.s5.4a912d2bd7c0 from=translated src=- shape=a758dd9a vocab=feac7e68
-/
@[simp] theorem swap_zero : (0 : KatzLevelPForm R p k).swap = 0 := rfl

/--
@isnad1 id=eq.0h5v.s6.0e29bfa325ca from=translated src=- shape=4d508b42 vocab=04c29d65
-/
@[simp] theorem swap_add (F G : KatzLevelPForm R p k) : (F + G).swap = F.swap + G.swap := rfl

/--
@isnad1 id=eq.0h4v.s5.34f828849308 from=translated src=- shape=c7447093 vocab=43f3a2b0
-/
@[simp] theorem swap_neg (F : KatzLevelPForm R p k) : (-F).swap = -F.swap := rfl

/--
@isnad1 id=eq.0h5v.s6.8ca96bae37b1 from=translated src=- shape=4d508b42 vocab=11e23043
-/
@[simp] theorem swap_sub (F G : KatzLevelPForm R p k) : (F - G).swap = F.swap - G.swap := rfl

/--
@isnad1 id=eq.0h5v.s6.11765047d448 from=translated src=- shape=ee755ed0 vocab=322aad6a
-/
@[simp] theorem swap_smul (c : R) (F : KatzLevelPForm R p k) : (c • F).swap = c • F.swap := rfl

def DependsOnlyOnSndLine (F : KatzLevelPForm R p k) : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D D' : LevelPData A) (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W p D'),
    InLine W p D.xQ D'.xQ → F.toFun W hW D' hD' = F.toFun W hW D hD

def DependsOnlyOnLines (F : KatzLevelPForm R p k) : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D D' : LevelPData A) (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W p D'),
    InLine W p D.xP D'.xP → InLine W p D.xQ D'.xQ → F.toFun W hW D' hD' = F.toFun W hW D hD

def SwapInvariant (F : KatzLevelPForm R p k) : Prop :=
  ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D),
    F.toFun W hW D.swap hD.swap = F.toFun W hW D hD

/--
@isnad1 id=dependso.0h3v.s5.f22d567be29f from=translated src=- shape=11e8f5be vocab=0c4ed37b
-/
theorem DependsOnlyOnSndLine.zero : (0 : KatzLevelPForm R p k).DependsOnlyOnSndLine :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl

/--
@isnad1 id=dependso.2h5v.s6.95209d248c4a from=translated src=- shape=9df9deff vocab=0d96648a
-/
theorem DependsOnlyOnSndLine.add {F G : KatzLevelPForm R p k} (hF : F.DependsOnlyOnSndLine)
    (hG : G.DependsOnlyOnSndLine) : (F + G).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [add_toFun, hF W hW D D' hD hD' hQ, hG W hW D D' hD hD' hQ]

/--
@isnad1 id=dependso.1h4v.s5.eefebdfc4965 from=translated src=- shape=509b9873 vocab=22fdd376
-/
theorem DependsOnlyOnSndLine.neg {F : KatzLevelPForm R p k} (hF : F.DependsOnlyOnSndLine) :
    (-F).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [neg_toFun, hF W hW D D' hD hD' hQ]

/--
@isnad1 id=dependso.1h5v.s5.0095eedb06c1 from=translated src=- shape=d346e4cd vocab=cf7bb487
-/
theorem DependsOnlyOnSndLine.smul (c : R) {F : KatzLevelPForm R p k}
    (hF : F.DependsOnlyOnSndLine) : (c • F).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [smul_toFun, hF W hW D D' hD hD' hQ]

/--
@isnad1 id=dependso.2h6v.s5.ae0a3d4a6b97 from=translated src=- shape=f4ded5dc vocab=730843d4
-/
theorem DependsOnlyOnSndLine.mul {F : KatzLevelPForm R p k} {G : KatzLevelPForm R p l}
    (hF : F.DependsOnlyOnSndLine) (hG : G.DependsOnlyOnSndLine) :
    (F.mul G).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [mul_toFun, hF W hW D D' hD hD' hQ, hG W hW D D' hD hD' hQ]

end KatzLevelPForm

structure KatzGamma0Form (R : Type u) [CommRing R] (p : ℕ) (k : ℤ) : Type (u + 1)
    extends KatzLevelPForm R p k where

  dependsOnlyOnSndLine : toKatzLevelPForm.DependsOnlyOnSndLine

namespace KatzGamma0Form

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}

/--
@isnad1 id=injectiv.0h3v.s4.f953c60fed1d from=translated src=- shape=53affa7e vocab=f7844ef2
-/
theorem toKatzLevelPForm_injective :
    Function.Injective (toKatzLevelPForm : KatzGamma0Form R p k → KatzLevelPForm R p k) := by
  rintro ⟨F, _⟩ ⟨G, _⟩ h
  congr

/--
@isnad1 id=eq.1h5v.s5.48ab8e022f2c from=translated src=- shape=e4ae9f35 vocab=63f4ae4d
-/
@[ext]
theorem ext {F G : KatzGamma0Form R p k} (h : F.toKatzLevelPForm = G.toKatzLevelPForm) : F = G :=
  toKatzLevelPForm_injective h

instance : Zero (KatzGamma0Form R p k) := ⟨⟨0, KatzLevelPForm.DependsOnlyOnSndLine.zero⟩⟩

instance : Add (KatzGamma0Form R p k) :=
  ⟨fun F G => ⟨F.toKatzLevelPForm + G.toKatzLevelPForm,
    F.dependsOnlyOnSndLine.add G.dependsOnlyOnSndLine⟩⟩

instance : Neg (KatzGamma0Form R p k) :=
  ⟨fun F => ⟨-F.toKatzLevelPForm, F.dependsOnlyOnSndLine.neg⟩⟩

instance : Sub (KatzGamma0Form R p k) :=
  ⟨fun F G => ⟨F.toKatzLevelPForm - G.toKatzLevelPForm, by
    rw [sub_eq_add_neg]; exact F.dependsOnlyOnSndLine.add G.dependsOnlyOnSndLine.neg⟩⟩

instance : SMul R (KatzGamma0Form R p k) :=
  ⟨fun c F => ⟨c • F.toKatzLevelPForm, F.dependsOnlyOnSndLine.smul c⟩⟩

/--
@isnad1 id=eq.0h3v.s5.eb44592de474 from=translated src=- shape=cdcf4edc vocab=63f4ae4d
-/
@[simp] theorem toKatzLevelPForm_zero : (0 : KatzGamma0Form R p k).toKatzLevelPForm = 0 := rfl
/--
@isnad1 id=eq.0h5v.s6.52a1606aa49c from=translated src=- shape=f31c8744 vocab=13ac8617
-/
@[simp] theorem toKatzLevelPForm_add (F G : KatzGamma0Form R p k) :
    (F + G).toKatzLevelPForm = F.toKatzLevelPForm + G.toKatzLevelPForm := rfl
/--
@isnad1 id=eq.0h4v.s5.0b34aeb22580 from=translated src=- shape=200891e2 vocab=81a3713c
-/
@[simp] theorem toKatzLevelPForm_neg (F : KatzGamma0Form R p k) :
    (-F).toKatzLevelPForm = -F.toKatzLevelPForm := rfl
/--
@isnad1 id=eq.0h5v.s6.e1c02046d233 from=translated src=- shape=f31c8744 vocab=0ed4558f
-/
@[simp] theorem toKatzLevelPForm_sub (F G : KatzGamma0Form R p k) :
    (F - G).toKatzLevelPForm = F.toKatzLevelPForm - G.toKatzLevelPForm := rfl
/--
@isnad1 id=eq.0h5v.s6.b488b10dc7a4 from=translated src=- shape=b784130a vocab=59d3ad38
-/
@[simp] theorem toKatzLevelPForm_smul (c : R) (F : KatzGamma0Form R p k) :
    (c • F).toKatzLevelPForm = c • F.toKatzLevelPForm := rfl

instance : AddCommGroup (KatzGamma0Form R p k) where
  add_assoc F G H := by ext1; simp [add_assoc]
  zero_add F := by ext1; simp
  add_zero F := by ext1; simp
  add_comm F G := by ext1; simp [add_comm]
  neg_add_cancel F := by ext1; simp
  sub_eq_add_neg F G := by ext1; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (KatzGamma0Form R p k) where
  one_smul F := by ext1; simp
  mul_smul a b F := by ext1; simp [mul_smul]
  smul_zero a := by ext1; simp
  smul_add a F G := by ext1; simp
  add_smul a b F := by ext1; simp [add_smul]
  zero_smul F := by ext1; simp

def mul (F : KatzGamma0Form R p k) (G : KatzGamma0Form R p l) : KatzGamma0Form R p (k + l) :=
  ⟨F.toKatzLevelPForm.mul G.toKatzLevelPForm, F.dependsOnlyOnSndLine.mul G.dependsOnlyOnSndLine⟩

/--
@isnad1 id=eq.0h6v.s6.497cff95bea5 from=translated src=- shape=970537ea vocab=56ed91b0
-/
@[simp] theorem toKatzLevelPForm_mul (F : KatzGamma0Form R p k) (G : KatzGamma0Form R p l) :
    (F.mul G).toKatzLevelPForm = F.toKatzLevelPForm.mul G.toKatzLevelPForm := rfl

end KatzGamma0Form

end ModularCurve

namespace KatzModularForm

variable {R : Type u} [CommRing R] {k : ℤ}

def pullbackLevelP (g : KatzModularForm R k) (p : ℕ) : ModularCurve.KatzLevelPForm R p k where
  toFun _ _ _ W hW _ _ := g.toFun W hW
  map_toFun := by
    intro A B _ _ _ _ f W hW hW' D hD hD'
    exact g.map_toFun f W hW hW'
  toFun_variableChange := by
    intro A _ _ C W hW hW' D hD hD'
    exact g.toFun_variableChange C W hW hW'

/--
@isnad1 id=eq.2h7v.s6.075103baf2e9 from=translated src=- shape=9d01f404 vocab=c1c37b33
-/
@[simp] theorem pullbackLevelP_toFun (g : KatzModularForm R k) (p : ℕ) {A : Type u} [CommRing A]
    [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : ModularCurve.LevelPData A)
    (hD : ModularCurve.IsLevelPStructure W p D) :
    (g.pullbackLevelP p).toFun W hW D hD = g.toFun W hW := rfl

/--
@isnad1 id=dependso.0h4v.s4.1cfe5ea6b12b from=translated src=- shape=60e740eb vocab=32a1b68d
-/
theorem dependsOnlyOnSndLine_pullbackLevelP (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackLevelP p).DependsOnlyOnSndLine :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl

/--
@isnad1 id=eq.0h4v.s5.5c469fc399c5 from=translated src=- shape=a0aa5813 vocab=8d58e6a0
-/
@[simp] theorem swap_pullbackLevelP (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackLevelP p).swap = g.pullbackLevelP p := rfl

def pullbackGamma0 (g : KatzModularForm R k) (p : ℕ) : ModularCurve.KatzGamma0Form R p k :=
  ⟨g.pullbackLevelP p, g.dependsOnlyOnSndLine_pullbackLevelP p⟩

/--
@isnad1 id=eq.0h4v.s5.2dcb637fb967 from=translated src=- shape=a0aa5813 vocab=9ef07107
-/
@[simp] theorem pullbackGamma0_toKatzLevelPForm (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackGamma0 p).toKatzLevelPForm = g.pullbackLevelP p := rfl

/--
@isnad1 id=eq.0h3v.s5.6a19be7b79be from=translated src=- shape=a574a441 vocab=ebeadec1
-/
@[simp] theorem pullbackLevelP_zero (p : ℕ) : (0 : KatzModularForm R k).pullbackLevelP p = 0 :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.1df1b550dc7b from=translated src=- shape=53d26a23 vocab=a0fde4ec
-/
@[simp] theorem pullbackLevelP_add (g h : KatzModularForm R k) (p : ℕ) :
    (g + h).pullbackLevelP p = g.pullbackLevelP p + h.pullbackLevelP p := rfl

/--
@isnad1 id=eq.0h5v.s6.711aa20b78c2 from=translated src=- shape=6f9990cf vocab=3bb24e47
-/
@[simp] theorem pullbackLevelP_smul (c : R) (g : KatzModularForm R k) (p : ℕ) :
    (c • g).pullbackLevelP p = c • g.pullbackLevelP p := rfl

end KatzModularForm

namespace ModularCurve.LevelP

variable (p : ℕ)

def borel : Subgroup (GL (Fin 2) (ZMod p)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh, zero_mul, mul_zero, add_zero]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_two]
    simp [hg]

def splitTorus : Subgroup (GL (Fin 2) (ZMod p)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg.1, hh.1, hg.2, hh.2]
    simp
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.adjugate_fin_two]
    simp [hg.1, hg.2]

def unipotentU : GL (Fin 2) (ZMod p) :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num⟩

def swapW : GL (Fin 2) (ZMod p) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num⟩

/--
@isnad1 id=eq.0h1v.s8.d101bca0b42e from=translated src=- shape=e93126fb vocab=88d65b9a
-/
@[simp] theorem coe_unipotentU :
    (unipotentU p : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 1; 0, 1] := rfl

/--
@isnad1 id=eq.0h1v.s8.dc5dbcd6dab2 from=translated src=- shape=e93126fb vocab=d6129efb
-/
@[simp] theorem coe_swapW : (swapW p : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![0, 1; 1, 0] := rfl

end ModularCurve.LevelP

end
