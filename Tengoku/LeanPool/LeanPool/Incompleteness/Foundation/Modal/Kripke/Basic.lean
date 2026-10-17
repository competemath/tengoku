/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Axioms
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Substitution

/-! # Basic -/

@[expose] public section
open scoped LO.Axioms LO.Dia LO.Entailment LO.Modal LO.Modal.Formula


namespace LO
namespace Modal

open Entailment

namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
structure Frame where
  /-- Imported declaration from the Incompleteness formalization. -/
  World : Type
  /-- Imported declaration from the Incompleteness formalization. -/
  Rel : Rel World World
  [world_nonempty : Nonempty World]

instance : CoeSort Frame (Type) := ⟨Frame.World⟩
instance : CoeFun Frame (fun F => F.World → F.World → Prop) := ⟨Frame.Rel⟩
instance {F : Frame} : Nonempty F.World := F.world_nonempty

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺ " => Frame.Rel'

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Kripke.Frame.RelItr' {F : Frame} (n : ℕ) := F.Rel.iterate n
/-- Imported declaration from the Incompleteness formalization. -/
notation x:45 " ≺^[" n "] " y:46 => Frame.RelItr' n x y

/-- Imported declaration from the Incompleteness formalization. -/
abbrev FrameClass := Set Frame

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FrameClass.nonempty (C : FrameClass) := ∃ F, F ∈ C

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Valuation (F : Frame) := F.World → ℕ → Prop

/-- Imported declaration from the Incompleteness formalization. -/
structure Model extends Frame where
  /-- Imported declaration from the Incompleteness formalization. -/
  Val : Valuation toFrame
instance : CoeFun (Model) (fun M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

end Kripke

namespace Formula
namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
def Satisfies (M : Kripke.Model) (x : M.World) : Formula ℕ → Prop
  | atom a  => M x a
  | ⊥  => False
  | φ ==> ψ => (Satisfies M x φ) ==> (Satisfies M x ψ)
  | □φ   => ∀ y, x ≺ y → (Satisfies M y φ)

namespace Satisfies

protected instance semantics {M : Kripke.Model} :
    Semantics (Formula ℕ) (M.World) :=
  ⟨fun x ↦ Formula.Kripke.Satisfies M x⟩

variable {M : Kripke.Model} {x : M.World} {φ ψ : Formula ℕ}

/--
@isnad1 id=iff.0h3v.s4.2f6c0b81ecaa from=translated src=- shape=b454fa63 vocab=4e9cace7
-/
@[simp 1100] protected lemma iff_models : x ⊧ φ ↔ Kripke.Satisfies M x φ := iff_of_eq rfl

/--
@isnad1 id=iff.0h3v.s4.391d000ee6ba from=translated src=- shape=09604ee0 vocab=e40ffcca
-/
@[simp 1100] lemma atom_def : Kripke.Satisfies M x (atom a) ↔ M x a := by simp [Satisfies];

/--
@isnad1 id=not.0h2v.s4.9240ece9cc77 from=translated src=- shape=b9337ad7 vocab=7cc041ec
-/
protected lemma bot_def : ¬x ⊧ ⊥ := by simp [Satisfies];

/--
@isnad1 id=iff.0h4v.s5.3ade46619edc from=translated src=- shape=a7b1f95c vocab=e2126176
-/
protected lemma imp_def : x ⊧ φ ==> ψ ↔ (x ⊧ φ) → (x ⊧ ψ) := by tauto;

/--
@isnad1 id=iff.0h4v.s5.8a3670ffec96 from=translated src=- shape=416a10d0 vocab=e2126176
-/
protected lemma imp_def₂ : x ⊧ φ ==> ψ ↔ ¬x ⊧ φ ∨ x ⊧ ψ := by tauto;

/--
@isnad1 id=iff.0h4v.s5.dce6bdd9c2ab from=translated src=- shape=046850b5 vocab=b5b909fd
-/
protected lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies]; tauto;

/--
@isnad1 id=iff.0h4v.s5.fe8e24f49842 from=translated src=- shape=046850b5 vocab=1f74041a
-/
protected lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];

/--
@isnad1 id=iff.0h3v.s5.b960937bb045 from=translated src=- shape=ac8f78eb vocab=6b182f54
-/
protected lemma not_def : x ⊧ ∼φ ↔ ¬(x ⊧ φ) := by simp [Satisfies];

/--
@isnad1 id=realize.0h2v.s4.a4aefad06b09 from=translated src=- shape=7d3c1e9a vocab=12929b06
-/
protected lemma top_def : x ⊧ ⊤ := by simp [Satisfies];

/--
@isnad1 id=iff.0h3v.s5.f1f0490022aa from=translated src=- shape=2013b155 vocab=58365299
-/
@[simp 1100] protected lemma box_def :
    Kripke.Satisfies M x (□φ) ↔ ∀ y, x ≺ y → y ⊧ φ := by
  simp [Satisfies];

/--
@isnad1 id=iff.0h3v.s5.13a7b9db86b2 from=translated src=- shape=5305f252 vocab=8be1b75c
-/
@[simp 1100] protected lemma dia_def :
    Kripke.Satisfies M x (◇φ) ↔ ∃ y, x ≺ y ∧ y ⊧ φ := by
  simp [Satisfies];

/--
@isnad1 id=iff.0h4v.s5.b32f36832471 from=translated src=- shape=7c794631 vocab=35c6f5c1
-/
lemma iff_def : x ⊧ φ <=> ψ ↔ (x ⊧ φ ↔ x ⊧ ψ) := by
  simp [Satisfies]
  tauto

/--
@isnad1 id=iff.0h3v.s5.6aa4be29c067 from=translated src=- shape=2f2cef1c vocab=e1e97d5d
-/
@[simp 1100] lemma negneg_def : Kripke.Satisfies M x (∼∼φ) ↔ x ⊧ φ := by
  classical
  simp [Satisfies]

/--
@isnad1 id=iff.0h4v.s5.3a3aa49c8a0b from=translated src=- shape=2d20ecb4 vocab=208ee757
-/
lemma multibox_def : x ⊧ □^[n]φ ↔ ∀ {y}, x ≺^[n] y → y ⊧ φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    · rintro h y ⟨z, Rxz, Rzy⟩;
      replace h : ∀ y, x ≺ y → y ⊧ □^[n]φ := Satisfies.box_def.mp <| by simpa using h;
      exact (ih.mp <| h _ Rxz) Rzy;
    · suffices (∀ {y z}, x ≺ z → z ≺^[n] y → Satisfies M y φ) → x ⊧ (□□^[n]φ) by simpa;
      intro h y Rxy;
      apply ih.mpr;
      intro z Ryz;
      exact h Rxy Ryz;

/--
@isnad1 id=iff.0h4v.s5.09a042518283 from=translated src=- shape=7f16d1f5 vocab=9f57b47b
-/
lemma multidia_def : x ⊧ ◇^[n]φ ↔ ∃ y, x ≺^[n] y ∧ y ⊧ φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    · intro h;
      replace h : x ⊧ (◇◇^[n]φ) := by simpa using h;
      obtain ⟨y, Rxy, hv⟩ := Satisfies.dia_def.mp h;
      obtain ⟨x, Ryx, hx⟩ := ih.mp hv;
      exact ⟨x, ⟨y, Rxy, Ryx⟩, hx⟩;
    · rintro ⟨y, ⟨z, Rxz, Rzy⟩, hy⟩;
      suffices x ⊧ ◇◇^[n]φ by simpa;
      exact Satisfies.dia_def.mpr ⟨z, Rxz, ih.mpr ⟨y, Rzy, hy⟩⟩;

/--
@isnad1 id=realize.2h5v.s6.99b988ddfbc3 from=translated src=- shape=aceb5410 vocab=e2126176
-/
lemma trans (hpq : x ⊧ φ ==> ψ) (hqr : x ⊧ ψ ==> χ) : x ⊧ φ ==> χ :=
  Satisfies.imp_def.mpr fun hφ => Satisfies.imp_def.mp hqr (Satisfies.imp_def.mp hpq hφ)

/--
@isnad1 id=realize.2h4v.s5.1136e27fb894 from=translated src=- shape=86846f88 vocab=e2126176
-/
lemma mdp (hpq : x ⊧ φ ==> ψ) (hp : x ⊧ φ) : x ⊧ ψ := Satisfies.imp_def.mp hpq hp

/--
@isnad1 id=iff.0h3v.s6.1ad200687d5d from=translated src=- shape=99938af2 vocab=8fa47ff8
-/
lemma diaDual : x ⊧ ◇φ ↔ x ⊧ ∼□(∼φ) := by simp [Satisfies];

/--
@isnad1 id=iff.0h3v.s6.3baf49ef8c4e from=translated src=- shape=99938af2 vocab=8fa47ff8
-/
lemma box_dual : x ⊧ □φ ↔ x ⊧ ∼◇(∼φ) := by simp [Satisfies];

/--
@isnad1 id=iff.0h4v.s6.7457cb48ebb3 from=translated src=- shape=32141556 vocab=fbb7a8f4
-/
lemma not_imp : ¬(x ⊧ φ ==> ψ) ↔ x ⊧ φ ⋏ ∼ψ := by simp [Satisfies];

/--
@isnad1 id=iff.0h5v.s5.198588016252 from=translated src=- shape=4c7c0efc vocab=ba8a958c
-/
lemma iff_subst_self {x : F.World} (s) :
  letI U : Kripke.Valuation F := fun w a => Satisfies ⟨F, V⟩ w ((.atom a)⟦s⟧);
  Satisfies ⟨F, U⟩ x φ ↔ Satisfies ⟨F, V⟩ x (φ⟦s⟧) := by
  induction φ using Formula.rec' generalizing x with
  | hatom a => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | hbox φ ih =>
    constructor;
    · exact fun hbφ y Rxy => ih.mp <| hbφ y Rxy;
    · exact fun hbφ y Rxy => ih.mpr <| hbφ y Rxy;
  | himp φ ψ ihφ ihψ =>
    constructor;
    · exact fun hφψ hφ => ihψ.mp <| hφψ <| ihφ.mpr hφ;
    · exact fun hφψs hφ => ihψ.mpr <| hφψs <| ihφ.mp hφ;

end Satisfies

/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnModel (M : Kripke.Model) (φ : Formula ℕ) := ∀ x : M.World, x ⊧ φ

namespace ValidOnModel

instance semantics : Semantics (Formula ℕ) (Kripke.Model) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

/--
@isnad1 id=iff.0h2v.s4.bebc2258979c from=translated src=- shape=84e0b463 vocab=ca1eae4d
-/
@[simp] protected lemma iff_models {M : Kripke.Model} :
    M ⊧ f ↔ Kripke.ValidOnModel M f :=
  iff_of_eq rfl

variable {M : Kripke.Model} {φ ψ χ : Formula ℕ}

/--
@isnad1 id=not.0h1v.s4.93b69af22475 from=translated src=- shape=6fb7f272 vocab=3e1842d1
-/
protected lemma bot_def : ¬M ⊧ ⊥ := by
  intro h
  obtain ⟨x⟩ := M.world_nonempty
  exact Satisfies.bot_def (h x)

/--
@isnad1 id=realize.0h1v.s4.f29c9105de66 from=translated src=- shape=75b9ccd3 vocab=25d84cfe
-/
protected lemma top_def : M ⊧ ⊤ := by
  intro x
  exact Satisfies.top_def

instance : Semantics.Bot (Kripke.Model) where
  realize_bot := fun _ => ValidOnModel.bot_def;

instance : Semantics.Top (Kripke.Model) where
  realize_top := fun _ => ValidOnModel.top_def;

/--
@isnad1 id=iff.0h2v.s5.66d72f077acd from=translated src=- shape=2c9fae5f vocab=4b60b3ee
-/
lemma iff_not_exists_world {M : Kripke.Model} : (¬M ⊧ φ) ↔ (∃ x : M.World, ¬x ⊧ φ) := by
  apply not_iff_not.mp;
  push Not;
  tauto;

alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_exists_world

/--
@isnad1 id=realize.2h3v.s5.0e504caa898a from=translated src=- shape=7af8841f vocab=2f9f8c64
-/
protected lemma mdp (hpq : M ⊧ φ ==> ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro x;
  exact (Satisfies.imp_def.mp <| hpq x) (hp x);

/--
@isnad1 id=realize.1h2v.s4.26a2125e2031 from=translated src=- shape=3f6f82cd vocab=8c9eb9b6
-/
protected lemma nec (h : M ⊧ φ) : M ⊧ □φ := by
  intro x y _;
  exact h y;

/--
@isnad1 id=realize.0h3v.s4.99fe7de5204b from=translated src=- shape=0184ee8a vocab=523fad42
-/
protected lemma imply₁ : M ⊧ (Axioms.Imply₁ φ ψ) := by simp [ValidOnModel]; tauto;

/--
@isnad1 id=realize.0h4v.s4.e732bc093355 from=translated src=- shape=dd1fe334 vocab=ef2ed6e1
-/
protected lemma imply₂ : M ⊧ (Axioms.Imply₂ φ ψ χ) := by simp [ValidOnModel]; tauto;

/--
@isnad1 id=realize.0h3v.s4.e24d9dd08c21 from=translated src=- shape=0184ee8a vocab=dae9093f
-/
protected lemma elimContra :
    M ⊧ (Axioms.ElimContra φ ψ) := by
  simp [ValidOnModel, Satisfies]; tauto;

/--
@isnad1 id=realize.0h3v.s4.e9d55b0d3895 from=translated src=- shape=0184ee8a vocab=9b080405
-/
protected lemma axiomK : M ⊧ (Axioms.K φ ψ)  := by
  intro V;
  apply Satisfies.imp_def.mpr;
  intro hpq;
  apply Satisfies.imp_def.mpr;
  intro hp x Rxy;
  replace hpq := Satisfies.imp_def.mp <| hpq x Rxy;
  simp_all

end ValidOnModel

/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFrame (F : Kripke.Frame) (φ : Formula ℕ) := ∀ V, (⟨F, V⟩ : Kripke.Model) ⊧ φ

namespace ValidOnFrame

instance semantics : Semantics (Formula ℕ) (Kripke.Frame) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Kripke.Frame}

/--
@isnad1 id=iff.0h2v.s4.189e27db4745 from=translated src=- shape=d962512f vocab=4f8d7fbd
-/
@[simp] protected lemma models_iff : F ⊧ φ ↔ Kripke.ValidOnFrame F φ := iff_of_eq rfl

/--
@isnad1 id=iff.0h2v.s5.add40b5c9abf from=translated src=- shape=c6fec093 vocab=e813a4ad
-/
lemma models_set_iff : F ⊧* Φ ↔ ∀ φ ∈ Φ, F ⊧ φ := by simp [Semantics.realizeSet_iff];

/--
@isnad1 id=realize.0h1v.s4.ca24f54b41a8 from=translated src=- shape=75b9ccd3 vocab=ceeef34d
-/
protected lemma top_def : F ⊧ ⊤ := by simp [ValidOnFrame];

/--
@isnad1 id=not.0h1v.s4.c449100293fc from=translated src=- shape=6fb7f272 vocab=9f8d0d5a
-/
protected lemma bot_def : ¬F ⊧ ⊥ := by simp [ValidOnFrame];

instance : Semantics.Top (Kripke.Frame) where
  realize_top _ := ValidOnFrame.top_def;

instance : Semantics.Bot (Kripke.Frame) where
  realize_bot _ := ValidOnFrame.bot_def

/--
@isnad1 id=iff.0h2v.s4.a1be011a36d8 from=translated src=- shape=6eaf6ad6 vocab=ae671711
-/
lemma iff_not_exists_valuation : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F, ¬(⟨F, V⟩ :
    Kripke.Model) ⊧ φ) := by
  simp [ValidOnFrame];

alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation

/--
@isnad1 id=iff.0h2v.s5.255804780c8d from=translated src=- shape=a481eb48 vocab=5a7b1010
-/
lemma iff_not_exists_valuation_world : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F, ∃ x : (⟨F, V⟩ :
    Kripke.Model).World, ¬Satisfies _ x φ) := by
  simp [ValidOnFrame, ValidOnModel, Semantics.Realize];

alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ :=
  iff_not_exists_valuation_world

/--
@isnad1 id=iff.0h2v.s5.48c52307f3de from=translated src=- shape=83dd715c vocab=6591d5c3
-/
lemma iff_not_exists_model_world :  (¬F ⊧ φ) ↔ (∃ M : Kripke.Model, ∃ x :
    M.World, M.toFrame = F ∧ ¬(x ⊧ φ)) := by
  constructor;
  · intro h;
    obtain ⟨V, x, h⟩ := iff_not_exists_valuation_world.mp h;
    use ⟨F, V⟩, x;
    tauto;
  · rintro ⟨M, x, rfl, h⟩;
    exact iff_not_exists_valuation_world.mpr ⟨M.Val, x, h⟩;

alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world

/--
@isnad1 id=realize.2h3v.s5.7ae1ddba833e from=translated src=- shape=7af8841f vocab=3b376ad0
-/
protected lemma mdp (hpq : F ⊧ φ ==> ψ) (hp : F ⊧ φ) : F ⊧ ψ := by
  intro V x;
  exact (hpq V x) (hp V x);

/--
@isnad1 id=realize.1h2v.s4.33db5fcb2bef from=translated src=- shape=3f6f82cd vocab=805aa33c
-/
protected lemma nec (h : F ⊧ φ) : F ⊧ □φ := by
  intro V x y _;
  exact h V y;

/--
@isnad1 id=realize.1h3v.s4.fd8653cff451 from=translated src=- shape=4b9ac5f1 vocab=652df5e3
-/
protected lemma subst (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  replace hC := iff_not_exists_valuation_world.mp hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  exact h (fun w a => Satisfies ⟨F, V⟩ w (atom a⟦s⟧)) x;

/--
@isnad1 id=realize.0h3v.s4.5d73530a2fe3 from=translated src=- shape=0184ee8a vocab=4ec766da
-/
protected lemma imply₁ :
    F ⊧ (Axioms.Imply₁ φ ψ) := by
  intro V; exact ValidOnModel.imply₁ (M := ⟨F, V⟩);

/--
@isnad1 id=realize.0h4v.s4.e080904b205a from=translated src=- shape=dd1fe334 vocab=55d15a2c
-/
protected lemma imply₂ :
    F ⊧ (Axioms.Imply₂ φ ψ χ) := by
  intro V; exact ValidOnModel.imply₂ (M := ⟨F, V⟩);

/--
@isnad1 id=realize.0h3v.s4.5445b383011b from=translated src=- shape=0184ee8a vocab=3d9ded41
-/
protected lemma elimContra :
    F ⊧ (Axioms.ElimContra φ ψ) := by
  intro V; exact ValidOnModel.elimContra (M := ⟨F, V⟩);

/--
@isnad1 id=realize.0h3v.s4.2936167e76e9 from=translated src=- shape=0184ee8a vocab=6d4a74d5
-/
protected lemma axiomK : F ⊧ (Axioms.K φ ψ) := by intro V; exact ValidOnModel.axiomK (M := ⟨F, V⟩);

end ValidOnFrame

/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFrameClass (C : Kripke.FrameClass) (φ : Formula ℕ) := ∀ {F}, F ∈ C → F ⊧ φ

namespace ValidOnFrameClass

protected instance semantics :
    Semantics (Formula ℕ) (Kripke.FrameClass) :=
  ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩

variable {C : Kripke.FrameClass}

/--
@isnad1 id=iff.0h2v.s4.2da53686ed92 from=translated src=- shape=d962512f vocab=4c937e09
-/
@[simp] protected lemma models_iff : C ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass C φ := iff_of_eq rfl

/--
@isnad1 id=realize.0h1v.s4.3a6241b51545 from=translated src=- shape=75b9ccd3 vocab=e66c3389
-/
protected lemma top_def : C ⊧ ⊤ := by simp [ValidOnFrameClass];

/--
@isnad1 id=not.1h1v.s4.b1b80342d7b8 from=translated src=- shape=4515b943 vocab=59174c30
-/
protected lemma bot_def (h : Set.Nonempty C) : ¬C ⊧ ⊥ := by simpa [ValidOnFrameClass];

/--
@isnad1 id=iff.0h2v.s5.c20e0b4c8dc5 from=translated src=- shape=26105338 vocab=0e2e2143
-/
lemma iff_not_exists_frame {C : Kripke.FrameClass} : (¬C ⊧ φ) ↔ (∃ F ∈ C, ¬F ⊧ φ) := by
  apply not_iff_not.mp;
  push Not;
  tauto;

alias ⟨exists_frame_of_not, not_of_exists_frame⟩ := iff_not_exists_frame

/--
@isnad1 id=iff.0h2v.s5.2c1cfd5803dd from=translated src=- shape=50aba44b vocab=b27ceaa3
-/
lemma iff_not_exists_model {C : Kripke.FrameClass} : (¬C ⊧ φ) ↔ (∃ M :
    Kripke.Model, M.toFrame ∈ C ∧ ¬M ⊧ φ) := by
  apply not_iff_not.mp;
  push Not;
  tauto;

alias ⟨exists_model_of_not, not_of_exists_model⟩ := iff_not_exists_model

/--
@isnad1 id=iff.0h2v.s5.25cceeb6c37e from=translated src=- shape=7f19b628 vocab=5054a97b
-/
lemma iff_not_exists_model_world {C : Kripke.FrameClass} : (¬C ⊧ φ) ↔ (∃ M : Kripke.Model, ∃ x :
    M.World, M.toFrame ∈ C ∧ ¬(x ⊧ φ)) := by
  apply not_iff_not.mp;
  push Not;
  tauto;

alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world

end ValidOnFrameClass

end Kripke
end Formula

namespace Kripke

namespace FrameClass

/-- Imported declaration from the Incompleteness formalization. -/
class DefinedBy (C : Kripke.FrameClass) (Γ : Set (Formula ℕ)) where
  defines : ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, F ⊧ φ)

/-- Imported declaration from the Incompleteness formalization. -/
class FiniteDefinedBy (C Γ) extends FrameClass.DefinedBy C Γ where
  finite : Set.Finite Γ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedByFormula (C : Kripke.FrameClass) (φ : Formula ℕ) := FrameClass.DefinedBy C {φ}

/--
@isnad1 id=definedb.1h2v.s4.d32a1d0e6d09 from=translated src=- shape=ab8af8f8 vocab=f5259544
-/
lemma definedByFormula_of_iff_mem_validate (h : ∀ F, F ∈ C ↔ F ⊧ φ) : DefinedByFormula C φ := by
  constructor;
  simpa;

/--
@isnad1 id=definedb.0h4v.s5.b0ee66a27b8c from=translated src=- shape=35291cc0 vocab=a7ed0b37
-/
instance definedBy_inter
  (C₁ Γ₁) [h₁ : DefinedBy C₁ Γ₁]
  (C₂ Γ₂) [h₂ : DefinedBy C₂ Γ₂]
  : DefinedBy (C₁ ∩ C₂) (Γ₁ ∪ Γ₂) := ⟨by
  rintro F;
  constructor
  · rintro ⟨hF₁, hF₂⟩;
    rintro φ (hφ₁ | hφ₂);
    · exact h₁.defines F |>.mp hF₁ _ hφ₁;
    · exact h₂.defines F |>.mp hF₂ _ hφ₂;
  · intro h;
    constructor;
    · apply h₁.defines F |>.mpr;
      simp_all
    · apply h₂.defines F |>.mpr;
      simp_all
⟩

/--
@isnad1 id=definedb.0h6v.s5.2667cf193531 from=translated src=- shape=7739e298 vocab=a7ed0b37
-/
lemma definedBy_triinter
  (C₁ Γ₁) [DefinedBy C₁ Γ₁]
  (C₂ Γ₂) [DefinedBy C₂ Γ₂]
  (C₃ Γ₃) [DefinedBy C₃ Γ₃]
  : DefinedBy (C₁ ∩ C₂ ∩ C₃) (Γ₁ ∪ Γ₂ ∪ Γ₃) := definedBy_inter (C₁ ∩ C₂) (Γ₁ ∪ Γ₂) C₃ Γ₃

/--
@isnad1 id=definedb.0h6v.s6.25ae7abc3ba8 from=translated src=- shape=ac31ad24 vocab=bbbbaeb2
-/
lemma definedByFormula_triinter
  (C₁ φ₁) [DefinedByFormula C₁ φ₁]
  (C₂ φ₂) [DefinedByFormula C₂ φ₂]
  (C₃ φ₃) [DefinedByFormula C₃ φ₃]
  : DefinedBy (C₁ ∩ C₂ ∩ C₃) {φ₁, φ₂, φ₃} := by
  simpa [show ({φ₁, φ₂, φ₃} : Set (Formula ℕ)) = {φ₁} ∪ {φ₂} ∪ {φ₃} by aesop]
  using definedBy_triinter C₁ {φ₁} C₂ {φ₂} C₃ {φ₃}

/-- Imported declaration from the Incompleteness formalization. -/
class IsNonempty (C : Kripke.FrameClass) : Prop where
  nonempty : Nonempty C

end FrameClass

/-- Imported declaration from the Incompleteness formalization. -/
abbrev AllFrameClass : FrameClass := Set.univ

instance _root_.LO.Modal.Kripke.AllFrameClass.DefinedBy :
    AllFrameClass.DefinedByFormula (Axioms.K (.atom 0) (.atom 1)) :=
  FrameClass.definedByFormula_of_iff_mem_validate <| by
    simp only [Set.mem_univ, true_iff];
    intro F;
    exact Formula.Kripke.ValidOnFrame.axiomK;

namespace FrameClass

variable {C : Kripke.FrameClass}

/--
@isnad1 id=definedb.1h2v.s5.97891fd70dd0 from=translated src=- shape=86cd7cc9 vocab=c77f5441
-/
lemma definedBy_with_axiomK (defines : C.DefinedBy Γ) :
    DefinedBy C (insert (Axioms.K (.atom 0) (.atom 1)) Γ) := by
  convert definedBy_inter AllFrameClass {Axioms.K (.atom 0) (.atom 1)} C Γ <;>
    simp [AllFrameClass, Set.singleton_union];

end FrameClass

end Kripke

end Modal
end LO
