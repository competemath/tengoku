/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Vorspiel.BinaryRelations
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.IntProp.Substitution
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.Axioms
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.Semantics
public import Tengoku

/-! # Basic -/

@[expose] public section

namespace LO
namespace IntProp

namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
structure Frame where
  /-- Imported declaration from the Incompleteness formalization. -/
  World : Type
  [world_nonempty : Nonempty World]
  /-- Imported declaration from the Incompleteness formalization. -/
  Rel : Rel World World
  rel_refl : Std.Refl Rel
  rel_trans : IsTrans World Rel

instance : CoeSort Frame (Type) := ⟨Frame.World⟩
instance : CoeFun Frame (fun F => F.World → F.World → Prop) := ⟨Frame.Rel⟩
instance {F : Frame} : Nonempty F.World := F.world_nonempty
-- instance {F : Frame} : IsPartialOrder _ F.Rel := F.rel_po

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.IntProp.Kripke.Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ≺ " => Frame.Rel'

namespace Frame

variable {F : Frame} {x y z : F.World}

/--
@isnad1 id=rel.0h2v.s3.90a44f5b719f from=translated src=- shape=f3577ae2 vocab=2614c9a6
-/
@[refl, simp] lemma rel_refl' : x ≺ x := F.rel_refl.refl x

/--
@isnad1 id=rel.2h4v.s4.046b460e1cea from=translated src=- shape=de5dbc67 vocab=2614c9a6
-/
@[trans] lemma rel_trans' : x ≺ y → y ≺ z → x ≺ z :=
  F.rel_trans.trans x y z

end Frame

/-- Imported declaration from the Incompleteness formalization. -/
abbrev pointFrame : Frame where
  World := Unit
  Rel := fun _ _ => True
  rel_refl := ⟨fun _ => trivial⟩
  rel_trans := ⟨fun _ _ _ _ _ => trivial⟩

/-- Imported declaration from the Incompleteness formalization. -/
abbrev FrameClass := Set (Frame)

/-- Imported declaration from the Incompleteness formalization. -/
structure Valuation (F : Frame) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Val : F.World → ℕ → Prop
  hereditary : ∀ {w₁ w₂ : F.World}, (w₁ ≺ w₂) → ∀ {a}, (Val w₁ a) → (Val w₂ a)
instance {F : Frame} : CoeFun (Valuation F) (fun _ => F.World → ℕ → Prop) := ⟨Valuation.Val⟩

/-- Imported declaration from the Incompleteness formalization. -/
structure Model extends Frame where
  /-- Imported declaration from the Incompleteness formalization. -/
  Val : Valuation toFrame
instance : CoeFun (Model) (fun M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

end Kripke

open Kripke

open Formula

namespace Formula
namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
def Satisfies (M : Kripke.Model) (w : M.World) : Formula ℕ → Prop
  | atom a => M w a
  | ⊥      => False
  | φ ⋏ ψ  => Satisfies M w φ ∧ Satisfies M w ψ
  | φ ⋎ ψ  => Satisfies M w φ ∨ Satisfies M w ψ
  | φ ==> ψ => ∀ {w' : M.World}, (w ≺ w') → (Satisfies M w' φ → Satisfies M w' ψ)

namespace Satisfies

instance semantics (M : Kripke.Model) : Semantics (Formula ℕ) (M.World) :=
  ⟨fun w ↦ Formula.Kripke.Satisfies M w⟩

variable {M : Kripke.Model} {w w' : M.World} {a : ℕ} {φ ψ χ : Formula ℕ}

/--
@isnad1 id=iff.0h3v.s4.bb6b4b8a8dfa from=translated src=- shape=b454fa63 vocab=560c0b89
-/
@[simp 1100] protected lemma iff_models : w ⊧ φ ↔ Formula.Kripke.Satisfies M w φ := iff_of_eq rfl

/--
@isnad1 id=iff.0h3v.s4.5afcc5e85b51 from=translated src=- shape=37e49c1a vocab=f31c44d0
-/
@[simp 1100] lemma atom_def : Formula.Kripke.Satisfies M w (atom a) ↔ M w a := by simp [Satisfies];

/--
@isnad1 id=iff.0h2v.s4.3021112d09ff from=translated src=- shape=528287e4 vocab=c9aab742
-/
@[simp 1100] lemma top_def : Formula.Kripke.Satisfies M w ⊤ ↔ True := by simp [Satisfies];

/--
@isnad1 id=iff.0h2v.s4.360062571d94 from=translated src=- shape=528287e4 vocab=348e07ac
-/
@[simp 1100] lemma bot_def : Formula.Kripke.Satisfies M w ⊥ ↔ False := by simp [Satisfies];

/--
@isnad1 id=iff.0h4v.s5.22951051de32 from=translated src=- shape=46839bbf vocab=0f13bbbf
-/
@[simp 1100] lemma and_def :
    Formula.Kripke.Satisfies M w (φ ⋏ ψ) ↔ w ⊧ φ ∧ w ⊧ ψ := by
  simp [Satisfies];

/--
@isnad1 id=iff.0h4v.s5.cd3b3e592480 from=translated src=- shape=46839bbf vocab=5d052229
-/
@[simp 1100] lemma or_def :
    Formula.Kripke.Satisfies M w (φ ⋎ ψ) ↔ w ⊧ φ ∨ w ⊧ ψ := by
  simp [Satisfies];

/--
@isnad1 id=iff.0h4v.s5.697af2f9c10c from=translated src=- shape=19a23f6b vocab=04d0ff35
-/
@[simp 1100] lemma imp_def : Formula.Kripke.Satisfies M w (φ ==> ψ) ↔ ∀ {w' :
    M.World}, (w ≺ w') → (w' ⊧ φ → w' ⊧ ψ) := by
  simp [Satisfies, imp_iff_not_or];

/--
@isnad1 id=iff.0h3v.s5.168eb762706a from=translated src=- shape=0bef896d vocab=a56136ac
-/
@[simp 1100] lemma neg_def : Formula.Kripke.Satisfies M w (∼φ) ↔ ∀ {w' :
    M.World}, (w ≺ w') → ¬(w' ⊧ φ) := by
  simp [Satisfies];

/--
@isnad1 id=realize.2h4v.s5.f123e6d5f869 from=translated src=- shape=477a12b1 vocab=f89cc468
-/
lemma formula_hereditary
  (hw : w ≺ w') : w ⊧ φ → w' ⊧ φ := by
  induction φ using Formula.rec' with
  | hatom => apply M.Val.hereditary hw;
  | himp =>
    intro hpq v hv;
    exact hpq <| M.rel_trans.trans _ _ _ hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];

/--
@isnad1 id=iff.0h3v.s5.1772e8e84575 from=translated src=- shape=97e3524b vocab=e1a61827
-/
lemma negEquiv : w ⊧ ∼φ ↔ w ⊧ φ ==> ⊥ := by simp_all [Satisfies];

/--
@isnad1 id=iff.0h5v.s5.f4ec88129ae8 from=translated src=- shape=4a248b0f vocab=69370807
-/
lemma iff_subst_self {F : Frame} {V : Valuation F} {x : F.World} (s) :
  letI U : Kripke.Valuation F := ⟨
    fun w a => Satisfies ⟨F, V⟩ w ((.atom a)⟦s⟧),
    fun {_ _} Rwv {_} => formula_hereditary Rwv
  ⟩;
  Satisfies ⟨F, U⟩ x φ ↔ Satisfies ⟨F, V⟩ x (φ⟦s⟧) := by
  induction φ using Formula.rec' generalizing x with
  | hatom a => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp φ ψ ihφ ihψ =>
    constructor;
    · intro hφψ y Rxy hφs;
      apply ihψ.mp;
      apply hφψ Rxy;
      apply ihφ.mpr hφs;
    · intro hφψs y Rxy hφ;
      apply ihψ.mpr;
      apply hφψs Rxy;
      apply ihφ.mp hφ;
  | hand φ ψ ihφ ihψ =>
    constructor;
    · rintro ⟨hφ, hψ⟩;
      exact ⟨ihφ.mp hφ, ihψ.mp hψ⟩
    · rintro ⟨hφ, hψ⟩;
      exact ⟨ihφ.mpr hφ, ihψ.mpr hψ⟩
  | hor φ ψ ihφ ihψ =>
    constructor;
    · rintro (hφ | hψ)
      · exact .inl <| ihφ.mp hφ
      · exact .inr <| ihψ.mp hψ
    · rintro (hφ | hψ)
      · exact .inl <| ihφ.mpr hφ
      · exact .inr <| ihψ.mpr hψ

end Satisfies

open Satisfies

/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnModel (M : Kripke.Model) (φ : Formula ℕ) := ∀ w : M.World, w ⊧ φ

namespace ValidOnModel

instance semantics : Semantics (Formula ℕ) (Model) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

variable {M : Model} {φ ψ χ : Formula ℕ}

/--
@isnad1 id=iff.0h2v.s4.0983f6c494a9 from=translated src=- shape=d962512f vocab=098c7a0f
-/
@[simp] protected lemma iff_models : M ⊧ φ ↔ Formula.Kripke.ValidOnModel M φ := iff_of_eq rfl

/--
@isnad1 id=realize.0h1v.s4.a4716fb9567c from=translated src=- shape=75b9ccd3 vocab=4f2b9a78
-/
protected lemma verum : M ⊧ ⊤ := by simp [ValidOnModel, Satisfies];

/--
@isnad1 id=not.0h1v.s4.e5970c2fc039 from=translated src=- shape=6fb7f272 vocab=ee4164b8
-/
protected lemma bot : ¬M ⊧ ⊥ := by simp [ValidOnModel, Satisfies];

/--
@isnad1 id=iff.0h2v.s5.ade6e122967d from=translated src=- shape=2c9fae5f vocab=41117bdc
-/
lemma iff_not_exists_world {M : Kripke.Model} : (¬M ⊧ φ) ↔ (∃ x : M.World, ¬x ⊧ φ) := by
  apply not_iff_not.mp;
  push Not;
  tauto;

alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_exists_world

/--
@isnad1 id=realize.0h3v.s5.e5f86e0c9714 from=translated src=- shape=6c8b9e6f vocab=e4402220
-/
protected lemma andElim₁ : M ⊧ φ ⋏ ψ ==> φ := by simp_all [ValidOnModel, Satisfies];

/--
@isnad1 id=realize.0h3v.s5.4578860b29db from=translated src=- shape=33f55064 vocab=e4402220
-/
protected lemma andElim₂ : M ⊧ φ ⋏ ψ ==> ψ := by simp_all [ValidOnModel, Satisfies];

/--
@isnad1 id=realize.0h3v.s5.bb5aa5380f61 from=translated src=- shape=ff2acf1b vocab=e4402220
-/
protected lemma andInst₃ : M ⊧ φ ==> ψ ==> φ ⋏ ψ := by
  intro x y _ hp z Ryz hq;
  replace hp : Satisfies M z φ := formula_hereditary Ryz hp;
  exact ⟨hp, hq⟩;

/--
@isnad1 id=realize.0h3v.s5.2d9afece7cfe from=translated src=- shape=320fac80 vocab=75b18e6d
-/
protected lemma orInst₁ : M ⊧ φ ==> φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

/--
@isnad1 id=realize.0h3v.s5.5c0fe040aa77 from=translated src=- shape=098ecc28 vocab=75b18e6d
-/
protected lemma orInst₂ : M ⊧ ψ ==> φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

/--
@isnad1 id=realize.0h4v.s6.dc65441de812 from=translated src=- shape=992ef589 vocab=75b18e6d
-/
protected lemma orElim : M ⊧ (φ ==> χ) ==> (ψ ==> χ) ==> (φ ⋎ ψ ==> χ) := by
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (M.rel_trans.trans _ _ _ hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

/--
@isnad1 id=realize.0h3v.s5.7d00d915e6db from=translated src=- shape=e852bbbc vocab=28635fea
-/
protected lemma imply₁ : M ⊧ φ ==> ψ ==> φ := by
  intro x y _ hp z Ryz _;
  exact formula_hereditary Ryz hp;

/--
@isnad1 id=realize.0h4v.s6.7cbd3457e879 from=translated src=- shape=5666318d vocab=28635fea
-/
protected lemma imply₂ : M ⊧ (φ ==> ψ ==> χ) ==> (φ ==> ψ) ==> φ ==> χ := by
  intro x y _ hpqr z Ryz hpq w Rzw hp;
  have Ryw : y ≺ w := Frame.rel_trans' Ryz Rzw;
  have Rww : w ≺ w := Frame.rel_refl';
  exact hpqr Ryw hp Rww (hpq Rzw hp);

/--
@isnad1 id=realize.2h3v.s5.dc9553b5f98f from=translated src=- shape=7af8841f vocab=28635fea
-/
protected lemma mdp (hpq : M ⊧ φ ==> ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro w;
  exact hpq w Frame.rel_refl' <| hp w;

/--
@isnad1 id=realize.0h2v.s4.7cffdaeffcb4 from=translated src=- shape=fb7cb33e vocab=54f8e8ab
-/
protected lemma efq : M ⊧ Axioms.EFQ φ := by simp [ValidOnModel, Satisfies];

/--
@isnad1 id=realize.1h2v.s4.46c2e6091afa from=translated src=- shape=9b67223b vocab=e734639e
-/
protected lemma lem : IsSymmetric M.Rel → M ⊧ Axioms.LEM φ := by
  unfold IsSymmetric Axioms.LEM;
  contrapose;
  push Not;
  intro h;
  obtain ⟨x, ⟨hnxφ, ⟨y, Rxy, hyφ⟩⟩⟩ := by simpa [Satisfies] using exists_world_of_not h;
  use x, y;
  constructor;
  · assumption;
  · by_contra Ryx;
    have : x ⊧ φ := formula_hereditary Ryx hyφ;
    contradiction;

/--
@isnad1 id=realize.1h3v.s4.16e253a71f5e from=translated src=- shape=c339b2d3 vocab=8625be9f
-/
protected lemma dum : Connected M.Rel → M ⊧ Axioms.Dummett φ ψ := by
  unfold Connected Axioms.Dummett;
  contrapose;
  push Not;
  intro h;
  obtain ⟨x, ⟨y, Rxy, hyφ, nhyψ⟩, ⟨z, Ryz, hzψ, nhyφ⟩⟩ := by
    simpa [Satisfies] using exists_world_of_not h;
  use x, y, z;
  refine ⟨⟨Rxy, Ryz⟩, ?_, ?_⟩;
  · by_contra Ryz;
    have : z ⊧ φ := formula_hereditary Ryz hyφ;
    contradiction;
  · by_contra Rzy;
    have : y ⊧ ψ := formula_hereditary Rzy hzψ;
    contradiction;

/--
@isnad1 id=realize.1h2v.s4.f9daf552a20c from=translated src=- shape=9b67223b vocab=3366314c
-/
protected lemma wlem : Confluent M.Rel → M ⊧ Axioms.WeakLEM φ := by
  unfold Confluent Axioms.WeakLEM;
  contrapose;
  push Not;
  intro h;
  obtain ⟨x, ⟨y, Rxy, hyφ⟩, ⟨z, Rxz, hz⟩⟩ := by
    simpa [Satisfies] using exists_world_of_not h;
  use x, y, z;
  refine ⟨⟨Rxy, Rxz⟩, ?_⟩;
  · rintro w Ryw;
    by_contra Rzw;
    have : w ⊧ φ := formula_hereditary Ryw hyφ;
    simp_all

end ValidOnModel

/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFrame (F : Frame) (φ : Formula ℕ) := ∀ V, (⟨F, V⟩ : Kripke.Model) ⊧ φ

namespace ValidOnFrame

instance semantics : Semantics (Formula ℕ) (Frame) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame} {φ ψ χ : Formula ℕ}

/--
@isnad1 id=iff.0h2v.s4.efe9649cd605 from=translated src=- shape=d962512f vocab=5297c871
-/
@[simp] protected lemma models_iff : F ⊧ φ ↔ ValidOnFrame F φ := iff_of_eq rfl

/--
@isnad1 id=realize.0h1v.s4.35771ae0039b from=translated src=- shape=75b9ccd3 vocab=14953a43
-/
protected lemma top : F ⊧ ⊤ := by tauto;

/--
@isnad1 id=not.0h1v.s4.a96c5ff2a745 from=translated src=- shape=6fb7f272 vocab=8016fce3
-/
protected lemma bot : ¬F ⊧ ⊥ := by
  intro h
  exact ValidOnModel.bot (h ⟨fun _ _ => True, by tauto⟩)
instance : Semantics.Bot (Frame) := ⟨fun _ => ValidOnFrame.bot⟩

/--
@isnad1 id=iff.0h2v.s4.0d5f6ea248ca from=translated src=- shape=6eaf6ad6 vocab=378fdb78
-/
lemma iff_not_exists_valuation : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F, ¬(⟨F, V⟩ :
    Kripke.Model) ⊧ φ) := by
  simp [ValidOnFrame];

alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation

/--
@isnad1 id=iff.0h2v.s5.25cdb92da96e from=translated src=- shape=a481eb48 vocab=fb61167f
-/
lemma iff_not_exists_valuation_world : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F, ∃ x : (⟨F, V⟩ :
    Kripke.Model).World, ¬Satisfies _ x φ) := by
  simp [ValidOnFrame, ValidOnModel, Semantics.Realize];

alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ :=
  iff_not_exists_valuation_world

/--
@isnad1 id=iff.0h2v.s5.48a090d34f55 from=translated src=- shape=83dd715c vocab=ada317bc
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
@isnad1 id=realize.1h3v.s4.6a8708423333 from=translated src=- shape=4b9ac5f1 vocab=4f65987f
-/
protected lemma subst (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := exists_valuation_world_of_not hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  apply h;

/--
@isnad1 id=realize.0h3v.s5.965fdb5b5e5d from=translated src=- shape=6c8b9e6f vocab=5b61fe52
-/
protected lemma andElim₁ : F ⊧ φ ⋏ ψ ==> φ := fun _ => ValidOnModel.andElim₁

/--
@isnad1 id=realize.0h3v.s5.cdd07e78c205 from=translated src=- shape=33f55064 vocab=5b61fe52
-/
protected lemma andElim₂ : F ⊧ φ ⋏ ψ ==> ψ := fun _ => ValidOnModel.andElim₂

/--
@isnad1 id=realize.0h3v.s5.cc236c9dd838 from=translated src=- shape=ff2acf1b vocab=5b61fe52
-/
protected lemma andInst₃ : F ⊧ φ ==> ψ ==> φ ⋏ ψ := fun _ => ValidOnModel.andInst₃

/--
@isnad1 id=realize.0h3v.s5.b7044c7d0d35 from=translated src=- shape=320fac80 vocab=dfb869b9
-/
protected lemma orInst₁ : F ⊧ φ ==> φ ⋎ ψ := fun _ => ValidOnModel.orInst₁

/--
@isnad1 id=realize.0h3v.s5.c1ae221c4523 from=translated src=- shape=098ecc28 vocab=dfb869b9
-/
protected lemma orInst₂ : F ⊧ ψ ==> φ ⋎ ψ := fun _ => ValidOnModel.orInst₂

/--
@isnad1 id=realize.0h4v.s6.0b572af85363 from=translated src=- shape=992ef589 vocab=dfb869b9
-/
protected lemma orElim : F ⊧ (φ ==> χ) ==> (ψ ==> χ) ==> (φ ⋎ ψ ==> χ) :=
  fun _ => ValidOnModel.orElim

/--
@isnad1 id=realize.0h3v.s5.c97814b6edf2 from=translated src=- shape=e852bbbc vocab=1c81e95f
-/
protected lemma imply₁ : F ⊧ φ ==> ψ ==> φ := fun _ => ValidOnModel.imply₁

/--
@isnad1 id=realize.0h4v.s6.a0cb7dfe3a0b from=translated src=- shape=5666318d vocab=1c81e95f
-/
protected lemma imply₂ : F ⊧ (φ ==> ψ ==> χ) ==> (φ ==> ψ) ==> φ ==> χ :=
  fun _ => ValidOnModel.imply₂

/--
@isnad1 id=realize.2h3v.s5.c5813713b40a from=translated src=- shape=7af8841f vocab=1c81e95f
-/
protected lemma mdp (hpq : F ⊧ φ ==> ψ) (hp : F ⊧ φ) : F ⊧ ψ :=
  fun V x => ValidOnModel.mdp (hpq V) (hp V) x

/--
@isnad1 id=realize.0h2v.s4.add10c1dc61b from=translated src=- shape=fb7cb33e vocab=0a49bdad
-/
protected lemma efq : F ⊧ Axioms.EFQ φ := fun _ => ValidOnModel.efq

/--
@isnad1 id=realize.1h2v.s4.c4adafa7e825 from=translated src=- shape=9c73810c vocab=5f3f35bf
-/
protected lemma lem (F_symm : IsSymmetric F.Rel) : F ⊧ Axioms.LEM φ :=
  fun _ => ValidOnModel.lem F_symm

/--
@isnad1 id=realize.1h3v.s4.fb927457b760 from=translated src=- shape=8c6eb4fc vocab=9481d30c
-/
protected lemma dum (F_conn : Connected F.Rel) : F ⊧ Axioms.Dummett φ ψ :=
  fun _ => ValidOnModel.dum F_conn

/--
@isnad1 id=realize.1h2v.s4.8455c8104b39 from=translated src=- shape=9c73810c vocab=d8249ba5
-/
protected lemma wlem (F_conf : Confluent F.Rel) : F ⊧ Axioms.WeakLEM φ :=
  fun _ => ValidOnModel.wlem F_conf

end ValidOnFrame

/-- Imported declaration from the Incompleteness formalization. -/
def ValidOnFrameClass (C : FrameClass) (φ : Formula ℕ) := ∀ F, F ∈ C → F ⊧ φ

namespace ValidOnFrameClass

variable {C : FrameClass} {φ ψ χ : Formula ℕ}

instance semantics : Semantics (Formula ℕ) (FrameClass) := ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩

/--
@isnad1 id=iff.0h2v.s4.72764fbc473d from=translated src=- shape=d962512f vocab=bb13c208
-/
@[simp] protected lemma models_iff : C ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass C φ := iff_of_eq rfl

/--
@isnad1 id=not.1h1v.s4.eea631c38dca from=translated src=- shape=4515b943 vocab=1908898f
-/
protected lemma bot (h_nonempty : C.Nonempty) : ¬C ⊧ ⊥ := by
  simp only [ValidOnFrameClass.models_iff, ValidOnFrameClass, Semantics.Bot.realize_bot, imp_false,
    not_forall, not_not];
  exact h_nonempty;

/--
@isnad1 id=iff.0h2v.s5.ac91d3848e28 from=translated src=- shape=26105338 vocab=279637a8
-/
lemma iff_not_exists_frame {C : Kripke.FrameClass} : (¬C ⊧ φ) ↔ (∃ F ∈ C, ¬F ⊧ φ) := by
  apply not_iff_not.mp;
  push Not;
  tauto;

alias ⟨exists_frame_of_not, not_of_exists_frame⟩ := iff_not_exists_frame

/--
@isnad1 id=iff.0h2v.s5.a1bfe125ee22 from=translated src=- shape=50aba44b vocab=883f2b32
-/
lemma iff_not_exists_model {C : Kripke.FrameClass} : (¬C ⊧ φ) ↔ (∃ M :
    Kripke.Model, M.toFrame ∈ C ∧ ¬M ⊧ φ) := by
  apply not_iff_not.mp;
  push Not;
  tauto;

alias ⟨exists_model_of_not, not_of_exists_model⟩ := iff_not_exists_model

/--
@isnad1 id=iff.0h2v.s5.e5ec032f5160 from=translated src=- shape=7f19b628 vocab=a41a8518
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

variable {C : FrameClass} {φ ψ χ : Formula ℕ}

/-- Imported declaration from the Incompleteness formalization. -/
class DefinedBy (C : Kripke.FrameClass) (Γ : Set (Formula ℕ)) where
  defines : ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, F ⊧ φ)

/-- Imported declaration from the Incompleteness formalization. -/
class FiniteDefinedBy (C Γ) extends FrameClass.DefinedBy C Γ where
  finite : Set.Finite Γ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev DefinedByFormula (C : Kripke.FrameClass) (φ : Formula ℕ) := FrameClass.DefinedBy C {φ}

/--
@isnad1 id=definedb.1h2v.s4.280feefaa897 from=translated src=- shape=ab8af8f8 vocab=34d2540d
-/
lemma definedByFormula_of_iff_mem_validate (h : ∀ F, F ∈ C ↔ F ⊧ φ) : DefinedByFormula C φ := by
  constructor;
  simpa;

/--
@isnad1 id=definedb.0h4v.s5.a685501f3cd0 from=translated src=- shape=35291cc0 vocab=4e92c773
-/
instance definedBy_inter
  (C₁ Γ₁) [h₁ : DefinedBy C₁ Γ₁]
  (C₂ Γ₂) [h₂ : DefinedBy C₂ Γ₂]
  : DefinedBy (C₁ ∩ C₂) (Γ₁ ∪ Γ₂) := ⟨by
  rintro F;
  constructor
  · rintro ⟨hF₁, hF₂⟩ φ (hφ₁ | hφ₂)
    · exact h₁.defines F |>.mp hF₁ _ hφ₁
    · exact h₂.defines F |>.mp hF₂ _ hφ₂
  · intro h
    exact ⟨h₁.defines F |>.mpr fun φ hφ => h _ (.inl hφ),
      h₂.defines F |>.mpr fun φ hφ => h _ (.inr hφ)⟩
⟩

/-- Imported declaration from the Incompleteness formalization. -/
class IsNonempty (C : Kripke.FrameClass) : Prop where
  nonempty : Nonempty C

end FrameClass

/-- Imported declaration from the Incompleteness formalization. -/
abbrev AllFrameClass : FrameClass := Set.univ

instance _root_.LO.IntProp.Kripke.AllFrameClass.DefinedBy :
    AllFrameClass.DefinedByFormula (Axioms.EFQ (.atom 0)) :=
  FrameClass.definedByFormula_of_iff_mem_validate <| by
    simp only [Set.mem_univ, true_iff];
    intro F;
    exact Formula.Kripke.ValidOnFrame.efq;

namespace FrameClass

variable {C : Kripke.FrameClass} {Γ : Set (Formula ℕ)}

/--
@isnad1 id=definedb.1h2v.s5.aff08ca3776c from=translated src=- shape=b90ef82c vocab=453ea665
-/
lemma definedBy_with_axiomEFQ (defines : C.DefinedBy Γ) :
    DefinedBy C (insert (Axioms.EFQ (.atom 0)) Γ) := by
  convert definedBy_inter AllFrameClass {Axioms.EFQ (.atom 0)} C Γ <;>
    simp [AllFrameClass, Set.singleton_union];

end FrameClass

end Kripke

end IntProp
end LO
