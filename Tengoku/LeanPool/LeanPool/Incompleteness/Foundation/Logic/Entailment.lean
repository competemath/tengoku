/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.Semantics
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Vorspiel.Collection
public import Tengoku

/-!
# Basic definitions and properties of proof system related notions

This file defines a characterization of the system/proof/provability/calculus of formulae.
Also defines soundness and completeness.

## Main Definitions
* `LO.Entailment F S`: a general framework of deductive system `S` for formulae `F`.
* `LO.Entailment.Inconsistent 𝓢`: a proposition that states that all formulae in `F` is provable
* from `𝓢`.
* `LO.Entailment.Consistent 𝓢`: a proposition that states that `𝓢` is not inconsistent.
* `LO.Entailment.Sound 𝓢 𝓜`: provability from `𝓢` implies satisfiability on `𝓜`.
* `LO.Entailment.Complete 𝓢 𝓜`: satisfiability on `𝓜` implies provability from `𝓢`.

## Notation
* `𝓢 ⊢ φ`: a type of formalized proofs of `φ : F` from deductive system `𝓢 : S`.
* `𝓢 ⊢! φ`: a proposition that states there is a proof of `φ` from `𝓢`, i.e. `φ` is provable from
* `𝓢`.
* `𝓢 ⊬ φ`: a proposition that states `φ` is not provable from `𝓢`.
* `𝓢 ⊢* T`: a type of formalized proofs for each formulae in a set `T` from `𝓢`.
* `𝓢 ⊢!* T`: a proposition that states each formulae in `T` is provable from `𝓢`.

-/

@[expose] public section

namespace LO

/-- Imported declaration from the Incompleteness formalization. -/
class Entailment (F : outParam Type*) (S : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Prf : S → F → Type*

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢ " => Entailment.Prf

namespace Entailment

variable {F : Type*} {S T U : Type*} [Entailment F S] [Entailment F T] [Entailment F U]

section «lp_section_1»

variable (𝓢 : S)

/-- Imported declaration from the Incompleteness formalization. -/
def Provable (f : F) : Prop := Nonempty (𝓢 ⊢ f)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Unprovable (f : F) : Prop := ¬Provable 𝓢 f

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢! " => Provable

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊬ " => Unprovable

/-- Imported declaration from the Incompleteness formalization. -/
def PrfSet (s : Set F) : Type _ := {f : F} → f ∈ s → 𝓢 ⊢ f

/-- Imported declaration from the Incompleteness formalization. -/
def ProvableSet (s : Set F) : Prop := ∀ {f}, f ∈ s → 𝓢 ⊢! f

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢* " => PrfSet

/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢!* " => ProvableSet

/-- Imported declaration from the Incompleteness formalization. -/
def theory : Set F := {f | 𝓢 ⊢! f}

end «lp_section_1»

/--
@isnad1 id=iff.0h4v.s4.95dfbd829972 from=translated src=- shape=62081e16 vocab=100aee8c
-/
lemma unprovable_iff_isEmpty {𝓢 : S} {f : F} :
    𝓢 ⊬ f ↔ IsEmpty (𝓢 ⊢ f) := by simp [Provable, Unprovable]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.Entailment.Provable.get {𝓢 : S} {f : F} (h : 𝓢 ⊢! f) : 𝓢 ⊢ f :=
  Classical.choice h

/--
@isnad1 id=iff.0h4v.s4.22498ffe0595 from=translated src=- shape=83ec8d8b vocab=939416cd
-/
lemma provableSet_iff {𝓢 : S} {s : Set F} :
    𝓢 ⊢!* s ↔ Nonempty (𝓢 ⊢* s) := by
  simp [ProvableSet, PrfSet, Provable, Classical.nonempty_pi, ←imp_iff_not_or]

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.Entailment.ProvableSet.get {𝓢 : S} {s : Set F} (h : 𝓢 ⊢!* s) : 𝓢 ⊢* s :=
  Classical.choice (α := 𝓢 ⊢* s) (provableSet_iff.mp h : Nonempty (𝓢 ⊢* s))

/-- Imported declaration from the Incompleteness formalization. -/
class WeakerThan (𝓢 : S) (𝓣 : T) : Prop where
  subset : theory 𝓢 ⊆ theory 𝓣

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " wkn " => WeakerThan

/-- Imported declaration from the Incompleteness formalization. -/
class StrictlyWeakerThan (𝓢 : S) (𝓣 : T) : Prop where
   weakerThan : 𝓢 wkn 𝓣
   notWT : ¬𝓣 wkn 𝓢

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " swkn " => StrictlyWeakerThan

/-- Imported declaration from the Incompleteness formalization. -/
class Equiv (𝓢 : S) (𝓣 : T) : Prop where
  eq : theory 𝓢 = theory 𝓣

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ≊ " => Equiv

section «lp_section_2»

variable {𝓢 : S} {𝓣 : T} {𝓤 : U}

@[instance, simp, refl] protected lemma _root_.LO.Entailment.WeakerThan.refl (𝓢 : S) :
    𝓢 wkn 𝓢 :=
  ⟨Set.Subset.refl _⟩

lemma _root_.LO.Entailment.WeakerThan.wk (h : 𝓢 wkn 𝓣) {φ} : 𝓢 ⊢! φ → 𝓣 ⊢! φ := @h.subset φ

lemma _root_.LO.Entailment.WeakerThan.pbl [h : 𝓢 wkn 𝓣] {φ} : 𝓢 ⊢! φ → 𝓣 ⊢! φ := @h.subset φ

@[trans] lemma _root_.LO.Entailment.WeakerThan.trans :
    𝓢 wkn 𝓣 → 𝓣 wkn 𝓤 → 𝓢 wkn 𝓤 :=
  fun w₁ w₂ ↦ ⟨Set.Subset.trans w₁.subset w₂.subset⟩

/--
@isnad1 id=iff.0h5v.s5.1e963fbba2f6 from=translated src=- shape=1243100c vocab=184259b1
-/
lemma weakerThan_iff : 𝓢 wkn 𝓣 ↔ (∀ {f}, 𝓢 ⊢! f → 𝓣 ⊢! f) :=
  ⟨fun h _ hf ↦ h.subset hf, fun h ↦ ⟨fun _ hf ↦ h hf⟩⟩

/--
@isnad1 id=iff.0h5v.s5.f7ccc67d8df2 from=translated src=- shape=b175cbb9 vocab=593d7225
-/
lemma not_weakerThan_iff : ¬𝓢 wkn 𝓣 ↔ (∃ f, 𝓢 ⊢! f ∧ 𝓣 ⊬ f) := by simp [weakerThan_iff, Unprovable];

/--
@isnad1 id=iff.0h5v.s5.09b98b29b63a from=translated src=- shape=400d0f99 vocab=159275b0
-/
lemma strictlyWeakerThan_iff : 𝓢 swkn 𝓣 ↔ (∀ {f}, 𝓢 ⊢! f → 𝓣 ⊢! f) ∧ (∃ f, 𝓢 ⊬ f ∧ 𝓣 ⊢! f) := by
  constructor
  · rintro ⟨wt, nwt⟩
    exact ⟨weakerThan_iff.mp wt, by rcases not_weakerThan_iff.mp nwt with ⟨φ, ht, hs⟩; exact ⟨φ,
      hs, ht⟩⟩
  · rintro ⟨h, φ, hs, ht⟩
    exact ⟨weakerThan_iff.mpr h, not_weakerThan_iff.mpr ⟨φ, ht, hs⟩⟩

@[trans]
lemma _root_.LO.Entailment.strictlyWeakerThan.trans : 𝓢 swkn 𝓣 → 𝓣 swkn 𝓤 → 𝓢 swkn 𝓤 := by
  rintro ⟨h₁, nh₁⟩ ⟨h₂, _⟩
  refine ⟨WeakerThan.trans h₁ h₂, not_weakerThan_iff.mpr ?_⟩
  obtain ⟨f, hf₁, hf₂⟩ := not_weakerThan_iff.mp nh₁
  exact ⟨f, weakerThan_iff.mp h₂ hf₁, hf₂⟩

/--
@isnad1 id=provable.2h6v.s5.6514f0a04fa6 from=translated src=- shape=1f708af3 vocab=184259b1
-/
lemma weakening (h : 𝓢 wkn 𝓣) {f} : 𝓢 ⊢! f → 𝓣 ⊢! f := weakerThan_iff.mp h

lemma _root_.LO.Entailment.StrictlyWeakerThan.of_unprovable_provable {𝓢 : S} {𝓣 : T} [𝓢 wkn 𝓣] {φ :
    F}
    (hS : 𝓢 ⊬ φ) (hT : 𝓣 ⊢! φ) : 𝓢 swkn 𝓣 := ⟨inferInstance, fun h ↦ hS (h.wk hT)⟩

lemma _root_.LO.Entailment.Equiv.iff : 𝓢 ≊ 𝓣 ↔ (∀ f, 𝓢 ⊢! f ↔ 𝓣 ⊢! f) :=
  ⟨fun e ↦ by simpa [Set.ext_iff, theory] using e.eq, fun e ↦ ⟨by simpa [Set.ext_iff,
    theory] using e⟩⟩

@[instance, simp, refl] protected lemma _root_.LO.Entailment.Equiv.refl (𝓢 : S) : 𝓢 ≊ 𝓢 := ⟨rfl⟩

@[symm] lemma _root_.LO.Entailment.Equiv.symm : 𝓢 ≊ 𝓣 → 𝓣 ≊ 𝓢 := fun e ↦ ⟨Eq.symm e.eq⟩

@[trans] lemma _root_.LO.Entailment.Equiv.trans :
    𝓢 ≊ 𝓣 → 𝓣 ≊ 𝓤 → 𝓢 ≊ 𝓤 :=
  fun e₁ e₂ ↦ ⟨Eq.trans e₁.eq e₂.eq⟩

lemma _root_.LO.Entailment.Equiv.antisymm_iff : 𝓢 ≊ 𝓣 ↔ 𝓢 wkn 𝓣 ∧ 𝓣 wkn 𝓢 := by
  refine ⟨fun e ↦ ⟨⟨Set.Subset.antisymm_iff.mp e.eq |>.1⟩, ⟨Set.Subset.antisymm_iff.mp e.eq |>.2⟩⟩,
    ?_⟩
  rintro ⟨w₁, w₂⟩
  exact ⟨Set.Subset.antisymm w₁.subset w₂.subset⟩

/--
@isnad1 id=equiv.1h5v.s5.645f4c959b31 from=translated src=- shape=b8df03fe vocab=f4ee73f1
-/
alias ⟨_, Equiv.antisymm⟩ := Equiv.antisymm_iff

lemma _root_.LO.Entailment.Equiv.le : 𝓢 ≊ 𝓣 → 𝓢 wkn 𝓣 := fun e ↦ ⟨by rw [e.eq]⟩

end «lp_section_2»

/--
@isnad1 id=provable.0h3v.s4.fc7bfb40e6f8 from=translated src=- shape=cd779a2c vocab=7374cb6a
-/
@[simp] lemma provableSet_theory (𝓢 : S) : 𝓢 ⊢!* theory 𝓢 := fun hf ↦ hf

/-- Imported declaration from the Incompleteness formalization. -/
def Inconsistent (𝓢 : S) : Prop := ∀ f, 𝓢 ⊢! f

/-- Imported declaration from the Incompleteness formalization. -/
class Consistent (𝓢 : S) : Prop where
  not_inconsistent : ¬Inconsistent 𝓢

/--
@isnad1 id=iff.0h3v.s4.c92786b72532 from=translated src=- shape=4263d0d4 vocab=afc0d1ac
-/
lemma inconsistent_def {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∀ f, 𝓢 ⊢! f := by simp [Inconsistent]

/--
@isnad1 id=iff.0h3v.s4.505d6fc4c10b from=translated src=- shape=6e311c50 vocab=7bc68400
-/
lemma inconsistent_iff_theory_eq {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by
  simp [Inconsistent, Set.ext_iff, theory]

/--
@isnad1 id=iff.0h3v.s4.9f761a7ee52e from=translated src=- shape=b287b7b8 vocab=6301be2e
-/
lemma not_inconsistent_iff_consistent {𝓢 : S} :
    ¬Inconsistent 𝓢 ↔ Consistent 𝓢 :=
  ⟨fun h ↦ ⟨h⟩, by rintro ⟨h⟩; exact h⟩

/--
@isnad1 id=not.1h3v.s4.562ce7b482a0 from=translated src=- shape=ee5a6a4e vocab=6301be2e
-/
alias ⟨_, Consistent.not_inc⟩ := not_inconsistent_iff_consistent

/--
@isnad1 id=iff.0h3v.s4.f70386d6289b from=translated src=- shape=b287b7b8 vocab=6301be2e
-/
lemma not_consistent_iff_inconsistent {𝓢 : S} :
    ¬Consistent 𝓢 ↔ Inconsistent 𝓢 := by simp [←not_inconsistent_iff_consistent]

/--
@isnad1 id=not.1h3v.s4.daae5dc4b091 from=translated src=- shape=ee5a6a4e vocab=6301be2e
-/
alias ⟨_, Inconsistent.not_con⟩ := not_consistent_iff_inconsistent

/--
@isnad1 id=iff.0h3v.s4.5159eadc4c0d from=translated src=- shape=0fc8d8b6 vocab=5e9bba77
-/
lemma consistent_iff_exists_unprovable {𝓢 : S} :
    Consistent 𝓢 ↔ ∃ f, 𝓢 ⊬ f := by
  simp [←not_inconsistent_iff_consistent, inconsistent_def]

/--
@isnad1 id=ex.1h3v.s4.27b0fa37181d from=translated src=- shape=30ea44d0 vocab=5e9bba77
-/
alias ⟨Consistent.exists_unprovable, _⟩ := consistent_iff_exists_unprovable

lemma _root_.LO.Entailment.Consistent.of_unprovable {𝓢 : S} {f} (h : 𝓢 ⊬ f) : Consistent 𝓢 :=
  ⟨fun hp ↦ h (hp f)⟩

/--
@isnad1 id=iff.0h3v.s4.505d6fc4c10b from=translated src=- shape=6e311c50 vocab=7bc68400
-/
lemma inconsistent_iff_theory_eq_univ {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by simp [inconsistent_def, theory, Set.ext_iff]

/--
@isnad1 id=eq.1h3v.s4.551e99f2e234 from=translated src=- shape=17e72e16 vocab=7bc68400
-/
alias ⟨Inconsistent.theory_eq, _⟩ := inconsistent_iff_theory_eq_univ

lemma _root_.LO.Entailment.Inconsistent.of_ge {𝓢 : S} {𝓣 : T} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 wkn 𝓣) :
    Inconsistent 𝓣 :=
  fun f ↦ h.subset (h𝓢 f)

lemma _root_.LO.Entailment.Consistent.of_le {𝓢 : S} {𝓣 : T} (h𝓢 : Consistent 𝓢) (h : 𝓣 wkn 𝓢) :
    Consistent 𝓣 :=
  ⟨fun H ↦ not_consistent_iff_inconsistent.mpr (H.of_ge h) h𝓢⟩

/-- Imported declaration from the Incompleteness formalization. -/
@[ext] structure Translation {S S' F F'} [Entailment F S] [Entailment F' S'] (𝓢 : S) (𝓣 : S') where
  /-- Imported declaration from the Incompleteness formalization. -/
  toFun : F → F'
  /-- Imported declaration from the Incompleteness formalization. -/
  prf {f} : 𝓢 ⊢ f → 𝓣 ⊢ toFun f

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ↝ " => Translation

/-- Imported declaration from the Incompleteness formalization. -/
@[ext] structure Bitranslation {S S' F F'} [Entailment F S] [Entailment F' S'] (𝓢 : S) (𝓣 :
    S') where
  /-- Imported declaration from the Incompleteness formalization. -/
  r : 𝓢 ↝ 𝓣
  /-- Imported declaration from the Incompleteness formalization. -/
  l : 𝓣 ↝ 𝓢
  /-- Imported declaration from the Incompleteness formalization. -/
  r_l : r.toFun ∘ l.toFun = id
  /-- Imported declaration from the Incompleteness formalization. -/
  l_r : l.toFun ∘ r.toFun = id

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ↭ " => Bitranslation

/-- Imported declaration from the Incompleteness formalization. -/
@[ext] structure FaithfulTranslation {S S' F F'} [Entailment F S] [Entailment F' S'] (𝓢 : S) (𝓣 :
    S') extends 𝓢 ↝ 𝓣 where
  /-- Imported declaration from the Incompleteness formalization. -/
  prfInv {f} : 𝓣 ⊢ toFun f → 𝓢 ⊢ f

/-- Imported declaration from the Incompleteness formalization. -/
infix:40 " ↝¹ " => FaithfulTranslation

namespace Translation

variable {S S' S'' : Type*} {F F' F'' : Type*} [Entailment F S] [Entailment F' S']
variable [Entailment F'' S'']

/-- Imported declaration from the Incompleteness formalization. -/
instance (𝓢 : S) (𝓣 : S') : CoeFun (𝓢 ↝ 𝓣) (fun _ ↦ F → F') := ⟨Translation.toFun⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected def id (𝓢 : S) : 𝓢 ↝ 𝓢 where
  toFun := id
  prf := id

/--
@isnad1 id=eq.0h4v.s4.56ce14e993f5 from=translated src=- shape=5bdef8b7 vocab=367b724f
-/
@[simp] lemma id_app (𝓢 : S) (f : F) : Translation.id 𝓢 f = f := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝ 𝓤) (ψ : 𝓢 ↝ 𝓣) : 𝓢 ↝ 𝓤 where
  toFun := φ.toFun ∘ ψ.toFun
  prf := φ.prf ∘ ψ.prf

/--
@isnad1 id=eq.0h12v.s6.76277061b9bd from=translated src=- shape=66e08d1c vocab=372f84c0
-/
@[simp] lemma comp_app {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝ 𝓤) (ψ : 𝓢 ↝ 𝓣) (f : F) :
    φ.comp ψ f = φ (ψ f) := rfl

/--
@isnad1 id=provable.1h8v.s5.90d30baa8e0e from=translated src=- shape=0b9d0425 vocab=54a1b60a
-/
lemma provable {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↝ 𝓣) {φ} (h : 𝓢 ⊢! φ) : 𝓣 ⊢! f φ := ⟨f.prf h.get⟩

end Translation

namespace Bitranslation

variable {S S' S'' : Type*} {F F' F'' : Type*} [Entailment F S] [Entailment F' S']
variable [Entailment F'' S'']

/--
@isnad1 id=eq.0h8v.s6.72ab8fe4c034 from=translated src=- shape=6a1a9fdb vocab=4f609c88
-/
@[simp] lemma r_l_app {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↭ 𝓣) (φ : F') : f.r (f.l φ) = φ := congr_fun f.r_l φ

/--
@isnad1 id=eq.0h8v.s6.f984d891487b from=translated src=- shape=f4049e3a vocab=4f609c88
-/
@[simp] lemma l_r_app {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↭ 𝓣) (φ : F) : f.l (f.r φ) = φ := congr_fun f.l_r φ

/-- Imported declaration from the Incompleteness formalization. -/
protected def id (𝓢 : S) : 𝓢 ↭ 𝓢 where
  r := Translation.id 𝓢
  l := Translation.id 𝓢
  r_l := by ext; simp
  l_r := by ext; simp

/-- Imported declaration from the Incompleteness formalization. -/
protected def symm {𝓢 : S} {𝓣 : S'} (φ : 𝓢 ↭ 𝓣) : 𝓣 ↭ 𝓢 where
  r := φ.l
  l := φ.r
  r_l := φ.l_r
  l_r := φ.r_l

/-- Imported declaration from the Incompleteness formalization. -/
def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↭ 𝓤) (ψ : 𝓢 ↭ 𝓣) : 𝓢 ↭ 𝓤 where
  r := φ.r.comp ψ.r
  l := ψ.l.comp φ.l
  r_l := by ext; simp
  l_r := by ext; simp

end Bitranslation

namespace FaithfulTranslation

variable {S S' S'' : Type*} {F F' F'' : Type*} [Entailment F S] [Entailment F' S']
variable [Entailment F'' S'']

instance (𝓢 : S) (𝓣 : S') : CoeFun (𝓢 ↝¹ 𝓣) (fun _ ↦ F → F') := ⟨fun t ↦ t.toFun⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected def id (𝓢 : S) : 𝓢 ↝¹ 𝓢 where
  toFun := id
  prf := id
  prfInv := id

/--
@isnad1 id=eq.0h4v.s5.6fd5d177218b from=translated src=- shape=1b9d5082 vocab=c95a0a74
-/
@[simp] lemma id_app (𝓢 : S) (f : F) : FaithfulTranslation.id 𝓢 f = f := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝¹ 𝓤) (ψ : 𝓢 ↝¹ 𝓣) : 𝓢 ↝¹ 𝓤 where
  toFun := φ.toFun ∘ ψ.toFun
  prf := φ.prf ∘ ψ.prf
  prfInv := ψ.prfInv ∘ φ.prfInv

/--
@isnad1 id=eq.0h12v.s6.878f2042fba8 from=translated src=- shape=e1c244b8 vocab=bee6a058
-/
@[simp] lemma comp_app {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝¹ 𝓤) (ψ : 𝓢 ↝¹ 𝓣) (f : F) :
    φ.comp ψ f = φ (ψ f) := rfl

/--
@isnad1 id=provable.1h8v.s6.c14cfdb45e4f from=translated src=- shape=1512d109 vocab=cb653451
-/
lemma provable {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↝¹ 𝓣) {φ} (h : 𝓢 ⊢! φ) : 𝓣 ⊢! f φ := ⟨f.prf h.get⟩

/--
@isnad1 id=iff.0h8v.s6.efc3bc081143 from=translated src=- shape=d8172e74 vocab=cb653451
-/
lemma provable_iff {𝓢 : S} {𝓣 : S'} (f : 𝓢 ↝¹ 𝓣) {φ} : 𝓣 ⊢! f φ ↔ 𝓢 ⊢! φ :=
  ⟨fun h ↦ ⟨f.prfInv h.get⟩, fun h ↦ ⟨f.prf h.get⟩⟩

end FaithfulTranslation

section «lp_section_3»

variable [LogicalConnective F]

variable (𝓢 : S)

/-- Imported declaration from the Incompleteness formalization. -/
def Complete : Prop := ∀ f, 𝓢 ⊢! f ∨ 𝓢 ⊢! ∼f

/-- Imported declaration from the Incompleteness formalization. -/
def Undecidable (f : F) : Prop := 𝓢 ⊬ f ∧ 𝓢 ⊬ ∼f

end «lp_section_3»

/--
@isnad1 id=iff.0h3v.s5.488bff378572 from=translated src=- shape=68021148 vocab=11b5ac4b
-/
lemma incomplete_iff_exists_undecidable [LogicalConnective F] {𝓢 : S} :
    ¬Entailment.Complete 𝓢 ↔ ∃ f, Undecidable 𝓢 f := by simp [Complete, Undecidable, not_or]

variable (S T)

/-- Imported declaration from the Incompleteness formalization. -/
class Axiomatized [Collection F S] where
  /-- Imported declaration from the Incompleteness formalization. -/
  prfAxm {𝓢 : S} : 𝓢 ⊢* Collection.set 𝓢
  /-- Imported declaration from the Incompleteness formalization. -/
  weakening {𝓢 𝓣 : S} : 𝓢 ⊆ 𝓣 → 𝓢 ⊢ f → 𝓣 ⊢ f

alias byAxm := Axiomatized.prfAxm
alias wk := Axiomatized.weakening

/-- Imported declaration from the Incompleteness formalization. -/
class StrongCut [Collection F T] where
  /-- Imported declaration from the Incompleteness formalization. -/
  cut {𝓢 : S} {𝓣 : T} {φ} : 𝓢 ⊢* Collection.set 𝓣 → 𝓣 ⊢ φ → 𝓢 ⊢ φ

variable {S T}

section «lp_section_4»

namespace Axiomatized

variable [Collection F S] [Axiomatized S] {𝓢 𝓣 : S}

/--
@isnad1 id=provable.0h3v.s4.f58d570937c9 from=translated src=- shape=04482f56 vocab=1880bd04
-/
@[simp] lemma provable_axm (𝓢 : S) : 𝓢 ⊢!* Collection.set 𝓢 := fun hf ↦ ⟨prfAxm hf⟩

/--
@isnad1 id=le.0h3v.s5.d69782ead7f1 from=translated src=- shape=1ec081f3 vocab=cb08742f
-/
lemma axm_subset (𝓢 : S) : Collection.set 𝓢 ⊆ theory 𝓢 := fun _ hp ↦ provable_axm 𝓢 hp

/--
@isnad1 id=weakerth.1h4v.s5.7889805690f3 from=translated src=- shape=267979b2 vocab=3164a7f4
-/
lemma le_of_subset (h : 𝓢 ⊆ 𝓣) : 𝓢 wkn 𝓣 := ⟨by rintro f ⟨b⟩; exact ⟨weakening h b⟩⟩

lemma «weakening!» (h : 𝓢 ⊆ 𝓣) {f} : 𝓢 ⊢! f → 𝓣 ⊢! f := by rintro ⟨b⟩; exact ⟨weakening h b⟩

/-- Imported declaration from the Incompleteness formalization.
@isnad1 id=weakerth.1h4v.s5.7889805690f3 from=translated src=- shape=267979b2 vocab=3164a7f4
-/
lemma weakerThanOfSubset (h : 𝓢 ⊆ 𝓣) : 𝓢 wkn 𝓣 := ⟨fun _ ↦ weakening! h⟩

/-- Imported declaration from the Incompleteness formalization. -/
def translation (h : 𝓢 ⊆ 𝓣) : 𝓢 ↝ 𝓣 where
  toFun := id
  prf := weakening h

end Axiomatized

/--
@isnad1 id=provable.0h3v.s4.f58d570937c9 from=translated src=- shape=04482f56 vocab=1880bd04
-/
alias by_axm := Axiomatized.provable_axm
/--
@isnad1 id=provable.2h5v.s5.803a8c8ee837 from=translated src=- shape=4bae752b vocab=aba8d49d
-/
alias wk! := Axiomatized.weakening!

section «lp_section_5»

variable [Collection F S] [Collection F T] [Axiomatized S]

/-- Imported declaration from the Incompleteness formalization. -/
def FiniteAxiomatizable (𝓢 : S) : Prop := ∃ 𝓕 : S, Collection.Finite 𝓕 ∧ 𝓕 ≊ 𝓢

lemma _root_.LO.Entailment.Consistent.of_subset {𝓢 𝓣 : S} (h𝓢 : Consistent 𝓢) (h : 𝓣 ⊆ 𝓢) :
    Consistent 𝓣 :=
  h𝓢.of_le (Axiomatized.le_of_subset h)

lemma _root_.LO.Entailment.Inconsistent.of_supset {𝓢 𝓣 : S} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ⊆ 𝓣) :
    Inconsistent 𝓣 :=
  h𝓢.of_ge (Axiomatized.le_of_subset h)

end «lp_section_5»

namespace StrongCut

variable [Collection F T] [StrongCut S T]

/-- Imported declaration from the Incompleteness formalization. -/
def translation {𝓢 : S} {𝓣 : T} (B : 𝓢 ⊢* Collection.set 𝓣) : 𝓣 ↝ 𝓢 where
  toFun := id
  prf := StrongCut.cut B

end StrongCut

namespace WeakerThan

end WeakerThan

/-- Imported declaration from the Incompleteness formalization. -/
lemma _root_.LO.Entailment.WeakerThan.ofSubset [Collection F S] [Axiomatized S] {𝓢 𝓣 : S} (h :
    𝓢 ⊆ 𝓣) :
    𝓢 wkn 𝓣 :=
  ⟨fun _ ↦ wk! h⟩

variable (S)

/-- Imported declaration from the Incompleteness formalization. -/
class Compact [Collection F S] where
  /-- Imported declaration from the Incompleteness formalization. -/
  φ {𝓢 : S} {f : F} : 𝓢 ⊢ f → S
  /-- Imported declaration from the Incompleteness formalization. -/
  φPrf {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : φ b ⊢ f
  φ_subset {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : φ b ⊆ 𝓢
  φ_finite {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : Collection.Finite (φ b)

variable {S}

namespace Compact

variable [Collection F S] [Compact S]

/--
@isnad1 id=ex.1h4v.s5.25208edcc9ca from=translated src=- shape=fd20e5e5 vocab=6989eb0c
-/
lemma finite_provable {𝓢 : S} (h : 𝓢 ⊢! f) : ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ Collection.Finite 𝓕 ∧ 𝓕 ⊢! f := by
  rcases h with ⟨b⟩
  exact ⟨φ b, φ_subset b, φ_finite b, ⟨φPrf b⟩⟩

end Compact

end «lp_section_4»

end Entailment

namespace Entailment

variable {S : Type*} {F : Type*} [LogicalConnective F] [Entailment F S]

variable (S)

/-- Imported declaration from the Incompleteness formalization. -/
class DeductiveExplosion where
  /-- Imported declaration from the Incompleteness formalization. -/
  dexp {𝓢 : S} : 𝓢 ⊢ ⊥ → (φ : F) → 𝓢 ⊢ φ

variable {S}

section «lp_section_6»

variable [DeductiveExplosion S]

namespace DeductiveExplosion

/-- Imported declaration from the Incompleteness formalization. -/
lemma «dexp!» {𝓢 : S} (h : 𝓢 ⊢! ⊥) (f : F) : 𝓢 ⊢! f := by
  rcases h with ⟨b⟩; exact ⟨DeductiveExplosion.dexp b f⟩

end DeductiveExplosion

/--
@isnad1 id=iff.0h3v.s5.114e61b939d3 from=translated src=- shape=65cc516a vocab=d43caf8b
-/
lemma inconsistent_iff_provable_bot {𝓢 : S} :
    Inconsistent 𝓢 ↔ 𝓢 ⊢! ⊥ := ⟨fun h ↦ h ⊥, fun h f ↦ DeductiveExplosion.dexp! h f⟩

/--
@isnad1 id=inconsis.1h3v.s5.4cf48c30eacf from=translated src=- shape=090158cc vocab=d43caf8b
-/
alias ⟨_, inconsistent_of_provable⟩ := inconsistent_iff_provable_bot

/--
@isnad1 id=iff.0h3v.s5.c13199d539a5 from=translated src=- shape=65cc516a vocab=5ae61f6e
-/
lemma consistent_iff_unprovable_bot {𝓢 : S} :
    Consistent 𝓢 ↔ 𝓢 ⊬ ⊥ := by
  simp [inconsistent_iff_provable_bot, ←not_inconsistent_iff_consistent]

/--
@isnad1 id=unprovab.1h3v.s5.dee5364087ae from=translated src=- shape=fbb3b348 vocab=5ae61f6e
-/
alias ⟨Consistent.not_bot, _⟩ := consistent_iff_unprovable_bot

variable [Collection F S] [Axiomatized S] [Compact S]

/--
@isnad1 id=iff.0h3v.s6.1dd3ba6f18e4 from=translated src=- shape=f47fba93 vocab=8bced408
-/
lemma inconsistent_compact {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ Collection.Finite 𝓕 ∧ Inconsistent 𝓕 :=
  ⟨fun H ↦ by rcases Compact.finite_provable (H ⊥) with ⟨𝓕, h𝓕, fin, h⟩; exact ⟨𝓕, h𝓕, fin,
    inconsistent_of_provable h⟩, by
    rintro ⟨𝓕, h𝓕, _, H⟩; exact H.of_supset h𝓕⟩

/--
@isnad1 id=iff.0h3v.s5.8188c06c2a9e from=translated src=- shape=b2ef2b77 vocab=0d00ee49
-/
lemma consistent_compact {𝓢 : S} :
    Consistent 𝓢 ↔ ∀ 𝓕 : S, 𝓕 ⊆ 𝓢 → Collection.Finite 𝓕 → Consistent 𝓕 := by
  simp [←not_inconsistent_iff_consistent, inconsistent_compact (𝓢 := 𝓢)]

end «lp_section_6»

variable (S)

/-- Imported declaration from the Incompleteness formalization. -/
class Deduction [Cons F S] where
  /-- Imported declaration from the Incompleteness formalization. -/
  ofInsert {φ ψ : F} {𝓢 : S} : cons φ 𝓢 ⊢ ψ → 𝓢 ⊢ φ ==> ψ
  /-- Imported declaration from the Incompleteness formalization. -/
  inv {φ ψ : F} {𝓢 : S} : 𝓢 ⊢ φ ==> ψ → cons φ 𝓢 ⊢ ψ

variable {S}

section «lp_section_7»

variable [Cons F S] [Deduction S] {𝓢 : S} {φ ψ : F}

alias deduction := Deduction.ofInsert

namespace Deduction

lemma «of_insert!» (h : cons φ 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ==> ψ := by
  rcases h with ⟨b⟩; exact ⟨Deduction.ofInsert b⟩

/--
@isnad1 id=provable.1h5v.s5.9563c9dcf820 from=translated src=- shape=da2b5295 vocab=8d64a0b3
-/
alias deduction! := Deduction.of_insert!

lemma «inv!» (h : 𝓢 ⊢! φ ==> ψ) : cons φ 𝓢 ⊢! ψ := by
  rcases h with ⟨b⟩; exact ⟨Deduction.inv b⟩

end Deduction

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.Deduction.translation (φ : F) (𝓢 : S) : cons φ 𝓢 ↝ 𝓢 where
  toFun := fun ψ ↦ φ ==> ψ
  prf := deduction

/--
@isnad1 id=iff.0h5v.s5.25f708370f25 from=translated src=- shape=ce90148b vocab=8d64a0b3
-/
lemma deduction_iff : cons φ 𝓢 ⊢! ψ ↔ 𝓢 ⊢! φ ==> ψ :=
  ⟨Deduction.of_insert!, Deduction.inv!⟩

end «lp_section_7»

end Entailment

section «lp_section_8»

variable {S : Type*} {F : Type*} [Entailment F S] {M : Type*} [Semantics F M]

/-- Imported declaration from the Incompleteness formalization. -/
class Sound (𝓢 : S) (𝓜 : M) : Prop where
  sound : ∀ {f : F}, 𝓢 ⊢! f → 𝓜 ⊧ f

/-- Imported declaration from the Incompleteness formalization. -/
class Complete (𝓢 : S) (𝓜 : M) : Prop where
  complete : ∀ {f : F}, 𝓜 ⊧ f → 𝓢 ⊢! f

namespace Sound

section «lp_section_9»

variable {𝓢 𝓣 : S} {𝓜 𝓝 : M} [Sound 𝓢 𝓜] [Sound 𝓣 𝓝]

/--
@isnad1 id=unprovab.1h6v.s5.80676d1eb37e from=translated src=- shape=25a70d52 vocab=89b76ce3
-/
lemma not_provable_of_countermodel {φ : F} (hp : ¬𝓜 ⊧ φ) : 𝓢 ⊬ φ :=
  fun b ↦ hp (Sound.sound b)

/--
@isnad1 id=consiste.1h5v.s5.338065bd7a23 from=translated src=- shape=dd14ca9d vocab=513b5007
-/
lemma consistent_of_meaningful : Semantics.Meaningful 𝓜 → Entailment.Consistent 𝓢 :=
  fun H ↦ ⟨fun h ↦ by rcases H with ⟨f, hf⟩; exact hf (Sound.sound (h f))⟩

/--
@isnad1 id=consiste.0h5v.s5.b7195c715d86 from=translated src=- shape=b5fe2c2c vocab=f96c9ad0
-/
lemma consistent_of_model [LogicalConnective F] [Semantics.Bot M] (𝓜 : M) [Sound 𝓢 𝓜] :
    Entailment.Consistent 𝓢 :=
  consistent_of_meaningful (𝓜 := 𝓜) inferInstance

/--
@isnad1 id=realizes.1h6v.s5.9eb08d4b753c from=translated src=- shape=d7fa86ba vocab=c2866577
-/
lemma realizeSet_of_prfSet {T : Set F} (b : 𝓢 ⊢!* T) : 𝓜 ⊧* T :=
  ⟨fun _ hf => sound (b hf)⟩

end «lp_section_9»

section «lp_section_10»

variable {𝓢 : S} {T : Set F} [Sound 𝓢 (Semantics.models M T)]

/--
@isnad1 id=conseque.1h6v.s5.4f90768942ee from=translated src=- shape=4edea83b vocab=8fe3d935
-/
lemma consequence_of_provable {f : F} : 𝓢 ⊢! f → T ⊨[M] f := sound

/--
@isnad1 id=consiste.1h5v.s5.750b8b712e47 from=translated src=- shape=ad5cace7 vocab=dee8f154
-/
lemma consistent_of_satisfiable [∀ 𝓜 : M, Semantics.Meaningful 𝓜] :
    Semantics.Satisfiable M T → Entailment.Consistent 𝓢 :=
  fun H ↦ consistent_of_meaningful (Semantics.meaningful_iff_satisfiableSet.mp H)

end «lp_section_10»

end Sound

namespace Complete

section «lp_section_11»

variable {𝓢 : S} {𝓜 : M} [Complete 𝓢 𝓜]

/--
@isnad1 id=meaningf.1h5v.s5.2e9fc8606b26 from=translated src=- shape=44f63bc5 vocab=9455e2a8
-/
lemma meaningful_of_consistent : Entailment.Consistent 𝓢 → Semantics.Meaningful 𝓜 := by
  contrapose
  suffices (∀ (f : F), 𝓜 ⊧ f) → Entailment.Inconsistent 𝓢 by
    simpa [Semantics.not_meaningful_iff, Entailment.not_consistent_iff_inconsistent]
  exact fun h f ↦ Complete.complete (h f)

end «lp_section_11»

section «lp_section_12»

variable {𝓢 : S} {s : Set F} [Complete 𝓢 (Semantics.models M s)]

/--
@isnad1 id=provable.1h6v.s5.19cee4dc0f44 from=translated src=- shape=0eb604a2 vocab=96f78072
-/
lemma provable_of_consequence {f : F} : s ⊨[M] f → 𝓢 ⊢! f := complete

/--
@isnad1 id=iff.0h6v.s6.e607564de6ef from=translated src=- shape=75a66a0b vocab=381ab89d
-/
lemma provable_iff_consequence [Sound 𝓢 (Semantics.models M s)] {f : F} :
    s ⊨[M] f ↔ 𝓢 ⊢! f :=
  ⟨complete, Sound.sound⟩

section «lp_section_13»

variable [LogicalConnective F] [∀ 𝓜 : M, Semantics.Meaningful 𝓜]

omit [LogicalConnective F] in
/--
@isnad1 id=satisfia.1h5v.s5.ee30a572a2ae from=translated src=- shape=cbe74ce2 vocab=34dab717
-/
lemma satisfiable_of_consistent :
    Entailment.Consistent 𝓢 → Semantics.Satisfiable M s :=
  fun H ↦ Semantics.meaningful_iff_satisfiableSet.mpr (meaningful_of_consistent H)

omit [LogicalConnective F] in
/--
@isnad1 id=inconsis.1h5v.s5.9f6780389aec from=translated src=- shape=2da1c856 vocab=75af7b69
-/
lemma inconsistent_of_unsatisfiable :
    ¬Semantics.Satisfiable M s → Entailment.Inconsistent 𝓢 := by
  contrapose; simpa [←Entailment.not_consistent_iff_inconsistent] using satisfiable_of_consistent

omit [LogicalConnective F] in
/--
@isnad1 id=iff.0h5v.s6.1cd187cf6d69 from=translated src=- shape=341099e8 vocab=ed48cdf9
-/
lemma consistent_iff_satisfiable [Sound 𝓢 (Semantics.models M s)] :
    Entailment.Consistent 𝓢 ↔ Semantics.Satisfiable M s :=
  ⟨satisfiable_of_consistent, Sound.consistent_of_satisfiable⟩

end «lp_section_13»

/--
@isnad1 id=weakerth.1h7v.s6.7cef48a55cf3 from=translated src=- shape=1cf0de49 vocab=baaa4de6
-/
lemma weakerthan_of_models {𝓣 : S} {t : Set F} [Sound 𝓣 (Semantics.models M t)]
    (H : ∀ 𝓜 : M, 𝓜 ⊧* s → 𝓜 ⊧* t) : 𝓣 wkn 𝓢 :=
  Entailment.weakerThan_iff.mpr <| fun h ↦ provable_of_consequence <|
      fun 𝓜 h𝓜 ↦ Sound.consequence_of_provable (M :=
    M) (T := t) h (H 𝓜 h𝓜)

end «lp_section_12»

end Complete

end «lp_section_8»

end LO
