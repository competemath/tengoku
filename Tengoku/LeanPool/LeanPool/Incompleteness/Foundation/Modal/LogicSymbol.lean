/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.LogicSymbol
public import Tengoku

/-! # LogicSymbol -/

@[expose] public section

open Function

namespace LO

/-- Imported declaration from the Incompleteness formalization. -/
class Box (F : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  box : F → F
  box_injective : Function.Injective box := by simp [Function.Injective];

/-- Imported declaration from the Incompleteness formalization. -/
prefix:76 "□" => Box.box

namespace Box

attribute [match_pattern] Box.box
attribute [simp] Box.box_injective

variable [Box F]

/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern] abbrev boxdot [Wedge F] (φ : F) : F := φ ⋏ □φ
/-- Imported notation from the Incompleteness formalization. -/
prefix:76 "⊡" => boxdot

/-- Imported declaration from the Incompleteness formalization. -/
abbrev multibox (n : ℕ) : F → F := (□ ·)^[n]
/-- Imported declaration from the Incompleteness formalization. -/
notation:76 "□^[" n:90 "]" φ:80 => multibox n φ

/-- Imported declaration from the Incompleteness formalization. -/
class Subclosed (C : F → Prop) where
  box_closed : C (□φ) → C φ

attribute [aesop safe 5 forward] Subclosed.box_closed

variable {φ ψ : F} {n : ℕ}

/--
@isnad1 id=iff.0h3v.s4.a3b17a6ab68b from=translated src=- shape=f432663e vocab=4003ec79
-/
@[simp]
lemma box_injective' : □φ = □ψ ↔ φ = ψ := box_injective.eq_iff

/--
@isnad1 id=eq.0h3v.s5.43b85db43b53 from=translated src=- shape=66cdf2c1 vocab=abdd4aa8
-/
@[simp] lemma multibox_succ : □^[(n + 1)]φ = □(□^[n]φ) := by apply iterate_succ_apply'

/--
@isnad1 id=injectiv.0h2v.s4.d0d40da693a8 from=translated src=- shape=a38aa54f vocab=ccb60482
-/
@[simp] lemma multibox_injective : Function.Injective (□^[n] · : F → F) := by
  apply Function.Injective.iterate (by simp);

/--
@isnad1 id=iff.0h4v.s4.d3410b6c24f1 from=translated src=- shape=fdd38b1f vocab=eb06d240
-/
@[simp]
lemma multimop_injective' : □^[n]φ = □^[n]ψ ↔ φ = ψ := multibox_injective.eq_iff

end Box

/-- Imported declaration from the Incompleteness formalization. -/
class Dia (F : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  dia : F → F
  dia_injective : Function.Injective dia := by simp [Function.Injective];

/-- Imported declaration from the Incompleteness formalization. -/
prefix:76 "◇" => Dia.dia

namespace Dia

attribute [match_pattern] Dia.dia
attribute [simp] Dia.dia_injective

variable [Dia F]

/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern] abbrev diadot [Vee F] (φ : F) : F := φ ⋎ ◇φ
/-- Imported notation from the Incompleteness formalization. -/
prefix:76 "diaDot" => diadot

/-- Imported declaration from the Incompleteness formalization. -/
abbrev multidia (n : ℕ) : F → F := (◇ ·)^[n]

/-- Imported declaration from the Incompleteness formalization. -/
notation:76 "◇^[" n:90 "]" φ:80 => multidia n φ

/-- Imported declaration from the Incompleteness formalization. -/
class Subclosed [LogicalConnective F] (C : F → Prop) where
  dia_closed : C (◇φ) → C φ

attribute [aesop safe 5 forward] Subclosed.dia_closed

variable {φ ψ : F} {n : ℕ}

/--
@isnad1 id=iff.0h3v.s4.661bd2901270 from=translated src=- shape=f432663e vocab=55b5a663
-/
@[simp]
lemma dia_injective' : ◇φ = ◇ψ ↔ φ = ψ := dia_injective.eq_iff

/--
@isnad1 id=eq.0h3v.s5.7ee494496adf from=translated src=- shape=66cdf2c1 vocab=698659ce
-/
@[simp] lemma multidia_succ : ◇^[(n + 1)]φ = ◇(◇^[n]φ) := by apply iterate_succ_apply'

/--
@isnad1 id=injectiv.0h2v.s4.6e8e41fcc403 from=translated src=- shape=a38aa54f vocab=5cddcad3
-/
@[simp] lemma multidia_injective : Function.Injective (◇^[n] · : F → F) := by
  apply Function.Injective.iterate (by simp);

/--
@isnad1 id=iff.0h4v.s4.65415a990cec from=translated src=- shape=fdd38b1f vocab=e699282e
-/
@[simp]
lemma multidia_injective' : ◇^[n]φ = ◇^[n]ψ ↔ φ = ψ := multidia_injective.eq_iff

end Dia

/-- Imported declaration from the Incompleteness formalization. -/
class BasicModalLogicalConnective (F : Type*) extends LogicalConnective F, Box F, Dia F

/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.BasicModalLogicConnective.Subclosed [BasicModalLogicalConnective F] (C : F →
  Prop) extends
  toLogicalConnectiveSubclosed : LogicalConnective.Subclosed C,
  toBoxSubclosed : Box.Subclosed C,
  toDiaSubclosed : Dia.Subclosed C

/-- Imported declaration from the Incompleteness formalization. -/
class DiaAbbrev (F : Type*) [Box F] [Dia F] [Tilde F] where
  dia_abbrev {φ : F} : ◇φ =  ∼(□(∼φ))

/-- Imported declaration from the Incompleteness formalization. -/
class ModalDeMorgan (F : Type*) [LogicalConnective F] [Box F] [Dia F] extends DeMorgan F where
  dia (φ : F) : ∼◇φ = □(∼φ)
  box (φ : F) : ∼□φ = ◇(∼φ)

attribute [simp] ModalDeMorgan.dia ModalDeMorgan.box

end LO

section «lp_section_1»

open LO (Box Dia)
variable {F : Type*}

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.multibox [Box F] (n : ℕ) : Set F → Set F := Set.image (□·)^[n]
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 "□''^[" n:90 "]" s:80 => Set.multibox n s

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.multidia [Dia F] (n : ℕ) : Set F → Set F := Set.image (◇·)^[n]
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 "◇''^[" n:90 "]" s:80 => Set.multidia n s

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.box [Box F] : Set F → Set F := Set.multibox (n := 1)
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "□''" => Set.box

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.dia [Dia F] : Set F → Set F := Set.multidia (n := 1)
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "◇''" => Set.dia

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.premultibox [Box F] (n : ℕ) : Set F → Set F := Set.preimage (□·)^[n]
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 "□''⁻¹^[" n:90 "]" s:80 => Set.premultibox n s

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.premultidia [Dia F] (n : ℕ) : Set F → Set F := Set.preimage (◇·)^[n]
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 "◇''⁻¹^[" n:90 "]" s:80 => Set.premultidia n s

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.prebox [Box F] : Set F → Set F := Set.premultibox (n := 1)
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "□''⁻¹" => Set.prebox

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.predia [Dia F] : Set F → Set F := Set.premultidia (n := 1)
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "◇''⁻¹" => Set.predia

namespace Set

variable {s t : Set F}

section «lp_section_2»

variable [Box F]

@[simp] lemma eq_box_multibox_one : □''s = □''^[1]s := by rfl

@[simp 1100] lemma eq_prebox_premultibox_one : □''⁻¹s = □''⁻¹^[1]s := by rfl

/--
@isnad1 id=le.1h4v.s5.6ad223cd07a6 from=translated src=- shape=cfec2d49 vocab=b3eeed40
-/
@[simp 1100] lemma multibox_subset_mono (h : s ⊆ t) : □''^[n]s ⊆ □''^[n]t := by
  simp_all [Set.subset_def];

/--
@isnad1 id=le.1h3v.s5.20293c41c304 from=translated src=- shape=b3afd9a0 vocab=c972de87
-/
lemma box_subset_mono (h : s ⊆ t) : □''s ⊆ □''t := by simpa using multibox_subset_mono (n := 1) h;

/--
@isnad1 id=le.1h4v.s5.04e02638ea72 from=translated src=- shape=cfec2d49 vocab=5c760765
-/
@[simp 1100] lemma premultibox_subset_mono (h : s ⊆ t) : □''⁻¹^[n]s ⊆ □''⁻¹^[n]t := by
  simp_all [Set.subset_def];

/--
@isnad1 id=le.1h3v.s5.423fba9836c6 from=translated src=- shape=b3afd9a0 vocab=8f33d82b
-/
lemma prebox_subset_mono (h : s ⊆ t) : □''⁻¹s ⊆  □''⁻¹t := by
  simpa using premultibox_subset_mono (n := 1) h;

/--
@isnad1 id=iff.0h4v.s5.0409a2dcf518 from=translated src=- shape=e3e40c18 vocab=a88bf442
-/
@[simp 1100] lemma iff_mem_premultibox : φ ∈ □''⁻¹^[n]s ↔ □^[n]φ ∈ s := by simp;

/--
@isnad1 id=iff.0h4v.s5.131b7e6b4900 from=translated src=- shape=d27fb997 vocab=6780958a
-/
@[simp 1100] lemma iff_mem_multibox : □^[n]φ ∈ □''^[n]s ↔ φ ∈ s := by simp;

/--
@isnad1 id=le.1h4v.s5.0ca99c775bfd from=translated src=- shape=3f37095a vocab=617c4d9f
-/
lemma subset_premulitibox_iff_multibox_subset (h : s ⊆ □''⁻¹^[n]t) :  □''^[n]s ⊆ t := by
  simp_all

/--
@isnad1 id=le.1h3v.s5.1da6203fad76 from=translated src=- shape=584045a2 vocab=3928d54a
-/
lemma subset_prebox_iff_box_subset (h : s ⊆ □''⁻¹t) : □''s ⊆ t := by
  simpa using subset_premulitibox_iff_multibox_subset (n := 1) h

/--
@isnad1 id=le.1h4v.s5.a4d538c0f2ce from=translated src=- shape=3f37095a vocab=617c4d9f
-/
lemma subset_multibox_iff_premulitibox_subset (h : s ⊆ □''^[n]t) : □''⁻¹^[n]s ⊆ t := by
  intro φ hp;
  have := premultibox_subset_mono h hp;
  simp_all;
/--
@isnad1 id=le.1h3v.s5.765a8d822935 from=translated src=- shape=584045a2 vocab=3928d54a
-/
lemma subset_box_iff_prebox_subset (h : s ⊆ □''t) : □''⁻¹s ⊆ t := by
  simpa using subset_multibox_iff_premulitibox_subset (n := 1) h

/--
@isnad1 id=ex.2h5v.s5.07af30ad8663 from=translated src=- shape=9bb97d52 vocab=e2ce37a5
-/
lemma forall_multibox_of_subset_multibox (h : s ⊆ □''^[n]t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = □^[n]ψ := by
  intro φ hp;
  obtain ⟨ψ, _, rfl⟩ := h hp;
  use ψ;
/--
@isnad1 id=ex.2h4v.s5.66a2e01c7ff4 from=translated src=- shape=48447c0e vocab=b21d89c2
-/
lemma forall_box_of_subset_box (h : s ⊆ □''t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = □ψ := by
  simpa using forall_multibox_of_subset_multibox (n := 1) h

lemma eq_premultibox_multibox_of_subset_premultibox (h : s ⊆ □''^[n]t) : □''^[n]□''⁻¹^[n]s = s := by
  apply Set.eq_of_subset_of_subset;
  · simp_all
  · intro φ hp;
    obtain ⟨ψ, _, rfl⟩ := forall_multibox_of_subset_multibox h φ hp;
    simp_all [Set.premultibox];
lemma eq_prebox_box_of_subset_prebox (h : s ⊆ □''t) : □''□''⁻¹s = s := by
  simpa using eq_premultibox_multibox_of_subset_premultibox (n := 1) h

end «lp_section_2»

section «lp_section_3»

variable [Dia F]

@[simp] lemma eq_dia_multidia_one : ◇''s = ◇''^[1]s := by rfl

@[simp 1100] lemma eq_predia_premultidia_one : ◇''⁻¹s = ◇''⁻¹^[1]s := by rfl

/--
@isnad1 id=le.1h4v.s5.62cf5fc8e631 from=translated src=- shape=cfec2d49 vocab=ebb01f53
-/
@[simp 1100] lemma multidia_subset_mono (h : s ⊆ t) : ◇''^[n]s ⊆ ◇''^[n]t := by
  simp_all [Set.subset_def];

/--
@isnad1 id=le.1h3v.s5.c05c4813a0fa from=translated src=- shape=b3afd9a0 vocab=e035e42a
-/
lemma dia_subset_mono (h : s ⊆ t) : ◇''s ⊆ ◇''t := by simpa using multidia_subset_mono (n := 1) h;

/--
@isnad1 id=le.1h4v.s5.55d594f995e8 from=translated src=- shape=cfec2d49 vocab=1c7c8694
-/
@[simp 1100] lemma premultidia_subset_mono (h : s ⊆ t) : ◇''⁻¹^[n]s ⊆ ◇''⁻¹^[n]t := by
  simp_all [Set.subset_def];

/--
@isnad1 id=le.1h3v.s5.2497879a0ea1 from=translated src=- shape=b3afd9a0 vocab=7c08348b
-/
lemma predia_subset_mono (h : s ⊆ t) : ◇''⁻¹s ⊆ ◇''⁻¹t := by
  simpa using premultidia_subset_mono (n := 1) h;

/--
@isnad1 id=iff.0h4v.s5.7183a2452dd6 from=translated src=- shape=e3e40c18 vocab=1ab1065e
-/
@[simp 1100] lemma iff_mem_premultidia : φ ∈ ◇''⁻¹^[n]s ↔ ◇^[n]φ ∈ s := by simp;

/--
@isnad1 id=iff.0h4v.s5.6660105b6f7d from=translated src=- shape=d27fb997 vocab=4965754b
-/
@[simp 1100] lemma iff_mem_multidia : ◇^[n]φ ∈ ◇''^[n]s ↔ φ ∈ s := by simp;

/--
@isnad1 id=le.1h4v.s5.aecfb10a180e from=translated src=- shape=3f37095a vocab=6e0ee3bb
-/
lemma subset_premultidia_iff_multidia_subset (h : s ⊆ ◇''⁻¹^[n]t) :  ◇''^[n]s ⊆ t := by
  simp_all

/--
@isnad1 id=le.1h3v.s5.91371f0ad087 from=translated src=- shape=584045a2 vocab=b455ee7d
-/
lemma subset_predia_iff_dia_subset (h : s ⊆ ◇''⁻¹t) : ◇''s ⊆ t := by
  simpa using subset_premultidia_iff_multidia_subset (n := 1) h

/--
@isnad1 id=le.1h4v.s5.2fd8d63b61fb from=translated src=- shape=3f37095a vocab=6e0ee3bb
-/
lemma subset_multidia_iff_premultidia_subset (h : s ⊆ ◇''^[n]t) : ◇''⁻¹^[n]s ⊆ t := by
  intro φ hp;
  have := premultidia_subset_mono h hp;
  simp_all;

/--
@isnad1 id=le.1h3v.s5.33887f4b0c49 from=translated src=- shape=584045a2 vocab=b455ee7d
-/
lemma subset_dia_iff_predia_subset (h : s ⊆ ◇''t) : ◇''⁻¹s ⊆ t := by
  simpa using subset_multidia_iff_premultidia_subset (n := 1) h

/--
@isnad1 id=ex.2h5v.s5.f513887dd371 from=translated src=- shape=9bb97d52 vocab=2e4fae0e
-/
lemma forall_multidia_of_subset_multidia (h : s ⊆ ◇''^[n]t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = ◇^[n]ψ := by
  intro φ hp;
  obtain ⟨ψ, _, rfl⟩ := h hp;
  use ψ;
/--
@isnad1 id=ex.2h4v.s5.a533ff74c707 from=translated src=- shape=48447c0e vocab=e85c9d44
-/
lemma forall_dia_of_subset_dia (h : s ⊆ ◇''t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = ◇ψ := by
  simpa using forall_multidia_of_subset_multidia (n := 1) h

lemma eq_premultidia_multidia_of_subset_premultidia (h : s ⊆ ◇''^[n]t) : ◇''^[n]◇''⁻¹^[n]s = s := by
  apply Set.eq_of_subset_of_subset;
  · simp_all
  · intro φ hp;
    obtain ⟨ψ, _, rfl⟩ := forall_multidia_of_subset_multidia h φ hp;
    simp_all [Set.premultidia];
lemma eq_predia_dia_of_subset_predia (h : s ⊆ ◇''t) : ◇''◇''⁻¹s = s := by
  simpa using eq_premultidia_multidia_of_subset_premultidia (n := 1) h

end «lp_section_3»

end Set

section «lp_section_4»

variable [DecidableEq F]

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Finset.multibox [Box F] (n : ℕ) : Finset F → Finset F := Finset.image (□·)^[n]

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Finset.multidia [Dia F] (n : ℕ) : Finset F → Finset F := Finset.image (◇·)^[n]

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Finset.modalBox [Box F] : Finset F → Finset F := Finset.multibox (n := 1)

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Finset.dia [Dia F] : Finset F → Finset F := Finset.multidia (n := 1)

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev Finset.premultibox [Box F] (n : ℕ) : Finset F → Finset F :=
  fun s => Finset.preimage s (□·)^[n] (Box.box_injective.iterate n).injOn

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev Finset.premultidia [Dia F] (n : ℕ) : Finset F → Finset F :=
  fun s => Finset.preimage s (◇·)^[n] (Dia.dia_injective.iterate n).injOn

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev Finset.prebox [Box F] : Finset F → Finset F :=
  Finset.premultibox (n := 1)

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev Finset.predia [Dia F] : Finset F → Finset F :=
  Finset.premultidia (n := 1)

end «lp_section_4»

namespace Finset

variable {s t : Finset F} {n : ℕ}

section «lp_section_5»

variable [Box F]

@[simp] lemma eq_box_multibox_one [DecidableEq F] : s.modalBox = s.multibox 1 := by rfl

@[simp] lemma eq_prebox_premultibox_one : s.prebox = s.premultibox 1 := by rfl

/--
@isnad1 id=eq.0h3v.s5.a06e33cebbfe from=translated src=- shape=8e6c0f78 vocab=150bb855
-/
lemma multibox_coe [DecidableEq F] : (s.multibox n) = □''^[n](s : Set F) := by simp_all

/--
@isnad1 id=eq.0h2v.s5.34e7915b3bd4 from=translated src=- shape=24fbe911 vocab=6b085ad0
-/
lemma box_coe [DecidableEq F] : s.modalBox = □''(s : Set F) := by simpa using multibox_coe (n := 1)

/--
@isnad1 id=iff.0h4v.s5.a5720c067a78 from=translated src=- shape=3db674f1 vocab=15907fc1
-/
lemma multibox_mem_coe [DecidableEq F] : φ ∈ s.multibox n ↔ φ ∈ □''^[n](↑s : Set F) := by
  constructor <;> simp_all

/--
@isnad1 id=iff.0h3v.s5.e873b39a34b4 from=translated src=- shape=107a617c vocab=c9172c9a
-/
lemma box_mem_coe [DecidableEq F] : φ ∈ s.modalBox ↔ φ ∈ □''(↑s : Set F) := by simp;

/--
@isnad1 id=eq.0h3v.s5.34b2ba2004ae from=translated src=- shape=8388b253 vocab=ec450a2c
-/
lemma premultibox_coe : (s.premultibox n) = □''⁻¹^[n](s : Set F) := by simp_all

/--
@isnad1 id=eq.0h2v.s4.44803bee5b2d from=translated src=- shape=9d34c258 vocab=3ac8b854
-/
lemma prebox_coe : s.prebox = □''⁻¹(↑s : Set F) := by simpa using premultibox_coe (n := 1)

/--
@isnad1 id=eq.1h4v.s5.0e9bfa110cf8 from=translated src=- shape=24b5aa46 vocab=a24590e2
-/
lemma premultibox_multibox_eq_of_subset_multibox
  [DecidableEq F]
  {s : Finset F} {t : Set F} (hs : ↑s ⊆ □''^[n]t) : (s.premultibox n).multibox n = s := by
  have := Set.eq_premultibox_multibox_of_subset_premultibox hs;
  rw [←premultibox_coe, ←multibox_coe] at this;
  exact Finset.coe_inj.mp this;

/--
@isnad1 id=eq.1h3v.s5.e2048f74ab2d from=translated src=- shape=dd065e21 vocab=7b3a08a7
-/
lemma prebox_box_eq_of_subset_box [DecidableEq F] {s : Finset F} {t : Set F} (hs : ↑s ⊆ □''t) :
    s.prebox.modalBox = s
  := by simpa using premultibox_multibox_eq_of_subset_multibox (n := 1) hs

end «lp_section_5»

section «lp_section_6»

variable [Dia F]

@[simp] lemma eq_dia_multidia_one [DecidableEq F] : s.dia = s.multidia 1 := by rfl

@[simp] lemma eq_predia_premultidia_one : s.predia = s.premultidia 1 := by rfl

/--
@isnad1 id=eq.0h3v.s5.a8f408b77b6c from=translated src=- shape=8e6c0f78 vocab=cb62de26
-/
lemma multidia_coe [DecidableEq F] : (s.multidia n) = ◇''^[n](s : Set F) := by simp_all

/--
@isnad1 id=eq.0h2v.s5.66192b66bf63 from=translated src=- shape=24fbe911 vocab=b4dfa597
-/
lemma dia_coe [DecidableEq F] : s.dia = ◇''(s : Set F) := by simpa using multidia_coe (n := 1)

/--
@isnad1 id=iff.0h4v.s5.e052499f5c0e from=translated src=- shape=3db674f1 vocab=0a3486be
-/
lemma multidia_mem_coe [DecidableEq F] : φ ∈ s.multidia n ↔ φ ∈ ◇''^[n](↑s : Set F) := by
  constructor <;> simp_all

/--
@isnad1 id=iff.0h3v.s5.2b677bcd5b47 from=translated src=- shape=107a617c vocab=7fec59d4
-/
lemma dia_mem_coe [DecidableEq F] : φ ∈ s.dia ↔ φ ∈ ◇''(↑s : Set F) := by simp;

/--
@isnad1 id=eq.0h3v.s5.b9fde9601609 from=translated src=- shape=8388b253 vocab=8043b144
-/
lemma premultidia_coe : (s.premultidia n) = ◇''⁻¹^[n](s : Set F) := by simp_all

/--
@isnad1 id=eq.0h2v.s4.b6fea67354ff from=translated src=- shape=9d34c258 vocab=fb230167
-/
lemma predia_coe : s.predia = ◇''⁻¹(↑s : Set F) := by simpa using premultidia_coe (n := 1)

/--
@isnad1 id=eq.1h4v.s5.b2a67b32bc0b from=translated src=- shape=24b5aa46 vocab=2c48b989
-/
lemma premultidia_multidia_eq_of_subset_multidia
  [DecidableEq F]
  {s : Finset F} {t : Set F} (hs : ↑s ⊆ ◇''^[n]t) : (s.premultidia n).multidia n = s := by
  have := Set.eq_premultidia_multidia_of_subset_premultidia hs;
  rw [←premultidia_coe, ←multidia_coe] at this;
  exact Finset.coe_inj.mp this;

/--
@isnad1 id=eq.1h3v.s5.8ac0ec5765a1 from=translated src=- shape=dd065e21 vocab=076fdc45
-/
lemma predia_dia_eq_of_subset_dia [DecidableEq F] {s : Finset F} {t : Set F} (hs : ↑s ⊆ ◇''t) :
    s.predia.dia = s
  := by simpa using premultidia_multidia_eq_of_subset_multidia (n := 1) hs

end «lp_section_6»

end Finset

section «lp_section_7»

variable [DecidableEq F]

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.multibox [Box F] (n : ℕ) : List F → List F :=
  fun l => Finset.multibox n l.toFinset |>.toList
/-- Imported declaration from the Incompleteness formalization. -/
notation "□'^[" n:90 "]" l:80 => List.multibox n l

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.multidia [Dia F] (n : ℕ) : List F → List F :=
  fun l => Finset.multidia n l.toFinset |>.toList
/-- Imported declaration from the Incompleteness formalization. -/
notation "◇'^[" n:90 "]" l:80 => List.multidia n l

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.box [Box F] : List F → List F := List.multibox (n := 1)
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "□'" => List.box

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.dia [Dia F] : List F → List F := List.multidia (n := 1)
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "◇'" => List.dia

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.premultibox [Box F] (n : ℕ) : List F → List F :=
  fun l => Finset.premultibox n l.toFinset |>.toList
/-- Imported declaration from the Incompleteness formalization. -/
notation "□'⁻¹^[" n:90 "]" l:80 => List.premultibox n l

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.premultidia [Dia F] (n : ℕ) : List F → List F :=
  fun l => Finset.premultidia n l.toFinset |>.toList
/-- Imported declaration from the Incompleteness formalization. -/
notation "◇'⁻¹^[" n:90 "]" l:80 => List.premultidia n l

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.prebox [Box F] : List F → List F := List.premultibox (n := 1)
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "□'⁻¹" => List.prebox

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.predia [Dia F] : List F → List F := List.premultidia (n := 1)
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "◇'⁻¹" => List.predia

end «lp_section_7»

namespace List

variable {l : List F} {s : Set F} {φ : F}

/--
@isnad1 id=ex.2h5v.s6.7a232bd0dd1b from=translated src=- shape=a7f10715 vocab=ef33c9ed
-/
lemma forall_multibox_of_subset_multibox [Box F] (h : ∀ φ ∈ l, φ ∈ □''^[n]s) :
    ∀ φ ∈ l, ∃ ψ ∈ s, φ = □^[n]ψ := by
  intro φ hp;
  obtain ⟨ψ, _, rfl⟩ := h φ hp;
  use ψ;

/--
@isnad1 id=ex.2h4v.s6.3e0b9855c274 from=translated src=- shape=13775df9 vocab=a3f4c19b
-/
lemma forall_box_of_subset_box [Box F] (h : ∀ φ ∈ l, φ ∈ □''s) : ∀ φ ∈ l, ∃ ψ ∈ s, φ = □ψ := by
  simpa using forall_multibox_of_subset_multibox (n := 1) h

/--
@isnad1 id=ex.2h5v.s6.b4f16a30bf96 from=translated src=- shape=a7f10715 vocab=88237179
-/
lemma forall_multidia_of_subset_multidia [Dia F] (h : ∀ φ ∈ l, φ ∈ ◇''^[n]s) :
    ∀ φ ∈ l, ∃ ψ ∈ s, φ = ◇^[n]ψ := by
  intro φ hp;
  obtain ⟨ψ, _, rfl⟩ := h φ hp;
  use ψ;

/--
@isnad1 id=ex.2h4v.s6.26359a7ea9ab from=translated src=- shape=13775df9 vocab=c26a3951
-/
lemma forall_dia_of_subset_dia [Dia F] (h : ∀ φ ∈ l, φ ∈ ◇''s) : ∀ φ ∈ l, ∃ ψ ∈ s, φ = ◇ψ := by
  simpa using forall_multidia_of_subset_multidia (n := 1) h

variable [DecidableEq F]

section «lp_section_8»

variable [Box F]

@[simp] lemma eq_box_multibox_one : □'l = □'^[1]l := by rfl

@[simp] lemma eq_prebox_premultibox_one : □'⁻¹l = □'⁻¹^[1]l := by rfl

/--
@isnad1 id=eq.0h2v.s4.2e564cbe618d from=translated src=- shape=50e1f1b2 vocab=b158a109
-/
@[simp 1100] lemma multibox_nil : (□'^[n]([] :List F)) = [] := by simp;

/--
@isnad1 id=eq.0h1v.s4.b6c0cdfbe693 from=translated src=- shape=d7ff9a0e vocab=1c755bcd
-/
lemma box_nil : (□'([] : List F)) = [] := by simp;

/--
@isnad1 id=eq.0h2v.s4.547ddedf56bd from=translated src=- shape=50e1f1b2 vocab=db2cdead
-/
@[simp 1100] lemma premultibox_nil : (□'⁻¹^[n]([] :List F)) = [] := by simp;

/--
@isnad1 id=eq.0h1v.s4.bb8139adf7ba from=translated src=- shape=d7ff9a0e vocab=7cd9ea53
-/
lemma prebox_nil : (□'⁻¹([] : List F)) = [] := by simp;

/--
@isnad1 id=eq.0h3v.s5.4f0bdb48607a from=translated src=- shape=907060b7 vocab=b11420a4
-/
@[simp 1100] lemma multibox_single : (□'^[n][φ]) = [□^[n]φ] := by simp;

/--
@isnad1 id=eq.0h2v.s4.755d14f00cc1 from=translated src=- shape=5dc12440 vocab=841ef8f8
-/
lemma box_single : (□'[φ]) = [□φ] := by simp;

/--
@isnad1 id=perm.1h4v.s5.200c0a6555d6 from=translated src=- shape=3a8b9ac3 vocab=fd1392f8
-/
lemma multibox_cons (hl : φ ∉ l) : □'^[n](φ :: l) ~ □^[n]φ :: □'^[n]l := by
  simp only [List.multibox, Finset.multibox, List.toFinset_cons, Finset.image_insert];
  apply Finset.toList_insert;
  simp_all;
/--
@isnad1 id=perm.1h3v.s5.28f97b745fb8 from=translated src=- shape=ce45e0f8 vocab=a102a3c7
-/
lemma box_cons (hl : φ ∉ l) : □'(φ :: l) ~ □φ :: □'l := multibox_cons hl

end «lp_section_8»

section «lp_section_9»

variable [Dia F]

@[simp] lemma eq_dia_multidia_one : ◇'l = ◇'^[1]l := by rfl

@[simp] lemma eq_predia_premultidia_one : ◇'⁻¹l = ◇'⁻¹^[1]l := by rfl

/--
@isnad1 id=eq.0h2v.s4.f9dca2b0bbfc from=translated src=- shape=50e1f1b2 vocab=72f9a993
-/
@[simp 1100] lemma multidia_nil : (◇'^[n]([] :List F)) = [] := by simp;

/--
@isnad1 id=eq.0h1v.s4.f3231d140fc1 from=translated src=- shape=d7ff9a0e vocab=ba730273
-/
lemma dia_nil : (◇'([] : List F)) = [] := by simp;

/--
@isnad1 id=eq.0h2v.s4.2d1f0805753a from=translated src=- shape=50e1f1b2 vocab=9d75e975
-/
@[simp 1100] lemma premultidia_nil : (◇'⁻¹^[n]([] :List F)) = [] := by simp;

/--
@isnad1 id=eq.0h1v.s4.4456ea6ba193 from=translated src=- shape=d7ff9a0e vocab=b1dcdd72
-/
lemma predia_nil : (◇'⁻¹([] : List F)) = [] := by simp;

/--
@isnad1 id=eq.0h3v.s5.87e9ecf37b42 from=translated src=- shape=907060b7 vocab=1b09b278
-/
@[simp 1100] lemma multidia_single : (◇'^[n][φ]) = [◇^[n]φ] := by simp;

/--
@isnad1 id=eq.0h2v.s4.51be2d6d57ba from=translated src=- shape=5dc12440 vocab=72668e59
-/
lemma dia_single : (◇'[φ]) = [◇φ] := by simp;

/--
@isnad1 id=perm.1h4v.s5.db62df19150f from=translated src=- shape=3a8b9ac3 vocab=2d5c68b9
-/
lemma multidia_cons (hl : φ ∉ l) : ◇'^[n](φ :: l) ~ ◇^[n]φ :: ◇'^[n]l := by
  simp only [List.multidia, Finset.multidia, List.toFinset_cons, Finset.image_insert];
  apply Finset.toList_insert;
  simp_all;

/--
@isnad1 id=perm.1h3v.s5.cac572fe0a2d from=translated src=- shape=ce45e0f8 vocab=e4275622
-/
lemma dia_cons (hl : φ ∉ l) : ◇'(φ :: l) ~ ◇φ :: ◇'l := multidia_cons hl

end «lp_section_9»

end List

end «lp_section_1»
