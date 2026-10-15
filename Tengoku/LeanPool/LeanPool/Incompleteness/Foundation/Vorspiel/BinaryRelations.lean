/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku

/-! # BinaryRelations -/

@[expose] public section

section «lp_section_1»

variable {α : Type u} (rel : α → α → Prop)
local infix:50 " ≺ " => rel

/-- Imported declaration from the Incompleteness formalization. -/
def IsSymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

-- NOTE: Another convention uses `x ≺ y → x ≺ z → y ≺ z`.
/-- Imported declaration from the Incompleteness formalization. -/
def Euclidean := ∀ ⦃x y z⦄, x ≺ y → x ≺ z → z ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
def Serial := ∀ x, ∃ y, x ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
def Confluent := ∀ ⦃x y z⦄, ((x ≺ y ∧ x ≺ z) → ∃ w, (y ≺ w ∧ z ≺ w))

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.RelDense := ∀ ⦃x y⦄, x ≺ y → ∃z, x ≺ z ∧ z ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
def Connected := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
def Functional := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y = z

/-- Imported declaration from the Incompleteness formalization. -/
def RightConvergent := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y ∨ y = z

/-- Imported declaration from the Incompleteness formalization. -/
def Coreflexive := ∀ ⦃x y⦄, x ≺ y → x = y

/-- Imported declaration from the Incompleteness formalization. -/
def Equality := ∀ ⦃x y⦄, x ≺ y ↔ x = y

/-- Imported declaration from the Incompleteness formalization. -/
def Isolated := ∀ ⦃x y⦄, ¬(x ≺ y)

/-- Imported declaration from the Incompleteness formalization. -/
def Assymetric := ∀ ⦃x y⦄, (x ≺ y) → ¬(y ≺ x)

/-- Imported declaration from the Incompleteness formalization. -/
def Universal := ∀ ⦃x y⦄, x ≺ y

/-- Imported declaration from the Incompleteness formalization. -/
abbrev ConverseWellFounded := WellFounded <| flip (· ≺ ·)

end «lp_section_1»

section «lp_section_2»

variable {α : Type u}
variable {rel : α → α → Prop}

/--
@isnad1 id=serial.0h3v.s4.01feff25b217 from=translated src=- shape=5a1031c8 vocab=502e26a4
-/
lemma serial_of_refl (hRefl : ∀ x, rel x x) : Serial rel := fun w => ⟨w, hRefl w⟩

/--
@isnad1 id=euclidea.1h3v.s5.88ddf7a97bff from=translated src=- shape=acc53825 vocab=7feed880
-/
lemma eucl_of_symm_trans (hSymm : IsSymmetric rel)
    (hTrans : ∀ ⦃x y z⦄, rel x y → rel y z → rel x z) :
    Euclidean rel := fun _ _ _ Rxy Rxz => hSymm <| hTrans (hSymm Rxy) Rxz

/--
@isnad1 id=var.2h7v.s5.e8fdcb1bc6c7 from=translated src=- shape=6227c902 vocab=7feed880
-/
lemma trans_of_symm_eucl (hSymm : IsSymmetric rel) (hEucl : Euclidean rel) :
    ∀ ⦃x y z⦄, rel x y → rel y z → rel x z :=
  fun _ _ _ Rxy Ryz => hSymm <| hEucl (hSymm Rxy) Ryz

/--
@isnad1 id=issymmet.1h3v.s4.52f1a5099ae1 from=translated src=- shape=6d72508f vocab=7feed880
-/
lemma symm_of_refl_eucl (hRefl : ∀ x, rel x x) (hEucl : Euclidean rel) :
    IsSymmetric rel := fun {x} {_} Rxy => hEucl (hRefl x) Rxy

/--
@isnad1 id=var.1h8v.s5.ac3dd099fbc9 from=translated src=- shape=bcd0e937 vocab=10c9f8e8
-/
lemma trans_of_refl_eucl (hRefl : ∀ x, rel x x) (hEucl : Euclidean rel) :
    ∀ ⦃x y z⦄, rel x y → rel y z → rel x z :=
  trans_of_symm_eucl (symm_of_refl_eucl hRefl hEucl) hEucl

/--
@isnad1 id=var.3h3v.s4.48a4e28d7fec from=translated src=- shape=706fc96c vocab=16e9d228
-/
lemma refl_of_symm_serial_eucl (hSymm : IsSymmetric rel) (hSerial : Serial rel) (hEucl :
    Euclidean rel) :
    ∀ x, rel x x := by
  rintro x;
  obtain ⟨y, Rxy⟩ := hSerial x;
  exact trans_of_symm_eucl hSymm hEucl Rxy (hSymm Rxy);

/--
@isnad1 id=coreflex.2h3v.s5.6ff1ecc7f610 from=translated src=- shape=ec24f3f1 vocab=5bb97419
-/
lemma corefl_of_refl_assym_eucl (hRefl : ∀ x, rel x x)
    (hAntisymm : ∀ ⦃x y⦄, rel x y → rel y x → x = y) (hEucl : Euclidean rel) :
    Coreflexive rel := fun {x} {_} Rxy => hAntisymm Rxy (hEucl (hRefl x) Rxy)

/--
@isnad1 id=equality.1h3v.s4.6035b24fe315 from=translated src=- shape=6d72508f vocab=3da34dbf
-/
lemma equality_of_refl_corefl (hRefl : ∀ x, rel x x) (hCorefl : Coreflexive rel) :
    Equality rel := fun {x} {_} => ⟨fun Rxy => hCorefl Rxy, by rintro rfl; exact hRefl x⟩

/--
@isnad1 id=equality.2h3v.s5.165c77d05902 from=translated src=- shape=ec24f3f1 vocab=abf47b05
-/
lemma equality_of_refl_assym_eucl (hRefl : ∀ x, rel x x)
    (hAntisymm : ∀ ⦃x y⦄, rel x y → rel y x → x = y) (hEucl : Euclidean rel) :
    Equality rel :=
  equality_of_refl_corefl hRefl (corefl_of_refl_assym_eucl hRefl hAntisymm hEucl)

/--
@isnad1 id=var.1h3v.s4.4aa117218e61 from=translated src=- shape=cac3c8ec vocab=390bced7
-/
lemma refl_of_equality (h : Equality rel) : ∀ x, rel x x := fun _ => h.mpr rfl

/--
@isnad1 id=coreflex.1h2v.s3.47cc2f78ea03 from=translated src=- shape=6e704b37 vocab=3da34dbf
-/
lemma corefl_of_equality (h : Equality rel) : Coreflexive rel := fun {_} {_} Rxy => h.mp Rxy

/--
@isnad1 id=not.1h3v.s4.d436d35dc373 from=translated src=- shape=bdc98a16 vocab=30873b55
-/
lemma irreflexive_of_assymetric (hAssym : Assymetric rel) : ∀ x, ¬ rel x x :=
  fun _ Rxx => hAssym Rxx Rxx

/--
@isnad1 id=var.1h3v.s4.3e5a3cb8890e from=translated src=- shape=cac3c8ec vocab=cdb66650
-/
lemma refl_of_universal (h : Universal rel) : ∀ x, rel x x := fun x => @h x x

/--
@isnad1 id=euclidea.1h2v.s3.d00302176564 from=translated src=- shape=6e704b37 vocab=ef1cb494
-/
lemma eucl_of_universal (h : Universal rel) : Euclidean rel := fun {_} {_} {_} _ _ => @h _ _

/--
@isnad1 id=confluen.1h3v.s4.f092e166eb3b from=translated src=- shape=6d72508f vocab=37d1ad3b
-/
lemma confluent_of_refl_connected (hRefl : ∀ x, rel x x) (hConfl : Connected rel) :
    Confluent rel := by
  rintro x y z ⟨Rxy, Rxz⟩;
  rcases @hConfl x y z ⟨Rxy, Rxz⟩ with (Ryz | Rzy);
  · exact ⟨z, Ryz, hRefl z⟩;
  · exact ⟨y, hRefl y, Rzy⟩;

section «lp_section_3»

/--
@isnad1 id=iff.0h2v.s5.a0506b0df4a1 from=translated src=- shape=3deb11c8 vocab=0729ccad
-/
lemma ConverseWellFounded.iff_has_max : ConverseWellFounded r ↔ (∀ (s :
    Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(r m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

/--
@isnad1 id=converse.0h2v.s4.46e661ab0cef from=translated src=- shape=c87b7e96 vocab=63735c17
-/
lemma Finite.converseWellFounded_of_trans_irrefl
    [Finite α] [IsTrans α rel] [Std.Irrefl rel] : ConverseWellFounded rel := by
  have : IsTrans α (flip rel) :=
    ⟨fun a b c rba rcb => IsTrans.trans c b a rcb rba⟩
  have : Std.Irrefl (flip rel) :=
    ⟨fun a h => Std.Irrefl.irrefl (r := rel) a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl (flip rel)

/--
@isnad1 id=converse.2h3v.s5.218da76a6eda from=translated src=- shape=fcfef084 vocab=a19440f7
-/
lemma Finite.converseWellFounded_of_trans_irrefl'
    (hFinite : Finite α) (hTrans : ∀ ⦃x y z⦄, rel x y → rel y z → rel x z)
  (hIrrefl : ∀ x, ¬ rel x x) : ConverseWellFounded rel :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨fun _ _ _ ba cb ↦ hTrans cb ba⟩
    ⟨hIrrefl⟩

end «lp_section_3»

/--
@isnad1 id=wellfoun.0h1v.s3.8037a2245799 from=translated src=- shape=de0eb3a2 vocab=5af9d863
-/
@[simp]
lemma WellFounded.trivial_wellfounded : WellFounded (α := α) (fun _ _ => False) :=
  ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩

/-- Imported declaration from the Incompleteness formalization. -/
def Relation.IrreflGen (R : α → α → Prop) := fun x y => x ≠ y ∧ R x y

/-- Imported declaration from the Incompleteness formalization. -/
abbrev WeaklyConverseWellFounded (R : α → α → Prop) := ConverseWellFounded (Relation.IrreflGen R)
alias WCWF := WeaklyConverseWellFounded

section «lp_section_4»

/--
@isnad1 id=ex.1h2v.s6.7ad06ce68bf2 from=translated src=- shape=01d83e3d vocab=bc10daae
-/
lemma dependent_choice {R : α → α → Prop} (h : ∃ s : Set α, s.Nonempty ∧ ∀ a ∈ s, ∃ b ∈ s, R a b)
  : ∃ f : ℕ → α, ∀ x, R (f x) (f (x + 1)) := by
  obtain ⟨s, ⟨x, hx⟩, h'⟩ := h;
  choose! f hfs hR using h';
  use fun n ↦ f^[n] x;
  intro n;
  simp only [Function.iterate_succ'];
  refine hR (f^[n] x) ?a;
  induction n with
  | zero => simpa;
  | succ n ih => simp only [Function.iterate_succ']; apply hfs _ ih;

/--
@isnad1 id=ex.0h3v.s5.e5291cb8ee22 from=translated src=- shape=d58aa30a vocab=b37b6ae0
-/
lemma Finite.exists_ne_map_eq_of_infinite_lt {α β} [LinearOrder α] [Infinite α] [Finite β] (f :
    α → β)
  : ∃ x y : α, (x < y) ∧ f x = f y
  := by
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f;
    rcases lt_trichotomy i j with (hij | rfl | hij);
    · exact ⟨i, j, hij, e⟩;
    · contradiction;
    · exact ⟨j, i, hij, e.symm⟩;

/--
@isnad1 id=eq.1h6v.s4.12b6384343ea from=translated src=- shape=766a490b vocab=1305c626
-/
lemma antisymm_of_WCWF {R : α → α → Prop} : WCWF R → ∀ ⦃x y⦄, R x y → R y x → x = y := by
  contrapose;
  simp only [not_forall, forall_exists_index];
  intro x y Rxy Ryz hxy;
  apply ConverseWellFounded.iff_has_max.not.mpr;
  push Not;
  use {x, y};
  constructor;
  · simp;
  · intro z hz;
    by_cases z = x;
    · use y; simp_all [Relation.IrreflGen];
    · use x; simp_all [Relation.IrreflGen];

/--
@isnad1 id=wcwf.2h3v.s5.6ab440fa04d5 from=translated src=- shape=9f0e5a18 vocab=d70cbabd
-/
lemma WCWF_of_finite_trans_antisymm {R : α → α → Prop} (hFin : Finite α)
    (R_trans : ∀ ⦃x y z⦄, R x y → R y z → R x z) :
    (∀ ⦃x y⦄, R x y → R y x → x = y) → WCWF R := by
    contrapose;
    intro hWCWF;
    replace hWCWF := ConverseWellFounded.iff_has_max.not.mp hWCWF;
    push Not at hWCWF;
    obtain ⟨f, hf⟩ := dependent_choice hWCWF; clear hWCWF;
    replace hf : ∀ x, f x ≠ f (x + 1) ∧ R (f x) (f (x + 1)) := by
      intro x
      exact hf x
    push Not
    obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite_lt f;
    use (f i), (f (i + 1));
    have ⟨hi₁, hi₂⟩ := hf i;
    refine ⟨(by assumption), ?_, (by assumption)⟩;
    have : i + 1 < j := lt_iff_le_and_ne.mpr ⟨by omega, by aesop⟩;
    have H : ∀ i j, i < j → R (f i) (f j) := by
      intro i j hij
      induction hij with
      | refl => exact hf i |>.2;
      | step _ ih => exact R_trans ih <| hf _ |>.2;
    simp_all

end «lp_section_4»

end «lp_section_2»
