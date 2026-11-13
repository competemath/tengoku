/-
# Total composition

Operads in the library are defined by partial composition `x ∘ᵢ y`. May's original definition
uses *total composition*: an operation `x` with inputs `A` and an operation `y a` with inputs `B a`
for each input `a` compose to an operation with inputs `Σ a, B a`,

  `γ x y : S (Σ a, B a)`,

subject to equivariance, two unit laws and associativity. This file builds total composition from
partial composition and proves May's axioms for it; `Operad.MayClass` proves the converse and that
the two definitions are equivalent.

* **Filling** (`May.fill`): the operations `y a` inserted one at a time at the inputs `a` in a
  list. The result does not depend on the order (`May.fill_perm`, by parallel associativity), it
  commutes with relabelling (`May.fill_map`), and filling the inputs of a composite `X ∘ᵢ Y` is
  the composite of the filled operations (`May.fill_comp`, the interchange law, by sequential
  and parallel associativity).
* **Total composition** (`SetOperad.total`): filling every input. It satisfies **May's axioms**:
  equivariance (`SetOperad.total_map`), the unit laws (`SetOperad.total_one_left`,
  `SetOperad.total_one_right`) and associativity (`SetOperad.total_assoc`, from the interchange
  law by `May.fill_fill`).
* **Operads in modules** (`SymOperad.total`): total composition of the underlying set operad,
  linear in the outer operation and multilinear in the inserted ones (`SymOperad.totalL`), with the
  same axioms (`SymOperad.total_assoc`, ...).

Inputs filled so far are tracked by a *stage* (`May.Stage`): the inputs not yet filled, and the
inputs of the operations inserted. Every comparison is an identity of explicit bijections, checked
on elements.
-/
import Tengoku.LeanOperads.Operad.SetOperad
import Tengoku.Seed.Data.List.Perm.Basic
import Tengoku.Seed.Data.Fintype.Sigma
import Tengoku.Seed.LinearAlgebra.Multilinear.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

set_option synthInstance.maxSize 1024

namespace Operad

open Sym

namespace May

/-! ## Filling the inputs one at a time -/

section Stages

variable {A : Type} [DecidableEq A] {B : A → Type} [∀ a, DecidableEq (B a)]

/-- **The inputs after filling those in `l`**: the inputs not in `l`, and the inputs of the
operations inserted at those in `l`.-/
abbrev Stage (B : A → Type) (l : List A) : Type :=
  {a : A // a ∉ l} ⊕ Σ a : {a : A // a ∈ l}, B a.1

/- The instances on stages are stated once, generically, so that every stage carries the same
instances whatever its type of inputs (membership in a list of a sum type would otherwise be
decided through a different `BEq`). -/
instance Stage.instDecidableEq (l : List A) : DecidableEq (Stage B l) :=
  inferInstanceAs (DecidableEq ({a : A // a ∉ l} ⊕ Σ a : {a : A // a ∈ l}, B a.1))

instance Stage.instFintype [Fintype A] [∀ a, Fintype (B a)] (l : List A) :
    Fintype (Stage B l) :=
  inferInstanceAs (Fintype ({a : A // a ∉ l} ⊕ Σ a : {a : A // a ∈ l}, B a.1))

/-- Before filling anything, the inputs are those of the outer operation.-/
def initEquiv (B : A → Type) : A ≃ Stage B [] where
  toFun a := Sum.inl ⟨a, by simp⟩
  invFun
    | Sum.inl a => a.1
    | Sum.inr p => absurd p.1.2 (by simp)
  left_inv _ := rfl
  right_inv := by
    rintro (a | ⟨⟨a, ha⟩, b⟩)
    · rfl
    · simp at ha

/-- **Filling one more input** `a ∉ l`: the composite of the stage of `l` with the operation
inserted at `a` has the inputs of the stage of `a :: l`.-/
def stepEquiv (a : A) (l : List A) (ha : a ∉ l) :
    Without (Stage B l) (Sum.inl ⟨a, ha⟩) ⊕ B a ≃ Stage B (a :: l) where
  toFun
    | Sum.inl ⟨Sum.inl c, hc⟩ => Sum.inl ⟨c.1, by
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => hc (by rw [Sum.inl.injEq, Subtype.ext_iff, h]), c.2⟩⟩
    | Sum.inl ⟨Sum.inr p, _⟩ => Sum.inr ⟨⟨p.1.1, List.mem_cons_of_mem a p.1.2⟩, p.2⟩
    | Sum.inr b => Sum.inr ⟨⟨a, List.mem_cons_self⟩, b⟩
  invFun
    | Sum.inl c => Sum.inl ⟨Sum.inl ⟨c.1, fun h => c.2 (List.mem_cons_of_mem a h)⟩, by
        intro h
        rw [Sum.inl.injEq, Subtype.ext_iff] at h
        exact c.2 (h ▸ List.mem_cons_self)⟩
    | Sum.inr ⟨c, b⟩ =>
        if h : c.1 = a then Sum.inr (cast (congrArg B h) b)
        else Sum.inl ⟨Sum.inr ⟨⟨c.1, (List.mem_cons.1 c.2).resolve_left h⟩, b⟩, by simp⟩
  left_inv := by
    rintro (⟨(c | ⟨⟨c, hc⟩, b⟩), hne⟩ | b)
    · rfl
    · have hca : c ≠ a := fun h => ha (h ▸ hc)
      simp [hca]
    · simp
  right_inv := by
    rintro (c | ⟨⟨c, hc⟩, b⟩)
    · rfl
    · by_cases h : c = a
      · subst h
        simp
      · simp [h]

/-- **Two lists with the same members give the same stage.**-/
def stagePerm {l l' : List A} (h : ∀ a, a ∈ l ↔ a ∈ l') : Stage B l ≃ Stage B l' where
  toFun
    | Sum.inl c => Sum.inl ⟨c.1, fun hc => c.2 ((h c.1).2 hc)⟩
    | Sum.inr ⟨c, b⟩ => Sum.inr ⟨⟨c.1, (h c.1).1 c.2⟩, b⟩
  invFun
    | Sum.inl c => Sum.inl ⟨c.1, fun hc => c.2 ((h c.1).1 hc)⟩
    | Sum.inr ⟨c, b⟩ => Sum.inr ⟨⟨c.1, (h c.1).2 c.2⟩, b⟩
  left_inv := by rintro (c | ⟨c, b⟩) <;> rfl
  right_inv := by rintro (c | ⟨c, b⟩) <;> rfl

/-- After filling every input, the inputs are those of the inserted operations.-/
def finalEquiv (B : A → Type) (l : List A) (hl : ∀ a, a ∈ l) : Stage B l ≃ Σ a, B a where
  toFun
    | Sum.inl c => absurd (hl c.1) c.2
    | Sum.inr p => ⟨p.1.1, p.2⟩
  invFun p := Sum.inr ⟨⟨p.1, hl p.1⟩, p.2⟩
  left_inv := by
    rintro (c | ⟨c, b⟩)
    · exact absurd (hl c.1) c.2
    · rfl
  right_inv _ := rfl

end Stages

section Relabel

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {P P' Q Q' : Type} [Fintype P] [DecidableEq P] [Fintype P'] [DecidableEq P']
  [Fintype Q] [DecidableEq Q] [Fintype Q'] [DecidableEq Q']

/-- Relabellings along equivalences with the same values agree.
@isnad1 id=eq.1h6v.s6.7112cf1e9ce2 from=translated src=- shape=f6e7af38 vocab=ac222f92
-/
lemma map_congr {e e' : P ≃ P'} (h : ∀ p, e p = e' p) (X : S P) :
    SetOperad.map e X = SetOperad.map e' X := by
  rw [Equiv.ext h]

/-- Two relabellings in a row, as one.
@isnad1 id=eq.0h7v.s6.fa2b6b643527 from=translated src=- shape=a29c14c8 vocab=5cc32ea5
-/
lemma map_map (e : P ≃ P') (f : P' ≃ Q) (X : S P) :
    SetOperad.map f (SetOperad.map e X) = SetOperad.map (e.trans f) X :=
  (SetOperad.map_trans e f X).symm

/-- **Relabelling the outer operation of a composite**, the slot `i'` being the image of `i`.
@isnad1 id=eq.1h9v.s8.4b9a3e722431 from=translated src=- shape=f9475628 vocab=f51b6176
-/
lemma comp_map_left (e : P ≃ P') (i : P) (i' : P') (hi : e i = i') (X : S P) (Y : S Q) :
    SetOperad.comp i' (SetOperad.map e X) Y
      = SetOperad.map ((compEquiv e (Equiv.refl Q) i).trans (slotEquiv hi))
          (SetOperad.comp i X Y) := by
  subst hi
  rw [← map_map, SetOperad.map_comp, SetOperad.map_refl]
  symm
  refine (map_congr (e' := Equiv.refl _) (fun s => ?_) _).trans (SetOperad.map_refl _)
  rcases s with s | s <;> rfl

/-- **Relabelling the inner operation of a composite.**
@isnad1 id=eq.0h8v.s8.deae5622beff from=translated src=- shape=48be796f vocab=c367d508
-/
lemma comp_map_right (i : P) (f : Q ≃ Q') (X : S P) (Y : S Q) :
    SetOperad.comp i X (SetOperad.map f Y)
      = SetOperad.map (Equiv.sumCongr (Equiv.refl (Without P i)) f) (SetOperad.comp i X Y) := by
  have h := SetOperad.map_comp (S := S) (Equiv.refl P) f i X Y
  rw [SetOperad.map_refl] at h
  refine h.symm.trans ?_
  exact map_congr (fun s => by rcases s with s | s <;> rfl) _

/-- **Parallel associativity**, solved for the composite filling `i` first.
@isnad1 id=eq.1h9v.s11.062020f9924c from=translated src=- shape=d5be136c vocab=79ec8e2c
-/
lemma comp_par_eq {i k : P} (hik : i ≠ k) (X : S P) (Y : S Q) (Z : S Q') :
    SetOperad.comp (Sum.inl ⟨k, Ne.symm hik⟩) (SetOperad.comp i X Y) Z
      = SetOperad.map (parEquiv hik Q Q').symm
          (SetOperad.comp (Sum.inl ⟨i, hik⟩) (SetOperad.comp k X Z) Y) := by
  rw [← SetOperad.comp_assoc_par hik, SetOperad.map_symm_map]

/-- **Sequential associativity**, solved for the composite filling the inner operation first.
@isnad1 id=eq.0h9v.s10.d51e2c7aed12 from=translated src=- shape=86b07f25 vocab=a9ad03af
-/
lemma comp_seq_eq (i : P) (j : Q) (X : S P) (Y : S Q) (Z : S Q') :
    SetOperad.comp (Sum.inr j) (SetOperad.comp i X Y) Z
      = SetOperad.map (seqEquiv i j Q').symm (SetOperad.comp i X (SetOperad.comp j Y Z)) := by
  rw [← SetOperad.comp_assoc_seq i j, SetOperad.map_symm_map]

/-- **The right unit**, solved for the composite.
@isnad1 id=eq.0h4v.s7.5eb2d0b91a6d from=translated src=- shape=844452bb vocab=37846557
-/
lemma comp_one_eq (i : P) (X : S P) :
    SetOperad.comp i X SetOperad.one = SetOperad.map (rightUnitEquiv i).symm X := by
  conv_lhs => rw [← SetOperad.map_symm_map (rightUnitEquiv i) (SetOperad.comp i X SetOperad.one)]
  rw [SetOperad.comp_one]

/-- **The left unit**, solved for the composite.
@isnad1 id=eq.0h3v.s7.c947557e8a9a from=translated src=- shape=4e6ecc17 vocab=23264356
-/
lemma one_comp_eq (Y : S Q) :
    SetOperad.comp () SetOperad.one Y = SetOperad.map (leftUnitEquiv Q).symm Y := by
  conv_lhs => rw [← SetOperad.map_symm_map (leftUnitEquiv Q) (SetOperad.comp () SetOperad.one Y)]
  rw [SetOperad.one_comp]

end Relabel

section Fill

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- **Filling the inputs in `l`**, the last one first: the operation `y a` is inserted at each
input `a` of `x` in `l`.-/
def fill (x : S A) (y : (a : A) → S (B a)) : (l : List A) → l.Nodup → S (Stage B l)
  | [], _ => SetOperad.map (initEquiv B) x
  | a :: l, h => SetOperad.map (stepEquiv a l (List.nodup_cons.1 h).1)
      (SetOperad.comp (Sum.inl ⟨a, (List.nodup_cons.1 h).1⟩ : Stage B l)
        (fill x y l (List.nodup_cons.1 h).2) (y a))

/--
@isnad1 id=eq.1h5v.s7.4ccb1c686378 from=translated src=- shape=ae87e1c0 vocab=b1072197
-/
lemma fill_nil (x : S A) (y : (a : A) → S (B a)) (h : ([] : List A).Nodup) :
    fill x y [] h = SetOperad.map (initEquiv B) x := rfl

/--
@isnad1 id=eq.1h7v.s11.5861c694405e from=translated src=- shape=92bc5853 vocab=2ff40c3e
-/
lemma fill_cons (x : S A) (y : (a : A) → S (B a)) (a : A) (l : List A) (h : (a :: l).Nodup) :
    fill x y (a :: l) h = SetOperad.map (stepEquiv a l (List.nodup_cons.1 h).1)
      (SetOperad.comp (Sum.inl ⟨a, (List.nodup_cons.1 h).1⟩ : Stage B l)
        (fill x y l (List.nodup_cons.1 h).2) (y a)) := rfl

/-- **Filling does not depend on the order**: two orders of the same inputs give the same
operation, by parallel associativity.
@isnad1 id=eq.3h7v.s7.4162b78b4df2 from=translated src=- shape=3648245c vocab=0621f1d8
-/
theorem fill_perm (x : S A) (y : (a : A) → S (B a)) {l l' : List A} (hp : l.Perm l')
    (hl : l.Nodup) (hl' : l'.Nodup) :
    SetOperad.map (stagePerm (B := B) fun _ => hp.mem_iff) (fill x y l hl) = fill x y l' hl' := by
  revert hl hl'
  induction hp with
  | nil =>
    intro hl hl'
    rw [fill_nil, map_map]
    refine map_congr (fun _ => ?_) x
    rfl
  | cons a hp ih =>
    intro hl hl'
    obtain ⟨ha₁, hl₁⟩ := List.nodup_cons.1 hl
    obtain ⟨ha₂, hl₂⟩ := List.nodup_cons.1 hl'
    rw [fill_cons, fill_cons, ← ih hl₁ hl₂,
      comp_map_left (stagePerm (B := B) fun _ => hp.mem_iff) (Sum.inl ⟨a, ha₁⟩)
        (Sum.inl ⟨a, ha₂⟩) rfl, map_map, map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(c | ⟨c, b⟩), hc⟩ | b <;> rfl
  | swap a b l =>
    intro hl hl'
    have hab : a ≠ b := fun h => (List.nodup_cons.1 hl').1 (h ▸ List.mem_cons_self)
    have ha : a ∉ l := (List.nodup_cons.1 (List.nodup_cons.1 hl).2).1
    have hb : b ∉ l := fun h => (List.nodup_cons.1 hl).1 (List.mem_cons_of_mem a h)
    have ha' : a ∉ b :: l := (List.nodup_cons.1 hl').1
    have hb' : b ∉ a :: l := (List.nodup_cons.1 hl).1
    have hik : (Sum.inl ⟨a, ha⟩ : Stage B l) ≠ Sum.inl ⟨b, hb⟩ := by
      simp [hab]
    rw [fill_cons, fill_cons, fill_cons, fill_cons,
      comp_map_left (stepEquiv a l ha) (Sum.inl ⟨Sum.inl ⟨b, hb⟩, Ne.symm hik⟩)
        (Sum.inl ⟨b, hb'⟩) rfl,
      comp_map_left (stepEquiv b l hb) (Sum.inl ⟨Sum.inl ⟨a, ha⟩, hik⟩)
        (Sum.inl ⟨a, ha'⟩) rfl,
      comp_par_eq hik]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(⟨(c | ⟨⟨c, hc⟩, d⟩), hc'⟩ | d), hd⟩ | d <;> rfl
  | trans hp₁ hp₂ ih₁ ih₂ =>
    intro hl hl'
    have hm := (hp₁.nodup_iff).1 hl
    rw [← ih₂ hm hl', ← ih₁ hl hm, map_map]
    exact map_congr (fun s => by rcases s with c | ⟨c, b⟩ <;> rfl) _

end Fill

section Congr

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A A' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  {B : A → Type} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
  {B' : A' → Type} [∀ a, Fintype (B' a)] [∀ a, DecidableEq (B' a)]

/-- **Relabelling a stage** along `σ : A ≃ A'` and `τ a : B a ≃ B' (σ a)`.-/
def stageCongr (σ : A ≃ A') (τ : ∀ a, B a ≃ B' (σ a)) (l : List A) :
    Stage B l ≃ Stage B' (l.map σ) :=
  Equiv.sumCongr
    (σ.subtypeEquiv fun _ => not_congr (List.mem_map_of_injective σ.injective).symm)
    (Equiv.sigmaCongr (σ.subtypeEquiv fun _ => (List.mem_map_of_injective σ.injective).symm)
      fun a => τ a.1)

end Congr

section Unit

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A]

/-- The input of `A` that an input of a stage with units inserted comes from.-/
def unitVal {l : List A} : Stage (fun _ : A => Unit) l → A
  | Sum.inl c => c.1
  | Sum.inr p => p.1.1

/-- **Filling with units relabels**: inserting the unit at the inputs in `l` relabels the
operation along a bijection that keeps track of the inputs.
@isnad1 id=ex.1h4v.s7.b77adbfe5c0d from=translated src=- shape=01d17058 vocab=de1bb016
-/
theorem fill_one (x : S A) (l : List A) (hl : l.Nodup) :
    ∃ e : A ≃ Stage (fun _ : A => Unit) l, (∀ a, unitVal (e a) = a) ∧
      fill x (fun _ => SetOperad.one) l hl = SetOperad.map e x := by
  induction l with
  | nil => exact ⟨initEquiv _, fun _ => rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
    obtain ⟨e, he, hx⟩ := ih hl'
    let r := rightUnitEquiv (A := Stage (fun _ : A => Unit) l) (Sum.inl ⟨a, ha⟩)
    refine ⟨e.trans (r.symm.trans (stepEquiv (B := fun _ : A => Unit) a l ha)), fun b => ?_, ?_⟩
    · have key : ∀ s : Stage (fun _ : A => Unit) l,
          unitVal (stepEquiv (B := fun _ : A => Unit) a l ha (r.symm s)) = unitVal s := by
        intro s
        by_cases hs : s = Sum.inl ⟨a, ha⟩
        · subst hs
          rw [rightUnitEquiv_symm_self]
          rfl
        · rw [rightUnitEquiv_symm_of_ne hs]
          rcases s with c | ⟨c, u⟩ <;> rfl
      simp only [Equiv.trans_apply]
      rw [key, he]
    · rw [fill_cons, hx, comp_one_eq, map_map, map_map]

end Unit

section Interchange

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {W₁ : P → Type} [∀ p, Fintype (W₁ p)] [∀ p, DecidableEq (W₁ p)]
  {W₂ : Q → Type} [∀ q, Fintype (W₂ q)] [∀ q, DecidableEq (W₂ q)]

/-- **The inputs of the operations inserted into a composite**: `W₁` at the inputs coming from the
outer operation, `W₂` at those coming from the inner one.-/
def sumFam (W₁ : P → Type) (W₂ : Q → Type) (i : P) : Without P i ⊕ Q → Type
  | Sum.inl p => W₁ p.1
  | Sum.inr q => W₂ q

instance (i : P) (j : Without P i ⊕ Q) : Fintype (sumFam W₁ W₂ i j) :=
  match j with
  | Sum.inl p => inferInstanceAs (Fintype (W₁ p.1))
  | Sum.inr q => inferInstanceAs (Fintype (W₂ q))

instance (i : P) (j : Without P i ⊕ Q) : DecidableEq (sumFam W₁ W₂ i j) :=
  match j with
  | Sum.inl p => inferInstanceAs (DecidableEq (W₁ p.1))
  | Sum.inr q => inferInstanceAs (DecidableEq (W₂ q))

/-- The operations inserted into a composite.-/
def sumVal (i : P) (w₁ : (p : P) → S (W₁ p)) (w₂ : (q : Q) → S (W₂ q)) :
    (j : Without P i ⊕ Q) → S (sumFam W₁ W₂ i j)
  | Sum.inl p => w₁ p.1
  | Sum.inr q => w₂ q

/-- **Splitting a list of inputs of a composite**: `L₁` and `L₂` list, in order, the inputs in
`L` coming from the outer and from the inner operation.-/
inductive Splits {i : P} : List (Without P i ⊕ Q) → List P → List Q → Prop
  | nil : Splits [] [] []
  | left {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q} (p : Without P i) :
      Splits L L₁ L₂ → Splits (Sum.inl p :: L) (p.1 :: L₁) L₂
  | right {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q} (q : Q) :
      Splits L L₁ L₂ → Splits (Sum.inr q :: L) L₁ (q :: L₂)

namespace Splits

variable {i : P} {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q}

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
/--
@isnad1 id=iff.1h7v.s6.9a1efd8c65da from=translated src=- shape=1245bccc vocab=169c7e12
-/
lemma mem_left (h : Splits L L₁ L₂) (p : Without P i) : p.1 ∈ L₁ ↔ Sum.inl p ∈ L := by
  induction h with
  | nil => simp
  | left p' _ ih =>
    simp only [List.mem_cons, ih, Sum.inl.injEq]
    exact or_congr_left ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
  | right q _ ih => simp [ih]

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
/--
@isnad1 id=iff.1h7v.s6.38ca842ca102 from=translated src=- shape=984f4505 vocab=e207760e
-/
lemma mem_right (h : Splits L L₁ L₂) (q : Q) : q ∈ L₂ ↔ Sum.inr q ∈ L := by
  induction h with
  | nil => simp
  | left p _ ih => simp [ih]
  | right q' _ ih => simp [ih]

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
/--
@isnad1 id=not.1h6v.s5.c13b7271fd5f from=translated src=- shape=0ec5efa1 vocab=7fca8c28
-/
lemma not_mem (h : Splits L L₁ L₂) : i ∉ L₁ := by
  induction h with
  | nil => simp
  | left p _ ih => simp [ih, Ne.symm p.2]
  | right q _ ih => exact ih

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
/--
@isnad1 id=nodup.2h6v.s5.eeeceef91167 from=translated src=- shape=2fee9c84 vocab=b4c6d208
-/
lemma nodup_left (h : Splits L L₁ L₂) (hL : L.Nodup) : L₁.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | left p h ih =>
    obtain ⟨hp, hL⟩ := List.nodup_cons.1 hL
    exact List.nodup_cons.2 ⟨fun h' => hp ((h.mem_left p).1 h'), ih hL⟩
  | right q _ ih => exact ih (List.nodup_cons.1 hL).2

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
/--
@isnad1 id=nodup.2h6v.s5.dfbb4c00821d from=translated src=- shape=258b7a71 vocab=b4c6d208
-/
lemma nodup_right (h : Splits L L₁ L₂) (hL : L.Nodup) : L₂.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | left p _ ih => exact ih (List.nodup_cons.1 hL).2
  | right q h ih =>
    obtain ⟨hq, hL⟩ := List.nodup_cons.1 hL
    exact List.nodup_cons.2 ⟨fun h' => hq ((h.mem_right q).1 h'), ih hL⟩

end Splits

/-- **The inputs after filling the inputs in `L` of a composite**, against those of the composite
of the filled operations.-/
def interEquiv {i : P} {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q}
    (h : Splits L L₁ L₂) :
    Stage (sumFam W₁ W₂ i) L ≃
      Without (Stage W₁ L₁) (Sum.inl ⟨i, h.not_mem⟩) ⊕ Stage W₂ L₂ where
  toFun
    | Sum.inl ⟨Sum.inl p, hp⟩ =>
        Sum.inl ⟨Sum.inl ⟨p.1, fun h' => hp ((h.mem_left p).1 h')⟩, by
          simp [Subtype.ext_iff, p.2]⟩
    | Sum.inl ⟨Sum.inr q, hq⟩ => Sum.inr (Sum.inl ⟨q, fun h' => hq ((h.mem_right q).1 h')⟩)
    | Sum.inr ⟨⟨Sum.inl p, hp⟩, w⟩ =>
        Sum.inl ⟨Sum.inr ⟨⟨p.1, (h.mem_left p).2 hp⟩, w⟩, by simp⟩
    | Sum.inr ⟨⟨Sum.inr q, hq⟩, w⟩ =>
        Sum.inr (Sum.inr ⟨⟨q, (h.mem_right q).2 hq⟩, w⟩)
  invFun
    | Sum.inl ⟨Sum.inl c, hc⟩ =>
        Sum.inl ⟨Sum.inl ⟨c.1, fun e => hc (by simp [Subtype.ext_iff, e])⟩,
          fun h' => c.2 ((h.mem_left _).2 h')⟩
    | Sum.inl ⟨Sum.inr ⟨c, w⟩, _⟩ =>
        Sum.inr ⟨⟨Sum.inl ⟨c.1,
            fun e => h.not_mem (Eq.subst (motive := (· ∈ L₁)) e c.2)⟩,
          (h.mem_left ⟨c.1, _⟩).1 c.2⟩, w⟩
    | Sum.inr (Sum.inl d) => Sum.inl ⟨Sum.inr d.1, fun h' => d.2 ((h.mem_right _).2 h')⟩
    | Sum.inr (Sum.inr ⟨d, w⟩) => Sum.inr ⟨⟨Sum.inr d.1, (h.mem_right _).1 d.2⟩, w⟩
  left_inv := by
    rintro (⟨(p | q), hp⟩ | ⟨⟨(p | q), hp⟩, w⟩) <;> rfl
  right_inv := by
    rintro (⟨(c | ⟨c, w⟩), hc⟩ | (d | ⟨d, w⟩)) <;> rfl

omit [Fintype P] [Fintype Q] [DecidableEq Q] in
/-- Inner inputs first, then outer ones.
@isnad1 id=splits.0h5v.s6.cc8c861e85f1 from=translated src=- shape=1cf41c23 vocab=4b8c60f6
-/
lemma splits_append {i : P} (L₁ : List (Without P i)) (L₂ : List Q) :
    Splits (L₂.map Sum.inr ++ L₁.map Sum.inl) (L₁.map Subtype.val) L₂ := by
  induction L₂ with
  | nil =>
    induction L₁ with
    | nil => exact Splits.nil
    | cons p L₁ ih => exact Splits.left p ih
  | cons q L₂ ih => exact Splits.right q ih

/-- **Filling the inputs of a composite is composing the filled operations** (the interchange
law): inserting operations at some inputs of `X ∘ᵢ Y`, in any order, is the composite of `X`
with those at its inputs inserted and `Y` with those at its inputs inserted.
@isnad1 id=eq.2h13v.s11.b4225f7a80df from=translated src=- shape=12646abc vocab=00d7d26b
-/
theorem fill_comp (i : P) (X : S P) (Y : S Q) (w₁ : (p : P) → S (W₁ p))
    (w₂ : (q : Q) → S (W₂ q)) {L : List (Without P i ⊕ Q)} {L₁ : List P} {L₂ : List Q}
    (h : Splits L L₁ L₂) (hL : L.Nodup) :
    fill (SetOperad.comp i X Y) (sumVal i w₁ w₂) L hL
      = SetOperad.map (interEquiv h).symm
          (SetOperad.comp (Sum.inl ⟨i, h.not_mem⟩ : Stage W₁ L₁)
            (fill X w₁ L₁ (h.nodup_left hL)) (fill Y w₂ L₂ (h.nodup_right hL))) := by
  induction h with
  | nil =>
    rw [fill_nil, fill_nil, fill_nil,
      comp_map_left (initEquiv W₁) i (Sum.inl ⟨i, List.not_mem_nil⟩ : Stage W₁ []) rfl,
      comp_map_right]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with p | q <;> rfl
  | left p h ih =>
    obtain ⟨hj, hL'⟩ := List.nodup_cons.1 hL
    have hp : p.1 ∉ _ := fun h' => hj ((h.mem_left p).1 h')
    have hik : (Sum.inl ⟨i, h.not_mem⟩ : Stage W₁ _) ≠ Sum.inl ⟨p.1, hp⟩ := by
      simp [Subtype.ext_iff, Ne.symm p.2]
    rw [fill_cons, fill_cons, ih hL',
      comp_map_left (interEquiv h).symm (Sum.inl ⟨Sum.inl ⟨p.1, hp⟩, Ne.symm hik⟩)
        (Sum.inl ⟨Sum.inl p, hj⟩ : Stage (sumFam W₁ W₂ i) _) rfl,
      comp_map_left (stepEquiv p.1 _ hp) (Sum.inl ⟨Sum.inl ⟨i, h.not_mem⟩, hik⟩)
        (Sum.inl ⟨i, (h.left p).not_mem⟩ : Stage W₁ (p.1 :: _)) rfl]
    erw [comp_par_eq hik]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(⟨(c | ⟨c, w⟩), hc⟩ | w), hw⟩ | (d | ⟨d, w⟩) <;> rfl
  | right q h ih =>
    obtain ⟨hj, hL'⟩ := List.nodup_cons.1 hL
    have hq : q ∉ _ := fun h' => hj ((h.mem_right q).1 h')
    rw [fill_cons, fill_cons, ih hL',
      comp_map_left (interEquiv h).symm (Sum.inr (Sum.inl ⟨q, hq⟩))
        (Sum.inl ⟨Sum.inr q, hj⟩ : Stage (sumFam W₁ W₂ i) _) rfl,
      comp_map_right]
    erw [comp_seq_eq]
    simp only [map_map]
    refine map_congr (fun s => ?_) _
    rcases s with ⟨(c | ⟨c, w⟩), hc⟩ | (⟨(d | ⟨d, w⟩), hd⟩ | w) <;> rfl

end Interchange

end May

open May

namespace SetOperad

section Total

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- **Total composition**: the operation `y a` inserted at every input `a` of `x`.-/
noncomputable def total (x : S A) (y : (a : A) → S (B a)) : S (Σ a, B a) :=
  map (finalEquiv B _ fun a => Finset.mem_toList.2 (Finset.mem_univ a))
    (fill x y (Finset.univ : Finset A).toList (Finset.nodup_toList _))

/-- **Total composition along any order of the inputs.**
@isnad1 id=eq.2h6v.s7.e61c91301db6 from=translated src=- shape=a95f7b41 vocab=30233516
-/
theorem total_eq_fill (x : S A) (y : (a : A) → S (B a)) (l : List A) (hl : l.Nodup)
    (hc : ∀ a, a ∈ l) : total x y = map (finalEquiv B l hc) (fill x y l hl) := by
  have hp : (Finset.univ : Finset A).toList.Perm l :=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hl).2 fun a => by simp [hc a]
  rw [total, ← fill_perm x y hp, map_map]
  refine map_congr (fun s => ?_) _
  rcases s with c | ⟨c, b⟩
  · exact absurd (Finset.mem_toList.2 (Finset.mem_univ _)) c.2
  · rfl

/-- **The right unit law of total composition**: inserting the unit at every input.
@isnad1 id=eq.0h3v.s6.bb898fc930ff from=translated src=- shape=d60f0790 vocab=214e7d4b
-/
theorem total_one_right (x : S A) :
    map (Equiv.sigmaPUnit A) (total x fun _ => (one : S Unit)) = x := by
  have hc : ∀ a, a ∈ (Finset.univ : Finset A).toList :=
    fun a => Finset.mem_toList.2 (Finset.mem_univ a)
  obtain ⟨e, he, hx⟩ := fill_one x _ (Finset.nodup_toList (Finset.univ : Finset A))
  rw [total_eq_fill _ _ _ (Finset.nodup_toList _) hc, hx, map_map, map_map]
  refine (map_congr (e' := Equiv.refl A) (fun a => ?_) x).trans (map_refl x)
  have h := he a
  revert h
  simp only [Equiv.trans_apply, Equiv.refl_apply]
  rcases e a with c | ⟨c, u⟩
  · exact absurd (hc c.1) c.2
  · exact id

end Total

section TotalUnit

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {E : Unit → Type} [∀ u, Fintype (E u)] [∀ u, DecidableEq (E u)]

/-- **The left unit law of total composition**: inserting an operation into the unit.
@isnad1 id=eq.0h3v.s7.e5af1c673dc7 from=translated src=- shape=fd98a81c vocab=f3b3243a
-/
theorem total_one_left (y : (u : Unit) → S (E u)) :
    map (Equiv.uniqueSigma E) (total one y) = y () := by
  rw [total_eq_fill one y [()] (List.nodup_singleton _) (fun u => List.mem_singleton.2 rfl),
    fill_cons, fill_nil,
    comp_map_left (initEquiv E) () (Sum.inl ⟨(), List.not_mem_nil⟩ : Stage E []) rfl,
    one_comp_eq]
  simp only [map_map]
  refine (map_congr (e' := Equiv.refl (E ())) (fun b => ?_) _).trans (map_refl _)
  rfl

end TotalUnit

end SetOperad

namespace May

section Assoc

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)] {C : (a : A) → B a → Type} [∀ a b, Fintype (C a b)]
  [∀ a b, DecidableEq (C a b)]

/-- **The inputs of the operations inserted at a stage**: those of `z a b` at an input `b` of
`y a`, and a single one at the inputs not filled yet.-/
def lowFam (C : (a : A) → B a → Type) (l : List A) : Stage B l → Type
  | Sum.inl _ => Unit
  | Sum.inr p => C p.1.1 p.2

instance (l : List A) (s : Stage B l) : Fintype (lowFam C l s) :=
  match s with
  | Sum.inl _ => inferInstanceAs (Fintype Unit)
  | Sum.inr p => inferInstanceAs (Fintype (C p.1.1 p.2))

instance (l : List A) (s : Stage B l) : DecidableEq (lowFam C l s) :=
  match s with
  | Sum.inl _ => inferInstanceAs (DecidableEq Unit)
  | Sum.inr p => inferInstanceAs (DecidableEq (C p.1.1 p.2))

/-- The operations inserted at a stage: `z a b` at an input `b` of `y a`, the unit elsewhere.-/
def lowVal (z : (a : A) → (b : B a) → S (C a b)) (l : List A) :
    (s : Stage B l) → S (lowFam C l s)
  | Sum.inl _ => SetOperad.one
  | Sum.inr p => z p.1.1 p.2

/-- **The inputs after filling all the inputs coming from the inserted operations**, against
those of the stage with the total composites inserted.-/
def assocEquiv (l : List A) (L : List (Stage B l)) (hL : ∀ s, s ∈ L ↔ s.isRight = true) :
    Stage (lowFam C l) L ≃ Stage (fun a => Σ b, C a b) l where
  toFun
    | Sum.inl ⟨Sum.inl c, _⟩ => Sum.inl c
    | Sum.inl ⟨Sum.inr _, h⟩ => absurd ((hL _).2 rfl) h
    | Sum.inr ⟨⟨Sum.inl _, h⟩, _⟩ => absurd ((hL _).1 h) (by simp)
    | Sum.inr ⟨⟨Sum.inr p, _⟩, w⟩ => Sum.inr ⟨p.1, ⟨p.2, w⟩⟩
  invFun
    | Sum.inl c => Sum.inl ⟨Sum.inl c, fun h => by simpa using (hL _).1 h⟩
    | Sum.inr ⟨a, ⟨b, w⟩⟩ => Sum.inr ⟨⟨Sum.inr ⟨a, b⟩, (hL _).2 rfl⟩, w⟩
  left_inv := by
    rintro (⟨(c | p), h⟩ | ⟨⟨(c | p), h⟩, w⟩)
    · rfl
    · exact absurd ((hL _).2 rfl) h
    · exact absurd ((hL _).1 h) (by simp)
    · rfl
  right_inv := by
    rintro (c | ⟨a, ⟨b, w⟩⟩) <;> rfl

/-- At a step, the inputs of the inserted operations agree on both sides.-/
def lowStep (a : A) (l : List A) (ha : a ∉ l) :
    (t : Without (Stage B l) (Sum.inl ⟨a, ha⟩) ⊕ B a) →
      sumFam (lowFam C l) (C a) (Sum.inl ⟨a, ha⟩) t ≃
        lowFam C (a :: l) (stepEquiv a l ha t)
  | Sum.inl ⟨Sum.inl _, _⟩ => Equiv.refl _
  | Sum.inl ⟨Sum.inr _, _⟩ => Equiv.refl _
  | Sum.inr _ => Equiv.refl _

end Assoc

end May

namespace SetOperad

section Assoc

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)] {C : (a : A) → B a → Type} [∀ a b, Fintype (C a b)]
  [∀ a b, DecidableEq (C a b)]

/-- The inputs of the operations inserted after a total composition.-/
private def lowFinal (l : List A) (hc : ∀ a, a ∈ l) :
    (s : Stage B l) → lowFam C l s ≃ C (finalEquiv B l hc s).1 (finalEquiv B l hc s).2
  | Sum.inl c => absurd (hc c.1) c.2
  | Sum.inr _ => Equiv.refl _

end Assoc

end SetOperad

namespace May

section FillCongr

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
  {A : Type} [Fintype A] [DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

/-- **Filling only uses the operations inserted at the inputs filled.**
@isnad1 id=eq.2h7v.s7.5a65883e32b5 from=translated src=- shape=b2be2bd3 vocab=5556dcee
-/
theorem fill_congr (x : S A) {y y' : (a : A) → S (B a)} (l : List A) (hl : l.Nodup)
    (h : ∀ a ∈ l, y a = y' a) : fill x y l hl = fill x y' l hl := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [fill_cons, fill_cons, ih _ fun b hb => h b (List.mem_cons_of_mem a hb),
      h a List.mem_cons_self]

/-- The inputs other than `a`, in some order.-/
noncomputable def others (a : A) : List A := (Finset.univ.erase a).toList

/--
@isnad1 id=nodup.0h2v.s4.fcb6d516df69 from=translated src=- shape=d671e702 vocab=480126d4
-/
lemma others_nodup (a : A) : (a :: others a).Nodup :=
  List.nodup_cons.2 ⟨by simp [others], Finset.nodup_toList _⟩

/--
@isnad1 id=mem.0h3v.s4.ec34c5b09fd8 from=translated src=- shape=8a0b9703 vocab=ba91e8c6
-/
lemma mem_others (a b : A) : b ∈ a :: others a := by
  by_cases h : b = a
  · exact h ▸ List.mem_cons_self
  · exact List.mem_cons_of_mem a (by simp [others, h])

/-- **Total composition with the input `a` filled last.**
@isnad1 id=eq.0h6v.s11.063a12b97f69 from=translated src=- shape=9a2fccc9 vocab=1ee6d29e
-/
theorem total_eq_comp (x : S A) (y : (a : A) → S (B a)) (a : A) :
    SetOperad.total x y = SetOperad.map
      ((stepEquiv a (others a) (List.nodup_cons.1 (others_nodup a)).1).trans
        (finalEquiv B _ (mem_others a)))
      (SetOperad.comp
        (Sum.inl ⟨a, (List.nodup_cons.1 (others_nodup a)).1⟩ : Stage B (others a))
        (fill x y (others a) (List.nodup_cons.1 (others_nodup a)).2) (y a)) := by
  rw [SetOperad.total_eq_fill x y _ (others_nodup a) (mem_others a), fill_cons, map_map]

end FillCongr

end May

namespace SymOperad

open SetOperad

variable {R : Type u} [CommRing R] {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]
  {A : Type} [Fintype A] [hA : DecidableEq A] {B : A → Type} [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]

variable (R) in
/-- **Filling** in an operad in modules: that of its underlying set operad.-/
noncomputable def fill (x : Q A) (y : (a : A) → Q (B a)) (l : List A) (hl : l.Nodup) :
    Q (Stage B l) :=
  (Und.of R Q).symm (May.fill (S := Und R Q) (Und.of R Q x) (fun a => Und.of R Q (y a)) l hl)

/--
@isnad1 id=eq.1h6v.s9.e6bad0b4df05 from=translated src=- shape=2f5153c7 vocab=73f1ea7b
-/
lemma fill_nil (x : Q A) (y : (a : A) → Q (B a)) (h : ([] : List A).Nodup) :
    fill R x y [] h = map (R := R) (initEquiv B) x := rfl

/--
@isnad1 id=eq.1h8v.s17.7488c5403f20 from=translated src=- shape=ac2b21a3 vocab=64ec59fc
-/
lemma fill_cons (x : Q A) (y : (a : A) → Q (B a)) (a : A) (l : List A) (h : (a :: l).Nodup) :
    fill R x y (a :: l) h = map (R := R) (stepEquiv a l (List.nodup_cons.1 h).1)
      (comp (R := R) (Sum.inl ⟨a, (List.nodup_cons.1 h).1⟩ : Stage B l)
        (fill R x y l (List.nodup_cons.1 h).2) (y a)) := rfl

variable (R) in
/-- **Total composition** in an operad in modules: that of its underlying set operad.-/
noncomputable def total (x : Q A) (y : (a : A) → Q (B a)) : Q (Σ a, B a) :=
  (Und.of R Q).symm (SetOperad.total (S := Und R Q) (Und.of R Q x) fun a => Und.of R Q (y a))

/-- Filling, in an operad in modules, is linear in the outer operation.
@isnad1 id=eq.1h8v.s9.e03909cc34c9 from=translated src=- shape=025f38fa vocab=87dd873f
-/
lemma fill_add (x x' : Q A) (y : (a : A) → Q (B a)) (l : List A) (hl : l.Nodup) :
    fill R (x + x') y l hl = fill R x y l hl + fill R x' y l hl := by
  induction l with
  | nil => exact (map (R := R) (initEquiv B)).map_add x x'
  | cons a l ih =>
    rw [fill_cons, fill_cons, fill_cons, ih, map_add, LinearMap.add_apply, map_add]

/-- Filling, in an operad in modules, is linear in the outer operation.
@isnad1 id=eq.1h8v.s10.2e2524b8d485 from=translated src=- shape=4c832d58 vocab=65284d42
-/
lemma fill_smul (c : R) (x : Q A) (y : (a : A) → Q (B a)) (l : List A) (hl : l.Nodup) :
    fill R (c • x) y l hl = c • fill R x y l hl := by
  induction l with
  | nil => exact (map (R := R) (initEquiv B)).map_smul c x
  | cons a l ih =>
    rw [fill_cons, fill_cons, ih, map_smul, LinearMap.smul_apply, map_smul]

/--
@isnad1 id=eq.2h7v.s9.938c00d93ba3 from=translated src=- shape=a2b7736d vocab=6dbee03f
-/
lemma total_eq_fill (x : Q A) (y : (a : A) → Q (B a)) (l : List A) (hl : l.Nodup)
    (hc : ∀ a, a ∈ l) : total R x y = map (R := R) (finalEquiv B l hc) (fill R x y l hl) :=
  SetOperad.total_eq_fill (S := Und R Q) _ _ l hl hc

/-- **Total composition is linear in the outer operation.**
@isnad1 id=eq.0h7v.s9.734e3d437754 from=translated src=- shape=f9c73488 vocab=6e1bbbfd
-/
theorem total_add (x x' : Q A) (y : (a : A) → Q (B a)) :
    total R (x + x') y = total R x y + total R x' y := by
  rw [total_eq_fill _ y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a),
    total_eq_fill x y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a),
    total_eq_fill x' y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a), fill_add, map_add]

/-- **Total composition is linear in the outer operation.**
@isnad1 id=eq.0h7v.s10.41ac4f1b442a from=translated src=- shape=a91e9f14 vocab=cb1d1722
-/
theorem total_smul (c : R) (x : Q A) (y : (a : A) → Q (B a)) :
    total R (c • x) y = c • total R x y := by
  rw [total_eq_fill _ y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a),
    total_eq_fill x y _ (Finset.nodup_toList Finset.univ)
      fun a => Finset.mem_toList.2 (Finset.mem_univ a), fill_smul, map_smul]

/-- Total composition with one inserted operation varying.
@isnad1 id=eq.0h8v.s17.d43920ecc9d1 from=translated src=- shape=92c4914c vocab=3ee9f7a8
-/
lemma total_update (x : Q A) (y : (a : A) → Q (B a)) (a : A) (v : Q (B a)) :
    total R x (Function.update y a v)
      = map (R := R) ((stepEquiv a (others a) (List.nodup_cons.1 (others_nodup a)).1).trans
          (finalEquiv B _ (mem_others a)))
        (comp (R := R)
          (Sum.inl ⟨a, (List.nodup_cons.1 (others_nodup a)).1⟩ : Stage B (others a))
          (fill R x y (others a) (List.nodup_cons.1 (others_nodup a)).2) v) := by
  have := May.total_eq_comp (S := Und R Q) (Und.of R Q x)
    (fun b => Und.of R Q (Function.update y a v b)) a
  refine this.trans ?_
  congr 2
  · exact May.fill_congr _ _ _ fun b hb => by
      have hba : b ≠ a := by
        rintro rfl
        exact (List.nodup_cons.1 (others_nodup b)).1 hb
      exact Function.update_of_ne hba v y
  · exact Function.update_self a v y

/-- **Total composition is multilinear in the inserted operations.**
@isnad1 id=eq.0h9v.s9.df7d8edefc57 from=translated src=- shape=ee7307af vocab=e2f5ff72
-/
theorem total_update_add (x : Q A) (y : (a : A) → Q (B a)) (a : A) (v v' : Q (B a)) :
    total R x (Function.update y a (v + v'))
      = total R x (Function.update y a v) + total R x (Function.update y a v') := by
  rw [total_update, total_update, total_update, map_add, map_add]

/-- **Total composition is multilinear in the inserted operations.**
@isnad1 id=eq.0h9v.s10.71eb8f38716a from=translated src=- shape=755fec71 vocab=7b5d0896
-/
theorem total_update_smul (x : Q A) (y : (a : A) → Q (B a)) (a : A) (c : R) (v : Q (B a)) :
    total R x (Function.update y a (c • v)) = c • total R x (Function.update y a v) := by
  rw [total_update, total_update, map_smul, map_smul]

variable (R) in
/-- **Total composition as a multilinear map** of the inserted operations.-/
noncomputable def totalML (x : Q A) : MultilinearMap R (fun a => Q (B a)) (Q (Σ a, B a)) where
  toFun y := total R x y
  map_update_add' := by
    intro d y a v v'
    obtain rfl : d = hA := Subsingleton.elim _ _
    exact total_update_add x y a v v'
  map_update_smul' := by
    intro d y a c v
    obtain rfl : d = hA := Subsingleton.elim _ _
    exact total_update_smul x y a c v

variable (R) in
/-- **Total composition**, linear in the outer operation and multilinear in the inserted ones.-/
noncomputable def totalL : Q A →ₗ[R] MultilinearMap R (fun a => Q (B a)) (Q (Σ a, B a)) where
  toFun := totalML R
  map_add' x x' := MultilinearMap.ext fun y => total_add x x' y
  map_smul' c x := MultilinearMap.ext fun y => total_smul c x y

/-! ### May's axioms in an operad in modules -/

/-- **The right unit law of total composition** in an operad in modules.
@isnad1 id=eq.0h4v.s9.b8a8a173729e from=translated src=- shape=f9f29b1c vocab=caa4ae70
-/
theorem total_one_right (x : Q A) :
    map (R := R) (Equiv.sigmaPUnit A) (total R x fun _ => (one R : Q Unit)) = x :=
  SetOperad.total_one_right (S := Und R Q) x

/-- **The left unit law of total composition** in an operad in modules.
@isnad1 id=eq.0h4v.s9.940d7753f605 from=translated src=- shape=bd52bb31 vocab=286b7cd4
-/
theorem total_one_left {E : Unit → Type} [∀ u, Fintype (E u)] [∀ u, DecidableEq (E u)]
    (y : (u : Unit) → Q (E u)) :
    map (R := R) (Equiv.uniqueSigma E) (total R (one R) y) = y () :=
  SetOperad.total_one_left (S := Und R Q) y

end SymOperad

end Operad
