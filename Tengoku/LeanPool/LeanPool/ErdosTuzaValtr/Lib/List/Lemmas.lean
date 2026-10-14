/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ErdosTuzaValtr.Lib.List.Defs

/-!
# LeanPool.ErdosTuzaValtr.Lib.List.Lemmas

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Lib.List.Lemmas`.
-/

@[expose] public section

variable {α : Type _}

section ListIn

/--
@isnad1 id=in.2h4v.s5.5771b5aa5383 from=translated src=- shape=cc435a3d vocab=0c699f51
-/
theorem List.in_superset {l : List α} {S T : Finset α} (h : S ⊆ T) : l.In S → l.In T :=
  fun l_in_S _ al => h (l_in_S _ al)

/--
@isnad1 id=in.2h4v.s4.e57180a290ea from=translated src=- shape=37443c93 vocab=e7b5ef10
-/
theorem List.subset_in {l1 l2 : List α} {S : Finset α} (h : l1 ⊆ l2) (h_l2 : l2.In S) : l1.In S :=
  fun a ha => h_l2 a (h ha)

/--
@isnad1 id=in.0h2v.s3.7d0e9f70c1e2 from=translated src=- shape=a73e189b vocab=ea23032f
-/
@[simp]
theorem List.nil_in {S : Finset α} : [].In S := by simp [List.In]

/--
@isnad1 id=iff.0h4v.s5.80ee7c313845 from=translated src=- shape=bf0412fd vocab=5de3af71
-/
@[simp]
theorem List.cons_in {a : α} {l : List α} {S : Finset α} : (a :: l).In S ↔ a ∈ S ∧ l.In S := by
  simp [List.In]

/--
@isnad1 id=iff.0h4v.s5.954711f4d0cf from=translated src=- shape=5edfa601 vocab=5d86f605
-/
@[simp]
theorem List.append_in {l1 l2 : List α} {S : Finset α} : (l1 ++ l2).In S ↔ l1.In S ∧ l2.In S := by
  constructor
  · intro h
    refine ⟨fun a al1 => ?_, fun a al2 => ?_⟩
    · exact h a (List.mem_append_left l2 al1)
    · exact h a (List.mem_append_right l1 al2)
  · rintro ⟨h1, h2⟩ a al12
    rw [List.mem_append] at al12
    rcases al12 with al1 | al2
    · exact h1 a al1
    · exact h2 a al2

/--
@isnad1 id=iff.0h3v.s4.dc8e2b028713 from=translated src=- shape=d1aa4cb8 vocab=425270f6
-/
@[simp]
theorem List.reverse_in {l : List α} {S : Finset α} : l.reverse.In S ↔ l.In S := by simp [List.In]

end ListIn

/--
@isnad1 id=eq.0h2v.s4.f2a01ed22641 from=translated src=- shape=d82fd520 vocab=81c9f96a
-/
theorem List.reverse_getLast {l : List α} : l.reverse.getLast? = l.head? := by cases l <;> simp

/--
@isnad1 id=eq.0h2v.s4.824e76dd5ce2 from=translated src=- shape=d82fd520 vocab=81c9f96a
-/
theorem List.reverse_head {l : List α} : l.reverse.head? = l.getLast? := by
  convert List.reverse_getLast.symm; simp

section Mirror

open OrderDual

/--
@isnad1 id=eq.0h1v.s3.1a9b44fb468d from=translated src=- shape=54ac7aa7 vocab=01d71837
-/
@[simp]
theorem List.Mirror_nil : ([] : List α).Mirror = [] :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.f6b36f535112 from=translated src=- shape=5fc8b653 vocab=b2c43e09
-/
@[simp]
theorem List.Mirror_singleton {a : α} : [a].Mirror = [toDual a] :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.774349ac9d04 from=translated src=- shape=5477ed18 vocab=53801c71
-/
@[simp]
theorem List.Mirror_cons {a : α} {l : List α} : (a :: l).Mirror = l.Mirror ++ [toDual a] := by
  simp [List.Mirror]

/--
@isnad1 id=eq.0h3v.s5.b280190f95a0 from=translated src=- shape=6a588f17 vocab=1aefdb5e
-/
@[simp]
theorem List.Mirror_append {l1 l2 : List α} : (l1 ++ l2).Mirror = l2.Mirror ++ l1.Mirror := by
  simp [List.Mirror]

/--
@isnad1 id=eq.0h1v.s3.9b9016f0858b from=translated src=- shape=c1167d68 vocab=73403690
-/
@[simp]
theorem List.ofMirror_nil : ([] : List αᵒᵈ).ofMirror = [] :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.120d6fb5aab4 from=translated src=- shape=9bcc0c0c vocab=e2d10d1d
-/
@[simp]
theorem List.ofMirrorMirror {l : List αᵒᵈ} : l.ofMirror.Mirror = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.ofMirror, List.Mirror] at ih ⊢
    simp_all

/--
@isnad1 id=eq.0h2v.s4.45c19bbc89b8 from=translated src=- shape=72570f23 vocab=d53ace36
-/
@[simp]
theorem Finset.ofMirrorMirror [LinearOrder α] {S : Finset αᵒᵈ} : S.ofMirror.Mirror = S :=
  by
  rw [Finset.ofMirror, Finset.Mirror]
  rw [Finset.image_image]
  simp only [Function.comp_def, OrderDual.toDual_ofDual, Finset.image_id']

/--
@isnad1 id=eq.0h2v.s4.53fd1e04f277 from=translated src=- shape=7b7f08c2 vocab=1acdab6a
-/
@[simp]
theorem List.Mirror_length {l : List α} : l.Mirror.length = l.length := by rw [List.Mirror]; simp

/--
@isnad1 id=iff.0h2v.s6.2ca78e970079 from=translated src=- shape=ef84248d vocab=da6e2da6
-/
theorem List.chain'_mirror [LinearOrder α] {l : List α} :
    List.IsChain (· < ·) l.Mirror ↔ List.IsChain (· < ·) l := by
  simp_rw [List.Mirror, List.isChain_reverse, List.isChain_map, toDual_lt_toDual]

/--
@isnad1 id=eq.0h2v.s5.1491fd7e3b94 from=translated src=- shape=31ceda68 vocab=436f10f2
-/
theorem List.Mirror_getLast {l : List α} : l.Mirror.getLast? = Option.map toDual l.head? := by
  rw [List.Mirror, List.reverse_getLast, List.head?_map]

/--
@isnad1 id=eq.0h2v.s5.51189f0c8ab8 from=translated src=- shape=31ceda68 vocab=436f10f2
-/
theorem List.Mirror_head {l : List α} : l.Mirror.head? = Option.map toDual l.getLast? := by
  rw [List.Mirror, List.reverse_head, List.getLast?_map]

/--
@isnad1 id=eq.0h2v.s5.5fbc4917616f from=translated src=- shape=97af617e vocab=19ff1e4b
-/
theorem List.ofMirror_getLast {l : List αᵒᵈ} :
    l.ofMirror.getLast? = Option.map ofDual l.head? := by
  rw [List.ofMirror, List.reverse_getLast, List.head?_map]

/--
@isnad1 id=eq.0h2v.s5.e0959ededd95 from=translated src=- shape=97af617e vocab=19ff1e4b
-/
theorem List.ofMirror_head {l : List αᵒᵈ} :
    l.ofMirror.head? = Option.map ofDual l.getLast? := by
  rw [List.ofMirror, List.reverse_head, List.getLast?_map]

/--
@isnad1 id=iff.0h3v.s5.170b0e99e55f from=translated src=- shape=56ed0a60 vocab=2b4df70a
-/
theorem List.Mirror_mem_getLast {a : α} {l : List α} :
    toDual a ∈ l.Mirror.getLast? ↔ a ∈ l.head? := by
  rw [List.Mirror_getLast, Option.mem_map_of_injective toDual.injective]

/--
@isnad1 id=iff.0h3v.s5.cd5984fa61c9 from=translated src=- shape=56ed0a60 vocab=2b4df70a
-/
theorem List.Mirror_mem_head {a : α} {l : List α} :
    toDual a ∈ l.Mirror.head? ↔ a ∈ l.getLast? := by
  rw [List.Mirror_head, Option.mem_map_of_injective toDual.injective]

/--
@isnad1 id=iff.0h3v.s4.457164a7c438 from=translated src=- shape=1fc5b723 vocab=d6786d96
-/
@[simp]
theorem List.Mirror_in [LinearOrder α] {l : List α} {S : Finset α} :
    l.Mirror.In S.Mirror ↔ l.In S := by
  rw [List.Mirror]; simp; constructor <;> simp [List.In, Finset.Mirror]

/--
@isnad1 id=iff.0h3v.s6.6fd906428b0a from=translated src=- shape=0cf4d3fa vocab=dc77df30
-/
@[simp]
theorem Finset.memMirror [LinearOrder α] {a : α} {S : Finset α} : toDual a ∈ S.Mirror ↔ a ∈ S := by
  simp [Finset.Mirror]

/--
@isnad1 id=eq.0h2v.s4.de68304852b7 from=translated src=- shape=081d62cf vocab=ab0d575f
-/
@[simp]
theorem Finset.Mirror_card [LinearOrder α] {S : Finset α} : S.Mirror.card = S.card :=
  by
  rw [Finset.Mirror]
  apply S.card_image_of_injective
  intro a b; simp

end Mirror

/--
@isnad1 id=eq.0h5v.s5.d217a1ddb733 from=translated src=- shape=0e11b8b5 vocab=6071cf5d
-/
@[simp]
theorem List.getLast?_cons_append_cons (a b : α) (l1 l2 : List α) :
    (a :: (l1 ++ b :: l2)).getLast? = (b :: l2).getLast? := by
  induction l1 generalizing a with
  | nil => simp only [nil_append, getLast?_cons_cons]
  | cons c l1 ih =>
    simp_all

/-- Split off the head of a list given a witness that `a` is its head. -/
def List.takeHead' {a : α} : ∀ {l : List α} (_ : a ∈ l.head?), Σ' t, l = a :: t
  | [], h => absurd h (Option.not_mem_none a)
  | b :: t, h => ⟨t, by rw [List.head?_cons, Option.mem_some_iff] at h; rw [h]⟩

/-- Split a nonempty list into its head and tail. -/
def List.takeHead : ∀ {l : List α}, l ≠ [] → Σ' (h1 : α) (t : List α), l = h1 :: t
  | [], h => absurd rfl h
  | h1 :: t, _ => ⟨h1, t, rfl⟩

/-- Split a list of length at least 2 into its first two elements and the rest. -/
def List.takeHead2 : ∀ {l : List α}, 2 ≤ l.length → Σ' (h1 h2 : α) (t : List α), l = h1 :: h2 :: t
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [_], h => absurd h (Bool.of_decide_false rfl)
  | a :: b :: t, _ => ⟨a, b, t, rfl⟩

/-- Split a list of length at least 3 into its first three elements and the rest. -/
def List.takeHead3 :
    ∀ {l : List α}, 3 ≤ l.length → Σ' (h1 h2 h3 : α) (t : List α), l = h1 :: h2 :: h3 :: t
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [_], h => absurd h (Bool.of_decide_false rfl)
  | [_, _], h => absurd h (Bool.of_decide_false rfl)
  | a :: b :: c :: t, _ => ⟨a, b, c, t, rfl⟩

/-- Split off the last element of a list given a witness that `a` is its last element. -/
def List.takeLast' {a : α} : ∀ {l : List α} (_ : a ∈ l.getLast?), Σ' l', l = l' ++ [a]
  | [], h => absurd h (Option.not_mem_none a)
  | [b], h => ⟨[], by
      rw [List.getLast?_singleton, Option.mem_some_iff] at h; rw [h, nil_append]⟩
  | b :: c :: t, h =>
    let h' : a ∈ (c :: t).getLast? := by
      rw [List.getLast?_cons_cons] at h; exact h
    let ⟨l'', hl''⟩ := List.takeLast' h'
    ⟨b :: l'', by simp only [cons_append, cons.injEq, true_and]; exact hl''⟩

/-- Split a nonempty list into its last element and the preceding prefix. -/
def List.takeLast : ∀ {l : List α}, l ≠ [] → Σ' (e1 : α) (m : List α), l = m ++ [e1]
  | [], h => absurd rfl h
  | [a], _ => ⟨a, [], rfl⟩
  | a :: b :: rest, _ =>
    let h : b :: rest ≠ [] := List.cons_ne_nil b rest
    let ⟨e1, m', eq_l'⟩ := List.takeLast h
    ⟨e1, a :: m', congr_arg (List.cons a) eq_l'⟩

/-- Split a list of length at least 2 into its last two elements and the preceding prefix. -/
def List.takeLast2 : ∀ {l : List α}, 2 ≤ l.length → Σ' (e1 e2 : α) (m : List α), l = m ++ [e1, e2]
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [_], h => absurd h (Bool.of_decide_false rfl)
  | [a, b], _ => ⟨a, b, [], rfl⟩
  | a :: b :: c :: t, _ =>
    let h : 2 ≤ (b :: c :: t).length := (2 : ℕ).le_add_left (List.length t)
    let ⟨e1, e2, m', eq_l'⟩ := List.takeLast2 h
    ⟨e1, e2, a :: m', congr_arg (List.cons a) eq_l'⟩

/-- Split a list of length at least 3 into its last three elements and the preceding prefix. -/
def List.takeLast3 :
    ∀ {l : List α}, 3 ≤ l.length → Σ' (e1 e2 e3 : α) (m : List α), l = m ++ [e1, e2, e3]
  | [], h => absurd h (Bool.of_decide_false rfl)
  | [_], h => absurd h (Bool.of_decide_false rfl)
  | [_, _], h => absurd h (Bool.of_decide_false rfl)
  | [a, b, c], _ => ⟨a, b, c, [], rfl⟩
  | a :: b :: c :: d :: t, _ =>
    let h : 3 ≤ (b :: c :: d :: t).length := (3 : ℕ).le_add_left (List.length t)
    let ⟨e1, e2, e3, m', eq_l'⟩ := List.takeLast3 h
    ⟨e1, e2, e3, a :: m', congr_arg (List.cons a) eq_l'⟩
