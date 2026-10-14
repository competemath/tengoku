/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/
module

public import Tengoku.LeanPool.LeanPool.ErdosTuzaValtr.Lib.List.Defs

/-!
# LeanPool.ErdosTuzaValtr.Lib.List.Chain3

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Lib.List.Chain3`.
-/

@[expose] public section

variable {α : Type _} {R : α → α → α → Prop}

namespace List

/--
@isnad1 id=iff.0h8v.s6.363eba9167d5 from=translated src=- shape=717295a0 vocab=9c9d9bc8
-/
theorem chain3_split {a b c d : α} {l1 l2 : List α} :
    Chain3 R a b (l1 ++ c :: d :: l2) ↔ Chain3 R a b (l1 ++ [c, d]) ∧ Chain3 R c d l2 := by
  induction l1 generalizing a b with
  | nil => simp only [nil_append, chain3_cons, Chain3.nil, and_true, and_assoc]
  | cons x l1 IH => simp only [cons_append, chain3_cons, IH, and_assoc]

/--
@isnad1 id=iff.0h9v.s6.bc0b8f4f1df8 from=translated src=- shape=a1d5409d vocab=9c9d9bc8
-/
@[simp]
theorem chain3_append_cons3 {a b c d e : α} {l1 l2 : List α} :
    Chain3 R a b (l1 ++ c :: d :: e :: l2) ↔
      Chain3 R a b (l1 ++ [c, d]) ∧ R c d e ∧ Chain3 R d e l2 :=
  by rw [chain3_split, chain3_cons]

/--
@isnad1 id=chain3.0h2v.s3.169c419dc7e6 from=translated src=- shape=2c1b15f1 vocab=05e2ee4a
-/
@[simp]
theorem chain3'_nil : Chain3' R [] :=
  trivial

/--
@isnad1 id=chain3.0h3v.s4.62b6f56070cc from=translated src=- shape=76009fd5 vocab=996086f3
-/
@[simp]
theorem chain3'_singleton (a : α) : Chain3' R [a] :=
  trivial

/--
@isnad1 id=chain3.0h4v.s4.3cc98081ecd9 from=translated src=- shape=0c4e22ee vocab=996086f3
-/
@[simp]
theorem chain3'_pair (a b : α) : Chain3' R [a, b] :=
  Chain3.nil

/--
@isnad1 id=iff.0h6v.s5.e63ab29a094a from=translated src=- shape=7e37bcc1 vocab=b2b84a36
-/
@[simp]
theorem chain3'_cons {x y z l} : Chain3' R (x :: y :: z :: l) ↔ R x y z ∧ Chain3' R (y :: z :: l) :=
  chain3_cons

/--
@isnad1 id=iff.0h6v.s6.5976268aef07 from=translated src=- shape=632497c5 vocab=9fca6835
-/
theorem chain3'_split {a b : α} :
    ∀ {l1 l2 : List α},
      Chain3' R (l1 ++ a :: b :: l2) ↔ Chain3' R (l1 ++ [a, b]) ∧ Chain3' R (a :: b :: l2)
  | [], l2 => (and_iff_right (chain3'_pair a b)).symm
  | [c], l2 => by simp
  | c :: d :: l1, l2 => chain3_split

/--
@isnad1 id=iff.0h7v.s6.14532e77bd9e from=translated src=- shape=a8263d60 vocab=9fca6835
-/
@[simp]
theorem chain3'_append_cons3 {a b c : α} {l1 l2 : List α} :
    Chain3' R (l1 ++ a :: b :: c :: l2) ↔
      Chain3' R (l1 ++ [a, b]) ∧ R a b c ∧ Chain3' R (b :: c :: l2) :=
  by rw [chain3'_split, chain3'_cons]

namespace Chain3'

/--
@isnad1 id=chain3.1h4v.s5.2ac8f966161a from=translated src=- shape=046db7f9 vocab=5a311c97
-/
theorem left_of_append {l1 l2 : List α} (h : Chain3' R (l1 ++ l2)) : Chain3' R l1 := by
  induction l1 with
  | nil => simp only [chain3'_nil]
  | cons a l1 ih =>
    cases l1 with
    | nil => simp only [chain3'_singleton]
    | cons b l1 =>
      cases l1 with
      | nil => simp only [chain3'_pair]
      | cons c l1 =>
        simp_all

/--
@isnad1 id=chain3.1h4v.s5.aa6439e24255 from=translated src=- shape=e5b67f11 vocab=5a311c97
-/
theorem right_of_append {l1 l2 : List α} (h : Chain3' R (l1 ++ l2)) : Chain3' R l2 := by
  induction l1 generalizing l2 with
  | nil => exact h
  | cons a l1 ih =>
    cases l1 with
    | nil =>
      cases l2 with
      | nil => simp only [chain3'_nil]
      | cons c l2 =>
        cases l2 with
        | nil => simp only [chain3'_singleton]
        | cons d l2 =>
          simp_all
    | cons b l1 =>
      cases l1 with
      | nil =>
        cases l2 with
        | nil => simp only [chain3'_nil]
        | cons d l2 =>
          simp_all
      | cons c l1 =>
        simp_all

theorem «infix» {l₁ l : List α} (h : Chain3' R l) (h' : l₁ <:+: l) : Chain3' R l₁ := by
  rcases h' with ⟨l₂, l₃, rfl⟩; exact h.left_of_append.right_of_append

/--
@isnad1 id=chain3.2h4v.s4.44f93eca1f5a from=translated src=- shape=c313d849 vocab=a7a9e7f3
-/
theorem suffix {l₁ l : List α} (h : Chain3' R l) (h' : l₁ <:+ l) : Chain3' R l₁ :=
  h.«infix» h'.isInfix

theorem «prefix» {l₁ l : List α} (h : Chain3' R l) (h' : l₁ <+: l) : Chain3' R l₁ :=
  h.«infix» h'.isInfix

/--
@isnad1 id=chain3.1h4v.s4.ec9728ebe093 from=translated src=- shape=e5fbfae6 vocab=0e9d8648
-/
theorem drop {l : List α} (h : Chain3' R l) (n : ℕ) : Chain3' R (List.drop n l) :=
  h.suffix (drop_suffix _ _)

/--
@isnad1 id=chain3.1h3v.s4.2acce1d598b1 from=translated src=- shape=cc53954a vocab=53e63134
-/
theorem dropLast {l : List α} (h : Chain3' R l) : Chain3' R l.dropLast :=
  h.«prefix» l.dropLast_prefix

/--
@isnad1 id=chain3.1h4v.s4.1ca7fa847f35 from=translated src=- shape=e5fbfae6 vocab=0ea318ba
-/
theorem take {l : List α} (h : Chain3' R l) (n : ℕ) : Chain3' R (List.take n l) :=
  h.«prefix» (take_prefix _ _)

/--
@isnad1 id=chain3.1h3v.s4.9ba47cddac43 from=translated src=- shape=cc53954a vocab=8303c29b
-/
theorem tail {l : List α} (h : Chain3' R l) : Chain3' R l.tail := by
  cases l with
  | nil => simp only [List.tail_nil, chain3'_nil]
  | cons a l =>
    cases l with
    | nil => simp only [List.tail_cons, chain3'_nil]
    | cons b l =>
      cases l with
      | nil => simp only [List.tail_cons, chain3'_singleton]
      | cons c l =>
        simp_all

end Chain3'

/--
@isnad1 id=iff.0h3v.s4.6d37b5312ea4 from=translated src=- shape=eb9bca38 vocab=74bbcf56
-/
theorem chain3'_mirror {l : List α} :
    Chain3' (Mirror3 R) l.Mirror ↔ Chain3' R l := by
  induction l with
  | nil => simp only [List.Mirror, map_nil, reverse_nil, chain3'_nil]
  | cons a l ih =>
    cases l with
    | nil =>
      simp only [List.Mirror, map_cons, map_nil, reverse_cons, reverse_nil, nil_append,
        chain3'_singleton]
    | cons b l =>
      cases l with
      | nil =>
        rw [List.Mirror]
        simp only [map_cons, map_nil, reverse_cons, reverse_nil, nil_append, cons_append,
          chain3'_pair]
      | cons c l =>
        rw [List.Mirror]
        simp only [map_cons, reverse_cons, append_assoc, cons_append, nil_append,
          chain3'_append_cons3, chain3'_pair, and_true, chain3'_cons]
        simp only [List.Mirror, map_cons, reverse_cons, append_assoc, cons_append, nil_append] at ih
        rw [← ih, Mirror3]
        simp only [OrderDual.ofDual_toDual]
        exact and_comm

end List
