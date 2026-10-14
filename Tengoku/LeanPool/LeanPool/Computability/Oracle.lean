/-
Copyright (c) 2026 Tanner Duve, Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Tengoku

/-!
# Oracle Computability

This file defines a model of oracle computability using partial recursive functions. It extends
the notion of `Nat.Partrec` by allowing access to a set of oracle functions.

## Main Definitions

* `RecursiveIn O f`:
  A partial function `f : ℕ →. ℕ` is recursive in a set of oracles `O ⊆ ℕ →. ℕ` if it can be
  constructed from constants, basic operations, and functions in `O` using pairing, composition,
  primitive recursion, and μ-recursion.
* `liftPrim`: Encodes a function `α →. σ` as a function `ℕ →. ℕ` using `Primcodable`.
* `RecursiveIn'`, `RecursiveIn₂`, `ComputableIn`, `ComputableIn₂`:
  Versions of `RecursiveIn` for functions between `Primcodable` types.

## Implementation Notes

The encoding/decoding mechanism relies on `Primcodable`. The definition of `RecursiveIn` mimics
the inductive structure of `Nat.Partrec`.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers*, Vol. I.

## Tags

Computability, Oracle, Recursion, Primitive Recursion
-/

@[expose] public section

open Primrec Nat.Partrec Part Encodable

namespace Computability

variable {f g h : ℕ →. ℕ}

/--
The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O fun _ => 0
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O fun n => (Nat.unpair n).1
  | right : RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : ∀ g ∈ O, RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
      RecursiveIn O fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)

/-- The primitive recursive functions `ℕ → ℕ` relative to a set of oracles `O`. -/
inductive PrimrecIn (O : Set (ℕ → ℕ)) : (ℕ → ℕ) → Prop
  | zero : PrimrecIn O fun _ => 0
  | succ : PrimrecIn O Nat.succ
  | left : PrimrecIn O fun n => n.unpair.1
  | right : PrimrecIn O fun n => n.unpair.2
  | oracle : ∀ g ∈ O, PrimrecIn O g
  | pair {f g : ℕ → ℕ} :
      PrimrecIn O f → PrimrecIn O g → PrimrecIn O fun n => Nat.pair (f n) (g n)
  | comp {f g : ℕ → ℕ} : PrimrecIn O f → PrimrecIn O g → PrimrecIn O fun n => f (g n)
  | prec {f g : ℕ → ℕ} :
      PrimrecIn O f →
        PrimrecIn O g →
          PrimrecIn O
            (Nat.unpaired fun z n => n.rec (f z) fun y IH => g <| Nat.pair z <| Nat.pair y IH)

/-- Encodes a partial function `α →. σ` as a partial function `ℕ →. ℕ` using `Primcodable`. -/
def liftPrim {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) : ℕ →. ℕ :=
  fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

/-- Encodes a total function `α → σ` as a function `ℕ → ℕ` using `Primcodable`. -/
def liftPrimrec {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) : ℕ → ℕ :=
  fun n => (decode (α := α) n).map (fun a => encode (f a)) |>.getD 0

/-- A partial function between `Primcodable` types is recursive in `O` if its lift is. -/
def RecursiveIn' {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α →. σ) : Prop :=
  RecursiveIn O (liftPrim f)

/-- Relative primitive recursion between primcodable types -/
def PrimrecIn' {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ → ℕ)) (f : α → σ) : Prop :=
  PrimrecIn O (liftPrimrec f)

/-- A binary partial function is recursive in `O` if the curried form is. -/
def RecursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β →. σ) : Prop :=
  RecursiveIn' O (fun p : α × β => f p.1 p.2)

/-- A total function is computable in `O` if its constant lift is recursive in `O`. -/
def ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α → σ) : Prop :=
  RecursiveIn' O (fun a => Part.some (f a))

/-- A binary total function is computable in `O`. -/
def ComputableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β → σ) : Prop :=
  ComputableIn O (fun p : α × β => f p.1 p.2)

/--
@isnad1 id=recursiv.2h3v.s5.2df7c23d452e from=translated src=- shape=60375b08 vocab=5feca121
-/
theorem RecursiveIn.of_eq {f g : ℕ →. ℕ} (hf : RecursiveIn O f) (H : ∀ n, f n = g n) :
    RecursiveIn O g :=
  (funext H : f = g) ▸ hf

/--
@isnad1 id=recursiv.2h3v.s5.d21d4582bbb8 from=translated src=- shape=63d90b8b vocab=603b394e
-/
theorem RecursiveIn.of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : RecursiveIn O f)
    (H : ∀ n, g n ∈ f n) : RecursiveIn O g :=
  hf.of_eq fun n => eq_some_iff.2 (H n)
/--
If a function is partial recursive, then it is recursive in every partial function.
@isnad1 id=recursiv.1h2v.s3.895591f6f27d from=translated src=- shape=e6c76c10 vocab=ef0ae235
-/
lemma recursiveIn_of_partrec (pF : Nat.Partrec f) : RecursiveIn O f := by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih

/--
If a function is computable, then it is computable in every oracle.
@isnad1 id=computab.1h4v.s5.31b151796c0b from=translated src=- shape=6470f395 vocab=8526a5b6
-/
theorem computableIn_of_computable {f : α → β} [Primcodable α]
[Primcodable β]
(hf : Computable f) : ComputableIn O f :=
  recursiveIn_of_partrec hf

/--
@isnad1 id=recursiv.1h2v.s4.49b9cf185ef8 from=translated src=- shape=5e64c308 vocab=062300fc
-/
theorem RecursiveIn.of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
RecursiveIn O (fun n => f n) := recursiveIn_of_partrec (Nat.Partrec.of_primrec hf)

/--
@isnad1 id=computab.1h4v.s5.97f7aae69827 from=translated src=- shape=3c82cf89 vocab=92ac4495
-/
theorem computableIn_of_primrec {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} (hf : Primrec f) (O : Set (ℕ →. ℕ)) :
    ComputableIn O f := computableIn_of_computable (Primrec.to_comp hf)

/--
@isnad1 id=computab.1h5v.s5.27d98e943193 from=translated src=- shape=85012e5e vocab=681df69f
-/
theorem computableIn₂_of_primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Primrec₂ f) (O : Set (ℕ →. ℕ)) :
    ComputableIn₂ O f :=
  computableIn_of_primrec hf O

/--
@isnad1 id=recursiv.1h4v.s5.57541b4400b3 from=translated src=- shape=706b2119 vocab=ea536fd8
-/
protected theorem ComputableIn.recursiveIn' {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : ComputableIn O f) :
    RecursiveIn' O (fun a => Part.some (f a)) := hf

/--
@isnad1 id=recursiv.1h5v.s5.c7437110d633 from=translated src=- shape=32699f47 vocab=3643cf86
-/
protected theorem ComputableIn₂.recursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : ComputableIn₂ O f) :
    RecursiveIn₂ O fun a => (f a : β →. σ) := hf

/--
@isnad1 id=recursiv.0h1v.s3.4d80c21cf000 from=translated src=- shape=5195c8ad vocab=650e14fd
-/
protected theorem RecursiveIn.some : RecursiveIn O some :=
  RecursiveIn.of_primrec Nat.Primrec.id

/--
@isnad1 id=recursiv.0h1v.s3.44d4fb1c4da7 from=translated src=- shape=b6854a9d vocab=c2e9be97
-/
theorem RecursiveIn.none : RecursiveIn O (fun _ => none) :=
  (RecursiveIn.of_primrec (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by
      obtain ⟨_, hn, -⟩ := Nat.rfind_dom.1 h
      simp at hn

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/--
@isnad1 id=computab.0h4v.s4.82a9cbffafff from=translated src=- shape=46061524 vocab=0f7b1075
-/
theorem const_in (O : Set (ℕ →. ℕ)) (s : σ) : ComputableIn O (fun _ : α => s) :=
  computableIn_of_primrec (Primrec.const s) O

/--
@isnad1 id=computab.0h2v.s4.480080853f80 from=translated src=- shape=2a4816c8 vocab=4c679c9a
-/
theorem id_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@id α) :=
  computableIn_of_primrec Primrec.id O

/--
@isnad1 id=computab.0h3v.s4.3fc04985c441 from=translated src=- shape=538af1e1 vocab=2c5d40e2
-/
theorem fst_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.fst α β) :=
  computableIn_of_primrec Primrec.fst O

/--
@isnad1 id=computab.0h3v.s4.85ceded19d1f from=translated src=- shape=da9633cb vocab=a0244531
-/
theorem snd_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.snd α β) :=
  computableIn_of_primrec Primrec.snd O

/--
@isnad1 id=computab.0h1v.s4.e4f2c0480af3 from=translated src=- shape=dbdaaccb vocab=22768fc0
-/
theorem unpair_in (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.unpair :=
  computableIn_of_primrec Primrec.unpair O

/--
@isnad1 id=computab.0h1v.s4.1e14cc8684ed from=translated src=- shape=19797508 vocab=14fb6f06
-/
theorem succ_in (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.succ :=
  computableIn_of_primrec Primrec.succ O

/--
@isnad1 id=computab.0h3v.s4.3d775072f5af from=translated src=- shape=8e04e710 vocab=54892e53
-/
theorem sumInl_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inl α β) :=
  computableIn_of_primrec Primrec.sumInl O

/--
@isnad1 id=computab.0h3v.s4.6225c489d279 from=translated src=- shape=826c1210 vocab=9ab492d7
-/
theorem sumInr_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inr α β) :=
  computableIn_of_primrec Primrec.sumInr O

/--
If a function is recursive in the constant zero function,
then it is partial recursive.
@isnad1 id=partrec.1h1v.s4.590084f50c91 from=translated src=- shape=81c5e63a vocab=051e0ab7
-/
lemma RecursiveIn.partrec_of_zero (fRecInZero : RecursiveIn {fun _ => Part.some 0} f) :
    Nat.Partrec f := by
  induction fRecInZero with
  | zero | succ | left | right => constructor
  | oracle g hg => rw [hg]; exact Nat.Partrec.zero
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

/--
If a function is partial recursive in the constant none function,
then it is partial recursive.
@isnad1 id=partrec.1h1v.s4.b0164e885a19 from=translated src=- shape=8a78ab05 vocab=8af7ab1e
-/
lemma RecursiveIn.partrec_of_none (fRecInNone : RecursiveIn {fun _ => Part.none} f) :
    Nat.Partrec f := by
  induction fRecInNone with
  | zero | succ | left | right => constructor
  | oracle g hg => rw [hg]; exact Nat.Partrec.none
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

/--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
@isnad1 id=iff.0h1v.s4.79e5b684b73c from=translated src=- shape=40870e4b vocab=813607fd
-/
theorem partrec_iff_forall_recursiveIn : Nat.Partrec f ↔ ∀ g, RecursiveIn {g} f:=
  ⟨fun hf _ ↦ recursiveIn_of_partrec hf, (· _ |>.partrec_of_zero)⟩

/--
@isnad1 id=iff.0h1v.s4.aa61e4c4b32f from=translated src=- shape=24b3d016 vocab=c1099534
-/
@[simp]
lemma recursiveIn_empty_iff_partrec : RecursiveIn {} f ↔ Nat.Partrec f := by
  constructor
  · intro hf
    induction hf with
    | zero | succ | left | right => constructor
    | oracle g hg => cases hg
    | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
    | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
    | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
    | rfind _ ih => exact .rfind ih
  · intro hf
    exact recursiveIn_of_partrec (O := ({} : Set (ℕ →. ℕ))) hf

/--
@isnad1 id=recursiv.2h3v.s5.0801e3c279e8 from=translated src=- shape=da37bff4 vocab=7e41b72c
-/
theorem recursiveIn_mono {O₁ O₂ : Set (ℕ →. ℕ)} (hsub : O₁ ⊆ O₂) {g : ℕ →. ℕ} :
      RecursiveIn O₁ g → RecursiveIn O₂ g := by
  intro hg
  induction hg with
  | zero | succ | left | right => constructor
  | oracle g hg => exact RecursiveIn.oracle g (hsub hg)
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih

/--
@isnad1 id=recursiv.2h3v.s5.6072ef62af01 from=translated src=- shape=817f8e9d vocab=171d3625
-/
theorem RecursiveIn_subst {O O' : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} (hf : RecursiveIn O f)
    (hO : ∀ g, g ∈ O → RecursiveIn O' g) : RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

end Computability
