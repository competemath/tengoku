/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
public import Tengoku.Complexitylib.Complexitylib.Encoding.Data
public import Tengoku

/-!
# Encodings into `Data`

This file defines the class that is used to encode arbitrary data structures into `Data`,
so that RTMs (rose tree machines) can operate on them.

Instances are provided for convenience for `Data` itself, `Bool`, `List α`, `Option α`, `α × β`,
and `ℕ` (binary encoding via `List Bool`)

Every `DataEncode` instance also yields a *bitstring* encoding `DataEncode.bitstringEncode`, by
serializing the target `Data` value with `Data.toBits`. Since both the `DataEncode` instance and
`Data.toBits` are injective, `bitstringEncode` is injective too
(`DataEncode.bitstringEncode_injective`). A list is encoded as its entries' encodings inside one
pair of brackets (`DataEncode.bitstringEncode_list`, `DataEncode.bitstringEncode_append`).
-/

public section

namespace Complexity

/-- Encoding of types into `Data`. -/
class DataEncode (α : Type) where
  /-- Encode a value of `α` as `Data`. -/
  encode : α → Data
  /-- The encoding is injective, so distinct values never collide. -/
  h_inj : encode.Injective

instance : DataEncode Data where
  encode b := b
  h_inj := by intros a b h_eq; grind

/--
@isnad1 id=eq.0h1v.s3.b22b91dd4cd4 from=translated src=- shape=9023e767 vocab=9de90c65
-/
@[simp, scoped grind =]
lemma DataEncode_encode_data (d : Data) : DataEncode.encode d = d := rfl

instance : DataEncode Bool where
  encode b := if b then Data.l [ Data.l [] ] else Data.l []
  h_inj := by intros a b h_eq; grind

instance (α : Type) [DataEncode α] : DataEncode (List α) where
  encode xs := Data.l (xs.map DataEncode.encode)
  h_inj := by
    intro a b h
    exact List.map_injective_iff.mpr DataEncode.h_inj (Data.l.inj h)

/--
@isnad1 id=eq.0h1v.s4.db8d4b489e91 from=translated src=- shape=c32de6d1 vocab=7ed224f0
-/
@[simp, scoped grind =]
lemma DataEncode_list_nil {α : Type} [DataEncode α] :
  DataEncode.encode ([] : List α) = Data.l [] := by
  simp [DataEncode.encode]

/--
@isnad1 id=iff.0h2v.s4.e1840e6d8bb2 from=translated src=- shape=c32d1a15 vocab=022bd27b
-/
@[simp, scoped grind =]
lemma DataEncode_list_eq_nil_iff_nil {α : Type} [DataEncode α] (xs : List α) :
  DataEncode.encode xs = Data.empty ↔ xs = [] := by
  simp [DataEncode.encode]

/--
@isnad1 id=eq.0h2v.s4.e6b73ef68f09 from=translated src=- shape=15757df6 vocab=b433620d
-/
@[simp, scoped grind =]
lemma DataEncode_list_tail {α : Type} [DataEncode α] (xs : List α) :
  (DataEncode.encode xs).asList.tail = (DataEncode.encode xs.tail).asList := by
  simp [DataEncode.encode]

instance (α : Type) [DataEncode α] : DataEncode (Option α) where
  encode := fun
    | none => Data.l []
    | some x => Data.l [DataEncode.encode x]
  h_inj := by
    intro a b h
    grind [DataEncode.h_inj]

/--
@isnad1 id=eq.0h2v.s4.f58ec9f73b0d from=translated src=- shape=8c7d6c0e vocab=00d25719
-/
@[simp]
lemma DataEncode_Option_empty {α : Type} [DataEncode α] (x : Option α) :
  (DataEncode.encode x == Data.empty) = x.isNone := by
  cases x <;> simp [DataEncode.encode, Data.empty]

instance (α β : Type) [DataEncode α] [DataEncode β] : DataEncode (α × β) where
  encode := fun (a, b) => Data.l [DataEncode.encode a, DataEncode.encode b]
  h_inj := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    grind [DataEncode.h_inj]

/--
@isnad1 id=eq.0h4v.s5.49e6ddb37f57 from=translated src=- shape=c5c931eb vocab=01341f40
-/
lemma DataEncode_pair {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
  DataEncode.encode (a, b) = Data.l [DataEncode.encode a, DataEncode.encode b] := by
  simp [DataEncode.encode]

instance : DataEncode ℕ where
  encode x := DataEncode.encode (Nat.bits x)
  h_inj := by
    intro a b h
    have hb : a.bits = b.bits := DataEncode.h_inj h
    have hrec : ∀ n : ℕ, n.bits.foldr (fun b acc => Nat.bit b acc) 0 = n := by
      intro n
      induction n using Nat.binaryRec' with
      | zero => simp
      | bit b n hn ih => rw [Nat.bits_append_bit n b hn]; simp [ih]
    have := congrArg (List.foldr (fun b acc => Nat.bit b acc) 0) hb
    simpa [hrec] using this

/-- Encode a value into a bitstring (`List Bool`) by first encoding it into `Data` and then
serializing that with the parenthesized `Data.toBits`. This is the class-inferrable bitstring
encoding available for any type with a `DataEncode` instance. -/
@[expose] def DataEncode.bitstringEncode {α : Type} [DataEncode α] (a : α) : List Bool :=
  (DataEncode.encode a).toBits

/--
@isnad1 id=eq.0h2v.s4.c1884f9ea74c from=translated src=- shape=9083eee3 vocab=dc5f8517
-/
lemma DataEncode.bitstringEncode_def {α : Type} [DataEncode α] (a : α) :
    DataEncode.bitstringEncode a = (DataEncode.encode a).toBits := rfl

/-- The bitstring encoding is injective: distinct values yield distinct bitstrings. This composes
the injectivity of the `DataEncode` instance with that of `Data.toBits`.
@isnad1 id=injectiv.0h1v.s3.d3cccbdc7729 from=translated src=- shape=c0744be9 vocab=1afe54e7
-/
theorem DataEncode.bitstringEncode_injective {α : Type} [DataEncode α] :
    Function.Injective (DataEncode.bitstringEncode (α := α)) :=
  Data.toBits_injective.comp DataEncode.h_inj

/-- **The encoding of a list.** A list is encoded as its entries' encodings, one after
another, inside a single pair of brackets.
@isnad1 id=eq.0h2v.s5.9dbeabf888b4 from=translated src=- shape=af895be9 vocab=d09d9da0
-/
theorem DataEncode.bitstringEncode_list {α : Type} [DataEncode α] (l : List α) :
    DataEncode.bitstringEncode l
      = false :: ((l.map DataEncode.bitstringEncode).flatten ++ [true]) := by
  rw [DataEncode.bitstringEncode_def,
    show DataEncode.encode l = Data.l (l.map DataEncode.encode) from rfl, Data.toBits_l,
    List.map_map]
  rfl

/-- **The encoding of an append.** The entries of both lists, one run after the other,
inside a single pair of brackets.
@isnad1 id=eq.0h3v.s6.1b2630dbaa5e from=translated src=- shape=7b152799 vocab=d09d9da0
-/
theorem DataEncode.bitstringEncode_append {α : Type} [DataEncode α] (l₁ l₂ : List α) :
    DataEncode.bitstringEncode (l₁ ++ l₂)
      = false :: ((l₁.map DataEncode.bitstringEncode).flatten
          ++ (l₂.map DataEncode.bitstringEncode).flatten ++ [true]) := by
  rw [DataEncode.bitstringEncode_list, List.map_append, List.flatten_append]

end Complexity
