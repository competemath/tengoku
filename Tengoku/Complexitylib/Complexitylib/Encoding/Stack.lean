/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Encoding.Pairing

/-!
# Exact nested-pair stack encoding

A stack is encoded top first: the empty stack is `[]`, and pushing a frame
pairs its encoding with the encoded tail. Empty frame encodings are permitted;
the pair separator still distinguishes a nonempty stack from an empty one.
The frame encoder need not be injective for the projection and length laws.

The raw stack operations are the existing `pair`, `pairFst`, and `pairSnd`,
including their total behavior on malformed strings. Their polynomial-time
closure rules live in `Classes.P.Pairing`, outside this machine-independent
module. Return values and algorithm-specific frame semantics are not encoded here.
-/

@[expose] public section

namespace Complexity.StackEncoding

variable {α : Type*}

/-- Encode a stack with its top frame first, using the supplied frame encoding. -/
def encode (frame : α → List Bool) : List α → List Bool
  | [] => []
  | f :: fs => pair (frame f) (encode frame fs)

/--
@isnad1 id=eq.0h2v.s4.f80f496e7fde from=translated src=- shape=afc1e2a8 vocab=6ca8a8dc
-/
@[simp] theorem encode_nil (frame : α → List Bool) : encode frame [] = [] := rfl

/--
@isnad1 id=eq.0h4v.s4.b4e830b975aa from=translated src=- shape=d6fa1e1b vocab=9b2008c0
-/
@[simp] theorem encode_cons (frame : α → List Bool) (f : α) (fs : List α) :
    encode frame (f :: fs) = pair (frame f) (encode frame fs) := rfl

/-- Reading the top of an encoded nonempty stack recovers its frame encoding.
@isnad1 id=eq.0h4v.s4.9327eb7f4fb1 from=translated src=- shape=37355495 vocab=3d0e8cf6
-/
theorem pairFst_encode_cons (frame : α → List Bool) (f : α) (fs : List α) :
    pairFst (encode frame (f :: fs)) = frame f :=
  pairFst_pair _ _

/-- Popping an encoded nonempty stack recovers the encoded tail.
@isnad1 id=eq.0h4v.s4.aa0e3cd0208c from=translated src=- shape=aaa333ea vocab=69473fd6
-/
theorem pairSnd_encode_cons (frame : α → List Bool) (f : α) (fs : List α) :
    pairSnd (encode frame (f :: fs)) = encode frame fs :=
  pairSnd_pair _ _

/-- Even an empty frame encoding has a separator, so only an empty stack encodes to `[]`.
@isnad1 id=iff.0h3v.s4.a96bae30a72e from=translated src=- shape=ef3db790 vocab=6ca8a8dc
-/
theorem encode_eq_nil_iff (frame : α → List Bool) (fs : List α) :
    encode frame fs = [] ↔ fs = [] := by
  cases fs with
  | nil => simp
  | cons f fs =>
      constructor
      · intro h
        have hlength := congrArg List.length h
        simp only [encode_cons, pair_length, List.length_nil] at hlength
        omega
      · intro h
        cases h

/-- Exact length, including the doubled frame and two separator bits at every push.
@isnad1 id=eq.0h3v.s6.0464fcfc914d from=translated src=- shape=cefd1ac3 vocab=fd93e0f8
-/
@[simp] theorem length_encode (frame : α → List Bool) (fs : List α) :
    (encode frame fs).length =
      fs.foldr (fun f n => 2 * (frame f).length + 2 + n) 0 := by
  induction fs with
  | nil => rfl
  | cons f fs ih => rw [encode_cons, pair_length, ih, List.foldr_cons]

/-- A uniform frame-length bound gives a linear bound in the number of live frames.
@isnad1 id=le.1h4v.s6.996afed92591 from=translated src=- shape=8ca9c4cd vocab=82c61b46
-/
theorem length_encode_le (frame : α → List Bool) : ∀ (fs : List α) (B : ℕ),
    (∀ f ∈ fs, (frame f).length ≤ B) →
      (encode frame fs).length ≤ fs.length * (2 * B + 2)
  | [], _, _ => by simp
  | f :: fs, B, h => by
      have hf := h f List.mem_cons_self
      have hrest := length_encode_le frame fs B fun g hg => h g (List.mem_cons_of_mem _ hg)
      rw [encode_cons, pair_length, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end Complexity.StackEncoding
