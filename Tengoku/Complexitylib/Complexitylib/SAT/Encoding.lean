/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.Semantics
public import Tengoku
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# SAT: Encoding Layer

This file pins down how CNFs and literals are written as `List Bool`, which
is the bit-string format that the TM verifier will actually parse.

## Format summary

```
  data bit b              ↦  [b, b]           (doubled)
  literal separator  "|"  ↦  [false, true]   (one undoubled pair)
  clause separator   "#"  ↦  [true, false]   (one undoubled pair)
```

- A variable index `v : ℕ` is encoded **in unary** as `replicate v true` —
  that is, `v` consecutive `1`-bits. `Unary.encode 0 = []`.
  Unary is chosen (over binary) so that `|encode v| ≥ v`, which makes
  `maxVar φ ≤ |φ.encode|` automatic. This is what powers the
  `PolyBalanced` step in the NP-membership proof.
- A literal `(sign, var)` is encoded as `[sign] ++ Unary.encode var` —
  call this the *raw* literal encoding (a list of single bits).
- A clause is a list of raw-encoded literals, each *doubled* bit-by-bit,
  separated (and terminated) by `|`. An empty clause is the empty list.
- A CNF is a list of encoded clauses, each terminated by `#`. An empty
  CNF is the empty list.

Inside a clause, every bit is doubled, so the only pairs that appear are
`00`, `11` (data), `01` (lit sep), `10` (clause sep). The four patterns
cover all four two-bit combinations and are mutually exclusive, giving a
well-defined token stream for any valid encoding.

## Why this format

- `|` and `#` can't collide with data because all data bits are doubled.
- No length prefixes — parsing is a single pass over the input.
- Unary variables give `|encodeRaw ℓ| = ℓ.var + 1`, which propagates to
  `maxVar φ ≤ |φ.encode|` (key for `PolyBalanced`).
- Distinguishes `[]` (true CNF) from `[[]]` (one unsatisfiable clause):
  the former encodes to `[]`, the latter to `[true, false]`.

The matching executable decoder `CNF.decode?`, its round-trip theorem, and its
soundness theorem live with the token parser in `Complexitylib.SAT.Verifier`.
-/

@[expose] public section

namespace Complexity

namespace SAT

-- ════════════════════════════════════════════════════════════════════════
-- Unary encoding of natural numbers (used for variable indices)
-- ════════════════════════════════════════════════════════════════════════

namespace Unary

/-- Unary encoding of `n`: `n` consecutive `true` bits. `encode 0 = []`. -/
def encode (n : Nat) : List Bool := List.replicate n true

/-- The unary encoding of `n` has length exactly `n`.
@isnad1 id=eq.0h1v.s3.9d0f21ab25d5 from=translated src=- shape=c3f7ecf6 vocab=756a6ce1
-/
@[simp] theorem length_encode (n : Nat) : (encode n).length = n := by
  simp [encode]

/-- Zero encodes to the empty bit list.
@isnad1 id=eq.0h0v.s3.15e30a6ed58c from=translated src=- shape=58b8d025 vocab=40986e81
-/
@[simp] theorem encode_zero : encode 0 = [] := rfl

/-- Every bit in a unary encoding is `true`.
@isnad1 id=eq.1h2v.s4.e636696b0456 from=translated src=- shape=6a69b208 vocab=f2d13d99
-/
theorem encode_all_true (n : Nat) : ∀ b ∈ encode n, b = true := by
  intro b hb
  simp [encode, List.mem_replicate] at hb
  exact hb.2

end Unary

-- ════════════════════════════════════════════════════════════════════════
-- Literal raw encoding: sign bit + unary var
-- ════════════════════════════════════════════════════════════════════════

namespace Lit

/-- Raw literal encoding: `[sign] ++ unary(var)`. Produces a list of
    single (undoubled) bits; the doubling happens at the clause level. -/
def encodeRaw (ℓ : Lit) : List Bool := ℓ.sign :: Unary.encode ℓ.var

/-- The raw literal encoding has length `ℓ.var + 1`: one sign bit plus a unary var.
@isnad1 id=eq.0h1v.s4.e8708acd6ba9 from=translated src=- shape=802c6af4 vocab=eb93dff4
-/
@[simp] theorem encodeRaw_length (ℓ : Lit) : ℓ.encodeRaw.length = ℓ.var + 1 := by
  simp [encodeRaw]

/-- The raw encoding of a literal has `ℓ.var ≤ |encodeRaw| - 1`. Key for
    `maxVar ≤ |encode|`.
@isnad1 id=lt.0h1v.s3.8b4a60da9d87 from=translated src=- shape=b4e3cde8 vocab=9c100986
-/
theorem var_lt_encodeRaw_length (ℓ : Lit) : ℓ.var < ℓ.encodeRaw.length := by
  simp

/-- The raw literal encoding is injective: sign and var are recoverable.
@isnad1 id=injectiv.0h0v.s2.72ca1fd66597 from=translated src=- shape=4b736592 vocab=ce7669af
-/
theorem encodeRaw_injective : Function.Injective Lit.encodeRaw := by
  rintro ⟨s₁, v₁⟩ ⟨s₂, v₂⟩ h
  have hlen : v₁ + 1 = v₂ + 1 := by
    have := congrArg List.length h
    simpa using this
  have hvar : v₁ = v₂ := by omega
  subst hvar
  have hsign : s₁ = s₂ := by simpa [encodeRaw] using h
  subst hsign
  rfl

end Lit

-- ════════════════════════════════════════════════════════════════════════
-- Bit doubling
-- ════════════════════════════════════════════════════════════════════════

/-- Double each bit: `b ↦ [b, b]`. The image consists only of `00` and `11`
    two-bit patterns, so `01` and `10` cannot appear in doubled data. -/
def doubleBits (bs : List Bool) : List Bool := bs.flatMap (fun b => [b, b])

/-- Doubling the empty bit list yields the empty list.
@isnad1 id=eq.0h0v.s3.1bd50db90368 from=translated src=- shape=9b1c3ca8 vocab=b18b9269
-/
@[simp] theorem doubleBits_nil : doubleBits [] = [] := rfl

/-- Doubling a cons prepends the head bit twice: `doubleBits (b :: bs) = b :: b :: …`.
@isnad1 id=eq.0h2v.s4.c122f3d220a4 from=translated src=- shape=ede16f07 vocab=26e49786
-/
@[simp] theorem doubleBits_cons (b : Bool) (bs : List Bool) :
    doubleBits (b :: bs) = b :: b :: doubleBits bs := by
  simp [doubleBits]

/-- Doubling exactly doubles the length: `|doubleBits bs| = 2 * |bs|`.
@isnad1 id=eq.0h1v.s4.17a6cc6e7561 from=translated src=- shape=b89013fa vocab=24683427
-/
@[simp] theorem doubleBits_length (bs : List Bool) :
    (doubleBits bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ih]; ring

-- ════════════════════════════════════════════════════════════════════════
-- Clause and CNF encoding
-- ════════════════════════════════════════════════════════════════════════

namespace Clause

/-- Encoded clause: each literal's raw bits doubled, followed by `[0,1]`. -/
def encode : Clause → List Bool
  | [] => []
  | ℓ :: ℓs => doubleBits ℓ.encodeRaw ++ [false, true] ++ encode ℓs

/-- The empty clause encodes to the empty bit list.
@isnad1 id=eq.0h0v.s3.9553873b0fb4 from=translated src=- shape=1d803c6d vocab=d829ee3b
-/
@[simp] theorem encode_nil : encode ([] : Clause) = [] := rfl

/-- Unfolding lemma: encoding `ℓ :: ℓs` emits the doubled raw literal,
    the `[false, true]` literal separator, then the encoded tail.
@isnad1 id=eq.0h2v.s5.57bccc0daa28 from=translated src=- shape=851d84e4 vocab=a2baa198
-/
theorem encode_cons (ℓ : Lit) (ℓs : Clause) :
    encode (ℓ :: ℓs) = doubleBits ℓ.encodeRaw ++ [false, true] ++ encode ℓs := rfl

/-- Length bound on the encoded clause: each literal contributes at most
    `2 * |encodeRaw| + 2` bits (doubling + separator).
@isnad1 id=eq.0h1v.s5.95a542685f3c from=translated src=- shape=537d8844 vocab=cb6ce505
-/
theorem length_encode (c : Clause) :
    c.encode.length = c.foldr (fun ℓ acc => 2 * ℓ.encodeRaw.length + 2 + acc) 0 := by
  induction c with
  | nil => rfl
  | cons ℓ ℓs ih =>
    simp only [encode_cons, List.length_append, List.length_cons, List.length_nil,
               doubleBits_length, List.foldr_cons, ih]

end Clause

namespace CNF

/-- Encoded CNF: each clause followed by `[1,0]`. -/
def encode : CNF → List Bool
  | [] => []
  | c :: cs => c.encode ++ [true, false] ++ encode cs

/-- The empty CNF encodes to the empty bit list.
@isnad1 id=eq.0h0v.s3.c08fcef650f6 from=translated src=- shape=1d803c6d vocab=54c45a2a
-/
@[simp] theorem encode_nil : encode ([] : CNF) = [] := rfl

/-- Unfolding lemma: encoding `c :: cs` emits the encoded clause, the
    `[true, false]` clause separator, then the encoded tail.
@isnad1 id=eq.0h2v.s5.cf25878f68f1 from=translated src=- shape=513b0e2e vocab=fa8bd2c3
-/
theorem encode_cons (c : Clause) (cs : CNF) :
    encode (c :: cs) = c.encode ++ [true, false] ++ encode cs := rfl

/-- Length bound: each clause contributes `|c.encode| + 2` bits to the CNF.
@isnad1 id=eq.0h1v.s5.2379db945cd9 from=translated src=- shape=f0c91334 vocab=79225e5a
-/
theorem length_encode (φ : CNF) :
    φ.encode.length = φ.foldr (fun c acc => c.encode.length + 2 + acc) 0 := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp only [encode_cons, List.length_append, List.length_cons, List.length_nil, ih,
               List.foldr_cons]

/-- `CNF.encode` is a `++`-homomorphism — the per-family reduction emitters
    compose by output concatenation.
@isnad1 id=eq.0h2v.s5.b01c29681427 from=translated src=- shape=82c640f9 vocab=be3a3405
-/
theorem encode_append (φ ψ : CNF) : encode (φ ++ ψ) = encode φ ++ encode ψ := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    rw [List.cons_append, encode_cons, encode_cons, ih]
    simp [List.append_assoc]

end CNF

/-- Doubling a run of `true`s doubles its length.
@isnad1 id=eq.0h1v.s4.1bf9d150adb4 from=translated src=- shape=7f5b0e99 vocab=5df41e85
-/
theorem doubleBits_replicate_true (v : ℕ) :
    doubleBits (List.replicate v true) = List.replicate (2 * v) true := by
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [List.replicate_succ, doubleBits_cons, ih,
      show 2 * (v + 1) = (2 * v + 1) + 1 from by omega,
      List.replicate_succ, List.replicate_succ]

/-- The encoded form of one literal inside a clause: doubled sign, doubled
    unary variable index, separator — exactly the word the reduction's
    literal emitter appends.
@isnad1 id=eq.0h2v.s6.4e16d59d8fb2 from=translated src=- shape=183afa52 vocab=32dc8135
-/
theorem Clause.encode_cons' (ℓ : Lit) (ℓs : Clause) :
    Clause.encode (ℓ :: ℓs)
      = ([ℓ.sign, ℓ.sign] ++ List.replicate (2 * ℓ.var) true ++ [false, true])
          ++ Clause.encode ℓs := by
  rw [Clause.encode_cons, Lit.encodeRaw, Unary.encode, doubleBits_cons,
    doubleBits_replicate_true]
  simp [List.append_assoc]

-- ════════════════════════════════════════════════════════════════════════
-- maxVar ≤ |encode|  (the key bound for PolyBalanced)
-- ════════════════════════════════════════════════════════════════════════
--
-- With unary variables, each literal `ℓ` contributes `2 * (ℓ.var + 1)` bits
-- to its doubled block, so `ℓ.var ≤ |c.encode|` and hence `c.maxVar ≤ |c.encode|`,
-- and `φ.maxVar ≤ |φ.encode|`.

namespace Clause

/-- Every variable in a clause has index `≤ |c.encode|`. Immediate from unary.
@isnad1 id=le.0h1v.s3.c513cd3b3c5f from=translated src=- shape=b4e3cde8 vocab=eb4fd39a
-/
theorem maxVar_le_encode_length (c : Clause) : c.maxVar ≤ c.encode.length := by
  induction c with
  | nil => simp
  | cons ℓ ℓs ih =>
    simp only [maxVar_cons, encode_cons, List.length_append, List.length_cons, List.length_nil,
               doubleBits_length, Lit.encodeRaw_length]
    have h_var : ℓ.var ≤ 2 * (ℓ.var + 1) + 2 + (Clause.encode ℓs).length := by omega
    have h_tail : Clause.maxVar ℓs ≤ 2 * (ℓ.var + 1) + 2 + (Clause.encode ℓs).length :=
      le_trans ih (by omega)
    exact max_le h_var h_tail

end Clause

namespace CNF

/-- **Key bound for `PolyBalanced`.** Every variable mentioned in `φ` has
    index at most `|φ.encode|`. Hence any satisfying assignment `α` (with
    unused positions truncated) has length at most `|φ.encode| + 1`.
@isnad1 id=le.0h1v.s3.dcb0c5c9b361 from=translated src=- shape=b4e3cde8 vocab=01b69b9e
-/
theorem maxVar_le_encode_length (φ : CNF) : φ.maxVar ≤ φ.encode.length := by
  induction φ with
  | nil => simp
  | cons c cs ih =>
    simp only [maxVar_cons, encode_cons, List.length_append, List.length_cons, List.length_nil]
    have h_c : c.maxVar ≤ c.encode.length + 2 + (CNF.encode cs).length :=
      le_trans c.maxVar_le_encode_length (by omega)
    have h_tail : CNF.maxVar cs ≤ c.encode.length + 2 + (CNF.encode cs).length :=
      le_trans ih (by omega)
    exact max_le h_c h_tail

end CNF

-- ════════════════════════════════════════════════════════════════════════
-- Lemmas about doubled data: only `00` and `11` appear
-- ════════════════════════════════════════════════════════════════════════

/-- `doubleBits bs` contains no `[false, true]` or `[true, false]` pair at
    an even-index boundary. Concretely: every pair `(b_{2k}, b_{2k+1})` in
    `doubleBits bs` has `b_{2k} = b_{2k+1}`.
@isnad1 id=eq.1h2v.s6.cc3e70c9909e from=translated src=- shape=15b4542a vocab=6bf11908
-/
theorem doubleBits_pair_eq (bs : List Bool) (k : Nat) (h : 2 * k + 1 < (doubleBits bs).length) :
    (doubleBits bs)[2 * k]? = (doubleBits bs)[2 * k + 1]? := by
  induction bs generalizing k with
  | nil => simp at h
  | cons b bs ih =>
    match k with
    | 0 => simp [doubleBits_cons]
    | k + 1 =>
      simp only [doubleBits_cons, List.length_cons] at h
      have h2 : 2 * k + 1 < (doubleBits bs).length := by omega
      have ih' := ih k h2
      show (b :: b :: doubleBits bs)[2 * (k + 1)]? = (b :: b :: doubleBits bs)[2 * (k + 1) + 1]?
      have e1 : 2 * (k + 1) = (2 * k) + 2 := by ring
      have e2 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      rw [e2, e1]
      simp only [List.getElem?_cons_succ]
      exact ih'

end SAT

end Complexity
