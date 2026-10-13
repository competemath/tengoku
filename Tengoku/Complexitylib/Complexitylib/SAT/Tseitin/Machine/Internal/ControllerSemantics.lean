/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Machine.Internal.ControllerInvariant

/-!
# Semantic glue for the streaming Tseitin controller

This proof-only module identifies the register and output updates exposed by
`Machine.Internal.BufferSpecs` with the corresponding pure transitions in
`ThreeSAT.Streaming`. No concrete Turing-machine execution is simulated here.
The results are definitional seams used by the later controller induction.

## Main results

- `literalBits_eq_encodeTokens_literal_internal`
- `clauseBits_eq_encodeTokens_clause_internal`
- `bufferValues_startLiteral_internal`
- `bufferValues_incrementLiteral_internal`
- `bufferValues_committed_eq_pushLiteral_internal`
- `commitBits_eq_pushLiteral_emitted_internal`
- `bufferValues_closed_eq_closeClause_internal`
- `pendingBits_eq_closeClause_emitted_internal`
-/

public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Canonical encodings of emitted chunks -/

private theorem encodeTokens_replicate_bit_true_internal (n : ℕ) :
    encodeTokens (List.replicate n (EncToken.bit true)) =
      List.replicate (2 * n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, encodeTokens_cons, ih]
      change [true, true] ++ List.replicate (2 * n) true =
        List.replicate (2 * Nat.succ n) true
      rw [show 2 * Nat.succ n = 2 + 2 * n by omega, List.replicate_add]
      rfl

/-- The literal chunk used by `emitLitTM` is exactly the canonical token
encoding of one completed literal.
@isnad1 id=eq.0h2v.s4.584b786745bd from=translated src=- shape=077fccb3 vocab=81c39cef
-/
theorem literalBits_eq_encodeTokens_literal_internal (sign : Bool) (var : ℕ) :
    literalBits sign var =
      encodeTokens
        (Clause.tokens [({ sign := sign, var := var } : Lit)]) := by
  cases sign <;>
    simp [literalBits, Clause.tokens, Lit.rawTokens, Lit.encodeRaw, Unary.encode,
      EncToken.encode, encodeTokens_replicate_bit_true_internal]

/-- The clause chunk used by `emitClauseTM` is exactly the canonical token
encoding of one exact-three-literal CNF clause.
@isnad1 id=eq.0h6v.s5.d96448fe7aee from=translated src=- shape=335a746c vocab=78d0444c
-/
theorem clauseBits_eq_encodeTokens_clause_internal
    (aSign : Bool) (a : ℕ) (bSign : Bool) (b : ℕ)
    (cSign : Bool) (c : ℕ) :
    clauseBits aSign a bSign b cSign c =
      encodeTokens
        (CNF.tokens
          [[({ sign := aSign, var := a } : Lit),
            ({ sign := bSign, var := b } : Lit),
            ({ sign := cSign, var := c } : Lit)]]) := by
  cases aSign <;> cases bSign <;> cases cSign <;>
    simp [clauseBits, literalBits, CNF.tokens, Clause.tokens, Lit.rawTokens,
      Lit.encodeRaw, Unary.encode, EncToken.encode,
      encodeTokens_replicate_bit_true_internal, List.append_assoc]

/-! ## Simple scanner transitions -/

/-- Reading a sign bit at a clause boundary starts a zero-valued literal and
does not change any register value.
@isnad1 id=eq.0h4v.s4.bdc2d131b00f from=translated src=- shape=7a643053 vocab=bf1e6206
-/
theorem bufferValues_startLiteral_internal
    (next : ℕ) (pending : Streaming.Pending) (emitted : List EncToken)
    (sign : Bool) :
    BufferValues.ofStreaming
        { next, pending, scan := .boundary, emitted } =
      BufferValues.ofStreaming
        { next, pending, scan := .literal sign 0, emitted } := by
  rfl

/-- Reading a unary `true` body bit increments exactly the current-literal
register.
@isnad1 id=eq.0h5v.s6.0a1849bda3db from=translated src=- shape=d34d28ec vocab=4b2c2759
-/
theorem bufferValues_incrementLiteral_internal
    (next : ℕ) (pending : Streaming.Pending) (emitted : List EncToken)
    (sign : Bool) (var : ℕ) :
    ({ BufferValues.ofStreaming
        { next, pending, scan := .literal sign var, emitted } with
          current := var + 1 } : BufferValues) =
      BufferValues.ofStreaming
        { next, pending, scan := .literal sign (var + 1), emitted } := by
  rfl

/-- Pure boundary-bit transition, stated in the form consumed by the
controller token induction.
@isnad1 id=eq.0h4v.s5.b2297d919912 from=translated src=- shape=d9700daa vocab=a9862da2
-/
theorem streaming_step_boundary_bit_internal
    (next : ℕ) (pending : Streaming.Pending) (emitted : List EncToken)
    (sign : Bool) :
    Streaming.step
        { next, pending, scan := .boundary, emitted } (.bit sign) =
      some { next, pending, scan := .literal sign 0, emitted } := by
  rfl

/-- Pure unary-body transition corresponding to `incRegTM currentReg`.
@isnad1 id=eq.0h5v.s5.c44d4dcb175a from=translated src=- shape=dc399e3f vocab=a46b3968
-/
theorem streaming_step_literal_true_internal
    (next : ℕ) (pending : Streaming.Pending) (emitted : List EncToken)
    (sign : Bool) (var : ℕ) :
    Streaming.step
        { next, pending, scan := .literal sign var, emitted } (.bit true) =
      some { next, pending, scan := .literal sign (var + 1), emitted } := by
  rfl

/-! ## Literal commit -/

/-- The post-register tuple of `commitLiteralTM` is exactly the register
representation of the pure `pushLiteral` result.
@isnad1 id=eq.0h5v.s5.de19bb8b5000 from=translated src=- shape=882cee70 vocab=fa6b8b0d
-/
theorem bufferValues_committed_eq_pushLiteral_internal
    (next : ℕ) (pending : Streaming.Pending) (emitted : List EncToken)
    (sign : Bool) (var : ℕ) :
    (BufferValues.ofStreaming
        { next, pending, scan := .literal sign var, emitted }).committed
          (PendingSigns.ofStreaming pending) =
      BufferValues.ofStreaming
        (Streaming.pushLiteral
          { next, pending, scan := .literal sign var, emitted }
          { sign := sign, var := var }) := by
  cases pending <;> rfl

/-- The bits appended by `commitLiteralTM` turn the old pure output
accumulator into exactly the `pushLiteral` accumulator.
@isnad1 id=eq.0h5v.s5.fc3f413676c1 from=translated src=- shape=f1e2e20a vocab=c11d3975
-/
theorem commitBits_eq_pushLiteral_emitted_internal
    (next : ℕ) (pending : Streaming.Pending) (emitted : List EncToken)
    (sign : Bool) (var : ℕ) :
    encodeTokens emitted ++
        commitBits (PendingSigns.ofStreaming pending)
          (BufferValues.ofStreaming
            { next, pending, scan := .literal sign var, emitted }) =
      encodeTokens
        (Streaming.pushLiteral
          { next, pending, scan := .literal sign var, emitted }
          { sign := sign, var := var }).emitted := by
  cases pending with
  | zero => simp [Streaming.pushLiteral, commitBits]
  | one a => simp [Streaming.pushLiteral, commitBits]
  | two a b => simp [Streaming.pushLiteral, commitBits]
  | three a b c =>
      rcases a with ⟨aSign, aVar⟩
      rcases b with ⟨bSign, bVar⟩
      rcases c with ⟨cSign, cVar⟩
      change encodeTokens emitted ++
          clauseBits aSign aVar bSign bVar true next =
        encodeTokens
          (emitted ++
            CNF.tokens
              [[({ sign := aSign, var := aVar } : Lit),
                ({ sign := bSign, var := bVar } : Lit),
                Lit.pos next]])
      rw [encodeTokens_append,
        clauseBits_eq_encodeTokens_clause_internal]
      simp [Lit.pos]

/-! ## Clause close -/

/-- Closing a pure pending window produces exactly the post-register tuple
specified by `closeClauseTM`.
@isnad1 id=eq.0h3v.s4.06f14909de67 from=translated src=- shape=8da9bbe7 vocab=8a201149
-/
theorem bufferValues_closed_eq_closeClause_internal
    (next : ℕ) (pending : Streaming.Pending) (emitted : List EncToken) :
    (BufferValues.ofStreaming
        { next, pending, scan := .boundary, emitted }).closed
          (PendingSigns.ofStreaming pending) =
      BufferValues.ofStreaming
        (Streaming.closeClause
          { next, pending, scan := .boundary, emitted }) := by
  cases pending <;>
    simp [BufferValues.closed, BufferValues.advanced, BufferValues.cleared,
      BufferValues.ofStreaming, Streaming.closeClause,
      Streaming.Pending.toClause, Clause.tseitinFreshCount]

/-- The chunk selected by `pendingBits` is the canonical token encoding of
the pure pending clause's exact-three transformation.
@isnad1 id=eq.0h2v.s4.7b99c695d107 from=translated src=- shape=25711291 vocab=5c5fb395
-/
theorem pendingBits_eq_to3CNF_tokens_internal
    (next : ℕ) (pending : Streaming.Pending) :
    pendingBits (PendingSigns.ofStreaming pending)
        (BufferValues.ofStreaming
          { next, pending, scan := .boundary, emitted := [] }) =
      encodeTokens ((pending.toClause.to3CNF next).tokens) := by
  cases pending with
  | zero =>
      simp [pendingBits, BufferValues.ofStreaming, Streaming.Pending.toClause,
        Clause.to3CNF, clauseBits_eq_encodeTokens_clause_internal,
        CNF.tokens, encodeTokens_append, Lit.pos, Lit.negVar,
        List.append_assoc]
  | one a =>
      rcases a with ⟨aSign, aVar⟩
      simp [pendingBits, BufferValues.ofStreaming, Streaming.Pending.toClause,
        Clause.to3CNF, clauseBits_eq_encodeTokens_clause_internal]
  | two a b =>
      rcases a with ⟨aSign, aVar⟩
      rcases b with ⟨bSign, bVar⟩
      simp [pendingBits, BufferValues.ofStreaming, Streaming.Pending.toClause,
        Clause.to3CNF, clauseBits_eq_encodeTokens_clause_internal]
  | three a b c =>
      rcases a with ⟨aSign, aVar⟩
      rcases b with ⟨bSign, bVar⟩
      rcases c with ⟨cSign, cVar⟩
      simp [pendingBits, BufferValues.ofStreaming, Streaming.Pending.toClause,
        Clause.to3CNF, clauseBits_eq_encodeTokens_clause_internal]

/-- Appending `pendingBits` to the represented output accumulator yields
exactly the output accumulator of `Streaming.closeClause`.
@isnad1 id=eq.0h3v.s5.acefc14b730d from=translated src=- shape=4a1306ff vocab=f4227e1b
-/
theorem pendingBits_eq_closeClause_emitted_internal
    (next : ℕ) (pending : Streaming.Pending) (emitted : List EncToken) :
    encodeTokens emitted ++
        pendingBits (PendingSigns.ofStreaming pending)
          (BufferValues.ofStreaming
            { next, pending, scan := .boundary, emitted }) =
      encodeTokens
        (Streaming.closeClause
          { next, pending, scan := .boundary, emitted }).emitted := by
  change encodeTokens emitted ++
      pendingBits (PendingSigns.ofStreaming pending)
        (BufferValues.ofStreaming
          { next, pending, scan := .boundary, emitted }) =
    encodeTokens (emitted ++ (pending.toClause.to3CNF next).tokens)
  rw [encodeTokens_append]
  have hchunk := pendingBits_eq_to3CNF_tokens_internal next pending
  simpa [BufferValues.ofStreaming] using congrArg (encodeTokens emitted ++ ·) hchunk

end Machine

end ThreeSAT

end SAT

end Complexity
