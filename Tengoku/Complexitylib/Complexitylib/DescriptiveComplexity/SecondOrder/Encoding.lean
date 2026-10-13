/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Encoding.Defs
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Encoding.Internal

/-!
# Exact truth-table certificates for second-order witnesses

The encoder bijects Boolean relation environments with all bit strings of the
prescribed length. The decoder rejects exactly incorrect lengths. Nullary
relations take one bit, and an empty context takes no bits. The exact length is
a polynomial in the universe size, for a fixed relation context.
-/

public section

namespace Complexity.DescriptiveComplexity.DecREnv

/-- Every relation-table cell occurs in the certificate enumeration.
@isnad1 id=mem.0h3v.s4.49d163910504 from=translated src=- shape=7bf92869 vocab=eb5ad43d
-/
theorem mem_encodingSites (card : Nat) (rctx : List Nat) (site : EncodingSite card rctx) :
    site ∈ encodingSites card rctx := mem_encodingSites_internal card rctx site

/-- Each relation-table cell occurs exactly once.
@isnad1 id=nodup.0h2v.s3.72236753b46a from=translated src=- shape=0f4d44b1 vocab=2a7084ec
-/
theorem encodingSites_nodup (card : Nat) (rctx : List Nat) :
    (encodingSites card rctx).Nodup := encodingSites_nodup_internal card rctx

/-- The site list has the exact sum-of-powers length.
@isnad1 id=eq.0h2v.s4.4b1f12ee84a9 from=translated src=- shape=330cdc11 vocab=b64e575c
-/
@[simp] theorem encodingSites_length (card : Nat) (rctx : List Nat) :
    (encodingSites card rctx).length = encodingLength card rctx :=
  encodingSites_length_internal card rctx

/-- The empty relation context needs no certificate bits.
@isnad1 id=eq.0h1v.s3.145b169b1751 from=translated src=- shape=8686b4dd vocab=6164cd81
-/
@[simp] theorem encodingLength_nil (card : Nat) : encodingLength card [] = 0 := rfl

/-- Extending the context adds one truth table of length `card ^ k`.
@isnad1 id=eq.0h3v.s5.911dd48fae0f from=translated src=- shape=63254cf4 vocab=c58ec893
-/
@[simp] theorem encodingLength_cons (card k : Nat) (rctx : List Nat) :
    encodingLength card (k :: rctx) = card ^ k + encodingLength card rctx := rfl

/-- The certificate has exactly the sum of its relation-table sizes.
@isnad1 id=eq.0h3v.s4.ed2b084d8150 from=translated src=- shape=08878b77 vocab=383839ea
-/
@[simp] theorem encode_length {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    (encode ρ).length = encodingLength card rctx := by
  simp only [encode, List.length_map, encodingSites_length]

/-- The certificate lists each relation's canonical truth table in context order.
@isnad1 id=eq.0h3v.s5.2384319e83ba from=translated src=- shape=0dcf816f vocab=a98fdabb
-/
theorem encode_eq_flatMap {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    encode ρ = (List.finRange rctx.length).flatMap fun r => encodeRelC (ρ r) := by
  simp [encode, encodingSites, List.map_flatMap, List.map_map, Function.comp_def, encodeRelC]

/-- Extending the environment prepends the new relation's truth table.
@isnad1 id=eq.0h5v.s5.84e34155df5d from=translated src=- shape=ff5895a3 vocab=2d4e4e27
-/
theorem encode_cons {card k : Nat} {rctx : List Nat}
    (S : (Fin k → Fin card) → Bool) (ρ : DecREnv card rctx) :
    encode (ρ.cons S) = encodeRelC S ++ encode ρ := by
  simp only [encode_eq_flatMap, List.length_cons, List.finRange_succ,
    List.flatMap_cons, List.flatMap_map]
  rfl

/-- A single unary relation is encoded in vertex order.
@isnad1 id=eq.0h2v.s6.b509ed91f740 from=translated src=- shape=be6feedf vocab=aa35dba6
-/
theorem encode_unary {card : Nat} (color : Fin card → Bool) :
    encode ((empty card).cons (fun args : Fin 1 → Fin card => color (args 0))) =
      List.ofFn color := by
  rw [encode_cons]
  simp [encode, encodingSites, encodeRelC, allTuples, List.ofFn_eq_map]

/-- Direct reads recover every encoded relation.
@isnad1 id=eq.0h3v.s4.98fd4141ac7b from=translated src=- shape=d5fbd7c8 vocab=e6a2c4e5
-/
@[simp] theorem read_encode {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    read card rctx (encode ρ) = ρ := read_encode_internal ρ

/-- Every string of the specified length is the encoding of its decoded tables.
@isnad1 id=eq.1h3v.s4.2779ba14a4d7 from=translated src=- shape=19042863 vocab=a432c814
-/
theorem encode_read (card : Nat) (rctx : List Nat) (bits : List Bool)
    (h : bits.length = encodingLength card rctx) :
    encode (read card rctx bits) = bits := encode_read_internal card rctx bits h

/-- The checked decoder recovers the supplied relation environment.
@isnad1 id=eq.0h3v.s4.73ad00c43a00 from=translated src=- shape=a088113a vocab=5b57d926
-/
@[simp] theorem decode_encode {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    decode card rctx (encode ρ) = some ρ := by
  simp [decode]

/-- Distinct relation environments have distinct certificates.
@isnad1 id=injectiv.0h2v.s3.2e527fceb980 from=translated src=- shape=7ed84ba3 vocab=a146bed4
-/
theorem encode_injective (card : Nat) (rctx : List Nat) :
    Function.Injective (encode (card := card) (rctx := rctx)) := by
  intro ρ τ h
  simpa only [read_encode] using congrArg (read card rctx) h

/-- Decoding succeeds precisely on a relation environment's canonical encoding.
@isnad1 id=iff.0h4v.s5.082ed27b6d38 from=translated src=- shape=c80d2950 vocab=5e750da7
-/
theorem decode_eq_some_iff {card : Nat} {rctx : List Nat} (bits : List Bool)
    (ρ : DecREnv card rctx) : decode card rctx bits = some ρ ↔ encode ρ = bits := by
  constructor
  · intro h
    unfold decode at h
    split at h
    next hlen =>
      cases Option.some.inj h
      exact encode_read card rctx bits hlen
    next => contradiction
  · rintro rfl
    exact decode_encode ρ

/-- Certificate rejection is exactly a length mismatch.
@isnad1 id=iff.0h3v.s4.a545eb91f768 from=translated src=- shape=1d7b5920 vocab=8dcf1e88
-/
@[simp] theorem decode_eq_none_iff (card : Nat) (rctx : List Nat) (bits : List Bool) :
    decode card rctx bits = none ↔ bits.length ≠ encodingLength card rctx := by
  simp [decode]

/-- Exact witness length is a polynomial in universe cardinality.
@isnad1 id=eq.0h2v.s4.c51b370a0228 from=translated src=- shape=09c391c2 vocab=e1c98660
-/
@[simp] theorem encodingPolynomial_eval (card : Nat) (rctx : List Nat) :
    (encodingPolynomial rctx).eval card = encodingLength card rctx :=
  encodingPolynomial_eval_internal card rctx

/-- Increasing the universe size cannot shorten a relation certificate.
@isnad1 id=monotone.0h1v.s3.d311b5b1b8ca from=translated src=- shape=1c64838b vocab=8ec3eb71
-/
theorem encodingLength_mono (rctx : List Nat) :
    Monotone (fun card => encodingLength card rctx) := encodingLength_mono_internal rctx

end Complexity.DescriptiveComplexity.DecREnv
