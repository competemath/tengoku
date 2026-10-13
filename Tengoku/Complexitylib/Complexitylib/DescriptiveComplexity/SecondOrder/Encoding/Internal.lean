/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.DescriptiveComplexity.SecondOrder.Encoding.Defs
public import Tengoku

/-!
# Relation-certificate encoding proofs

Completeness and cardinality of the site enumeration give absence of duplicates.
Reading at a site's index then yields both directions of the encoding bijection.
-/

public section

namespace Complexity.DescriptiveComplexity.DecREnv

/--
@isnad1 id=mem.0h3v.s4.49d163910504 from=translated src=- shape=7bf92869 vocab=eb5ad43d
-/
theorem mem_encodingSites_internal (card : Nat) (rctx : List Nat)
    (site : EncodingSite card rctx) : site ∈ encodingSites card rctx := by
  rcases site with ⟨r, args⟩
  simp [encodingSites, mem_allTuples]

/--
@isnad1 id=eq.0h2v.s4.4b1f12ee84a9 from=translated src=- shape=330cdc11 vocab=b64e575c
-/
theorem encodingSites_length_internal (card : Nat) (rctx : List Nat) :
    (encodingSites card rctx).length = encodingLength card rctx := by
  simp [encodingSites, List.length_flatMap, allTuples_length, encodingLength,
    ← List.ofFn_eq_map, List.get_eq_getElem]

/--
@isnad1 id=nodup.0h2v.s3.72236753b46a from=translated src=- shape=0f4d44b1 vocab=2a7084ec
-/
theorem encodingSites_nodup_internal (card : Nat) (rctx : List Nat) :
    (encodingSites card rctx).Nodup := by
  have hall : (encodingSites card rctx).toFinset = Finset.univ := by
    ext site
    simp [mem_encodingSites_internal]
  apply (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (encodingSites card rctx : Multiset (EncodingSite card rctx)))).mp
  change (encodingSites card rctx).toFinset.card = (encodingSites card rctx).length
  rw [hall, Finset.card_univ, encodingSites_length_internal]
  simp [Fintype.card_sigma, encodingLength, ← List.sum_ofFn, List.get_eq_getElem]

/--
@isnad1 id=eq.0h3v.s4.98fd4141ac7b from=translated src=- shape=d5fbd7c8 vocab=e6a2c4e5
-/
theorem read_encode_internal {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    read card rctx (encode ρ) = ρ := by
  funext r args
  simp [read, encode, List.getElem?_idxOf (mem_encodingSites_internal card rctx ⟨r, args⟩)]

/--
@isnad1 id=eq.1h3v.s4.2779ba14a4d7 from=translated src=- shape=19042863 vocab=a432c814
-/
theorem encode_read_internal (card : Nat) (rctx : List Nat) (bits : List Bool)
    (h : bits.length = encodingLength card rctx) :
    encode (read card rctx bits) = bits := by
  have hlen : (encodingSites card rctx).length = bits.length :=
    (encodingSites_length_internal card rctx).trans h.symm
  apply List.ext_getElem (by simp [encode, hlen])
  intro i hi hj
  simp only [encode, List.getElem_map, read,
    (encodingSites_nodup_internal card rctx).idxOf_getElem]
  simp [List.getElem?_eq_getElem hj]

/--
@isnad1 id=eq.0h2v.s4.c51b370a0228 from=translated src=- shape=09c391c2 vocab=e1c98660
-/
theorem encodingPolynomial_eval_internal (card : Nat) (rctx : List Nat) :
    (encodingPolynomial rctx).eval card = encodingLength card rctx := by
  induction rctx with
  | nil => simp [encodingPolynomial, encodingLength]
  | cons k rctx ih =>
    simpa [encodingPolynomial, encodingLength, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X] using congrArg (card ^ k + ·) ih

/--
@isnad1 id=monotone.0h1v.s3.d311b5b1b8ca from=translated src=- shape=1c64838b vocab=8ec3eb71
-/
theorem encodingLength_mono_internal (rctx : List Nat) :
    Monotone (fun card => encodingLength card rctx) := by
  intro a b hab
  induction rctx with
  | nil => rfl
  | cons k rctx ih =>
    exact Nat.add_le_add (Nat.pow_le_pow_left hab k) ih

end Complexity.DescriptiveComplexity.DecREnv
