/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Certificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Systre key, parsed inside the kernel

`bcsKeyLine` is the verbatim `key` line of the `id bcs` block of the RCSR
Systre archive `rcsr.arc` (Gavrog distribution) — byte-for-byte, including
the original spacing. `parseKey` is a first-principles character-level
tokenizer and integer reader over that string (no library string functions
beyond `String.toList`, so every step reduces inside the kernel). The theorem
`parseKey_bcsKeyLine` has the kernel itself verify that parsing the published
key yields exactly the edge list `edges` on which the whole development —
and hence the main theorem `bcs_coordination_sequence` — is built.

What remains outside the kernel after this file is only the claim that
`bcsKeyLine` equals the corresponding line of the published archive: a byte
comparison anyone can perform directly against
`src/org/gavrog/apps/systre/rcsr.arc` in the Gavrog repository.
-/

namespace Bcs

/-- The `key` line of the `id bcs` block of `rcsr.arc`, verbatim.-/
def bcsKeyLine : String :=
  "key      3 1 2 0 0 0 1 2 0 0 1 1 3 0 0 0 1 3 0 1 0 1 4 0 0 0 1 4 1 0 0 2 5 -1 -1 1 2 5 0 0 0 2 6 0 0 0 2 6 0 1 0 3 5 -1 -1 1 3 5 0 -1 1 3 7 -1 -1 1 3 7 0 0 0 4 6 -1 0 1 4 6 0 1 0 4 7 -1 0 0 4 7 -1 0 1 5 8 0 0 0 5 8 0 0 1 6 8 -1 -1 1 6 8 0 -1 1 7 8 0 -1 1 7 8 0 0 1"

/-- Split a character list into space-separated tokens.-/
def tokens (s : List Char) : List (List Char) :=
  (s.foldr
    (fun c acc =>
      if c = ' ' then [] :: acc
      else
        match acc with
        | t :: ts => (c :: t) :: ts
        | [] => [[c]])
    [[]]).filter (· ≠ [])

/-- Read a decimal digit string as a natural number (as `Int`).-/
def readNat (ds : List Char) : Int :=
  ds.foldl (fun a c => a * 10 + ((c.toNat : Int) - 48)) 0

/-- Read an optionally-negated decimal integer.-/
def readInt : List Char → Int
  | '-' :: ds => -(readNat ds)
  | ds => readNat ds

/-- Group a flat integer stream into Systre-key edges `(u, v, dx, dy, dz)`.-/
def groupEdges : List Int → List (Nat × Nat × Int × Int × Int)
  | u :: v :: dx :: dy :: dz :: rest => (u.toNat, v.toNat, dx, dy, dz) :: groupEdges rest
  | _ => []

/-- Parse a Systre `key` line: tokenize, drop the `key` tag and the
dimension, read integers, group into edges.-/
def parseKey (s : String) : List (Nat × Nat × Int × Int × Int) :=
  groupEdges (((tokens s.toList).drop 2).map readInt)

/-- **The kernel checks the transcription**: parsing the verbatim published
key line yields exactly the edge list the development uses.
@isnad1 id=eq.0h0v.s3.e04877bbc731 from=translated src=- shape=17248fe8 vocab=b839d9f0
-/
theorem parseKey_bcsKeyLine : parseKey bcsKeyLine = edges := by
  decide +kernel

end Bcs
