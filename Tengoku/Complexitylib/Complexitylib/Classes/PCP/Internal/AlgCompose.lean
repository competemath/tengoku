/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.LocalTest
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.NumEncPi
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.Compose

/-!
# The composed graph, in numbers

The binary graph a family of tests produces has one vertex per position and per
(test, random string), and one edge per (test, random string, read). Both are
numbered by `NumEnc`, so an edge index splits by division and remainder into the
test, the string and the read, and the two endpoints are read off from there.

## Main results

- `Complexity.MultiTest.enc_edgeOf` — the edge a number names carries that number
- `Complexity.MultiTest.enc_edge` — how an edge's number splits
- `Complexity.MultiTest.val_tail_toGraph`, `val_head_toGraph` — the endpoints
- `Complexity.RegCSP.enc_pos_inl`, `enc_pos_lin`, `enc_pos_quad` — the three
  kinds of position of the composed proof
-/

@[expose] public section

namespace Complexity

namespace MultiTest

open NumEnc BooleanAnalysis

variable {Pos E Q : Type} (M : MultiTest Pos E Q) [Fintype Pos] [Fintype E] [Fintype Q]
  [NumEnc Pos] [NumEnc E] [NumEnc Q]

omit [Fintype Pos] [NumEnc Pos] in
/--
@isnad1 id=eq.0h5v.s7.301056b3736f from=translated src=- shape=7fc25e64 vocab=3bc31a28
-/
theorem enc_edgeOf (k : Fin (Fintype.card M.Edge)) : enc (M.edgeOf k) = k.val := by
  show enc ((NumEnc.equivFinCard M.Edge).symm k) = _
  have h : (NumEnc.equivFinCard M.Edge ((NumEnc.equivFinCard M.Edge).symm k)).val = k.val :=
    congrArg Fin.val (Equiv.apply_symm_apply _ _)
  exact h

omit [Fintype Q] [NumEnc Q] in
/--
@isnad1 id=eq.0h5v.s7.415b1d0ed753 from=translated src=- shape=135367c8 vocab=6496e38c
-/
theorem val_vertIdx (v : M.Vert) : (M.vertIdx v).val = enc v := rfl

omit [Fintype Pos] [Fintype E] [Fintype Q] [NumEnc Pos] in
/-- **How an edge's number splits**: the test, then the random string, then the
read.
@isnad1 id=eq.0h5v.s7.8f9712d71d22 from=translated src=- shape=053ec859 vocab=eeb2cc31
-/
theorem enc_edge (x : M.Edge) :
    enc x = enc x.1 * (card (Cube M.R) * card Q) + (enc x.2.1 * card Q + enc x.2.2) := rfl

/-- **The first endpoint**: the test vertex, numbered after all the positions.
@isnad1 id=eq.0h5v.s7.d4cf2976f5c0 from=translated src=- shape=8d353567 vocab=f79903c8
-/
theorem val_tail_toGraph (k : Fin (Fintype.card M.Edge)) :
    (M.toGraph.tail k).val
      = card Pos + (enc (M.edgeOf k).1 * card (Cube M.R) + enc (M.edgeOf k).2.1) := rfl

/-- **The second endpoint**: the position the read asks for.
@isnad1 id=eq.0h5v.s7.31ed3cf41dab from=translated src=- shape=697c9b42 vocab=16deda1a
-/
theorem val_head_toGraph (k : Fin (Fintype.card M.Edge)) :
    (M.toGraph.head k).val
      = enc (M.pos (M.edgeOf k).1 (M.edgeOf k).2.1 (M.edgeOf k).2.2) := rfl

end MultiTest

/-! ### The composed proof's positions -/

namespace RegCSP

open NumEnc BooleanAnalysis Tester

variable {β : Type} [Fintype β] [DecidableEq β] [Nonempty β] (R : RegCSP β)
  [NumEnc R.graph.V] [NumEnc R.graph.D] {B : ℕ}

omit [Fintype β] [DecidableEq β] [Nonempty β] in
/-- **A position in a vertex's encoding block.**
@isnad1 id=eq.0h5v.s8.3a85f504ca9e from=translated src=- shape=fc97738b vocab=871d74b7
-/
theorem enc_pos_inl (v : R.graph.V) (y : Cube B) :
    NumEnc.enc (Sum.inl (v, y) : R.Pos (B := B))
      = NumEnc.enc v * card (Cube B) + NumEnc.enc y := rfl

omit [Fintype β] [DecidableEq β] [Nonempty β] in
/-- **A position in a dart's linear table**, after all the encoding blocks.
@isnad1 id=eq.0h5v.s8.30629537e535 from=translated src=- shape=810cb9f2 vocab=edbbf4e9
-/
theorem enc_pos_lin (p : R.Dart) (y : Cube (nOf B)) :
    NumEnc.enc (Sum.inr (Sum.inl (p, y)) : R.Pos (B := B))
      = card R.graph.V * card (Cube B)
        + (NumEnc.enc p * card (Cube (nOf B)) + NumEnc.enc y) := rfl

omit [Fintype β] [DecidableEq β] [Nonempty β] in
/-- **A position in a dart's quadratic table**, after the linear ones.
@isnad1 id=eq.0h5v.s8.ad526487ce43 from=translated src=- shape=8e13269d vocab=da33a5b1
-/
theorem enc_pos_quad (p : R.Dart) (y : Cube (nOf B * nOf B)) :
    NumEnc.enc (Sum.inr (Sum.inr (p, y)) : R.Pos (B := B))
      = card R.graph.V * card (Cube B)
        + (card R.Dart * card (Cube (nOf B))
          + (NumEnc.enc p * card (Cube (nOf B * nOf B)) + NumEnc.enc y)) := rfl

omit [Fintype β] [DecidableEq β] [Nonempty β] in
/-- **A dart's number splits into its vertex and its label.**
@isnad1 id=eq.0h3v.s6.568098d4d783 from=translated src=- shape=fe93cef3 vocab=bbdec71c
-/
theorem enc_dart (p : R.Dart) :
    NumEnc.enc p = NumEnc.enc p.1 * card R.graph.D + NumEnc.enc p.2 := rfl

end RegCSP

end Complexity
