/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Certificate
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Distance
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `Adj` agrees with `nbrs`: the two hand transcriptions of the bcs net coincide

`RcsrProofs/Bcs/Certificate.lean` encodes the bcs net's 24 voltage edges as the
flat list `edges` and derives directed neighbors `nbrs : BfsSt → List BfsSt`
by folding over it. `RcsrProofs/Bcs/Distance.lean` independently encodes the same
graph as the inductive relation `Adj : St → St → Prop` with 48 constructors
(one per directed edge). These are two separate hand transcriptions of one
graph; nothing before this file ties them together at the kernel level.

`adj_iff_mem_nbrs` closes that gap: `Adj` and membership in `nbrs` agree on
every state, class-by-class. Combined with `RcsrProofs/Bcs/KeyParse.lean`
(published Systre key string parses to `edges`), this completes the chain
key → `edges` → `Adj`.
-/

namespace Bcs

/-! ## Helper lemmas: `nbrs` on a literal class reduces to an explicit list

For each class `c ∈ 1..8`, `nbrs (c, x, y, z)` unfolds (via the `edges` fold)
to an explicit 6-element list once the class-literal equality tests in the
fold are decided. The pattern is the same for every class: unfold `nbrs` and
`edges`, evaluate the `Nat` literal `BEq` tests with `Nat.reduceBEq`, discharge
the resulting `if false = true then _ else _` shape, and clean up the trivial
`+0` / `-0` / `- (-1) = + 1` arithmetic that appears in the untraveled voltage
components. -/

-- Each fold-unfolding simp call walks the full 24-entry edges list; the default
-- heartbeat budget is occasionally too tight for the elaborator on this machine.
set_option maxHeartbeats 8000000 in
/--
@isnad1 id=eq.0h3v.s8.f845c41593ed from=translated src=- shape=be888048 vocab=f9d36231
-/
theorem nbrs_one (x y z : Int) :
    nbrs (1, x, y, z) =
      [(4, x+1, y, z), (4, x, y, z), (3, x, y+1, z), (3, x, y, z),
       (2, x, y, z+1), (2, x, y, z)] := by
  simp only [nbrs, edges, List.foldl, Nat.reduceBEq, Bool.false_eq_true, ite_false,
    ite_true, add_zero, sub_zero, sub_neg_eq_add, Int.add_neg_eq_sub]

-- Each fold-unfolding simp call walks the full 24-entry edges list; the default
-- heartbeat budget is occasionally too tight for the elaborator on this machine.
set_option maxHeartbeats 8000000 in
/--
@isnad1 id=eq.0h3v.s8.231d8787de6c from=translated src=- shape=b0a26d60 vocab=75c781f0
-/
theorem nbrs_two (x y z : Int) :
    nbrs (2, x, y, z) =
      [(6, x, y+1, z), (6, x, y, z), (5, x, y, z), (5, x-1, y-1, z+1),
       (1, x, y, z-1), (1, x, y, z)] := by
  simp only [nbrs, edges, List.foldl, Nat.reduceBEq, Bool.false_eq_true, ite_false,
    ite_true, add_zero, sub_zero, sub_neg_eq_add, Int.add_neg_eq_sub]

-- Each fold-unfolding simp call walks the full 24-entry edges list; the default
-- heartbeat budget is occasionally too tight for the elaborator on this machine.
set_option maxHeartbeats 8000000 in
/--
@isnad1 id=eq.0h3v.s8.c0513cd1452e from=translated src=- shape=94e52c42 vocab=75c781f0
-/
theorem nbrs_three (x y z : Int) :
    nbrs (3, x, y, z) =
      [(7, x, y, z), (7, x-1, y-1, z+1), (5, x, y-1, z+1), (5, x-1, y-1, z+1),
       (1, x, y-1, z), (1, x, y, z)] := by
  simp only [nbrs, edges, List.foldl, Nat.reduceBEq, Bool.false_eq_true, ite_false,
    ite_true, add_zero, sub_zero, sub_neg_eq_add, Int.add_neg_eq_sub]

-- Each fold-unfolding simp call walks the full 24-entry edges list; the default
-- heartbeat budget is occasionally too tight for the elaborator on this machine.
set_option maxHeartbeats 8000000 in
/--
@isnad1 id=eq.0h3v.s8.d9147f0dae1e from=translated src=- shape=d3b6ac35 vocab=75c781f0
-/
theorem nbrs_four (x y z : Int) :
    nbrs (4, x, y, z) =
      [(7, x-1, y, z+1), (7, x-1, y, z), (6, x, y+1, z), (6, x-1, y, z+1),
       (1, x-1, y, z), (1, x, y, z)] := by
  simp only [nbrs, edges, List.foldl, Nat.reduceBEq, Bool.false_eq_true, ite_false,
    ite_true, add_zero, sub_zero, sub_neg_eq_add, Int.add_neg_eq_sub]

-- Each fold-unfolding simp call walks the full 24-entry edges list; the default
-- heartbeat budget is occasionally too tight for the elaborator on this machine.
set_option maxHeartbeats 8000000 in
/--
@isnad1 id=eq.0h3v.s8.50d762a3a5ad from=translated src=- shape=913bdc82 vocab=75c781f0
-/
theorem nbrs_five (x y z : Int) :
    nbrs (5, x, y, z) =
      [(8, x, y, z+1), (8, x, y, z), (3, x, y+1, z-1), (3, x+1, y+1, z-1),
       (2, x, y, z), (2, x+1, y+1, z-1)] := by
  simp only [nbrs, edges, List.foldl, Nat.reduceBEq, Bool.false_eq_true, ite_false,
    ite_true, add_zero, sub_zero, sub_neg_eq_add, Int.add_neg_eq_sub]

-- Each fold-unfolding simp call walks the full 24-entry edges list; the default
-- heartbeat budget is occasionally too tight for the elaborator on this machine.
set_option maxHeartbeats 8000000 in
/--
@isnad1 id=eq.0h3v.s8.9bd07457a680 from=translated src=- shape=18f7fdaf vocab=75c781f0
-/
theorem nbrs_six (x y z : Int) :
    nbrs (6, x, y, z) =
      [(8, x, y-1, z+1), (8, x-1, y-1, z+1), (4, x, y-1, z), (4, x+1, y, z-1),
       (2, x, y-1, z), (2, x, y, z)] := by
  simp only [nbrs, edges, List.foldl, Nat.reduceBEq, Bool.false_eq_true, ite_false,
    ite_true, add_zero, sub_zero, sub_neg_eq_add, Int.add_neg_eq_sub]

-- Each fold-unfolding simp call walks the full 24-entry edges list; the default
-- heartbeat budget is occasionally too tight for the elaborator on this machine.
set_option maxHeartbeats 8000000 in
/--
@isnad1 id=eq.0h3v.s8.51e7cf342274 from=translated src=- shape=641e67ff vocab=75c781f0
-/
theorem nbrs_seven (x y z : Int) :
    nbrs (7, x, y, z) =
      [(8, x, y, z+1), (8, x, y-1, z+1), (4, x+1, y, z-1), (4, x+1, y, z),
       (3, x, y, z), (3, x+1, y+1, z-1)] := by
  simp only [nbrs, edges, List.foldl, Nat.reduceBEq, Bool.false_eq_true, ite_false,
    ite_true, add_zero, sub_zero, sub_neg_eq_add, Int.add_neg_eq_sub]

-- Each fold-unfolding simp call walks the full 24-entry edges list; the default
-- heartbeat budget is occasionally too tight for the elaborator on this machine.
set_option maxHeartbeats 8000000 in
/--
@isnad1 id=eq.0h3v.s8.c125164c8ffb from=translated src=- shape=f3bb3cb0 vocab=75c781f0
-/
theorem nbrs_eight (x y z : Int) :
    nbrs (8, x, y, z) =
      [(7, x, y, z-1), (7, x, y+1, z-1), (6, x, y+1, z-1), (6, x+1, y+1, z-1),
       (5, x, y, z-1), (5, x, y, z)] := by
  simp only [nbrs, edges, List.foldl, Nat.reduceBEq, Bool.false_eq_true, ite_false,
    ite_true, add_zero, sub_zero, sub_neg_eq_add, Int.add_neg_eq_sub]

/-! ## Main theorem: `Adj` agrees with `nbrs`

`Adj` uses `Fin 8` classes `0..7`; `nbrs` uses `Nat` classes `1..8` (`v.val + 1`
recovers the `nbrs` class from an `Adj` class). After `fin_cases v` fixes the
source class, the `nbrs_*` helper lemmas turn the membership side into an
explicit 6-element list. Forward: `cases h` restricts to the (at most) 6
`Adj` constructors that could produce that source class, and each is one of
the 6 listed neighbors (`tauto` closes the purely propositional shape once
`and_true`/`true_and` clear the trivial `True` conjuncts that `omega` alone
cannot see through; the remaining cases with genuine `Int` arithmetic go to
`omega`). Backward: `fin_cases w` fixes the target
class too, then `rcases` splits the 6-way membership disjunction; 5 of the 6
disjuncts carry a false `Nat`-literal class equation killed by `omega`, and
the true one rewrites the target cell coordinates and matches the
correspondingly-shaped `Adj` constructor. -/

set_option maxHeartbeats 8000000 in
/--
@isnad1 id=iff.0h8v.s7.264b29e495c3 from=translated src=- shape=e42198c4 vocab=25d1de42
-/
theorem adj_iff_mem_nbrs (v w : Fin 8) (x y z x' y' z' : Int) :
    Adj (v, x, y, z) (w, x', y', z') ↔
      ((w.val + 1 : Nat), x', y', z') ∈ nbrs ((v.val + 1 : Nat), x, y, z) := by
  fin_cases v <;>
  · constructor
    · intro h
      cases h <;>
        simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd, nbrs_one, nbrs_two,
          nbrs_three, nbrs_four, nbrs_five, nbrs_six, nbrs_seven, nbrs_eight, List.mem_cons,
          List.not_mem_nil, or_false, Prod.mk.injEq, and_true, true_and] <;>
        first | tauto | omega
    · intro h
      simp only [Nat.reduceAdd, nbrs_one, nbrs_two, nbrs_three,
        nbrs_four, nbrs_five, nbrs_six, nbrs_seven, nbrs_eight] at h
      fin_cases w <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h <;>
        (rcases h with ⟨h1,hx,hy,hz⟩|⟨h1,hx,hy,hz⟩|⟨h1,hx,hy,hz⟩|⟨h1,hx,hy,hz⟩|⟨h1,hx,hy,hz⟩|⟨h1,hx,hy,hz⟩ <;>
          first
            | omega
            | (rw [hx, hy, hz];
               -- Each call supplies the constructor's own (a,b,c) so its conclusion's
               -- *source* cell is literally (x,y,z): for constructors whose source
               -- coordinate carries a shift (e.g. `e1_12'`'s source is `(1,x,y,z+1)`),
               -- the call must pre-invert that shift (`z-1` in that example), which
               -- leaves a `z-1+1` needing ring normalization (not just defeq) to match
               -- the ambient `z` — hence `simpa` throughout rather than bare `exact`.
               first
                 | exact Adj.e0_12 x y z    | exact Adj.e1_12 x y z
                 | exact Adj.e2_13 x y z    | exact Adj.e3_13 x y z
                 | exact Adj.e4_14 x y z    | exact Adj.e5_14 x y z
                 | exact Adj.e0_12' x y z   | simpa using Adj.e1_12' x y (z-1)
                 | exact Adj.e2_13' x y z   | simpa using Adj.e3_13' x (y-1) z
                 | exact Adj.e4_14' x y z   | simpa using Adj.e5_14' (x-1) y z
                 | exact Adj.e6_25 x y z    | exact Adj.e7_25 x y z
                 | exact Adj.e8_26 x y z    | exact Adj.e9_26 x y z
                 | simpa using Adj.e6_25' (x+1) (y+1) (z-1) | exact Adj.e7_25' x y z
                 | exact Adj.e8_26' x y z   | simpa using Adj.e9_26' x (y-1) z
                 | exact Adj.e10_35 x y z   | exact Adj.e11_35 x y z
                 | exact Adj.e12_37 x y z   | exact Adj.e13_37 x y z
                 | simpa using Adj.e10_35' (x+1) (y+1) (z-1)
                 | simpa using Adj.e11_35' x (y+1) (z-1)
                 | simpa using Adj.e12_37' (x+1) (y+1) (z-1) | exact Adj.e13_37' x y z
                 | exact Adj.e14_46 x y z   | exact Adj.e15_46 x y z
                 | exact Adj.e16_47 x y z   | exact Adj.e17_47 x y z
                 | simpa using Adj.e14_46' (x+1) y (z-1)
                 | simpa using Adj.e15_46' x (y-1) z
                 | simpa using Adj.e16_47' (x+1) y z
                 | simpa using Adj.e17_47' (x+1) y (z-1)
                 | exact Adj.e18_58 x y z   | exact Adj.e19_58 x y z
                 | exact Adj.e20_68 x y z   | exact Adj.e21_68 x y z
                 | exact Adj.e18_58' x y z  | simpa using Adj.e19_58' x y (z-1)
                 | simpa using Adj.e20_68' (x+1) (y+1) (z-1)
                 | simpa using Adj.e21_68' x (y+1) (z-1)
                 | exact Adj.e22_78 x y z   | exact Adj.e23_78 x y z
                 | simpa using Adj.e22_78' x (y+1) (z-1)
                 | simpa using Adj.e23_78' x y (z-1)))

/-! ## Corroboration: the BFS shell computation doesn't depend on start class

`bcsShells` starts the BFS from vertex class 1. `bcsShellsFrom` parameterizes
the start class, so any of the 8 (isomorphic, by vertex-transitivity of the
bcs net) starting points should give the same coordination sequence. This is
a computational corroboration of that transitivity, checked by compiled
evaluation off the main `adj_iff_mem_nbrs` proof path. -/

/-- BFS shell sizes from the given start class at the origin cell, generalizing
`bcsShells` (which fixes `start = 1`).-/
def bcsShellsFrom (start : Nat) (n : Nat) : Array Nat := Id.run do
  let start : BfsSt := (start, 0, 0, 0)
  let mut seen : Std.HashSet BfsSt := (Std.HashSet.emptyWithCapacity).insert start
  let mut frontier : Array BfsSt := #[start]
  let mut out : Array Nat := #[1]
  for _ in [0:n] do
    let mut next : Array BfsSt := #[]
    for s in frontier do
      for t in nbrs s do
        if !seen.contains t then
          seen := seen.insert t
          next := next.push t
    out := out.push next.size
    frontier := next
  return out

end Bcs
