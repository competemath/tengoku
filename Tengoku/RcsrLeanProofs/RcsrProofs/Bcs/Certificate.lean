/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/
import Std.Data.HashSet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordination sequence of the bcs net — certified BFS

The bcs net (RCSR symbol `bcs`, space group Ia-3d) is encoded by its canonical
Systre key: an 8-vertex quotient graph over ℤ³ with 24 voltage edges, taken from
the `id bcs` block of the Systre archive `rcsr.arc` (Gavrog distribution).

`bcsShells n` computes the coordination sequence (shell sizes) of the infinite
abelian cover by breadth-first search from vertex 1. The theorem `bcs_shells_25`
kernel-checks the first 26 terms against the submitted OEIS values
1, 6, 24, 56, 98, 152, ... (a(n) = 6n²+2 for n ≥ 3).
-/

namespace Bcs

/-- A state of the infinite periodic graph: (vertex class 1..8, cell in ℤ³),
packed as a flat tuple for hashing.-/
abbrev BfsSt := Nat × Int × Int × Int

/-- The 24 edges of the bcs Systre key: (u, v, voltage). Vertices 1-indexed.-/
def edges : List (Nat × Nat × Int × Int × Int) :=
  [ (1,2,0,0,0), (1,2,0,0,1), (1,3,0,0,0), (1,3,0,1,0), (1,4,0,0,0), (1,4,1,0,0),
    (2,5,-1,-1,1), (2,5,0,0,0), (2,6,0,0,0), (2,6,0,1,0),
    (3,5,-1,-1,1), (3,5,0,-1,1), (3,7,-1,-1,1), (3,7,0,0,0),
    (4,6,-1,0,1), (4,6,0,1,0), (4,7,-1,0,0), (4,7,-1,0,1),
    (5,8,0,0,0), (5,8,0,0,1), (6,8,-1,-1,1), (6,8,0,-1,1),
    (7,8,0,-1,1), (7,8,0,0,1) ]

/-- Directed neighbors of a state: each undirected voltage edge used both ways.-/
def nbrs (s : BfsSt) : List BfsSt :=
  let (v, x, y, z) := s
  edges.foldl (init := []) fun acc (u, w, dx, dy, dz) =>
    let acc := if u == v then (w, x+dx, y+dy, z+dz) :: acc else acc
    if w == v then (u, x-dx, y-dy, z-dz) :: acc else acc

/-- BFS shell sizes from vertex 1 at the origin: `bcsShells n = [|S₀|, ..., |Sₙ|]`.-/
def bcsShells (n : Nat) : Array Nat := Id.run do
  let start : BfsSt := (1, 0, 0, 0)
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
