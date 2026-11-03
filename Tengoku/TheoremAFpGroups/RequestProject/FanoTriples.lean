module

public import Tengoku.TheoremAFpGroups.RequestProject.GirthKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Fano-plane triple system (Proposition 3.2 of the revised manuscript)

Points and lines are numbered modulo seven, with `L_j = {j, j+1, j+3}`.
The retained flags are numbered as follows:

* `0` is the distinguished index, `1` is `a`, and `2` is `b`;
* `f_{j,0}` has number `3+j`, and `f_{j,1}` has number `10+j`;
* `f_{j,3}` has number `16+j`, for `1 ≤ j ≤ 6`.

The missing flag `f_{0,3}` is replaced by `b` in the point triple at `3`,
and by `a` in the line triple at `0`. The extra triple is `(b,0) → a`.
The definitions below follow these formulas, rather than using a searched example.

All finite checks are evaluated by the Lean kernel. The existing soundness
theorems turn the checks into the actual girth bound and integral row identity.
No externally executed computation is part of the proof.
-/

@[expose] public section

namespace FanoTriples

open TripleSystem

def a : ℕ := 1
def b : ℕ := 2
def flag0 (j : ℕ) : ℕ := 3 + j
def flag1 (j : ℕ) : ℕ := 10 + j
/-- Used only for the retained flags, i.e. `1 ≤ j ≤ 6`.-/
def flag3 (j : ℕ) : ℕ := 16 + j

/-- The twenty retained flags and the three additional indices give exactly `Fin 23`.
@isnad1 id=eq.0h0v.s6.80a19d4e1979 from=translated src=- shape=256252aa vocab=d1200ff3
-/
theorem index_labels :
    [0, a, b] ++ (List.range 7).map flag0 ++ (List.range 7).map flag1 ++
      (List.range 6).map (fun j => flag3 (j + 1)) = List.range 23 := by
  decide +kernel

/-- The triple `π_p` of flags through point `p`, replacing `f_{0,3}` by `b`.-/
def pointTriple (p : ℕ) : Triple :=
  (flag0 p, flag1 ((p + 6) % 7), if p = 3 then b else flag3 ((p + 4) % 7))

/-- The triple `λ_j` of flags on line `L_j`, replacing `f_{0,3}` by `a`.-/
def lineTriple (j : ℕ) : Triple :=
  (flag0 j, flag1 j, if j = 0 then a else flag3 j)

/-- The triple subdividing the removed flag, with the distinguished pendant index.-/
def gamma : Triple := (b, 0, a)

/-- The order is `π_0,...,π_6,λ_0,...,λ_6,γ`.-/
def triples : List Triple :=
  (List.range 7).map pointTriple ++ (List.range 7).map lineTriple ++ [gamma]

/--
@isnad1 id=eq.0h0v.s3.b107e23fb418 from=translated src=- shape=b3c4969c vocab=61e5ad52
-/
theorem triples_length : triples.length = 15 := by decide +kernel

/-- The list represents a set of fifteen different triples, as in Definition 3.1.
@isnad1 id=nodup.0h0v.s1.9ce68366e8ab from=translated src=- shape=25b03439 vocab=1ec1d613
-/
theorem triples_nodup : triples.Nodup := by decide +kernel

/-- The coefficients are `+1` at point triples and `γ`, and `-1` at line triples.-/
def nu (l : Fin triples.length) : ℤ :=
  if l.val < 7 then 1 else if l.val < 14 then -1 else 1

/--
@isnad1 id=or.0h1v.s4.7dc674b5d605 from=translated src=- shape=1c0ff9e5 vocab=0d203bef
-/
theorem nu_unit (l : Fin triples.length) : nu l = 1 ∨ nu l = -1 := by
  simp only [nu]
  split_ifs <;> simp

/--
@isnad1 id=eq.0h0v.s3.1a7c92097937 from=translated src=- shape=801679d3 vocab=21a0a013
-/
theorem wellFormed_check : wellFormedCheck 23 triples = true := by decide +kernel

/--
@isnad1 id=wellform.0h0v.s2.d8f85b5813d5 from=translated src=- shape=cef8a6bf vocab=09fdb5ea
-/
theorem wellFormed : WellFormed 23 triples :=
  wellFormed_of_wellFormedCheck 23 triples wellFormed_check

set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h0v.s3.cdf20263c8c9 from=translated src=- shape=4fcb0093 vocab=66d4d984
-/
theorem row_check : rowCheck 23 triples nu = true := by decide +kernel

/-- Equation (3.2), with the signs prescribed in the manuscript.
@isnad1 id=rowident.0h0v.s3.fb405cbe4073 from=translated src=- shape=fb58fac9 vocab=888bf996
-/
theorem rowIdentity : RowIdentity 23 triples nu :=
  rowIdentity_of_rowCheck 23 triples nu row_check

/-- The incidence neighbors, numbered `0,...,22` and then `23,...,37`.-/
def neighbors (v : ℕ) : List ℕ :=
  if v < 23 then
    triples.zipIdx.filterMap (fun (t, l) =>
      if GirthKernel.memN v t.entries then some (23 + l) else none)
  else if v < 38 then (triples[v - 23]?.getD (0, 0, 0)).entries else []

/-- Store a finite table in the kernel-friendly binary-tree representation.-/
def tableTree : ℕ → (ℕ → List ℕ) → GirthKernel.NTree
  | 0, _ => .leaf
  | k + 1, f => .node (tableTree k (fun i => f (2 * i + 1))) (f 0)
      (tableTree k (fun i => f (2 * i + 2)))

def tree : GirthKernel.NTree := tableTree 6 neighbors

set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h0v.s4.ca5c63432325 from=translated src=- shape=826c4bcd vocab=d9171ee5
-/
theorem incidence_check : GirthKernel.incCheck tree 23 0 triples = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/--
@isnad1 id=eq.0h0v.s3.922e976bf0d8 from=translated src=- shape=c1506343 vocab=0dcad026
-/
theorem girth_check : GirthKernel.girthCheckN 38 tree 23 = true := by decide +kernel

end FanoTriples
