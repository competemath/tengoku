/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Basic
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Cograph.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport between cograph predicates and the canonical foundation

`Nikoghosyan.Cograph.InducedP4` is a structure with the four distinct vertices,
the three path edges, and the three missing chords. The canonical
`Nikoghosyan.InducedP4` is the same mathematical predicate as a flattened
conjunction. This module records the equivalences; a cotree is not used.
-/

universe u

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The structured induced-`P4` predicate is definitionally the same data as the
canonical flattened conjunction.
@isnad1 id=iff.0h6v.s5.d5d696ebb3c4 from=translated src=- shape=db36992b vocab=66fe4605
-/
lemma inducedP4_iff {G : SimpleGraph V} {a b c d : V} :
    InducedP4 G a b c d ↔ Nikoghosyan.InducedP4 G a b c d := by
  constructor
  · intro h
    exact ⟨h.ne_ab, h.ne_ac, h.ne_ad, h.ne_bc, h.ne_bd, h.ne_cd,
      h.adj_ab, h.adj_bc, h.adj_cd, h.not_ac, h.not_ad, h.not_bd⟩
  · intro h
    rcases h with ⟨nab, nac, nad, nbc, nbd, ncd, eab, ebc, ecd, nac', nad', nbd'⟩
    exact
      { ne_ab := nab
        ne_ac := nac
        ne_ad := nad
        ne_bc := nbc
        ne_bd := nbd
        ne_cd := ncd
        adj_ab := eab
        adj_bc := ebc
        adj_cd := ecd
        not_ac := nac'
        not_ad := nad'
        not_bd := nbd' }

/--
@isnad1 id=iff.0h3v.s4.b862c9bf940d from=translated src=- shape=ad908040 vocab=a04c5600
-/
lemma isCograph_iff {G : SimpleGraph V} {U : Finset V} :
    IsCograph G U ↔ Nikoghosyan.IsCograph G U := by
  constructor
  · intro h a b c d ha hb hc hd hp
    exact h ha hb hc hd (inducedP4_iff.2 hp)
  · intro h a b c d ha hb hc hd hp
    exact h ha hb hc hd (inducedP4_iff.1 hp)

/--
@isnad1 id=iff.0h2v.s4.e5c28459cd71 from=translated src=- shape=0e29dda8 vocab=df07e1df
-/
lemma noInducedP4UnionP1_iff {G : SimpleGraph V} :
    NoInducedP4UnionP1 G ↔ Nikoghosyan.NoInducedP4UnionP1 G := by
  constructor
  · intro h a b c d x hp hxa hxb hxc hxd
    exact h (inducedP4_iff.2 hp) hxa hxb hxc hxd
  · intro h a b c d x hp hxa hxb hxc hxd
    exact h (inducedP4_iff.1 hp) hxa hxb hxc hxd

/--
@isnad1 id=iff.0h2v.s4.37306c8940b1 from=translated src=- shape=8efafc73 vocab=21adf52f
-/
lemma isCographGraph_iff_isCograph_univ {G : SimpleGraph V} :
    IsCographGraph G ↔ Nikoghosyan.IsCograph G Finset.univ := by
  rw [isCographGraph_iff_univ, isCograph_iff]

/-- Canonical `antineighbors` is the finset of the set-valued `antineighborhood`.
@isnad1 id=eq.0h3v.s5.5879893d0eb6 from=translated src=- shape=c4c45b2f vocab=7a867be8
-/
lemma antineighbors_coe (G : SimpleGraph V) (v : V) :
    (Nikoghosyan.antineighbors G v : Set V) = antineighborhood G v := by
  ext x
  simp [Nikoghosyan.antineighbors, antineighborhood]

end Cograph
end Nikoghosyan
