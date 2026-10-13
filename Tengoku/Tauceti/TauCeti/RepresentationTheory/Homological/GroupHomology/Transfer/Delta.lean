/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Homological.GroupHomology.LongExactSequence
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Basic

/-!
# Transfer commutes with the connecting map

Let `S` be a finite-index subgroup of a group `G` and `X` a short exact sequence of
`G`-representations. Restricting `X` to `S` keeps it short exact, and the transfer
`Hₙ(G, M) ⟶ Hₙ(S, Res_S M)` commutes with the connecting maps of the two long exact sequences:

`Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`
`    ↓              ↓`
`Hᵢ(S, X₃) ⟶ Hⱼ(S, X₁)`

with `j + 1 = i`. This is what lets a statement about the transfer be moved up or down in degree
by dimension shifting.

## Main results

* `TauCeti.groupHomology.δ_comp_indIso_inv`: the inverse of Shapiro's isomorphism commutes with
  the connecting maps.
* `TauCeti.groupHomology.δ_comp_transfer`: the transfer commutes with the connecting maps.
-/

public section

universe u

open CategoryTheory Rep

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {R G : Type u} [CommRing R] [Group G] (S : Subgroup G)

/-- **Shapiro's isomorphism commutes with the connecting maps.** For a short exact sequence `Y` of
`S`-representations, the inverse of `Hₙ(G, Ind_S^G Y) ≅ Hₙ(S, Y)` intertwines the connecting map
of `Y` with the connecting map of the induced sequence `Ind_S^G Y`. Exactness of `Ind_S^G Y` is a
hypothesis because Mathlib provides left exactness of induction only for finite-index `S`, where
`hIY` is `hY.map_of_exact _`. -/
@[reassoc]
theorem δ_comp_indIso_inv [DecidableEq G] {Y : ShortComplex (Rep.{u} R S)} (hY : Y.ShortExact)
    (hIY : (Y.map (indFunctor R S.subtype)).ShortExact) (i j : ℕ) (hij : j + 1 = i) :
    δ hY i j hij ≫ (indIso S Y.X₁ j).inv = (indIso S Y.X₃ i).inv ≫ δ hIY i j hij := by
  rw [indIso_inv, indIso_inv]
  -- The unit of induction–restriction applied to `Y` is a morphism `Y ⟶ Res_S Ind_S^G Y`. Pinning
  -- the free universe of `indResAdjunction` avoids seconds of universe unification.
  exact δ_naturality _ hY hIY (Y.mapNatTrans (indResAdjunction.{u} R S.subtype).unit) i j hij

end TauCeti.groupHomology
