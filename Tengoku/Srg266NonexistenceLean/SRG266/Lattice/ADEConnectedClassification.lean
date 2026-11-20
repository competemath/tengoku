/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADETripodStandard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open SimpleGraph

variable {V : Type*}

def ConnectedADECoordinates [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ t : ADEType, t.IsRegular ∧ t.rank = Fintype.card V ∧
    ∃ coord : Fin t.rank ≃ V, ∀ i j,
      graphCartanMatrix G (coord i) (coord j) = t.gram i j

/--
@isnad1 id=connecte.1h4v.s5.96548ee5f056 from=translated src=- shape=e6043de8 vocab=eab8d256
-/
theorem connectedADECoordinates_of_dTripodIso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {t : ℕ} (ht : 0 < t) (g : tripodGraph 1 1 t ≃g G) :
    ConnectedADECoordinates G := by
  let e : Fin (t + 3) ≃ V := (dTripodEquiv t ht).trans g.toEquiv
  refine ⟨.D (t + 3), by simp only [ADEType.IsRegular]; omega, ?_, e, ?_⟩
  · simpa only [ADEType.rank, Fintype.card_fin] using Fintype.card_congr e
  · intro i j
    change graphCartanMatrix G (e i) (e j) = gramD (t + 3) i j
    calc
      _ = graphCartanMatrix (tripodGraph 1 1 t)
          (dTripodEquiv t ht i) (dTripodEquiv t ht j) :=
        graphCartanMatrix_apply_iso g _ _
      _ = gramD (t + 3) i j := graphCartanMatrix_dTripod t ht i j

/--
@isnad1 id=connecte.0h3v.s5.7f7fd940a0ca from=translated src=- shape=ac98b8dc vocab=0a0302d7
-/
theorem connectedADECoordinates_of_e6TripodIso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (g : tripodGraph 1 2 2 ≃g G) : ConnectedADECoordinates G := by
  let e : Fin 6 ≃ V := e6TripodEquiv.trans g.toEquiv
  refine ⟨.E6, by simp only [ADEType.IsRegular], ?_, e, ?_⟩
  · simpa only [ADEType.rank, Fintype.card_fin] using Fintype.card_congr e
  · intro i j
    change graphCartanMatrix G (e i) (e j) = gramE 6 i j
    calc
      _ = graphCartanMatrix (tripodGraph 1 2 2)
          (e6TripodEquiv i) (e6TripodEquiv j) := graphCartanMatrix_apply_iso g _ _
      _ = gramE 6 i j := graphCartanMatrix_e6Tripod i j

/--
@isnad1 id=connecte.0h3v.s5.ae9e07bb52cd from=translated src=- shape=ac98b8dc vocab=0a0302d7
-/
theorem connectedADECoordinates_of_e7TripodIso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (g : tripodGraph 1 2 3 ≃g G) : ConnectedADECoordinates G := by
  let e : Fin 7 ≃ V := e7TripodEquiv.trans g.toEquiv
  refine ⟨.E7, by simp only [ADEType.IsRegular], ?_, e, ?_⟩
  · simpa only [ADEType.rank, Fintype.card_fin] using Fintype.card_congr e
  · intro i j
    change graphCartanMatrix G (e i) (e j) = gramE 7 i j
    calc
      _ = graphCartanMatrix (tripodGraph 1 2 3)
          (e7TripodEquiv i) (e7TripodEquiv j) := graphCartanMatrix_apply_iso g _ _
      _ = gramE 7 i j := graphCartanMatrix_e7Tripod i j

/--
@isnad1 id=connecte.0h3v.s5.38b65ef69f45 from=translated src=- shape=ac98b8dc vocab=0a0302d7
-/
theorem connectedADECoordinates_of_e8TripodIso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (g : tripodGraph 1 2 4 ≃g G) : ConnectedADECoordinates G := by
  let e : Fin 8 ≃ V := e8TripodEquiv.trans g.toEquiv
  refine ⟨.E8, by simp only [ADEType.IsRegular], ?_, e, ?_⟩
  · simpa only [ADEType.rank, Fintype.card_fin] using Fintype.card_congr e
  · intro i j
    change graphCartanMatrix G (e i) (e j) = gramE 8 i j
    calc
      _ = graphCartanMatrix (tripodGraph 1 2 4)
          (e8TripodEquiv i) (e8TripodEquiv j) := graphCartanMatrix_apply_iso g _ _
      _ = gramE 8 i j := graphCartanMatrix_e8Tripod i j

end Lattice
end SRG266
