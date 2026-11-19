import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.KLinkedRooted

import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Routing paired mixed-fan arrivals through a linked hub

A perfect matching of distinct hub arrivals can be realized by disjoint
paths whose interiors avoid every arrival.
-/

namespace HadwigerLean
namespace Woven

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι]

/-- The prescribed pairing of the mixed-fan arrivals.-/
def hubArrivalPairs {m : ℕ} (arrival : ι → W)
    (slot : Fin m × Fin 2 ≃ ι) : IndexedPairs (Fin m) W where
  start := fun i => arrival (slot (i,0))
  finish := fun i => arrival (slot (i,1))

/-- The finite set of all arrival vertices.-/
noncomputable def hubArrivals (arrival : ι → W) : Finset W := by
  classical
  exact Finset.univ.image arrival

private theorem hubArrivalPairs_disjoint {m : ℕ}
    (arrival : ι → W) (hinj : Function.Injective arrival)
    (slot : Fin m × Fin 2 ≃ ι) :
    (hubArrivalPairs arrival slot).DisjointTerminals := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hvi hvj
  rcases hvi with hvi | hvi <;> rcases hvj with hvj | hvj
  · have heq : (i,(0 : Fin 2)) = (j,(0 : Fin 2)) :=
      slot.injective (hinj (by simpa [hubArrivalPairs] using hvi.symm.trans hvj))
    exact hij (congrArg Prod.fst heq)
  · have heq : (i,(0 : Fin 2)) = (j,(1 : Fin 2)) :=
      slot.injective (hinj (by simpa [hubArrivalPairs] using hvi.symm.trans hvj))
    cases (congrArg Prod.snd heq)
  · have heq : (i,(1 : Fin 2)) = (j,(0 : Fin 2)) :=
      slot.injective (hinj (by simpa [hubArrivalPairs] using hvi.symm.trans hvj))
    cases (congrArg Prod.snd heq)
  · have heq : (i,(1 : Fin 2)) = (j,(1 : Fin 2)) :=
      slot.injective (hinj (by simpa [hubArrivalPairs] using hvi.symm.trans hvj))
    exact hij (congrArg Prod.fst heq)

private theorem hubArrivalPairs_ne {m : ℕ}
    (arrival : ι → W) (hinj : Function.Injective arrival)
    (slot : Fin m × Fin 2 ≃ ι) (i : Fin m) :
    (hubArrivalPairs arrival slot).start i ≠
      (hubArrivalPairs arrival slot).finish i := by
  intro h
  have heq : (i,(0 : Fin 2)) = (i,(1 : Fin 2)) :=
    slot.injective (hinj (by simpa [hubArrivalPairs] using h))
  cases (congrArg Prod.snd heq)

private theorem hubArrivalPairs_inside {m : ℕ}
    (arrival : ι → W) (slot : Fin m × Fin 2 ≃ ι)
    (i : Fin m) :
    (hubArrivalPairs arrival slot).terminals i ⊆
      (hubArrivals arrival : Set W) := by
  intro v hv
  rcases hv with rfl | rfl
  · exact Finset.mem_image.mpr ⟨slot (i,0), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨slot (i,1), Finset.mem_univ _, rfl⟩

/-- A rooted-linked hub routes every prescribed pairing of distinct
arrivals, and the route interiors avoid all arrivals.-/
theorem exists_hub_arrival_routing {m : ℕ}
    (H : SimpleGraph W) (arrival : ι → W)
    (hinj : Function.Injective arrival)
    (slot : Fin m × Fin 2 ≃ ι)
    (hrooted : Linkedness.RootedLinked H (hubArrivals arrival)) :
    ∃ L : IndexedLinkage H (hubArrivalPairs arrival slot),
      Linkedness.InteriorsAvoid L (hubArrivals arrival) := by
  exact hrooted m (hubArrivalPairs arrival slot)
    (hubArrivalPairs_disjoint arrival hinj slot)
    (hubArrivalPairs_ne arrival hinj slot)
    (hubArrivalPairs_inside arrival slot)

end Woven
end HadwigerLean
