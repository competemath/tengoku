import Tengoku.Linearhadwiger.HadwigerLean.Woven.MixedFanTail
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reindexing and projecting the mixed Menger linkage
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V} {a : ℕ}
  {P : IndexedPairs (Fin a × Fin 2) V}

/-- The canonical auxiliary source represented by a proxy or a pair.-/
def pairedMixedSource : Z ⊕ Fin a → PairedFanVertex V a
  | .inl z => .inl z.1
  | .inr i => .inr i

theorem pairedMixedSource_injective :
    Function.Injective (pairedMixedSource (Z := Z) (a := a)) := by
  intro x y h
  cases x with
  | inl z =>
      cases y with
      | inl w =>
          change Sum.inl z.1 = Sum.inl w.1 at h
          exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective h))
      | inr j => cases h
  | inr i =>
      cases y with
      | inl w => cases h
      | inr j =>
          change Sum.inr i = Sum.inr j at h
          exact congrArg Sum.inr (Sum.inr_injective h)
theorem pairedMixedSource_mem (x : Z ⊕ Fin a) :
    pairedMixedSource x ∈
      pairedFanLeftSet (a := a) Z ∪
        pairedFanRightSet (V := V) (a := a) := by
  cases x with
  | inl z =>
      exact Finset.mem_union_left _ ((mem_pairedFanLeftSet Z z.1).2 z.2)
  | inr i =>
      exact Finset.mem_union_right _ (mem_pairedFanRightSet i)

/-- A full mixed linkage has a distinct path assigned to every proxy and
every auxiliary pair source.-/
theorem pairedMixed_slot_index
    (Q : IndexedPairs (Fin ((pairedFanLeftSet (a := a) Z).card +
        (pairedFanRightSet (V := V) (a := a)).card))
      (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hAB : SetMenger.IsABLinkage M
      (pairedFanLeftSet (a := a) Z ∪
        pairedFanRightSet (V := V) (a := a))
      (pairedFanLeftSet (a := a) H)) :
    ∃ f : Z ⊕ Fin a → Fin ((pairedFanLeftSet (a := a) Z).card +
        (pairedFanRightSet (V := V) (a := a)).card),
      Function.Injective f ∧
      ∀ x, Q.start (f x) = pairedMixedSource x := by
  classical
  let f (x : Z ⊕ Fin a) := Classical.choose
    (pairedMixed_start_surjective Q M hAB
      (pairedMixedSource x) (pairedMixedSource_mem x))
  have hf (x : Z ⊕ Fin a) :
      Q.start (f x) = pairedMixedSource x :=
    Classical.choose_spec
      (pairedMixed_start_surjective Q M hAB
        (pairedMixedSource x) (pairedMixedSource_mem x))
  refine ⟨f, ?_, hf⟩
  intro x y hxy
  apply pairedMixedSource_injective
  calc
    pairedMixedSource x = Q.start (f x) := (hf x).symm
    _ = Q.start (f y) := by rw [hxy]
    _ = pairedMixedSource y := hf y

/-- Decode the hub endpoint of a saturated auxiliary path.-/
noncomputable def pairedMixedFinish
    {ι : Type*} (Q : IndexedPairs ι (PairedFanVertex V a))
    (hfinish : ∀ j, Q.finish j ∈ pairedFanLeftSet (a := a) H)
    (j : ι) : H :=
  pairedFanLeftDecode H ⟨Q.finish j, hfinish j⟩

/-- Copy an auxiliary path to its canonical proxy or pair source and
its decoded old-vertex hub endpoint.-/
noncomputable def pairedMixedCanonicalPath
    {ι : Type*} (Q : IndexedPairs ι (PairedFanVertex V a))
    (M : IndexedLinkage (pairedFanGraph G P.start) Q)
    (hfinish : ∀ j, Q.finish j ∈ pairedFanLeftSet (a := a) H)
    (j : ι) (x : Z ⊕ Fin a)
    (hstart : Q.start j = pairedMixedSource x) :
    (pairedFanGraph G P.start).Path
      (pairedMixedSource x) (.inl (pairedMixedFinish Q hfinish j).1) := by
  have hend : Q.finish j =
      Sum.inl (pairedMixedFinish Q hfinish j).1 :=
    (pairedFanLeftDecode_spec H ⟨Q.finish j, hfinish j⟩).symm
  exact ⟨((M.path j : (pairedFanGraph G P.start).Walk
      (Q.start j) (Q.finish j)).copy hstart hend),
    by simpa using (M.path j).property⟩

end Woven
end HadwigerLean
