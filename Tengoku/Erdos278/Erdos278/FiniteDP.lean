import Tengoku.Erdos278.Erdos278.PartitionDP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- The same recurrence with a finite coordinate type, enumerated by `equivFin`.-/
noncomputable def finiteSeparationDP {r : ℕ} {C : Type*} [Fintype C]
    (choices : C → Finset (SeparationMask r)) : Finset (SeparationMask r) :=
  separationDP (fun t => if ht : t < Fintype.card C then
    choices ((Fintype.equivFin C).symm ⟨t, ht⟩) else {∅}) (Fintype.card C)

/--
@isnad1 id=iff.0h4v.s7.9951a3b00d97 from=translated src=- shape=ff32b849 vocab=d1656370
-/
theorem finite_separation_dp_exact {r : ℕ} {C : Type*} [Fintype C]
    (choices : C → Finset (SeparationMask r)) (H : SeparationMask r) :
    H ∈ finiteSeparationDP choices ↔
      ∃ f : C → SeparationMask r, (∀ c, f c ∈ choices c) ∧
        H = univ.biUnion f := by
  classical
  rw [finiteSeparationDP, separation_dp_exact]
  let enc := Fintype.equivFin C
  constructor
  · rintro ⟨g, hg, hH⟩
    let f : C → SeparationMask r := fun c => g (enc c).val
    have hf (c : C) : f c ∈ choices c := by
      have h := hg (enc c).val (enc c).isLt
      simpa [enc, f] using h
    refine ⟨f, hf, hH.trans ?_⟩
    ext e
    simp only [mem_biUnion, mem_range, mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, he⟩
      refine ⟨enc.symm ⟨t, ht⟩, ?_⟩
      simpa [f] using he
    · rintro ⟨c, he⟩
      exact ⟨(enc c).val, (enc c).isLt, he⟩
  · rintro ⟨f, hf, hH⟩
    let g : ℕ → SeparationMask r := fun t =>
      if ht : t < Fintype.card C then f (enc.symm ⟨t, ht⟩) else ∅
    refine ⟨g, ?_, hH.trans ?_⟩
    · intro t ht
      simpa [g, ht, enc] using hf (enc.symm ⟨t, ht⟩)
    · ext e
      simp only [mem_biUnion, mem_range, mem_univ, true_and]
      constructor
      · rintro ⟨c, he⟩
        refine ⟨(enc c).val, (enc c).isLt, ?_⟩
        simpa [g] using he
      · rintro ⟨t, ht, he⟩
        exact ⟨enc.symm ⟨t, ht⟩, by simpa [g, ht] using he⟩

/-- Exact partial-coding DP, with an alphabet allowed to vary by coordinate.
@isnad1 id=iff.2h5v.s7.909a19e805b5 from=translated src=- shape=b3315054 vocab=074a3278
-/
theorem coordinate_dp_exact {r : ℕ} {C : Type*} [Fintype C]
    (hr : 0 < r) (V : C → Finset (Fin r)) (b : C → ℕ)
    (hb : ∀ c, 0 < b c) (H : SeparationMask r) :
    H ∈ finiteSeparationDP (fun c => localSeparationMasks (V c) (b c)) ↔
      ∃ u : ∀ c, Fin r → Fin (b c),
        H = univ.biUnion (fun c => separationMask (V c) (u c)) := by
  classical
  rw [finite_separation_dp_exact]
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hex (c : C) := (local_masks_exact hr (hb c) (V c) (f c)).mp (hf c)
    refine ⟨fun c => Classical.choose (hex c), ?_⟩
    apply biUnion_congr rfl
    intro c _
    exact (Classical.choose_spec (hex c)).symm
  · rintro ⟨u, rfl⟩
    exact ⟨fun c => separationMask (V c) (u c),
      fun c => (local_masks_exact hr (hb c) (V c) _).mpr ⟨u c, rfl⟩, rfl⟩

end Erdos278
