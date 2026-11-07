module

public import Tengoku.Seed.Data.Vector.Basic
public import Tengoku.Seed.Data.PFun

namespace Part
end Part

namespace FoundationFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose]
public section

namespace Part
open _root_.Part

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h4v.s5.762e77de95b0 from=translated src=- shape=fb946f3c vocab=4f845458
-/
@[simp] lemma mem_vector_mOfFn : ∀ {n : ℕ} {w : List.Vector α n} {v : Fin n →. α},
    w ∈ List.Vector.mOfFn v ↔ ∀ i, w.get i ∈ v i
  |     0, _, _ => by simp [List.Vector.mOfFn, List.Vector.eq_nil]
  | n + 1, w, v => by
    suffices (∃ a ∈ v 0, ∃ u, (∀ (i : Fin n), u.get i ∈ v i.succ) ∧ w = a ::ᵥ u) ↔ ∀ (i : Fin (n + 1)), w.get i ∈ v i by
      simpa [List.Vector.mOfFn, @mem_vector_mOfFn _ n]
    constructor
    · rintro ⟨a, ha, v, hv, rfl⟩ i; cases i using Fin.cases <;> simp [ha, hv]
    · intro h; exact ⟨w.head, by simpa using h 0, w.tail, fun i ↦ by simpa using h i.succ, by simp⟩

/--
@isnad1 id=iff.0h1v.s3.a8a8f9fffae4 from=translated src=- shape=ea786a35 vocab=fa458670
-/
lemma unit_dom_iff (x : Part Unit) : x.Dom ↔ () ∈ x := by simp [dom_iff_mem, show ∀ x : Unit, x = () by intro x; rfl]

end Part
