module

public import Tengoku
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Data.Finset.Pi

public section

namespace Finset
variable {ι : Type*} {α : ι → Type*} {s : Finset ι} {t : ∀ i, Finset (α i)}

/--
@isnad1 id=eq.1h4v.s6.0f79459e61e9 from=translated src=- shape=97592402 vocab=a0700a99
-/
lemma card_pi' (ht : ∀ i ∉ s, ∃ x, t i = {x}) :
    #(s.pi' t fun i hi ↦ by obtain ⟨x, hx⟩ := ht i hi; simp [hx]) = ∏ i ∈ s, #(t i) := by
  classical choose x hx using id ht; rw [pi'_of_forall_singleton x hx, card_map, card_pi]

end Finset
