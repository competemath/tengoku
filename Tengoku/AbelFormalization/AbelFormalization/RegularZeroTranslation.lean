import Tengoku.AbelFormalization.AbelFormalization.RegularZeroBasics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/--
@isnad1 id=eq.0h5v.s6.1e56487e2310 from=translated src=- shape=a8a0f3fb vocab=155bcdd5
-/
theorem regularZeroSet_preimage_add_right
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E) (Omega : Set E) (f : E → F) :
    regularZeroSet ((fun x : E ↦ x + c) ⁻¹' Omega)
        (fun x ↦ f (x + c)) =
      (fun x : E ↦ x + c) ⁻¹' regularZeroSet Omega f := by
  ext x
  simp only [regularZeroSet, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [fderiv_comp_add_right]

/--
@isnad1 id=iff.0h5v.s6.aef936c67507 from=translated src=- shape=e6adf176 vocab=0090c7e9
-/
theorem finite_regularZeroSet_add_right_iff
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E) (Omega : Set E) (f : E → F) :
    (regularZeroSet ((fun x : E ↦ x + c) ⁻¹' Omega)
      (fun x ↦ f (x + c))).Finite ↔
      (regularZeroSet Omega f).Finite := by
  rw [regularZeroSet_preimage_add_right]
  constructor
  · intro h
    apply h.of_preimage
    intro x
    exact ⟨x - c, by abel⟩
  · intro h
    exact Set.Finite.preimage
      (Set.injOn_of_injective (fun _ _ hxy ↦ add_right_cancel hxy)) h

end AbelFormalization
