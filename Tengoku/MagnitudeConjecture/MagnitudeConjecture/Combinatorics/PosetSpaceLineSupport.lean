import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.PosetSpaceRealization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Upper-set lines remember their supports -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.PosetSpace
universe u
variable {k T : Type u} [Field k] [PartialOrder T]

/-- A nonzero map between upper-set lines forces inclusion of their supports.
@isnad1 id=le.3h5v.s7.ce07b19a7239 from=translated src=- shape=fa427979 vocab=cb6a283d
-/
theorem line_support_subset_of_nonzero
    {U V : Set T} {hU : IsUpperSet U} {hV : IsUpperSet V}
    (f : line k T U hU ⟶ line k T V hV) (hf : f ≠ 0) : U ⊆ V := by
  classical
  have h₁ : f.linear (1 : k) ≠ 0 := by
    intro hz
    apply hf
    apply Hom.ext
    apply LinearMap.ext
    intro x
    change f.linear x = 0
    calc
      f.linear x = f.linear (x • (1 : k)) := by simp
      _ = x • f.linear (1 : k) := f.linear.map_smul x 1
      _ = 0 := by rw [hz, smul_zero]
  intro t ht
  by_contra hn
  have hm := f.map_subspace t (1 : k) (by change (1 : k) ∈ if t ∈ U then ⊤ else ⊥; simp [ht])
  rw [line_subspace_of_not_mem k T V hV t hn] at hm
  exact h₁ (by simpa using hm)

/-- The hom of an isomorphism between upper-set lines is nonzero.
@isnad1 id=ne.2h5v.s7.cbca87a6542c from=translated src=- shape=8c060eaf vocab=bb79de41
-/
theorem lineIso_hom_ne_zero
    {U V : Set T} {hU : IsUpperSet U} {hV : IsUpperSet V}
    (e : line k T U hU ≅ line k T V hV) : e.hom ≠ 0 := by
  intro hz
  have h := e.hom_inv_id
  rw [hz, zero_comp] at h
  have h₁ := congrArg (fun f : line k T U hU ⟶ line k T U hU ↦ f.linear (1 : k)) h
  exact (zero_ne_one : (0 : k) ≠ 1) (by simpa using h₁)

/-- Isomorphic upper-set lines have equal supports.
@isnad1 id=eq.2h5v.s6.939c81afe677 from=translated src=- shape=4b365702 vocab=4d216385
-/
theorem line_support_eq_of_iso
    {U V : Set T} {hU : IsUpperSet U} {hV : IsUpperSet V}
    (e : line k T U hU ≅ line k T V hV) : U = V :=
  Set.Subset.antisymm
    (line_support_subset_of_nonzero e.hom (lineIso_hom_ne_zero e))
    (line_support_subset_of_nonzero e.inv (lineIso_hom_ne_zero e.symm))

end MagnitudeConjecture.PosetSpace
