import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem

set_option autoImplicit false

/--
@isnad1 id=and.5h5v.s10.e9e07e362ede from=translated src=- shape=5f11005f vocab=6b838be6
-/
theorem solution
    {S : Type*} [CommRing S] (γ : S ≃+* S) {P₁ P₂ : Ideal S}
    (h₁ : P₁.map (γ : S →+* S) = P₁ ∨ P₁.map (γ : S →+* S) = P₂)
    (h₂ : P₂.map (γ : S →+* S) = P₁ ∨ P₂.map (γ : S →+* S) = P₂)
    {a : S} (hγa : γ a = a) (ha₁ : a ∈ P₁) (ha₂ : a ∉ P₂) :
    P₁.map (γ : S →+* S) = P₁ ∧ P₂.map (γ : S →+* S) = P₂ := by
  have hmem : a ∈ P₁.map (γ : S →+* S) := by
    rw [← hγa]; exact Ideal.mem_map_of_mem _ ha₁
  have hP₁ : P₁.map (γ : S →+* S) = P₁ := by
    rcases h₁ with h | h
    · exact h
    · exact absurd (h ▸ hmem) ha₂
  refine ⟨hP₁, ?_⟩
  rcases h₂ with h | h
  ·
    exfalso
    have hinj : Function.Injective (Ideal.map (γ : S →+* S)) := fun I J hIJ => by
      have := congrArg (Ideal.map ((γ.symm : S ≃+* S) : S →+* S)) hIJ
      rwa [Ideal.map_map, Ideal.map_map, show ((γ.symm : S ≃+* S) : S →+* S).comp (γ : S →+* S) = RingHom.id S
        from by ext x; simp, Ideal.map_id, Ideal.map_id] at this
    have : P₂ = P₁ := hinj (h.trans hP₁.symm)
    exact ha₂ (this ▸ ha₁)
  · exact h
